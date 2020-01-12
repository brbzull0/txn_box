/** @file
 * Comparison implementations.
 *
 * Copyright 2019, Oath Inc.
 * SPDX-License-Identifier: Apache-2.0
 */

#include <string>
#include <algorithm>

#include <swoc/bwf_base.h>

#include "txn_box/common.h"
#include "txn_box/Rxp.h"
#include "txn_box/Comparison.h"
#include "txn_box/Directive.h"
#include "txn_box/Config.h"
#include "txn_box/Context.h"

using swoc::TextView;
using namespace swoc::literals;
using swoc::Errata;
using swoc::Rv;

Comparison::Factory Comparison::_factory;

unsigned Comparison::rxp_group_count() const { return 0; }

Errata Comparison::define(swoc::TextView name, ValueMask const& types, Comparison::Loader &&worker) {
  _factory[name] = std::make_tuple(std::move(worker), types);
  return {};
}

Rv<Comparison::Handle> Comparison::load(Config & cfg, ValueType ftype, YAML::Node node) {
  for ( auto const& [ key_node, value_node ] : node ) {
    TextView key { key_node.Scalar() };
    auto && [ arg, arg_errata ] { parse_arg(key) };
    if (!arg_errata.is_ok()) {
      return std::move(arg_errata);
    }
    if (key == Directive::DO_KEY) {
      continue;
    }
    // See if this is in the factory. It's not an error if it's not, to enable adding extra
    // keys to comparison. First key that is in the factory determines the comparison type.
    if ( auto spot { _factory.find(key) } ; spot != _factory.end()) {
      auto &&[loader, types] = spot->second;
      if (! types[IndexFor(ftype)]) {
        return Error(R"(Comparison "{}" at {} is not valid for a feature of type "{}".)", key, node.Mark(), ftype);
      }

      auto &&[handle, errata]{loader(cfg, node, key, arg, value_node)};

      if (!errata.is_ok()) {
        return std::move(errata);
      }

      return std::move(handle);
    }
  }
  return Error(R"(No valid comparison key in object at {}.)", node.Mark());
}
/* ------------------------------------------------------------------------------------ */
/** Utility base class for comparisons that are based on literal string matching.
 * This is @b not intended to be used as a comparison itself.
 */
class Cmp_String: public Comparison {
  using self_type = Cmp_String; ///< Self reference type.
  using super_type = Comparison; ///< Parent type.
public:
  static constexpr TextView NO_CASE_OPT { "nc" };

  static constexpr TextView MATCH_KEY { "match" };
  static constexpr TextView CONTAIN_KEY { "contain" };
  static constexpr TextView PREFIX_KEY { "prefix" };
  static constexpr TextView SUFFIX_KEY { "suffix" };
  static constexpr TextView RXP_KEY { "rxp" };

  /// Mark for @c STRING support only.
  static const ValueMask TYPES;

  /** Compare @a text for a match.
   *
   * @param ctx The transaction context.
   * @param text The feature to compare.
   * @return @c true if @a text matches, @c false otherwise.
   */
  bool operator() (Context& ctx, FeatureView& text) const override;

  /** Instantiate an instance from YAML configuration.
   *
   * @param cfg Global configuration object.
   * @param cmp_node The node containing the comparison.
   * @param key Key for comparison.
   * @param arg Argument for @a key, if any (stripped from @a key).
   * @param value_node Value node for for @a key.
   * @return An instance or errors on failure.
   */
  static Rv<Handle> load(Config& cfg, YAML::Node const& cmp_node, TextView const& key, TextView const& arg, YAML::Node value_node);

protected:
  Expr _expr; ///< Expression to compare with.

  /** Specialized comparison.
   *
   * @param ctx Runtime context.
   * @param text Configured value to check with.
   * @param active Active value to be compred to configured value.
   * @return @c true on match @c false otherwise.
   *
   * This class will handle extracting the stored expression and pass it piecewise (if needed)
   * to the specialized subclass. @a text is the extracted text, @a active is the value passed
   * in at run time to check.
   */
  virtual bool operator()(Context & ctx, TextView const& text, FeatureView & active) const = 0;

  struct expr_validator {
    bool _nested_p = false;

    bool operator () (std::monostate const& nil) { return false; }
    bool operator () (Feature const& f) { return f.index() == IndexFor(STRING); }
    bool operator () (Expr::Direct const& d) { return true; }
    bool operator () (Expr::Composite const& comp) { return true; }
    bool operator () (Expr::Tuple const& t) {
      return !_nested_p && std::all_of(t._exprs.begin(), t._exprs.end(), [](Expr const& x) {
        return std::visit(expr_validator{true}, x._expr);
      });
    }
  };

  /// Internal constructor used by @c load.
  explicit Cmp_String(Expr && expr);
};

bool Cmp_String::operator()(Context &ctx, FeatureView &active) const {
  Feature f { ctx.extract(_expr)};
  if (auto view = std::get_if<IndexFor(STRING)>(&f) ; nullptr != view) {
    return (*this)(ctx, *view, active);
  } else if ( auto t = std::get_if<IndexFor(TUPLE)>(&f) ; nullptr != t) {
    return std::any_of(t->begin(), t->end(), [&](Feature * f) -> bool {
      auto view = std::get_if<IndexFor(STRING)>(f);
      return view && (*this)(ctx, *view, active);
    });
  }
  return false;
}

// ---
// Specialized subclasses for the various options.

/// Match entire string.
class Cmp_MatchStd : public Cmp_String {
protected:
  using Cmp_String::Cmp_String;
  bool operator() (Context & ctx, TextView const& text, FeatureView & active) const override;
};

bool Cmp_MatchStd::operator()(Context& ctx, TextView const& text, FeatureView & active) const {
  if (text == active) {
    ctx.set_literal_capture(active);
    active = TextView{}; // matched everything, clear active feature.
    return true;
  }
  return false;
}

/// Match entire string, ignoring case
class Cmp_MatchNC : public Cmp_String {
protected:
  using Cmp_String::Cmp_String;
  bool operator() (Context & ctx, TextView const& text, FeatureView & active) const override;
};

bool Cmp_MatchNC::operator()(Context& ctx, TextView const& text, FeatureView & active) const {
  if (0 == strcasecmp(text,active)) {
    ctx.set_literal_capture(active);
    active = TextView{}; // matched everything, clear active feature.
    return true;
  }
  return false;
}

class Cmp_Suffix : public Cmp_String {
protected:
  using Cmp_String::Cmp_String;
  bool operator() (Context & ctx, TextView const& text, FeatureView & active) const override;
};

bool Cmp_Suffix::operator()(Context& ctx, TextView const& text, FeatureView & active) const {
  if (active.ends_with(text)) {
    ctx.set_literal_capture(active.suffix(text.size()));
    active.remove_suffix(text.size());
    return true;
  }
  return false;
}

class Cmp_SuffixNC : public Cmp_String {
protected:
  using Cmp_String::Cmp_String;
  bool operator() (Context & ctx, TextView const& text, FeatureView & active) const override;
};

bool Cmp_SuffixNC::operator()(Context& ctx, TextView const& text, FeatureView & active) const {
  if (active.ends_with_nocase(text)) {
    ctx.set_literal_capture(active.suffix(text.size()));
    active.remove_suffix(text.size());
    return true;
  }
  return false;
}

class Cmp_Prefix : public Cmp_String {
protected:
  using Cmp_String::Cmp_String;
  bool operator() (Context & ctx, TextView const& text, FeatureView & active) const override;
};

bool Cmp_Prefix::operator()(Context& ctx, TextView const& text, FeatureView & active) const {
  if (active.starts_with(text)) {
    ctx.set_literal_capture(active.suffix(text.size()));
    active.remove_prefix(text.size());
    return true;
  }
  return false;
}

class Cmp_PrefixNC : public Cmp_String {
protected:
  using Cmp_String::Cmp_String;
  bool operator() (Context & ctx, TextView const& text, FeatureView & active) const override;
};

bool Cmp_PrefixNC::operator()(Context& ctx, TextView const& text, FeatureView & active) const {
  if (active.starts_with_nocase(text)) {
    ctx.set_literal_capture(active.suffix(text.size()));
    active.remove_prefix(text.size());
    return true;
  }
  return false;
}

class Cmp_Contain : public Cmp_String {
protected:
  using Cmp_String::Cmp_String;
  bool operator() (Context & ctx, TextView const& text, FeatureView & active) const override;
};

bool Cmp_Contain::operator()(Context& ctx, TextView const& text, FeatureView & active) const {
  if (auto idx = active.find(text) ; idx != TextView::npos) {
    if (ctx._active_p) {
      auto n = active.size() - text.size();
      auto span = ctx._arena->alloc(n).rebind<char>();
      memcpy(span, active.prefix(idx));
      memcpy(span.data() + idx, active.suffix(idx).data(), active.size() - (idx + text.size()));
      ctx.set_literal_capture(span.view());
    }
    return true;
  }
  return false;
}

class Cmp_ContainNC : public Cmp_String {
protected:
  using Cmp_String::Cmp_String;
  bool operator() (Context & ctx, TextView const& text, FeatureView & active) const override;
};

bool Cmp_ContainNC::operator()(Context& ctx, TextView const& text, FeatureView & active) const {
  if (text.size() <= active.size()) {
    auto spot = std::search(active.begin(), active.end(), text.begin(), text.end()
                            , [](char lhs, char rhs) { return tolower(lhs) == tolower(rhs); });
    if (spot != active.end()) {
      if (ctx._active_p) {
        size_t idx = spot - active.begin();
        auto n = active.size() - text.size();
        auto span = ctx._arena->alloc(n).rebind<char>();
        memcpy(span, active.prefix(idx));
        memcpy(span.data() + idx, active.suffix(idx).data(), active.size() - (idx + text.size()));
        ctx.set_literal_capture(span.view());
      }
      return true;
    }
  }
  return false;
}


class Cmp_Rxp : public Cmp_String {
protected:
  using Cmp_String::Cmp_String;
  bool operator() (Context & ctx, TextView const& text, FeatureView & active) const override;
};

bool Cmp_Rxp::operator()(Context & ctx, TextView const& text, FeatureView & active) const {

}

// ---

const ValueMask Cmp_String::TYPES {MaskFor({ STRING, TUPLE }) };

Cmp_String::Cmp_String(Expr && expr) : _expr(std::move(expr)) {}

Rv<Comparison::Handle> Cmp_String::load(Config &cfg, YAML::Node const& cmp_node, TextView const& key, TextView const& arg, YAML::Node value_node) {
  auto &&[expr, errata]{cfg.parse_expr(value_node)};

  if (!errata.is_ok()) {
    errata.info(R"(While parsing comparison "{}" at {}.)", key, cmp_node.Mark());
    return std::move(errata);
  }

  if (!TYPES[IndexFor(expr._result_type)]) {
    return Error(R"(Value type "{}" for comparison "{}" at {} is not supported.)"
                 , expr._result_type, key, cmp_node.Mark());
  }

  if (TUPLE == expr._result_type && ! std::visit(expr_validator{}, expr._expr)) {
    return Error(R"(Value type "{}" for comparison "{}" at {} is not supported - lists must be of string values only.)"
                 , expr._result_type, key, cmp_node.Mark());
  }

  auto options = arg;
  bool nc_p = false;
  while (options) {
    auto token = options.take_prefix_at(',');
    if (0 == strcasecmp(NO_CASE_OPT, token)) {
      nc_p = true;
    } else {
      return Error(R"("{}" is not a valid option for comparison "{}".)", token, key);
    }
  }

  if (MATCH_KEY == key) {
    if (nc_p) {
      return Handle { new Cmp_MatchNC(std::move(expr)) };
    } else {
      return Handle { new Cmp_MatchStd(std::move(expr)) };
    }
  } else if (PREFIX_KEY == key) {
    return nc_p
      ? Handle{new Cmp_PrefixNC(std::move(expr))}
      : Handle{new Cmp_Prefix(std::move(expr))};
  } else if (SUFFIX_KEY == key) {
    return nc_p
      ? Handle{new Cmp_SuffixNC(std::move(expr))}
      : Handle{new Cmp_Suffix(std::move(expr))};
  } else if (CONTAIN_KEY == key) {

  } else if (RXP_KEY == key) {

  }

  return {};
}

/* ------------------------------------------------------------------------------------ */
/* ------------------------------------------------------------------------------------ */
class Cmp_RegexMatch : public Comparison {
  using self_type = Cmp_RegexMatch;
  using super_type = Comparison;
public:
  /// Standard key.
  static const std::string KEY;
  /// Case insensitive comparison key.
  static const std::string KEY_NOCASE;
  /// Valid types for this comparison.
  static const ValueMask TYPES;

  bool operator() (Context& ctx, FeatureView& text) const override;
  unsigned rxp_group_count() const override;

  static Rv<Handle> load(Config& cfg, YAML::Node cmp_node, YAML::Node key_node);

protected:
  Rxp _rxp; ///< regular expression to match.
  bool _caseless_p = false;

  explicit Cmp_RegexMatch(Rxp && rxp) : _rxp(std::move(rxp)) {}
};

const std::string Cmp_RegexMatch::KEY { "regex" };
const std::string Cmp_RegexMatch::KEY_NOCASE { "regex-nocase" };
const ValueMask Cmp_RegexMatch::TYPES { MaskFor(STRING) };

unsigned Cmp_RegexMatch::rxp_group_count() const { return _rxp.capture_count(); }

Rv<Comparison::Handle> Cmp_RegexMatch::load(Config &cfg, YAML::Node cmp_node, YAML::Node key_node) {
  auto && [ fmt, errata ] { cfg.parse_feature(key_node) };
  if (! errata.is_ok()) {
    errata.info(R"(While parsing "{}" comparison value at {}.)", KEY, cmp_node.Mark());
    return { {}, std::move(errata) };
  }
  if (! fmt._literal_p) {
    return Error(R"(Dynamic regular expression support is not yet implemented at {}.)", key_node.Mark());
  }
  // Handle empty format / string?
  Rxp::OptionGroup rxp_opt;
  if (cmp_node[KEY_NOCASE] == key_node) {
    rxp_opt[Rxp::OPT_NOCASE] = true;
  }
  auto && [ rxp, rxp_errata ] { Rxp::parse(fmt[0]._ext, rxp_opt) }; // Config coalesced the literals.
  if (! rxp_errata.is_ok()) {
    rxp_errata.info(R"(While parsing "{}" value at {}.)", KEY, key_node.Mark());
    return { {}, std::move(rxp_errata) };
  }

  cfg.require_rxp_group_count(rxp.capture_count());
  return { Handle(new self_type(std::move(rxp))), {} };
}

bool Cmp_RegexMatch::operator()(Context& ctx, FeatureView &text) const {
  auto result = _rxp(text, ctx._rxp_working);
  if (result > 0) {
    // Update context to have this match as the active capture groups.
    ctx.promote_capture_data();
    ctx._rxp_src = text;
    return true;
  }
  return false;
}

/* ------------------------------------------------------------------------------------ */
swoc::Lexicon<BoolTag> BoolNames { { BoolTag::True, { "true", "1", "on", "enable", "Y", "yes" }}
                                   , { BoolTag::False, { "false", "0", "off", "disable", "N", "no" }}
};

/** Compare a boolean value.
 * Check if a value is true.
 */
class Cmp_true: public Comparison {
  using self_type = Cmp_true; ///< Self reference type.
  using super_type = Comparison; ///< Parent type.
public:
  static const std::string KEY; ///< Comparison name.
  static const ValueMask TYPES; ///< Supported types.

  bool operator() (Context& ctx, std::variant_alternative_t<IndexFor(STRING), Feature::variant_type>& text) const override;
  bool operator() (Context& ctx, std::variant_alternative_t<IndexFor(BOOLEAN), Feature::variant_type>& data) const override;
  bool operator() (Context& ctx, std::variant_alternative_t<IndexFor(INTEGER), Feature::variant_type>& data) const override;

  /// Construct an instance from YAML configuration.
  static Rv<Handle> load(Config& cfg, YAML::Node cmp_node, YAML::Node key_node);

protected:
  Cmp_true() = default;
};

const std::string Cmp_true::KEY { "true" };
const ValueMask Cmp_true::TYPES { MaskFor({ STRING, BOOLEAN, INTEGER }) };

bool Cmp_true::operator()(Context &ctx, feature_type_for<STRING> &text) const {
  return true == BoolNames[text];
}

bool Cmp_true::operator()(Context &ctx, feature_type_for<BOOLEAN> &data) const {
  return data;
}

bool Cmp_true::operator()(Context &ctx, feature_type_for<INTEGER> &data) const {
  return data != 0;
}

Rv<Comparison::Handle> Cmp_true::load(Config &cfg, YAML::Node cmp_node, YAML::Node key_node) {
  return { Handle{new self_type}, {} };
}

/** Compare a boolean value.
 * Check if a value is false.
 */
class Cmp_false: public Comparison {
  using self_type = Cmp_false; ///< Self reference type.
  using super_type = Comparison; ///< Parent type.
public:
  static const std::string KEY; ///< Comparison name.
  static const ValueMask TYPES; ///< Supported types.

  bool operator() (Context& ctx,feature_type_for<STRING>& text) const override;
  bool operator() (Context& ctx, feature_type_for<BOOLEAN>& data) const override;
  bool operator() (Context& ctx, feature_type_for<INTEGER>& data) const override;

  /// Construct an instance from YAML configuration.
  static Rv<Handle> load(Config& cfg, YAML::Node cmp_node, YAML::Node key_node);

protected:
  Cmp_false() = default;
};

const std::string Cmp_false::KEY { "false" };
const ValueMask Cmp_false::TYPES { MaskFor({ STRING, BOOLEAN, INTEGER }) };

bool Cmp_false::operator()(Context &ctx, feature_type_for<STRING> &text) const {
  return false == BoolNames[text];
}

bool Cmp_false::operator()(Context &ctx, feature_type_for<BOOLEAN> &data) const {
  return ! data;
}

bool Cmp_false::operator()(Context &ctx, feature_type_for<INTEGER> &data) const {
  return data == 0;
}

Rv<Comparison::Handle> Cmp_false::load(Config &cfg, YAML::Node cmp_node, YAML::Node key_node) {
  return { Handle{new self_type}, {} };
}
/* ------------------------------------------------------------------------------------ */
// Comarison functions.
// Because of template issues, can't use standard functors (e.g. std::equal_to) nor lambdas.
// Well, I _could_, but it would be as verbose as this style and more obscure.
namespace {
bool eq(feature_type_for<INTEGER> lhs, feature_type_for<INTEGER> rhs) { return lhs == rhs; }
bool ne(feature_type_for<INTEGER> lhs, feature_type_for<INTEGER> rhs) { return lhs != rhs; }
bool lt(feature_type_for<INTEGER> lhs, feature_type_for<INTEGER> rhs) { return lhs <  rhs; }
bool le(feature_type_for<INTEGER> lhs, feature_type_for<INTEGER> rhs) { return lhs <= rhs; }
bool gt(feature_type_for<INTEGER> lhs, feature_type_for<INTEGER> rhs) { return lhs >  rhs; }
bool ge(feature_type_for<INTEGER> lhs, feature_type_for<INTEGER> rhs) { return lhs >= rhs; }
} // namespace

/// Comment elements for all binary integer comparisons.
struct Binary_Integer_Compare_Commons {
  static const ValueMask TYPES; ///< Feature type supported.
};
const ValueMask Binary_Integer_Compare_Commons::TYPES { MaskFor(INTEGER) };

template < bool P(feature_type_for<INTEGER>, feature_type_for<INTEGER>) >
class Cmp_Binary_Integer : public Comparison, public Binary_Integer_Compare_Commons {
  using self_type = Cmp_Binary_Integer; ///< Self reference type.
  using super_type = Comparison; ///< Parent type.
public:
  static const std::string KEY; ///< Comparison name.

  bool operator() (Context& ctx, feature_type_for<INTEGER>& data) const override {
    auto value = ctx.extract(_value_fmt);
    return P(data, std::get<IndexFor(INTEGER)>(value));
  }

  /// Construct an instance from YAML configuration.
  static Rv<Handle> load(Config& cfg, YAML::Node const& cmp_node, YAML::Node const& key_node);

protected:
  Expr _value_fmt;

  Cmp_Binary_Integer(Expr && fmt) : _value_fmt(std::move(fmt)) {}
};

template < bool P(feature_type_for<INTEGER>, feature_type_for<INTEGER>) >
Rv<Comparison::Handle> Cmp_Binary_Integer<P>::load(Config& cfg, YAML::Node const& cmp_node, YAML::Node const& key_node) {
  auto && [ fmt, errata ] = cfg.parse_feature(key_node);
  if (!errata.is_ok()) {
    return { {}, std::move(errata.info(R"(While parsing comparison "{}" value at {}.)", KEY, key_node.Mark())) };
  }
  if (!TYPES[fmt._result_type]) {
    return Error(R"(The type {} of the value for "{}" at {} is not one of {} as required.)", fmt._result_type, KEY, key_node.Mark(), TYPES);
  }
  return { Handle(new self_type(std::move(fmt))), {} };
}

using Cmp_eq = Cmp_Binary_Integer<eq>;
using Cmp_ne = Cmp_Binary_Integer<ne>;
using Cmp_lt = Cmp_Binary_Integer<lt>;
using Cmp_le = Cmp_Binary_Integer<le>;
using Cmp_gt = Cmp_Binary_Integer<gt>;
using Cmp_ge = Cmp_Binary_Integer<ge>;

template<> const std::string Cmp_eq::KEY { "eq" };
template<> const std::string Cmp_ne::KEY { "ne" };
template<> const std::string Cmp_lt::KEY { "lt" };
template<> const std::string Cmp_le::KEY { "le" };
template<> const std::string Cmp_gt::KEY { "gt" };
template<> const std::string Cmp_ge::KEY { "ge" };
/* ------------------------------------------------------------------------------------ */

namespace {
[[maybe_unused]] bool INITIALIZED = [] () -> bool {
  Comparison::define(Cmp_Match::KEY, Cmp_Match::TYPES, Cmp_Match::load);
  Comparison::define(Cmp_MatchNocase::KEY, Cmp_MatchNocase::TYPES, Cmp_MatchNocase::load);
  Comparison::define(Cmp_Suffix::KEY, Cmp_Suffix::TYPES, &Cmp_Suffix::load);
  Comparison::define(Cmp_SuffixNocase::KEY, Cmp_SuffixNocase::TYPES, Cmp_SuffixNocase::load);
  Comparison::define(Cmp_Prefix::KEY, Cmp_Prefix::TYPES, &Cmp_Prefix::load);
  Comparison::define(Cmp_PrefixNocase::KEY, Cmp_PrefixNocase::TYPES, Cmp_PrefixNocase::load);
  Comparison::define(Cmp_RegexMatch::KEY, Cmp_RegexMatch::TYPES, Cmp_RegexMatch::load);
  Comparison::define(Cmp_RegexMatch::KEY_NOCASE, Cmp_RegexMatch::TYPES, Cmp_RegexMatch::load);
  Comparison::define(Cmp_true::KEY, Cmp_true::TYPES, Cmp_true::load);
  Comparison::define(Cmp_false::KEY, Cmp_false::TYPES, Cmp_false::load);

  Comparison::define(Cmp_eq::KEY, Cmp_eq::TYPES, Cmp_eq::load);
  Comparison::define(Cmp_ne::KEY, Cmp_ne::TYPES, Cmp_ne::load);
  Comparison::define(Cmp_lt::KEY, Cmp_le::TYPES, Cmp_lt::load);
  Comparison::define(Cmp_le::KEY, Cmp_lt::TYPES, Cmp_le::load);
  Comparison::define(Cmp_gt::KEY, Cmp_gt::TYPES, Cmp_gt::load);
  Comparison::define(Cmp_ge::KEY, Cmp_ge::TYPES, Cmp_ge::load);

  BoolNames.set_default(BoolTag::INVALID);

  return true;
} ();

}; // namespace

