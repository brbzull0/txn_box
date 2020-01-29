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

bool Comparison::operator()(Context &ctx, Generic *g) const {
  Feature f { g->extract() };
  return IndexFor(GENERIC) == f.index() ? false : (*this)(ctx, f);
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

protected:
  union Options {
    unsigned int all;
    struct {
      unsigned int nc : 1;
    } f;
    Options() { all = 0; } // Force zero initialization.
  };

  static Rv<Options> parse_options(TextView options);
};

Rv<Cmp_String::Options> Cmp_String::parse_options(TextView options) {
  Options zret;
  while (options) {
    auto token = options.take_prefix_at(',');
    if (0 == strcasecmp(NO_CASE_OPT, token)) {
      zret.f.nc = true;
    } else {
      return Error(R"("{}" is not a valid option for a string comparison.)", token);
    }
  }
  return zret;
}

// ---
// Specialized subclasses for the various options.

/// Base case for literal string comparisons.
class Cmp_LiteralString : public Cmp_String {
public:
  static constexpr TextView MATCH_KEY { "match" };
  static constexpr TextView CONTAIN_KEY { "contain" };
  static constexpr TextView PREFIX_KEY { "prefix" };
  static constexpr TextView SUFFIX_KEY { "suffix" };
  static constexpr TextView TLD_KEY { "tld" };

  /// Mark for @c STRING support only.
  static const ValueMask TYPES;

  /** Compare @a text for a match.
   *
   * @param ctx The transaction context.
   * @param text The feature to compare.
   * @return @c true if @a text matches, @c false otherwise.
   *
   * External API - required as a @c Comparison.
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
  Expr _expr; ///< To be compared to active feature.

  Cmp_LiteralString(Expr && expr);

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
    bool operator () (Feature const& f) { return ValueTypeOf(f) == STRING; }
    bool operator () (Expr::Direct const& d) { return d._result_type == STRING; }
    bool operator () (Expr::Composite const& comp) { return true; }
    bool operator () (Expr::List const& list) {
      return !_nested_p && std::all_of(list._exprs.begin(), list._exprs.end(), [](Expr const& x) {
        return std::visit(expr_validator{true}, x._expr);
      });
    }
  };
};

const ValueMask Cmp_LiteralString::TYPES = MaskFor({ STRING, TUPLE });

Cmp_LiteralString::Cmp_LiteralString(Expr && expr) : _expr(std::move(expr)) {}

bool Cmp_LiteralString::operator()(Context &ctx, FeatureView &active) const {
  Feature f { ctx.extract(_expr)};
  if (auto view = std::get_if<IndexFor(STRING)>(&f) ; nullptr != view) {
    return (*this)(ctx, *view, active);
  } else if ( auto t = std::get_if<IndexFor(TUPLE)>(&f) ; nullptr != t) {
    return std::any_of(t->begin(), t->end(), [&](Feature & f) -> bool {
      auto view = std::get_if<IndexFor(STRING)>(&f);
      return view && (*this)(ctx, *view, active);
    });
  }
  return false;
}

/// Match entire string.
class Cmp_MatchStd : public Cmp_LiteralString {
protected:
  using Cmp_LiteralString::Cmp_LiteralString;
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
class Cmp_MatchNC : public Cmp_LiteralString {
protected:
  using Cmp_LiteralString::Cmp_LiteralString;
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

class Cmp_Suffix : public Cmp_LiteralString {
protected:
  using Cmp_LiteralString::Cmp_LiteralString;
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

class Cmp_SuffixNC : public Cmp_LiteralString {
protected:
  using Cmp_LiteralString::Cmp_LiteralString;
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

class Cmp_Prefix : public Cmp_LiteralString {
protected:
  using Cmp_LiteralString::Cmp_LiteralString;
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

class Cmp_PrefixNC : public Cmp_LiteralString {
protected:
  using Cmp_LiteralString::Cmp_LiteralString;
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

class Cmp_Contain : public Cmp_LiteralString {
protected:
  using Cmp_LiteralString::Cmp_LiteralString;
  bool operator() (Context & ctx, TextView const& text, FeatureView & active) const override;
};

bool Cmp_Contain::operator()(Context& ctx, TextView const& text, FeatureView & active) const {
  if (auto idx = active.find(text) ; idx != TextView::npos) {
    if (ctx._update_remainder_p) {
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

class Cmp_ContainNC : public Cmp_LiteralString {
protected:
  using Cmp_LiteralString::Cmp_LiteralString;
  bool operator() (Context & ctx, TextView const& text, FeatureView & active) const override;
};

bool Cmp_ContainNC::operator()(Context& ctx, TextView const& text, FeatureView & active) const {
  if (text.size() <= active.size()) {
    auto spot = std::search(active.begin(), active.end(), text.begin(), text.end()
                            , [](char lhs, char rhs) { return tolower(lhs) == tolower(rhs); });
    if (spot != active.end()) {
      if (ctx._update_remainder_p) {
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

class Cmp_TLD : public Cmp_LiteralString {
protected:
  using Cmp_LiteralString::Cmp_LiteralString;
  bool operator() (Context & ctx, TextView const& text, FeatureView & active) const override;
};

bool Cmp_TLD::operator()(Context& ctx, TextView const& text, FeatureView & active) const {
  if (active.ends_with(text) && (text.size() == active.size() || active[active.size() - text.size() - 1] == '.')) {
    ctx.set_literal_capture(active.suffix(text.size()+1));
    ctx._remainder = active;
    ctx._remainder.remove_suffix(text.size()+1);
    return true;
  }
  return false;
}

class Cmp_TLDNC : public Cmp_LiteralString {
protected:
  using Cmp_LiteralString::Cmp_LiteralString;
  bool operator() (Context & ctx, TextView const& text, FeatureView & active) const override;
};

bool Cmp_TLDNC::operator()(Context& ctx, TextView const& text, FeatureView & active) const {
  if (active.ends_with_nocase(text) && (text.size() == active.size() || active[active.size() - text.size() - 1] == '.')) {
    ctx.set_literal_capture(active.suffix(text.size()+1));
    active.remove_suffix(text.size()+1);
    return true;
  }
  return false;
}
// ---

Rv<Comparison::Handle> Cmp_LiteralString::load(Config &cfg, YAML::Node const& cmp_node, TextView const& key, TextView const& arg, YAML::Node value_node) {
  auto &&[expr, errata]{cfg.parse_expr(value_node)};

  if (!errata.is_ok()) {
    errata.info(R"(While parsing comparison "{}" at {}.)", key, cmp_node.Mark());
    return std::move(errata);
  }

  auto && [ options, opt_errata ] { parse_options(arg) };
  if (! opt_errata.is_ok()) {
    opt_errata.info(R"(While parsing argument "{}" for comparison "{}".)", arg, key);
    return std::move(opt_errata);
  }

  auto expr_type = expr.result_type();
  if (!TYPES[IndexFor(expr_type)]) {
    return Error(R"(Value type "{}" for comparison "{}" at {} is not supported.)"
                 , expr_type, key, cmp_node.Mark());
  }

  if (TUPLE == expr_type && ! std::visit(expr_validator{}, expr._expr)) {
    return Error(R"(Value type "{}" for comparison "{}" at {} is not supported - lists must be of string values only.)"
                 , expr_type, key, cmp_node.Mark());
  }

  if (MATCH_KEY == key) {
    return options.f.nc
    ? Handle { new Cmp_MatchNC(std::move(expr)) }
    : Handle { new Cmp_MatchStd(std::move(expr)) };
  } else if (PREFIX_KEY == key) {
    return options.f.nc
      ? Handle{new Cmp_PrefixNC(std::move(expr))}
      : Handle{new Cmp_Prefix(std::move(expr))};
  } else if (SUFFIX_KEY == key) {
    return options.f.nc
      ? Handle{new Cmp_SuffixNC(std::move(expr))}
      : Handle{new Cmp_Suffix(std::move(expr))};
  } else if (CONTAIN_KEY == key) {
    return options.f.nc
    ? Handle(new Cmp_Contain(std::move(expr)))
    : Handle(new Cmp_ContainNC(std::move(expr)));
  } else if (TLD_KEY == key) {
    return options.f.nc
           ? Handle(new Cmp_TLDNC(std::move(expr)))
           : Handle(new Cmp_TLD(std::move(expr)));
  }

  return Error(R"(Internal error, unrecognized key "{}".)", key);
}
/* ------------------------------------------------------------------------------------ */
class Cmp_Rxp : public Cmp_String {
  using self_type = Cmp_Rxp;
  using super_type = Cmp_String;

public:
  static constexpr TextView KEY { "rxp" };
  static const ValueMask TYPES;

  static Rv<Comparison::Handle> load(Config &cfg, YAML::Node const& cmp_node, TextView const& key, TextView const& arg, YAML::Node value_node);

protected:
  using Item = std::variant<Rxp, Expr>;

  struct expr_visitor {
    expr_visitor(Config & cfg, Rxp::Options opt) : _cfg(cfg), _rxp_opt(opt) {}

    Rv<Handle> operator() (Feature & f);
    Rv<Handle> operator() (Expr::List & l);
    Rv<Handle> operator() (Expr::Direct & d);
    Rv<Handle> operator() (Expr::Composite & comp);
    template < typename T > Rv<Handle> operator() (T &) { return Error("Invalid feature type"); }

    Config & _cfg;
    Rxp::Options _rxp_opt;
  };

  struct rxp_visitor {
    bool operator() (Rxp const& rxp);
    bool operator() (Expr const& expr);

    Context & _ctx;
    Rxp::Options _rxp_opt;
    TextView _src;
  };
};

class Cmp_RxpSingle : public Cmp_Rxp {
  using self_type = Cmp_RxpSingle;
  using super_type = Cmp_Rxp;
public:
  Cmp_RxpSingle(Expr && expr, Rxp::Options);
  Cmp_RxpSingle(Rxp && rxp);
protected:
  bool operator()(Context &ctx, FeatureView &active) const override;

  Rxp::Options _opt;
  Item _rxp;
};

class Cmp_RxpList : public Cmp_Rxp {
  using self_type = Cmp_RxpList;
  using super_type = Cmp_Rxp;
  friend super_type;
public:
  Cmp_RxpList(Rxp::Options opt) : _opt(opt) {}
protected:
  struct expr_visitor {
    Errata operator() (Feature & f) {
      if (IndexFor(STRING) != f.index()) {
        return Error(R"("{}" literal must be a string.)", KEY);
      }

      auto && [ rxp, rxp_errata] { Rxp::parse(std::get<IndexFor(STRING)>(f), _rxp_opt) };
      if (! rxp_errata.is_ok()) {
        rxp_errata.info(R"(While parsing feature expression for "{}" comparison.)", KEY);
        return std::move(rxp_errata);
      }
      _rxp.emplace_back(std::move(rxp));
      return {};
    }
    Errata operator() (Expr::List & t) {
      return Error("Invalid type");
    }
    Errata operator() (Expr::Direct & d) {
      _rxp.emplace_back(Expr{std::move(d)});
      return {};
    }
    Errata operator() (Expr::Composite & comp) {
      _rxp.emplace_back(Expr{std::move(comp)});
      return {};
    }
    Errata operator() (std::monostate) {
      return Error("Invalid type");
    }

    std::vector<Item> &_rxp;
    Rxp::Options _rxp_opt;
  };

  bool operator()(Context &ctx, FeatureView &active) const override;

  Rxp::Options _opt;
  std::vector<Item> _rxp;
};

const ValueMask Cmp_Rxp::TYPES {MaskFor({ STRING, ACTIVE }) };

bool Cmp_Rxp::rxp_visitor::operator()(const Rxp &rxp) {
  auto result = rxp(_src, _ctx.rxp_working_match_data());
  if (result > 0) {
    _ctx.rxp_commit_match(_src);
    return true;
  }
  return false;
}

bool Cmp_Rxp::rxp_visitor::operator() (Expr const& expr) {
  auto f = _ctx.extract(expr);
  if (auto text = std::get_if<IndexFor(STRING)>(&f) ; text != nullptr ) {
    auto &&[rxp, rxp_errata]{Rxp::parse(*text, _rxp_opt)};
    if (rxp_errata.is_ok()) {
      return (*this)(rxp);
    }
  }
  return false;
}

Rv<Comparison::Handle> Cmp_Rxp::expr_visitor::operator() (Feature & f) {
  if (IndexFor(STRING) != f.index()) {
    return Error(R"("{}" literal must be a string.)", KEY);
  }

  auto && [ rxp, rxp_errata] { Rxp::parse(std::get<IndexFor(STRING)>(f), _rxp_opt) };
  if (! rxp_errata.is_ok()) {
    rxp_errata.info(R"(While parsing feature expression for "{}" comparison.)", KEY);
    return std::move(rxp_errata);
  }
  return Handle(new Cmp_RxpSingle(std::move(rxp)));
}

Rv<Comparison::Handle> Cmp_Rxp::expr_visitor::operator() (Expr::Direct & d) {
  return Handle(new Cmp_RxpSingle(Expr{std::move(d)}, _rxp_opt));
}

Rv<Comparison::Handle> Cmp_Rxp::expr_visitor::operator() (Expr::Composite & comp) {
  return Handle(new Cmp_RxpSingle(Expr{std::move(comp)}, _rxp_opt));
}

Rv<Comparison::Handle> Cmp_Rxp::expr_visitor::operator() (Expr::List & l) {
  auto rxm = new Cmp_RxpList{_rxp_opt};
  Cmp_RxpList::expr_visitor ev {rxm->_rxp, _rxp_opt};
  for ( auto && elt : l._exprs) {
    if (elt.result_type() != STRING) {
      return Error(R"("{}" literal must be a string.)", KEY);
    }
    std::visit(ev, elt._expr);
  }
  return Handle { rxm };
}

Rv<Comparison::Handle> Cmp_Rxp::load(Config &cfg, YAML::Node const& cmp_node, TextView const& key, TextView const& arg, YAML::Node value_node) {
  auto &&[expr, errata]{cfg.parse_expr(value_node)};

  if (!errata.is_ok()) {
    errata.info(R"(While parsing comparison "{}" at {}.)", key, cmp_node.Mark());
    return std::move(errata);
  }

  auto &&[options, opt_errata]{self_type::parse_options(arg)};
  if (!opt_errata.is_ok()) {
    opt_errata.info(R"(While parsing argument "{}" for comparison "{}".)", arg, key);
    return std::move(opt_errata);
  }

  Rxp::Options rxp_opt;
  rxp_opt.f.nc = options.f.nc;
  return std::visit(expr_visitor{cfg, rxp_opt}, expr._expr);
}

Cmp_RxpSingle::Cmp_RxpSingle(Expr && expr, Rxp::Options opt) : _rxp(std::move(expr)), _opt(opt) {
}

Cmp_RxpSingle::Cmp_RxpSingle(Rxp && rxp) : _rxp(std::move(rxp)) {
}

bool Cmp_RxpSingle::operator()(Context & ctx, FeatureView & active) const {
  return std::visit(rxp_visitor{ctx, _opt, active}, _rxp);
}

bool Cmp_RxpList::operator()(Context &ctx, FeatureView &active) const {
  return std::any_of(_rxp.begin(), _rxp.end(), [&](Item const&item) {
    return std::visit(rxp_visitor{ctx, _opt}, item);
  });
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
  Expr _value_fmt;

  Cmp_Binary_Integer(Expr && fmt) : _value_fmt(std::move(fmt)) {}
};

template < bool P(feature_type_for<INTEGER>, feature_type_for<INTEGER>) >
Rv<Comparison::Handle> Cmp_Binary_Integer<P>::load(Config& cfg, YAML::Node const& cmp_node, TextView const& key, TextView const& arg, YAML::Node value_node) {
  auto && [ expr, errata ] = cfg.parse_expr(value_node);
  if (!errata.is_ok()) {
    return std::move(errata.info(R"(While parsing comparison "{}" value at {}.)", KEY, value_node.Mark()));
  }
  auto expr_type = expr.result_type();
  if (!TYPES[expr_type]) {
    return Error(R"(The type {} of the value for "{}" at {} is not one of {} as required.)", expr_type, KEY, value_node.Mark(), TYPES);
  }
  return Handle(new self_type(std::move(expr)));
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
  Comparison::define(Cmp_LiteralString::MATCH_KEY, Cmp_LiteralString::TYPES, Cmp_LiteralString::load);
  Comparison::define(Cmp_LiteralString::PREFIX_KEY, Cmp_LiteralString::TYPES, Cmp_LiteralString::load);
  Comparison::define(Cmp_LiteralString::SUFFIX_KEY, Cmp_LiteralString::TYPES, Cmp_LiteralString::load);
  Comparison::define(Cmp_LiteralString::CONTAIN_KEY, Cmp_LiteralString::TYPES, Cmp_LiteralString::load);
  Comparison::define(Cmp_LiteralString::TLD_KEY, Cmp_LiteralString::TYPES, Cmp_LiteralString::load);

  Comparison::define(Cmp_Rxp::KEY, Cmp_Rxp::TYPES, Cmp_Rxp::load);

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

