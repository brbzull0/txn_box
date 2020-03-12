/** @file Feature modifiers.
 *
 * Copyright 2019, Oath Inc.
 * SPDX-License-Identifier: Apache-2.0
 */

#include "txn_box/Modifier.h"
#include "txn_box/Context.h"
#include "txn_box/Config.h"
#include "txn_box/Comparison.h"
#include "txn_box/yaml_util.h"

using swoc::TextView;
using swoc::Errata;
using swoc::Rv;
using namespace swoc::literals;

/// Static mapping from modifier to factory.
Modifier::Factory Modifier::_factory;

Errata Modifier::define(swoc::TextView name, Modifier::Worker const &f) {
  if (auto spot = _factory.find(name) ; spot == _factory.end()) {
    _factory.insert(spot, {name, f});
    return {};
  }
  return Error(R"(Modifier "{}" is already defined.)", name);
}

Rv<Modifier::Handle> Modifier::load(Config &cfg, YAML::Node const &node, ValueType ftype) {
  if (! node.IsMap()) {
    return Error(R"(Modifier at {} is not an object as required.)", node.Mark());
  }

  for ( auto const& [ key_node, value_node ] : node ) {
    TextView key { key_node.Scalar() };
    // See if @a key is in the factory.
    if ( auto spot { _factory.find(key) } ; spot != _factory.end()) {
      auto &&[handle, errata]{spot->second(cfg, node, value_node)};

      if (!errata.is_ok()) {
        return std::move(errata);
      }
      if (! handle->is_valid_for(ftype)) {
        return Error(R"(Modifier "{}" at {} cannot accept a feature of type "{}".)", key, node.Mark(), ftype);
      }

      return std::move(handle);
    }
  }
  return Error(R"(No valid modifier key in object at {}.)", node.Mark());
}

class Mod_Hash : public Modifier {
  using self_type = Mod_Hash;
  using super_type = Modifier;
public:
  static const std::string KEY; ///< Identifier name.

  /** Modify the feature.
   *
   * @param ctx Run time context.
   * @param feature Feature to modify [in,out]
   * @return Errors, if any.
   */
  Rv<Feature> operator()(Context& ctx, Feature const& feature) override;

  /** Check if @a ftype is a valid type to be modified.
   *
   * @param ftype Type of feature to modify.
   * @return @c true if this modifier can modity that feature type, @c false if not.
   */
  bool is_valid_for(ValueType ftype) const override;

  /// Resulting type of feature after modifying.
  ValueType result_type(ValueType) const override;

  /** Create an instance from YAML config.
   *
   * @param cfg Configuration state object.
   * @param mod_node Node with modifier.
   * @param key_node Node in @a mod_node that identifies the modifier.
   * @return A constructed instance or errors.
   */
  static Rv<Handle> load(Config& cfg, YAML::Node mod_node, YAML::Node key_node);

protected:
  unsigned _n = 0; ///< Number of hash buckets.

  /// Constructor for @c load.
  Mod_Hash(unsigned n);
};

const std::string Mod_Hash::KEY { "hash" };

Mod_Hash::Mod_Hash(unsigned n) : _n(n) {}

bool Mod_Hash::is_valid_for(ValueType ftype) const {
  return STRING == ftype;
}

ValueType Mod_Hash::result_type(ValueType) const {
  return INTEGER;
}

Rv<Feature> Mod_Hash::operator()(Context &ctx, Feature const& feature) {
  feature_type_for<INTEGER> value = std::hash<std::string_view>{}(std::get<IndexFor(STRING)>(feature));
  return Feature{feature_type_for<INTEGER>{value % _n}};
}

Rv<Modifier::Handle> Mod_Hash::load(Config &cfg, YAML::Node mod_node, YAML::Node key_node) {
  if (! key_node.IsScalar()) {
    return Error(R"(Value for "{}" at {} in modifier at {} is not a number as required.)", KEY, key_node.Mark(), mod_node.Mark());
  }
  TextView src{key_node.Scalar()}, parsed;
  src.trim_if(&isspace);
  auto n = swoc::svtou(src, &parsed);
  if (src.size() != parsed.size()) {
    return Error(R"(Value "{}" for "{}" at {} in modifier at {} is not a number as required.)", src, KEY, key_node.Mark(), mod_node.Mark());
  }
  if (n < 2) {
    return Error(R"(Value "{}" for "{}" at {} in modifier at {} must be at least 2.)", src, KEY, key_node.Mark(), mod_node.Mark());
  }

  return { Handle{new self_type(n)}, {} };
}

// ---
/// Filter a list.
class Mod_Filter : public Modifier {
  using self_type = Mod_Filter;
  using super_type = Modifier;
public:
  static constexpr TextView KEY = "filter"; ///< Identifier name.
  static constexpr TextView REPLACE_KEY = "replace"; ///< Replace element.
  static constexpr TextView DROP_KEY = "drop"; ///< Drop / remove element.
  static constexpr TextView PASS_KEY = "pass"; ///< Pass unalterated.

  /** Modify the feature.
   *
   * @param ctx Run time context.
   * @param feature Feature to modify [in,out]
   * @return Errors, if any.
   */
  Rv<Feature> operator()(Context& ctx, Feature const& feature) override;

  /** Check if @a ftype is a valid type to be modified.
   *
   * @param ftype Type of feature to modify.
   * @return @c true if this modifier can modify that feature type, @c false if not.
   */
  bool is_valid_for(ValueType ftype) const override;

  /// Resulting type of feature after modifying.
  ValueType result_type(ValueType in_type) const override;

  /** Create an instance from YAML config.
   *
   * @param cfg Configuration state object.
   * @param mod_node Node with modifier.
   * @param key_node Node in @a mod_node that identifies the modifier.
   * @return A constructed instance or errors.
   */
  static Rv<Handle> load(Config& cfg, YAML::Node mod_node, YAML::Node key_node);

protected:
  enum Action {
    PASS = 0, ///< No action
    DROP, ///< Remove element from result.
    REPLACE ///< Replace element in result.
  };

  /// A filter comparison case.
  struct Case {
    Action _action = PASS; ///< Action on match.
    Expr _expr; ///< Replacement expression, if any.
    Comparison::Handle _cmp; ///< Comparison.

    void assign(Comparison::Handle && handle) {
      _cmp = std::move(handle);
    }

    bool operator () (Context& ctx, Feature const& feature);

    Errata pre_load(Config & cfg, YAML::Node node);
  };

  ComparisonGroup<Case> _cases;

  Case const* compare(Context& ctx, Feature const& feature) const;
};

bool Mod_Filter::is_valid_for(ValueType) const {
  return true;
}

ValueType Mod_Filter::result_type(ValueType in_type) const {
  return in_type;
}

auto Mod_Filter::compare(Context& ctx, Feature const&feature) const -> Case const * {
  for ( auto const& c : _cases) {
    if (! c._cmp || (*c._cmp)(ctx, feature)) {
      return &c;
    }
  }
  return nullptr;
}

Rv<Feature> Mod_Filter::operator()(Context &ctx, Feature const& feature) {
  Action action;
  Feature zret;
  if (feature.is_list()) {
    auto src = std::get<IndexFor(TUPLE)>(feature);
    auto farray = static_cast<Feature*>(alloca(sizeof(Feature) * src.count()));
    feature_type_for<TUPLE> dst{farray, src.count() };
    unsigned dst_idx = 0;
    for ( Feature f = feature ; ! is_nil(f) ; f = cdr(f) ) {
      Feature item = car(f);
      auto c = _cases(ctx, item);
      Action action = ((c != _cases.end()) ? c->_action : DROP);
      switch (action) {
        case DROP:
          break;
        case PASS:
          dst[dst_idx++] = item;
          break;
        case REPLACE:
          dst[dst_idx++] = ctx.extract(c->_expr);
          break;
      }
    }
    auto span = ctx.span<Feature>(dst_idx);
    for ( unsigned idx = 0 ; idx < dst_idx ; ++idx) {
      span[idx] = dst[idx];
    }
    zret = span;
  } else {
    auto c = this->compare(ctx, feature);
    Action action = c ? c->_action : DROP;
    switch (action) {
      case DROP: zret = NIL_FEATURE; break;
      case PASS: zret = feature; break;
      case REPLACE: zret = ctx.extract(c->_expr); break;
    }
  }
  return zret;
}

Errata Mod_Filter::Case::pre_load(Config &cfg, YAML::Node cmp_node) {
  if (!cmp_node.IsMap()) {
    return Error("List element at {} for {} modifier is not a comparison object.", cmp_node.Mark(), KEY);
  }

  Expr replace_expr;
  unsigned action_count = 0;

  if (auto do_node = cmp_node[Global::DO_KEY] ; do_node) {
    return Error(R"("{}" at line {} is not allowed in a modifier comparison.)"
        , Global::DO_KEY, do_node.Mark()
    );
  }

  YAML::Node drop_node = cmp_node[DROP_KEY];
  if (drop_node) {
    _action = DROP;
    cmp_node.remove(DROP_KEY);
    ++action_count;
  }

  YAML::Node pass_node = cmp_node[PASS_KEY];
  if (pass_node) {
    _action = PASS;
    cmp_node.remove(PASS_KEY);
    ++action_count;
  }

  YAML::Node replace_node = cmp_node[REPLACE_KEY];
  if (replace_node) {
    auto &&[expr, errata] = cfg.parse_expr(replace_node);
    if (! errata.is_ok()) {
      errata.info("While parsing expression at {} for {} key in comparison at {}.", replace_node.Mark(), REPLACE_KEY, cmp_node.Mark());
      return std::move(errata);
    }
    _expr = std::move(expr);
    _action = REPLACE;
    cmp_node.remove(REPLACE_KEY);
    ++action_count;
  }

  if (action_count > 1) {
    return Error("Only one of {}, {}, {} is allowed in the {} comparison at {}.", REPLACE_KEY, DROP_KEY, PASS_KEY, KEY, cmp_node.Mark());
  }

  return {};
}

bool Mod_Filter::Case::operator()(Context& ctx, Feature const& feature) {
  return ! _cmp || (*_cmp)(ctx, feature);
}

Rv<Modifier::Handle> Mod_Filter::load(Config &cfg, YAML::Node mod_node, YAML::Node key_node) {
  auto self = new self_type;
  Handle handle(self);

  if (auto errata = self->_cases.load(cfg, key_node) ; ! errata.is_ok()) {
    errata.info(R"(While parsing modifier "{}" at line {}.)", KEY, mod_node.Mark());
  }

  return std::move(handle);
}

// ---

/// Replace the feature with another feature if the input is nil or empty.
class Mod_Else : public Modifier {
  using self_type = Mod_Else;
  using super_type = Modifier;
public:
  static constexpr TextView KEY { "else" }; ///< Identifier name.

  /** Modify the feature.
   *
   * @param ctx Run time context.
   * @param feature Feature to modify [in,out]
   * @return Errors, if any.
   */
  Rv<Feature> operator()(Context& ctx, Feature const& feature) override;

  /** Check if @a ftype is a valid type to be modified.
   *
   * @param ftype Type of feature to modify.
   * @return @c true if this modifier can modity that feature type, @c false if not.
   */
  bool is_valid_for(ValueType ftype) const override;

  /// Resulting type of feature after modifying.
  ValueType result_type(ValueType) const override;

  /** Create an instance from YAML config.
   *
   * @param cfg Configuration state object.
   * @param mod_node Node with modifier.
   * @param key_node Node in @a mod_node that identifies the modifier.
   * @return A constructed instance or errors.
   */
  static Rv<Handle> load(Config& cfg, YAML::Node mod_node, YAML::Node key_node);

protected:
  Expr _value;

  explicit Mod_Else(Expr && fmt) : _value(std::move(fmt)) {}
};

bool Mod_Else::is_valid_for(ValueType ftype) const {
  return STRING == ftype || NIL == ftype;
}

ValueType Mod_Else::result_type(ValueType) const {
  return _value.result_type();
}

Rv<Feature> Mod_Else::operator()(Context &ctx, Feature const& feature) {
  return is_empty(feature) ? ctx.extract(_value) : feature;
}

Rv<Modifier::Handle> Mod_Else::load(Config &cfg, YAML::Node mod_node, YAML::Node key_node) {
  auto && [ fmt, errata ] { cfg.parse_expr(key_node) };
  if (! errata.is_ok()) {
    errata.info(R"(While parsing "{}" modifier at {}.)", KEY, key_node.Mark());
    return std::move(errata);
  }
  return Handle(new self_type{std::move(fmt)});
};

// --- //

/// Convert the feature to an Integer.
class Mod_As_Integer : public Modifier {
  using self_type = Mod_As_Integer;
  using super_type = Modifier;
public:
  static const std::string KEY; ///< Identifier name.

  /** Modify the feature.
   *
   * @param ctx Run time context.
   * @param feature Feature to modify [in,out]
   * @return Errors, if any.
   */
  Rv<Feature> operator()(Context& ctx, Feature const& feature) override;

  /** Check if @a ftype is a valid type to be modified.
   *
   * @param ftype Type of feature to modify.
   * @return @c true if this modifier can modity that feature type, @c false if not.
   */
  bool is_valid_for(ValueType ftype) const override;

  /// Resulting type of feature after modifying.
  ValueType result_type(ValueType) const override;

  /** Create an instance from YAML config.
   *
   * @param cfg Configuration state object.
   * @param mod_node Node with modifier.
   * @param key_node Node in @a mod_node that identifies the modifier.
   * @return A constructed instance or errors.
   */
  static Rv<Handle> load(Config& cfg, YAML::Node mod_node, YAML::Node key_node);

protected:
  Expr _value; ///< Default value.

  explicit Mod_As_Integer(Expr && fmt) : _value(std::move(fmt)) {}

  /// Identity conversion.
  Feature convert(Context & ctx, feature_type_for<INTEGER> n) { return n; }
  /// Convert from string
  Feature convert(Context & ctx, feature_type_for<STRING> s) {
    TextView parsed;
    s.trim_if(&isspace);
    auto n = swoc::svtoi(s, &parsed);
    if (parsed.size() == s.size()) {
      return n;
    }
    return ctx.extract(_value);
  }

  /// Generic failure case.
  template < typename T > auto convert(Context & ctx, T & t) -> EnableForFeatureTypes<T, Feature> {
    return ctx.extract(_value);
  }
};

const std::string Mod_As_Integer::KEY { "as-integer" };

bool Mod_As_Integer::is_valid_for(ValueType ftype) const {
  return STRING == ftype || INTEGER == ftype;
}

ValueType Mod_As_Integer::result_type(ValueType) const {
  return INTEGER;
}

Rv<Feature> Mod_As_Integer::operator()(Context &ctx, Feature const& feature) {
  auto visitor = [&](auto & t) { return this->convert(ctx, t); };
  return std::visit(visitor, feature);
}

Rv<Modifier::Handle> Mod_As_Integer::load(Config &cfg, YAML::Node mod_node, YAML::Node key_node) {
  auto && [ fmt, errata ] { cfg.parse_expr(key_node) };
  if (! errata.is_ok()) {
    errata.info(R"(While parsing "{}" modifier at {}.)", KEY, key_node.Mark());
    return std::move(errata);
  }
  return Handle(new self_type{std::move(fmt)});
};

// --- //

/// Convert the feature to an IP address.
class Mod_As_IP_Addr : public Modifier {
  using self_type = Mod_As_IP_Addr;
  using super_type = Modifier;
public:
  static const std::string KEY; ///< Identifier name.

  /** Modify the feature.
   *
   * @param ctx Run time context.
   * @param feature Feature to modify [in,out]
   * @return Errors, if any.
   */
  Rv<Feature> operator()(Context& ctx, Feature const& feature) override;

  /** Check if @a ftype is a valid type to be modified.
   *
   * @param ftype Type of feature to modify.
   * @return @c true if this modifier can modity that feature type, @c false if not.
   */
  bool is_valid_for(ValueType ftype) const override;

  /// Resulting type of feature after modifying.
  ValueType result_type(ValueType) const override;

  /** Create an instance from YAML config.
   *
   * @param cfg Configuration state object.
   * @param mod_node Node with modifier.
   * @param key_node Node in @a mod_node that identifies the modifier.
   * @return A constructed instance or errors.
   */
  static Rv<Handle> load(Config& cfg, YAML::Node mod_node, YAML::Node key_node);

protected:
  explicit Mod_As_IP_Addr() = default;

  /// Identity conversion.
  Feature convert(Context & ctx, feature_type_for<IP_ADDR> n) { return n; }
  /// Convert from string
  Feature convert(Context & ctx, feature_type_for<STRING> s) {
    swoc::IPAddr addr{s};
    return addr.is_valid() ? Feature{addr} : NIL_FEATURE;
  }

  /// Generic failure case.
  template < typename T > auto convert(Context & ctx, T & t) -> EnableForFeatureTypes<T, Feature> {
    return NIL_FEATURE;
  }
};

const std::string Mod_As_IP_Addr::KEY { "as-ip-addr" };

bool Mod_As_IP_Addr::is_valid_for(ValueType ftype) const {
  return STRING == ftype || IP_ADDR == ftype;
}

ValueType Mod_As_IP_Addr::result_type(ValueType) const {
  return IP_ADDR;
}

Rv<Feature> Mod_As_IP_Addr::operator()(Context &ctx, Feature const& feature) {
  auto visitor = [&](auto & t) { return this->convert(ctx, t); };
  return std::visit(visitor, feature);
}

Rv<Modifier::Handle> Mod_As_IP_Addr::load(Config &cfg, YAML::Node mod_node, YAML::Node key_node) {
  return Handle(new self_type);
};

// --- //

namespace {
[[maybe_unused]] bool INITIALIZED = [] () -> bool {
  Modifier::define(Mod_Hash::KEY, &Mod_Hash::load);
  Modifier::define(Mod_Else::KEY, &Mod_Else::load);
  Modifier::define(Mod_As_Integer::KEY, &Mod_As_Integer::load);
  Modifier::define(Mod_Filter::KEY, &Mod_Filter::load);
  return true;
} ();
} // namespace