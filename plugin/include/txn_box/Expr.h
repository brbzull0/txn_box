/** @file
 * Feature Expression.
 *
 * Copyright 2020, Oath Inc.
 * SPDX-License-Identifier: Apache-2.0
 */

#pragma once

#include <string_view>
#include <variant>

#include <swoc/bwf_base.h>

#include "txn_box/Modifier.h"
#include "txn_box/Extractor.h"

/// Parsed feature expression.
class Expr {
  using self_type = Expr; ///< Self reference type.
  using Spec = Extractor::Spec; ///< Import for convenience.
public:
  Expr() = default;
  Expr(self_type const& that) = delete;
  Expr(self_type && that) = default;
  self_type & operator = (self_type const& that) = delete;
  self_type & operator = (self_type && that) = default;

  /** Construct from a Feature.
   *
   * @param f Feature that is the result of the expression.
   *
   * The constructed instance will always be the literal @a f.
   */
  Expr(Feature const& f) : _expr(f), _result_type(ValueTypeOf(f)) {}

  Expr(Spec const& spec) {
    if (spec._exf && spec._exf->is_direct()) {
      _expr.emplace<DIRECT>(spec);
    } else {
      auto & comp { _expr.emplace<Expr::COMPOSITE>() };
      comp._specs.push_back(spec);
      _result_type = spec._exf->result_type();
      _max_arg_idx = spec._idx;
    }
  }

  /// Output generator for BWF on an expression.
  class bwf_ex {
  public:
    /// Construct with specifier sequence.
    bwf_ex(std::vector<Spec> const& specs) : _specs(specs), _iter(specs.begin()) {}

    /// Validity check.
    explicit operator bool() const { return _iter != _specs.end(); }
    ///
    bool operator()(std::string_view& literal, Spec & spec);
  protected:
    std::vector<Spec> const& _specs; ///< Specifiers in format.
    std::vector<Spec>::const_iterator _iter; ///< Current specifier.
  };

  /// Single extractor that generates a direct view.
  /// Always a @c STRING
  struct Direct {
    Direct(Spec const& spec) : _spec(spec) {}
    Spec _spec; ///< Specifier with extractor.
  };

  /// A composite of extractors and literals.
  struct Composite {
    /// Specifiers / elements of the parsed format string.
    std::vector<Spec> _specs;

    /** Access a format element by index.
     *
     * @param idx Element index.
     * @return A reference to the element.
     */
    Spec& operator [] (size_t idx);

    /** Access a format element by index.
     *
     * @param idx Element index.
     * @return A reference to the element.
     */
    Spec const& operator [] (size_t idx) const;

  };

  struct Tuple {
    /// Expressions which are the elements of the tuple.
    std::vector<std::unique_ptr<self_type>> _exprs;
  };

  /// Concrete types for a specific expression.
  std::variant<std::monostate, Feature, Direct, Composite, Tuple> _expr;
  /// Enumerations for type indices.
  enum {
    NIL = 0,
    FEATURE = 1,
    DIRECT = 2,
    COMPOSITE = 3,
    TUPLE = 4
  };

  /// Feature type resulting from extraction of this expression.
  ValueType _result_type = STRING;
  /// Contains an extractor the references context data.
  bool _ctx_ref_p = false;
  ///< Largest argument index. -1 => no numbered arguments.
  int _max_arg_idx = -1;

  /// Post extraction modifiers.
  std::vector<Modifier::Handle> _mods;

  bool is_literal() const { return _expr.index() == NIL || _expr.index() == FEATURE; }

  struct bwf_visitor {
    bwf_visitor(Context & ctx) : _ctx(ctx) {}

    Feature operator () (std::monostate const& nil) { return NIL_FEATURE; }
    Feature operator () (Feature const& f) { return f; }
    Feature operator () (Direct const& d) {
      return static_cast<DirectFeature *>(d._spec._exf)->direct_view(_ctx, d._spec);
    }
    Feature operator () (Composite const& comp);
    Feature operator () (Tuple const& tuple) {
      return NIL_FEATURE;
    }

    Context& _ctx;
  };
};
