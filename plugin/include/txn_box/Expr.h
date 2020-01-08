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
  Expr(Feature const& f) : _expr(f) {}

  Expr(Spec const& spec) {
    if (spec._exf && spec._exf->is_direct()) {
      _expr.emplace<DIRECT>(spec);
    } else {
      auto & comp { _expr.emplace<Expr::COMPOSITE>() };
      comp._specs.push_back(spec);
      comp._result_type = spec._exf->result_type();
    }
  }

  /// Single extractor that generates a direct view.
  /// Always a @c STRING
  struct Direct {
    Direct(Spec const& spec) : _spec(spec) {}
    Spec _spec; ///< Specifier with extractor.
  };

  /// A composite of extractors and literals.
  struct Composite {
    /// Type of feature extracted by this format.
    ValueType _result_type = ValueType::STRING;

    int _max_arg_idx = -1; ///< Largest argument index. -1 => no numbered arguments.

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

  /// Post extraction modifiers.
  std::vector<Modifier::Handle> _mods;

  bool is_literal() const { return _expr.index() == NIL || _expr.index() == FEATURE; }

  static self_type make_direct(Spec const& spec) {
    Expr expr;
    expr._expr.emplace<DIRECT>(spec);
    return std::move(expr);
  }

};
