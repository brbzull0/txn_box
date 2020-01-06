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

// Forward references.
class Extractor;

/// Parsed feature expression.
class Expr {
  using self_type = Expr; ///< Self reference type.
public:
  Expr() = default;
  Expr(self_type const& that) = delete;
  Expr(self_type && that) = default;
  self_type & operator = (self_type const& that) = delete;
  self_type & operator = (self_type && that) = default;

  /** Featire Expression specifier.
   * This is a subclass of the base format specifier, in order to add a field that points at
   * the extractor, if any, for the specifier.
   */
  struct Spec : public swoc::bwf::Spec {
    /// Extractor used in the spec, if any.
    Extractor * _exf = nullptr;
    /// Config storage for extractor, if needed.
    swoc::MemSpan<void> _data;
  };

  /// Single extractor that generates a direct view.
  /// Always a @c STRING
  struct Direct {
    Spec _spec; ///< Specifier with extractor.
  };

  /// A composite of extractors and literals.
  struct Composite {
    /// Type of feature extracted by this format.
    ValueType _result_type = ValueType::STRING;

    /// @c true if the extracted feature should be forced to a C-string.
    /// @note This only applies for @c STRING features.
    bool _force_c_string_p = false;

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

  /// Concrete types for a specific expresion.
  std::variant<std::monostate, Feature, Direct, Composite, Tuple> _expr;
  /// Post extraction modifiers.
  std::vector<Modifier::Handle> _mods;

  bool is_literal() const { return _expr.index() == 0 || _expr.index() == 1; }
};
