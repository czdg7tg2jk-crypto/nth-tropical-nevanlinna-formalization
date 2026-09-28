import NthTropicalNevanlinna.Function.Tropicalization
import NthTropicalNevanlinna.Function.EntireMean
import NthTropicalNevanlinna.Function.Decomposition

/-!
# Paper guide: Section 2

This module is the reader-facing entry point for Section 2 of the paper.
It contains no duplicate definitions: the declarations below are implemented
in the imported dependency-oriented modules.

## Main objects

* `PolynomialPresentation`, `IsNthTropicalMeromorphicFunction`, and
  `NthTropicalMeromorphicFunction`: continuous piecewise-polynomial functions
  of exact ambient order `n`.
* `multiplicity`, `IsJthRoot`, and `IsJthPole`: intrinsic one-sided jet jumps.
* `IsTropicalEntire` and `IsTropicalNowhereVanishingEntire`.

## Main results, in paper order

* Section 2 tropicalization:
  `activeDequantizedNthTropicalSource_tropicalizesTo` and
  `nthTropicalizesTo_add`, `nthTropicalizesTo_mul`, `nthTropicalizesTo_div`.
* Proposition 2.2:
  `entire_midpoint_le_endpointMean` and
  `nowhereVanishingEntire_endpointMean_eq`.
* Proposition 2.3:
  `exists_entire_quotient_decomposition`.

## Technical implementation

Polynomial jets, spline assembly, presentation closure, and the construction
of numerator/denominator functions remain encapsulated in `Function/`.
-/

namespace NthTropicalNevanlinna.Paper.Section2

end NthTropicalNevanlinna.Paper.Section2
