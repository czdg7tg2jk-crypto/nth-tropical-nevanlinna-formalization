import NthTropicalNevanlinna.Truncated.FiniteRoots
import NthTropicalNevanlinna.Truncated.Main

/-!
# Paper guide: Section 6

## Main objects

* `forwardShift`, `tropicalTensor`, and `tropicalCasoratian`.
* `curveHyperOrder`, `truncatedSecondMainScale`, and the paper-facing
  hypothesis/conclusion structures for Theorem 6.2.

## Main results, in paper order

* Finite-root identity:
  `FiniteFirstOrderRootData.integratedRootCounting_eq_affine`,
  `FiniteRootCasoratianData.countingDifference_eventually_constant`, and
  `FiniteRootCasoratianData.casoratianCounting_isEquivalent_coordinateCountingSum`.
* Lemma 6.1:
  `tropicalCasoratian_commonFactor` and
  `casoratian_commonFactor_of_entire`.
* Theorem 6.2:
  `truncatedSecondMain` and
  `truncatedSecondMainPaperStatement_verified`.
* Corollary 6.3:
  `firstOrderTruncatedSecondMainPaperStatement_verified`.

## Technical implementation

Shift realizations, odd/even multiplicity transport, partial-counting
corrections, and the two little-o remainders remain under `Truncated/`.
Conditional assembly interfaces are retained for reuse, but the paper-facing
theorems construct all of their fields from the original hypotheses.
-/

namespace NthTropicalNevanlinna.Paper.Section6

end NthTropicalNevanlinna.Paper.Section6
