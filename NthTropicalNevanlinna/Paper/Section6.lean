import NthTropicalNevanlinna.Truncated.FiniteRoots
import NthTropicalNevanlinna.Truncated.Main

/-!
# Paper guide: Section 6

## Main objects

* `forwardShift`, `tropicalTensor`, and `tropicalCasoratian`.
* `curveHyperOrder`, `truncatedSecondMainScale`, and the paper-facing
  hypothesis/conclusion structures for Theorem 6.2.

## Main results, in paper order

* Finite-root identity (empty root sets are allowed):
  `finiteRootCasoratian_countingDifference_isBigO_one`,
  `finiteRootCasoratian_firstOrder_identity`, and
  `finiteRootCasoratian_firstOrder_multiplicative`.
  `finiteRootCasoratianData` constructs the affine tails and Casoratian root
  data from finite coordinate root sets, including a constant Casoratian.
  The exact affine identities remain available through
  `FiniteFirstOrderRootData.integratedRootCounting_eq_affine` and
  `FiniteRootCasoratianData.countingDifference_eventually_constant`.
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
