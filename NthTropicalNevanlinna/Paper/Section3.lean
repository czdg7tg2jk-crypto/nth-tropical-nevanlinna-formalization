import NthTropicalNevanlinna.PoissonJensen.Main
import NthTropicalNevanlinna.Nevanlinna.Counting
import NthTropicalNevanlinna.Nevanlinna.Jensen
import NthTropicalNevanlinna.Nevanlinna.Growth
import NthTropicalNevanlinna.Nevanlinna.Examples

/-!
# Paper guide: Section 3

## Main objects

* `proximity`, `maxPlusCounting`, `integratedCounting`,
  `partialIntegratedCounting`, and `characteristic`.
* `growthOrder` and `hyperOrder`.
* `tropicalHyperExponential`.

## Main results, in paper order

* Lemma 3.1: `endpoint_sub_eq_jet_sum` and
  `sub_leftEndpoint_eq_jet_sum`; intrinsic singularity-only versions live in
  `PoissonJensen/IntrinsicTelescoping.lean`.
* Lemma 3.2: `auxiliaryJump_eq_byRegion`.
* Theorem 3.3: `poissonJensen`, with `jensenFormula` as its `x = 0`
  specialization.
* Counting sum--integral identities:
  `countingBoxIntegrand_eq_maxPlusCounting_minimum`,
  `integratedCounting_eq_iteratedIntegral`, and
  `integratedCounting_eq_paperIteratedIntegral`.
  Regional restrictions are exposed by `partialIntegratedCounting` and
  `partialIntegratedRootCounting`.
* Theorem 3.5: `characteristic_eq_neg_add_at_zero`.
* Definition 3.7 and Proposition 3.8:
  `tropicalHyperExponential` and `proposition_3_8`.

## Technical implementation

The kernels `B_k`, `D_k`, `E`, the nine regions, and the auxiliary jumps
`Omega`, `Gamma` are proof-local APIs under `PoissonJensen/`; they are not
independent headline objects.
-/

namespace NthTropicalNevanlinna.Paper.Section3

end NthTropicalNevanlinna.Paper.Section3
