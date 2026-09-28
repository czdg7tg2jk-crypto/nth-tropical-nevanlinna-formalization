import NthTropicalNevanlinna.LogDerivative.Main

/-!
# Paper guide: Section 4

## Main objects

* `IsWellDefinedPolynomial` and
  `IsWellDefinedNthTropicalMeromorphicFunction` (Definition 4.2).
* `HasFiniteLogarithmicMeasure` and `atTopOutside`, the precise exceptional-set
  language used by the asymptotic results.

## Main results, in paper order

* Lemma 4.3: `wellDefinedPolynomial_iteratedDeriv_commonSign`.
* Lemma 4.4: `characteristicLemma44`; this packages derivative
  nonnegativity, monotonicity, and convexity of the characteristic.
* Displayed shift estimate: `pointwiseShiftEstimate_of_wellDefined`.
* Growth-shift lemma: `growthShiftLemma`.
* Pointwise logarithmic-derivative theorem:
  `pointwiseLogarithmicDerivative`.
* Logarithmic-derivative proximity corollary:
  `logarithmicDerivativeProximity`.

## Technical implementation

Local characteristic splines, event certificates, reflection arguments, and
the exponential-annulus exceptional-set construction stay encapsulated in
`LogDerivative/`.
-/

namespace NthTropicalNevanlinna.Paper.Section4

end NthTropicalNevanlinna.Paper.Section4
