import NthTropicalNevanlinna.Curves.FermatExamples

/-!
# Paper guide: Section 5

## Main objects

* `TropicalProjectiveSpace`, `TropicalHolomorphicCurveRepresentation`, and
  `NthTropicalHolomorphicCurve`.
* `cartanCharacteristic` and reduced curve representations.
* `HomogeneousTropicalPolynomial`,
  `TropicalHomogeneousFermatPolynomial`, and
  `OrdinaryHomogeneousFermatPolynomial`.

## Main results, in paper order

* Proposition 5.2:
  `cartanCharacteristic_eq_of_reduced_projectiveValue_eq_arbitraryOrders`
  compares reduced representations even when their coordinate orders differ.
  `cartanCharacteristic_eq_of_reducedCurveRepresentations` remains available
  for representations of one fixed-order curve.
* Proposition 5.3:
  `cartanCharacteristic_projectivePair_eq_characteristic_sub_arbitraryOrders`
  uses Proposition 2.3 and representation invariance, without equating the
  quotient order with the maximum coordinate order. The same-order interfaces
  remain available for compatibility.
* Proposition 5.4:
  `characteristic_coordinateQuotient_le_upToConstant`.
* Theorem 5.6: `secondMain_homogeneousTropicalPolynomial`.
* Corollary 5.7: `secondMain_firstOrder_tropicalFermat`.
* Theorem 5.8: `secondMain_ordinaryFermat`.
* Examples 5.9 and 5.10:
  `example59_ambientReciprocalCounting` and
  `example510_concrete_conclusions`.

## Technical implementation

Finite-support polynomial evaluation, automatic composition realizations,
power-multiplicity estimates, and tail bounds are kept under `Curves/`.
-/

namespace NthTropicalNevanlinna.Paper.Section5

end NthTropicalNevanlinna.Paper.Section5
