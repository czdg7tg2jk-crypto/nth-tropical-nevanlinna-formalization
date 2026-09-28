import NthTropicalNevanlinna.Truncated.ShiftCounting
import NthTropicalNevanlinna.LogDerivative.WellDefined
import NthTropicalNevanlinna.LogDerivative.Main

/-!
# The exact Jensen assembly for Theorem 6.2

The proof of Theorem 6.2 has two logically different parts.  Jensen's
formula, the triangle inequality, and the pole-count rearrangement are exact;
they are proved in this file.  The exact projective/permutation core of
`(equa2)` is also proved below, while `TranslationMultiplicity.lean` supplies
the local multiplicity transport used by `(equa1)`.  The two global little-o
estimates are then derived from the growth/logarithmic-derivative lemmas.
Finally, nonconstancy of the curve yields a nonconstant reference quotient;
its convex characteristic supplies the affine lower growth needed to derive
both internal nondegenerate limits from the original paper hypotheses.
-/

namespace NthTropicalNevanlinna

noncomputable section

open Filter Set
open scoped BigOperators Topology

/-- The little-o scale in Theorem 6.2. -/
def truncatedSecondMainScale {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) (σ r : ℝ) : ℝ :=
  cartanCharacteristic F r / r ^ σ

/-- The curve analogue of `hyperOrderQuotient`, using `T_F` in place of the
one-function characteristic. -/
def curveHyperOrderQuotient {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) (r : ℝ) : EReal :=
  ((Real.log (Real.log (cartanCharacteristic F r)) / Real.log r : ℝ) : EReal)

/-- The hyperorder `ρ₂(F)` in hypothesis `(6f1)`. -/
def curveHyperOrder {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) : EReal :=
  Filter.limsup (curveHyperOrderQuotient F) Filter.atTop

/-- Witnesses for the paper's statement that one index `l` makes every
coordinate quotient `fᵢ ⊘ f_l` a well-defined tropical meromorphic function.
The order may drop below the ambient curve order. -/
structure CurveWellDefinedReferenceQuotients {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) where
  reference : Fin (m + 1)
  quotientOrder : Fin (m + 1) → ℕ
  quotientOrder_le : ∀ i, quotientOrder i ≤ n
  quotient : ∀ i, NthTropicalMeromorphicFunction (quotientOrder i)
  quotient_eq : ∀ i x,
    quotient i x = F.eval i x - F.eval reference x
  quotient_wellDefined : ∀ i,
    IsWellDefinedNthTropicalMeromorphicFunction (quotient i)

/-- The original non-construction hypotheses of Theorem 6.2, with the real
number denoted `ρ₂` in the paper made explicit.  The paper globally declares
its tropical meromorphic functions, and hence its holomorphic curves, to be
nonconstant unless explicitly stated otherwise; `nonconstant` records that
convention rather than adding a new mathematical assumption. -/
structure TruncatedSecondMainPaperHypotheses {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) (σ : ℝ) where
  reduced : F.IsReduced
  nonconstant : F.IsNonconstant
  quotients : CurveWellDefinedReferenceQuotients F
  rho2 : ℝ
  hyperOrder_eq : curveHyperOrder F = (rho2 : EReal)
  rho2_lt_one : rho2 < 1
  sigma_pos : 0 < σ
  sigma_lt_one_sub_rho2 : σ < 1 - rho2

/-- An internal growth package used by the analytic assembly.  The two limits
are now derived below from the paper hypotheses; retaining this structure
keeps the remainder lemmas modular. -/
structure TruncatedSecondMainNondegenerateHypotheses {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) (σ : ℝ)
    extends TruncatedSecondMainPaperHypotheses F σ where
  characteristic_tendsto_atTop :
    Tendsto (cartanCharacteristic F) atTop atTop
  scale_tendsto_atTop :
    Tendsto (truncatedSecondMainScale F σ) atTop atTop

/-- The finite endpoint majorant obtained by applying the logarithmic
derivative estimate to every pair of shifts of every reference quotient. -/
def referenceQuotientPairwiseShiftVariation {n m : ℕ}
    {F : TropicalHolomorphicCurveRepresentation n m}
    (Q : CurveWellDefinedReferenceQuotients F) (x : ℝ) : ℝ :=
  casoratianPairwiseShiftVariation (fun i y ↦ Q.quotient i y) x

/-- Finite-sum closure for the endpoint kernel: pairwise little-o estimates
for all quotient shifts give a little-o estimate for the whole Casoratian
variation at the positive endpoint. -/
theorem referenceQuotientPairwiseShiftVariation_isLittleO_of_pairwise
    {n m : ℕ} {F : TropicalHolomorphicCurveRepresentation n m}
    (Q : CurveWellDefinedReferenceQuotients F) (σ : ℝ) (E : Set ℝ)
    (hpair : ∀ i k : Fin (m + 1),
      (fun r ↦ |Q.quotient i (r + k) - Q.quotient i (r + i)|) =o[
        atTopOutside E] truncatedSecondMainScale F σ) :
    referenceQuotientPairwiseShiftVariation Q =o[atTopOutside E]
      truncatedSecondMainScale F σ := by
  unfold referenceQuotientPairwiseShiftVariation
    casoratianPairwiseShiftVariation forwardShift
  exact Asymptotics.IsLittleO.sum (fun i _hi ↦
    Asymptotics.IsLittleO.sum (fun k _hk ↦ hpair i k))

/-- The corresponding finite-sum closure at the negative endpoint. -/
theorem referenceQuotientPairwiseShiftVariation_neg_isLittleO_of_pairwise
    {n m : ℕ} {F : TropicalHolomorphicCurveRepresentation n m}
    (Q : CurveWellDefinedReferenceQuotients F) (σ : ℝ) (E : Set ℝ)
    (hpair : ∀ i k : Fin (m + 1),
      (fun r ↦ |Q.quotient i (-r + k) - Q.quotient i (-r + i)|) =o[
        atTopOutside E] truncatedSecondMainScale F σ) :
    (fun r ↦ referenceQuotientPairwiseShiftVariation Q (-r)) =o[
      atTopOutside E] truncatedSecondMainScale F σ := by
  unfold referenceQuotientPairwiseShiftVariation
    casoratianPairwiseShiftVariation forwardShift
  exact Asymptotics.IsLittleO.sum (fun i _hi ↦
    Asymptotics.IsLittleO.sum (fun k _hk ↦ hpair i k))

/-- Both radial signs and the harmless factor `1/2` are assembled here.
Consequently the endpoint remainder in Theorem 6.2 reduces to the individual
pairwise quotient-shift estimates. -/
theorem referenceQuotientEndpointVariation_isLittleO_of_pairwise
    {n m : ℕ} {F : TropicalHolomorphicCurveRepresentation n m}
    (Q : CurveWellDefinedReferenceQuotients F) (σ : ℝ) (E : Set ℝ)
    (hplus : ∀ i k : Fin (m + 1),
      (fun r ↦ |Q.quotient i (r + k) - Q.quotient i (r + i)|) =o[
        atTopOutside E] truncatedSecondMainScale F σ)
    (hminus : ∀ i k : Fin (m + 1),
      (fun r ↦ |Q.quotient i (-r + k) - Q.quotient i (-r + i)|) =o[
        atTopOutside E] truncatedSecondMainScale F σ) :
    (fun r ↦ (referenceQuotientPairwiseShiftVariation Q r +
        referenceQuotientPairwiseShiftVariation Q (-r)) / 2) =o[
      atTopOutside E] truncatedSecondMainScale F σ := by
  have hsum :=
    (referenceQuotientPairwiseShiftVariation_isLittleO_of_pairwise
      Q σ E hplus).add
      (referenceQuotientPairwiseShiftVariation_neg_isLittleO_of_pairwise
        Q σ E hminus)
  simpa [div_eq_mul_inv, mul_comm] using hsum.const_mul_left (2 : ℝ)⁻¹

/-- Pointwise algebraic core of `(equa2)`.  A common reference coordinate
cancels exactly, after which the finite Casoratian maximum is controlled by
the pairwise shift variations of the well-defined quotients. -/
theorem casoratian_sub_diagonal_le_referenceQuotientVariation
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (S : CurveShiftRealizations F) (C : CurveCasoratianRealization F)
    (Q : CurveWellDefinedReferenceQuotients F) (x : ℝ) :
    |C.function x - ∑ i : Fin (m + 1), S.shifted i i x| ≤
      referenceQuotientPairwiseShiftVariation Q x := by
  classical
  have hraw :
      C.function x - ∑ i : Fin (m + 1), S.shifted i i x =
        tropicalCasoratian (fun i y ↦ F.eval i y) x -
          ∑ i : Fin (m + 1),
            forwardShift (fun y ↦ F.eval i y) i x := by
    rw [C.eq_casoratian]
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    exact S.eq_forwardShift i i x
  rw [hraw,
    tropicalCasoratian_sub_diagonal_eq_of_referenceQuotients
      (fun i y ↦ F.eval i y) (fun i y ↦ Q.quotient i y)
      (fun y ↦ F.eval Q.reference y) Q.quotient_eq x]
  exact abs_tropicalCasoratian_sub_diagonal_le_pairwiseVariation
    (fun i y ↦ Q.quotient i y) x

/-- The exact centered endpoint estimate behind `(equa2)`, including the
fixed center term which the paper denotes by `O(1)`. -/
theorem casoratianCenteredEndpointDefect_le_referenceQuotientVariation
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (S : CurveShiftRealizations F) (C : CurveCasoratianRealization F)
    (Q : CurveWellDefinedReferenceQuotients F) (r : ℝ) :
    casoratianCenteredEndpointDefect F S C r ≤
      (referenceQuotientPairwiseShiftVariation Q r +
          referenceQuotientPairwiseShiftVariation Q (-r)) / 2 +
        |C.function 0 - ∑ i : Fin (m + 1), S.shifted i i 0| := by
  classical
  have hplus := casoratian_sub_diagonal_le_referenceQuotientVariation
    F S C Q r
  have hminus := casoratian_sub_diagonal_le_referenceQuotientVariation
    F S C Q (-r)
  unfold casoratianCenteredEndpointDefect centeredEndpointMean
  have hsum :
      (∑ i : Fin (m + 1),
          ((S.shifted i i r + S.shifted i i (-r)) / 2 -
            S.shifted i i 0)) =
        ((∑ i : Fin (m + 1), S.shifted i i r) +
          ∑ i : Fin (m + 1), S.shifted i i (-r)) / 2 -
          ∑ i : Fin (m + 1), S.shifted i i 0 := by
    calc
      (∑ i : Fin (m + 1),
          ((S.shifted i i r + S.shifted i i (-r)) / 2 -
            S.shifted i i 0)) =
          (∑ i : Fin (m + 1),
            (S.shifted i i r + S.shifted i i (-r)) / 2) -
            ∑ i : Fin (m + 1), S.shifted i i 0 :=
        by
          simpa using (Finset.sum_sub_distrib
            (s := Finset.univ)
            (fun i : Fin (m + 1) ↦
              (S.shifted i i r + S.shifted i i (-r)) / 2)
            (fun i : Fin (m + 1) ↦ S.shifted i i 0))
      _ = (∑ i : Fin (m + 1),
            (S.shifted i i r + S.shifted i i (-r))) / 2 -
            ∑ i : Fin (m + 1), S.shifted i i 0 := by
        rw [Finset.sum_div]
      _ = ((∑ i : Fin (m + 1), S.shifted i i r) +
            ∑ i : Fin (m + 1), S.shifted i i (-r)) / 2 -
            ∑ i : Fin (m + 1), S.shifted i i 0 := by
        rw [Finset.sum_add_distrib]
  have hrearrange :
      (C.function r + C.function (-r)) / 2 - C.function 0 -
          (∑ i : Fin (m + 1),
            ((S.shifted i i r + S.shifted i i (-r)) / 2 -
              S.shifted i i 0)) =
        ((C.function r - ∑ i : Fin (m + 1), S.shifted i i r) +
          (C.function (-r) -
            ∑ i : Fin (m + 1), S.shifted i i (-r))) / 2 -
          (C.function 0 - ∑ i : Fin (m + 1), S.shifted i i 0) := by
    rw [hsum]
    ring
  rw [hrearrange]
  calc
    |((C.function r - ∑ i : Fin (m + 1), S.shifted i i r) +
          (C.function (-r) -
            ∑ i : Fin (m + 1), S.shifted i i (-r))) / 2 -
        (C.function 0 - ∑ i : Fin (m + 1), S.shifted i i 0)| ≤
      (|C.function r - ∑ i : Fin (m + 1), S.shifted i i r| +
          |C.function (-r) -
            ∑ i : Fin (m + 1), S.shifted i i (-r)|) / 2 +
        |C.function 0 - ∑ i : Fin (m + 1), S.shifted i i 0| := by
      calc
        |((C.function r - ∑ i : Fin (m + 1), S.shifted i i r) +
              (C.function (-r) -
                ∑ i : Fin (m + 1), S.shifted i i (-r))) / 2 -
            (C.function 0 - ∑ i : Fin (m + 1), S.shifted i i 0)| ≤
          |((C.function r - ∑ i : Fin (m + 1), S.shifted i i r) +
              (C.function (-r) -
                ∑ i : Fin (m + 1), S.shifted i i (-r))) / 2| +
            |C.function 0 - ∑ i : Fin (m + 1), S.shifted i i 0| :=
          by
            let a : ℝ :=
              ((C.function r - ∑ i : Fin (m + 1), S.shifted i i r) +
                (C.function (-r) -
                  ∑ i : Fin (m + 1), S.shifted i i (-r))) / 2
            let b : ℝ :=
              C.function 0 - ∑ i : Fin (m + 1), S.shifted i i 0
            change |a - b| ≤ |a| + |b|
            simpa [a, b, abs_sub_comm] using (abs_sub_le a 0 b)
        _ ≤ (|C.function r - ∑ i : Fin (m + 1), S.shifted i i r| +
              |C.function (-r) -
                ∑ i : Fin (m + 1), S.shifted i i (-r)|) / 2 +
            |C.function 0 - ∑ i : Fin (m + 1), S.shifted i i 0| := by
          have hvariation :
              |((C.function r - ∑ i : Fin (m + 1), S.shifted i i r) +
                  (C.function (-r) -
                    ∑ i : Fin (m + 1), S.shifted i i (-r))) / 2| ≤
                (|C.function r - ∑ i : Fin (m + 1), S.shifted i i r| +
                  |C.function (-r) -
                    ∑ i : Fin (m + 1), S.shifted i i (-r)|) / 2 := by
            rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
          exact add_le_add hvariation le_rfl
    _ ≤ (referenceQuotientPairwiseShiftVariation Q r +
          referenceQuotientPairwiseShiftVariation Q (-r)) / 2 +
        |C.function 0 - ∑ i : Fin (m + 1), S.shifted i i 0| := by
      have hvariation :=
        div_le_div_of_nonneg_right (add_le_add hplus hminus) (by norm_num : (0 : ℝ) ≤ 2)
      exact add_le_add hvariation le_rfl

/-- Jensen's formula, rewritten as `roots = poles + endpoint mean` after
padding the finite sum from the exact order `q` to any `upTo ≥ q`. -/
theorem rootCountingUpTo_eq_poleCountingUpTo_add_centeredEndpointMean
    {q upTo : ℕ} (f : NthTropicalMeromorphicFunction q)
    (hqu : q ≤ upTo) {r : ℝ} (hr : 0 < r) :
    rootCountingUpTo upTo r f =
      poleCountingUpTo upTo r f + centeredEndpointMean f r := by
  have h := ambientSignedCountingDifference_eq_endpointMean_sub f hqu hr
  simp only [ambientSignedCountingDifference, integratedCounting_neg] at h
  unfold rootCountingUpTo poleCountingUpTo centeredEndpointMean
  linarith

/-- The absolute difference of the total diagonal-shift pole count and the
Casoratian pole count is bounded by the sum of the orderwise absolute
differences. -/
theorem diagonalShiftPoleDifference_le_casoratianPoleDiscrepancy
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (S : CurveShiftRealizations F) (C : CurveCasoratianRealization F)
    (r : ℝ) :
    |(∑ i : Fin (m + 1), poleCountingUpTo n r (S.shifted i i)) -
        poleCountingUpTo n r C.function| ≤
      casoratianPoleDiscrepancy F S C r := by
  classical
  have hcomm :
      (∑ i : Fin (m + 1),
          ∑ j ∈ Finset.Icc 1 n,
            integratedCounting j r (S.shifted i i)) =
        ∑ j ∈ Finset.Icc 1 n,
          ∑ i : Fin (m + 1),
            integratedCounting j r (S.shifted i i) := by
    rw [Finset.sum_comm]
  unfold poleCountingUpTo casoratianPoleDiscrepancy
  rw [hcomm, abs_sub_comm, ← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-- Taking the absolute value only after summing coordinates and orders is
bounded by the orderwise discrepancy used in the source's `(equa1)`. -/
theorem coordinateRootDifference_le_shiftRootCountingDiscrepancy
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (S : CurveShiftRealizations F) (r : ℝ) :
    |coordinateRootCountingSum F r - diagonalShiftRootCountingSum F S r| ≤
      shiftRootCountingDiscrepancy F S r := by
  classical
  unfold coordinateRootCountingSum diagonalShiftRootCountingSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i : Fin (m + 1),
        (rootCountingUpTo n r (F.coordinate i) -
          rootCountingUpTo n r (S.shifted i i))| ≤
        ∑ i : Fin (m + 1),
          |rootCountingUpTo n r (F.coordinate i) -
            rootCountingUpTo n r (S.shifted i i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (m + 1), ∑ j ∈ Finset.Icc 1 n,
          |integratedRootCounting j r (F.coordinate i) -
            integratedRootCounting j r (S.shifted i i)| := by
      apply Finset.sum_le_sum
      intro i _hi
      unfold rootCountingUpTo
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = shiftRootCountingDiscrepancy F S r := by
      unfold shiftRootCountingDiscrepancy
      congr 1
      funext i
      apply Finset.sum_congr rfl
      intro j _hj
      rw [abs_sub_comm]

/-- The exact, pointwise Jensen/triangle-inequality core of Theorem 6.2.
The two hypotheses are precisely the numerical conclusions of `(equa1)` and
`(equa2)` at the chosen radius. -/
theorem truncatedSecondMain_pointwise
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (S : CurveShiftRealizations F) (C : CurveCasoratianRealization F)
    {r shiftError endpointError : ℝ} (hr : 0 < r)
    (hshift :
      |coordinateRootCountingSum F r - diagonalShiftRootCountingSum F S r| ≤
        evenShiftCorrection F S r + shiftError)
    (hendpoint :
      casoratianCenteredEndpointDefect F S C r ≤ endpointError) :
    truncatedSecondMainDifference F C r ≤
      casoratianPoleDiscrepancy F S C r + evenShiftCorrection F S r +
        (shiftError + endpointError) := by
  have hshiftJensen :
      diagonalShiftRootCountingSum F S r =
        (∑ i : Fin (m + 1), poleCountingUpTo n r (S.shifted i i)) +
          ∑ i : Fin (m + 1), centeredEndpointMean (S.shifted i i) r := by
    unfold diagonalShiftRootCountingSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    exact rootCountingUpTo_eq_poleCountingUpTo_add_centeredEndpointMean
      (S.shifted i i) (S.shiftedOrder_le i i) hr
  have hcasJensen :
      rootCountingUpTo n r C.function =
        poleCountingUpTo n r C.function + centeredEndpointMean C.function r :=
    rootCountingUpTo_eq_poleCountingUpTo_add_centeredEndpointMean
      C.function C.order_le hr
  have hpole := diagonalShiftPoleDifference_le_casoratianPoleDiscrepancy
    F S C r
  have hendpoint' :
      |(∑ i : Fin (m + 1), centeredEndpointMean (S.shifted i i) r) -
          centeredEndpointMean C.function r| ≤
        casoratianCenteredEndpointDefect F S C r := by
    unfold casoratianCenteredEndpointDefect
    rw [abs_sub_comm]
  have hdiagonal :
      |diagonalShiftRootCountingSum F S r -
          rootCountingUpTo n r C.function| ≤
        casoratianPoleDiscrepancy F S C r +
          casoratianCenteredEndpointDefect F S C r := by
    rw [hshiftJensen, hcasJensen]
    calc
      |((∑ i : Fin (m + 1), poleCountingUpTo n r (S.shifted i i)) +
          ∑ i : Fin (m + 1), centeredEndpointMean (S.shifted i i) r) -
          (poleCountingUpTo n r C.function + centeredEndpointMean C.function r)|
          = |((∑ i : Fin (m + 1), poleCountingUpTo n r (S.shifted i i)) -
              poleCountingUpTo n r C.function) +
              ((∑ i : Fin (m + 1),
                centeredEndpointMean (S.shifted i i) r) -
                centeredEndpointMean C.function r)| := by
        congr 1
        ring
      _ ≤ |(∑ i : Fin (m + 1), poleCountingUpTo n r (S.shifted i i)) -
              poleCountingUpTo n r C.function| +
            |(∑ i : Fin (m + 1),
                centeredEndpointMean (S.shifted i i) r) -
              centeredEndpointMean C.function r| := abs_add_le _ _
      _ ≤ casoratianPoleDiscrepancy F S C r +
            casoratianCenteredEndpointDefect F S C r :=
        add_le_add hpole hendpoint'
  have htriangle :
      truncatedSecondMainDifference F C r ≤
        |coordinateRootCountingSum F r - diagonalShiftRootCountingSum F S r| +
          |diagonalShiftRootCountingSum F S r -
            rootCountingUpTo n r C.function| := by
    exact abs_sub_le _ _ _
  linarith

/-- The two analytic estimates still required to derive Theorem 6.2 from the
paper's original growth and well-definedness hypotheses.  The fields are
constructible proof obligations, not axioms. -/
structure TruncatedSecondMainAnalyticEstimates
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (S : CurveShiftRealizations F) (C : CurveCasoratianRealization F)
    (σ : ℝ) where
  exceptionalSet : Set ℝ
  exceptionalSet_finiteLogMeasure :
    HasFiniteLogarithmicMeasure exceptionalSet
  shiftError : ℝ → ℝ
  endpointError : ℝ → ℝ
  shiftError_small :
    shiftError =o[atTopOutside exceptionalSet]
      truncatedSecondMainScale F σ
  endpointError_small :
    endpointError =o[atTopOutside exceptionalSet]
      truncatedSecondMainScale F σ
  shiftComparison :
    ∀ᶠ r in atTopOutside exceptionalSet,
      0 < r ∧
        shiftRootCountingDiscrepancy F S r ≤
          evenShiftCorrection F S r + shiftError r
  endpointComparison :
    ∀ᶠ r in atTopOutside exceptionalSet,
      casoratianCenteredEndpointDefect F S C r ≤ endpointError r

/-- A fixed constant is negligible on the explicit nondegenerate scale, also
after removing any exceptional set. -/
theorem const_isLittleO_truncatedSecondMainScale
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (σ c : ℝ) (E : Set ℝ)
    (hscale : Tendsto (truncatedSecondMainScale F σ) atTop atTop) :
    (fun _r : ℝ ↦ c) =o[atTopOutside E] truncatedSecondMainScale F σ := by
  rw [Asymptotics.isLittleO_const_left]
  right
  change Tendsto (fun r ↦ |truncatedSecondMainScale F σ r|)
    (atTopOutside E) atTop
  exact tendsto_abs_atTop_atTop.comp (hscale.mono_left inf_le_left)

/-- A projectively nonconstant curve has a nonconstant quotient relative to
every fixed reference coordinate.  If all reference quotients agreed at two
points, the two coordinate vectors would differ by one common scalar and
would therefore represent the same tropical projective point. -/
theorem exists_nonconstant_referenceQuotient
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (Q : CurveWellDefinedReferenceQuotients F)
    (hF : F.IsNonconstant) :
    ∃ i : Fin (m + 1), ∃ x y : ℝ,
      Q.quotient i x ≠ Q.quotient i y := by
  obtain ⟨x, y, hxy⟩ := hF
  by_cases hall : ∀ i : Fin (m + 1), Q.quotient i x = Q.quotient i y
  · apply False.elim
    apply hxy
    apply Quotient.sound
    refine ⟨F.eval Q.reference x - F.eval Q.reference y, ?_⟩
    intro i
    have hi := hall i
    rw [Q.quotient_eq i x, Q.quotient_eq i y] at hi
    linarith
  · simp only [not_forall] at hall
    obtain ⟨i, hi⟩ := hall
    exact ⟨i, x, y, hi⟩

/-- Nonconstancy of the projective curve and well-definedness of the
reference quotients force the Cartan characteristic to tend to infinity.
The nonconstant quotient has unbounded characteristic by the rigidity
consequence of Lemma 4.5, and Proposition 5.4 transfers this growth to the
ambient curve. -/
theorem cartanCharacteristic_tendsto_atTop_of_nonconstant
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (Q : CurveWellDefinedReferenceQuotients F)
    (hF : F.IsNonconstant) :
    Tendsto (cartanCharacteristic F) atTop atTop := by
  obtain ⟨i, x, y, hxy⟩ := exists_nonconstant_referenceQuotient F Q hF
  have hqT := characteristic_tendsto_atTop_of_wellDefined_nonconstant
    (Q.quotient_wellDefined i) ⟨x, y, hxy⟩
  let D := curveCoordinateMaximum F 0 - F.eval Q.reference 0
  apply Filter.tendsto_atTop.2
  intro B
  filter_upwards [hqT (eventually_ge_atTop (B + D)),
    eventually_gt_atTop (0 : ℝ)] with r hq hr
  have hdom := characteristic_coordinateQuotient_le_cartan_add_constant
    F i Q.reference (Q.quotient i) (Q.quotientOrder_le i)
      (Q.quotient_eq i) hr
  dsimp [D] at hq ⊢
  linarith

/-- A positive affine lower bound for one nonconstant reference quotient
gives the same kind of lower bound for the Cartan characteristic.  Hence
`T_F(r)/r^σ → ∞` for every `σ < 1`.  This is the structural input missing
from the false abstract implication “`T_F → ∞` alone implies scale growth”.
-/
theorem truncatedSecondMainScale_tendsto_atTop_of_nonconstant
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (Q : CurveWellDefinedReferenceQuotients F)
    (hF : F.IsNonconstant) {σ : ℝ} (hσ : σ < 1) :
    Tendsto (truncatedSecondMainScale F σ) atTop atTop := by
  obtain ⟨i, x, y, hxy⟩ := exists_nonconstant_referenceQuotient F Q hF
  obtain ⟨c, C, hc, hlinear⟩ :=
    characteristic_eventually_linear_lower_of_wellDefined_nonconstant
      (Q.quotient_wellDefined i) ⟨x, y, hxy⟩
  let D := curveCoordinateMaximum F 0 - F.eval Q.reference 0
  have hcurveLinear : ∀ᶠ r : ℝ in atTop,
      c * r + (C - D) ≤ cartanCharacteristic F r := by
    filter_upwards [hlinear, eventually_gt_atTop (0 : ℝ)] with r hlin hr
    have hdom := characteristic_coordinateQuotient_le_cartan_add_constant
      F i Q.reference (Q.quotient i) (Q.quotientOrder_le i)
        (Q.quotient_eq i) hr
    dsimp [D]
    linarith
  have hhalf : 0 < c / 2 := by positivity
  have hhalfLinear : ∀ᶠ r : ℝ in atTop,
      (c / 2) * r ≤ cartanCharacteristic F r := by
    filter_upwards [hcurveLinear,
      eventually_ge_atTop (-2 * (C - D) / c)] with r hlin hr
    have habsorb : (c / 2) * r ≤ c * r + (C - D) := by
      have hr' : -2 * (C - D) ≤ r * c := by
        calc
          -2 * (C - D) = (-2 * (C - D) / c) * c := by
            field_simp [ne_of_gt hc]
          _ ≤ r * c := mul_le_mul_of_nonneg_right hr hc.le
      nlinarith
    exact habsorb.trans hlin
  have hexp : 0 < 1 - σ := sub_pos.mpr hσ
  have hmodel : Tendsto (fun r : ℝ ↦ (c / 2) * r ^ (1 - σ))
      atTop atTop := (tendsto_rpow_atTop hexp).const_mul_atTop hhalf
  apply Filter.tendsto_atTop.2
  intro B
  filter_upwards [hmodel (eventually_ge_atTop B), hhalfLinear,
    eventually_gt_atTop (0 : ℝ)] with r hB hlin hr
  have hrpow : 0 < r ^ σ := Real.rpow_pos_of_pos hr σ
  have hratio : (c / 2) * r ^ (1 - σ) =
      ((c / 2) * r) / r ^ σ := by
    rw [Real.rpow_sub hr, Real.rpow_one]
    ring
  change B ≤ (c / 2) * r ^ (1 - σ) at hB
  rw [hratio] at hB
  exact hB.trans (div_le_div_of_nonneg_right hlin hrpow.le)

/-- An unbounded positive growth function cannot have negative hyperorder.
For the curve characteristic this follows directly from the definition: once
both `r` and `T_F(r)` exceed `exp 1`, the quotient
`log (log T_F(r)) / log r` is nonnegative. -/
theorem curveHyperOrder_nonneg_of_characteristic_tendsto_atTop
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (hT : Tendsto (cartanCharacteristic F) atTop atTop) :
    (0 : EReal) ≤ curveHyperOrder F := by
  have hrlarge : ∀ᶠ r : ℝ in atTop, Real.exp 1 ≤ r :=
    eventually_ge_atTop (Real.exp 1)
  have hTlarge : ∀ᶠ r : ℝ in atTop,
      Real.exp 1 ≤ cartanCharacteristic F r :=
    hT (eventually_ge_atTop (Real.exp 1))
  have hquotient : ∀ᶠ r : ℝ in atTop,
      (0 : EReal) ≤ curveHyperOrderQuotient F r := by
    filter_upwards [hrlarge, hTlarge] with r hr hTr
    have hrone : 1 < r := (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hr
    have hlogr : 0 < Real.log r := Real.log_pos hrone
    have hlogTone : 1 ≤ Real.log (cartanCharacteristic F r) := by
      rw [← Real.log_exp (1 : ℝ)]
      exact Real.strictMonoOn_log.monotoneOn
        (Real.exp_pos 1) ((Real.exp_pos 1).trans_le hTr) hTr
    have hloglogT : 0 ≤ Real.log (Real.log (cartanCharacteristic F r)) :=
      Real.log_nonneg hlogTone
    change (0 : EReal) ≤
      ((Real.log (Real.log (cartanCharacteristic F r)) / Real.log r : ℝ) : EReal)
    exact EReal.coe_nonneg.mpr (div_nonneg hloglogT hlogr.le)
  exact le_limsup_of_frequently_le' hquotient.frequently

/-- Real-valued form of the preceding nonnegativity statement. -/
theorem curveHyperOrder_parameter_nonneg_of_characteristic_tendsto_atTop
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m) (rho2 : ℝ)
    (horder : curveHyperOrder F = (rho2 : EReal))
    (hT : Tendsto (cartanCharacteristic F) atTop atTop) :
    0 ≤ rho2 := by
  have hnonneg : (0 : EReal) ≤ (rho2 : EReal) :=
    (curveHyperOrder_nonneg_of_characteristic_tendsto_atTop F hT).trans_eq horder
  exact_mod_cast hnonneg

/-- The two internal growth limits used by the analytic assembly are
consequences of the original paper hypotheses.  First, nonconstancy supplies
`T_F(r) → ∞`.  This makes `ρ₂ ≥ 0`; hence the paper range
`σ < 1 - ρ₂` implies `σ < 1`, and the positive affine lower bound above gives
`T_F(r) / r^σ → ∞`. -/
def TruncatedSecondMainNondegenerateHypotheses.ofPaper
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (σ : ℝ) (h : TruncatedSecondMainPaperHypotheses F σ) :
    TruncatedSecondMainNondegenerateHypotheses F σ := by
  have hT : Tendsto (cartanCharacteristic F) atTop atTop :=
    cartanCharacteristic_tendsto_atTop_of_nonconstant
      F h.quotients h.nonconstant
  have hρ0 : 0 ≤ h.rho2 :=
    curveHyperOrder_parameter_nonneg_of_characteristic_tendsto_atTop
      F h.rho2 h.hyperOrder_eq hT
  have hσ1 : σ < 1 := by linarith [h.sigma_lt_one_sub_rho2]
  exact
    { toTruncatedSecondMainPaperHypotheses := h
      characteristic_tendsto_atTop := hT
      scale_tendsto_atTop :=
        truncatedSecondMainScale_tendsto_atTop_of_nonconstant
          F h.quotients h.nonconstant hσ1 }

/-- The concrete `(equa1)` remainder follows from the curve growth bound in
the nondegenerate branch.  Nonnegativity of `rho2` is derived from
`T_F(r) → ∞`, rather than added as a separate hypothesis. -/
theorem coordinateRootShiftIncrement_isLittleO_of_nondegenerate
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (σ : ℝ) (h : TruncatedSecondMainNondegenerateHypotheses F σ) :
    ∃ E : Set ℝ, HasFiniteLogarithmicMeasure E ∧
      coordinateRootShiftIncrement F =o[atTopOutside E]
        truncatedSecondMainScale F σ := by
  classical
  have hrho0 : 0 ≤ h.rho2 :=
    curveHyperOrder_parameter_nonneg_of_characteristic_tendsto_atTop
      F h.rho2 h.hyperOrder_eq h.characteristic_tendsto_atTop
  have hcurveOrder :
      growthFunctionHyperOrder (cartanCharacteristic F) = (h.rho2 : EReal) := by
    rw [show growthFunctionHyperOrder (cartanCharacteristic F) =
        curveHyperOrder F by
      unfold growthFunctionHyperOrder curveHyperOrder
      congr 1]
    exact h.hyperOrder_eq
  have hcurveGrowth : ∀ alpha : ℝ, h.rho2 < alpha →
      ∀ᶠ r : ℝ in atTop,
        |Real.log (cartanCharacteristic F r)| ≤ r ^ alpha :=
    fun alpha halpha ↦
      eventually_abs_log_le_rpow_of_growthFunctionHyperOrder_lt
        (cartanCharacteristic F) h.rho2 alpha hcurveOrder halpha
  let increment : Fin (m + 1) → ℝ → ℝ := fun i r ↦
    rootCountingUpTo n (r + (i : ℝ)) (F.coordinate i) -
      rootCountingUpTo n (r - (i : ℝ)) (F.coordinate i)
  have hsingle : ∀ i : Fin (m + 1),
      ∃ E : Set ℝ, HasFiniteLogarithmicMeasure E ∧
        increment i =o[atTopOutside E] truncatedSecondMainScale F σ := by
    intro i
    by_cases hi0 : (i : ℕ) = 0
    · refine ⟨∅, by simp [HasFiniteLogarithmicMeasure], ?_⟩
      have hzero : increment i = fun _r : ℝ ↦ 0 := by
        funext r
        simp [increment, hi0]
      rw [hzero]
      exact Asymptotics.isLittleO_zero _ _
    · have hiposNat : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi0
      have hipos : 0 < (i : ℝ) := by exact_mod_cast hiposNat
      let A : ℝ → ℝ := fun s ↦
        rootCountingUpTo n (max 0 (s - (i : ℝ))) (F.coordinate i)
      have hAmono : MonotoneOn A (Set.Ici 0) := by
        intro x hx y hy hxy
        apply rootCountingUpTo_mono_radius n (le_max_left 0 (x - (i : ℝ)))
        exact max_le_max (le_refl 0) (sub_le_sub_right hxy (i : ℝ))
      have hAnonneg : ∀ s, 0 ≤ s → 0 ≤ A s := by
        intro s _hs
        exact rootCountingUpTo_nonneg n _ (F.coordinate i)
      let C : ℝ := curveCoordinateMaximum F 0 - F.eval i 0
      have hAdom : ∀ s, 0 < s → A s ≤ cartanCharacteristic F s + C := by
        intro s hs
        have hmaxle : max 0 (s - (i : ℝ)) ≤ s := by
          apply max_le hs.le
          linarith
        exact (rootCountingUpTo_mono_radius n
          (le_max_left 0 (s - (i : ℝ))) hmaxle (F.coordinate i)).trans
            (rootCountingUpTo_coordinate_le_cartan_add_constant F i hs)
      have hAgrowth : ∀ alpha : ℝ, h.rho2 < alpha →
          ∃ K : ℝ, 0 ≤ K ∧
            ∀ᶠ r : ℝ in atTop, |Real.log (A r)| ≤ K * r ^ alpha := by
        intro alpha halpha
        exact eventually_abs_log_le_mul_rpow_of_monotone_le_add
          A (cartanCharacteristic F) C h.rho2 alpha hAmono hAnonneg
          h.characteristic_tendsto_atTop hAdom hcurveGrowth halpha
          (hrho0.trans_lt halpha)
      obtain ⟨E, hE, hsmall⟩ :=
        growthShiftLemma_of_eventually_abs_log_le_rpow
          A (2 * (i : ℝ)) h.rho2 σ hAmono hAnonneg
          (mul_pos (by norm_num) hipos) hAgrowth h.rho2_lt_one
          h.sigma_pos h.sigma_lt_one_sub_rho2
      have hlarge : ∀ᶠ r : ℝ in atTopOutside E, (i : ℝ) ≤ r :=
        (eventually_ge_atTop (i : ℝ)).filter_mono inf_le_left
      have heq : (fun r ↦ A (r + 2 * (i : ℝ)) - A r) =ᶠ[
          atTopOutside E] increment i := by
        filter_upwards [hlarge] with r hr
        simp only [A, increment]
        have hrminus : 0 ≤ r - (i : ℝ) := sub_nonneg.mpr hr
        have hrplus : 0 ≤ r + (i : ℝ) := by linarith [hipos]
        rw [max_eq_right hrminus, max_eq_right]
        · have harg : r + 2 * (i : ℝ) - (i : ℝ) = r + (i : ℝ) := by ring
          rw [harg]
        · linarith
      have hsmall' : increment i =o[atTopOutside E]
          (fun r ↦ A r / r ^ σ) :=
        hsmall.congr' heq EventuallyEq.rfl
      have hscaleBigO : (fun r ↦ A r / r ^ σ) =O[atTopOutside E]
          truncatedSecondMainScale F σ := by
        rw [Asymptotics.isBigO_iff]
        refine ⟨2, ?_⟩
        have hBlarge : ∀ᶠ r : ℝ in atTopOutside E,
            max 1 |C| ≤ cartanCharacteristic F r :=
          Filter.Eventually.filter_mono inf_le_left
            (h.characteristic_tendsto_atTop
              (eventually_ge_atTop (max 1 |C|)))
        have hrpos : ∀ᶠ r : ℝ in atTopOutside E, 0 < r :=
          (eventually_gt_atTop (0 : ℝ)).filter_mono inf_le_left
        filter_upwards [hBlarge, hrpos] with r hBr hr
        have hBpos : 0 < cartanCharacteristic F r :=
          zero_lt_one.trans_le ((le_max_left 1 |C|).trans hBr)
        have hCBr : C ≤ cartanCharacteristic F r :=
          (le_abs_self C).trans ((le_max_right 1 |C|).trans hBr)
        have hAupper : A r ≤ 2 * cartanCharacteristic F r := by
          linarith [hAdom r hr]
        have hA0 : 0 ≤ A r := hAnonneg r hr.le
        have hrpow : 0 < r ^ σ := Real.rpow_pos_of_pos hr σ
        simp only [Real.norm_eq_abs, truncatedSecondMainScale]
        rw [abs_of_nonneg (div_nonneg hA0 hrpow.le),
          abs_of_nonneg (div_nonneg hBpos.le hrpow.le)]
        calc
          A r / r ^ σ ≤ (2 * cartanCharacteristic F r) / r ^ σ :=
            div_le_div_of_nonneg_right hAupper hrpow.le
          _ = 2 * (cartanCharacteristic F r / r ^ σ) := by ring
      exact ⟨E, hE, hsmall'.trans_isBigO hscaleBigO⟩
  choose E hE hsmall using hsingle
  let Eall : Set ℝ := ⋃ i ∈ (Finset.univ : Finset (Fin (m + 1))), E i
  have hEall : HasFiniteLogarithmicMeasure Eall :=
    hasFiniteLogarithmicMeasure_finset_biUnion Finset.univ
      (fun i ↦ E i) (fun i _hi ↦ hE i)
  refine ⟨Eall, hEall, ?_⟩
  have hcoordinate : coordinateRootShiftIncrement F = fun r ↦
      ∑ i : Fin (m + 1),
        (rootCountingUpTo n (r + (i : ℝ)) (F.coordinate i) -
          rootCountingUpTo n (r - (i : ℝ)) (F.coordinate i)) := by
    funext r
    exact coordinateRootShiftIncrement_eq_rootCountingUpTo_sub F r
  rw [hcoordinate]
  change (fun r ↦ ∑ i : Fin (m + 1), increment i r) =o[
    atTopOutside Eall] truncatedSecondMainScale F σ
  exact Asymptotics.IsLittleO.sum (fun i _hi ↦
    NthTropicalNevanlinna.Asymptotics.IsLittleO.mono_atTopOutside
      (hsmall i) (Set.subset_iUnion₂_of_subset i (Finset.mem_univ i) Subset.rfl))

/-- Every finitely many radial shift of every reference quotient is small on
the ambient curve scale.  Proposition 5.4 supplies the characteristic
domination, while the dominated-growth form of Theorem 4.7 avoids requiring
the quotient to have the same (or even a separately real-valued) hyperorder. -/
theorem referenceQuotientRadialShifts_isLittleO_of_nondegenerate
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (σ : ℝ) (h : TruncatedSecondMainNondegenerateHypotheses F σ) :
    ∃ E : Set ℝ, HasFiniteLogarithmicMeasure E ∧
      ∀ i j : Fin (m + 1), ∀ δ : ℝ, δ = 1 ∨ δ = -1 →
        (fun r ↦ |h.quotients.quotient i (δ * r + (j : ℝ)) -
          h.quotients.quotient i (δ * r)|) =o[atTopOutside E]
            truncatedSecondMainScale F σ := by
  classical
  have hrho0 : 0 ≤ h.rho2 :=
    curveHyperOrder_parameter_nonneg_of_characteristic_tendsto_atTop
      F h.rho2 h.hyperOrder_eq h.characteristic_tendsto_atTop
  have hcurveOrder :
      growthFunctionHyperOrder (cartanCharacteristic F) = (h.rho2 : EReal) := by
    rw [show growthFunctionHyperOrder (cartanCharacteristic F) =
        curveHyperOrder F by
      unfold growthFunctionHyperOrder curveHyperOrder
      congr 1]
    exact h.hyperOrder_eq
  have hcurveGrowth : ∀ alpha : ℝ, h.rho2 < alpha →
      ∀ᶠ r : ℝ in atTop,
        |Real.log (cartanCharacteristic F r)| ≤ r ^ alpha :=
    fun alpha halpha ↦
      eventually_abs_log_le_rpow_of_growthFunctionHyperOrder_lt
        (cartanCharacteristic F) h.rho2 alpha hcurveOrder halpha
  have hsingle : ∀ i j : Fin (m + 1),
      ∃ E : Set ℝ, HasFiniteLogarithmicMeasure E ∧
        ∀ δ : ℝ, δ = 1 ∨ δ = -1 →
          (fun r ↦ |h.quotients.quotient i (δ * r + (j : ℝ)) -
            h.quotients.quotient i (δ * r)|) =o[atTopOutside E]
              truncatedSecondMainScale F σ := by
    intro i j
    by_cases hj0 : (j : ℕ) = 0
    · refine ⟨∅, by simp [HasFiniteLogarithmicMeasure], ?_⟩
      intro δ _hδ
      have hzero : (fun r ↦ |h.quotients.quotient i (δ * r + (j : ℝ)) -
          h.quotients.quotient i (δ * r)|) = fun _r : ℝ ↦ 0 := by
        funext r
        simp [hj0]
      rw [hzero]
      exact Asymptotics.isLittleO_zero _ _
    · have hjposNat : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj0
      have hjne : (j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hjposNat)
      let q := h.quotients.quotient i
      let A : ℝ → ℝ := fun r ↦ characteristic (max 1 r) q
      let B : ℝ → ℝ := fun r ↦ cartanCharacteristic F (max 1 r)
      let C : ℝ := curveCoordinateMaximum F 0 -
        F.eval h.quotients.reference 0
      have hqmono : CharacteristicMonotone q :=
        characteristicMonotone_of_wellDefined (h.quotients.quotient_wellDefined i)
      have hAmono : MonotoneOn A (Set.Ici 0) := by
        intro x hx y hy hxy
        exact hqmono (by simp) (by simp) (max_le_max (le_refl 1) hxy)
      have hAnonneg : ∀ r, 0 ≤ r → 0 ≤ A r := by
        intro r _hr
        exact characteristic_nonneg _ _
      have hBtop : Tendsto B atTop atTop := by
        have heq : cartanCharacteristic F =ᶠ[atTop] B := by
          filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
          simp [B, max_eq_right hr]
        exact Tendsto.congr' heq h.characteristic_tendsto_atTop
      have hBgrowth : ∀ alpha : ℝ, h.rho2 < alpha →
          ∀ᶠ r : ℝ in atTop, |Real.log (B r)| ≤ r ^ alpha := by
        intro alpha halpha
        have hgrowth := hcurveGrowth alpha halpha
        filter_upwards [eventually_ge_atTop (1 : ℝ), hgrowth] with r hr hgr
        simpa [B, max_eq_right hr] using hgr
      have hdom : ∀ r, 0 < r → A r ≤ B r + C := by
        intro r _hr
        have hmaxpos : 0 < max 1 r := zero_lt_one.trans_le (le_max_left 1 r)
        exact characteristic_coordinateQuotient_le_cartan_add_constant
          F i h.quotients.reference q (h.quotients.quotientOrder_le i)
            (h.quotients.quotient_eq i) hmaxpos
      have hAgrowth : ∀ alpha : ℝ, h.rho2 < alpha →
          ∀ᶠ r : ℝ in atTop, |Real.log (A r)| ≤ r ^ alpha := by
        intro alpha halpha
        exact eventually_abs_log_le_rpow_of_monotone_le_add
          A B C h.rho2 alpha hAmono hAnonneg hBtop hdom hBgrowth
            hrho0 halpha
      obtain ⟨E, hE, hpointwise⟩ :=
        pointwiseLogarithmicDerivative_of_eventually_abs_log_le_rpow
          (h.quotients.quotientOrder i) q (j : ℝ) h.rho2 σ hjne
            (h.quotients.quotient_wellDefined i) hAgrowth h.rho2_lt_one
              h.sigma_pos h.sigma_lt_one_sub_rho2
      have hscaleBigO : logarithmicDerivativeScale q σ =O[atTopOutside E]
          truncatedSecondMainScale F σ := by
        rw [Asymptotics.isBigO_iff]
        refine ⟨2, ?_⟩
        have hFlarge : ∀ᶠ r : ℝ in atTopOutside E,
            max 1 |C| ≤ cartanCharacteristic F r :=
          Filter.Eventually.filter_mono inf_le_left
            (h.characteristic_tendsto_atTop
              (eventually_ge_atTop (max 1 |C|)))
        have hrpos : ∀ᶠ r : ℝ in atTopOutside E, 0 < r :=
          (eventually_gt_atTop (0 : ℝ)).filter_mono inf_le_left
        filter_upwards [hFlarge, hrpos] with r hFr hr
        have hFpos : 0 < cartanCharacteristic F r :=
          zero_lt_one.trans_le ((le_max_left 1 |C|).trans hFr)
        have hCFr : C ≤ cartanCharacteristic F r :=
          (le_abs_self C).trans ((le_max_right 1 |C|).trans hFr)
        have hqUpper : characteristic r q ≤ 2 * cartanCharacteristic F r := by
          linarith [characteristic_coordinateQuotient_le_cartan_add_constant
            F i h.quotients.reference q (h.quotients.quotientOrder_le i)
              (h.quotients.quotient_eq i) hr]
        have hrpow : 0 < r ^ σ := Real.rpow_pos_of_pos hr σ
        simp only [Real.norm_eq_abs, logarithmicDerivativeScale,
          truncatedSecondMainScale]
        rw [abs_of_nonneg (div_nonneg (characteristic_nonneg r q) hrpow.le),
          abs_of_nonneg (div_nonneg hFpos.le hrpow.le)]
        calc
          characteristic r q / r ^ σ ≤
              (2 * cartanCharacteristic F r) / r ^ σ :=
            div_le_div_of_nonneg_right hqUpper hrpow.le
          _ = 2 * (cartanCharacteristic F r / r ^ σ) := by ring
      refine ⟨E, hE, fun δ hδ ↦ ?_⟩
      exact (hpointwise δ hδ).trans_isBigO hscaleBigO
  choose E hE hsmall using hsingle
  let Eall : Set ℝ := ⋃ i ∈ (Finset.univ : Finset (Fin (m + 1))),
    ⋃ j ∈ (Finset.univ : Finset (Fin (m + 1))), E i j
  have hEall : HasFiniteLogarithmicMeasure Eall :=
    hasFiniteLogarithmicMeasure_finset_biUnion Finset.univ
      (fun i ↦ ⋃ j ∈ (Finset.univ : Finset (Fin (m + 1))), E i j)
      (fun i _hi ↦ hasFiniteLogarithmicMeasure_finset_biUnion Finset.univ
        (fun j ↦ E i j) (fun j _hj ↦ hE i j))
  refine ⟨Eall, hEall, ?_⟩
  intro i j δ hδ
  exact NthTropicalNevanlinna.Asymptotics.IsLittleO.mono_atTopOutside
    (hsmall i j δ hδ)
    (Set.subset_iUnion₂_of_subset i (Finset.mem_univ i)
      (Set.subset_iUnion₂_of_subset j (Finset.mem_univ j) Subset.rfl))

/-- The complete endpoint remainder in `(equa2)` on the ambient curve scale.
Pairwise shifted differences are reduced by the triangle inequality to two
radial shifts from the same base point, and the finite sums are then handled
by `referenceQuotientEndpointVariation_isLittleO_of_pairwise`. -/
theorem referenceQuotientEndpointVariation_isLittleO_of_nondegenerate
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (σ : ℝ) (h : TruncatedSecondMainNondegenerateHypotheses F σ) :
    ∃ E : Set ℝ, HasFiniteLogarithmicMeasure E ∧
      (fun r ↦ (referenceQuotientPairwiseShiftVariation h.quotients r +
          referenceQuotientPairwiseShiftVariation h.quotients (-r)) / 2) =o[
        atTopOutside E] truncatedSecondMainScale F σ := by
  obtain ⟨E, hE, hradial⟩ :=
    referenceQuotientRadialShifts_isLittleO_of_nondegenerate F σ h
  have hpair : ∀ i k : Fin (m + 1), ∀ δ : ℝ, δ = 1 ∨ δ = -1 →
      (fun r ↦ |h.quotients.quotient i (δ * r + (k : ℝ)) -
        h.quotients.quotient i (δ * r + (i : ℝ))|) =o[atTopOutside E]
          truncatedSecondMainScale F σ := by
    intro i k δ hδ
    have hk := hradial i k δ hδ
    have hi := hradial i i δ hδ
    apply (Asymptotics.isLittleO_iff).2
    intro eps heps
    have hkBound := (Asymptotics.isLittleO_iff.mp hk) (half_pos heps)
    have hiBound := (Asymptotics.isLittleO_iff.mp hi) (half_pos heps)
    filter_upwards [hkBound, hiBound] with r hkr hir
    have htriangle :
        |h.quotients.quotient i (δ * r + (k : ℝ)) -
            h.quotients.quotient i (δ * r + (i : ℝ))| ≤
          |h.quotients.quotient i (δ * r + (k : ℝ)) -
            h.quotients.quotient i (δ * r)| +
          |h.quotients.quotient i (δ * r + (i : ℝ)) -
            h.quotients.quotient i (δ * r)| := by
      calc
        |h.quotients.quotient i (δ * r + (k : ℝ)) -
            h.quotients.quotient i (δ * r + (i : ℝ))| ≤
            |h.quotients.quotient i (δ * r + (k : ℝ)) -
              h.quotients.quotient i (δ * r)| +
            |h.quotients.quotient i (δ * r) -
              h.quotients.quotient i (δ * r + (i : ℝ))| :=
          abs_sub_le _ _ _
        _ = _ := by
          congr 1
          exact abs_sub_comm _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    calc
      |h.quotients.quotient i (δ * r + (k : ℝ)) -
          h.quotients.quotient i (δ * r + (i : ℝ))| ≤ _ := htriangle
      _ ≤ (eps / 2) * ‖truncatedSecondMainScale F σ r‖ +
          (eps / 2) * ‖truncatedSecondMainScale F σ r‖ := by
        exact add_le_add
          (by simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)] using hkr)
          (by simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)] using hir)
      _ = eps * ‖truncatedSecondMainScale F σ r‖ := by ring
  refine ⟨E, hE, ?_⟩
  apply referenceQuotientEndpointVariation_isLittleO_of_pairwise
    h.quotients σ E
  · intro i k
    simpa using hpair i k 1 (Or.inl rfl)
  · intro i k
    simpa using hpair i k (-1) (Or.inr rfl)

/-- Construction of the two analytic fields from the concrete remainders
left by the exact `(equa1)` and `(equa2)` kernels.  In contrast with an
arbitrary certificate, the shift error is exactly the finite sum of source
counting increments and the endpoint error is exactly the finite quotient
variation plus the fixed centered value. -/
def truncatedSecondMainAnalyticEstimates_of_concreteRemainders
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (Q : CurveWellDefinedReferenceQuotients F) (σ : ℝ)
    (hscale : Tendsto (truncatedSecondMainScale F σ) atTop atTop)
    (Eshift Eendpoint : Set ℝ)
    (hEshift : HasFiniteLogarithmicMeasure Eshift)
    (hEendpoint : HasFiniteLogarithmicMeasure Eendpoint)
    (hshiftSmall : coordinateRootShiftIncrement F =o[atTopOutside Eshift]
      truncatedSecondMainScale F σ)
    (hendpointSmall :
      (fun r ↦ (referenceQuotientPairwiseShiftVariation Q r +
          referenceQuotientPairwiseShiftVariation Q (-r)) / 2) =o[
        atTopOutside Eendpoint] truncatedSecondMainScale F σ) :
    TruncatedSecondMainAnalyticEstimates F
      (canonicalCurveShiftRealizations F)
      (canonicalCurveCasoratianRealization F) σ := by
  let E := Eshift ∪ Eendpoint
  let center : ℝ :=
    |(canonicalCurveCasoratianRealization F).function 0 -
      ∑ i : Fin (m + 1),
        (canonicalCurveShiftRealizations F).shifted i i 0|
  let endpointVariation : ℝ → ℝ := fun r ↦
    (referenceQuotientPairwiseShiftVariation Q r +
      referenceQuotientPairwiseShiftVariation Q (-r)) / 2
  refine
    { exceptionalSet := E
      exceptionalSet_finiteLogMeasure := hEshift.union hEendpoint
      shiftError := coordinateRootShiftIncrement F
      endpointError := fun r ↦ endpointVariation r + center
      shiftError_small :=
        NthTropicalNevanlinna.Asymptotics.IsLittleO.mono_atTopOutside
          hshiftSmall Set.subset_union_left
      endpointError_small := ?_
      shiftComparison := ?_
      endpointComparison := ?_ }
  · exact
      (NthTropicalNevanlinna.Asymptotics.IsLittleO.mono_atTopOutside
        hendpointSmall Set.subset_union_right).add
      (const_isLittleO_truncatedSecondMainScale F σ center E hscale)
  · have hlarge : ∀ᶠ r : ℝ in atTopOutside E,
        max 1 (2 * (m : ℝ)) ≤ r :=
      (eventually_ge_atTop (max 1 (2 * (m : ℝ)))).filter_mono inf_le_left
    filter_upwards [hlarge] with r hr
    have hrpos : 0 < r :=
      lt_of_lt_of_le (by norm_num) ((le_max_left 1 (2 * (m : ℝ))).trans hr)
    have hrshift : 2 * (m : ℝ) ≤ r :=
      (le_max_right 1 (2 * (m : ℝ))).trans hr
    exact ⟨hrpos, shiftRootCountingDiscrepancy_canonical_le F hrshift⟩
  · filter_upwards [] with r
    exact casoratianCenteredEndpointDefect_le_referenceQuotientVariation
      F (canonicalCurveShiftRealizations F)
        (canonicalCurveCasoratianRealization F) Q r

/-- A literal Landau/filter formulation of formula `(6f2)`. -/
def TruncatedSecondMainConclusion
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (S : CurveShiftRealizations F) (C : CurveCasoratianRealization F)
    (σ : ℝ) : Prop :=
  ∃ E : Set ℝ, ∃ error : ℝ → ℝ,
    HasFiniteLogarithmicMeasure E ∧
      error =o[atTopOutside E] truncatedSecondMainScale F σ ∧
      ∀ᶠ r in atTopOutside E,
        truncatedSecondMainDifference F C r ≤
          casoratianPoleDiscrepancy F S C r +
            evenShiftCorrection F S r + error r

/-- The paper-quantifier target for Theorem 6.2.  Translation and Casoratian
closure are now automatic, so the statement exposes exactly the paper's
curve, growth, and well-defined quotient hypotheses and no realization
witnesses.  It is a `Prop`, not an asserted theorem. -/
def TruncatedSecondMainPaperStatement
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m) : Prop :=
  ∀ σ : ℝ, TruncatedSecondMainPaperHypotheses F σ →
    TruncatedSecondMainConclusion F
      (canonicalCurveShiftRealizations F)
      (canonicalCurveCasoratianRealization F) σ

/-- Theorem 6.2's final proof from `(equa1)` and `(equa2)`.  The reducedness
hypothesis is retained from the paper-facing statement; its analytic use is
inside the construction of `estimates`. -/
theorem truncatedSecondMain_of_analyticEstimates
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (_hFReduced : F.IsReduced)
    (S : CurveShiftRealizations F) (C : CurveCasoratianRealization F)
    (σ : ℝ) (estimates : TruncatedSecondMainAnalyticEstimates F S C σ) :
    TruncatedSecondMainConclusion F S C σ := by
  refine ⟨estimates.exceptionalSet,
    fun r ↦ estimates.shiftError r + estimates.endpointError r,
    estimates.exceptionalSet_finiteLogMeasure,
    estimates.shiftError_small.add estimates.endpointError_small, ?_⟩
  filter_upwards [estimates.shiftComparison,
    estimates.endpointComparison] with r hshift hendpoint
  apply truncatedSecondMain_pointwise F S C hshift.1 _ hendpoint
  exact (coordinateRootDifference_le_shiftRootCountingDiscrepancy F S r).trans
    hshift.2

/-- The nondegenerate Theorem 6.2 branch from the two concrete global
remainders exposed by the exact proof.  This no longer asks the caller to
manufacture an arbitrary `TruncatedSecondMainAnalyticEstimates` structure. -/
theorem truncatedSecondMain_nondegenerate_of_concreteRemainders
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (σ : ℝ) (h : TruncatedSecondMainNondegenerateHypotheses F σ)
    (Eshift Eendpoint : Set ℝ)
    (hEshift : HasFiniteLogarithmicMeasure Eshift)
    (hEendpoint : HasFiniteLogarithmicMeasure Eendpoint)
    (hshiftSmall : coordinateRootShiftIncrement F =o[atTopOutside Eshift]
      truncatedSecondMainScale F σ)
    (hendpointSmall :
      (fun r ↦ (referenceQuotientPairwiseShiftVariation h.quotients r +
          referenceQuotientPairwiseShiftVariation h.quotients (-r)) / 2) =o[
        atTopOutside Eendpoint] truncatedSecondMainScale F σ) :
    TruncatedSecondMainConclusion F
      (canonicalCurveShiftRealizations F)
      (canonicalCurveCasoratianRealization F) σ := by
  exact truncatedSecondMain_of_analyticEstimates F h.reduced
    (canonicalCurveShiftRealizations F)
    (canonicalCurveCasoratianRealization F) σ
    (truncatedSecondMainAnalyticEstimates_of_concreteRemainders
      F h.quotients σ h.scale_tendsto_atTop Eshift Eendpoint
        hEshift hEendpoint hshiftSmall hendpointSmall)

/-- Fully assembled nondegenerate branch of Theorem 6.2.  Both global
little-o remainders are now consequences of the curve hypotheses, so no
analytic certificate or remainder estimate is supplied by the caller. -/
theorem truncatedSecondMain_nondegenerate
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (σ : ℝ) (h : TruncatedSecondMainNondegenerateHypotheses F σ) :
    TruncatedSecondMainConclusion F
      (canonicalCurveShiftRealizations F)
      (canonicalCurveCasoratianRealization F) σ := by
  obtain ⟨Eshift, hEshift, hshiftSmall⟩ :=
    coordinateRootShiftIncrement_isLittleO_of_nondegenerate F σ h
  obtain ⟨Eendpoint, hEendpoint, hendpointSmall⟩ :=
    referenceQuotientEndpointVariation_isLittleO_of_nondegenerate F σ h
  exact truncatedSecondMain_nondegenerate_of_concreteRemainders
    F σ h Eshift Eendpoint hEshift hEendpoint hshiftSmall hendpointSmall

/-- Theorem 6.2 in the paper's original quantifiers.  The apparent
nondegenerate growth assumptions of the internal assembly are not additional
hypotheses: `ofPaper` derives both of them from the paper's global
nonconstancy convention, the well-defined reference quotients, Lemma 4.4,
Lemma 4.5, and Proposition 5.4. -/
theorem truncatedSecondMain
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (σ : ℝ) (h : TruncatedSecondMainPaperHypotheses F σ) :
    TruncatedSecondMainConclusion F
      (canonicalCurveShiftRealizations F)
      (canonicalCurveCasoratianRealization F) σ :=
  truncatedSecondMain_nondegenerate F σ
    (TruncatedSecondMainNondegenerateHypotheses.ofPaper F σ h)

/-- The paper-level predicate is therefore inhabited for every curve
representation, with its hypotheses supplied at the quantified call site. -/
theorem truncatedSecondMainPaperStatement_verified
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m) :
    TruncatedSecondMainPaperStatement F := by
  intro σ h
  exact truncatedSecondMain F σ h

/-- A reusable legacy reduction: any separately supplied analytic-estimate
package also implies the paper statement.  The direct theorem above no
longer needs this interface. -/
theorem truncatedSecondMainPaperStatement_of_analyticEstimates
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (hconstruct : ∀ (σ : ℝ), TruncatedSecondMainPaperHypotheses F σ →
      Nonempty (TruncatedSecondMainAnalyticEstimates F
        (canonicalCurveShiftRealizations F)
        (canonicalCurveCasoratianRealization F) σ)) :
    TruncatedSecondMainPaperStatement F := by
  intro σ hypotheses
  obtain ⟨estimates⟩ := hconstruct σ hypotheses
  exact truncatedSecondMain_of_analyticEstimates F hypotheses.reduced
    (canonicalCurveShiftRealizations F)
    (canonicalCurveCasoratianRealization F) σ estimates

/-! ## Corollary 6.3 -/

/-- The original hypotheses of Corollary 6.3.  Unlike Theorem 6.2, no
well-defined quotient hypothesis is present: for first-order piecewise-linear
functions it is automatic. -/
structure FirstOrderTruncatedSecondMainPaperHypotheses {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m) (σ : ℝ) where
  reduced : F.IsReduced
  nonconstant : F.IsNonconstant
  rho2 : ℝ
  hyperOrder_eq : curveHyperOrder F = (rho2 : EReal)
  rho2_lt_one : rho2 < 1
  sigma_pos : 0 < σ
  sigma_lt_one_sub_rho2 : σ < 1 - rho2

/-- Literal `A(r)=B(r)+o(T_F(r)/r^σ)` formulation used in Corollary 6.3.
The absolute-error majorant is equivalent to the usual scalar little-o
notation and is convenient for direct reuse of Theorem 6.2. -/
def FirstOrderTruncatedSecondMainConclusion {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m)
    (C : CurveCasoratianRealization F) (σ : ℝ) : Prop :=
  ∃ E : Set ℝ, ∃ error : ℝ → ℝ,
    HasFiniteLogarithmicMeasure E ∧
      error =o[atTopOutside E] truncatedSecondMainScale F σ ∧
      ∀ᶠ r in atTopOutside E,
        |coordinateRootCountingSum F r - rootCountingUpTo 1 r C.function| ≤
          error r

/-- Corollary 6.3 in the paper's original quantifiers, with the canonical
Casoratian realization hidden from the caller.  This is the formal statement
target; no proof is asserted here. -/
def FirstOrderTruncatedSecondMainPaperStatement : Prop :=
  ∀ (m : ℕ) (F : TropicalHolomorphicCurveRepresentation 1 m) (σ : ℝ),
    FirstOrderTruncatedSecondMainPaperHypotheses F σ →
      FirstOrderTruncatedSecondMainConclusion F
        (canonicalCurveCasoratianRealization F) σ

/-- Exact reduction of Corollary 6.3 to Theorem 6.2 plus the first-order
vanishing of the pole-discrepancy term.  The latter will follow from entirety
of shifts and finite maxima; it is kept explicit until that closure theorem
is connected to the canonical realizations. -/
theorem firstOrderTruncatedSecondMain_of_theorem62
    {m : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m)
    (S : CurveShiftRealizations F) (C : CurveCasoratianRealization F)
    (σ : ℝ) (hmain : TruncatedSecondMainConclusion F S C σ)
    (hpoles : ∀ r, casoratianPoleDiscrepancy F S C r = 0) :
    FirstOrderTruncatedSecondMainConclusion F C σ := by
  obtain ⟨E, error, hE, herror, hbound⟩ := hmain
  refine ⟨E, error, hE, herror, ?_⟩
  filter_upwards [hbound] with r hr
  simpa [truncatedSecondMainDifference, hpoles r, evenShiftCorrection] using hr

/-- The pole-discrepancy term in Theorem 6.2 vanishes identically for the
canonical first-order shifts and Casoratian. -/
theorem canonicalFirstOrderCasoratianPoleDiscrepancy_eq_zero
    {m : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m) (r : ℝ) :
    casoratianPoleDiscrepancy F
      (canonicalCurveShiftRealizations F)
      (canonicalCurveCasoratianRealization F) r = 0 := by
  classical
  unfold casoratianPoleDiscrepancy
  apply Finset.sum_eq_zero
  intro j hj
  have hjone : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hC : integratedCounting j r
      (canonicalCurveCasoratianRealization F).function = 0 :=
    integratedCounting_eq_zero_of_entire_any_order _
      (canonicalCurveCasoratianRealization_isTropicalEntire F) hjone r
  have hS : (∑ i : Fin (m + 1), integratedCounting j r
      ((canonicalCurveShiftRealizations F).shifted i i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    exact integratedCounting_eq_zero_of_entire_any_order _
      (canonicalCurveShiftRealizations_isTropicalEntire F i i) hjone r
  rw [hC, hS, sub_zero, abs_zero]

/-- Corollary 6.3 from the canonical Theorem 6.2 conclusion, with no extra
first-order pole hypothesis. -/
theorem firstOrderTruncatedSecondMain_of_canonicalTheorem62
    {m : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m) (σ : ℝ)
    (hmain : TruncatedSecondMainConclusion F
      (canonicalCurveShiftRealizations F)
      (canonicalCurveCasoratianRealization F) σ) :
    FirstOrderTruncatedSecondMainConclusion F
      (canonicalCurveCasoratianRealization F) σ := by
  exact firstOrderTruncatedSecondMain_of_theorem62 F
    (canonicalCurveShiftRealizations F)
    (canonicalCurveCasoratianRealization F) σ hmain
    (canonicalFirstOrderCasoratianPoleDiscrepancy_eq_zero F)

/-- A coordinate, regarded as a realization under the curve's first-order
ambient bound. -/
def firstOrderCoordinateRealization {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m) (i : Fin (m + 1)) :
    NthTropicalMeromorphicRealization 1 (fun x ↦ F.eval i x) where
  order := F.order i
  order_le := F.order_le i
  function := F.coordinate i
  eq_fun := fun _ ↦ rfl

/-- Automatic realization of `f_i ⊘ f_l = f_i-f_l` in ambient order one. -/
def firstOrderCoordinateQuotientRealization {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m)
    (i l : Fin (m + 1)) :
    NthTropicalMeromorphicRealization 1
      (fun x ↦ F.eval i x + (-1) * F.eval l x) :=
  (firstOrderCoordinateRealization F i).add
    ((firstOrderCoordinateRealization F l).smul (-1))

/-- For first-order curves the reference quotients required by Theorem 6.2
are automatic, as stated in the paper before Corollary 6.3. -/
def firstOrderWellDefinedReferenceQuotients {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m) :
    CurveWellDefinedReferenceQuotients F := by
  let l : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩
  exact
    { reference := l
      quotientOrder := fun i ↦ (firstOrderCoordinateQuotientRealization F i l).order
      quotientOrder_le := fun i ↦
        (firstOrderCoordinateQuotientRealization F i l).order_le
      quotient := fun i ↦ (firstOrderCoordinateQuotientRealization F i l).function
      quotient_eq := by
        intro i x
        rw [(firstOrderCoordinateQuotientRealization F i l).eq_fun]
        ring
      quotient_wellDefined := fun i ↦
        isWellDefined_of_order_le_one _
          (firstOrderCoordinateQuotientRealization F i l).order_le }

/-- Theorem 6.2 implies Corollary 6.3 in the original paper quantifiers.
This closes every first-order algebraic, realization, and analytic
obligation once the verified Theorem 6.2 is supplied below. -/
theorem firstOrderTruncatedSecondMainPaperStatement_of_theorem62
    (h62 : ∀ (m : ℕ) (F : TropicalHolomorphicCurveRepresentation 1 m),
      TruncatedSecondMainPaperStatement F) :
    FirstOrderTruncatedSecondMainPaperStatement := by
  intro m F σ h
  apply firstOrderTruncatedSecondMain_of_canonicalTheorem62 F σ
  apply h62 m F σ
  exact
    { reduced := h.reduced
      nonconstant := h.nonconstant
      quotients := firstOrderWellDefinedReferenceQuotients F
      rho2 := h.rho2
      hyperOrder_eq := h.hyperOrder_eq
      rho2_lt_one := h.rho2_lt_one
      sigma_pos := h.sigma_pos
      sigma_lt_one_sub_rho2 := h.sigma_lt_one_sub_rho2 }

/-- Corollary 6.3 in its original paper quantifiers, now discharged directly
from the fully verified Theorem 6.2. -/
theorem firstOrderTruncatedSecondMainPaperStatement_verified :
    FirstOrderTruncatedSecondMainPaperStatement :=
  firstOrderTruncatedSecondMainPaperStatement_of_theorem62
    (fun _m F ↦ truncatedSecondMainPaperStatement_verified F)

end

end NthTropicalNevanlinna
