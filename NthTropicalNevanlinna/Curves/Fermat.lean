import NthTropicalNevanlinna.Curves.SecondMain
import NthTropicalNevanlinna.Nevanlinna.Growth
import NthTropicalNevanlinna.Function.PresentationClosure

/-!
# Ordinary homogeneous Fermat polynomials and Theorem 5.8

This file formalizes the algebraic object and the Jensen/asymptotic assembly
in the proof of Theorem 5.8.  The endpoint sandwich based on (5a11) is proved
below.  The remaining pole-count argument (5a12)--(5a19) is developed from
the intrinsic multiplicity formula and the monotone slopes of a first-order
entire coordinate.
-/

open Filter Set
open scoped BigOperators Topology

namespace NthTropicalNevanlinna

noncomputable section

/-- An ordinary (non-tropical-addition) homogeneous Fermat polynomial
`∑ i, αᵢ xᵢⁿ`. -/
structure OrdinaryHomogeneousFermatPolynomial (m n : ℕ) where
  coefficient : Fin (m + 1) → ℝ

namespace OrdinaryHomogeneousFermatPolynomial

/-- The positivity condition on the coefficients in Theorem 5.8. -/
def HasPositiveCoefficients {m n : ℕ}
    (P : OrdinaryHomogeneousFermatPolynomial m n) : Prop :=
  ∀ i, 0 < P.coefficient i

/-- Ordinary evaluation: both the outer sum and the powers use the usual
real operations, not max-plus addition. -/
def eval {m n : ℕ} (P : OrdinaryHomogeneousFermatPolynomial m n)
    (x : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i, P.coefficient i * (x i) ^ n

/-- Pointwise ordinary Fermat composition with a first-order tropical curve. -/
def composeRaw {m n : ℕ} (P : OrdinaryHomogeneousFermatPolynomial m n)
    (F : TropicalHolomorphicCurveRepresentation 1 m) : ℝ → ℝ :=
  fun x ↦ P.eval (fun i ↦ F.eval i x)

/-- The lower coefficient `θ = min_i αᵢ`. -/
def coefficientMinimum {m n : ℕ}
    (P : OrdinaryHomogeneousFermatPolynomial m n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty P.coefficient

/-- The upper coefficient from the paper,
`Θ = 2^(n-1) * ∑ i, αᵢ`. -/
def upperCoefficient {m n : ℕ}
    (P : OrdinaryHomogeneousFermatPolynomial m n) : ℝ :=
  (2 : ℝ) ^ (n - 1) * ∑ i, P.coefficient i

theorem coefficientMinimum_pos {m n : ℕ}
    (P : OrdinaryHomogeneousFermatPolynomial m n)
    (hP : P.HasPositiveCoefficients) : 0 < P.coefficientMinimum := by
  exact (Finset.lt_inf'_iff _).2 (fun i _hi ↦ hP i)

theorem upperCoefficient_pos {m n : ℕ}
    (P : OrdinaryHomogeneousFermatPolynomial m n)
    (hP : P.HasPositiveCoefficients) : 0 < P.upperCoefficient := by
  apply mul_pos (pow_pos (by norm_num) _)
  exact Finset.sum_pos' (fun i _hi ↦ (hP i).le)
    ⟨0, Finset.mem_univ _, hP 0⟩

/-- A realization of the raw ordinary composition as a tropical meromorphic
function of exact order at most `n`.  Its construction requires the still
missing closure of global polynomial presentations under powers and finite
ordinary sums. -/
structure CurveComposition {m n : ℕ}
    (P : OrdinaryHomogeneousFermatPolynomial m n)
    (F : TropicalHolomorphicCurveRepresentation 1 m) where
  order : ℕ
  order_le : order ≤ n
  function : NthTropicalMeromorphicFunction order
  eq_composeRaw : ∀ x, function x = P.composeRaw F x

/-- The ordinary `n`-th power of one first-order coordinate, realized under
the ambient degree `n`. -/
private def coordinatePowerRealization {m n : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m) (i : Fin (m + 1)) :
    NthTropicalMeromorphicRealization n (fun x ↦ (F.eval i x) ^ n) := by
  let base : NthTropicalMeromorphicRealization (F.order i)
      (fun x ↦ F.eval i x) :=
    { order := F.order i
      order_le := le_rfl
      function := F.coordinate i
      eq_fun := fun _ ↦ rfl }
  have hbound : F.order i * n ≤ n := by
    calc
      F.order i * n ≤ 1 * n := Nat.mul_le_mul_right n (F.order_le i)
      _ = n := Nat.one_mul n
  exact (base.pow n).promote hbound

/-- Each powered and scaled coordinate is realizable under the ambient degree
`n`.  Positivity is needed later for its counting function, not for closure. -/
private def coordinateTermRealization {m n : ℕ}
    (P : OrdinaryHomogeneousFermatPolynomial m n)
    (F : TropicalHolomorphicCurveRepresentation 1 m) (i : Fin (m + 1)) :
    NthTropicalMeromorphicRealization n
      (fun x ↦ P.coefficient i * (F.eval i x) ^ n) :=
  (coordinatePowerRealization F i).smul (P.coefficient i)

/-- Ordinary Fermat composition is automatically a globally presented
tropical meromorphic function of some exact order at most `n`. -/
def curveComposition {m n : ℕ}
    (P : OrdinaryHomogeneousFermatPolynomial m n)
    (F : TropicalHolomorphicCurveRepresentation 1 m) : P.CurveComposition F := by
  let R := finsetSumRealization Finset.univ
    (fun i x ↦ P.coefficient i * (F.eval i x) ^ n)
    (P.coordinateTermRealization F)
  exact
    { order := R.order
      order_le := R.order_le
      function := R.function
      eq_composeRaw := fun x ↦ by
        rw [R.eq_fun]
        simp [composeRaw, eval] }

end OrdinaryHomogeneousFermatPolynomial

/-- The scale `T_f(r)^n` occurring throughout Theorem 5.8. -/
def curveCharacteristicPower {m n : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m) (r : ℝ) : ℝ :=
  (cartanCharacteristic F r) ^ n

/-- The growth condition displayed in (5f1).  Eventual positivity records the
implicit nonzero-denominator convention in the paper; without it Lean's
totalized identity `r / 0 = 0` would make the literal quotient misleading.
As in `growthOrder`, the quotient is cast to `EReal` so that `limsup` exists. -/
def OrdinaryFermatGrowthLimsupCondition {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m) : Prop :=
  (∀ᶠ r in atTop, 0 < cartanCharacteristic F r) ∧
    Filter.limsup
        (fun r : ℝ ↦ ((r / cartanCharacteristic F r : ℝ) : EReal)) atTop = 0

/-- The division-free Landau consequence used by the proof:
`r = o(T_f(r))`.  Deriving this from the literal limsup condition requires
eventual positivity/nonvanishing of `T_f`; that bridge is recorded explicitly
in the analytic-estimates structure below. -/
def CurveCharacteristicDominatesRadius {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m) : Prop :=
  (fun r : ℝ ↦ r) =o[atTop] fun r ↦ cartanCharacteristic F r

/-- The paper's limsup hypothesis, with the eventual positivity already
recorded in `OrdinaryFermatGrowthLimsupCondition`, really does imply the
division-free form `r = o(T_f(r))`. -/
theorem radius_isLittleO_characteristic_of_growthLimsupCondition
    {m : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hGrowth : OrdinaryFermatGrowthLimsupCondition F) :
    CurveCharacteristicDominatesRadius F := by
  let q : ℝ → ℝ := fun r ↦ r / cartanCharacteristic F r
  let qE : ℝ → EReal := fun r ↦ (q r : EReal)
  have hq_nonneg : ∀ᶠ r in atTop, (0 : EReal) ≤ qE r := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hGrowth.1] with r hr hT
    change (0 : EReal) ≤ ((r / cartanCharacteristic F r : ℝ) : EReal)
    exact_mod_cast div_nonneg hr.le hT.le
  have hliminf : (0 : EReal) ≤ Filter.liminf qE atTop :=
    Filter.le_liminf_of_le (by isBoundedDefault) hq_nonneg
  have hlimsup : Filter.limsup qE atTop ≤ (0 : EReal) := by
    simpa [qE, q] using hGrowth.2.le
  have hqE_tendsto : Tendsto qE atTop (𝓝 (0 : EReal)) :=
    tendsto_of_le_liminf_of_limsup_le hliminf hlimsup
  have hq_tendsto : Tendsto q atTop (𝓝 (0 : ℝ)) := by
    exact EReal.tendsto_coe.mp (by simpa [qE] using hqE_tendsto)
  rw [CurveCharacteristicDominatesRadius]
  have hzero : ∀ᶠ r in atTop,
      cartanCharacteristic F r = 0 → r = 0 := by
    filter_upwards [hGrowth.1] with r hT
    exact fun h ↦ (hT.ne' h).elim
  exact (Asymptotics.isLittleO_iff_tendsto' hzero).2 (by
    simpa [q] using hq_tendsto)

/-! ## Linear control of the negative tails of first-order entire functions -/

/-- On the positive ray, the negative part of a convex real function is at
most linear.  This is the rigorous convexity input behind the `O(r)` terms
around (5a17) in the paper. -/
theorem positiveTail_negativePart_isBigO_radius
    {q : ℕ} (f : NthTropicalMeromorphicFunction q) (hq : q ≤ 1)
    (hf : IsTropicalEntire f) :
    (fun r : ℝ ↦ maxPlusPositivePart (-f r)) =O[atTop] fun r : ℝ ↦ r := by
  have hconv := convexOn_univ_of_order_le_one_entire f hq hf
  let C : ℝ := |f 0| + |f 1 - f 0|
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  have hslope := (convexOn_iff_slope_mono_adjacent.mp hconv).2
    (x := (0 : ℝ)) (y := 1) (z := r)
    (Set.mem_univ 0) (Set.mem_univ r) (by norm_num) hr
  have hr1 : 0 < r - 1 := sub_pos.mpr hr
  have hlower : f 0 + r * (f 1 - f 0) ≤ f r := by
    have hslope' : f 1 - f 0 ≤ (f r - f 1) / (r - 1) := by
      norm_num at hslope ⊢
      exact hslope
    have hmul := (le_div_iff₀ hr1).mp hslope'
    nlinarith
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hneg : -f r ≤ C * r := by
    have h0 : -f 0 ≤ |f 0| := by
      simpa only [abs_neg] using le_abs_self (-f 0)
    have hdiff : -(f 1 - f 0) ≤ |f 1 - f 0| := by
      simpa only [abs_neg] using le_abs_self (-(f 1 - f 0))
    have hr0 : 0 ≤ r := le_trans (by norm_num) hr.le
    have hmulDiff := mul_le_mul_of_nonneg_left hdiff hr0
    have hCr : |f 0| ≤ |f 0| * r := by
      nlinarith [abs_nonneg (f 0)]
    nlinarith
  have hmax : maxPlusPositivePart (-f r) ≤ C * r := by
    rw [maxPlusPositivePart]
    exact max_le hneg (mul_nonneg hC (le_trans (by norm_num) hr.le))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg
    (maxPlusPositivePart_nonneg (-f r)), abs_of_pos (by linarith)]
  exact hmax

/-- Negative-ray counterpart of `positiveTail_negativePart_isBigO_radius`. -/
theorem negativeTail_negativePart_isBigO_radius
    {q : ℕ} (f : NthTropicalMeromorphicFunction q) (hq : q ≤ 1)
    (hf : IsTropicalEntire f) :
    (fun r : ℝ ↦ maxPlusPositivePart (-f (-r))) =O[atTop]
      fun r : ℝ ↦ r := by
  have hconv := convexOn_univ_of_order_le_one_entire f hq hf
  let C : ℝ := |f 0| + |f (-1) - f 0|
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  have hslope := (convexOn_iff_slope_mono_adjacent.mp hconv).2
    (x := -r) (y := (-1 : ℝ)) (z := 0)
    (Set.mem_univ (-r)) (Set.mem_univ 0) (by linarith) (by norm_num)
  have hr1 : 0 < r - 1 := sub_pos.mpr hr
  have hlower : f 0 + r * (f (-1) - f 0) ≤ f (-r) := by
    have hslope' : (f (-1) - f (-r)) / (r - 1) ≤ f 0 - f (-1) := by
      norm_num at hslope
      simpa [sub_eq_add_neg, add_comm] using hslope
    have hmul := (div_le_iff₀ hr1).mp hslope'
    nlinarith
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hneg : -f (-r) ≤ C * r := by
    have h0 : -f 0 ≤ |f 0| := by
      simpa only [abs_neg] using le_abs_self (-f 0)
    have hdiff : -(f (-1) - f 0) ≤ |f (-1) - f 0| :=
      by simpa only [abs_neg] using le_abs_self (-(f (-1) - f 0))
    have hr0 : 0 ≤ r := le_trans (by norm_num) hr.le
    have hmulDiff := mul_le_mul_of_nonneg_left hdiff hr0
    have hCr : |f 0| ≤ |f 0| * r := by
      nlinarith [abs_nonneg (f 0)]
    nlinarith
  have hmax : maxPlusPositivePart (-f (-r)) ≤ C * r := by
    rw [maxPlusPositivePart]
    exact max_le hneg (mul_nonneg hC (le_trans (by norm_num) hr.le))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg
    (maxPlusPositivePart_nonneg (-f (-r))), abs_of_pos (by linarith)]
  exact hmax

/-- Under (5f1), the positive-ray negative part of every coordinate is
`o(T_f)`. -/
theorem coordinate_positiveTail_negativePart_isLittleO_characteristic
    {m : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hGrowth : OrdinaryFermatGrowthLimsupCondition F) (i : Fin (m + 1)) :
    (fun r : ℝ ↦ maxPlusPositivePart (-F.eval i r)) =o[atTop]
      fun r ↦ cartanCharacteristic F r := by
  exact (positiveTail_negativePart_isBigO_radius
    (F.coordinate i) (F.order_le i) (F.coordinate_isTropicalEntire i)).trans_isLittleO
      (radius_isLittleO_characteristic_of_growthLimsupCondition F hGrowth)

/-- Under (5f1), the negative-ray negative part of every coordinate is
`o(T_f)`. -/
theorem coordinate_negativeTail_negativePart_isLittleO_characteristic
    {m : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hGrowth : OrdinaryFermatGrowthLimsupCondition F) (i : Fin (m + 1)) :
    (fun r : ℝ ↦ maxPlusPositivePart (-F.eval i (-r))) =o[atTop]
      fun r ↦ cartanCharacteristic F r := by
  exact (negativeTail_negativePart_isBigO_radius
    (F.coordinate i) (F.order_le i) (F.coordinate_isTropicalEntire i)).trans_isLittleO
      (radius_isLittleO_characteristic_of_growthLimsupCondition F hGrowth)

/-- The `n`-th powers of both coordinate negative tails are negligible on
the scale `T_f^n`. -/
theorem coordinate_negativeTailPowers_isLittleO_characteristicPower
    {m n : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hGrowth : OrdinaryFermatGrowthLimsupCondition F) (hn : 1 ≤ n)
    (i : Fin (m + 1)) :
    (fun r : ℝ ↦
        (maxPlusPositivePart (-F.eval i r)) ^ n +
          (maxPlusPositivePart (-F.eval i (-r))) ^ n) =o[atTop]
      fun r ↦ curveCharacteristicPower (n := n) F r := by
  have hpos := (coordinate_positiveTail_negativePart_isLittleO_characteristic
    F hGrowth i).pow (show 0 < n from hn)
  have hneg := (coordinate_negativeTail_negativePart_isLittleO_characteristic
    F hGrowth i).pow (show 0 < n from hn)
  simpa [curveCharacteristicPower] using hpos.add hneg

/-- If `a-b=o(b)`, then the same relative approximation survives every
positive natural power.  Keeping this lemma explicit avoids treating
`(1+o(1))^n=1+o(1)` as an informal algebraic rewrite. -/
theorem pow_sub_pow_isLittleO
    {a b : ℝ → ℝ} (h : (fun r ↦ a r - b r) =o[atTop] b)
    {n : ℕ} (hn : 1 ≤ n) :
    (fun r ↦ a r ^ n - b r ^ n) =o[atTop] fun r ↦ b r ^ n := by
  have ha : a =O[atTop] b := by
    have hsum := h.add_isBigO (Asymptotics.isBigO_refl b atTop)
    apply hsum.congr'
    · filter_upwards [] with r
      ring
    · exact EventuallyEq.rfl
  induction n, hn using Nat.le_induction with
  | base => simpa using h
  | succ n hnBase ih =>
      have hfirst := ih.mul_isBigO ha
      have hsecond := (Asymptotics.isBigO_refl (fun r ↦ b r ^ n) atTop).mul_isLittleO h
      have hsum := hfirst.add hsecond
      apply hsum.congr'
      · filter_upwards [] with r
        ring
      · filter_upwards [] with r
        rw [pow_succ]

/-! ## The nonnegative endpoint model in (5a11), (Pn1), and (Pn2) -/

/-- Replace every coordinate by its nonnegative part before taking the
ordinary Fermat power. -/
def positiveCoordinateFermatSum {m n : ℕ}
    (P : OrdinaryHomogeneousFermatPolynomial m n)
    (F : TropicalHolomorphicCurveRepresentation 1 m) (x : ℝ) : ℝ :=
  ∑ i, P.coefficient i * (maxPlusPositivePart (F.eval i x)) ^ n

/-- The nonnegative part of the largest homogeneous coordinate. -/
def positiveCurveMaximum {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m) (x : ℝ) : ℝ :=
  maxPlusPositivePart (curveCoordinateMaximum F x)

/-- The positive-part Fermat sum is bounded below by the smallest coefficient
times the `n`-th power of the positive coordinate maximum. -/
theorem coefficientMinimum_mul_positiveCurveMaximum_pow_le
    {m n : ℕ} (P : OrdinaryHomogeneousFermatPolynomial m n)
    (hP : P.HasPositiveCoefficients)
    (F : TropicalHolomorphicCurveRepresentation 1 m) (x : ℝ) :
    P.coefficientMinimum * (positiveCurveMaximum F x) ^ n ≤
      positiveCoordinateFermatSum P F x := by
  obtain ⟨i, _hi, himax⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (m + 1))).Nonempty)
    (fun i ↦ F.eval i x)
  have hcoeff : P.coefficientMinimum ≤ P.coefficient i :=
    Finset.inf'_le P.coefficient (Finset.mem_univ i)
  have hpow : 0 ≤ (maxPlusPositivePart (F.eval i x)) ^ n :=
    pow_nonneg (maxPlusPositivePart_nonneg _) _
  have hterm :
      P.coefficientMinimum * (maxPlusPositivePart (F.eval i x)) ^ n ≤
        P.coefficient i * (maxPlusPositivePart (F.eval i x)) ^ n :=
    mul_le_mul_of_nonneg_right hcoeff hpow
  have hsingle :
      P.coefficient i * (maxPlusPositivePart (F.eval i x)) ^ n ≤
        positiveCoordinateFermatSum P F x := by
    unfold positiveCoordinateFermatSum
    simpa only [Finset.sum_const_zero, Finset.sum_attach] using
      (Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin (m + 1))))
        (f := fun k ↦ P.coefficient k * (maxPlusPositivePart (F.eval k x)) ^ n)
        (fun k _hk ↦
          mul_nonneg (hP k).le (pow_nonneg (maxPlusPositivePart_nonneg _) _))
        (Finset.mem_univ i))
  have hpositiveMax : positiveCurveMaximum F x =
      maxPlusPositivePart (F.eval i x) := by
    unfold positiveCurveMaximum curveCoordinateMaximum
    rw [himax]
  rw [hpositiveMax]
  exact hterm.trans hsingle

/-- The corresponding pointwise upper bound uses the sum of coefficients. -/
theorem positiveCoordinateFermatSum_le_coefficientSum_mul
    {m n : ℕ} (P : OrdinaryHomogeneousFermatPolynomial m n)
    (hP : P.HasPositiveCoefficients)
    (F : TropicalHolomorphicCurveRepresentation 1 m) (x : ℝ) :
    positiveCoordinateFermatSum P F x ≤
      (∑ i, P.coefficient i) * (positiveCurveMaximum F x) ^ n := by
  unfold positiveCoordinateFermatSum
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _hi
  have hcoordinate : F.eval i x ≤ curveCoordinateMaximum F x :=
    coordinate_le_curveCoordinateMaximum F i x
  have hpositive : maxPlusPositivePart (F.eval i x) ≤ positiveCurveMaximum F x := by
    unfold positiveCurveMaximum maxPlusPositivePart
    exact max_le_max_right 0 hcoordinate
  have hpow := pow_le_pow_left₀ (maxPlusPositivePart_nonneg (F.eval i x)) hpositive n
  exact mul_le_mul_of_nonneg_left hpow (hP i).le

/-- Symmetric positive endpoint mean for the coordinate maximum. -/
def positiveCurveEndpointMean {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m) (r : ℝ) : ℝ :=
  (positiveCurveMaximum F r + positiveCurveMaximum F (-r)) / 2

/-- Symmetric positive endpoint mean of the coordinatewise Fermat sum. -/
def positiveFermatEndpointMean {m n : ℕ}
    (P : OrdinaryHomogeneousFermatPolynomial m n)
    (F : TropicalHolomorphicCurveRepresentation 1 m) (r : ℝ) : ℝ :=
  (positiveCoordinateFermatSum P F r +
      positiveCoordinateFermatSum P F (-r)) / 2

/-- Exact two-sided algebraic estimate for the nonnegative endpoint model.
All asymptotic error in Theorem 5.8 is therefore confined to removing the
negative parts and the fixed centering constant. -/
theorem positiveFermatEndpointMean_sandwich
    {m n : ℕ} (P : OrdinaryHomogeneousFermatPolynomial m n)
    (hP : P.HasPositiveCoefficients) (hn : 1 ≤ n)
    (F : TropicalHolomorphicCurveRepresentation 1 m) (r : ℝ) :
    P.coefficientMinimum * (positiveCurveEndpointMean F r) ^ n ≤
      positiveFermatEndpointMean P F r ∧
    positiveFermatEndpointMean P F r ≤
      P.upperCoefficient * (positiveCurveEndpointMean F r) ^ n := by
  let A := positiveCurveMaximum F r
  let B := positiveCurveMaximum F (-r)
  have hA : 0 ≤ A := maxPlusPositivePart_nonneg _
  have hB : 0 ≤ B := maxPlusPositivePart_nonneg _
  have hθ : 0 ≤ P.coefficientMinimum :=
    (P.coefficientMinimum_pos hP).le
  have hsumCoeff : 0 ≤ ∑ i, P.coefficient i :=
    Finset.sum_nonneg (fun i _hi ↦ (hP i).le)
  have hlowerR := coefficientMinimum_mul_positiveCurveMaximum_pow_le P hP F r
  have hlowerL := coefficientMinimum_mul_positiveCurveMaximum_pow_le P hP F (-r)
  have hupperR := positiveCoordinateFermatSum_le_coefficientSum_mul P hP F r
  have hupperL := positiveCoordinateFermatSum_le_coefficientSum_mul P hP F (-r)
  have hpowerMeanLower : ((A + B) / 2) ^ n ≤ (A ^ n + B ^ n) / 2 := by
    have h := add_pow_le hA hB n
    have htwo : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
    rw [div_pow]
    rw [show (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) by
      rw [← pow_succ', Nat.sub_add_cancel hn]]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * 2 ^ (n - 1))).2 (by
      nlinarith)
  have hpowerMeanUpper : (A ^ n + B ^ n) / 2 ≤ (A + B) ^ n / 2 := by
    exact div_le_div_of_nonneg_right
      (pow_add_pow_le hA hB (by omega)) (by norm_num)
  constructor
  · change P.coefficientMinimum * ((A + B) / 2) ^ n ≤
      (positiveCoordinateFermatSum P F r +
        positiveCoordinateFermatSum P F (-r)) / 2
    calc
      P.coefficientMinimum * ((A + B) / 2) ^ n ≤
          P.coefficientMinimum * ((A ^ n + B ^ n) / 2) :=
        mul_le_mul_of_nonneg_left hpowerMeanLower hθ
      _ ≤ (positiveCoordinateFermatSum P F r +
          positiveCoordinateFermatSum P F (-r)) / 2 := by
        change P.coefficientMinimum * A ^ n ≤
          positiveCoordinateFermatSum P F r at hlowerR
        change P.coefficientMinimum * B ^ n ≤
          positiveCoordinateFermatSum P F (-r) at hlowerL
        nlinarith
  · change (positiveCoordinateFermatSum P F r +
        positiveCoordinateFermatSum P F (-r)) / 2 ≤
      P.upperCoefficient * ((A + B) / 2) ^ n
    calc
      (positiveCoordinateFermatSum P F r +
          positiveCoordinateFermatSum P F (-r)) / 2 ≤
          (∑ i, P.coefficient i) * ((A ^ n + B ^ n) / 2) := by
        change positiveCoordinateFermatSum P F r ≤
          (∑ i, P.coefficient i) * A ^ n at hupperR
        change positiveCoordinateFermatSum P F (-r) ≤
          (∑ i, P.coefficient i) * B ^ n at hupperL
        nlinarith
      _ ≤ (∑ i, P.coefficient i) * ((A + B) ^ n / 2) :=
        mul_le_mul_of_nonneg_left hpowerMeanUpper hsumCoeff
      _ = P.upperCoefficient * ((A + B) / 2) ^ n := by
        unfold OrdinaryHomogeneousFermatPolynomial.upperCoefficient
        rw [div_pow]
        rw [show (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) by
          rw [← pow_succ', Nat.sub_add_cancel hn]]
        field_simp

/-- Pole-counting sum through the ambient order `upTo`. -/
def ambientPoleCounting {k : ℕ} (upTo : ℕ) (r : ℝ)
    (h : NthTropicalMeromorphicFunction k) : ℝ :=
  ∑ j ∈ Finset.Icc 1 upTo, integratedCounting j r h

/-- The nonnegative pole part of an intrinsic multiplicity. -/
def poleMultiplicity {k : ℕ} (h : NthTropicalMeromorphicFunction k)
    (j : ℕ) (x : ℝ) : ℝ :=
  max (-multiplicity h j x) 0

/-- Counting may equivalently be performed over all genuine singularities;
root terms disappear after taking the pole part.  This form is convenient for
ordinary sums, because intrinsic multiplicity is additive. -/
theorem integratedCounting_eq_sum_poleMultiplicity
    {k : ℕ} (h : NthTropicalMeromorphicFunction k) (j : ℕ) (r : ℝ) :
    integratedCounting j r h =
      (1 / 2) * ∑ x ∈ jthSingularPointsIn h j (-r) r,
        poleMultiplicity h j x * (r - |x|) ^ j := by
  classical
  unfold integratedCounting jthPolePoints jthSingularPointsIn
  congr 1
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hpole : multiplicity h j x < 0
  · have hne : multiplicity h j x ≠ 0 := ne_of_lt hpole
    simp [IsJthPole, hpole, hne, poleMultiplicity, rootOrPoleMultiplicity,
      abs_of_neg hpole, max_eq_left (neg_nonneg.mpr hpole.le)]
  · have hnonneg : 0 ≤ multiplicity h j x := le_of_not_gt hpole
    by_cases hzero : multiplicity h j x = 0
    · simp [IsJthPole, hzero]
    · simp [IsJthPole, hpole, hzero, poleMultiplicity,
        max_eq_right (neg_nonpos.mpr hnonneg)]

/-- Pole counting is subadditive under an ordinary pointwise sum.  This is
the fully intrinsic version of the first elementary counting inequality used
after (5a19). -/
theorem integratedCounting_add_le
    {nq ng nh : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng)
    (h : NthTropicalMeromorphicFunction nh)
    (hq : ∀ x, q x = g x + h x) (j : ℕ) (r : ℝ) :
    integratedCounting j r q ≤
      integratedCounting j r g + integratedCounting j r h := by
  classical
  let Sq := jthSingularPointsIn q j (-r) r
  let Sg := jthSingularPointsIn g j (-r) r
  let Sh := jthSingularPointsIn h j (-r) r
  let S := Sg ∪ Sh
  let weight : ℝ → ℝ := fun x ↦ (r - |x|) ^ j
  have hSqS : Sq ⊆ S := by
    intro x hx
    have hxq := mem_jthSingularPointsIn_iff.mp hx
    have hm := multiplicity_eq_add_of_eq_add q g h hq j x
    by_cases hg0 : multiplicity g j x = 0
    · have hh0 : multiplicity h j x ≠ 0 := by
        intro hh0
        apply hxq.2
        rw [hm, hg0, hh0, add_zero]
      exact Finset.mem_union_right Sg
        (mem_jthSingularPointsIn_iff.mpr ⟨hxq.1, hh0⟩)
    · exact Finset.mem_union_left Sh
        (mem_jthSingularPointsIn_iff.mpr ⟨hxq.1, hg0⟩)
  have hweight_nonneg {x : ℝ} (hx : x ∈ S) : 0 ≤ weight x := by
    have hxradial : x ∈ Ioo (-r) r := by
      rcases Finset.mem_union.mp hx with hxg | hxh
      · exact (mem_jthSingularPointsIn_iff.mp hxg).1
      · exact (mem_jthSingularPointsIn_iff.mp hxh).1
    exact pow_nonneg (sub_nonneg.mpr (abs_lt.mpr hxradial).le) _
  have hpole_le (x : ℝ) :
      poleMultiplicity q j x ≤ poleMultiplicity g j x + poleMultiplicity h j x := by
    have hm := multiplicity_eq_add_of_eq_add q g h hq j x
    unfold poleMultiplicity
    apply max_le
    · calc
        -(multiplicity q j x) =
            -multiplicity g j x + -multiplicity h j x := by rw [hm]; ring
        _ ≤ max (-multiplicity g j x) 0 + max (-multiplicity h j x) 0 :=
          add_le_add (le_max_left _ _) (le_max_left _ _)
    · exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hmain :
      (∑ x ∈ Sq, poleMultiplicity q j x * weight x) ≤
        ∑ x ∈ S,
          (poleMultiplicity g j x + poleMultiplicity h j x) * weight x := by
    calc
      (∑ x ∈ Sq, poleMultiplicity q j x * weight x) ≤
          ∑ x ∈ Sq,
            (poleMultiplicity g j x + poleMultiplicity h j x) * weight x := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_right (hpole_le x)
          (hweight_nonneg (hSqS hx))
      _ ≤ ∑ x ∈ S,
          (poleMultiplicity g j x + poleMultiplicity h j x) * weight x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hSqS
        intro x hxS _hxSq
        exact mul_nonneg
          (add_nonneg (le_max_right _ _) (le_max_right _ _))
          (hweight_nonneg hxS)
  have hsum_g :
      (∑ x ∈ S, poleMultiplicity g j x * weight x) =
        ∑ x ∈ Sg, poleMultiplicity g j x * weight x := by
    symm
    apply Finset.sum_subset (Finset.subset_union_left)
    intro x hxS hxnot
    have hg0 : multiplicity g j x = 0 := by
      by_contra hg0
      have hxradial : x ∈ Ioo (-r) r := by
        rcases Finset.mem_union.mp hxS with hxg | hxh
        · exact (mem_jthSingularPointsIn_iff.mp hxg).1
        · exact (mem_jthSingularPointsIn_iff.mp hxh).1
      exact hxnot (mem_jthSingularPointsIn_iff.mpr ⟨hxradial, hg0⟩)
    simp [poleMultiplicity, hg0]
  have hsum_h :
      (∑ x ∈ S, poleMultiplicity h j x * weight x) =
        ∑ x ∈ Sh, poleMultiplicity h j x * weight x := by
    symm
    apply Finset.sum_subset (Finset.subset_union_right)
    intro x hxS hxnot
    have hh0 : multiplicity h j x = 0 := by
      by_contra hh0
      have hxradial : x ∈ Ioo (-r) r := by
        rcases Finset.mem_union.mp hxS with hxg | hxh
        · exact (mem_jthSingularPointsIn_iff.mp hxg).1
        · exact (mem_jthSingularPointsIn_iff.mp hxh).1
      exact hxnot (mem_jthSingularPointsIn_iff.mpr ⟨hxradial, hh0⟩)
    simp [poleMultiplicity, hh0]
  rw [integratedCounting_eq_sum_poleMultiplicity,
    integratedCounting_eq_sum_poleMultiplicity,
    integratedCounting_eq_sum_poleMultiplicity]
  dsimp [Sq, Sg, Sh, S, weight] at hmain hsum_g hsum_h ⊢
  have hsplit :
      (∑ x ∈ jthSingularPointsIn g j (-r) r ∪
          jthSingularPointsIn h j (-r) r,
        (poleMultiplicity g j x + poleMultiplicity h j x) *
          (r - |x|) ^ j) =
        (∑ x ∈ jthSingularPointsIn g j (-r) r ∪
            jthSingularPointsIn h j (-r) r,
          poleMultiplicity g j x * (r - |x|) ^ j) +
        ∑ x ∈ jthSingularPointsIn g j (-r) r ∪
            jthSingularPointsIn h j (-r) r,
          poleMultiplicity h j x * (r - |x|) ^ j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hsplit, hsum_g, hsum_h] at hmain
  linarith

private theorem leftPieceAt_eq_C_mul_of_eq_smul
    {nq ng : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (c : ℝ)
    (hq : ∀ x, q x = c * g x) (x : ℝ) :
    q.presentation.leftPieceAt x =
      Polynomial.C c * g.presentation.leftPieceAt x := by
  obtain ⟨aq, haq, hqgerm⟩ := q.presentation.exists_left_germ_interval x
  obtain ⟨ag, hag, hggerm⟩ := g.presentation.exists_left_germ_interval x
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Ioo_infinite (max_lt haq hag)).mono
  intro y hy
  have hyq : y ∈ Ioo aq x :=
    ⟨(le_max_left aq ag).trans_lt hy.1, hy.2⟩
  have hyg : y ∈ Ioo ag x :=
    ⟨(le_max_right aq ag).trans_lt hy.1, hy.2⟩
  change (q.presentation.leftPieceAt x).eval y =
    (Polynomial.C c * g.presentation.leftPieceAt x).eval y
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [← hqgerm y hyq, ← hggerm y hyg, hq y]

private theorem rightPieceAt_eq_C_mul_of_eq_smul
    {nq ng : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (c : ℝ)
    (hq : ∀ x, q x = c * g x) (x : ℝ) :
    q.presentation.rightPieceAt x =
      Polynomial.C c * g.presentation.rightPieceAt x := by
  obtain ⟨bq, hbq, hqgerm⟩ := q.presentation.exists_right_germ_interval x
  obtain ⟨bg, hbg, hggerm⟩ := g.presentation.exists_right_germ_interval x
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Ioo_infinite (lt_min hbq hbg)).mono
  intro y hy
  have hyq : y ∈ Ioo x bq :=
    ⟨hy.1, hy.2.trans_le (min_le_left bq bg)⟩
  have hyg : y ∈ Ioo x bg :=
    ⟨hy.1, hy.2.trans_le (min_le_right bq bg)⟩
  change (q.presentation.rightPieceAt x).eval y =
    (Polynomial.C c * g.presentation.rightPieceAt x).eval y
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [← hqgerm y hyq, ← hggerm y hyg, hq y]

private theorem normalizedPolynomialJet_C_mul
    (c : ℝ) (p : Polynomial ℝ) (j : ℕ) (x : ℝ) :
    normalizedPolynomialJet (Polynomial.C c * p) j x =
      c * normalizedPolynomialJet p j x := by
  rw [← Polynomial.smul_eq_C_mul]
  simp [normalizedPolynomialJet]

/-- Normalized jet of a natural power of an affine polynomial.  This is the
precise algebraic identity underlying equation (5a12). -/
theorem normalizedPolynomialJet_pow_of_natDegree_le_one
    (p : Polynomial ℝ) (hp : p.natDegree ≤ 1)
    (n j : ℕ) (x : ℝ) :
    normalizedPolynomialJet (p ^ n) j x =
      (n.choose j : ℝ) * (p.eval x) ^ (n - j) *
        (normalizedPolynomialJet p 1 x) ^ j := by
  rw [normalizedPolynomialJet, ← Polynomial.taylor_coeff,
    Polynomial.taylor_pow, Polynomial.eq_X_add_C_of_natDegree_le_one hp]
  have ht : Polynomial.taylor x
      (Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0)) =
      Polynomial.C (p.coeff 1 * x + p.coeff 0) +
        Polynomial.C (p.coeff 1) * Polynomial.X := by
    simp [Polynomial.taylor_apply]
    ring
  rw [ht]
  have hpoly :
      (Polynomial.C (p.coeff 1 * x + p.coeff 0) +
          Polynomial.C (p.coeff 1) * Polynomial.X) ^ n =
        ((Polynomial.X + Polynomial.C (p.coeff 1 * x + p.coeff 0)) ^ n).comp
          (Polynomial.C (p.coeff 1) * Polynomial.X) := by
    change _ = (Polynomial.compRingHom
      (Polynomial.C (p.coeff 1) * Polynomial.X))
        ((Polynomial.X + Polynomial.C (p.coeff 1 * x + p.coeff 0)) ^ n)
    rw [map_pow]
    congr 1
    simp
    ring
  rw [hpoly, Polynomial.comp_C_mul_X_coeff,
    Polynomial.coeff_X_add_C_pow]
  have hjet : normalizedPolynomialJet
      (Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0))
        1 x = p.coeff 1 := by
    simp [normalizedPolynomialJet]
  rw [hjet]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  ring

private theorem leftPieceAt_eq_pow_of_eq_pow
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng)
    (hq : ∀ x, q x = (g x) ^ d) (x : ℝ) :
    q.presentation.leftPieceAt x = (g.presentation.leftPieceAt x) ^ d := by
  obtain ⟨aq, haq, hqgerm⟩ := q.presentation.exists_left_germ_interval x
  obtain ⟨ag, hag, hggerm⟩ := g.presentation.exists_left_germ_interval x
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Ioo_infinite (max_lt haq hag)).mono
  intro y hy
  have hyq : y ∈ Ioo aq x :=
    ⟨(le_max_left aq ag).trans_lt hy.1, hy.2⟩
  have hyg : y ∈ Ioo ag x :=
    ⟨(le_max_right aq ag).trans_lt hy.1, hy.2⟩
  change (q.presentation.leftPieceAt x).eval y =
    ((g.presentation.leftPieceAt x) ^ d).eval y
  simp only [Polynomial.eval_pow]
  rw [← hqgerm y hyq, ← hggerm y hyg, hq y]

private theorem rightPieceAt_eq_pow_of_eq_pow
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng)
    (hq : ∀ x, q x = (g x) ^ d) (x : ℝ) :
    q.presentation.rightPieceAt x = (g.presentation.rightPieceAt x) ^ d := by
  obtain ⟨bq, hbq, hqgerm⟩ := q.presentation.exists_right_germ_interval x
  obtain ⟨bg, hbg, hggerm⟩ := g.presentation.exists_right_germ_interval x
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Ioo_infinite (lt_min hbq hbg)).mono
  intro y hy
  have hyq : y ∈ Ioo x bq :=
    ⟨hy.1, hy.2.trans_le (min_le_left bq bg)⟩
  have hyg : y ∈ Ioo x bg :=
    ⟨hy.1, hy.2.trans_le (min_le_right bq bg)⟩
  change (q.presentation.rightPieceAt x).eval y =
    ((g.presentation.rightPieceAt x) ^ d).eval y
  simp only [Polynomial.eval_pow]
  rw [← hqgerm y hyq, ← hggerm y hyg, hq y]

/-- Intrinsic version of equation (5a12), valid for every realization of the
ordinary power and for every exact coordinate order at most one. -/
theorem multiplicity_power_of_order_le_one
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hq : ∀ x, q x = (g x) ^ d) (j : ℕ) (x : ℝ) :
    multiplicity q j x =
      (d.choose j : ℝ) * (g x) ^ (d - j) *
        (rightSign x ^ (j + 1) *
            (normalizedPolynomialJet (g.presentation.rightPieceAt x) 1 x) ^ j -
          leftSign x ^ (j + 1) *
            (normalizedPolynomialJet (g.presentation.leftPieceAt x) 1 x) ^ j) := by
  simp only [multiplicity, multiplicityUsingPresentation]
  rw [leftPieceAt_eq_pow_of_eq_pow q g hq x,
    rightPieceAt_eq_pow_of_eq_pow q g hq x,
    normalizedPolynomialJet_pow_of_natDegree_le_one _
      ((g.presentation.rightPieceAt_natDegree_le x).trans hng),
    normalizedPolynomialJet_pow_of_natDegree_le_one _
      ((g.presentation.leftPieceAt_natDegree_le x).trans hng),
    g.presentation.rightPieceAt_eval, g.presentation.leftPieceAt_eval]
  ring

/-! ### Monotone affine slopes of a first-order entire coordinate -/

/-- The slope of the affine piece with presentation index `i`. -/
def presentationSlope {q : ℕ} {f : ℝ → ℝ}
    (P : PolynomialPresentation q f) (i : ℤ) : ℝ :=
  (P.piece i).coeff 1

theorem normalizedPolynomialJet_one_eq_presentationSlope
    {q : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation q f)
    (hq : q ≤ 1) (i : ℤ) (x : ℝ) :
    normalizedPolynomialJet (P.piece i) 1 x = presentationSlope P i := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one
    ((P.piece_natDegree_le i).trans hq)]
  simp [normalizedPolynomialJet, presentationSlope]

/-- At every presentation cut, the first multiplicity is exactly the jump
of the affine slope.  The radial signs disappear because their exponent is
two; this remains true at the distinguished cut `0`. -/
theorem firstMultiplicity_at_cutPoint_eq_slope_sub
    {q : ℕ} (f : NthTropicalMeromorphicFunction q) (hq : q ≤ 1)
    (P : PolynomialPresentation q f) (i : ℤ) :
    multiplicity f 1 (P.cutPoint i) =
      presentationSlope P (i + 1) - presentationSlope P i := by
  rw [multiplicity_cutPoint_of_presentation]
  simp only [presentationMultiplicityAtCutPoint]
  rw [normalizedPolynomialJet_one_eq_presentationSlope P hq,
    normalizedPolynomialJet_one_eq_presentationSlope P hq]
  unfold rightSign leftSign
  split_ifs <;> ring

/-- Convexity/entirety in the exact form needed by (5a12): the slopes of any
chosen presentation form a monotone integer-indexed sequence. -/
theorem presentationSlope_monotone_of_entire
    {q : ℕ} (f : NthTropicalMeromorphicFunction q) (hq : q ≤ 1)
    (hf : IsTropicalEntire f) (P : PolynomialPresentation q f) :
    Monotone (presentationSlope P) := by
  by_cases hq0 : q = 0
  · subst q
    have hslope_zero : ∀ i, presentationSlope P i = 0 := by
      intro i
      unfold presentationSlope
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      exact (P.piece_natDegree_le i).trans_lt (by omega)
    intro i k hik
    rw [hslope_zero i, hslope_zero k]
  apply monotone_int_of_le_succ
  intro i
  have hmult := (isTropicalEntire_iff_multiplicity_nonneg f).mp hf
    (P.cutPoint i) 1 (by omega) (by omega)
  rw [firstMultiplicity_at_cutPoint_eq_slope_sub f hq P i] at hmult
  linarith

/-- Apart from the distinguished origin, taking an ordinary power creates no
new singular location: every nonzero multiplicity of `q=f^d` occurs at a cut
of any chosen presentation of `f`.  The origin is already the normalized cut
`P.cutPoint 0`, so the conclusion has no exceptional point. -/
theorem multiplicity_power_eq_zero_or_sourceCutPoint
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hq : ∀ x, q x = (g x) ^ d) (P : PolynomialPresentation ng g)
    (j : ℕ) (x : ℝ) :
    multiplicity q j x = 0 ∨ ∃ i : ℤ, x = P.cutPoint i := by
  by_cases hx0 : x = 0
  · right
    exact ⟨0, by simpa [hx0] using P.cutPoint_zero.symm⟩
  rcases multiplicity_eq_zero_or_cutPoint_of_presentation g P 1 x with
    hzero | ⟨i, hxi, _hmult⟩
  · left
    have hslope :
        normalizedPolynomialJet (g.presentation.rightPieceAt x) 1 x =
          normalizedPolynomialJet (g.presentation.leftPieceAt x) 1 x := by
      have hm := hzero
      simp only [multiplicity, multiplicityUsingPresentation] at hm
      rcases lt_or_gt_of_ne hx0 with hx | hx
      · rw [rightSign_of_neg hx, leftSign_of_nonpos hx.le] at hm
        norm_num at hm
        linarith
      · rw [rightSign_of_nonneg hx.le, leftSign_of_pos hx] at hm
        norm_num at hm
        linarith
    rw [multiplicity_power_of_order_le_one q g hng hq j x, hslope]
    rcases lt_or_gt_of_ne hx0 with hx | hx
    · rw [rightSign_of_neg hx, leftSign_of_nonpos hx.le]
      ring
    · rw [rightSign_of_nonneg hx.le, leftSign_of_pos hx]
      ring
  · exact Or.inr ⟨i, hxi⟩

/-- Consequently the intrinsic singular finset of a power is contained in
the source presentation's finite cut set on the same interval. -/
theorem jthSingularPointsIn_power_subset_sourceCuts
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hq : ∀ x, q x = (g x) ^ d) (P : PolynomialPresentation ng g)
    (j : ℕ) (a b : ℝ) :
    ↑(jthSingularPointsIn q j a b) ⊆ ↑(presentationCutPointsIn P a b) := by
  intro x hx
  have hx' := (mem_jthSingularPointsIn_iff.mp hx)
  rcases multiplicity_power_eq_zero_or_sourceCutPoint q g hng hq P j x with
    hzero | ⟨i, hxi⟩
  · exact (hx'.2 hzero).elim
  · exact mem_presentationCutPointsIn_of_eq_cutPoint P hx'.1 hxi

/-- Reindex the intrinsic pole count of a power by the finite integer interval
of any source presentation.  Absolute values on the radial weight make the
two harmless boundary indices nonnegative; on actual singularities in
`(-r,r)` they agree with the original weight. -/
theorem integratedCounting_power_le_sourceIndexSum
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hq : ∀ x, q x = (g x) ^ d) (P : PolynomialPresentation ng g)
    (j : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    integratedCounting j r q ≤
      (1 / 2) *
        ∑ i ∈ Finset.Ico (presentationIntervalIndex P (-r))
            (presentationIntervalIndex P r),
          poleMultiplicity q j (P.cutPoint i) *
            abs (r - |P.cutPoint i|) ^ j := by
  classical
  rw [integratedCounting_eq_sum_poleMultiplicity]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  let S := jthSingularPointsIn q j (-r) r
  let C := presentationCutPointsIn P (-r) r
  let I := Finset.Ico (presentationIntervalIndex P (-r))
    (presentationIntervalIndex P r)
  let term : ℝ → ℝ := fun x ↦
    poleMultiplicity q j x * abs (r - |x|) ^ j
  have hSC : ↑S ⊆ (↑C : Set ℝ) :=
    jthSingularPointsIn_power_subset_sourceCuts q g hng hq P j (-r) r
  have hterm_nonneg (x : ℝ) : 0 ≤ term x :=
    mul_nonneg (by simp [poleMultiplicity]) (pow_nonneg (abs_nonneg _) _)
  have hsource :
      (∑ x ∈ S, poleMultiplicity q j x * (r - |x|) ^ j) ≤
        ∑ x ∈ C, term x := by
    calc
      (∑ x ∈ S, poleMultiplicity q j x * (r - |x|) ^ j) =
          ∑ x ∈ S, term x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxIoo := (mem_jthSingularPointsIn_iff.mp hx).1
        have hxr : |x| < r := (abs_lt).2 hxIoo
        simp [term, abs_of_pos (sub_pos.mpr hxr)]
      _ ≤ ∑ x ∈ C, term x := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hSC
          (fun x _hxC _hxS ↦ hterm_nonneg x)
  refine hsource.trans ?_
  change (∑ x ∈ C, term x) ≤ ∑ i ∈ I, term (P.cutPoint i)
  have hCsubset : C ⊆ I.image P.cutPoint := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  calc
    (∑ x ∈ C, term x) ≤ ∑ x ∈ I.image P.cutPoint, term x :=
      Finset.sum_le_sum_of_subset_of_nonneg hCsubset
        (fun x _hx _hxC ↦ hterm_nonneg x)
    _ = ∑ i ∈ I, term (P.cutPoint i) := by
      rw [Finset.sum_image]
      exact P.cutPoint_strictMono.injective.injOn

/-- Equation (5a12) evaluated at the `i`-th cut of an arbitrary source
presentation. -/
theorem multiplicity_power_at_sourceCutPoint
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hq : ∀ x, q x = (g x) ^ d) (P : PolynomialPresentation ng g)
    (j : ℕ) (i : ℤ) :
    multiplicity q j (P.cutPoint i) =
      (d.choose j : ℝ) * (g (P.cutPoint i)) ^ (d - j) *
        (rightSign (P.cutPoint i) ^ (j + 1) *
            (presentationSlope P (i + 1)) ^ j -
          leftSign (P.cutPoint i) ^ (j + 1) *
            (presentationSlope P i) ^ j) := by
  rw [multiplicity_power_of_order_le_one q g hng hq]
  have hmem : P.cutPoint i ∈ Ioc (P.cutPoint (i - 1)) (P.cutPoint i) :=
    ⟨P.cutPoint_strictMono (by omega), le_rfl⟩
  have hindex : presentationIntervalIndex P (P.cutPoint i) = i :=
    presentationIntervalIndex_eq_of_mem P hmem
  have hleftP : P.leftPieceAt (P.cutPoint i) = P.piece i := by
    simp [PolynomialPresentation.leftPieceAt, hindex]
  have hrightP : P.rightPieceAt (P.cutPoint i) = P.piece (i + 1) := by
    simp [PolynomialPresentation.rightPieceAt, hindex]
  have hleft : g.presentation.leftPieceAt (P.cutPoint i) = P.piece i := by
    rw [← hleftP]
    exact g.presentation.leftPieceAt_eq P (P.cutPoint i)
  have hright : g.presentation.rightPieceAt (P.cutPoint i) = P.piece (i + 1) := by
    rw [← hrightP]
    exact g.presentation.rightPieceAt_eq P (P.cutPoint i)
  rw [hleft, hright,
    normalizedPolynomialJet_one_eq_presentationSlope P hng,
    normalizedPolynomialJet_one_eq_presentationSlope P hng]

/-- Absolute local bound extracted from (5a12).  It is deliberately stated
before the tail case split, so both rays use the same estimate. -/
theorem poleMultiplicity_power_at_sourceCutPoint_le
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hq : ∀ x, q x = (g x) ^ d) (P : PolynomialPresentation ng g)
    (j : ℕ) (i : ℤ) (hi : i ≠ 0) :
    poleMultiplicity q j (P.cutPoint i) ≤
      (d.choose j : ℝ) * |g (P.cutPoint i)| ^ (d - j) *
        |(presentationSlope P (i + 1)) ^ j -
          (presentationSlope P i) ^ j| := by
  rw [poleMultiplicity, multiplicity_power_at_sourceCutPoint q g hng hq P]
  have hchoose : 0 ≤ (d.choose j : ℝ) := by positivity
  have hpow : 0 ≤ |g (P.cutPoint i)| ^ (d - j) := pow_nonneg (abs_nonneg _) _
  have hmaxAbs : max
      (-((d.choose j : ℝ) * g (P.cutPoint i) ^ (d - j) *
        (rightSign (P.cutPoint i) ^ (j + 1) * presentationSlope P (i + 1) ^ j -
          leftSign (P.cutPoint i) ^ (j + 1) * presentationSlope P i ^ j))) 0 ≤
      |(d.choose j : ℝ) * g (P.cutPoint i) ^ (d - j) *
        (rightSign (P.cutPoint i) ^ (j + 1) * presentationSlope P (i + 1) ^ j -
          leftSign (P.cutPoint i) ^ (j + 1) * presentationSlope P i ^ j)| := by
    exact max_le (neg_le_abs _) (abs_nonneg _)
  refine hmaxAbs.trans ?_
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hchoose]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hchoose hpow)
  have hcut_ne : P.cutPoint i ≠ 0 := by
    rw [← P.cutPoint_zero]
    exact P.cutPoint_strictMono.injective.ne hi
  rcases lt_or_gt_of_ne hcut_ne with hx | hx
  · rw [rightSign_of_neg hx, leftSign_of_nonpos hx.le]
    rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  · rw [rightSign_of_nonneg hx.le, leftSign_of_pos hx]
    simp

theorem poleMultiplicity_power_at_positiveCut_eq_zero
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hgEntire : IsTropicalEntire g) (hq : ∀ x, q x = (g x) ^ d)
    (P : PolynomialPresentation ng g) (j : ℕ) {i : ℤ} (hi : 0 < i)
    (hg : 0 ≤ g (P.cutPoint i)) (hs : 0 ≤ presentationSlope P i) :
    poleMultiplicity q j (P.cutPoint i) = 0 := by
  have hmono := presentationSlope_monotone_of_entire g hng hgEntire P
  have hsle : presentationSlope P i ≤ presentationSlope P (i + 1) :=
    hmono (by omega)
  have hsnext : 0 ≤ presentationSlope P (i + 1) := hs.trans hsle
  have hpowSlope : presentationSlope P i ^ j ≤
      presentationSlope P (i + 1) ^ j :=
    pow_le_pow_left₀ hs hsle j
  have hx : 0 < P.cutPoint i := by
    rw [← P.cutPoint_zero]
    exact P.cutPoint_strictMono hi
  rw [poleMultiplicity,
    multiplicity_power_at_sourceCutPoint q g hng hq P]
  rw [rightSign_of_nonneg hx.le, leftSign_of_pos hx]
  simp only [one_pow, one_mul]
  rw [max_eq_right]
  exact neg_nonpos.mpr (mul_nonneg
    (mul_nonneg (by positivity) (pow_nonneg hg _)) (sub_nonneg.mpr hpowSlope))

theorem poleMultiplicity_power_at_negativeCut_eq_zero
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hgEntire : IsTropicalEntire g) (hq : ∀ x, q x = (g x) ^ d)
    (P : PolynomialPresentation ng g) (j : ℕ) {i : ℤ} (hi : i < 0)
    (hg : 0 ≤ g (P.cutPoint i))
    (hs : presentationSlope P (i + 1) ≤ 0) :
    poleMultiplicity q j (P.cutPoint i) = 0 := by
  have hmono := presentationSlope_monotone_of_entire g hng hgEntire P
  have hsle : presentationSlope P i ≤ presentationSlope P (i + 1) :=
    hmono (by omega)
  have hsi : presentationSlope P i ≤ 0 := hsle.trans hs
  have hnegLe : -presentationSlope P (i + 1) ≤ -presentationSlope P i :=
    neg_le_neg hsle
  have hpowSlope : (-presentationSlope P (i + 1)) ^ j ≤
      (-presentationSlope P i) ^ j :=
    pow_le_pow_left₀ (neg_nonneg.mpr hs) hnegLe j
  have hx : P.cutPoint i < 0 := by
    rw [← P.cutPoint_zero]
    exact P.cutPoint_strictMono hi
  have hradial : 0 ≤ (-1 : ℝ) ^ (j + 1) *
      (presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j) := by
    calc
      0 ≤ (-presentationSlope P i) ^ j -
          (-presentationSlope P (i + 1)) ^ j := sub_nonneg.mpr hpowSlope
      _ = (-1 : ℝ) ^ (j + 1) *
          (presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j) := by
        rw [neg_pow (presentationSlope P i) j,
          neg_pow (presentationSlope P (i + 1)) j, pow_succ]
        ring
  rw [poleMultiplicity,
    multiplicity_power_at_sourceCutPoint q g hng hq P]
  rw [rightSign_of_neg hx, leftSign_of_nonpos hx.le]
  rw [← mul_sub]
  rw [max_eq_right]
  exact neg_nonpos.mpr (mul_nonneg
    (mul_nonneg (by positivity) (pow_nonneg hg _)) hradial)

theorem presentationPiece_eval_sub_eq_slope_mul_sub
    {q : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation q f)
    (hq : q ≤ 1) (i : ℤ) (x y : ℝ) :
    (P.piece i).eval y - (P.piece i).eval x =
      presentationSlope P i * (y - x) := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one
    ((P.piece_natDegree_le i).trans hq)]
  simp [presentationSlope]
  ring

/-- A genuinely positive affine slope forces an entire first-order function
to become nonnegative on the right. -/
theorem eventually_nonneg_atTop_of_positive_presentationSlope
    {q : ℕ} (g : NthTropicalMeromorphicFunction q) (hq : q ≤ 1)
    (hgEntire : IsTropicalEntire g) (P : PolynomialPresentation q g)
    {i : ℤ} (hi : 0 < presentationSlope P i) :
    ∀ᶠ x in atTop, 0 ≤ g x := by
  let a := P.cutPoint (i - 1)
  let b := P.cutPoint i
  have hab : a < b := P.cutPoint_strictMono (by omega)
  have hga : g a = (P.piece i).eval a := by
    apply P.eq_piece i
    constructor
    · dsimp [a]
      exact le_rfl
    · dsimp [a, b]
      exact hab.le
  have hgb : g b = (P.piece i).eval b := P.eq_piece i ⟨hab.le, le_rfl⟩
  have hsecant : (g b - g a) / (b - a) = presentationSlope P i := by
    rw [hga, hgb, presentationPiece_eval_sub_eq_slope_mul_sub P hq]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
  have hconv := convexOn_univ_of_order_le_one_entire g hq hgEntire
  filter_upwards [eventually_gt_atTop b,
    eventually_ge_atTop (b + max 0 (-g b / presentationSlope P i))] with x hbx hx
  have hslope := (convexOn_iff_slope_mono_adjacent.mp hconv).2
    (Set.mem_univ a) (Set.mem_univ x) hab hbx
  rw [hsecant] at hslope
  have hmul := (le_div_iff₀ (sub_pos.mpr hbx)).mp hslope
  have hthreshold : -g b ≤ presentationSlope P i * (x - b) := by
    have hmax : -g b / presentationSlope P i ≤
        max 0 (-g b / presentationSlope P i) := le_max_right _ _
    have hdiv : -g b / presentationSlope P i ≤ x - b := by
      linarith [hmax, hx]
    have hmul' := (div_le_iff₀ hi).mp hdiv
    nlinarith
  nlinarith

/-- A genuinely negative affine slope forces an entire first-order function
to become nonnegative on the left. -/
theorem eventually_nonneg_atBot_of_negative_presentationSlope
    {q : ℕ} (g : NthTropicalMeromorphicFunction q) (hq : q ≤ 1)
    (hgEntire : IsTropicalEntire g) (P : PolynomialPresentation q g)
    {i : ℤ} (hi : presentationSlope P i < 0) :
    ∀ᶠ x in atBot, 0 ≤ g x := by
  let a := P.cutPoint (i - 1)
  let b := P.cutPoint i
  have hab : a < b := P.cutPoint_strictMono (by omega)
  have hga : g a = (P.piece i).eval a := by
    apply P.eq_piece i
    constructor
    · dsimp [a]
      exact le_rfl
    · dsimp [a, b]
      exact hab.le
  have hgb : g b = (P.piece i).eval b := P.eq_piece i ⟨hab.le, le_rfl⟩
  have hsecant : (g b - g a) / (b - a) = presentationSlope P i := by
    rw [hga, hgb, presentationPiece_eval_sub_eq_slope_mul_sub P hq]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
  have hconv := convexOn_univ_of_order_le_one_entire g hq hgEntire
  filter_upwards [eventually_lt_atBot a,
    eventually_le_atBot (a - max 0 (g a / presentationSlope P i))] with x hxa hx
  have hslope := (convexOn_iff_slope_mono_adjacent.mp hconv).2
    (Set.mem_univ x) (Set.mem_univ b) hxa hab
  rw [hsecant] at hslope
  have hden : 0 < a - x := sub_pos.mpr hxa
  have hleft : (g a - g x) / (a - x) ≤ presentationSlope P i := by
    exact hslope
  have hmul := (div_le_iff₀ hden).mp hleft
  have hthreshold : presentationSlope P i * (a - x) ≤ g a := by
    have hmax : g a / presentationSlope P i ≤
        max 0 (g a / presentationSlope P i) := le_max_right _ _
    have hx' : max 0 (g a / presentationSlope P i) ≤ a - x := by linarith
    have hdiv : g a / presentationSlope P i ≤ a - x := hmax.trans hx'
    have := mul_le_mul_of_nonpos_left hdiv hi.le
    have hne : presentationSlope P i ≠ 0 := ne_of_lt hi
    rw [mul_div_cancel₀ _ hne] at this
    exact this
  nlinarith

theorem sum_Ico_consecutive_int
    (f : ℤ → ℝ) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ i ∈ Finset.Ico a b, f i) + ∑ i ∈ Finset.Ico b c, f i =
      ∑ i ∈ Finset.Ico a c, f i := by
  rw [← Finset.sum_union]
  · congr 1
    exact Finset.Ico_union_Ico_eq_Ico hab hbc
  · rw [Finset.disjoint_left]
    intro x hxab hxbc
    have hxlt : x < b := (Finset.mem_Ico.mp hxab).2
    have hble : b ≤ x := (Finset.mem_Ico.mp hxbc).1
    exact (not_lt_of_ge hble) hxlt

theorem sum_adjacent_sub_Ico (s : ℤ → ℝ) {a b : ℤ} (hab : a ≤ b) :
    (∑ i ∈ Finset.Ico a b, (s (i + 1) - s i)) = s b - s a := by
  induction b, hab using Int.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [← sum_Ico_consecutive_int _ hab (show b ≤ b + 1 by omega)]
      have hsingle : Finset.Ico b (b + 1) = {b} := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_singleton]
        omega
      rw [ih, hsingle]
      simp

/-- Bounded monotone slopes have uniformly bounded total variation after any
fixed natural power.  This is the telescoping inequality used in (5a18). -/
theorem sum_abs_pow_slopeJumps_le
    (s : ℤ → ℝ) (hs : Monotone s) {a b : ℤ} (hab : a ≤ b)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ i ∈ Finset.Icc a b, |s i| ≤ K)
    (j : ℕ) :
    (∑ i ∈ Finset.Ico a b, |s (i + 1) ^ j - s i ^ j|) ≤
      2 * K * (j : ℝ) * K ^ (j - 1) := by
  have hterm (i : ℤ) (hi : i ∈ Finset.Ico a b) :
      |s (i + 1) ^ j - s i ^ j| ≤
        (s (i + 1) - s i) * (j : ℝ) * K ^ (j - 1) := by
    have hai : a ≤ i := (Finset.mem_Ico.mp hi).1
    have hib : i < b := (Finset.mem_Ico.mp hi).2
    have hmono : s i ≤ s (i + 1) := hs (by omega)
    have hiBound : |s i| ≤ K := hbound i (Finset.mem_Icc.mpr ⟨hai, hib.le⟩)
    have hnextBound : |s (i + 1)| ≤ K :=
      hbound (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    calc
      |s (i + 1) ^ j - s i ^ j| ≤
          |s (i + 1) - s i| * (j : ℝ) *
            max |s (i + 1)| |s i| ^ (j - 1) :=
        abs_pow_sub_pow_le (s (i + 1)) (s i) j
      _ = (s (i + 1) - s i) * (j : ℝ) *
            max |s (i + 1)| |s i| ^ (j - 1) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
      _ ≤ (s (i + 1) - s i) * (j : ℝ) * K ^ (j - 1) := by
        gcongr
        exact max_le hnextBound hiBound
  calc
    (∑ i ∈ Finset.Ico a b, |s (i + 1) ^ j - s i ^ j|) ≤
        ∑ i ∈ Finset.Ico a b,
          (s (i + 1) - s i) * (j : ℝ) * K ^ (j - 1) :=
      Finset.sum_le_sum (fun i hi ↦ hterm i hi)
    _ = (s b - s a) * (j : ℝ) * K ^ (j - 1) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, sum_adjacent_sub_Ico s hab]
    _ ≤ 2 * K * (j : ℝ) * K ^ (j - 1) := by
      have ha := hbound a (Finset.mem_Icc.mpr ⟨le_rfl, hab⟩)
      have hb := hbound b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)
      have hsab : 0 ≤ s b - s a := sub_nonneg.mpr (hs hab)
      have hj : 0 ≤ (j : ℝ) := by positivity
      have hpow : 0 ≤ K ^ (j - 1) := pow_nonneg hK _
      have hdiff : s b - s a ≤ 2 * K := by
        have hsb : s b ≤ K := (le_abs_self _).trans hb
        have hsa : -K ≤ s a := by linarith [neg_abs_le (s a)]
        linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdiff hj) hpow

/-- If every affine slope is nonpositive, the represented function is
globally antitone. -/
theorem antitone_of_presentationSlope_nonpos
    {q : ℕ} (g : NthTropicalMeromorphicFunction q) (hq : q ≤ 1)
    (hgEntire : IsTropicalEntire g) (P : PolynomialPresentation q g)
    (hs : ∀ i, presentationSlope P i ≤ 0) : Antitone g := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · exact le_rfl
  obtain ⟨z, hyz, hright⟩ := P.exists_right_germ_interval y
  let v := (y + z) / 2
  have hyv : y < v := by dsimp [v]; linarith
  have hvz : v < z := by dsimp [v]; linarith
  have hconv := convexOn_univ_of_order_le_one_entire g hq hgEntire
  have hslope := (convexOn_iff_slope_mono_adjacent.mp hconv).2
    (Set.mem_univ x) (Set.mem_univ v) hxy hyv
  have hrightV := hright v ⟨hyv, hvz⟩
  have hrightY := P.rightPieceAt_eval y
  have hlinear :
      ((P.rightPieceAt y).eval v - (P.rightPieceAt y).eval y) / (v - y) =
        (P.rightPieceAt y).coeff 1 := by
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one
      ((P.rightPieceAt_natDegree_le y).trans hq)]
    simp
    field_simp [ne_of_gt (sub_pos.mpr hyv)]
  have hcoeff : (P.rightPieceAt y).coeff 1 ≤ 0 := by
    simp only [PolynomialPresentation.rightPieceAt]
    split <;> exact hs _
  rw [hrightV, ← hrightY, hlinear] at hslope
  rw [hrightY] at hslope
  have hden : 0 < y - x := sub_pos.mpr hxy
  have hnum := (div_le_iff₀ hden).mp (hslope.trans hcoeff)
  linarith

/-- If every affine slope is nonnegative, the represented function is
globally monotone. -/
theorem monotone_of_presentationSlope_nonneg
    {q : ℕ} (g : NthTropicalMeromorphicFunction q) (hq : q ≤ 1)
    (hgEntire : IsTropicalEntire g) (P : PolynomialPresentation q g)
    (hs : ∀ i, 0 ≤ presentationSlope P i) : Monotone g := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · exact le_rfl
  obtain ⟨z, hzx, hleft⟩ := P.exists_left_germ_interval x
  let u := (z + x) / 2
  have hzu : z < u := by dsimp [u]; linarith
  have hux : u < x := by dsimp [u]; linarith
  have hconv := convexOn_univ_of_order_le_one_entire g hq hgEntire
  have hslope := (convexOn_iff_slope_mono_adjacent.mp hconv).2
    (Set.mem_univ u) (Set.mem_univ y) hux hxy
  have hleftU := hleft u ⟨hzu, hux⟩
  have hleftX := P.leftPieceAt_eval x
  have hlinear :
      ((P.leftPieceAt x).eval x - (P.leftPieceAt x).eval u) / (x - u) =
        (P.leftPieceAt x).coeff 1 := by
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one
      ((P.leftPieceAt_natDegree_le x).trans hq)]
    simp
    field_simp [ne_of_gt (sub_pos.mpr hux)]
  have hcoeff : 0 ≤ (P.leftPieceAt x).coeff 1 := by
    unfold PolynomialPresentation.leftPieceAt
    exact hs _
  rw [hleftU, ← hleftX, hlinear] at hslope
  rw [hleftX] at hslope
  have hden : 0 < y - x := sub_pos.mpr hxy
  have hquot : 0 ≤ (g y - g x) / (y - x) := hcoeff.trans hslope
  have hnum := (le_div_iff₀ hden).mp hquot
  linarith

theorem abs_apply_le_linear_on_nonnegative_of_slopes_nonpos
    {q : ℕ} (g : NthTropicalMeromorphicFunction q) (hq : q ≤ 1)
    (hgEntire : IsTropicalEntire g) (P : PolynomialPresentation q g)
    (hs : ∀ i, presentationSlope P i ≤ 0) {x : ℝ} (hx : 0 ≤ x) :
    |g x| ≤ |g 0| + |presentationSlope P 1| * x := by
  have hanti := antitone_of_presentationSlope_nonpos g hq hgEntire P hs
  have hupper : g x ≤ g 0 := hanti hx
  have hcut1 : 0 < P.cutPoint 1 := by
    rw [← P.cutPoint_zero]
    exact P.cutPoint_strictMono (by omega)
  have hlower : g 0 + presentationSlope P 1 * x ≤ g x := by
    by_cases hxc : x ≤ P.cutPoint 1
    · have hpiece := P.eq_piece 1 ⟨by simpa [P.cutPoint_zero] using hx, hxc⟩
      have hzeroPiece := P.eq_piece 1 ⟨by simp [P.cutPoint_zero], hcut1.le⟩
      norm_num [P.cutPoint_zero] at hzeroPiece
      rw [hpiece, hzeroPiece]
      have hdiff := presentationPiece_eval_sub_eq_slope_mul_sub
        P hq 1 0 x
      nlinarith
    · have hcx : P.cutPoint 1 < x := lt_of_not_ge hxc
      have hconv := convexOn_univ_of_order_le_one_entire g hq hgEntire
      have hslope := (convexOn_iff_slope_mono_adjacent.mp hconv).2
        (Set.mem_univ 0) (Set.mem_univ x) hcut1 hcx
      have hzeroPiece := P.eq_piece 1 ⟨by simp [P.cutPoint_zero], hcut1.le⟩
      have hcutPiece := P.eq_piece 1 ⟨by
        simpa [P.cutPoint_zero] using hcut1.le, le_rfl⟩
      norm_num [P.cutPoint_zero] at hzeroPiece
      have hfirstSlope : (g (P.cutPoint 1) - g 0) / (P.cutPoint 1 - 0) =
          presentationSlope P 1 := by
        rw [hzeroPiece, hcutPiece,
          presentationPiece_eval_sub_eq_slope_mul_sub P hq]
        field_simp [ne_of_gt hcut1]
      rw [hfirstSlope] at hslope
      have hmul := (le_div_iff₀ (sub_pos.mpr hcx)).mp hslope
      have hcutValue : g (P.cutPoint 1) =
          g 0 + presentationSlope P 1 * P.cutPoint 1 := by
        rw [hzeroPiece, hcutPiece]
        have hdiff := presentationPiece_eval_sub_eq_slope_mul_sub
          P hq 1 0 (P.cutPoint 1)
        nlinarith
      rw [hcutValue] at hmul
      nlinarith
  rw [abs_le]
  constructor
  · have hsabs : -|presentationSlope P 1| ≤ presentationSlope P 1 :=
      neg_abs_le _
    have hxmul := mul_le_mul_of_nonneg_right hsabs hx
    have hgabs : -|g 0| ≤ g 0 := neg_abs_le _
    linarith
  · have hgabs : g 0 ≤ |g 0| := le_abs_self _
    have hnonneg : 0 ≤ |presentationSlope P 1| * x :=
      mul_nonneg (abs_nonneg _) hx
    linarith

theorem abs_apply_le_linear_on_nonpositive_of_slopes_nonneg
    {q : ℕ} (g : NthTropicalMeromorphicFunction q) (hq : q ≤ 1)
    (hgEntire : IsTropicalEntire g) (P : PolynomialPresentation q g)
    (hs : ∀ i, 0 ≤ presentationSlope P i) {x : ℝ} (hx : x ≤ 0) :
    |g x| ≤ |g 0| + |presentationSlope P 0| * |x| := by
  have hmono := monotone_of_presentationSlope_nonneg g hq hgEntire P hs
  have hupper : g x ≤ g 0 := hmono hx
  have hcutNeg : P.cutPoint (-1) < 0 := by
    rw [← P.cutPoint_zero]
    exact P.cutPoint_strictMono (by omega)
  have hlower : g 0 + presentationSlope P 0 * x ≤ g x := by
    by_cases hcx : P.cutPoint (-1) ≤ x
    · have hpiece := P.eq_piece 0 ⟨by simpa using hcx, by simpa [P.cutPoint_zero] using hx⟩
      have hzeroPiece := P.eq_piece 0 ⟨hcutNeg.le, by simp [P.cutPoint_zero]⟩
      norm_num [P.cutPoint_zero] at hzeroPiece
      rw [hpiece, hzeroPiece]
      have hdiff := presentationPiece_eval_sub_eq_slope_mul_sub
        P hq 0 0 x
      nlinarith
    · have hxc : x < P.cutPoint (-1) := lt_of_not_ge hcx
      have hconv := convexOn_univ_of_order_le_one_entire g hq hgEntire
      have hslope := (convexOn_iff_slope_mono_adjacent.mp hconv).2
        (Set.mem_univ x) (Set.mem_univ 0) hxc hcutNeg
      have hnegPiece := P.eq_piece 0 ⟨le_rfl, by
        simpa [P.cutPoint_zero] using hcutNeg.le⟩
      have hzeroPiece := P.eq_piece 0 ⟨hcutNeg.le, by simp [P.cutPoint_zero]⟩
      norm_num at hnegPiece
      norm_num [P.cutPoint_zero] at hzeroPiece
      have hlastSlope : (g 0 - g (P.cutPoint (-1))) /
          (0 - P.cutPoint (-1)) = presentationSlope P 0 := by
        apply (div_eq_iff (ne_of_gt (sub_pos.mpr hcutNeg))).2
        rw [hzeroPiece, hnegPiece]
        exact presentationPiece_eval_sub_eq_slope_mul_sub
          P hq 0 (P.cutPoint (-1)) 0
      rw [hlastSlope] at hslope
      have hmul := (div_le_iff₀ (sub_pos.mpr hxc)).mp hslope
      have hcutValue : g (P.cutPoint (-1)) =
          g 0 + presentationSlope P 0 * P.cutPoint (-1) := by
        rw [hzeroPiece, hnegPiece]
        have hdiff := presentationPiece_eval_sub_eq_slope_mul_sub
          P hq 0 0 (P.cutPoint (-1))
        nlinarith
      rw [hcutValue] at hmul
      nlinarith
  rw [abs_le]
  constructor
  · have hsabs : presentationSlope P 0 ≤ |presentationSlope P 0| :=
      le_abs_self _
    have hxneg : 0 ≤ -x := neg_nonneg.mpr hx
    have hxmul := mul_le_mul_of_nonneg_right hsabs hxneg
    have hgabs : -|g 0| ≤ g 0 := neg_abs_le _
    rw [abs_of_nonpos hx]
    nlinarith
  · have hgabs : g 0 ≤ |g 0| := le_abs_self _
    have hnonneg : 0 ≤ |presentationSlope P 0| * |x| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    linarith

theorem sourceIndex_cut_abs_le_radius
    {q : ℕ} {g : ℝ → ℝ} (P : PolynomialPresentation q g)
    {r : ℝ} (hr : 0 ≤ r) {i : ℤ}
    (hi : i ∈ Finset.Ico (presentationIntervalIndex P (-r))
      (presentationIntervalIndex P r)) :
    |P.cutPoint i| ≤ r := by
  let a := presentationIntervalIndex P (-r)
  let b := presentationIntervalIndex P r
  have hneg := presentationIntervalIndex_mem P (-r)
  have hpos := presentationIntervalIndex_mem P r
  change -r ∈ Ioc (P.cutPoint (a - 1)) (P.cutPoint a) at hneg
  change r ∈ Ioc (P.cutPoint (b - 1)) (P.cutPoint b) at hpos
  have hai : a ≤ i := (Finset.mem_Ico.mp hi).1
  have hib : i < b := (Finset.mem_Ico.mp hi).2
  have hlower : -r ≤ P.cutPoint i :=
    hneg.2.trans (P.cutPoint_strictMono.monotone hai)
  have hupper : P.cutPoint i ≤ r := by
    have hii : i ≤ b - 1 := by omega
    exact (P.cutPoint_strictMono.monotone hii).trans hpos.1.le
  exact (abs_le.mpr ⟨hlower, hupper⟩)

theorem sourceIndex_lower_le_zero
    {q : ℕ} {g : ℝ → ℝ} (P : PolynomialPresentation q g)
    {r : ℝ} (hr : 0 < r) : presentationIntervalIndex P (-r) ≤ 0 := by
  let a := presentationIntervalIndex P (-r)
  have hneg := presentationIntervalIndex_mem P (-r)
  change -r ∈ Ioc (P.cutPoint (a - 1)) (P.cutPoint a) at hneg
  by_contra hnot
  have hidx : 0 ≤ a - 1 := by omega
  have hcut : P.cutPoint 0 ≤ P.cutPoint (a - 1) :=
    P.cutPoint_strictMono.monotone hidx
  rw [P.cutPoint_zero] at hcut
  linarith [hneg.1]

theorem one_le_sourceIndex_upper
    {q : ℕ} {g : ℝ → ℝ} (P : PolynomialPresentation q g)
    {r : ℝ} (hr : 0 < r) : 1 ≤ presentationIntervalIndex P r := by
  let b := presentationIntervalIndex P r
  have hpos := presentationIntervalIndex_mem P r
  change r ∈ Ioc (P.cutPoint (b - 1)) (P.cutPoint b) at hpos
  by_contra hnot
  have hidx : b ≤ 0 := by omega
  have hcut : P.cutPoint b ≤ P.cutPoint 0 :=
    P.cutPoint_strictMono.monotone hidx
  rw [P.cutPoint_zero] at hcut
  linarith [hpos.2]

theorem power_poles_eventually_zero_on_positiveCutIndices
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hgEntire : IsTropicalEntire g) (hq : ∀ x, q x = (g x) ^ d)
    (P : PolynomialPresentation ng g) (j : ℕ)
    (hpos : ∃ i, 0 < presentationSlope P i) :
    ∃ I : ℤ, 0 < I ∧ ∀ i, I ≤ i →
      poleMultiplicity q j (P.cutPoint i) = 0 := by
  rcases hpos with ⟨i₀, hi₀⟩
  rcases (eventually_atTop.1
    (eventually_nonneg_atTop_of_positive_presentationSlope
      g hng hgEntire P hi₀)) with ⟨R, hR⟩
  obtain ⟨u, hu⟩ := (tendsto_atTop_atTop.mp P.cutPoint_tendsto_atTop) R
  let I := max (max i₀ u) 1
  refine ⟨I, by dsimp [I]; omega, ?_⟩
  intro i hIi
  have hiI₀ : i₀ ≤ i := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hIi)
  have huI : u ≤ i := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hIi)
  have hcutR : R ≤ P.cutPoint i := hu i huI
  have hg : 0 ≤ g (P.cutPoint i) := hR _ hcutR
  have hs : 0 ≤ presentationSlope P i :=
    hi₀.le.trans ((presentationSlope_monotone_of_entire g hng hgEntire P) hiI₀)
  exact poleMultiplicity_power_at_positiveCut_eq_zero
    q g hng hgEntire hq P j (lt_of_lt_of_le (by dsimp [I]; omega) hIi) hg hs

theorem power_poles_eventually_zero_on_negativeCutIndices
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hgEntire : IsTropicalEntire g) (hq : ∀ x, q x = (g x) ^ d)
    (P : PolynomialPresentation ng g) (j : ℕ)
    (hneg : ∃ i, presentationSlope P i < 0) :
    ∃ I : ℤ, I < 0 ∧ ∀ i, i ≤ I →
      poleMultiplicity q j (P.cutPoint i) = 0 := by
  rcases hneg with ⟨i₀, hi₀⟩
  rcases (eventually_atBot.1
    (eventually_nonneg_atBot_of_negative_presentationSlope
      g hng hgEntire P hi₀)) with ⟨R, hR⟩
  obtain ⟨u, hu⟩ := (tendsto_atBot_atBot.mp P.cutPoint_tendsto_atBot) R
  let I := min (min (i₀ - 1) u) (-1)
  refine ⟨I, by dsimp [I]; omega, ?_⟩
  intro i hiI
  have hii₀ : i + 1 ≤ i₀ := by
    dsimp [I] at hiI
    omega
  have hiu : i ≤ u := by
    dsimp [I] at hiI
    omega
  have hcutR : P.cutPoint i ≤ R := hu i hiu
  have hg : 0 ≤ g (P.cutPoint i) := hR _ hcutR
  have hs : presentationSlope P (i + 1) ≤ 0 :=
    ((presentationSlope_monotone_of_entire g hng hgEntire P) hii₀).trans hi₀.le
  exact poleMultiplicity_power_at_negativeCut_eq_zero
    q g hng hgEntire hq P j (lt_of_le_of_lt hiI (by dsimp [I]; omega)) hg hs

/-- Any fixed finite block of cut contributions is `O(r^d)` for `j≤d`.
This packages the compact pieces in (5a14) and (5a16). -/
theorem fixed_sourceIndexSum_isBigO_radiusPower
    {nq q d j : ℕ} {f : ℝ → ℝ} (h : NthTropicalMeromorphicFunction nq)
    (P : PolynomialPresentation q f) (hj : j ≤ d)
    (A : Finset ℤ) :
    (fun r : ℝ ↦ ∑ i ∈ A,
      poleMultiplicity h j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j) =O[atTop]
        fun r : ℝ ↦ r ^ d := by
  let C : ℝ := ∑ i ∈ A,
    poleMultiplicity h j (P.cutPoint i) * (1 + |P.cutPoint i|) ^ j
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : 0 ≤ r := by linarith
  have hrd : 0 ≤ r ^ d := pow_nonneg hr0 _
  have hsumNonneg : 0 ≤ ∑ i ∈ A,
      poleMultiplicity h j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j := by
    exact Finset.sum_nonneg (fun i _hi ↦ mul_nonneg
      (by simp [poleMultiplicity]) (pow_nonneg (abs_nonneg _) _))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsumNonneg,
    abs_of_nonneg hrd]
  calc
    (∑ i ∈ A, poleMultiplicity h j (P.cutPoint i) *
        abs (r - |P.cutPoint i|) ^ j) ≤
        ∑ i ∈ A, poleMultiplicity h j (P.cutPoint i) *
          ((1 + |P.cutPoint i|) ^ j * r ^ d) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (by simp [poleMultiplicity])
      have habs : abs (r - |P.cutPoint i|) ≤
          (1 + |P.cutPoint i|) * r := by
        calc
          abs (r - |P.cutPoint i|) ≤ r + |P.cutPoint i| := by
            rw [abs_sub_comm]
            simpa [abs_of_nonneg hr0, add_comm] using
              (abs_sub_le |P.cutPoint i| 0 r)
          _ ≤ (1 + |P.cutPoint i|) * r := by
            nlinarith [abs_nonneg (P.cutPoint i)]
      calc
        abs (r - |P.cutPoint i|) ^ j ≤
            ((1 + |P.cutPoint i|) * r) ^ j :=
          pow_le_pow_left₀ (abs_nonneg _) habs j
        _ = (1 + |P.cutPoint i|) ^ j * r ^ j := by rw [mul_pow]
        _ ≤ (1 + |P.cutPoint i|) ^ j * r ^ d := by
          gcongr
    _ = C * r ^ d := by
      dsimp [C]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem positive_sourceIndexSum_isBigO_of_slopes_nonpos
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hgEntire : IsTropicalEntire g) (hq : ∀ x, q x = (g x) ^ d)
    (P : PolynomialPresentation ng g) {j : ℕ} (hj : j ≤ d)
    (hs : ∀ i, presentationSlope P i ≤ 0) :
    (fun r : ℝ ↦
      ∑ i ∈ Finset.Ico 1 (presentationIntervalIndex P r),
        poleMultiplicity q j (P.cutPoint i) *
        abs (r - |P.cutPoint i|) ^ j) =O[atTop] fun r : ℝ ↦ r ^ d := by
  let K : ℝ := |presentationSlope P 1|
  let C : ℝ := |g 0| + K
  let B : ℝ := (d.choose j : ℝ) * C ^ (d - j) *
    (2 * K * (j : ℝ) * K ^ (j - 1))
  have hK : 0 ≤ K := abs_nonneg _
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) hK
  rw [Asymptotics.isBigO_iff]
  refine ⟨B, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  let b := presentationIntervalIndex P r
  have hb : 1 ≤ b := one_le_sourceIndex_upper P (by linarith)
  have hposCut : 0 < P.cutPoint 1 := by
    rw [← P.cutPoint_zero]
    exact P.cutPoint_strictMono (by omega)
  have hboundSlope : ∀ i ∈ Finset.Icc (1 : ℤ) b,
      |presentationSlope P i| ≤ K := by
    intro i hi
    have hsiLower := (presentationSlope_monotone_of_entire g hng hgEntire P)
      (Finset.mem_Icc.mp hi).1
    have hsiUpper := hs i
    dsimp [K]
    rw [abs_of_nonpos hsiUpper, abs_of_nonpos (hs 1)]
    linarith
  have hjumps := sum_abs_pow_slopeJumps_le (presentationSlope P)
    (presentationSlope_monotone_of_entire g hng hgEntire P) hb K hK hboundSlope j
  have hterm (i : ℤ) (hi : i ∈ Finset.Ico (1 : ℤ) b) :
      poleMultiplicity q j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j ≤
        ((d.choose j : ℝ) * C ^ (d - j) * r ^ d) *
          |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j| := by
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have hib : i < b := (Finset.mem_Ico.mp hi).2
    have hcutPos : 0 ≤ P.cutPoint i :=
      by
        rw [← P.cutPoint_zero]
        exact P.cutPoint_strictMono.monotone (by omega)
    have hposMem := presentationIntervalIndex_mem P r
    have hcutLt : P.cutPoint i < r := by
      have hii : i ≤ b - 1 := by omega
      exact (P.cutPoint_strictMono.monotone hii).trans_lt hposMem.1
    have hcutAbs : |P.cutPoint i| = P.cutPoint i := abs_of_nonneg hcutPos
    have hradial : abs (r - |P.cutPoint i|) ≤ r := by
      rw [hcutAbs, abs_of_nonneg (sub_nonneg.mpr hcutLt.le)]
      linarith
    have hgBound0 := abs_apply_le_linear_on_nonnegative_of_slopes_nonpos
      g hng hgEntire P hs hcutPos
    have hgBound : |g (P.cutPoint i)| ≤ C * r := by
      dsimp [C, K]
      have hcutLe : P.cutPoint i ≤ r := hcutLt.le
      have hmul := mul_le_mul_of_nonneg_left hcutLe (abs_nonneg (presentationSlope P 1))
      have hg0scale : |g 0| ≤ |g 0| * r := by nlinarith [abs_nonneg (g 0)]
      nlinarith
    have hpole := poleMultiplicity_power_at_sourceCutPoint_le
      q g hng hq P j i (by omega)
    have hpowG : |g (P.cutPoint i)| ^ (d - j) ≤ (C * r) ^ (d - j) :=
      pow_le_pow_left₀ (abs_nonneg _) hgBound _
    have hpowR : abs (r - |P.cutPoint i|) ^ j ≤ r ^ j :=
      pow_le_pow_left₀ (abs_nonneg _) hradial _
    calc
      poleMultiplicity q j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j ≤
          ((d.choose j : ℝ) * |g (P.cutPoint i)| ^ (d - j) *
            |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j|) *
              abs (r - |P.cutPoint i|) ^ j :=
        mul_le_mul_of_nonneg_right hpole (pow_nonneg (abs_nonneg _) _)
      _ ≤ ((d.choose j : ℝ) * (C * r) ^ (d - j) *
            |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j|) *
              r ^ j := by gcongr
      _ = ((d.choose j : ℝ) * C ^ (d - j) * r ^ d) *
            |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j| := by
        rw [mul_pow]
        have hrpow : r ^ (d - j) * r ^ j = r ^ d := by
          rw [← pow_add, Nat.sub_add_cancel hj]
        calc
          (d.choose j : ℝ) * (C ^ (d - j) * r ^ (d - j)) *
                |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j| *
              r ^ j =
              (d.choose j : ℝ) * C ^ (d - j) *
                (r ^ (d - j) * r ^ j) *
                  |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j| := by
                ring
          _ = _ := by rw [hrpow]
  have hsumNonneg : 0 ≤ ∑ i ∈ Finset.Ico (1 : ℤ) b,
      poleMultiplicity q j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j := by
    exact Finset.sum_nonneg (fun i _hi ↦ mul_nonneg
      (by simp [poleMultiplicity]) (pow_nonneg (abs_nonneg _) _))
  have hrd : 0 ≤ r ^ d := pow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsumNonneg,
    abs_of_nonneg hrd]
  calc
    (∑ i ∈ Finset.Ico (1 : ℤ) b,
        poleMultiplicity q j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j) ≤
        ∑ i ∈ Finset.Ico (1 : ℤ) b,
          ((d.choose j : ℝ) * C ^ (d - j) * r ^ d) *
            |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j| :=
      Finset.sum_le_sum (fun i hi ↦ hterm i hi)
    _ = ((d.choose j : ℝ) * C ^ (d - j) * r ^ d) *
        (∑ i ∈ Finset.Ico (1 : ℤ) b,
          |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j|) := by
      rw [Finset.mul_sum]
    _ ≤ ((d.choose j : ℝ) * C ^ (d - j) * r ^ d) *
        (2 * K * (j : ℝ) * K ^ (j - 1)) := by
      gcongr
    _ = B * r ^ d := by dsimp [B]; ring

theorem negative_sourceIndexSum_isBigO_of_slopes_nonneg
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hgEntire : IsTropicalEntire g) (hq : ∀ x, q x = (g x) ^ d)
    (P : PolynomialPresentation ng g) {j : ℕ} (hj : j ≤ d)
    (hs : ∀ i, 0 ≤ presentationSlope P i) :
    (fun r : ℝ ↦
      ∑ i ∈ Finset.Ico (presentationIntervalIndex P (-r)) 0,
        poleMultiplicity q j (P.cutPoint i) *
        abs (r - |P.cutPoint i|) ^ j) =O[atTop] fun r : ℝ ↦ r ^ d := by
  let K : ℝ := |presentationSlope P 0|
  let C : ℝ := |g 0| + K
  let B : ℝ := (d.choose j : ℝ) * C ^ (d - j) *
    (2 * K * (j : ℝ) * K ^ (j - 1))
  have hK : 0 ≤ K := abs_nonneg _
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) hK
  rw [Asymptotics.isBigO_iff]
  refine ⟨B, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  let a := presentationIntervalIndex P (-r)
  have ha : a ≤ 0 := sourceIndex_lower_le_zero P (by linarith)
  have hboundSlope : ∀ i ∈ Finset.Icc a (0 : ℤ),
      |presentationSlope P i| ≤ K := by
    intro i hi
    have hsiUpper := (presentationSlope_monotone_of_entire g hng hgEntire P)
      (Finset.mem_Icc.mp hi).2
    have hsiLower := hs i
    dsimp [K]
    rw [abs_of_nonneg hsiLower, abs_of_nonneg (hs 0)]
    exact hsiUpper
  have hjumps := sum_abs_pow_slopeJumps_le (presentationSlope P)
    (presentationSlope_monotone_of_entire g hng hgEntire P) ha K hK hboundSlope j
  have hterm (i : ℤ) (hi : i ∈ Finset.Ico a (0 : ℤ)) :
      poleMultiplicity q j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j ≤
        ((d.choose j : ℝ) * C ^ (d - j) * r ^ d) *
          |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j| := by
    have hia : a ≤ i := (Finset.mem_Ico.mp hi).1
    have hi0 : i < 0 := (Finset.mem_Ico.mp hi).2
    have hcutNeg : P.cutPoint i ≤ 0 := by
      rw [← P.cutPoint_zero]
      exact (P.cutPoint_strictMono hi0).le
    have hnegMem := presentationIntervalIndex_mem P (-r)
    have hcutLower : -r ≤ P.cutPoint i :=
      hnegMem.2.trans (P.cutPoint_strictMono.monotone hia)
    have hcutAbs : |P.cutPoint i| = -P.cutPoint i := abs_of_nonpos hcutNeg
    have hradial : abs (r - |P.cutPoint i|) ≤ r := by
      rw [hcutAbs]
      have hnonneg : 0 ≤ r - -P.cutPoint i := by linarith
      rw [abs_of_nonneg hnonneg]
      linarith
    have hgBound0 := abs_apply_le_linear_on_nonpositive_of_slopes_nonneg
      g hng hgEntire P hs hcutNeg
    have hgBound : |g (P.cutPoint i)| ≤ C * r := by
      dsimp [C, K]
      have hcutLe : |P.cutPoint i| ≤ r := by
        rw [hcutAbs]
        linarith
      have hmul := mul_le_mul_of_nonneg_left hcutLe (abs_nonneg (presentationSlope P 0))
      have hg0scale : |g 0| ≤ |g 0| * r := by nlinarith [abs_nonneg (g 0)]
      nlinarith
    have hpole := poleMultiplicity_power_at_sourceCutPoint_le
      q g hng hq P j i (by omega)
    have hpowG : |g (P.cutPoint i)| ^ (d - j) ≤ (C * r) ^ (d - j) :=
      pow_le_pow_left₀ (abs_nonneg _) hgBound _
    have hpowR : abs (r - |P.cutPoint i|) ^ j ≤ r ^ j :=
      pow_le_pow_left₀ (abs_nonneg _) hradial _
    calc
      poleMultiplicity q j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j ≤
          ((d.choose j : ℝ) * |g (P.cutPoint i)| ^ (d - j) *
            |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j|) *
              abs (r - |P.cutPoint i|) ^ j :=
        mul_le_mul_of_nonneg_right hpole (pow_nonneg (abs_nonneg _) _)
      _ ≤ ((d.choose j : ℝ) * (C * r) ^ (d - j) *
            |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j|) *
              r ^ j := by gcongr
      _ = ((d.choose j : ℝ) * C ^ (d - j) * r ^ d) *
            |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j| := by
        rw [mul_pow]
        have hrpow : r ^ (d - j) * r ^ j = r ^ d := by
          rw [← pow_add, Nat.sub_add_cancel hj]
        calc
          (d.choose j : ℝ) * (C ^ (d - j) * r ^ (d - j)) *
                |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j| *
              r ^ j =
              (d.choose j : ℝ) * C ^ (d - j) *
                (r ^ (d - j) * r ^ j) *
                  |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j| := by
                ring
          _ = _ := by rw [hrpow]
  have hsumNonneg : 0 ≤ ∑ i ∈ Finset.Ico a (0 : ℤ),
      poleMultiplicity q j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j := by
    exact Finset.sum_nonneg (fun i _hi ↦ mul_nonneg
      (by simp [poleMultiplicity]) (pow_nonneg (abs_nonneg _) _))
  have hrd : 0 ≤ r ^ d := pow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsumNonneg,
    abs_of_nonneg hrd]
  calc
    (∑ i ∈ Finset.Ico a (0 : ℤ),
        poleMultiplicity q j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j) ≤
        ∑ i ∈ Finset.Ico a (0 : ℤ),
          ((d.choose j : ℝ) * C ^ (d - j) * r ^ d) *
            |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j| :=
      Finset.sum_le_sum (fun i hi ↦ hterm i hi)
    _ = ((d.choose j : ℝ) * C ^ (d - j) * r ^ d) *
        (∑ i ∈ Finset.Ico a (0 : ℤ),
          |presentationSlope P (i + 1) ^ j - presentationSlope P i ^ j|) := by
      rw [Finset.mul_sum]
    _ ≤ ((d.choose j : ℝ) * C ^ (d - j) * r ^ d) *
        (2 * K * (j : ℝ) * K ^ (j - 1)) := by
      gcongr
    _ = B * r ^ d := by dsimp [B]; ring

theorem positive_sourceIndexSum_isBigO_of_eventually_zero
    {nq q d j : ℕ} {f : ℝ → ℝ} (h : NthTropicalMeromorphicFunction nq)
    (P : PolynomialPresentation q f) (hj : j ≤ d) {I : ℤ} (hI : 1 ≤ I)
    (hzero : ∀ i, I ≤ i → poleMultiplicity h j (P.cutPoint i) = 0) :
    (fun r : ℝ ↦ ∑ i ∈ Finset.Ico 1 (presentationIntervalIndex P r),
      poleMultiplicity h j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j) =O[atTop]
        fun r : ℝ ↦ r ^ d := by
  let fixed : ℝ → ℝ := fun r ↦ ∑ i ∈ Finset.Ico (1 : ℤ) I,
    poleMultiplicity h j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j
  have hfixed : fixed =O[atTop] fun r : ℝ ↦ r ^ d :=
    fixed_sourceIndexSum_isBigO_radiusPower h P hj (Finset.Ico 1 I)
  apply hfixed.congr'
  · filter_upwards [eventually_gt_atTop (P.cutPoint I)] with r hr
    let b := presentationIntervalIndex P r
    have hmem := presentationIntervalIndex_mem P r
    have hIb : I < b := by
      by_contra hnot
      have hbI : b ≤ I := le_of_not_gt hnot
      have hcut := P.cutPoint_strictMono.monotone hbI
      linarith [hmem.2]
    change (∑ i ∈ Finset.Ico (1 : ℤ) I,
      poleMultiplicity h j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j) = _
    rw [← sum_Ico_consecutive_int _ hI hIb.le]
    have htail : (∑ i ∈ Finset.Ico I b,
        poleMultiplicity h j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hzero i (Finset.mem_Ico.mp hi).1, zero_mul]
    rw [htail, add_zero]
  · exact EventuallyEq.rfl

theorem negative_sourceIndexSum_isBigO_of_eventually_zero
    {nq q d j : ℕ} {f : ℝ → ℝ} (h : NthTropicalMeromorphicFunction nq)
    (P : PolynomialPresentation q f) (hj : j ≤ d) {I : ℤ} (hI : I < 0)
    (hzero : ∀ i, i ≤ I → poleMultiplicity h j (P.cutPoint i) = 0) :
    (fun r : ℝ ↦ ∑ i ∈ Finset.Ico (presentationIntervalIndex P (-r)) 0,
      poleMultiplicity h j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j) =O[atTop]
        fun r : ℝ ↦ r ^ d := by
  let fixed : ℝ → ℝ := fun r ↦ ∑ i ∈ Finset.Ico (I + 1) (0 : ℤ),
    poleMultiplicity h j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j
  have hfixed : fixed =O[atTop] fun r : ℝ ↦ r ^ d :=
    fixed_sourceIndexSum_isBigO_radiusPower h P hj (Finset.Ico (I + 1) 0)
  apply hfixed.congr'
  · filter_upwards [eventually_gt_atTop (-P.cutPoint I)] with r hr
    let a := presentationIntervalIndex P (-r)
    have hmem := presentationIntervalIndex_mem P (-r)
    have haI : a ≤ I := by
      by_contra hnot
      have hIa : I < a := lt_of_not_ge hnot
      have hcut : P.cutPoint I ≤ P.cutPoint (a - 1) :=
        P.cutPoint_strictMono.monotone (by omega)
      linarith [hmem.1]
    have haNext : a ≤ I + 1 := by omega
    have hnext0 : I + 1 ≤ 0 := by omega
    change (∑ i ∈ Finset.Ico (I + 1) (0 : ℤ),
      poleMultiplicity h j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j) = _
    rw [← sum_Ico_consecutive_int _ haNext hnext0]
    have htail : (∑ i ∈ Finset.Ico a (I + 1),
        poleMultiplicity h j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hzero i (by have := (Finset.mem_Ico.mp hi).2; omega), zero_mul]
    rw [htail, zero_add]
  · exact EventuallyEq.rfl

/-- The full source-index majorant for one `j` is `O(r^d)`.  The proof is the
complete two-ray case split behind (5a13)--(5a18): on each ray either a
strictly outward slope occurs, after which all power poles vanish, or all
slopes have the opposite weak sign and their powered jumps telescope. -/
theorem sourceIndexSum_power_isBigO_radiusPower
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hgEntire : IsTropicalEntire g) (hq : ∀ x, q x = (g x) ^ d)
    (P : PolynomialPresentation ng g) {j : ℕ} (hj : j ≤ d) :
    (fun r : ℝ ↦
      ∑ i ∈ Finset.Ico (presentationIntervalIndex P (-r))
          (presentationIntervalIndex P r),
        poleMultiplicity q j (P.cutPoint i) *
          abs (r - |P.cutPoint i|) ^ j) =O[atTop] fun r : ℝ ↦ r ^ d := by
  let negative : ℝ → ℝ := fun r ↦
    ∑ i ∈ Finset.Ico (presentationIntervalIndex P (-r)) 0,
      poleMultiplicity q j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j
  let zero : ℝ → ℝ := fun r ↦
    ∑ i ∈ Finset.Ico (0 : ℤ) 1,
      poleMultiplicity q j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j
  let positive : ℝ → ℝ := fun r ↦
    ∑ i ∈ Finset.Ico 1 (presentationIntervalIndex P r),
      poleMultiplicity q j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j
  have hpositive : positive =O[atTop] fun r : ℝ ↦ r ^ d := by
    by_cases hpos : ∃ i, 0 < presentationSlope P i
    · rcases power_poles_eventually_zero_on_positiveCutIndices
        q g hng hgEntire hq P j hpos with ⟨I, hI, hzero⟩
      exact positive_sourceIndexSum_isBigO_of_eventually_zero q P hj
        (by omega) hzero
    · have hs : ∀ i, presentationSlope P i ≤ 0 := by
        intro i
        exact le_of_not_gt (fun hi ↦ hpos ⟨i, hi⟩)
      exact positive_sourceIndexSum_isBigO_of_slopes_nonpos
        q g hng hgEntire hq P hj hs
  have hnegative : negative =O[atTop] fun r : ℝ ↦ r ^ d := by
    by_cases hneg : ∃ i, presentationSlope P i < 0
    · rcases power_poles_eventually_zero_on_negativeCutIndices
        q g hng hgEntire hq P j hneg with ⟨I, hI, hzero⟩
      exact negative_sourceIndexSum_isBigO_of_eventually_zero q P hj hI hzero
    · have hs : ∀ i, 0 ≤ presentationSlope P i := by
        intro i
        exact le_of_not_gt (fun hi ↦ hneg ⟨i, hi⟩)
      exact negative_sourceIndexSum_isBigO_of_slopes_nonneg
        q g hng hgEntire hq P hj hs
  have hzero : zero =O[atTop] fun r : ℝ ↦ r ^ d :=
    fixed_sourceIndexSum_isBigO_radiusPower q P hj (Finset.Ico 0 1)
  have hparts := (hnegative.add hzero).add hpositive
  apply hparts.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    let a := presentationIntervalIndex P (-r)
    let b := presentationIntervalIndex P r
    have ha : a ≤ 0 := sourceIndex_lower_le_zero P hr
    have hb : 1 ≤ b := one_le_sourceIndex_upper P hr
    dsimp [negative, zero, positive]
    rw [← sum_Ico_consecutive_int _ ha (show (0 : ℤ) ≤ b by omega),
      ← sum_Ico_consecutive_int _ (show (0 : ℤ) ≤ 1 by omega) hb]
    ring
  · exact EventuallyEq.rfl

/-- One integrated pole count of an ordinary power is `O(r^d)`. -/
theorem integratedCounting_power_isBigO_radiusPower
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hgEntire : IsTropicalEntire g) (hq : ∀ x, q x = (g x) ^ d)
    (P : PolynomialPresentation ng g) {j : ℕ} (hj : j ≤ d) :
    (fun r ↦ integratedCounting j r q) =O[atTop] fun r : ℝ ↦ r ^ d := by
  let majorant : ℝ → ℝ := fun r ↦
    (1 / 2) * ∑ i ∈ Finset.Ico (presentationIntervalIndex P (-r))
        (presentationIntervalIndex P r),
      poleMultiplicity q j (P.cutPoint i) * abs (r - |P.cutPoint i|) ^ j
  have hmajorant : majorant =O[atTop] fun r : ℝ ↦ r ^ d :=
    (sourceIndexSum_power_isBigO_radiusPower
      q g hng hgEntire hq P hj).const_mul_left (1 / 2 : ℝ)
  rw [Asymptotics.isBigO_iff] at hmajorant ⊢
  rcases hmajorant with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop (0 : ℝ)] with r hCr hr
  have hle := integratedCounting_power_le_sourceIndexSum
    q g hng hq P j hr
  have hnonneg := integratedCounting_nonneg j r q
  have hmajorantNonneg : 0 ≤ majorant r := by
    dsimp [majorant]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _hi ↦ mul_nonneg
      (by simp [poleMultiplicity]) (pow_nonneg (abs_nonneg _) _)))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hle.trans (by
    change majorant r ≤ C * ‖r ^ d‖
    rw [← abs_of_nonneg hmajorantNonneg, ← Real.norm_eq_abs]
    exact hCr)

/-- Summing `j=1,…,d` gives the complete single-coordinate estimate (5a19)
on the polynomial scale `r^d`. -/
theorem ambientPoleCounting_power_isBigO_radiusPower
    {nq ng d : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (hng : ng ≤ 1)
    (hgEntire : IsTropicalEntire g) (hq : ∀ x, q x = (g x) ^ d) :
    (fun r ↦ ambientPoleCounting d r q) =O[atTop] fun r : ℝ ↦ r ^ d := by
  unfold ambientPoleCounting
  exact Asymptotics.IsBigO.sum (fun j hj ↦
    integratedCounting_power_isBigO_radiusPower
      q g hng hgEntire hq g.presentation (Finset.mem_Icc.mp hj).2)

/-- Equation (5a19) for one coordinate, on the theorem's natural scale. -/
theorem coordinatePower_poleCounting_isLittleO_characteristicPower
    {m n : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hGrowth : OrdinaryFermatGrowthLimsupCondition F) (hn : 1 ≤ n)
    (i : Fin (m + 1)) :
    (fun r ↦ ambientPoleCounting n r
      (OrdinaryHomogeneousFermatPolynomial.coordinatePowerRealization
        (n := n) F i).function) =o[atTop]
      fun r ↦ curveCharacteristicPower (n := n) F r := by
  let q := (OrdinaryHomogeneousFermatPolynomial.coordinatePowerRealization
    (n := n) F i).function
  have hq (x : ℝ) : q x = (F.coordinate i x) ^ n := by
    exact (OrdinaryHomogeneousFermatPolynomial.coordinatePowerRealization
      (n := n) F i).eq_fun x
  have hbig : (fun r ↦ ambientPoleCounting n r q) =O[atTop]
      fun r : ℝ ↦ r ^ n :=
    ambientPoleCounting_power_isBigO_radiusPower q (F.coordinate i)
      (F.order_le i) (F.coordinate_isTropicalEntire i) hq
  have hr := radius_isLittleO_characteristic_of_growthLimsupCondition F hGrowth
  have hrn := hr.pow (show 0 < n from hn)
  exact hbig.trans_isLittleO (by
    simpa [CurveCharacteristicDominatesRadius, curveCharacteristicPower] using hrn)

/-- Intrinsic multiplicity scales linearly under a pointwise ordinary scalar
multiple, independently of the exact orders and chosen presentations. -/
theorem multiplicity_eq_smul_of_eq_smul
    {nq ng : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (c : ℝ)
    (hq : ∀ x, q x = c * g x) (j : ℕ) (x : ℝ) :
    multiplicity q j x = c * multiplicity g j x := by
  simp only [multiplicity, multiplicityUsingPresentation]
  rw [leftPieceAt_eq_C_mul_of_eq_smul q g c hq x,
    rightPieceAt_eq_C_mul_of_eq_smul q g c hq x,
    normalizedPolynomialJet_C_mul, normalizedPolynomialJet_C_mul]
  ring

/-- A positive ordinary scalar pulls exactly out of every integrated pole
count. -/
theorem integratedCounting_smul
    {nq ng : ℕ} (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (c : ℝ) (hc : 0 < c)
    (hq : ∀ x, q x = c * g x) (j : ℕ) (r : ℝ) :
    integratedCounting j r q = c * integratedCounting j r g := by
  classical
  have hsingular : jthSingularPointsIn q j (-r) r =
      jthSingularPointsIn g j (-r) r := by
    ext x
    simp only [mem_jthSingularPointsIn_iff]
    apply and_congr_right
    intro _hx
    rw [multiplicity_eq_smul_of_eq_smul q g c hq]
    constructor
    · intro hcm hg0
      exact hcm (by rw [hg0, mul_zero])
    · intro hg0 hcm
      rcases mul_eq_zero.mp hcm with hc0 | hm0
      · exact (ne_of_gt hc) hc0
      · exact hg0 hm0
  have hpole (x : ℝ) : poleMultiplicity q j x = c * poleMultiplicity g j x := by
    rw [poleMultiplicity, poleMultiplicity,
      multiplicity_eq_smul_of_eq_smul q g c hq]
    rcases le_total 0 (multiplicity g j x) with hm | hm
    · rw [max_eq_right (neg_nonpos.mpr (mul_nonneg hc.le hm)),
        max_eq_right (neg_nonpos.mpr hm)]
      ring
    · rw [max_eq_left (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hc.le hm)),
        max_eq_left (neg_nonneg.mpr hm)]
      ring
  rw [integratedCounting_eq_sum_poleMultiplicity,
    integratedCounting_eq_sum_poleMultiplicity, hsingular]
  simp_rw [hpole]
  calc
    (1 / 2) * ∑ x ∈ jthSingularPointsIn g j (-r) r,
        c * poleMultiplicity g j x * (r - |x|) ^ j =
        (1 / 2) *
          (c * ∑ x ∈ jthSingularPointsIn g j (-r) r,
            poleMultiplicity g j x * (r - |x|) ^ j) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _hx
          ring
    _ = c * ((1 / 2) * ∑ x ∈ jthSingularPointsIn g j (-r) r,
          poleMultiplicity g j x * (r - |x|) ^ j) := by ring

theorem ambientPoleCounting_add_le
    {nq ng nh : ℕ} (upTo : ℕ) (r : ℝ)
    (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng)
    (h : NthTropicalMeromorphicFunction nh)
    (hq : ∀ x, q x = g x + h x) :
    ambientPoleCounting upTo r q ≤
      ambientPoleCounting upTo r g + ambientPoleCounting upTo r h := by
  unfold ambientPoleCounting
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _hj
  exact integratedCounting_add_le q g h hq j r

theorem ambientPoleCounting_smul
    {nq ng : ℕ} (upTo : ℕ) (r : ℝ)
    (q : NthTropicalMeromorphicFunction nq)
    (g : NthTropicalMeromorphicFunction ng) (c : ℝ) (hc : 0 < c)
    (hq : ∀ x, q x = c * g x) :
    ambientPoleCounting upTo r q = c * ambientPoleCounting upTo r g := by
  unfold ambientPoleCounting
  simp_rw [integratedCounting_smul q g c hc hq]
  exact (Finset.mul_sum _ _ _).symm

theorem ambientPoleCounting_eq_zero_of_pointwise_zero
    {nq : ℕ} (upTo : ℕ) (r : ℝ)
    (q : NthTropicalMeromorphicFunction nq) (hq : ∀ x, q x = 0) :
    ambientPoleCounting upTo r q = 0 := by
  have hmult (j : ℕ) (x : ℝ) : multiplicity q j x = 0 := by
    have hscale := multiplicity_eq_smul_of_eq_smul q q 0
      (fun y ↦ by simp [hq y]) j x
    simpa using hscale
  unfold ambientPoleCounting
  apply Finset.sum_eq_zero
  intro j _hj
  unfold integratedCounting
  have hempty : jthPolePoints q j r = ∅ := by
    ext x
    simp [IsJthPole, hmult]
  simp [hempty]

/-- The pole count of the canonical realization of a finite ordinary sum is
bounded by the sum of the pole counts of its terms. -/
theorem ambientPoleCounting_finsetSumRealization_le
    {ι : Type*} [DecidableEq ι] {n : ℕ}
    (s : Finset ι) (f : ι → ℝ → ℝ)
    (R : ∀ i, NthTropicalMeromorphicRealization n (f i))
    (upTo : ℕ) (r : ℝ) :
    ambientPoleCounting upTo r (finsetSumRealization s f R).function ≤
      ∑ i ∈ s, ambientPoleCounting upTo r (R i).function := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have hz := ambientPoleCounting_eq_zero_of_pointwise_zero upTo r
        (finsetSumRealization ∅ f R).function
        (fun x ↦ by rw [(finsetSumRealization ∅ f R).eq_fun]; simp)
      rw [hz]
  | @insert a s ha ih =>
      let Q := finsetSumRealization (insert a s) f R
      let S := finsetSumRealization s f R
      have hQ (x : ℝ) : Q.function x = (R a).function x + S.function x := by
        rw [Q.eq_fun, (R a).eq_fun, S.eq_fun]
        simp [Finset.sum_insert, ha]
      have hih : ambientPoleCounting upTo r S.function ≤
          ∑ i ∈ s, ambientPoleCounting upTo r (R i).function := by
        simpa only [S] using ih
      calc
        ambientPoleCounting upTo r Q.function ≤
            ambientPoleCounting upTo r (R a).function +
              ambientPoleCounting upTo r S.function :=
          ambientPoleCounting_add_le upTo r Q.function (R a).function S.function hQ
        _ ≤ ambientPoleCounting upTo r (R a).function +
            ∑ i ∈ s, ambientPoleCounting upTo r (R i).function := by
          apply add_le_add
          · exact le_rfl
          · exact hih
        _ = ∑ i ∈ insert a s,
            ambientPoleCounting upTo r (R i).function := by
          rw [Finset.sum_insert ha]

/-- Reduction of the ordinary Fermat composition's pole count to the pole
counts of the unscaled coordinate powers.  This formally proves both
“elementary” counting rules invoked immediately after (5a19). -/
theorem ordinaryFermatComposition_poleCounting_le_coordinatePowers
    {m n : ℕ} (P : OrdinaryHomogeneousFermatPolynomial m n)
    (hP : P.HasPositiveCoefficients)
    (F : TropicalHolomorphicCurveRepresentation 1 m) (r : ℝ) :
    ambientPoleCounting n r (P.curveComposition F).function ≤
      ∑ i, P.coefficient i *
        ambientPoleCounting n r
          (OrdinaryHomogeneousFermatPolynomial.coordinatePowerRealization
            (n := n) F i).function := by
  let term := fun i : Fin (m + 1) ↦ P.coordinateTermRealization F i
  have hsum := ambientPoleCounting_finsetSumRealization_le Finset.univ
    (fun i x ↦ P.coefficient i * (F.eval i x) ^ n) term n r
  have hterm (i : Fin (m + 1)) :
      ambientPoleCounting n r (term i).function =
        P.coefficient i * ambientPoleCounting n r
          (OrdinaryHomogeneousFermatPolynomial.coordinatePowerRealization
            (n := n) F i).function := by
    apply ambientPoleCounting_smul n r (term i).function
      (OrdinaryHomogeneousFermatPolynomial.coordinatePowerRealization
        (n := n) F i).function
      (P.coefficient i) (hP i)
    intro x
    rw [(term i).eq_fun,
      (OrdinaryHomogeneousFermatPolynomial.coordinatePowerRealization
        (n := n) F i).eq_fun]
  change ambientPoleCounting n r (P.curveComposition F).function ≤
    ∑ i ∈ Finset.univ, ambientPoleCounting n r (term i).function at hsum
  calc
    ambientPoleCounting n r (P.curveComposition F).function ≤
        ∑ i ∈ Finset.univ, ambientPoleCounting n r (term i).function := hsum
    _ = ∑ i, P.coefficient i *
        ambientPoleCounting n r
          (OrdinaryHomogeneousFermatPolynomial.coordinatePowerRealization
            (n := n) F i).function := by
      simp_rw [hterm]

/-- The pole-count part of Theorem 5.8, obtained by summing (5a19) over the
positive Fermat coefficients and using the intrinsic addition/scaling laws. -/
theorem ordinaryFermatComposition_poleCounting_isLittleO
    {m n : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m)
    (P : OrdinaryHomogeneousFermatPolynomial m n)
    (hP : P.HasPositiveCoefficients)
    (hGrowth : OrdinaryFermatGrowthLimsupCondition F) (hn : 1 ≤ n) :
    (fun r ↦ ambientPoleCounting n r (P.curveComposition F).function) =o[atTop]
      fun r ↦ curveCharacteristicPower (n := n) F r := by
  let rhs : ℝ → ℝ := fun r ↦ ∑ i, P.coefficient i *
    ambientPoleCounting n r
      (OrdinaryHomogeneousFermatPolynomial.coordinatePowerRealization
        (n := n) F i).function
  have hrhs : rhs =o[atTop]
      fun r ↦ curveCharacteristicPower (n := n) F r := by
    exact Asymptotics.IsLittleO.sum (fun i _hi ↦
      (coordinatePower_poleCounting_isLittleO_characteristicPower
        F hGrowth hn i).const_mul_left (P.coefficient i))
  rw [Asymptotics.isLittleO_iff] at hrhs ⊢
  intro c hc
  filter_upwards [hrhs hc] with r hr
  have hle := ordinaryFermatComposition_poleCounting_le_coordinatePowers
    P hP F r
  have hleft : 0 ≤ ambientPoleCounting n r (P.curveComposition F).function := by
    unfold ambientPoleCounting
    exact Finset.sum_nonneg (fun j _hj ↦ integratedCounting_nonneg j r _)
  have hright : 0 ≤ rhs r := by
    dsimp [rhs]
    exact Finset.sum_nonneg (fun i _hi ↦ mul_nonneg (hP i).le (by
      unfold ambientPoleCounting
      exact Finset.sum_nonneg (fun j _hj ↦ integratedCounting_nonneg j r _)))
  rw [Real.norm_eq_abs, abs_of_nonneg hleft]
  exact hle.trans (by
    change rhs r ≤ c * ‖curveCharacteristicPower F r‖
    rw [← abs_of_nonneg hright, ← Real.norm_eq_abs]
    exact hr)

/-- Root-counting sum, written in the paper's notation as the pole count of
the tropical reciprocal `-h`. -/
def ambientReciprocalCounting {k : ℕ} (upTo : ℕ) (r : ℝ)
    (h : NthTropicalMeromorphicFunction k) : ℝ :=
  ∑ j ∈ Finset.Icc 1 upTo, integratedCounting j r (-h)

/-- The ordinary Fermat endpoint mean used after Jensen's formula. -/
def ordinaryFermatEndpointMean {m n : ℕ}
    (P : OrdinaryHomogeneousFermatPolynomial m n)
    (F : TropicalHolomorphicCurveRepresentation 1 m) (r : ℝ) : ℝ :=
  (P.composeRaw F r + P.composeRaw F (-r)) / 2

/-- `lower ≤ middle + o(scale)` and `middle ≤ upper + o(scale)` at infinity.
Two error functions are used because this is the unambiguous rigorous reading
of the two occurrences of `o(T_f(r)^n)` in a two-sided estimate. -/
def IsSandwichedUpToLittleOAtTop
    (lower middle upper scale : ℝ → ℝ) : Prop :=
  ∃ lowerError upperError : ℝ → ℝ,
    lowerError =o[atTop] scale ∧
    upperError =o[atTop] scale ∧
    lower ≤ᶠ[atTop] (fun r ↦ middle r + lowerError r) ∧
    middle ≤ᶠ[atTop] (fun r ↦ upper r + upperError r)

/-- Replacing the middle term by a function differing from it by
`o(scale)` preserves a two-sided little-o sandwich. -/
theorem IsSandwichedUpToLittleOAtTop.congr_middle
    {lower middle replacement upper scale : ℝ → ℝ}
    (h : IsSandwichedUpToLittleOAtTop lower middle upper scale)
    (hdiff : (fun r ↦ replacement r - middle r) =o[atTop] scale) :
    IsSandwichedUpToLittleOAtTop lower replacement upper scale := by
  rcases h with ⟨lowerError, upperError, hlowerError, hupperError,
    hlower, hupper⟩
  refine ⟨fun r ↦ lowerError r - (replacement r - middle r),
    fun r ↦ upperError r + (replacement r - middle r),
    hlowerError.sub hdiff, hupperError.add hdiff, ?_, ?_⟩
  · filter_upwards [hlower] with r hr
    linarith
  · filter_upwards [hupper] with r hr
    linarith

/-- The reciprocal count equals the endpoint mean, the pole count, and the
constant Jensen correction.  This is the exact part of equation (Pn). -/
theorem ambientReciprocalCounting_eq_ordinaryFermatEndpointMean_sub_add
    {m n : ℕ} (P : OrdinaryHomogeneousFermatPolynomial m n)
    (F : TropicalHolomorphicCurveRepresentation 1 m)
    (C : P.CurveComposition F) {r : ℝ} (hr : 0 < r) :
    ambientReciprocalCounting n r C.function =
      ordinaryFermatEndpointMean P F r - C.function 0 +
        ambientPoleCounting n r C.function := by
  have hsigned := ambientSignedCountingDifference_eq_endpointMean_sub
    C.function C.order_le hr
  unfold ambientSignedCountingDifference at hsigned
  unfold ambientReciprocalCounting ambientPoleCounting ordinaryFermatEndpointMean
  rw [← C.eq_composeRaw r, ← C.eq_composeRaw (-r)]
  linarith

/-- A fixed constant is `o(T_f^n)` under the growth condition, provided
`n ≥ 1`. -/
theorem constant_isLittleO_curveCharacteristicPower
    {m n : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hn : 1 ≤ n) (hGrowth : CurveCharacteristicDominatesRadius F) (c : ℝ) :
    (fun _r : ℝ ↦ c) =o[atTop]
      fun r ↦ curveCharacteristicPower (n := n) F r := by
  have hconstantPower :
      (fun _r : ℝ ↦ c) =o[atTop] (fun r : ℝ ↦ r ^ n) := by
    have hpower := Asymptotics.isLittleO_pow_pow_atTop_of_lt
      (𝕜 := ℝ) (p := 0) (q := n) (show 0 < n from hn)
    have hscaled := hpower.const_mul_left c
    simpa using hscaled
  have hgrowthPower := hGrowth.pow (show 0 < n from hn)
  exact hconstantPower.trans (by
    simpa [CurveCharacteristicDominatesRadius, curveCharacteristicPower] using
      hgrowthPower)

theorem maxPlusPositivePart_eq_add_negativePart (x : ℝ) :
    maxPlusPositivePart x = x + maxPlusPositivePart (-x) := by
  rcases le_total 0 x with hx | hx
  · simp [maxPlusPositivePart, max_eq_left hx,
      max_eq_right (neg_nonpos.mpr hx)]
  · simp [maxPlusPositivePart, max_eq_right hx,
      max_eq_left (neg_nonneg.mpr hx)]

/-- Passing from the centered Cartan characteristic to the symmetric mean of
the positive coordinate maximum changes the answer by `o(T_f)`. -/
theorem positiveCurveEndpointMean_sub_characteristic_isLittleO
    {m : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hGrowth : OrdinaryFermatGrowthLimsupCondition F) :
    (fun r ↦ positiveCurveEndpointMean F r - cartanCharacteristic F r) =o[atTop]
      fun r ↦ cartanCharacteristic F r := by
  let M : ℝ → ℝ := curveCoordinateMaximum F
  have hmaxPosBigO :
      (fun r : ℝ ↦ maxPlusPositivePart (-M r)) =O[atTop]
        fun r ↦ maxPlusPositivePart (-F.eval 0 r) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [] with r
    have hcoord := coordinate_le_curveCoordinateMaximum F (0 : Fin (m + 1)) r
    have hle : maxPlusPositivePart (-M r) ≤
        maxPlusPositivePart (-F.eval 0 r) := by
      unfold maxPlusPositivePart
      exact max_le_max_right 0 (neg_le_neg hcoord)
    simp only [Real.norm_eq_abs, one_mul,
      abs_of_nonneg (maxPlusPositivePart_nonneg (-M r)),
      abs_of_nonneg (maxPlusPositivePart_nonneg (-F.eval 0 r))]
    exact hle
  have hmaxNegBigO :
      (fun r : ℝ ↦ maxPlusPositivePart (-M (-r))) =O[atTop]
        fun r ↦ maxPlusPositivePart (-F.eval 0 (-r)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [] with r
    have hcoord := coordinate_le_curveCoordinateMaximum F (0 : Fin (m + 1)) (-r)
    have hle : maxPlusPositivePart (-M (-r)) ≤
        maxPlusPositivePart (-F.eval 0 (-r)) := by
      unfold maxPlusPositivePart
      exact max_le_max_right 0 (neg_le_neg hcoord)
    simp only [Real.norm_eq_abs, one_mul,
      abs_of_nonneg (maxPlusPositivePart_nonneg (-M (-r))),
      abs_of_nonneg (maxPlusPositivePart_nonneg (-F.eval 0 (-r)))]
    exact hle
  have hpos := hmaxPosBigO.trans_isLittleO
    (coordinate_positiveTail_negativePart_isLittleO_characteristic F hGrowth 0)
  have hneg := hmaxNegBigO.trans_isLittleO
    (coordinate_negativeTail_negativePart_isLittleO_characteristic F hGrowth 0)
  have htails := (hpos.add hneg).const_mul_left (1 / 2 : ℝ)
  have hconstant := constant_isLittleO_curveCharacteristicPower
    F (show 1 ≤ 1 by rfl)
      (radius_isLittleO_characteristic_of_growthLimsupCondition F hGrowth) (M 0)
  have hsum := htails.add (by
    simpa only [curveCharacteristicPower, pow_one] using hconstant)
  apply hsum.congr'
  · filter_upwards [] with r
    unfold positiveCurveEndpointMean positiveCurveMaximum cartanCharacteristic
    dsimp [M]
    have hr := maxPlusPositivePart_eq_add_negativePart
      (curveCoordinateMaximum F r)
    have hl := maxPlusPositivePart_eq_add_negativePart
      (curveCoordinateMaximum F (-r))
    linarith
  · exact EventuallyEq.rfl

/-- The positive endpoint mean and the Cartan characteristic have the same
`n`-th power up to `o(T_f^n)`. -/
theorem positiveCurveEndpointMean_pow_sub_characteristicPower_isLittleO
    {m n : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hGrowth : OrdinaryFermatGrowthLimsupCondition F) (hn : 1 ≤ n) :
    (fun r ↦ positiveCurveEndpointMean F r ^ n -
      curveCharacteristicPower (n := n) F r) =o[atTop]
        fun r ↦ curveCharacteristicPower (n := n) F r := by
  simpa [curveCharacteristicPower] using pow_sub_pow_isLittleO
    (positiveCurveEndpointMean_sub_characteristic_isLittleO F hGrowth) hn

/-- A real power differs from the same power of its positive part only by
the `n`-th power of its negative part.  The inequality is uniform in parity. -/
theorem abs_pow_sub_positivePart_pow_le_negativePart_pow
    (x : ℝ) (n : ℕ) :
    |x ^ n - (maxPlusPositivePart x) ^ n| ≤
      (maxPlusPositivePart (-x)) ^ n := by
  rcases le_total 0 x with hx | hx
  · have hpx : maxPlusPositivePart x = x := by
      exact max_eq_left hx
    have hnx : maxPlusPositivePart (-x) = 0 := by
      exact max_eq_right (neg_nonpos.mpr hx)
    rw [hpx, hnx]
    simp
  · have hxneg : x ≤ 0 := hx
    have hpx : maxPlusPositivePart x = 0 := by
      exact max_eq_right hxneg
    have hnx : maxPlusPositivePart (-x) = -x := by
      exact max_eq_left (neg_nonneg.mpr hxneg)
    rw [hpx, hnx]
    by_cases hn0 : n = 0
    · subst n
      norm_num
    · rw [zero_pow hn0, sub_zero, abs_pow, abs_of_nonpos hxneg]

/-- Removing all negative coordinate endpoint values changes the ordinary
Fermat endpoint mean by `o(T_f^n)`. -/
theorem ordinaryFermatEndpointMean_sub_positive_isLittleO
    {m n : ℕ} (P : OrdinaryHomogeneousFermatPolynomial m n)
    (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hGrowth : OrdinaryFermatGrowthLimsupCondition F) (hn : 1 ≤ n) :
    (fun r ↦ ordinaryFermatEndpointMean P F r -
      positiveFermatEndpointMean P F r) =o[atTop]
        fun r ↦ curveCharacteristicPower (n := n) F r := by
  let error : Fin (m + 1) → ℝ → ℝ := fun i r ↦
    (P.coefficient i / 2) *
      ((F.eval i r) ^ n - (maxPlusPositivePart (F.eval i r)) ^ n +
        ((F.eval i (-r)) ^ n - (maxPlusPositivePart (F.eval i (-r))) ^ n))
  have herror (i : Fin (m + 1)) :
      error i =o[atTop] fun r ↦ curveCharacteristicPower (n := n) F r := by
    have hbig : error i =O[atTop] fun r ↦
        (maxPlusPositivePart (-F.eval i r)) ^ n +
          (maxPlusPositivePart (-F.eval i (-r))) ^ n := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨|P.coefficient i| / 2, ?_⟩
      filter_upwards [] with r
      have hr := abs_pow_sub_positivePart_pow_le_negativePart_pow (F.eval i r) n
      have hl := abs_pow_sub_positivePart_pow_le_negativePart_pow (F.eval i (-r)) n
      have htails : 0 ≤ (maxPlusPositivePart (-F.eval i r)) ^ n +
          (maxPlusPositivePart (-F.eval i (-r))) ^ n :=
        add_nonneg (pow_nonneg (maxPlusPositivePart_nonneg _) _)
          (pow_nonneg (maxPlusPositivePart_nonneg _) _)
      dsimp [error]
      rw [abs_of_nonneg htails]
      calc
        |P.coefficient i / 2 *
            ((F.eval i r) ^ n - (maxPlusPositivePart (F.eval i r)) ^ n +
              ((F.eval i (-r)) ^ n -
                (maxPlusPositivePart (F.eval i (-r))) ^ n))| =
            (|P.coefficient i| / 2) *
              |(F.eval i r) ^ n - (maxPlusPositivePart (F.eval i r)) ^ n +
                ((F.eval i (-r)) ^ n -
                  (maxPlusPositivePart (F.eval i (-r))) ^ n)| := by
              rw [abs_mul, abs_div]
              norm_num
        _ ≤ (|P.coefficient i| / 2) *
            ((maxPlusPositivePart (-F.eval i r)) ^ n +
              (maxPlusPositivePart (-F.eval i (-r))) ^ n) := by
              apply mul_le_mul_of_nonneg_left _ (div_nonneg (abs_nonneg _) (by norm_num))
              exact (abs_add_le _ _).trans (add_le_add hr hl)
    exact hbig.trans_isLittleO
      (coordinate_negativeTailPowers_isLittleO_characteristicPower F hGrowth hn i)
  have hsum : (fun r ↦ ∑ i, error i r) =o[atTop]
      fun r ↦ curveCharacteristicPower (n := n) F r := by
    exact Asymptotics.IsLittleO.sum (fun i _hi ↦ herror i)
  apply hsum.congr'
  · filter_upwards [] with r
    unfold ordinaryFermatEndpointMean OrdinaryHomogeneousFermatPolynomial.composeRaw
      OrdinaryHomogeneousFermatPolynomial.eval positiveFermatEndpointMean
      positiveCoordinateFermatSum
    dsimp [error]
    calc
      (∑ i,
          P.coefficient i / 2 *
            ((F.eval i r) ^ n - (maxPlusPositivePart (F.eval i r)) ^ n +
              ((F.eval i (-r)) ^ n -
                (maxPlusPositivePart (F.eval i (-r))) ^ n))) =
          ∑ i,
            ((P.coefficient i * (F.eval i r) ^ n +
                P.coefficient i * (F.eval i (-r)) ^ n) / 2 -
              (P.coefficient i * (maxPlusPositivePart (F.eval i r)) ^ n +
                P.coefficient i * (maxPlusPositivePart (F.eval i (-r))) ^ n) / 2) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ =
          ((∑ i, P.coefficient i * (F.eval i r) ^ n) +
              (∑ i, P.coefficient i * (F.eval i (-r)) ^ n)) / 2 -
            ((∑ i, P.coefficient i * (maxPlusPositivePart (F.eval i r)) ^ n) +
              (∑ i, P.coefficient i * (maxPlusPositivePart (F.eval i (-r))) ^ n)) / 2 := by
            rw [Finset.sum_sub_distrib]
            simp only [div_eq_mul_inv]
            congr 1 <;> rw [← Finset.sum_mul, Finset.sum_add_distrib]
  · exact EventuallyEq.rfl

/-- The endpoint part of Theorem 5.8, including the two error terms hidden by
the paper's `o(T_f(r)^n)` notation.  This combines the exact positive-part
inequality with the two independently verified little-o comparisons above. -/
theorem ordinaryFermatEndpointMean_sandwich
    {m n : ℕ} (P : OrdinaryHomogeneousFermatPolynomial m n)
    (hP : P.HasPositiveCoefficients)
    (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hGrowth : OrdinaryFermatGrowthLimsupCondition F) (hn : 1 ≤ n) :
    IsSandwichedUpToLittleOAtTop
      (fun r ↦ P.coefficientMinimum * curveCharacteristicPower (n := n) F r)
      (ordinaryFermatEndpointMean P F)
      (fun r ↦ P.upperCoefficient * curveCharacteristicPower (n := n) F r)
      (curveCharacteristicPower (n := n) F) := by
  let scale : ℝ → ℝ := fun r ↦ curveCharacteristicPower (n := n) F r
  let powerError : ℝ → ℝ := fun r ↦
    positiveCurveEndpointMean F r ^ n - scale r
  let endpointError : ℝ → ℝ := fun r ↦
    ordinaryFermatEndpointMean P F r - positiveFermatEndpointMean P F r
  have hpower : powerError =o[atTop] scale := by
    simpa [powerError, scale] using
      positiveCurveEndpointMean_pow_sub_characteristicPower_isLittleO F hGrowth hn
  have hendpoint : endpointError =o[atTop] scale := by
    simpa [endpointError, scale] using
      ordinaryFermatEndpointMean_sub_positive_isLittleO P F hGrowth hn
  let lowerError : ℝ → ℝ := fun r ↦
    -endpointError r - P.coefficientMinimum * powerError r
  let upperError : ℝ → ℝ := fun r ↦
    P.upperCoefficient * powerError r + endpointError r
  have hlowerError : lowerError =o[atTop] scale := by
    simpa [lowerError] using
      (hendpoint.const_mul_left (-1 : ℝ)).sub
        (hpower.const_mul_left P.coefficientMinimum)
  have hupperError : upperError =o[atTop] scale := by
    exact (hpower.const_mul_left P.upperCoefficient).add hendpoint
  refine ⟨lowerError, upperError, hlowerError, hupperError, ?_, ?_⟩
  · filter_upwards [] with r
    have hpos := (positiveFermatEndpointMean_sandwich P hP hn F r).1
    dsimp [lowerError, endpointError, powerError, scale]
    linarith
  · filter_upwards [] with r
    have hpos := (positiveFermatEndpointMean_sandwich P hP hn F r).2
    dsimp [upperError, endpointError, powerError, scale]
    linarith

/-- Any `O(r^n)` error is negligible compared with `T_f(r)^n` under the
growth assumption of Theorem 5.8.  This is the precise final step used after
the polynomial pole-count estimate (5a19). -/
theorem isLittleO_curveCharacteristicPower_of_isBigO_radiusPower
    {m n : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hGrowth : OrdinaryFermatGrowthLimsupCondition F) (hn : 1 ≤ n)
    {A : ℝ → ℝ} (hA : A =O[atTop] fun r : ℝ ↦ r ^ n) :
    A =o[atTop] fun r ↦ curveCharacteristicPower (n := n) F r := by
  have hr := radius_isLittleO_characteristic_of_growthLimsupCondition F hGrowth
  have hrn := hr.pow (show 0 < n from hn)
  exact hA.trans_isLittleO (by
    simpa [CurveCharacteristicDominatesRadius, curveCharacteristicPower] using hrn)

/-- The precise formal conclusion corresponding to formula (5f2). -/
def OrdinaryFermatSecondMainConclusion
    {m n : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m)
    (P : OrdinaryHomogeneousFermatPolynomial m n) : Prop :=
  IsSandwichedUpToLittleOAtTop
    (fun r ↦ P.coefficientMinimum * curveCharacteristicPower (n := n) F r)
    (fun r ↦ ambientReciprocalCounting n r (P.curveComposition F).function)
    (fun r ↦ P.upperCoefficient * curveCharacteristicPower (n := n) F r)
    (curveCharacteristicPower (n := n) F)

/-- Theorem 5.8 with the paper's original mathematical hypotheses.  The
assumption `1 ≤ n` only makes explicit that the paper's natural degree is
positive; Lean's naturals also contain zero, for which the displayed lower
bound is generally false.  Both the pole estimate (5a12)--(5a19) and the
endpoint comparison (5a11), as well as the final Jensen assembly, are proved
above. -/
theorem secondMain_ordinaryFermat
    {m n : ℕ} (F : TropicalHolomorphicCurveRepresentation 1 m)
    (_hFReduced : F.IsReduced)
    (P : OrdinaryHomogeneousFermatPolynomial m n)
    (hPPositive : P.HasPositiveCoefficients)
    (hn : 1 ≤ n) (hGrowth : OrdinaryFermatGrowthLimsupCondition F) :
    OrdinaryFermatSecondMainConclusion F P := by
  let C := P.curveComposition F
  have hpole := ordinaryFermatComposition_poleCounting_isLittleO
    F P hPPositive hGrowth hn
  have hconstant := constant_isLittleO_curveCharacteristicPower
    F hn (radius_isLittleO_characteristic_of_growthLimsupCondition F hGrowth)
      (C.function 0)
  have hpoleSubConstant :
      (fun r ↦ ambientPoleCounting n r C.function - C.function 0) =o[atTop]
        fun r ↦ curveCharacteristicPower (n := n) F r :=
    hpole.sub hconstant
  have hreciprocalDiff :
      (fun r ↦ ambientReciprocalCounting n r C.function -
        ordinaryFermatEndpointMean P F r) =o[atTop]
          fun r ↦ curveCharacteristicPower (n := n) F r := by
    apply hpoleSubConstant.congr'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      rw [ambientReciprocalCounting_eq_ordinaryFermatEndpointMean_sub_add
        P F C hr]
      ring
    · exact EventuallyEq.rfl
  exact (ordinaryFermatEndpointMean_sandwich P hPPositive F hGrowth hn).congr_middle
    hreciprocalDiff

end

end NthTropicalNevanlinna
