import NthTropicalNevanlinna.Curves.Fermat
import NthTropicalNevanlinna.Function.SplineAssembly

/-!
# Examples 5.9 and 5.10

This file keeps the examples separate from the statement of Theorem 5.8.
Example 5.9 is evaluated exactly.  Example 5.10 is organized around the two
piecewise-linear entire functions displayed in the paper; its asymptotic
conclusions are then derived from their elementary quadratic estimates and
Jensen's formula.
-/

open Filter Set
open scoped BigOperators Topology

namespace NthTropicalNevanlinna

noncomputable section

/-! ## Globally polynomial examples -/

/-- A polynomial regarded as a function on the whole real line, presented on
the redundant integer cut grid.  This is useful for concrete examples: every
local polynomial germ is literally `p`. -/
def globalPolynomialPresentation {n : ℕ} (p : Polynomial ℝ)
    (hp : p.natDegree = n) :
    PolynomialPresentation n (fun x : ℝ ↦ p.eval x) where
  cutPoint i := (i : ℝ)
  piece _ := p
  cutPoint_strictMono := by
    intro i k hik
    change (i : ℝ) < (k : ℝ)
    exact_mod_cast hik
  cutPoint_zero := by simp
  cutPoint_tendsto_atTop := tendsto_intCast_atTop_atTop
  cutPoint_tendsto_atBot := tendsto_intCast_atBot_iff.mpr tendsto_id
  piece_natDegree_le := by intro i; simp [hp]
  eq_piece := by intro i x hx; rfl
  exists_piece_natDegree_eq := ⟨0, hp⟩

/-- Bundle a real polynomial of exact degree `n` as an `n`-th tropical
meromorphic function. -/
def globalPolynomialFunction {n : ℕ} (p : Polynomial ℝ)
    (hp : p.natDegree = n) : NthTropicalMeromorphicFunction n where
  toFun x := p.eval x
  continuous_toFun := p.continuous
  hasPolynomialPresentation := ⟨globalPolynomialPresentation p hp⟩

@[simp]
theorem globalPolynomialFunction_apply {n : ℕ} (p : Polynomial ℝ)
    (hp : p.natDegree = n) (x : ℝ) :
    globalPolynomialFunction p hp x = p.eval x := rfl

theorem multiplicity_globalPolynomialFunction {n : ℕ} (p : Polynomial ℝ)
    (hp : p.natDegree = n) (j : ℕ) (x : ℝ) :
    multiplicity (globalPolynomialFunction p hp) j x =
      rightSign x ^ (j + 1) * normalizedPolynomialJet p j x -
        leftSign x ^ (j + 1) * normalizedPolynomialJet p j x := by
  let P := globalPolynomialPresentation p hp
  rw [multiplicity_eq_usingPresentation (globalPolynomialFunction p hp) P]
  simp [multiplicityUsingPresentation, PolynomialPresentation.leftPieceAt,
    PolynomialPresentation.rightPieceAt, P, globalPolynomialPresentation]

theorem multiplicity_globalPolynomialFunction_of_ne_zero {n : ℕ}
    (p : Polynomial ℝ) (hp : p.natDegree = n) (j : ℕ) {x : ℝ}
    (hx : x ≠ 0) : multiplicity (globalPolynomialFunction p hp) j x = 0 := by
  rw [multiplicity_globalPolynomialFunction]
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · simp [rightSign_of_neg hxneg, leftSign_of_nonpos hxneg.le]
  · simp [rightSign_of_nonneg hxpos.le, leftSign_of_pos hxpos]

/-! ## Example 5.9 -/

def example59ZeroPolynomial : Polynomial ℝ := 0

def example59LinearPolynomial : Polynomial ℝ := 2 * Polynomial.X

def example59QuadraticPolynomial : Polynomial ℝ := 8 * Polynomial.X ^ 2

@[simp] theorem example59ZeroPolynomial_natDegree :
    example59ZeroPolynomial.natDegree = 0 := by simp [example59ZeroPolynomial]

@[simp] theorem example59LinearPolynomial_natDegree :
    example59LinearPolynomial.natDegree = 1 := by
  norm_num [example59LinearPolynomial]

@[simp] theorem example59QuadraticPolynomial_natDegree :
    example59QuadraticPolynomial.natDegree = 2 := by
  norm_num [example59QuadraticPolynomial]

def example59Zero : NthTropicalMeromorphicFunction 0 :=
  globalPolynomialFunction example59ZeroPolynomial example59ZeroPolynomial_natDegree

def example59Linear : NthTropicalMeromorphicFunction 1 :=
  globalPolynomialFunction example59LinearPolynomial example59LinearPolynomial_natDegree

def example59Quadratic : NthTropicalMeromorphicFunction 2 :=
  globalPolynomialFunction example59QuadraticPolynomial example59QuadraticPolynomial_natDegree

@[simp] theorem example59Zero_apply (x : ℝ) : example59Zero x = 0 := by
  simp [example59Zero, example59ZeroPolynomial]

@[simp] theorem example59Linear_apply (x : ℝ) : example59Linear x = 2 * x := by
  simp [example59Linear, example59LinearPolynomial]

@[simp] theorem example59Quadratic_apply (x : ℝ) : example59Quadratic x = 8 * x ^ 2 := by
  simp [example59Quadratic, example59QuadraticPolynomial]

theorem example59Zero_multiplicity_eq_zero (j : ℕ) (x : ℝ) :
    multiplicity example59Zero j x = 0 := by
  change multiplicity
    (globalPolynomialFunction example59ZeroPolynomial
      example59ZeroPolynomial_natDegree) j x = 0
  rw [multiplicity_globalPolynomialFunction]
  simp [example59ZeroPolynomial, normalizedPolynomialJet, rightSign, leftSign]

theorem example59Linear_multiplicity_eq_zero (j : ℕ) (x : ℝ) :
    multiplicity example59Linear j x = 0 := by
  by_cases hj0 : j = 0
  · subst j
    change multiplicity
      (globalPolynomialFunction example59LinearPolynomial
        example59LinearPolynomial_natDegree) 0 x = 0
    rw [multiplicity_globalPolynomialFunction]
    simp [example59Linear, example59LinearPolynomial, normalizedPolynomialJet,
      rightSign, leftSign]
    split_ifs <;> linarith
  · by_cases hj1 : j = 1
    · subst j
      change multiplicity
        (globalPolynomialFunction example59LinearPolynomial
          example59LinearPolynomial_natDegree) 1 x = 0
      rw [multiplicity_globalPolynomialFunction]
      simp [example59Linear, example59LinearPolynomial, normalizedPolynomialJet,
        rightSign, leftSign]
    · have h1j : 1 < j := by omega
      exact multiplicity_eq_zero_of_order_lt example59Linear h1j x

def example59FourLinearPolynomial : Polynomial ℝ := 4 * Polynomial.X

@[simp] theorem example59FourLinearPolynomial_natDegree :
    example59FourLinearPolynomial.natDegree = 1 := by
  norm_num [example59FourLinearPolynomial]

def example59FourLinear : NthTropicalMeromorphicFunction 1 :=
  globalPolynomialFunction example59FourLinearPolynomial
    example59FourLinearPolynomial_natDegree

@[simp] theorem example59FourLinear_apply (x : ℝ) : example59FourLinear x = 4 * x := by
  simp [example59FourLinear, example59FourLinearPolynomial]

theorem example59FourLinear_multiplicity_eq_zero (j : ℕ) (x : ℝ) :
    multiplicity example59FourLinear j x = 0 := by
  by_cases hj0 : j = 0
  · subst j
    change multiplicity
      (globalPolynomialFunction example59FourLinearPolynomial
        example59FourLinearPolynomial_natDegree) 0 x = 0
    rw [multiplicity_globalPolynomialFunction]
    simp [example59FourLinearPolynomial, normalizedPolynomialJet,
      rightSign, leftSign]
    split_ifs <;> linarith
  · by_cases hj1 : j = 1
    · subst j
      change multiplicity
        (globalPolynomialFunction example59FourLinearPolynomial
          example59FourLinearPolynomial_natDegree) 1 x = 0
      rw [multiplicity_globalPolynomialFunction]
      simp [example59FourLinearPolynomial, normalizedPolynomialJet,
        rightSign, leftSign]
    · exact multiplicity_eq_zero_of_order_lt example59FourLinear (by omega) x

/-- The paper's chosen heterogeneous-order representation `[0 : 2x]`.
The first coordinate has exact order zero and the second exact order one. -/
def example59Curve : TropicalHolomorphicCurveRepresentation 1 1 where
  order i := if i = 0 then 0 else 1
  order_le := by intro i; split_ifs <;> omega
  order_attained := ⟨1, by simp⟩
  coordinate i := by
    by_cases hi : i = 0
    · subst i
      simpa using example59Zero
    · have hi1 : i = 1 := by
        fin_cases i
        · contradiction
        · rfl
      subst i
      simpa using example59Linear
  coordinate_multiplicity_nonneg := by
    intro i x j hj hj1
    by_cases hi : i = 0
    · subst i
      change 0 ≤ multiplicity example59Zero j x
      rw [example59Zero_multiplicity_eq_zero]
    · have hi1 : i = 1 := by
        fin_cases i
        · contradiction
        · rfl
      subst i
      change 0 ≤ multiplicity example59Linear j x
      rw [example59Linear_multiplicity_eq_zero]

@[simp] theorem example59Curve_eval_zero (x : ℝ) : example59Curve.eval 0 x = 0 := by
  simp [example59Curve, TropicalHolomorphicCurveRepresentation.eval]

@[simp] theorem example59Curve_eval_one (x : ℝ) : example59Curve.eval 1 x = 2 * x := by
  simp [example59Curve, TropicalHolomorphicCurveRepresentation.eval]

theorem example59_curveCoordinateMaximum (x : ℝ) :
    curveCoordinateMaximum example59Curve x = max 0 (2 * x) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _hi
    fin_cases i
    · simp [example59Curve_eval_zero]
    · simp [example59Curve_eval_one]
  · apply max_le
    · rw [curveCoordinateMaximum]
      simpa only [example59Curve_eval_zero] using
        (Finset.le_sup' (fun i : Fin 2 ↦ example59Curve.eval i x)
          (Finset.mem_univ (0 : Fin 2)))
    · rw [curveCoordinateMaximum]
      simpa only [example59Curve_eval_one] using
        (Finset.le_sup' (fun i : Fin 2 ↦ example59Curve.eval i x)
          (Finset.mem_univ (1 : Fin 2)))

/-- The exact characteristic calculation `T_[0:2x](r)=r`. -/
theorem example59_cartanCharacteristic {r : ℝ} (hr : 0 ≤ r) :
    cartanCharacteristic example59Curve r = r := by
  rw [cartanCharacteristic]
  simp only [example59_curveCoordinateMaximum]
  rw [max_eq_right (by linarith : 0 ≤ 2 * r)]
  rw [max_eq_left (by linarith : 2 * (-r) ≤ 0)]
  simp <;> ring

theorem example59_growth_ratio {r : ℝ} (hr : 0 < r) :
    r / cartanCharacteristic example59Curve r = 1 := by
  rw [example59_cartanCharacteristic hr.le]
  exact div_self (ne_of_gt hr)

/-- The linear-growth curve in Example 5.9 does not satisfy (5f1). -/
theorem example59_not_growthLimsupCondition :
    ¬ OrdinaryFermatGrowthLimsupCondition example59Curve := by
  intro hGrowth
  have heventually :
      (fun r : ℝ ↦ ((r / cartanCharacteristic example59Curve r : ℝ) : EReal))
        =ᶠ[atTop] (fun _r : ℝ ↦ (1 : EReal)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [example59_growth_ratio hr]
    norm_num
  have hlimsup := Filter.limsup_congr heventually
  have honezero : (1 : EReal) = 0 := by
    rw [← Filter.limsup_const (f := (atTop : Filter ℝ)) (1 : EReal), ← hlimsup]
    exact hGrowth.2
  norm_num at honezero

/-- The ordinary Fermat polynomial in Example 5.9 has coefficients `(1,2)`
and degree two. -/
def example59FermatPolynomial : OrdinaryHomogeneousFermatPolynomial 1 2 where
  coefficient i := if i = 0 then 1 else 2

/-- The ordinary composition of the polynomial with the same curve object
used above is exactly `8x²`. -/
theorem example59_ordinaryComposition (x : ℝ) :
    example59FermatPolynomial.composeRaw example59Curve x =
      8 * x ^ 2 := by
  unfold OrdinaryHomogeneousFermatPolynomial.composeRaw
    OrdinaryHomogeneousFermatPolynomial.eval example59FermatPolynomial
  rw [Fin.sum_univ_two]
  simp
  ring

/-- A coherent realization of the ordinary composition in Example 5.9. -/
def example59Composition :
    example59FermatPolynomial.CurveComposition example59Curve where
  order := 2
  order_le := le_rfl
  function := example59Quadratic
  eq_composeRaw := fun x ↦ by
    rw [example59_ordinaryComposition, example59Quadratic_apply]

theorem example59Quadratic_multiplicity_one (x : ℝ) :
    multiplicity example59Quadratic 1 x = 0 := by
  by_cases hx : x = 0
  · subst x
    change multiplicity
      (globalPolynomialFunction example59QuadraticPolynomial
        example59QuadraticPolynomial_natDegree) 1 0 = 0
    rw [multiplicity_globalPolynomialFunction]
    norm_num [example59QuadraticPolynomial, normalizedPolynomialJet,
      rightSign, leftSign, ← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.hasseDeriv_monomial]
  · exact multiplicity_globalPolynomialFunction_of_ne_zero _ _ _ hx

theorem example59Quadratic_multiplicity_two (x : ℝ) :
    multiplicity example59Quadratic 2 x = if x = 0 then 16 else 0 := by
  by_cases hx : x = 0
  · subst x
    simp only [if_pos rfl]
    change multiplicity
      (globalPolynomialFunction example59QuadraticPolynomial
        example59QuadraticPolynomial_natDegree) 2 0 = 16
    rw [multiplicity_globalPolynomialFunction]
    simp_rw [normalizedPolynomialJet_eq_iterateDerivative_div]
    norm_num [example59QuadraticPolynomial, rightSign, leftSign]
  · rw [if_neg hx]
    exact multiplicity_globalPolynomialFunction_of_ne_zero _ _ _ hx

theorem example59Quadratic_entire : IsTropicalEntire example59Quadratic := by
  rw [isTropicalEntire_iff_multiplicity_nonneg]
  intro x j hj hj2
  interval_cases j
  · rw [example59Quadratic_multiplicity_one]
  · rw [example59Quadratic_multiplicity_two]
    split_ifs <;> norm_num

/-- The exact counting conclusion of Example 5.9.  The second-order root at
zero has multiplicity `16`; Jensen's factor `1/2` therefore gives `8r²`. -/
theorem example59_ambientReciprocalCounting {r : ℝ} (hr : 0 < r) :
    ambientReciprocalCounting 2 r example59Composition.function = 8 * r ^ 2 := by
  have hsigned := ambientSignedCountingDifference_eq_endpointMean_sub
    example59Quadratic (show 2 ≤ 2 by rfl) hr
  have hpole1 := integratedCounting_eq_zero_of_entire_any_order
    example59Quadratic example59Quadratic_entire (j := 1) (by omega) r
  have hpole2 := integratedCounting_eq_zero_of_entire_any_order
    example59Quadratic example59Quadratic_entire (j := 2) (by omega) r
  have hpoles : ambientPoleCounting 2 r example59Quadratic = 0 := by
    unfold ambientPoleCounting
    norm_num [show Finset.Icc 1 2 = {1, 2} by decide, hpole1, hpole2]
  change ambientReciprocalCounting 2 r example59Quadratic -
      ambientPoleCounting 2 r example59Quadratic =
        (example59Quadratic r + example59Quadratic (-r)) / 2 -
          example59Quadratic 0 at hsigned
  rw [hpoles, example59Quadratic_apply, example59Quadratic_apply,
    example59Quadratic_apply] at hsigned
  ring_nf at hsigned ⊢
  exact hsigned

/-! ## Example 5.10 -/

/-! ### Explicit integer-indexed spline constructions -/

/-- Cut grid for the first function: nonpositive integers, followed by the
positive odd integers `1,3,5,…`. -/
def example510FirstCut (i : ℤ) : ℝ :=
  if i ≤ 0 then (i : ℝ) else (2 * i - 1 : ℤ)

@[simp] theorem example510FirstCut_zero : example510FirstCut 0 = 0 := by
  simp [example510FirstCut]

theorem example510FirstCut_strictMono : StrictMono example510FirstCut := by
  intro i j hij
  by_cases hi : i ≤ 0
  · by_cases hj : j ≤ 0
    · simp [example510FirstCut, hi, hj]
      exact_mod_cast hij
    · have hjpos : 0 < j := lt_of_not_ge hj
      simp only [example510FirstCut, if_pos hi, if_neg hj]
      exact_mod_cast (show i < 2 * j - 1 by omega)
  · have hipos : 0 < i := lt_of_not_ge hi
    have hjpos : 0 < j := hipos.trans hij
    simp only [example510FirstCut, if_neg hi, if_neg (not_le.mpr hjpos)]
    exact_mod_cast (show 2 * i - 1 < 2 * j - 1 by omega)

theorem example510FirstCut_tendsto_atTop :
    Tendsto example510FirstCut atTop atTop := by
  apply tendsto_atTop_mono (f := fun i : ℤ ↦ (i : ℝ))
  · intro i
    by_cases hi : i ≤ 0
    · simp [example510FirstCut, hi]
    · rw [example510FirstCut, if_neg hi]
      norm_num
      exact_mod_cast (show i ≤ 2 * i - 1 by omega)
  · exact tendsto_intCast_atTop_atTop

theorem example510FirstCut_tendsto_atBot :
    Tendsto example510FirstCut atBot atBot := by
  apply (tendsto_intCast_atBot_iff.mpr tendsto_id).congr'
  filter_upwards [eventually_le_atBot (0 : ℤ)] with i hi
  simp [example510FirstCut, hi]

/-- A degree-one carrier presentation for the first cut grid.  Only its cut
sequence is used by the spline assembly. -/
def example510FirstGrid : PolynomialPresentation 1 (fun x : ℝ ↦ x) where
  cutPoint := example510FirstCut
  piece _ := Polynomial.X
  cutPoint_strictMono := example510FirstCut_strictMono
  cutPoint_zero := example510FirstCut_zero
  cutPoint_tendsto_atTop := example510FirstCut_tendsto_atTop
  cutPoint_tendsto_atBot := example510FirstCut_tendsto_atBot
  piece_natDegree_le := by simp
  eq_piece := by simp
  exists_piece_natDegree_eq := ⟨0, by simp⟩

/-- Affine pieces of the first function.  Piece `i>1` corresponds to the
paper's natural index `k=i-1`. -/
def example510FirstPiece (i : ℤ) : Polynomial ℝ :=
  if i ≤ 1 then 0 else
    Polynomial.C ((2 * (i - 1) - 1 : ℤ) : ℝ) * Polynomial.X -
      Polynomial.C ((2 * (i - 1) ^ 2 - 1 : ℤ) : ℝ)

theorem example510FirstPiece_degree (i : ℤ) :
    (example510FirstPiece i).natDegree ≤ 1 := by
  unfold example510FirstPiece
  split_ifs
  · simp
  · let a : ℝ := ((2 * (i - 1) - 1 : ℤ) : ℝ)
    let b : ℝ := ((2 * (i - 1) ^ 2 - 1 : ℤ) : ℝ)
    change (Polynomial.C a * Polynomial.X - Polynomial.C b).natDegree ≤ 1
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le
        (Polynomial.natDegree_mul_le.trans (by simp))
        (by simp))

theorem example510FirstPiece_adjacent (i : ℤ) :
    (example510FirstPiece i).eval (example510FirstCut i) =
      (example510FirstPiece (i + 1)).eval (example510FirstCut i) := by
  by_cases hi0 : i ≤ 0
  · have hi1 : i ≤ 1 := hi0.trans (by omega)
    have hisucc : i + 1 ≤ 1 := by omega
    simp [example510FirstPiece, hi1, hisucc]
  · have hipos : 0 < i := lt_of_not_ge hi0
    by_cases hi1 : i ≤ 1
    · have hieq : i = 1 := by omega
      subst i
      norm_num [example510FirstPiece, example510FirstCut]
    · have hi2 : 2 ≤ i := by omega
      have hnoti : ¬i ≤ 1 := hi1
      have hnotsucc : ¬i + 1 ≤ 1 := by omega
      rw [example510FirstPiece, if_neg hnoti,
        example510FirstPiece, if_neg hnotsucc,
        example510FirstCut, if_neg (not_le.mpr hipos)]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      push_cast
      ring

theorem example510FirstPiece_exact :
    ∃ i, (example510FirstPiece i).natDegree = 1 := by
  refine ⟨2, ?_⟩
  rw [example510FirstPiece, if_neg (by norm_num)]
  convert Polynomial.natDegree_X_sub_C (1 : ℝ) using 1 <;> norm_num

/-- The first piecewise-linear entire candidate from Example 5.10. -/
def example510First : NthTropicalMeromorphicFunction 1 :=
  assembleNthTropicalMeromorphicFunction example510FirstGrid
    example510FirstPiece example510FirstPiece_degree
    example510FirstPiece_adjacent example510FirstPiece_exact

theorem example510First_eq_piece (i : ℤ) {x : ℝ}
    (hx : x ∈ Icc (example510FirstCut (i - 1)) (example510FirstCut i)) :
    example510First x = (example510FirstPiece i).eval x := by
  exact assembledFunction_eq_piece example510FirstGrid example510FirstPiece
    example510FirstPiece_adjacent i hx

@[simp] theorem example510FirstCut_nat (k : ℕ) (hk : 1 ≤ k) :
    example510FirstCut (k : ℤ) = ((2 * k - 1 : ℕ) : ℝ) := by
  rw [example510FirstCut, if_neg]
  · norm_num
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    push_cast
    ring
  · exact_mod_cast (show ¬k ≤ 0 by omega)

theorem example510First_zero {x : ℝ} (hx : x ≤ 1) :
    example510First x = 0 := by
  let i := presentationIntervalIndex example510FirstGrid x
  have hmem := presentationIntervalIndex_mem example510FirstGrid x
  have hi : i ≤ 1 := by
    by_contra hnot
    have htwo : (2 : ℤ) ≤ i := by omega
    have hcut : example510FirstCut 1 ≤ example510FirstCut (i - 1) :=
      example510FirstCut_strictMono.monotone (by omega)
    have hlower : example510FirstCut (i - 1) < x := hmem.1
    have hone : example510FirstCut 1 = 1 := by norm_num [example510FirstCut]
    rw [hone] at hcut
    linarith [hlower]
  rw [example510First_eq_piece i ⟨hmem.1.le, hmem.2⟩]
  simp [example510FirstPiece, hi]

theorem example510First_piece (k : ℕ) (hk : 1 ≤ k) {x : ℝ}
    (hx : x ∈ Ico ((2 * k - 1 : ℕ) : ℝ) ((2 * k + 1 : ℕ) : ℝ)) :
    example510First x =
      (2 * k - 1 : ℕ) * x - (2 * k ^ 2 - 1 : ℕ) := by
  let i : ℤ := (k : ℤ) + 1
  have hleft : example510FirstCut (i - 1) = ((2 * k - 1 : ℕ) : ℝ) := by
    simpa [i] using example510FirstCut_nat k hk
  have hright : example510FirstCut i = ((2 * k + 1 : ℕ) : ℝ) := by
    rw [show i = ((k + 1 : ℕ) : ℤ) by simp [i]]
    rw [example510FirstCut_nat (k + 1) (by omega)]
    congr 1
  rw [example510First_eq_piece i (by simpa [hleft, hright] using
    (show x ∈ Icc ((2 * k - 1 : ℕ) : ℝ) ((2 * k + 1 : ℕ) : ℝ) from
      ⟨hx.1, le_of_lt hx.2⟩))]
  rw [example510FirstPiece, if_neg (by dsimp [i]; omega)]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  norm_num [i]
  have hkSq : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k (by omega)
  push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k),
    Nat.cast_sub (by omega : 1 ≤ 2 * k ^ 2)]
  ring

theorem example510First_cut_multiplicity_nonneg (i : ℤ) :
    0 ≤ presentationMultiplicityAtCutPoint
      (assembledPolynomialPresentation example510FirstGrid
        example510FirstPiece example510FirstPiece_degree
        example510FirstPiece_adjacent example510FirstPiece_exact) 1 i := by
  by_cases hi : i ≤ 0
  · have hiPiece : i ≤ 1 := by omega
    have hnextPiece : i + 1 ≤ 1 := by omega
    simp [presentationMultiplicityAtCutPoint, assembledPolynomialPresentation,
      example510FirstPiece,
      hiPiece, hnextPiece, normalizedPolynomialJet]
  · have hipos : 0 < i := lt_of_not_ge hi
    rw [presentationMultiplicityAtCutPoint_of_pos_index _ 1 hipos]
    by_cases hi1 : i ≤ 1
    · have hieq : i = 1 := by omega
      subst i
      norm_num [assembledPolynomialPresentation, example510FirstPiece,
        normalizedPolynomialJet]
    · have hnex : ¬i + 1 ≤ 1 := by omega
      simp [assembledPolynomialPresentation, example510FirstPiece,
        hi1, hnex, normalizedPolynomialJet]
      simp [Polynomial.derivative_pow]

theorem example510First_entire : IsTropicalEntire example510First := by
  rw [isTropicalEntire_iff_multiplicity_nonneg]
  intro x j hj hj1
  have hjeq : j = 1 := by omega
  subst j
  let P := assembledPolynomialPresentation example510FirstGrid
    example510FirstPiece example510FirstPiece_degree
    example510FirstPiece_adjacent example510FirstPiece_exact
  rcases multiplicity_eq_zero_or_cutPoint_of_presentation
      example510First P 1 x with hzero | ⟨i, _hxi, hcut⟩
  · rw [hzero]
  · rw [hcut]
    exact example510First_cut_multiplicity_nonneg i

theorem example510First_nonneg (x : ℝ) : 0 ≤ example510First x := by
  let i := presentationIntervalIndex example510FirstGrid x
  have hmem := presentationIntervalIndex_mem example510FirstGrid x
  rw [example510First_eq_piece i ⟨hmem.1.le, hmem.2⟩]
  by_cases hi : i ≤ 1
  · simp [example510FirstPiece, hi]
  · have hipos : 0 < i := by omega
    have hcut : example510FirstCut (i - 1) = ((2 * (i - 1) - 1 : ℤ) : ℝ) := by
      rw [example510FirstCut, if_neg (by omega)]
    rw [example510FirstPiece, if_neg hi]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    have hlower := hmem.1.le
    change example510FirstCut (i - 1) ≤ x at hlower
    rw [hcut] at hlower
    push_cast at hlower ⊢
    have hiReal : (2 : ℝ) ≤ (i : ℝ) := by
      exact_mod_cast (show (2 : ℤ) ≤ i by omega)
    have ht : 1 ≤ (i : ℝ) - 1 := by linarith
    have hcoef : 0 ≤ 2 * ((i : ℝ) - 1) - 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hlower hcoef
    nlinarith [hmul, sq_nonneg (((i : ℝ) - 1) - 1)]

/-- Even-integer cut grid for the second function. -/
def example510SecondCut (i : ℤ) : ℝ := (2 * i : ℤ)

@[simp] theorem example510SecondCut_zero : example510SecondCut 0 = 0 := by
  simp [example510SecondCut]

theorem example510SecondCut_strictMono : StrictMono example510SecondCut := by
  intro i j hij
  unfold example510SecondCut
  exact_mod_cast (show 2 * i < 2 * j by omega)

theorem example510SecondCut_tendsto_atTop :
    Tendsto example510SecondCut atTop atTop := by
  have h := tendsto_intCast_atTop_atTop.const_mul_atTop
    (show (0 : ℝ) < 2 by norm_num)
  apply h.congr'
  exact Eventually.of_forall (fun i ↦ by
    unfold example510SecondCut
    push_cast
    simp)

theorem example510SecondCut_tendsto_atBot :
    Tendsto example510SecondCut atBot atBot := by
  have h := (tendsto_intCast_atBot_iff.mpr tendsto_id).const_mul_atBot
    (show (0 : ℝ) < 2 by norm_num)
  apply h.congr'
  exact Eventually.of_forall (fun i ↦ by
    unfold example510SecondCut
    push_cast
    simp)

def example510SecondGrid : PolynomialPresentation 1 (fun x : ℝ ↦ x) where
  cutPoint := example510SecondCut
  piece _ := Polynomial.X
  cutPoint_strictMono := example510SecondCut_strictMono
  cutPoint_zero := example510SecondCut_zero
  cutPoint_tendsto_atTop := example510SecondCut_tendsto_atTop
  cutPoint_tendsto_atBot := example510SecondCut_tendsto_atBot
  piece_natDegree_le := by simp
  eq_piece := by simp
  exists_piece_natDegree_eq := ⟨0, by simp⟩

def example510SecondPiece (i : ℤ) : Polynomial ℝ :=
  if i ≤ 1 then 0 else
    Polynomial.C ((2 * (i - 1) : ℤ) : ℝ) * Polynomial.X -
      Polynomial.C ((2 * (i - 1) * i : ℤ) : ℝ)

theorem example510SecondPiece_degree (i : ℤ) :
    (example510SecondPiece i).natDegree ≤ 1 := by
  unfold example510SecondPiece
  split_ifs
  · simp
  · let a : ℝ := ((2 * (i - 1) : ℤ) : ℝ)
    let b : ℝ := ((2 * (i - 1) * i : ℤ) : ℝ)
    change (Polynomial.C a * Polynomial.X - Polynomial.C b).natDegree ≤ 1
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le
        (Polynomial.natDegree_mul_le.trans (by simp))
        (by simp))

theorem example510SecondPiece_adjacent (i : ℤ) :
    (example510SecondPiece i).eval (example510SecondCut i) =
      (example510SecondPiece (i + 1)).eval (example510SecondCut i) := by
  by_cases hi1 : i ≤ 1
  · by_cases hi0 : i ≤ 0
    · have hisucc : i + 1 ≤ 1 := by omega
      simp [example510SecondPiece, hi1, hisucc]
    · have hieq : i = 1 := by omega
      subst i
      norm_num [example510SecondPiece, example510SecondCut]
  · have hnotsucc : ¬i + 1 ≤ 1 := by omega
    rw [example510SecondPiece, if_neg hi1,
      example510SecondPiece, if_neg hnotsucc]
    simp only [example510SecondCut, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    push_cast
    ring

theorem example510SecondPiece_exact :
    ∃ i, (example510SecondPiece i).natDegree = 1 := by
  refine ⟨2, ?_⟩
  rw [example510SecondPiece, if_neg (by norm_num)]
  convert Polynomial.natDegree_X_sub_C (2 : ℝ) using 1 <;> norm_num

/-- The second piecewise-linear entire candidate from Example 5.10. -/
def example510Second : NthTropicalMeromorphicFunction 1 :=
  assembleNthTropicalMeromorphicFunction example510SecondGrid
    example510SecondPiece example510SecondPiece_degree
    example510SecondPiece_adjacent example510SecondPiece_exact

theorem example510Second_eq_piece (i : ℤ) {x : ℝ}
    (hx : x ∈ Icc (example510SecondCut (i - 1)) (example510SecondCut i)) :
    example510Second x = (example510SecondPiece i).eval x := by
  exact assembledFunction_eq_piece example510SecondGrid example510SecondPiece
    example510SecondPiece_adjacent i hx

@[simp] theorem example510SecondCut_nat (k : ℕ) :
    example510SecondCut (k : ℤ) = ((2 * k : ℕ) : ℝ) := by
  simp [example510SecondCut]

theorem example510Second_zero {x : ℝ} (hx : x ≤ 2) :
    example510Second x = 0 := by
  let i := presentationIntervalIndex example510SecondGrid x
  have hmem := presentationIntervalIndex_mem example510SecondGrid x
  have hi : i ≤ 1 := by
    by_contra hnot
    have hcut : example510SecondCut 1 ≤ example510SecondCut (i - 1) :=
      example510SecondCut_strictMono.monotone (by omega)
    have hlower : example510SecondCut (i - 1) < x := hmem.1
    have htwo : example510SecondCut 1 = 2 := by norm_num [example510SecondCut]
    rw [htwo] at hcut
    linarith [hlower]
  rw [example510Second_eq_piece i ⟨hmem.1.le, hmem.2⟩]
  simp [example510SecondPiece, hi]

theorem example510Second_piece (k : ℕ) (hk : 1 ≤ k) {x : ℝ}
    (hx : x ∈ Ico ((2 * k : ℕ) : ℝ) ((2 * k + 2 : ℕ) : ℝ)) :
    example510Second x =
      (2 * k : ℕ) * x - (2 * k * (k + 1) : ℕ) := by
  let i : ℤ := (k : ℤ) + 1
  have hleft : example510SecondCut (i - 1) = ((2 * k : ℕ) : ℝ) := by
    simpa [i] using example510SecondCut_nat k
  have hright : example510SecondCut i = ((2 * k + 2 : ℕ) : ℝ) := by
    rw [show i = ((k + 1 : ℕ) : ℤ) by simp [i]]
    rw [example510SecondCut_nat (k + 1)]
    congr 1
  rw [example510Second_eq_piece i (by simpa [hleft, hright] using
    (show x ∈ Icc ((2 * k : ℕ) : ℝ) ((2 * k + 2 : ℕ) : ℝ) from
      ⟨hx.1, le_of_lt hx.2⟩))]
  rw [example510SecondPiece, if_neg (by dsimp [i]; omega)]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  norm_num [i]

theorem example510Second_cut_multiplicity_nonneg (i : ℤ) :
    0 ≤ presentationMultiplicityAtCutPoint
      (assembledPolynomialPresentation example510SecondGrid
        example510SecondPiece example510SecondPiece_degree
        example510SecondPiece_adjacent example510SecondPiece_exact) 1 i := by
  by_cases hi : i ≤ 0
  · have hiPiece : i ≤ 1 := by omega
    have hnextPiece : i + 1 ≤ 1 := by omega
    simp [presentationMultiplicityAtCutPoint, assembledPolynomialPresentation,
      example510SecondPiece,
      hiPiece, hnextPiece, normalizedPolynomialJet]
  · have hipos : 0 < i := lt_of_not_ge hi
    rw [presentationMultiplicityAtCutPoint_of_pos_index _ 1 hipos]
    by_cases hi1 : i ≤ 1
    · have hieq : i = 1 := by omega
      subst i
      norm_num [assembledPolynomialPresentation, example510SecondPiece,
        normalizedPolynomialJet]
    · have hnex : ¬i + 1 ≤ 1 := by omega
      simp [assembledPolynomialPresentation, example510SecondPiece,
        hi1, hnex, normalizedPolynomialJet]

theorem example510Second_entire : IsTropicalEntire example510Second := by
  rw [isTropicalEntire_iff_multiplicity_nonneg]
  intro x j hj hj1
  have hjeq : j = 1 := by omega
  subst j
  let P := assembledPolynomialPresentation example510SecondGrid
    example510SecondPiece example510SecondPiece_degree
    example510SecondPiece_adjacent example510SecondPiece_exact
  rcases multiplicity_eq_zero_or_cutPoint_of_presentation
      example510Second P 1 x with hzero | ⟨i, _hxi, hcut⟩
  · rw [hzero]
  · rw [hcut]
    exact example510Second_cut_multiplicity_nonneg i

theorem example510Second_nonneg (x : ℝ) : 0 ≤ example510Second x := by
  let i := presentationIntervalIndex example510SecondGrid x
  have hmem := presentationIntervalIndex_mem example510SecondGrid x
  rw [example510Second_eq_piece i ⟨hmem.1.le, hmem.2⟩]
  by_cases hi : i ≤ 1
  · simp [example510SecondPiece, hi]
  · have hcut : example510SecondCut (i - 1) = ((2 * (i - 1) : ℤ) : ℝ) := rfl
    rw [example510SecondPiece, if_neg hi]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    have hlower := hmem.1.le
    change example510SecondCut (i - 1) ≤ x at hlower
    rw [hcut] at hlower
    push_cast at hlower ⊢
    have hiReal : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show (2 : ℤ) ≤ i by omega)
    have ht : 1 ≤ (i : ℝ) - 1 := by linarith
    have hcoef : 0 ≤ 2 * ((i : ℝ) - 1) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hlower hcoef
    nlinarith [hmul, mul_nonneg (by linarith : 0 ≤ (i : ℝ) - 1)
      (by linarith : 0 ≤ (i : ℝ) - 2)]

def example510G : TropicalHolomorphicCurveRepresentation 1 1 where
  order i := if i = 0 then 0 else 1
  order_le := by intro i; split_ifs <;> omega
  order_attained := ⟨1, by simp⟩
  coordinate i := by
    by_cases hi : i = 0
    · subst i
      simpa using example59Zero
    · have hi1 : i = 1 := by fin_cases i <;> simp_all
      subst i
      simpa using example510First
  coordinate_multiplicity_nonneg := by
    intro i x j hj hj1
    by_cases hi : i = 0
    · subst i
      change 0 ≤ multiplicity example59Zero j x
      rw [example59Zero_multiplicity_eq_zero]
    · have hi1 : i = 1 := by fin_cases i <;> simp_all
      subst i
      change 0 ≤ multiplicity example510First j x
      exact (isTropicalEntire_iff_multiplicity_nonneg example510First).mp
        example510First_entire x j hj hj1

@[simp] theorem example510G_eval_zero (x : ℝ) : example510G.eval 0 x = 0 := by
  simp [example510G, TropicalHolomorphicCurveRepresentation.eval]

@[simp] theorem example510G_eval_one (x : ℝ) :
    example510G.eval 1 x = example510First x := by
  simp [example510G, TropicalHolomorphicCurveRepresentation.eval]

def example510H : TropicalHolomorphicCurveRepresentation 1 1 where
  order _ := 1
  order_le := by simp
  order_attained := ⟨0, rfl⟩
  coordinate i := if i = 0 then example510First else example510Second
  coordinate_multiplicity_nonneg := by
    intro i x j hj hj1
    by_cases hi : i = 0
    · subst i
      change 0 ≤ multiplicity example510First j x
      exact (isTropicalEntire_iff_multiplicity_nonneg example510First).mp
        example510First_entire x j hj hj1
    · have hi1 : i = 1 := by fin_cases i <;> simp_all
      subst i
      change 0 ≤ multiplicity example510Second j x
      exact (isTropicalEntire_iff_multiplicity_nonneg example510Second).mp
        example510Second_entire x j hj hj1

@[simp] theorem example510H_eval_zero (x : ℝ) :
    example510H.eval 0 x = example510First x := by
  simp [example510H, TropicalHolomorphicCurveRepresentation.eval]

@[simp] theorem example510H_eval_one (x : ℝ) :
    example510H.eval 1 x = example510Second x := by
  simp [example510H, TropicalHolomorphicCurveRepresentation.eval]

def example510SumRealization :
    NthTropicalMeromorphicRealization 1
      (fun x ↦ example510First x + example510Second x) :=
  (show NthTropicalMeromorphicRealization 1 example510First from
    { order := 1, order_le := le_rfl, function := example510First,
      eq_fun := fun _ ↦ rfl }).add
  (show NthTropicalMeromorphicRealization 1 example510Second from
    { order := 1, order_le := le_rfl, function := example510Second,
      eq_fun := fun _ ↦ rfl })

/-- A realization of the two infinite piecewise-linear functions and the
three functions/curve representations used in Example 5.10.  The first four
fields are the paper's displayed definitions, with the interval quantifiers
made explicit. -/
structure Example510Realization where
  first : NthTropicalMeromorphicFunction 1
  second : NthTropicalMeromorphicFunction 1
  first_zero : ∀ x, x ≤ 1 → first x = 0
  first_piece : ∀ (k : ℕ), 1 ≤ k → ∀ x,
    x ∈ Ico ((2 * k - 1 : ℕ) : ℝ) ((2 * k + 1 : ℕ) : ℝ) →
      first x = (2 * k - 1 : ℕ) * x - (2 * k ^ 2 - 1 : ℕ)
  second_zero : ∀ x, x ≤ 2 → second x = 0
  second_piece : ∀ (k : ℕ), 1 ≤ k → ∀ x,
    x ∈ Ico ((2 * k : ℕ) : ℝ) ((2 * k + 2 : ℕ) : ℝ) →
      second x = (2 * k : ℕ) * x - (2 * k * (k + 1) : ℕ)
  first_nonneg : ∀ x, 0 ≤ first x
  second_nonneg : ∀ x, 0 ≤ second x
  first_entire : IsTropicalEntire first
  second_entire : IsTropicalEntire second
  g : TropicalHolomorphicCurveRepresentation 1 1
  g_eval_zero : ∀ x, g.eval 0 x = 0
  g_eval_one : ∀ x, g.eval 1 x = first x
  h : TropicalHolomorphicCurveRepresentation 1 1
  h_eval_zero : ∀ x, h.eval 0 x = first x
  h_eval_one : ∀ x, h.eval 1 x = second x
  sumOrder : ℕ
  sumOrder_le : sumOrder ≤ 1
  sum : NthTropicalMeromorphicFunction sumOrder
  sum_eq : ∀ x, sum x = first x + second x

/-- The paper's displayed data, now constructed rather than assumed.  The
ordinary sum carries its automatically detected exact order (bounded by one),
so no artificial exact-degree assertion is inserted. -/
def example510Realization : Example510Realization where
  first := example510First
  second := example510Second
  first_zero := fun _ hx ↦ example510First_zero hx
  first_piece := fun k hk _ hx ↦ example510First_piece k hk hx
  second_zero := fun _ hx ↦ example510Second_zero hx
  second_piece := fun k hk _ hx ↦ example510Second_piece k hk hx
  first_nonneg := example510First_nonneg
  second_nonneg := example510Second_nonneg
  first_entire := example510First_entire
  second_entire := example510Second_entire
  g := example510G
  g_eval_zero := example510G_eval_zero
  g_eval_one := example510G_eval_one
  h := example510H
  h_eval_zero := example510H_eval_zero
  h_eval_one := example510H_eval_one
  sumOrder := example510SumRealization.order
  sumOrder_le := example510SumRealization.order_le
  sum := example510SumRealization.function
  sum_eq := example510SumRealization.eq_fun

/-- `A(r)=c r²+o(r²)` in a literal Landau formulation. -/
def HasQuadraticAsymptotic (A : ℝ → ℝ) (c : ℝ) : Prop :=
  (fun r ↦ A r - c * r ^ 2) =o[atTop] fun r : ℝ ↦ r ^ 2

theorem example510First_quadraticError_isBigO :
    (fun r ↦ example510First r - (1 / 2 : ℝ) * r ^ 2) =O[atTop]
      fun r : ℝ ↦ r := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨3, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  let i := presentationIntervalIndex example510FirstGrid r
  let t : ℝ := (i : ℝ) - 1
  have hmem := presentationIntervalIndex_mem example510FirstGrid r
  have hi : 1 < i := by
    by_contra hnot
    have hile : i ≤ 1 := le_of_not_gt hnot
    have hcut : example510FirstCut i ≤ example510FirstCut 1 :=
      example510FirstCut_strictMono.monotone hile
    have hu := hmem.2
    change r ≤ example510FirstCut i at hu
    have hone : example510FirstCut 1 = 1 := by norm_num [example510FirstCut]
    rw [hone] at hcut
    linarith [hu]
  have hleftCut : example510FirstCut (i - 1) = 2 * t - 1 := by
    rw [example510FirstCut, if_neg (by omega)]
    dsimp [t]
    push_cast
    ring
  have hrightCut : example510FirstCut i = 2 * t + 1 := by
    rw [example510FirstCut, if_neg (by omega)]
    dsimp [t]
    push_cast
    ring
  have hlower : 2 * t - 1 < r := by
    have hm : example510FirstCut (i - 1) < r := hmem.1
    rw [hleftCut] at hm
    exact hm
  have hupper : r ≤ 2 * t + 1 := by
    have hm : r ≤ example510FirstCut i := hmem.2
    rw [hrightCut] at hm
    exact hm
  have ht : 1 ≤ t := by
    dsimp [t]
    have hit : (1 : ℤ) ≤ i - 1 := by omega
    exact_mod_cast hit
  have hvalue := example510First_eq_piece i ⟨hmem.1.le, hmem.2⟩
  rw [example510FirstPiece, if_neg (by omega)] at hvalue
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at hvalue
  have hvalue' : example510First r = (2 * t - 1) * r - (2 * t ^ 2 - 1) := by
    rw [hvalue]
    dsimp [t]
    push_cast
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hvalue']
  have hrabs : |r| = r := abs_of_pos (by linarith)
  rw [hrabs]
  have hdiff : (2 * t - 1) * r - (2 * t ^ 2 - 1) -
      (1 / 2 : ℝ) * r ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg (r - (2 * t - 1))]
  rw [abs_of_nonpos hdiff]
  have hsquare : (r - (2 * t - 1)) ^ 2 ≤ 4 := by nlinarith
  nlinarith

theorem example510Second_quadraticError_isBigO :
    (fun r ↦ example510Second r - (1 / 2 : ℝ) * r ^ 2) =O[atTop]
      fun r : ℝ ↦ r := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨3, ?_⟩
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with r hr
  let i := presentationIntervalIndex example510SecondGrid r
  let t : ℝ := (i : ℝ) - 1
  have hmem := presentationIntervalIndex_mem example510SecondGrid r
  have hi : 1 < i := by
    by_contra hnot
    have hile : i ≤ 1 := le_of_not_gt hnot
    have hcut : example510SecondCut i ≤ example510SecondCut 1 :=
      example510SecondCut_strictMono.monotone hile
    have hu := hmem.2
    change r ≤ example510SecondCut i at hu
    have htwo : example510SecondCut 1 = 2 := by norm_num [example510SecondCut]
    rw [htwo] at hcut
    linarith [hu]
  have hleftCut : example510SecondCut (i - 1) = 2 * t := by
    dsimp [example510SecondCut, t]
    push_cast
    ring
  have hrightCut : example510SecondCut i = 2 * t + 2 := by
    dsimp [example510SecondCut, t]
    push_cast
    ring
  have hlower : 2 * t < r := by
    have hm : example510SecondCut (i - 1) < r := hmem.1
    rw [hleftCut] at hm
    exact hm
  have hupper : r ≤ 2 * t + 2 := by
    have hm : r ≤ example510SecondCut i := hmem.2
    rw [hrightCut] at hm
    exact hm
  have ht : 1 ≤ t := by
    dsimp [t]
    have hit : (1 : ℤ) ≤ i - 1 := by omega
    exact_mod_cast hit
  have hvalue := example510Second_eq_piece i ⟨hmem.1.le, hmem.2⟩
  rw [example510SecondPiece, if_neg (by omega)] at hvalue
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at hvalue
  have hvalue' : example510Second r = 2 * t * r - 2 * t * (t + 1) := by
    rw [hvalue]
    dsimp [t]
    push_cast
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hvalue']
  have hrabs : |r| = r := abs_of_pos (by linarith)
  rw [hrabs]
  have hdiff : 2 * t * r - 2 * t * (t + 1) -
      (1 / 2 : ℝ) * r ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg (r - 2 * t)]
  rw [abs_of_nonpos hdiff]
  have hsquare : (r - 2 * t) ^ 2 ≤ 4 := by nlinarith
  nlinarith

theorem example510First_quadratic :
    HasQuadraticAsymptotic example510First (1 / 2) := by
  have hpow : (fun r : ℝ ↦ r) =o[atTop] fun r : ℝ ↦ r ^ 2 := by
    simpa using (Asymptotics.isLittleO_pow_pow_atTop_of_lt
      (𝕜 := ℝ) (p := 1) (q := 2) (by omega))
  exact example510First_quadraticError_isBigO.trans_isLittleO hpow

theorem example510Second_quadratic :
    HasQuadraticAsymptotic example510Second (1 / 2) := by
  have hpow : (fun r : ℝ ↦ r) =o[atTop] fun r : ℝ ↦ r ^ 2 := by
    simpa using (Asymptotics.isLittleO_pow_pow_atTop_of_lt
      (𝕜 := ℝ) (p := 1) (q := 2) (by omega))
  exact example510Second_quadraticError_isBigO.trans_isLittleO hpow

theorem abs_max_le_add_abs (a b : ℝ) : |max a b| ≤ |a| + |b| := by
  rw [abs_le]
  constructor
  · calc
      -(|a| + |b|) ≤ a := by linarith [neg_abs_le a, abs_nonneg b]
      _ ≤ max a b := le_max_left _ _
  · apply max_le
    · linarith [le_abs_self a, abs_nonneg b]
    · linarith [le_abs_self b, abs_nonneg a]

theorem example510Maximum_quadraticError_isBigO :
    (fun r ↦ max (example510First r) (example510Second r) -
        (1 / 2 : ℝ) * r ^ 2) =O[atTop] fun r : ℝ ↦ r := by
  have hfirst := example510First_quadraticError_isBigO
  have hsecond := example510Second_quadraticError_isBigO
  rw [Asymptotics.isBigO_iff] at hfirst hsecond ⊢
  rcases hfirst with ⟨c₁, h₁⟩
  rcases hsecond with ⟨c₂, h₂⟩
  refine ⟨c₁ + c₂, ?_⟩
  filter_upwards [h₁, h₂] with r hr₁ hr₂
  have hrewrite : max (example510First r) (example510Second r) -
      (1 / 2 : ℝ) * r ^ 2 =
      max (example510First r - (1 / 2 : ℝ) * r ^ 2)
        (example510Second r - (1 / 2 : ℝ) * r ^ 2) := by
    rw [max_sub_sub_right]
  rw [hrewrite, Real.norm_eq_abs]
  calc
    |max (example510First r - (1 / 2 : ℝ) * r ^ 2)
        (example510Second r - (1 / 2 : ℝ) * r ^ 2)| ≤
        |example510First r - (1 / 2 : ℝ) * r ^ 2| +
          |example510Second r - (1 / 2 : ℝ) * r ^ 2| :=
      abs_max_le_add_abs _ _
    _ = ‖example510First r - (1 / 2 : ℝ) * r ^ 2‖ +
        ‖example510Second r - (1 / 2 : ℝ) * r ^ 2‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ c₁ * ‖r‖ + c₂ * ‖r‖ := add_le_add hr₁ hr₂
    _ = (c₁ + c₂) * ‖r‖ := by ring

theorem example510Maximum_quadratic :
    HasQuadraticAsymptotic
      (fun r ↦ max (example510First r) (example510Second r)) (1 / 2) := by
  have hpow : (fun r : ℝ ↦ r) =o[atTop] fun r : ℝ ↦ r ^ 2 := by
    simpa using (Asymptotics.isLittleO_pow_pow_atTop_of_lt
      (𝕜 := ℝ) (p := 1) (q := 2) (by omega))
  exact example510Maximum_quadraticError_isBigO.trans_isLittleO hpow

/-- The three elementary estimates omitted behind “easily get” in the paper.
The structure is retained as a reusable interface; the concrete value
`example510QuadraticEstimates` below constructs all three fields. -/
structure Example510QuadraticEstimates (D : Example510Realization) : Prop where
  first : HasQuadraticAsymptotic D.first (1 / 2)
  second : HasQuadraticAsymptotic D.second (1 / 2)
  maximum : HasQuadraticAsymptotic (fun r ↦ max (D.first r) (D.second r)) (1 / 2)

def example510QuadraticEstimates :
    Example510QuadraticEstimates example510Realization where
  first := example510First_quadratic
  second := example510Second_quadratic
  maximum := example510Maximum_quadratic

theorem Example510Realization.sum_entire (D : Example510Realization) :
    IsTropicalEntire D.sum := by
  rw [isTropicalEntire_iff_multiplicity_nonneg]
  intro x j hj hj1
  have hadd := multiplicity_eq_add_of_eq_add D.sum D.first D.second D.sum_eq j x
  by_cases hjle : j ≤ 1
  · have hfirst := (isTropicalEntire_iff_multiplicity_nonneg D.first).mp
      D.first_entire x j hj hjle
    have hsecond := (isTropicalEntire_iff_multiplicity_nonneg D.second).mp
      D.second_entire x j hj hjle
    linarith
  · have hfirst : multiplicity D.first j x = 0 :=
      multiplicity_eq_zero_of_order_lt D.first (by omega) x
    have hsecond : multiplicity D.second j x = 0 :=
      multiplicity_eq_zero_of_order_lt D.second (by omega) x
    linarith

theorem Example510Realization.g_maximum (D : Example510Realization) (x : ℝ) :
    curveCoordinateMaximum D.g x = D.first x := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rw [D.g_eval_zero]
      exact D.first_nonneg x
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hs : Fin.succ (0 : Fin 1) = (1 : Fin 2) := by decide
      rw [hs, D.g_eval_one]
  · rw [curveCoordinateMaximum]
    simpa only [D.g_eval_one] using
      (Finset.le_sup' (fun i : Fin 2 ↦ D.g.eval i x)
        (Finset.mem_univ (1 : Fin 2)))

theorem Example510Realization.h_maximum (D : Example510Realization) (x : ℝ) :
    curveCoordinateMaximum D.h x = max (D.first x) (D.second x) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rw [D.h_eval_zero]
      exact le_max_left _ _
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hs : Fin.succ (0 : Fin 1) = (1 : Fin 2) := by decide
      rw [hs, D.h_eval_one]
      exact le_max_right _ _
  · apply max_le
    · rw [curveCoordinateMaximum]
      simpa only [D.h_eval_zero] using
        (Finset.le_sup' (fun i : Fin 2 ↦ D.h.eval i x)
          (Finset.mem_univ (0 : Fin 2)))
    · rw [curveCoordinateMaximum]
      simpa only [D.h_eval_one] using
        (Finset.le_sup' (fun i : Fin 2 ↦ D.h.eval i x)
          (Finset.mem_univ (1 : Fin 2)))

theorem Example510Realization.g_characteristic (D : Example510Realization)
    {r : ℝ} (hr : 0 ≤ r) : cartanCharacteristic D.g r = D.first r / 2 := by
  rw [cartanCharacteristic, D.g_maximum, D.g_maximum, D.g_maximum,
    D.first_zero (-r) (by linarith), D.first_zero 0 (by norm_num)]
  ring

theorem Example510Realization.h_characteristic (D : Example510Realization)
    {r : ℝ} (hr : 0 ≤ r) :
    cartanCharacteristic D.h r = max (D.first r) (D.second r) / 2 := by
  rw [cartanCharacteristic, D.h_maximum, D.h_maximum, D.h_maximum,
    D.first_zero (-r) (by linarith), D.second_zero (-r) (by linarith),
    D.first_zero 0 (by norm_num), D.second_zero 0 (by norm_num)]
  norm_num

theorem Example510Realization.first_reciprocalCounting (D : Example510Realization)
    {r : ℝ} (hr : 0 < r) :
    ambientReciprocalCounting 1 r D.first = D.first r / 2 := by
  have hsigned := ambientSignedCountingDifference_eq_endpointMean_sub
    D.first (show 1 ≤ 1 by rfl) hr
  have hpole := integratedCounting_eq_zero_of_entire_any_order
    D.first D.first_entire (j := 1) (by omega) r
  have hpoles : ambientPoleCounting 1 r D.first = 0 := by
    unfold ambientPoleCounting
    norm_num [show Finset.Icc 1 1 = {1} by decide, hpole]
  change ambientReciprocalCounting 1 r D.first - ambientPoleCounting 1 r D.first =
    (D.first r + D.first (-r)) / 2 - D.first 0 at hsigned
  rw [hpoles, D.first_zero (-r) (by linarith),
    D.first_zero 0 (by norm_num)] at hsigned
  linarith

theorem Example510Realization.first_reciprocalCounting_eq_g_characteristic
    (D : Example510Realization) {r : ℝ} (hr : 0 < r) :
    ambientReciprocalCounting 1 r D.first = cartanCharacteristic D.g r := by
  rw [D.first_reciprocalCounting hr, D.g_characteristic hr.le]

theorem Example510Realization.sum_reciprocalCounting (D : Example510Realization)
    {r : ℝ} (hr : 0 < r) :
    ambientReciprocalCounting 1 r D.sum = (D.first r + D.second r) / 2 := by
  have hsigned := ambientSignedCountingDifference_eq_endpointMean_sub
    D.sum D.sumOrder_le hr
  have hpole := integratedCounting_eq_zero_of_entire_any_order
    D.sum D.sum_entire (j := 1) (by omega) r
  have hneg : D.sum (-r) = 0 := by
    rw [D.sum_eq, D.first_zero (-r) (by linarith),
      D.second_zero (-r) (by linarith)]
    ring
  have hzero : D.sum 0 = 0 := by
    rw [D.sum_eq, D.first_zero 0 (by norm_num), D.second_zero 0 (by norm_num)]
    ring
  have hpoles : ambientPoleCounting 1 r D.sum = 0 := by
    unfold ambientPoleCounting
    norm_num [show Finset.Icc 1 1 = {1} by decide, hpole]
  change ambientReciprocalCounting 1 r D.sum - ambientPoleCounting 1 r D.sum =
    (D.sum r + D.sum (-r)) / 2 - D.sum 0 at hsigned
  rw [hpoles, hneg, hzero, D.sum_eq] at hsigned
  linarith

theorem Example510Realization.sum_proximity (D : Example510Realization)
    {r : ℝ} (hr : 0 < r) :
    proximity r D.sum = (D.first r + D.second r) / 2 := by
  have hnonneg : 0 ≤ D.sum r := by
    rw [D.sum_eq]
    exact add_nonneg (D.first_nonneg r) (D.second_nonneg r)
  have hneg : D.sum (-r) = 0 := by
    rw [D.sum_eq, D.first_zero (-r) (by linarith),
      D.second_zero (-r) (by linarith)]
    ring
  rw [proximity, maxPlusPositivePart, max_eq_left hnonneg, hneg, D.sum_eq]
  simp [maxPlusPositivePart]

theorem Example510Realization.sum_characteristic_eq_proximity
    (D : Example510Realization) (r : ℝ) :
    characteristic r D.sum = proximity r D.sum := by
  unfold characteristic
  have hsum : (∑ j ∈ Finset.Icc 1 D.sumOrder,
      integratedCounting j r D.sum) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact integratedCounting_eq_zero_of_entire_any_order
      D.sum D.sum_entire (Finset.mem_Icc.mp hj).1 r
  rw [hsum, add_zero]

/-- The paper's chain
`N(r,1/(f₁+f₂)) = T(r,f₁+f₂) = m(r,f₁+f₂)` is exact for this normalized
realization; in particular the stated `O(1)` errors may be taken to be zero. -/
theorem Example510Realization.sum_reciprocalCounting_eq_characteristic_eq_proximity
    (D : Example510Realization) {r : ℝ} (hr : 0 < r) :
    ambientReciprocalCounting 1 r D.sum = characteristic r D.sum ∧
      characteristic r D.sum = proximity r D.sum := by
  refine ⟨?_, D.sum_characteristic_eq_proximity r⟩
  rw [D.sum_reciprocalCounting hr, D.sum_characteristic_eq_proximity,
    D.sum_proximity hr]

/-- Formal conclusion and derivation of Example 5.10.  The first pair gives
the sharp lower coefficient `1/4`; the second pair gives `T_h~r²/4` while the
ordinary-sum reciprocal count is `~r²/2`, hence the sharp upper coefficient. -/
theorem example510_conclusions (D : Example510Realization)
    (E : Example510QuadraticEstimates D) :
    HasQuadraticAsymptotic (fun r ↦ cartanCharacteristic D.g r) (1 / 4) ∧
    HasQuadraticAsymptotic (fun r ↦ ambientReciprocalCounting 1 r D.first) (1 / 4) ∧
    HasQuadraticAsymptotic (fun r ↦ cartanCharacteristic D.h r) (1 / 4) ∧
    HasQuadraticAsymptotic (fun r ↦ ambientReciprocalCounting 1 r D.sum) (1 / 2) := by
  have hfirstHalf := E.first.const_mul_left (1 / 2 : ℝ)
  have hmaxHalf := E.maximum.const_mul_left (1 / 2 : ℝ)
  have hsumHalf := (E.first.add E.second).const_mul_left (1 / 2 : ℝ)
  constructor
  · apply hfirstHalf.congr'
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
      rw [D.g_characteristic hr]
      ring
    · exact EventuallyEq.rfl
  constructor
  · apply hfirstHalf.congr'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      rw [D.first_reciprocalCounting hr]
      ring
    · exact EventuallyEq.rfl
  constructor
  · apply hmaxHalf.congr'
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
      rw [D.h_characteristic hr]
      ring
    · exact EventuallyEq.rfl
  · apply hsumHalf.congr'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      rw [D.sum_reciprocalCounting hr]
      ring
    · exact EventuallyEq.rfl

/-- Unconditional, fully constructed version of Example 5.10. -/
theorem example510_concrete_conclusions :
    HasQuadraticAsymptotic
        (fun r ↦ cartanCharacteristic example510Realization.g r) (1 / 4) ∧
    HasQuadraticAsymptotic
        (fun r ↦ ambientReciprocalCounting 1 r example510Realization.first) (1 / 4) ∧
    HasQuadraticAsymptotic
        (fun r ↦ cartanCharacteristic example510Realization.h r) (1 / 4) ∧
    HasQuadraticAsymptotic
        (fun r ↦ ambientReciprocalCounting 1 r example510Realization.sum) (1 / 2) :=
  example510_conclusions example510Realization example510QuadraticEstimates

end

end NthTropicalNevanlinna
