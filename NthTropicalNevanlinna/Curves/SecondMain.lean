import NthTropicalNevanlinna.Curves.HomogeneousPolynomial

/-!
# The tropical second main theorem for a homogeneous polynomial

The paper's `O(1)` is represented by a single uniform absolute-error bound
on all positive radii.  The proof below exposes the stronger constant
`(β - γ) / d`.
-/

namespace NthTropicalNevanlinna

noncomputable section

open scoped BigOperators

/-- `A(r) = B(r) + O(1)` on positive radii, expressed without asymptotic
notation: one nonnegative constant bounds the absolute difference uniformly. -/
def IsEqUpToConstantOnPositiveRadii (A B : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ r, 0 < r → |A r - B r| ≤ C

/-- The signed counting term appearing in Theorem 5.6. -/
def ambientSignedCountingDifference {k : ℕ} (upTo : ℕ) (r : ℝ)
    (h : NthTropicalMeromorphicFunction k) : ℝ :=
  (∑ j ∈ Finset.Icc 1 upTo, integratedCounting j r (-h)) -
    ∑ j ∈ Finset.Icc 1 upTo, integratedCounting j r h

/-- Jensen's formula identifies the ambient signed count with the centered
endpoint mean.  Terms above the exact order of `h` vanish. -/
theorem ambientSignedCountingDifference_eq_endpointMean_sub
    {k upTo : ℕ} (h : NthTropicalMeromorphicFunction k)
    (hku : k ≤ upTo) {r : ℝ} (hr : 0 < r) :
    ambientSignedCountingDifference upTo r h =
      (h r + h (-r)) / 2 - h 0 := by
  have hroots := sum_integratedRootCounting_eq_of_order_le h hku r
  have hpoles := sum_integratedRootCounting_eq_of_order_le (-h) hku r
  simp only [integratedRootCounting_neg] at hpoles
  have hjensen := jensenFormula h hr
  rw [jensenRootMultiplicitySum_eq h hr,
    jensenPoleMultiplicitySum_eq h hr] at hjensen
  simp only [ambientSignedCountingDifference, integratedCounting_neg]
  rw [hroots, hpoles]
  linarith

/-- A pole count is zero either by entirety (within the exact order) or by
the automatic vanishing of multiplicities above that order. -/
theorem integratedCounting_eq_zero_of_entire_any_order
    {k : ℕ} (h : NthTropicalMeromorphicFunction k)
    (hEntire : IsTropicalEntire h) {j : ℕ} (hj : 1 ≤ j) (r : ℝ) :
    integratedCounting j r h = 0 := by
  by_cases hjk : j ≤ k
  · exact integratedCounting_eq_zero_of_entire h hEntire hj hjk r
  · rw [← integratedRootCounting_neg]
    exact integratedRootCounting_eq_zero_of_order_lt (-h)
      (lt_of_not_ge hjk) r

/-- The common analytic core of Theorem 5.6 and Corollary 5.7.  A function
lying between `γ + d max_i f_i` and `β + d max_i f_i` satisfies the desired
second-main identity, with explicit error at most `(β-γ)/d`. -/
theorem cartan_eq_scaled_signedCounting_upToConstant_of_degreeBounds
    {n m k d : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (h : NthTropicalMeromorphicFunction k) (hkn : k ≤ n)
    (hd : 0 < d) (γ β : ℝ) (hγβ : γ ≤ β)
    (hlower : ∀ x, γ + d * curveCoordinateMaximum F x ≤ h x)
    (hupper : ∀ x, h x ≤ β + d * curveCoordinateMaximum F x) :
    IsEqUpToConstantOnPositiveRadii
      (fun r ↦ cartanCharacteristic F r)
      (fun r ↦ (1 / (d : ℝ)) * ambientSignedCountingDifference n r h) := by
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine ⟨(β - γ) / (d : ℝ), div_nonneg (sub_nonneg.mpr hγβ) hdReal.le,
    fun r hr ↦ ?_⟩
  have hsigned :=
    ambientSignedCountingDifference_eq_endpointMean_sub h hkn hr
  have hinterval :
      |(d : ℝ) * cartanCharacteristic F r -
          ambientSignedCountingDifference n r h| ≤ β - γ := by
    rw [hsigned, cartanCharacteristic]
    apply abs_le.mpr
    constructor <;>
      linarith [hlower r, hlower (-r), hlower 0,
        hupper r, hupper (-r), hupper 0]
  have hrearrange :
      cartanCharacteristic F r -
          (1 / (d : ℝ)) * ambientSignedCountingDifference n r h =
        ((d : ℝ) * cartanCharacteristic F r -
          ambientSignedCountingDifference n r h) / (d : ℝ) := by
    field_simp [ne_of_gt hdReal]
  rw [hrearrange, abs_div, abs_of_pos hdReal]
  exact (div_le_div_iff_of_pos_right hdReal).mpr hinterval

/-- Theorem 5.6: the `n`-th tropical second main theorem for a degree-`d`
homogeneous tropical polynomial containing every pure power with a finite
coefficient.  Reducedness and nonconstancy reproduce the paper's quantifiers;
the numerical estimate itself only uses the displayed degree bounds.

The composition realization is constructed automatically by the finite-sum
and finite-maximum closure theorem. -/
theorem secondMain_homogeneousTropicalPolynomial
    {n m d : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (_hFReduced : F.IsReduced) (_hFNonconstant : F.IsNonconstant)
    (P : HomogeneousTropicalPolynomial m d) (hPure : P.HasAllPurePowers)
    (hd : 0 < d) :
    IsEqUpToConstantOnPositiveRadii
      (fun r ↦ cartanCharacteristic F r)
      (fun r ↦ (1 / (d : ℝ)) *
        ambientSignedCountingDifference n r (P.curveComposition F).function) := by
  let C := P.curveComposition F
  apply cartan_eq_scaled_signedCounting_upToConstant_of_degreeBounds
    F C.function C.order_le hd
    P.pureCoefficientMinimum P.coefficientMaximum
    (P.pureCoefficientMinimum_le_coefficientMaximum hPure)
  · intro x
    simpa [HomogeneousTropicalPolynomial.composeRaw, C.eq_composeRaw x] using
      P.pureCoefficientMinimum_add_degree_mul_le_eval hPure F x
  · intro x
    simpa [HomogeneousTropicalPolynomial.composeRaw, C.eq_composeRaw x] using
      P.eval_le_coefficientMaximum_add_degree_mul F x

/-- Corollary 5.7: for a first-order curve and a tropical homogeneous Fermat
polynomial, the pole-counting term of the composition vanishes. -/
theorem secondMain_firstOrder_tropicalFermat
    {m d : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m)
    (_hFReduced : F.IsReduced)
    (P : TropicalHomogeneousFermatPolynomial m d) (hd : 0 < d) :
    IsEqUpToConstantOnPositiveRadii
      (fun r ↦ cartanCharacteristic F r)
      (fun r ↦ (1 / (d : ℝ)) * integratedCounting 1 r
        (-(P.firstOrderCurveComposition F).function)) := by
  let C := P.firstOrderCurveComposition F
  have hgeneral :=
    cartan_eq_scaled_signedCounting_upToConstant_of_degreeBounds
      F C.function C.order_le hd
      P.coefficientMinimum P.coefficientMaximum
      P.coefficientMinimum_le_coefficientMaximum
      (fun x ↦ by
        simpa [TropicalHomogeneousFermatPolynomial.composeRaw,
          C.eq_composeRaw x] using
          P.coefficientMinimum_add_degree_mul_le_eval F x)
      (fun x ↦ by
        simpa [TropicalHomogeneousFermatPolynomial.composeRaw,
          C.eq_composeRaw x] using
          P.eval_le_coefficientMaximum_add_degree_mul F x)
  have hpole (r : ℝ) : integratedCounting 1 r C.function = 0 :=
    integratedCounting_eq_zero_of_entire_any_order
      C.function C.function_entire (by simp) r
  simpa [ambientSignedCountingDifference, hpole] using hgeneral

end

end NthTropicalNevanlinna
