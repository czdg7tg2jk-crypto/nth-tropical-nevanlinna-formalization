import NthTropicalNevanlinna.PoissonJensen.Telescoping
import NthTropicalNevanlinna.PoissonJensen.AuxiliaryJumps
import NthTropicalNevanlinna.Function.IntervalRestriction

/-!
# The n-th tropical Poisson--Jensen formula

The proof uses two finite polynomial presentations, one on `[-r,x]` and one
on `[x,r]`.  Their internal cuts, together with the distinguished centre
`x`, form the finite point family used in the paper's proof.
-/

open Set

namespace NthTropicalNevanlinna

noncomputable section

open scoped BigOperators

/-- Internal cuts to the left of `x`, the distinguished point `x`, and
internal cuts to its right. -/
abbrev PoissonJensenPoint (mLeft mRight : ℕ) :=
  Sum (Fin mLeft) (Option (Fin mRight))

/-- The real point represented by a finite Poisson--Jensen index. -/
def poissonJensenPointValue
    {n mLeft mRight : ℕ} {f : NthTropicalMeromorphicFunction n} {r x : ℝ}
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r) :
    PoissonJensenPoint mLeft mRight → ℝ
  | .inl i => PLeft.internalCut i
  | .inr none => x
  | .inr (some i) => PRight.internalCut i

theorem poissonJensenPointValue_mem
    {n mLeft mRight : ℕ} {f : NthTropicalMeromorphicFunction n} {r x : ℝ}
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r)
    (hx : x ∈ Ioo (-r) r) (q : PoissonJensenPoint mLeft mRight) :
    poissonJensenPointValue PLeft PRight q ∈ Ioo (-r) r := by
  cases q with
  | inl i =>
      exact ⟨PLeft.leftEndpoint_lt_internalCut i,
        (PLeft.internalCut_lt_rightEndpoint i).trans hx.2⟩
  | inr q =>
      cases q with
      | none => exact hx
      | some i =>
          exact ⟨hx.1.trans (PRight.leftEndpoint_lt_internalCut i),
            PRight.internalCut_lt_rightEndpoint i⟩

/-- The unique one of `F₁,...,F₉` containing a finite Poisson--Jensen point. -/
def poissonJensenRegion
    {n mLeft mRight : ℕ} {f : NthTropicalMeromorphicFunction n} {r x : ℝ}
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r)
    (hx : x ∈ Ioo (-r) r) (q : PoissonJensenPoint mLeft mRight) : RelativeRegion :=
  Classical.choose
    (exists_relativeRegion (x := x) (poissonJensenPointValue_mem PLeft PRight hx q))

theorem poissonJensenPointValue_in_region
    {n mLeft mRight : ℕ} {f : NthTropicalMeromorphicFunction n} {r x : ℝ}
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r)
    (hx : x ∈ Ioo (-r) r) (q : PoissonJensenPoint mLeft mRight) :
    InRelativeRegion (poissonJensenRegion PLeft PRight hx q) r x
      (poissonJensenPointValue PLeft PRight q) :=
  Classical.choose_spec
    (exists_relativeRegion (x := x) (poissonJensenPointValue_mem PLeft PRight hx q))

private theorem right_kernel_factor {n j : ℕ} {r x y : ℝ}
    (hxy : x ≤ y) (hjn : j ≤ n) :
    (r - y) ^ j * (r + x) ^ n =
      interactionKernel r x y ^ j *
        (symmetricKernel (n - j) r x + antisymmetricKernel (n - j) r x) := by
  rw [interactionKernel_of_le hxy,
    symmetricKernel_add_antisymmetricKernel, mul_pow]
  have hn : (r + x) ^ n = (r + x) ^ j * (r + x) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjn]
  rw [hn]
  ring

private theorem left_kernel_factor {n j : ℕ} {r x y : ℝ}
    (hyx : y ≤ x) (hjn : j ≤ n) :
    (r + y) ^ j * (r - x) ^ n =
      interactionKernel r x y ^ j *
        (symmetricKernel (n - j) r x - antisymmetricKernel (n - j) r x) := by
  rw [interactionKernel_of_ge hyx,
    symmetricKernel_sub_antisymmetricKernel, mul_pow]
  have hn : (r - x) ^ n = (r - x) ^ j * (r - x) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjn]
  rw [hn]
  ring

private theorem center_auxiliary_identity
    {n j : ℕ} (f : NthTropicalMeromorphicFunction n) {r x : ℝ}
    (hjn : j ≤ n) :
    (normalizedRightJet f j x * (r - x) ^ j) * (r + x) ^ n -
        ((-1 : ℝ) ^ (j + 1) * normalizedLeftJet f j x * (r + x) ^ j) *
          (r - x) ^ n =
      auxiliaryOmega f j x x * interactionKernel r x x ^ j *
          symmetricKernel (n - j) r x +
        auxiliaryGamma f j x x * interactionKernel r x x ^ j *
          antisymmetricKernel (n - j) r x := by
  rw [auxiliaryOmega_diag, auxiliaryGamma_diag,
    interactionKernel_diag, symmetricKernel, antisymmetricKernel]
  have hrx : r ^ 2 - x ^ 2 = (r - x) * (r + x) := by ring
  rw [hrx, mul_pow]
  have hplus : (r + x) ^ n = (r + x) ^ j * (r + x) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjn]
  have hminus : (r - x) ^ n = (r - x) ^ j * (r - x) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjn]
  rw [hplus, hminus, pow_succ]
  ring

private theorem right_cut_auxiliary_identity
    {n j : ℕ} (f : NthTropicalMeromorphicFunction n) {r x y : ℝ}
    (hxy : x < y) (hjn : j ≤ n) :
    derivativeJump f j y * (r - y) ^ j * (r + x) ^ n =
      auxiliaryOmega f j x y * interactionKernel r x y ^ j *
          symmetricKernel (n - j) r x +
        auxiliaryGamma f j x y * interactionKernel r x y ^ j *
          antisymmetricKernel (n - j) r x := by
  rw [auxiliaryOmega_of_gt f j hxy, auxiliaryGamma_of_gt f j hxy]
  rw [← derivativeJump]
  have hfactor := right_kernel_factor (n := n) (r := r) (x := x) (y := y) hxy.le hjn
  calc
    derivativeJump f j y * (r - y) ^ j * (r + x) ^ n =
        derivativeJump f j y * ((r - y) ^ j * (r + x) ^ n) := by ring
    _ = derivativeJump f j y *
        (interactionKernel r x y ^ j *
          (symmetricKernel (n - j) r x + antisymmetricKernel (n - j) r x)) := by
      rw [hfactor]
    _ = _ := by ring

private theorem left_cut_auxiliary_identity
    {n j : ℕ} (f : NthTropicalMeromorphicFunction n) {r x y : ℝ}
    (hyx : y < x) (hjn : j ≤ n) :
    -((-1 : ℝ) ^ j * derivativeJump f j y * (r + y) ^ j) * (r - x) ^ n =
      auxiliaryOmega f j x y * interactionKernel r x y ^ j *
          symmetricKernel (n - j) r x +
        auxiliaryGamma f j x y * interactionKernel r x y ^ j *
          antisymmetricKernel (n - j) r x := by
  rw [auxiliaryOmega_of_lt f j hyx, auxiliaryGamma_of_lt f j hyx]
  rw [← derivativeJump, pow_succ]
  have hfactor := left_kernel_factor (n := n) (r := r) (x := x) (y := y) hyx.le hjn
  calc
    -((-1) ^ j * derivativeJump f j y * (r + y) ^ j) * (r - x) ^ n =
        -((-1) ^ j * derivativeJump f j y) *
          ((r + y) ^ j * (r - x) ^ n) := by ring
    _ = -((-1) ^ j * derivativeJump f j y) *
        (interactionKernel r x y ^ j *
          (symmetricKernel (n - j) r x - antisymmetricKernel (n - j) r x)) := by
      rw [hfactor]
    _ = _ := by ring

/-- The weighted endpoint difference obtained directly from Lemma 3.1. -/
theorem weightedEndpointDifference_eq_auxiliarySum
    {n mLeft mRight : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hx : x ∈ Ioo (-r) r)
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r) :
    (f r - f x) * (r + x) ^ n - (f x - f (-r)) * (r - x) ^ n =
      ∑ j ∈ Finset.Icc 1 n, ∑ q : PoissonJensenPoint mLeft mRight,
        (auxiliaryOmega f j x (poissonJensenPointValue PLeft PRight q) *
            interactionKernel r x (poissonJensenPointValue PLeft PRight q) ^ j *
              symmetricKernel (n - j) r x +
          auxiliaryGamma f j x (poissonJensenPointValue PLeft PRight q) *
            interactionKernel r x (poissonJensenPointValue PLeft PRight q) ^ j *
              antisymmetricKernel (n - j) r x) := by
  have hRight := endpoint_sub_eq_jet_sum PRight
  have hLeft := sub_leftEndpoint_eq_jet_sum PLeft
  rw [PRight.firstPiece_eq_intrinsicRight] at hRight
  rw [PLeft.lastPiece_eq_intrinsicLeft] at hLeft
  have hRight' : f r - f x =
      ∑ j ∈ Finset.Icc 1 n,
        (normalizedRightJet f j x * (r - x) ^ j +
          ∑ i : Fin mRight,
            PRight.derivativeJumpAt j i * (r - PRight.internalCut i) ^ j) := by
    simpa only [normalizedRightJet] using hRight
  have hLeft' : f x - f (-r) =
      ∑ j ∈ Finset.Icc 1 n,
        ((-1 : ℝ) ^ (j + 1) * normalizedLeftJet f j x * (x - -r) ^ j +
          (-1 : ℝ) ^ j * ∑ i : Fin mLeft,
            PLeft.derivativeJumpAt j i * (PLeft.internalCut i - -r) ^ j) := by
    simpa only [normalizedLeftJet] using hLeft
  simp_rw [IntervalPolynomialPresentation.derivativeJumpAt_eq_intrinsic] at hRight' hLeft'
  rw [hRight', hLeft', Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Finset.mem_Icc.mp hj |>.2
  simp only [Fintype.sum_sum_type, Fintype.sum_option, poissonJensenPointValue]
  have hLeftCuts :
      ∑ i : Fin mLeft,
          -((-1 : ℝ) ^ j * derivativeJump f j (PLeft.internalCut i) *
              (PLeft.internalCut i - -r) ^ j) * (r - x) ^ n =
        ∑ i : Fin mLeft,
          (auxiliaryOmega f j x (PLeft.internalCut i) *
                interactionKernel r x (PLeft.internalCut i) ^ j *
                  symmetricKernel (n - j) r x +
            auxiliaryGamma f j x (PLeft.internalCut i) *
                interactionKernel r x (PLeft.internalCut i) ^ j *
                  antisymmetricKernel (n - j) r x) := by
    apply Finset.sum_congr rfl
    intro i hi
    convert left_cut_auxiliary_identity f
      (PLeft.internalCut_lt_rightEndpoint i) hjn using 1 <;> ring
  have hRightCuts :
      ∑ i : Fin mRight,
          derivativeJump f j (PRight.internalCut i) *
              (r - PRight.internalCut i) ^ j * (r + x) ^ n =
        ∑ i : Fin mRight,
          (auxiliaryOmega f j x (PRight.internalCut i) *
                interactionKernel r x (PRight.internalCut i) ^ j *
                  symmetricKernel (n - j) r x +
            auxiliaryGamma f j x (PRight.internalCut i) *
                interactionKernel r x (PRight.internalCut i) ^ j *
                  antisymmetricKernel (n - j) r x) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact right_cut_auxiliary_identity f
      (PRight.leftEndpoint_lt_internalCut i) hjn
  have hLeftWeighted :
      -((-1 : ℝ) ^ j *
          ∑ i : Fin mLeft, derivativeJump f j (PLeft.internalCut i) *
            (PLeft.internalCut i - -r) ^ j) * (r - x) ^ n =
        ∑ i : Fin mLeft,
          (auxiliaryOmega f j x (PLeft.internalCut i) *
                interactionKernel r x (PLeft.internalCut i) ^ j *
                  symmetricKernel (n - j) r x +
            auxiliaryGamma f j x (PLeft.internalCut i) *
                interactionKernel r x (PLeft.internalCut i) ^ j *
                  antisymmetricKernel (n - j) r x) := by
    calc
      -((-1 : ℝ) ^ j *
          ∑ i : Fin mLeft, derivativeJump f j (PLeft.internalCut i) *
            (PLeft.internalCut i - -r) ^ j) * (r - x) ^ n =
          ∑ i : Fin mLeft,
            -((-1 : ℝ) ^ j * derivativeJump f j (PLeft.internalCut i) *
              (PLeft.internalCut i - -r) ^ j) * (r - x) ^ n := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := hLeftCuts
  have hRightWeighted :
      (∑ i : Fin mRight, derivativeJump f j (PRight.internalCut i) *
          (r - PRight.internalCut i) ^ j) * (r + x) ^ n =
        ∑ i : Fin mRight,
          (auxiliaryOmega f j x (PRight.internalCut i) *
                interactionKernel r x (PRight.internalCut i) ^ j *
                  symmetricKernel (n - j) r x +
            auxiliaryGamma f j x (PRight.internalCut i) *
                interactionKernel r x (PRight.internalCut i) ^ j *
                  antisymmetricKernel (n - j) r x) := by
    calc
      (∑ i : Fin mRight, derivativeJump f j (PRight.internalCut i) *
          (r - PRight.internalCut i) ^ j) * (r + x) ^ n =
          ∑ i : Fin mRight,
            derivativeJump f j (PRight.internalCut i) *
              (r - PRight.internalCut i) ^ j * (r + x) ^ n := by
        rw [Finset.sum_mul]
      _ = _ := hRightCuts
  rw [← hLeftWeighted, ← hRightWeighted]
  rw [← center_auxiliary_identity f hjn]
  ring

/-- The `B`-part after substituting Lemma 3.2 into the auxiliary sum. -/
def poissonJensenOmegaSum
    {n mLeft mRight : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hx : x ∈ Ioo (-r) r)
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, ∑ q : PoissonJensenPoint mLeft mRight,
    (omegaMultiplicityCoefficient (poissonJensenRegion PLeft PRight hx q) j *
          multiplicity f j (poissonJensenPointValue PLeft PRight q) +
        omegaLeftJetCoefficient (poissonJensenRegion PLeft PRight hx q) j *
          normalizedLeftJet f j (poissonJensenPointValue PLeft PRight q)) *
      interactionKernel r x (poissonJensenPointValue PLeft PRight q) ^ j *
        symmetricKernel (n - j) r x

/-- The `D`-part after substituting Lemma 3.2 into the auxiliary sum. -/
def poissonJensenGammaSum
    {n mLeft mRight : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hx : x ∈ Ioo (-r) r)
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, ∑ q : PoissonJensenPoint mLeft mRight,
    (gammaMultiplicityCoefficient (poissonJensenRegion PLeft PRight hx q) j *
          multiplicity f j (poissonJensenPointValue PLeft PRight q) +
        gammaLeftJetCoefficient (poissonJensenRegion PLeft PRight hx q) j *
          normalizedLeftJet f j (poissonJensenPointValue PLeft PRight q)) *
      interactionKernel r x (poissonJensenPointValue PLeft PRight q) ^ j *
        antisymmetricKernel (n - j) r x

/--
Theorem 3.3 in coefficient-table form.  This is the displayed
Poisson--Jensen identity immediately after applying Lemma 3.2 and before the
paper combines the remaining left-jet terms at `0` and `x`.
-/
theorem poissonJensen_coefficientTable
    {n mLeft mRight : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo (-r) r)
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r) :
    f x = (f r + f (-r)) / 2 +
        antisymmetricKernel n r x / (2 * symmetricKernel n r x) *
          (f r - f (-r)) -
      poissonJensenOmegaSum f hx PLeft PRight / (2 * symmetricKernel n r x) -
      poissonJensenGammaSum f hx PLeft PRight / (2 * symmetricKernel n r x) := by
  have hWeighted := weightedEndpointDifference_eq_auxiliarySum f hx PLeft PRight
  have hExpanded :
      (f r - f x) * (r + x) ^ n - (f x - f (-r)) * (r - x) ^ n =
        poissonJensenOmegaSum f hx PLeft PRight +
          poissonJensenGammaSum f hx PLeft PRight := by
    rw [hWeighted]
    simp only [poissonJensenOmegaSum, poissonJensenGammaSum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    have hAux := auxiliaryJump_eq_byRegion f
      (poissonJensenRegion PLeft PRight hx q) hr hx hj1 hjn
      (poissonJensenPointValue_in_region PLeft PRight hx q)
    rw [hAux.1, hAux.2]
  have hB : symmetricKernel n r x ≠ 0 := symmetricKernel_ne_zero hr hx
  rw [← symmetricKernel_add_antisymmetricKernel n r x,
    ← symmetricKernel_sub_antisymmetricKernel n r x] at hExpanded
  field_simp [hB]
  linear_combination -1 * hExpanded

/-- The part of one Lemma 3.2 summand containing the normalized left jet. -/
def poissonJensenLeftJetContribution
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (region : RelativeRegion) (j : ℕ) (r x y : ℝ) : ℝ :=
  omegaLeftJetCoefficient region j * normalizedLeftJet f j y *
        interactionKernel r x y ^ j * symmetricKernel (n - j) r x +
    gammaLeftJetCoefficient region j * normalizedLeftJet f j y *
        interactionKernel r x y ^ j * antisymmetricKernel (n - j) r x

/-- The per-order left-jet correction contributed by the distinguished point `x`. -/
def poissonJensenCenterCorrectionTerm
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (r x : ℝ) : ℝ :=
  if x = 0 then 0 else
    normalizedLeftJet f j x *
      ((r + x) ^ n * (r - x) ^ j +
        (-1 : ℝ) ^ j * (r - x) ^ n * (r + x) ^ j)

/-- The per-order left-jet correction contributed by the distinguished point `0`. -/
def poissonJensenZeroCorrectionTerm
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (r x : ℝ) : ℝ :=
  if x = 0 then 0 else
    leftSign x * (r - |x|) ^ n * (1 - (-1 : ℝ) ^ (j + 1)) *
      normalizedLeftJet f j 0 * r ^ j

private theorem leftJetContribution_eq_specialTerms
    {n j : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x y : ℝ} (hjn : j ≤ n) (region : RelativeRegion)
    (hregion : InRelativeRegion region r x y) :
    poissonJensenLeftJetContribution f region j r x y =
      if y = x then poissonJensenCenterCorrectionTerm f j r x
      else if y = 0 then poissonJensenZeroCorrectionTerm f j r x else 0 := by
  rcases hregion with ⟨hy, hregion⟩
  cases region with
  | f1 =>
      have hyx : y ≠ x := ne_of_lt (hregion.trans_le (min_le_right 0 x))
      have hy0 : y ≠ 0 := ne_of_lt (hregion.trans_le (min_le_left 0 x))
      simp [poissonJensenLeftJetContribution, hyx, hy0,
        omegaLeftJetCoefficient, gammaLeftJetCoefficient]
  | f2 =>
      have hyx : y ≠ x := ne_of_gt ((le_max_right 0 x).trans_lt hregion)
      have hy0 : y ≠ 0 := ne_of_gt ((le_max_left 0 x).trans_lt hregion)
      simp [poissonJensenLeftJetContribution, hyx, hy0,
        omegaLeftJetCoefficient, gammaLeftJetCoefficient]
  | f3 =>
      rcases hregion with ⟨rfl, rfl⟩
      simp [poissonJensenLeftJetContribution, poissonJensenCenterCorrectionTerm,
        omegaLeftJetCoefficient, gammaLeftJetCoefficient]
  | f4 =>
      rcases hregion with ⟨hy0, hyx⟩
      simp [poissonJensenLeftJetContribution, ne_of_lt hyx, ne_of_gt hy0,
        omegaLeftJetCoefficient, gammaLeftJetCoefficient]
  | f5 =>
      rcases hregion with ⟨hxy, hy0⟩
      simp [poissonJensenLeftJetContribution, ne_of_gt hxy, ne_of_lt hy0,
        omegaLeftJetCoefficient, gammaLeftJetCoefficient]
  | f6 =>
      rcases hregion with ⟨hx0, rfl⟩
      have hxne : x ≠ 0 := ne_of_lt hx0
      have hxnonpos : x ≤ 0 := hx0.le
      simp only [if_neg hxne, if_pos rfl, poissonJensenLeftJetContribution,
        poissonJensenZeroCorrectionTerm, omegaLeftJetCoefficient,
        gammaLeftJetCoefficient, leftSign_of_nonpos hxnonpos,
        abs_of_nonpos hxnonpos, interactionKernel_of_le hx0.le,
        symmetricKernel, antisymmetricKernel]
      simp [hxne.symm]
      have hn : (r + x) ^ n = (r + x) ^ j * (r + x) ^ (n - j) := by
        rw [← pow_add, Nat.add_sub_of_le hjn]
      rw [mul_pow, hn]
      ring
  | f7 =>
      rcases hregion with ⟨rfl, hx0⟩
      have hxne : x ≠ 0 := ne_of_gt hx0
      have hxnonneg : 0 ≤ x := hx0.le
      simp only [if_neg hxne, if_pos rfl, poissonJensenLeftJetContribution,
        poissonJensenZeroCorrectionTerm, omegaLeftJetCoefficient,
        gammaLeftJetCoefficient, leftSign_of_pos hx0,
        abs_of_nonneg hxnonneg, interactionKernel_of_ge hxnonneg,
        symmetricKernel, antisymmetricKernel]
      simp [hxne.symm]
      have hn : (r - x) ^ n = (r - x) ^ j * (r - x) ^ (n - j) := by
        rw [← pow_add, Nat.add_sub_of_le hjn]
      rw [mul_pow, hn]
      ring
  | f8 =>
      rcases hregion with ⟨hx0, rfl⟩
      have hxne : y ≠ 0 := ne_of_gt hx0
      simp only [if_pos rfl, poissonJensenLeftJetContribution,
        poissonJensenCenterCorrectionTerm, if_neg hxne,
        omegaLeftJetCoefficient, gammaLeftJetCoefficient,
        interactionKernel_diag, symmetricKernel, antisymmetricKernel]
      have he : r ^ 2 - y ^ 2 = (r - y) * (r + y) := by ring
      have hp : (r + y) ^ n = (r + y) ^ j * (r + y) ^ (n - j) := by
        rw [← pow_add, Nat.add_sub_of_le hjn]
      have hm : (r - y) ^ n = (r - y) ^ j * (r - y) ^ (n - j) := by
        rw [← pow_add, Nat.add_sub_of_le hjn]
      rw [he, mul_pow, hp, hm, pow_succ]
      simp
      ring
  | f9 =>
      rcases hregion with ⟨rfl, hx0⟩
      have hxne : y ≠ 0 := ne_of_lt hx0
      simp only [if_pos rfl, poissonJensenLeftJetContribution,
        poissonJensenCenterCorrectionTerm, if_neg hxne,
        omegaLeftJetCoefficient, gammaLeftJetCoefficient,
        interactionKernel_diag, symmetricKernel, antisymmetricKernel]
      have he : r ^ 2 - y ^ 2 = (r - y) * (r + y) := by ring
      have hp : (r + y) ^ n = (r + y) ^ j * (r + y) ^ (n - j) := by
        rw [← pow_add, Nat.add_sub_of_le hjn]
      have hm : (r - y) ^ n = (r - y) ^ j * (r - y) ^ (n - j) := by
        rw [← pow_add, Nat.add_sub_of_le hjn]
      rw [he, mul_pow, hp, hm, pow_succ]
      simp
      ring

theorem poissonJensenPointValue_injective
    {n mLeft mRight : ℕ} {f : NthTropicalMeromorphicFunction n} {r x : ℝ}
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r) :
    Function.Injective (poissonJensenPointValue PLeft PRight) := by
  intro q₁ q₂ h
  cases q₁ with
  | inl i =>
      cases q₂ with
      | inl k =>
          congr 1
          exact PLeft.internalCut_strictMono.injective h
      | inr q =>
          cases q with
          | none =>
              exfalso
              exact (ne_of_lt (PLeft.internalCut_lt_rightEndpoint i)) h
          | some k =>
              exfalso
              have hik : PLeft.internalCut i < PRight.internalCut k :=
                (PLeft.internalCut_lt_rightEndpoint i).trans
                  (PRight.leftEndpoint_lt_internalCut k)
              exact (ne_of_lt hik) h
  | inr q₁ =>
      cases q₁ with
      | none =>
          cases q₂ with
          | inl k =>
              exfalso
              exact (ne_of_gt (PLeft.internalCut_lt_rightEndpoint k)) h
          | inr q₂ =>
              cases q₂ with
              | none => rfl
              | some k =>
                  exfalso
                  exact (ne_of_lt (PRight.leftEndpoint_lt_internalCut k)) h
      | some i =>
          cases q₂ with
          | inl k =>
              exfalso
              have hki : PLeft.internalCut k < PRight.internalCut i :=
                (PLeft.internalCut_lt_rightEndpoint k).trans
                  (PRight.leftEndpoint_lt_internalCut i)
              exact (ne_of_gt hki) h
          | inr q₂ =>
              cases q₂ with
              | none =>
                  exfalso
                  exact (ne_of_gt (PRight.leftEndpoint_lt_internalCut i)) h
              | some k =>
                  congr 2
                  exact PRight.internalCut_strictMono.injective h

/-- A chosen occurrence of `0` in the augmented finite point family. -/
structure PoissonJensenZeroWitness
    {n mLeft mRight : ℕ} {f : NthTropicalMeromorphicFunction n} {r x : ℝ}
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r) where
  point : PoissonJensenPoint mLeft mRight
  value_eq_zero : poissonJensenPointValue PLeft PRight point = 0

/--
All finite local data used by the proof of Theorem 3.3.  This is construction
data, not an additional hypothesis in the public Poisson--Jensen theorem.
-/
structure PoissonJensenLocalData
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (r x : ℝ) where
  mLeft : ℕ
  mRight : ℕ
  leftPresentation : IntervalPolynomialPresentation n mLeft f (-r) x
  rightPresentation : IntervalPolynomialPresentation n mRight f x r
  left_contains_globalCut :
    ∀ k : ℤ, -r < f.presentation.cutPoint k →
      f.presentation.cutPoint k < x →
        ∃ i : Fin mLeft, leftPresentation.internalCut i = f.presentation.cutPoint k
  right_contains_globalCut :
    ∀ k : ℤ, x < f.presentation.cutPoint k →
      f.presentation.cutPoint k < r →
        ∃ i : Fin mRight, rightPresentation.internalCut i = f.presentation.cutPoint k
  zeroWitness : PoissonJensenZeroWitness leftPresentation rightPresentation

/--
The global presentation always supplies the finite local meshes used in the
paper's proof, including an occurrence of `0` in the augmented point family.
-/
theorem exists_poissonJensenLocalData
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo (-r) r) :
    Nonempty (PoissonJensenLocalData f r x) := by
  obtain ⟨mLeft, PLeft, hLeft⟩ :=
    f.presentation.exists_intervalPresentation_complete hx.1
  obtain ⟨mRight, PRight, hRight⟩ :=
    f.presentation.exists_intervalPresentation_complete hx.2
  rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
  · obtain ⟨i, hi⟩ := hRight 0
      (by simpa [f.presentation.cutPoint_zero] using hxneg)
      (by simpa [f.presentation.cutPoint_zero] using hr)
    refine ⟨⟨mLeft, mRight, PLeft, PRight, hLeft, hRight,
      ⟨.inr (some i), ?_⟩⟩⟩
    simpa [poissonJensenPointValue, f.presentation.cutPoint_zero] using hi
  · subst x
    exact ⟨⟨mLeft, mRight, PLeft, PRight, hLeft, hRight,
      ⟨.inr none, rfl⟩⟩⟩
  · obtain ⟨i, hi⟩ := hLeft 0
      (by simpa [f.presentation.cutPoint_zero] using hr)
      (by simpa [f.presentation.cutPoint_zero] using hxpos)
    refine ⟨⟨mLeft, mRight, PLeft, PRight, hLeft, hRight,
      ⟨.inl i, ?_⟩⟩⟩
    simpa [poissonJensenPointValue, f.presentation.cutPoint_zero] using hi

/-- Canonical classical choice of the local data whose existence is proved above. -/
noncomputable def poissonJensenLocalData
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo (-r) r) :
    PoissonJensenLocalData f r x :=
  Classical.choice (exists_poissonJensenLocalData f hr hx)

private theorem sum_leftJetContribution_eq_specialTerms
    {n mLeft mRight : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hx : x ∈ Ioo (-r) r)
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r)
    (zeroWitness : PoissonJensenZeroWitness PLeft PRight)
    {j : ℕ} (hjn : j ≤ n) :
    (∑ q : PoissonJensenPoint mLeft mRight,
      poissonJensenLeftJetContribution f
        (poissonJensenRegion PLeft PRight hx q) j r x
          (poissonJensenPointValue PLeft PRight q)) =
      poissonJensenCenterCorrectionTerm f j r x +
        poissonJensenZeroCorrectionTerm f j r x := by
  have hRewrite :
      (∑ q : PoissonJensenPoint mLeft mRight,
        poissonJensenLeftJetContribution f
          (poissonJensenRegion PLeft PRight hx q) j r x
            (poissonJensenPointValue PLeft PRight q)) =
        ∑ q : PoissonJensenPoint mLeft mRight,
          if poissonJensenPointValue PLeft PRight q = x then
            poissonJensenCenterCorrectionTerm f j r x
          else if poissonJensenPointValue PLeft PRight q = 0 then
            poissonJensenZeroCorrectionTerm f j r x else 0 := by
    apply Finset.sum_congr rfl
    intro q hq
    exact leftJetContribution_eq_specialTerms f hjn
      (poissonJensenRegion PLeft PRight hx q)
      (poissonJensenPointValue_in_region PLeft PRight hx q)
  rw [hRewrite]
  by_cases hx0 : x = 0
  · subst x
    simp [poissonJensenCenterCorrectionTerm, poissonJensenZeroCorrectionTerm]
  · let center : PoissonJensenPoint mLeft mRight := Sum.inr none
    let value := poissonJensenPointValue PLeft PRight
    let centerTerm := poissonJensenCenterCorrectionTerm f j r x
    let zeroTerm := poissonJensenZeroCorrectionTerm f j r x
    have hinj : Function.Injective value :=
      poissonJensenPointValue_injective PLeft PRight
    have hx0symm : 0 ≠ x := Ne.symm hx0
    have hsplit : ∀ q : PoissonJensenPoint mLeft mRight,
        (if value q = x then centerTerm else if value q = 0 then zeroTerm else 0) =
          (if value q = x then centerTerm else 0) +
            (if value q = 0 then zeroTerm else 0) := by
      intro q
      by_cases hqx : value q = x
      · have hq0 : value q ≠ 0 := by simpa [hqx] using hx0
        simp [hqx, hq0, hx0, hx0symm]
      · by_cases hq0 : value q = 0
        · simp [hqx, hq0, hx0, hx0symm]
        · simp [hqx, hq0, hx0, hx0symm]
    have hSplitSum :
        (∑ q : PoissonJensenPoint mLeft mRight,
          if value q = x then centerTerm else if value q = 0 then zeroTerm else 0) =
          (∑ q : PoissonJensenPoint mLeft mRight,
            if value q = x then centerTerm else 0) +
          ∑ q : PoissonJensenPoint mLeft mRight,
            if value q = 0 then zeroTerm else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      exact hsplit q
    have hCenterSum :
        (∑ q : PoissonJensenPoint mLeft mRight,
          if value q = x then centerTerm else 0) = centerTerm := by
      rw [Finset.sum_eq_single center]
      · change (if x = x then centerTerm else 0) = centerTerm
        simp
      · intro q hq hqne
        have hvalue : value q ≠ x := by
          intro h
          apply hqne
          apply hinj
          calc
            value q = x := h
            _ = value center := by rfl
        simp [hvalue]
      · simp
    have hZeroSum :
        (∑ q : PoissonJensenPoint mLeft mRight,
          if value q = 0 then zeroTerm else 0) = zeroTerm := by
      rw [Finset.sum_eq_single zeroWitness.point]
      · simp [value, zeroWitness.value_eq_zero]
      · intro q hq hqne
        have hvalue : value q ≠ 0 := by
          intro h
          apply hqne
          apply hinj
          exact h.trans zeroWitness.value_eq_zero.symm
        simp [hvalue]
      · simp
    rw [hSplitSum, hCenterSum, hZeroSum]

/-- The `B`-weighted multiplicity sum appearing literally in (3pj). -/
def poissonJensenOmegaMultiplicitySum
    {n mLeft mRight : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hx : x ∈ Ioo (-r) r)
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, ∑ q : PoissonJensenPoint mLeft mRight,
    omegaMultiplicityCoefficient (poissonJensenRegion PLeft PRight hx q) j *
      multiplicity f j (poissonJensenPointValue PLeft PRight q) *
        interactionKernel r x (poissonJensenPointValue PLeft PRight q) ^ j *
          symmetricKernel (n - j) r x

/-- The `D`-weighted multiplicity sum appearing literally in (3pj). -/
def poissonJensenGammaMultiplicitySum
    {n mLeft mRight : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hx : x ∈ Ioo (-r) r)
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, ∑ q : PoissonJensenPoint mLeft mRight,
    gammaMultiplicityCoefficient (poissonJensenRegion PLeft PRight hx q) j *
      multiplicity f j (poissonJensenPointValue PLeft PRight q) *
        interactionKernel r x (poissonJensenPointValue PLeft PRight q) ^ j *
          antisymmetricKernel (n - j) r x

private def poissonJensenOmegaLeftJetSum
    {n mLeft mRight : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hx : x ∈ Ioo (-r) r)
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, ∑ q : PoissonJensenPoint mLeft mRight,
    omegaLeftJetCoefficient (poissonJensenRegion PLeft PRight hx q) j *
      normalizedLeftJet f j (poissonJensenPointValue PLeft PRight q) *
        interactionKernel r x (poissonJensenPointValue PLeft PRight q) ^ j *
          symmetricKernel (n - j) r x

private def poissonJensenGammaLeftJetSum
    {n mLeft mRight : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hx : x ∈ Ioo (-r) r)
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, ∑ q : PoissonJensenPoint mLeft mRight,
    gammaLeftJetCoefficient (poissonJensenRegion PLeft PRight hx q) j *
      normalizedLeftJet f j (poissonJensenPointValue PLeft PRight q) *
        interactionKernel r x (poissonJensenPointValue PLeft PRight q) ^ j *
          antisymmetricKernel (n - j) r x

private theorem range_succ_eq_insert_Icc_main (n : ℕ) :
    Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
  ext j
  simp
  omega

private theorem polynomial_eval_sub_eq_jetSum
    (p : Polynomial ℝ) {n : ℕ} (hp : p.natDegree ≤ n) (a b : ℝ) :
    p.eval b - p.eval a =
      ∑ j ∈ Finset.Icc 1 n,
        normalizedPolynomialJet p j a * (b - a) ^ j := by
  rw [polynomial_eval_eq_sum_normalizedJet p hp a b,
    range_succ_eq_insert_Icc_main, Finset.sum_insert (by simp)]
  simp [normalizedPolynomialJet]

private theorem sum_specialTerms_eq_polynomialCorrection
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (r x : ℝ) :
    (∑ j ∈ Finset.Icc 1 n,
      (poissonJensenCenterCorrectionTerm f j r x +
        poissonJensenZeroCorrectionTerm f j r x)) =
      (r + x) ^ n * ((f.presentation.leftPieceAt x).eval r - f x) +
        (r - x) ^ n * ((f.presentation.leftPieceAt x).eval (-r) - f x) +
        leftSign x * (r - |x|) ^ n *
          ((f.presentation.leftPieceAt 0).eval r +
            (f.presentation.leftPieceAt 0).eval (-r) - 2 * f 0) := by
  by_cases hx0 : x = 0
  · subst x
    have hp0 : (f.presentation.leftPieceAt 0).eval 0 = f 0 :=
      f.presentation.leftPieceAt_eval 0
    simp [poissonJensenCenterCorrectionTerm, poissonJensenZeroCorrectionTerm,
      leftSign, hp0]
    ring
  · rw [Finset.sum_add_distrib]
    have hCenter :
        (∑ j ∈ Finset.Icc 1 n, poissonJensenCenterCorrectionTerm f j r x) =
          (r + x) ^ n * ((f.presentation.leftPieceAt x).eval r - f x) +
            (r - x) ^ n * ((f.presentation.leftPieceAt x).eval (-r) - f x) := by
      let p := f.presentation.leftPieceAt x
      have hpr := polynomial_eval_sub_eq_jetSum p
        (f.presentation.leftPieceAt_natDegree_le x) x r
      have hpm := polynomial_eval_sub_eq_jetSum p
        (f.presentation.leftPieceAt_natDegree_le x) x (-r)
      have hpm' : p.eval (-r) - p.eval x =
          ∑ j ∈ Finset.Icc 1 n,
            (-1 : ℝ) ^ j * normalizedPolynomialJet p j x * (r + x) ^ j := by
        rw [hpm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [show -r - x = -(r + x) by ring, neg_pow]
        ring
      have hpx : p.eval x = f x := f.presentation.leftPieceAt_eval x
      simp only [poissonJensenCenterCorrectionTerm, if_neg hx0,
        normalizedLeftJet]
      calc
        (∑ j ∈ Finset.Icc 1 n,
          normalizedPolynomialJet p j x *
            ((r + x) ^ n * (r - x) ^ j +
              (-1 : ℝ) ^ j * (r - x) ^ n * (r + x) ^ j)) =
            (r + x) ^ n *
                (∑ j ∈ Finset.Icc 1 n,
                  normalizedPolynomialJet p j x * (r - x) ^ j) +
              (r - x) ^ n *
                (∑ j ∈ Finset.Icc 1 n,
                  (-1 : ℝ) ^ j * normalizedPolynomialJet p j x *
                    (r + x) ^ j) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by rw [← hpr, ← hpm', hpx]
    have hZero :
        (∑ j ∈ Finset.Icc 1 n, poissonJensenZeroCorrectionTerm f j r x) =
          leftSign x * (r - |x|) ^ n *
            ((f.presentation.leftPieceAt 0).eval r +
              (f.presentation.leftPieceAt 0).eval (-r) - 2 * f 0) := by
      let p := f.presentation.leftPieceAt 0
      have hpr := polynomial_eval_sub_eq_jetSum p
        (f.presentation.leftPieceAt_natDegree_le 0) 0 r
      have hpm := polynomial_eval_sub_eq_jetSum p
        (f.presentation.leftPieceAt_natDegree_le 0) 0 (-r)
      have hpm' : p.eval (-r) - p.eval 0 =
          ∑ j ∈ Finset.Icc 1 n,
            (-1 : ℝ) ^ j * normalizedPolynomialJet p j 0 * r ^ j := by
        rw [hpm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [show -r - 0 = -r by ring, neg_pow]
        ring
      have hpr' : p.eval r - p.eval 0 =
          ∑ j ∈ Finset.Icc 1 n,
            normalizedPolynomialJet p j 0 * r ^ j := by
        simpa using hpr
      have hp0 : p.eval 0 = f 0 := f.presentation.leftPieceAt_eval 0
      simp only [poissonJensenZeroCorrectionTerm, if_neg hx0,
        normalizedLeftJet]
      calc
        (∑ j ∈ Finset.Icc 1 n,
          leftSign x * (r - |x|) ^ n * (1 - (-1 : ℝ) ^ (j + 1)) *
            normalizedPolynomialJet p j 0 * r ^ j) =
            leftSign x * (r - |x|) ^ n *
              ((∑ j ∈ Finset.Icc 1 n,
                  normalizedPolynomialJet p j 0 * r ^ j) +
                ∑ j ∈ Finset.Icc 1 n,
                  (-1 : ℝ) ^ j * normalizedPolynomialJet p j 0 * r ^ j) := by
          rw [mul_add, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          rw [pow_succ]
          ring
        _ = _ := by
          rw [← hpr', ← hpm', hp0]
          simp only [p]
          ring
    rw [hCenter, hZero]

/--
Theorem 3.3: the n-th tropical Poisson--Jensen formula (3pj).

The finite presentations enumerate all local polynomial changes on the two
sides of `x`; redundant cuts contribute zero.  `zeroWitness` records the
paper's deliberate insertion of `0` into the augmented point family.
-/
theorem poissonJensen_of_presentations
    {n mLeft mRight : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo (-r) r)
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) x)
    (PRight : IntervalPolynomialPresentation n mRight f x r)
    (zeroWitness : PoissonJensenZeroWitness PLeft PRight) :
    f x = (f r + f (-r)) / 2 +
        antisymmetricKernel n r x / (2 * symmetricKernel n r x) *
          (f r - f (-r)) -
      poissonJensenOmegaMultiplicitySum f hx PLeft PRight /
        (2 * symmetricKernel n r x) -
      poissonJensenGammaMultiplicitySum f hx PLeft PRight /
        (2 * symmetricKernel n r x) -
      ((r + x) ^ n / (2 * symmetricKernel n r x) *
          ((f.presentation.leftPieceAt x).eval r - f x) +
        (r - x) ^ n / (2 * symmetricKernel n r x) *
          ((f.presentation.leftPieceAt x).eval (-r) - f x)) -
      leftSign x * (r - |x|) ^ n / (2 * symmetricKernel n r x) *
        ((f.presentation.leftPieceAt 0).eval r +
          (f.presentation.leftPieceAt 0).eval (-r) - 2 * f 0) := by
  have hCoefficient := poissonJensen_coefficientTable f hr hx PLeft PRight
  have hOmega : poissonJensenOmegaSum f hx PLeft PRight =
      poissonJensenOmegaMultiplicitySum f hx PLeft PRight +
        poissonJensenOmegaLeftJetSum f hx PLeft PRight := by
    simp only [poissonJensenOmegaSum, poissonJensenOmegaMultiplicitySum,
      poissonJensenOmegaLeftJetSum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have hGamma : poissonJensenGammaSum f hx PLeft PRight =
      poissonJensenGammaMultiplicitySum f hx PLeft PRight +
        poissonJensenGammaLeftJetSum f hx PLeft PRight := by
    simp only [poissonJensenGammaSum, poissonJensenGammaMultiplicitySum,
      poissonJensenGammaLeftJetSum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have hLeftJet :
      poissonJensenOmegaLeftJetSum f hx PLeft PRight +
          poissonJensenGammaLeftJetSum f hx PLeft PRight =
        (r + x) ^ n * ((f.presentation.leftPieceAt x).eval r - f x) +
          (r - x) ^ n * ((f.presentation.leftPieceAt x).eval (-r) - f x) +
          leftSign x * (r - |x|) ^ n *
            ((f.presentation.leftPieceAt 0).eval r +
              (f.presentation.leftPieceAt 0).eval (-r) - 2 * f 0) := by
    have hCombine :
        poissonJensenOmegaLeftJetSum f hx PLeft PRight +
            poissonJensenGammaLeftJetSum f hx PLeft PRight =
          ∑ j ∈ Finset.Icc 1 n,
            ∑ q : PoissonJensenPoint mLeft mRight,
              poissonJensenLeftJetContribution f
                (poissonJensenRegion PLeft PRight hx q) j r x
                  (poissonJensenPointValue PLeft PRight q) := by
      simp only [poissonJensenOmegaLeftJetSum,
        poissonJensenGammaLeftJetSum, poissonJensenLeftJetContribution]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_add_distrib]
    rw [hCombine]
    have hSpecial :
        (∑ j ∈ Finset.Icc 1 n,
          ∑ q : PoissonJensenPoint mLeft mRight,
            poissonJensenLeftJetContribution f
              (poissonJensenRegion PLeft PRight hx q) j r x
                (poissonJensenPointValue PLeft PRight q)) =
          ∑ j ∈ Finset.Icc 1 n,
            (poissonJensenCenterCorrectionTerm f j r x +
              poissonJensenZeroCorrectionTerm f j r x) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact sum_leftJetContribution_eq_specialTerms f hx PLeft PRight
        zeroWitness (Finset.mem_Icc.mp hj).2
    rw [hSpecial]
    exact sum_specialTerms_eq_polynomialCorrection f r x
  rw [hOmega, hGamma] at hCoefficient
  calc
    f x = _ := hCoefficient
    _ = _ := by
      linear_combination
        -(1 / (2 * symmetricKernel n r x)) * hLeftJet

/--
The signed-multiplicity form of the `x = 0` specialization in Theorem 3.3.
The finite point family contains every internal cut of the two interval
presentations and one distinguished copy of `0`; redundant cuts contribute
zero multiplicity.
-/
theorem jensenSignedSum_of_presentations
    {n mLeft mRight : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r)
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) 0)
    (PRight : IntervalPolynomialPresentation n mRight f 0 r) :
    f 0 = (f r + f (-r)) / 2 -
      (1 / 2) *
        ∑ j ∈ Finset.Icc 1 n,
          ∑ q : PoissonJensenPoint mLeft mRight,
            multiplicity f j (poissonJensenPointValue PLeft PRight q) *
              (r - |poissonJensenPointValue PLeft PRight q|) ^ j := by
  have hzero : (0 : ℝ) ∈ Ioo (-r) r := by
    constructor <;> linarith
  have h := weightedEndpointDifference_eq_auxiliarySum f hzero PLeft PRight
  simp only [add_zero, sub_zero, auxiliaryOmega_zero,
    interactionKernel_at_zero, symmetricKernel_at_zero,
    antisymmetricKernel_at_zero, mul_zero, add_zero] at h
  have hsum :
      (∑ j ∈ Finset.Icc 1 n,
        ∑ q : PoissonJensenPoint mLeft mRight,
          multiplicity f j (poissonJensenPointValue PLeft PRight q) *
              (r * (r - |poissonJensenPointValue PLeft PRight q|)) ^ j *
                r ^ (n - j)) =
        r ^ n *
          ∑ j ∈ Finset.Icc 1 n,
            ∑ q : PoissonJensenPoint mLeft mRight,
              multiplicity f j (poissonJensenPointValue PLeft PRight q) *
                (r - |poissonJensenPointValue PLeft PRight q|) ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    rw [mul_pow]
    have hp : r ^ j * r ^ (n - j) = r ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hjn]
    rw [← hp]
    ring
  rw [hsum] at h
  have hrpow : r ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hr)
  have hcancel :
      (f r - f 0) - (f 0 - f (-r)) =
        ∑ j ∈ Finset.Icc 1 n,
          ∑ q : PoissonJensenPoint mLeft mRight,
            multiplicity f j (poissonJensenPointValue PLeft PRight q) *
              (r - |poissonJensenPointValue PLeft PRight q|) ^ j := by
    apply mul_left_cancel₀ hrpow
    calc
      r ^ n * ((f r - f 0) - (f 0 - f (-r))) =
          (f r - f 0) * r ^ n - (f 0 - f (-r)) * r ^ n := by ring
      _ = _ := h
  linear_combination (-1 / 2) * hcancel

/-- Indices in the finite Jensen family which are `j`-th roots. -/
noncomputable def jensenRootPoints
    {n mLeft mRight : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ}
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) 0)
    (PRight : IntervalPolynomialPresentation n mRight f 0 r)
    (j : ℕ) : Finset (PoissonJensenPoint mLeft mRight) := by
  classical
  exact Finset.univ.filter (fun q ↦
    IsJthRoot f j (poissonJensenPointValue PLeft PRight q))

/-- Indices in the finite Jensen family which are `j`-th poles. -/
noncomputable def jensenPolePoints
    {n mLeft mRight : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ}
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) 0)
    (PRight : IntervalPolynomialPresentation n mRight f 0 r)
    (j : ℕ) : Finset (PoissonJensenPoint mLeft mRight) := by
  classical
  exact Finset.univ.filter (fun q ↦
    IsJthPole f j (poissonJensenPointValue PLeft PRight q))

/--
The root/pole form of the Jensen specialization in Theorem 3.3.  The two
filtered sums are the paper's sums over the `j`-th roots and `j`-th poles;
`rootOrPoleMultiplicity` turns their signed multiplicities into positive
weights.
-/
theorem jensenFormula_of_presentations
    {n mLeft mRight : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r)
    (PLeft : IntervalPolynomialPresentation n mLeft f (-r) 0)
    (PRight : IntervalPolynomialPresentation n mRight f 0 r) :
    f 0 = (f r + f (-r)) / 2 -
        (1 / 2) *
          ∑ j ∈ Finset.Icc 1 n,
            ∑ q ∈ jensenRootPoints f PLeft PRight j,
              rootOrPoleMultiplicity f j
                  (poissonJensenPointValue PLeft PRight q) *
                (r - |poissonJensenPointValue PLeft PRight q|) ^ j +
        (1 / 2) *
          ∑ j ∈ Finset.Icc 1 n,
            ∑ q ∈ jensenPolePoints f PLeft PRight j,
              rootOrPoleMultiplicity f j
                  (poissonJensenPointValue PLeft PRight q) *
                (r - |poissonJensenPointValue PLeft PRight q|) ^ j := by
  classical
  rw [jensenSignedSum_of_presentations f hr PLeft PRight]
  have hsplit :
      (∑ j ∈ Finset.Icc 1 n,
        ∑ q : PoissonJensenPoint mLeft mRight,
          multiplicity f j (poissonJensenPointValue PLeft PRight q) *
            (r - |poissonJensenPointValue PLeft PRight q|) ^ j) =
        (∑ j ∈ Finset.Icc 1 n,
          ∑ q ∈ jensenRootPoints f PLeft PRight j,
            rootOrPoleMultiplicity f j
                (poissonJensenPointValue PLeft PRight q) *
              (r - |poissonJensenPointValue PLeft PRight q|) ^ j) -
        (∑ j ∈ Finset.Icc 1 n,
          ∑ q ∈ jensenPolePoints f PLeft PRight j,
            rootOrPoleMultiplicity f j
                (poissonJensenPointValue PLeft PRight q) *
              (r - |poissonJensenPointValue PLeft PRight q|) ^ j) := by
    simp only [jensenRootPoints, jensenPolePoints]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hroot :
        0 < multiplicity f j (poissonJensenPointValue PLeft PRight q)
    · have hnotpole :
          ¬multiplicity f j (poissonJensenPointValue PLeft PRight q) < 0 :=
        not_lt.mpr hroot.le
      simp [IsJthRoot, IsJthPole, rootOrPoleMultiplicity,
        hroot, hnotpole, abs_of_pos hroot]
    · by_cases hpole :
          multiplicity f j (poissonJensenPointValue PLeft PRight q) < 0
      · have hnotroot :
            ¬0 < multiplicity f j (poissonJensenPointValue PLeft PRight q) :=
          not_lt.mpr hpole.le
        simp [IsJthRoot, IsJthPole, rootOrPoleMultiplicity,
          hnotroot, hpole, abs_of_neg hpole]
      · have hzero :
            multiplicity f j (poissonJensenPointValue PLeft PRight q) = 0 := by
          exact le_antisymm (not_lt.mp hroot) (not_lt.mp hpole)
        simp [IsJthRoot, IsJthPole, rootOrPoleMultiplicity, hzero]
  rw [hsplit]
  ring

/-! ## Presentation-free public forms -/

/-- The intrinsic `B`-weighted multiplicity sum, with all finite mesh data hidden. -/
noncomputable def poissonJensenOmegaMultiplicity
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo (-r) r) : ℝ :=
  let data := poissonJensenLocalData f hr hx
  poissonJensenOmegaMultiplicitySum f hx
    data.leftPresentation data.rightPresentation

/-- The intrinsic `D`-weighted multiplicity sum, with all finite mesh data hidden. -/
noncomputable def poissonJensenGammaMultiplicity
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo (-r) r) : ℝ :=
  let data := poissonJensenLocalData f hr hx
  poissonJensenGammaMultiplicitySum f hx
    data.leftPresentation data.rightPresentation

/--
Theorem 3.3 in the paper's original quantifier form.  The finite restrictions
of the global presentation and the inserted occurrence of `0` are constructed
internally by `exists_poissonJensenLocalData`.
-/
theorem poissonJensen
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo (-r) r) :
    f x = (f r + f (-r)) / 2 +
        antisymmetricKernel n r x / (2 * symmetricKernel n r x) *
          (f r - f (-r)) -
      poissonJensenOmegaMultiplicity f hr hx /
        (2 * symmetricKernel n r x) -
      poissonJensenGammaMultiplicity f hr hx /
        (2 * symmetricKernel n r x) -
      ((r + x) ^ n / (2 * symmetricKernel n r x) *
          ((f.presentation.leftPieceAt x).eval r - f x) +
        (r - x) ^ n / (2 * symmetricKernel n r x) *
          ((f.presentation.leftPieceAt x).eval (-r) - f x)) -
      leftSign x * (r - |x|) ^ n / (2 * symmetricKernel n r x) *
        ((f.presentation.leftPieceAt 0).eval r +
          (f.presentation.leftPieceAt 0).eval (-r) - 2 * f 0) := by
  let data := poissonJensenLocalData f hr hx
  simpa [poissonJensenOmegaMultiplicity,
    poissonJensenGammaMultiplicity, data] using
      poissonJensen_of_presentations f hr hx
        data.leftPresentation data.rightPresentation data.zeroWitness

private theorem zero_mem_symmetricIoo {r : ℝ} (hr : 0 < r) :
    (0 : ℝ) ∈ Ioo (-r) r := by
  constructor <;> linarith

/-- Canonical finite data for the Jensen specialization `x=0`. -/
noncomputable def jensenLocalData
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r) : PoissonJensenLocalData f r 0 :=
  poissonJensenLocalData f hr (zero_mem_symmetricIoo hr)

/-- The finite signed multiplicity sum in the `x=0` Jensen formula. -/
noncomputable def jensenSignedMultiplicitySum
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r) : ℝ :=
  let data := jensenLocalData f hr
  ∑ j ∈ Finset.Icc 1 n,
    ∑ q : PoissonJensenPoint data.mLeft data.mRight,
      multiplicity f j
          (poissonJensenPointValue data.leftPresentation data.rightPresentation q) *
        (r - |poissonJensenPointValue
          data.leftPresentation data.rightPresentation q|) ^ j

/-- The positive root contribution in the Jensen formula. -/
noncomputable def jensenRootMultiplicitySum
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r) : ℝ :=
  let data := jensenLocalData f hr
  ∑ j ∈ Finset.Icc 1 n,
    ∑ q ∈ jensenRootPoints f data.leftPresentation data.rightPresentation j,
      rootOrPoleMultiplicity f j
          (poissonJensenPointValue data.leftPresentation data.rightPresentation q) *
        (r - |poissonJensenPointValue
          data.leftPresentation data.rightPresentation q|) ^ j

/-- The positive pole contribution in the Jensen formula. -/
noncomputable def jensenPoleMultiplicitySum
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r) : ℝ :=
  let data := jensenLocalData f hr
  ∑ j ∈ Finset.Icc 1 n,
    ∑ q ∈ jensenPolePoints f data.leftPresentation data.rightPresentation j,
      rootOrPoleMultiplicity f j
          (poissonJensenPointValue data.leftPresentation data.rightPresentation q) *
        (r - |poissonJensenPointValue
          data.leftPresentation data.rightPresentation q|) ^ j

/-- The signed `x=0` specialization of Theorem 3.3, without mesh parameters. -/
theorem jensenSignedSum
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r) :
    f 0 = (f r + f (-r)) / 2 -
      (1 / 2) * jensenSignedMultiplicitySum f hr := by
  let data := jensenLocalData f hr
  simpa [jensenSignedMultiplicitySum, data] using
    jensenSignedSum_of_presentations f hr
      data.leftPresentation data.rightPresentation

/--
The root/pole Jensen formula from Theorem 3.3, in the paper's original
quantifier form and with all finite presentation data constructed internally.
-/
theorem jensenFormula
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r) :
    f 0 = (f r + f (-r)) / 2 -
        (1 / 2) * jensenRootMultiplicitySum f hr +
        (1 / 2) * jensenPoleMultiplicitySum f hr := by
  let data := jensenLocalData f hr
  simpa [jensenRootMultiplicitySum, jensenPoleMultiplicitySum, data] using
    jensenFormula_of_presentations f hr
      data.leftPresentation data.rightPresentation

end

end NthTropicalNevanlinna
