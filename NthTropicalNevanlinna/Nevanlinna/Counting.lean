import NthTropicalNevanlinna.Function.Operations
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Proximity, counting, and characteristic functions

The finite pole/root sets are extracted from a global presentation, but their
membership theorems are intrinsic: they contain exactly the roots or poles in
the open radial interval.  This makes all subsequent sums independent of
redundant cuts and of the chosen presentation.
-/

open Set MeasureTheory

namespace NthTropicalNevanlinna

noncomputable section

open scoped BigOperators

/-- Max-plus positive part `f⁺`. -/
def maxPlusPositivePart (x : ℝ) : ℝ := max x 0

/-- The max-plus proximity function `m(r,f)`. -/
def proximity {n : ℕ} (r : ℝ) (f : NthTropicalMeromorphicFunction n) : ℝ :=
  (maxPlusPositivePart (f r) + maxPlusPositivePart (f (-r))) / 2

/--
The finite set of cuts of `P` lying in `(a,b)`.  The integer interval used
before mapping is large enough to contain every such cut.
-/
noncomputable def presentationCutPointsIn
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    (a b : ℝ) : Finset ℝ := by
  classical
  exact ((Finset.Ico (presentationIntervalIndex P a)
    (presentationIntervalIndex P b)).image P.cutPoint).filter
      (fun y ↦ y ∈ Ioo a b)

theorem presentationCutPointsIn_subset_Ioo
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    {a b y : ℝ} (hy : y ∈ presentationCutPointsIn P a b) : y ∈ Ioo a b := by
  classical
  exact (Finset.mem_filter.mp hy).2

theorem mem_presentationCutPointsIn_of_eq_cutPoint
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    {a b y : ℝ} (hy : y ∈ Ioo a b) {k : ℤ} (hyk : y = P.cutPoint k) :
    y ∈ presentationCutPointsIn P a b := by
  classical
  let ia := presentationIntervalIndex P a
  let ib := presentationIntervalIndex P b
  have ha := presentationIntervalIndex_mem P a
  have hb := presentationIntervalIndex_mem P b
  change a ∈ Ioc (P.cutPoint (ia - 1)) (P.cutPoint ia) at ha
  change b ∈ Ioc (P.cutPoint (ib - 1)) (P.cutPoint ib) at hb
  have hiak : ia ≤ k := by
    by_contra h
    have hki : k < ia := lt_of_not_ge h
    have hcut : P.cutPoint k ≤ P.cutPoint (ia - 1) :=
      P.cutPoint_strictMono.monotone (by omega)
    rw [← hyk] at hcut
    linarith [ha.1, hy.1]
  have hkib : k < ib := by
    by_contra h
    have hibk : ib ≤ k := le_of_not_gt h
    have hcut : P.cutPoint ib ≤ P.cutPoint k :=
      P.cutPoint_strictMono.monotone hibk
    rw [← hyk] at hcut
    linarith [hb.2, hy.2]
  apply Finset.mem_filter.mpr
  refine ⟨?_, hy⟩
  apply Finset.mem_image.mpr
  exact ⟨k, Finset.mem_Ico.mpr ⟨hiak, hkib⟩, hyk.symm⟩

/--
The intrinsic finite set of genuine `j`-th singularities in `(a,b)`.

The ambient finite set is obtained from one presentation, but the filter is
the intrinsic condition `multiplicity f j y ≠ 0`.  The membership theorem
below removes the presentation from the public interface.
-/
noncomputable def jthSingularPointsIn
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (a b : ℝ) : Finset ℝ := by
  classical
  exact (presentationCutPointsIn f.presentation a b).filter
    (fun y ↦ multiplicity f j y ≠ 0)

@[simp]
theorem mem_jthSingularPointsIn_iff
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    {j : ℕ} {a b y : ℝ} :
    y ∈ jthSingularPointsIn f j a b ↔
      y ∈ Ioo a b ∧ multiplicity f j y ≠ 0 := by
  classical
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hycut, hyne⟩
    exact ⟨presentationCutPointsIn_subset_Ioo f.presentation hycut, hyne⟩
  · rintro ⟨hy, hyne⟩
    rcases multiplicity_eq_zero_or_cutPoint_of_presentation
        f f.presentation j y with hzero | ⟨k, hyk, hk⟩
    · exact (hyne hzero).elim
    · apply Finset.mem_filter.mpr
      exact ⟨mem_presentationCutPointsIn_of_eq_cutPoint
        f.presentation hy hyk, hyne⟩

/-- The intrinsic finite set of `j`-th poles in `(-r,r)`. -/
noncomputable def jthPolePoints
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (r : ℝ) : Finset ℝ := by
  classical
  exact (presentationCutPointsIn f.presentation (-r) r).filter
    (fun y ↦ IsJthPole f j y)

/-- The intrinsic finite set of `j`-th roots in `(-r,r)`. -/
noncomputable def jthRootPoints
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (r : ℝ) : Finset ℝ := by
  classical
  exact (presentationCutPointsIn f.presentation (-r) r).filter
    (fun y ↦ IsJthRoot f j y)

@[simp]
theorem mem_jthPolePoints_iff
    {n : ℕ} {f : NthTropicalMeromorphicFunction n} {j : ℕ} {r y : ℝ} :
    y ∈ jthPolePoints f j r ↔ y ∈ Ioo (-r) r ∧ IsJthPole f j y := by
  classical
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hycut, hypole⟩
    exact ⟨presentationCutPointsIn_subset_Ioo f.presentation hycut, hypole⟩
  · rintro ⟨hy, hypole⟩
    have hne : multiplicity f j y ≠ 0 := ne_of_lt hypole
    rcases multiplicity_eq_zero_or_cutPoint_of_presentation
        f f.presentation j y with hzero | ⟨k, hyk, hk⟩
    · exact (hne hzero).elim
    · apply Finset.mem_filter.mpr
      exact ⟨mem_presentationCutPointsIn_of_eq_cutPoint
        f.presentation hy hyk, hypole⟩

@[simp]
theorem mem_jthRootPoints_iff
    {n : ℕ} {f : NthTropicalMeromorphicFunction n} {j : ℕ} {r y : ℝ} :
    y ∈ jthRootPoints f j r ↔ y ∈ Ioo (-r) r ∧ IsJthRoot f j y := by
  classical
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hycut, hyroot⟩
    exact ⟨presentationCutPointsIn_subset_Ioo f.presentation hycut, hyroot⟩
  · rintro ⟨hy, hyroot⟩
    have hne : multiplicity f j y ≠ 0 := ne_of_gt hyroot
    rcases multiplicity_eq_zero_or_cutPoint_of_presentation
        f f.presentation j y with hzero | ⟨k, hyk, hk⟩
    · exact (hne hzero).elim
    · apply Finset.mem_filter.mpr
      exact ⟨mem_presentationCutPointsIn_of_eq_cutPoint
        f.presentation hy hyk, hyroot⟩

/-- The paper's `j`-th integrated max-plus counting function `N⁽ʲ⁾(r,f)`. -/
def integratedCounting
    {n : ℕ} (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction n) : ℝ :=
  (1 / 2) * ∑ y ∈ jthPolePoints f j r,
    rootOrPoleMultiplicity f j y * (r - |y|) ^ j

/-- The unintegrated `j`-th pole-counting function `n⁽ʲ⁾(t,f)`: the sum of
the genuine pole multiplicities in `(-t,t)`. -/
def maxPlusCounting
    {n : ℕ} (j : ℕ) (t : ℝ) (f : NthTropicalMeromorphicFunction n) : ℝ :=
  ∑ y ∈ jthPolePoints f j t, rootOrPoleMultiplicity f j y

/-- The box attached to a pole `y` in the paper's `j`-fold integral.  Up to
measure-zero boundary choices this is `[|y|,r]^j`. -/
def countingIntegrationBox (j : ℕ) (r y : ℝ) : Set (Fin j → ℝ) :=
  Set.univ.pi fun _ ↦ Ioc |y| r

/-- A finite simple-function expansion of
`n⁽ʲ⁾(min(t₁,…,tⱼ),f)` on the integration box `[0,r]^j`.  Writing the
integrand this way makes the Tonelli/Fubini computation independent of any
enumeration of the poles. -/
def countingBoxIntegrand
    {n : ℕ} (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction n)
    (t : Fin j → ℝ) : ℝ :=
  ∑ y ∈ jthPolePoints f j r,
    (countingIntegrationBox j r y).indicator
      (fun _ ↦ rootOrPoleMultiplicity f j y) t

/-- The minimum of the `j` integration radii.  The proof argument records
the paper's range `1 ≤ j`, so the finite index set is nonempty. -/
def countingMinimumRadius (j : ℕ) (hj : 1 ≤ j) (t : Fin j → ℝ) : ℝ :=
  Finset.univ.inf'
    (show (Finset.univ : Finset (Fin j)).Nonempty from
      ⟨⟨0, hj⟩, Finset.mem_univ _⟩) t

theorem lt_countingMinimumRadius_iff
    (j : ℕ) (hj : 1 ≤ j) (t : Fin j → ℝ) (a : ℝ) :
    a < countingMinimumRadius j hj t ↔ ∀ i, a < t i := by
  unfold countingMinimumRadius
  simp

private theorem jthPolePoints_countingMinimumRadius
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (hj : 1 ≤ j) {r : ℝ} {t : Fin j → ℝ}
    (ht : t ∈ Set.univ.pi fun _ ↦ Icc 0 r) :
    jthPolePoints f j (countingMinimumRadius j hj t) =
      (jthPolePoints f j r).filter (fun y ↦ ∀ i, |y| < t i) := by
  classical
  ext y
  simp only [mem_jthPolePoints_iff, Finset.mem_filter]
  have hcoord : ∀ i, 0 ≤ t i ∧ t i ≤ r := by
    intro i
    exact (Set.mem_pi.mp ht i (Set.mem_univ i))
  constructor
  · rintro ⟨hymin, hpole⟩
    have habs : |y| < countingMinimumRadius j hj t := abs_lt.mpr hymin
    have hall : ∀ i, |y| < t i :=
      (lt_countingMinimumRadius_iff j hj t |y|).mp habs
    have hyr : y ∈ Ioo (-r) r := abs_lt.mp <|
      lt_of_lt_of_le (hall ⟨0, hj⟩) (hcoord ⟨0, hj⟩).2
    exact ⟨⟨hyr, hpole⟩, hall⟩
  · rintro ⟨⟨hyr, hpole⟩, hall⟩
    have habs : |y| < countingMinimumRadius j hj t :=
      (lt_countingMinimumRadius_iff j hj t |y|).mpr hall
    exact ⟨abs_lt.mp habs, hpole⟩

/-- On the paper's cube `[0,r]^j`, the expanded box integrand is exactly
the unintegrated counting function evaluated at the minimum radius.  This is
the missing bridge between the displayed repeated integral and the finite
sum formula. -/
theorem countingBoxIntegrand_eq_maxPlusCounting_minimum
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (hj : 1 ≤ j) {r : ℝ} {t : Fin j → ℝ}
    (ht : t ∈ Set.univ.pi fun _ ↦ Icc 0 r) :
    countingBoxIntegrand j r f t =
      maxPlusCounting j (countingMinimumRadius j hj t) f := by
  classical
  rw [maxPlusCounting,
    jthPolePoints_countingMinimumRadius f j hj ht]
  unfold countingBoxIntegrand countingIntegrationBox
  simp only [Finset.sum_filter, Set.indicator_apply, Set.mem_pi,
    Set.mem_univ, true_implies]
  apply Finset.sum_congr rfl
  intro y hy
  have hcoord : ∀ i, t i ≤ r := fun i ↦
    (Set.mem_pi.mp ht i (Set.mem_univ i)).2
  by_cases hall : ∀ i, |y| < t i
  · rw [if_pos hall]
    simp [hall, hcoord]
  · rw [if_neg hall]
    simp [hall, hcoord]

/-- The literal `j`-dimensional Lebesgue integral occurring in (3aN), after
expanding the step counting function into its finitely many pole indicators. -/
def iteratedMaxPlusCountingIntegral
    {n : ℕ} (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction n) : ℝ :=
  ∫ t : Fin j → ℝ, countingBoxIntegrand j r f t

/-- The paper's literal repeated integral over `[0,r]^j`, written as one
Lebesgue integral on the finite product. -/
def paperIteratedMaxPlusCountingIntegral
    {n : ℕ} (j : ℕ) (hj : 1 ≤ j) (r : ℝ)
    (f : NthTropicalMeromorphicFunction n) : ℝ :=
  ∫ t : Fin j → ℝ in Set.univ.pi (fun _ ↦ Icc 0 r),
    maxPlusCounting j (countingMinimumRadius j hj t) f

theorem measurableSet_countingIntegrationBox (j : ℕ) (r y : ℝ) :
    MeasurableSet (countingIntegrationBox j r y) := by
  apply MeasurableSet.pi Set.countable_univ
  intro i hi
  exact measurableSet_Ioc

theorem measurableSet_countingIntegrationCube (j : ℕ) (r : ℝ) :
    MeasurableSet (Set.univ.pi fun _ : Fin j ↦ Icc 0 r) := by
  apply MeasurableSet.pi Set.countable_univ
  intro i hi
  exact measurableSet_Icc

/-- The literal repeated-integral definition and its finite indicator
expansion agree. -/
theorem paperIteratedMaxPlusCountingIntegral_eq_iterated
    {n : ℕ} (j : ℕ) (hj : 1 ≤ j) {r : ℝ} (hr : 0 ≤ r)
    (f : NthTropicalMeromorphicFunction n) :
    paperIteratedMaxPlusCountingIntegral j hj r f =
      iteratedMaxPlusCountingIntegral j r f := by
  classical
  unfold paperIteratedMaxPlusCountingIntegral iteratedMaxPlusCountingIntegral
  rw [← MeasureTheory.integral_indicator
    (measurableSet_countingIntegrationCube j r)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Set.univ.pi fun _ : Fin j ↦ Icc 0 r
  · rw [Set.indicator_of_mem ht]
    exact (countingBoxIntegrand_eq_maxPlusCounting_minimum f j hj ht).symm
  · simp only [Set.indicator_apply, if_neg ht]
    unfold countingBoxIntegrand
    symm
    apply Finset.sum_eq_zero
    intro y hy
    simp only [Set.indicator_apply]
    rw [if_neg]
    intro hbox
    apply ht
    rw [Set.mem_pi]
    intro i hi
    have hiBox := Set.mem_pi.mp hbox i (Set.mem_univ i)
    exact ⟨(abs_nonneg y).trans hiBox.1.le, hiBox.2⟩

/-- The integral formula in (3aN), proved without ordering or repeating the
pole set: every pole contributes the volume `(r-|y|)^j` of its box. -/
theorem iteratedMaxPlusCountingIntegral_eq_sum
    {n : ℕ} (j : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (f : NthTropicalMeromorphicFunction n) :
    iteratedMaxPlusCountingIntegral j r f =
      ∑ y ∈ jthPolePoints f j r,
        rootOrPoleMultiplicity f j y * (r - |y|) ^ j := by
  classical
  unfold iteratedMaxPlusCountingIntegral countingBoxIntegrand
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y hy
    have hyr : |y| ≤ r := by
      have hrad := (mem_jthPolePoints_iff.mp hy).1
      exact (abs_lt.mpr hrad).le
    rw [MeasureTheory.integral_indicator_const _
      (measurableSet_countingIntegrationBox j r y)]
    rw [show volume.real (countingIntegrationBox j r y) = (r - |y|) ^ j by
      unfold countingIntegrationBox
      rw [show volume.real (Set.univ.pi fun _ : Fin j ↦ Ioc |y| r) =
          ∏ _ : Fin j, (r - |y|) by
        exact Real.volume_pi_Ioc_toReal (fun _ ↦ hyr)]
      simp]
    simp [mul_comm]
  · intro y hy
    rw [MeasureTheory.integrable_indicator_iff
      (measurableSet_countingIntegrationBox j r y)]
    exact MeasureTheory.integrableOn_const (by
      unfold countingIntegrationBox
      rw [Real.volume_pi_Ioc]
      simp)

/-- Sum–integral equality in the normalization of the paper. -/
theorem integratedCounting_eq_iteratedIntegral
    {n : ℕ} (j : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (f : NthTropicalMeromorphicFunction n) :
    integratedCounting j r f =
      (1 / 2) * iteratedMaxPlusCountingIntegral j r f := by
  rw [iteratedMaxPlusCountingIntegral_eq_sum j hr f]
  rfl

/-- The sum–integral equality exactly as displayed in the paper. -/
theorem integratedCounting_eq_paperIteratedIntegral
    {n : ℕ} (j : ℕ) (hj : 1 ≤ j) {r : ℝ} (hr : 0 ≤ r)
    (f : NthTropicalMeromorphicFunction n) :
    integratedCounting j r f =
      (1 / 2) * paperIteratedMaxPlusCountingIntegral j hj r f := by
  rw [paperIteratedMaxPlusCountingIntegral_eq_iterated j hj hr f,
    integratedCounting_eq_iteratedIntegral j hr f]

/-- Auxiliary integrated counting sum over `j`-th roots. -/
def integratedRootCounting
    {n : ℕ} (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction n) : ℝ :=
  (1 / 2) * ∑ y ∈ jthRootPoints f j r,
    rootOrPoleMultiplicity f j y * (r - |y|) ^ j

/--
Partial `j`-th integrated counting over an arbitrary region.  The later open,
closed, and half-open variants are obtained by supplying `Ioo`, `Icc`, `Ioc`,
or `Ico` as `region`.
-/
def partialIntegratedCounting
    {n : ℕ} (region : Set ℝ)
    [DecidablePred (fun y : ℝ ↦ y ∈ region)]
    (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction n) : ℝ :=
  (1 / 2) * ∑ y ∈ (jthPolePoints f j r).filter (fun y ↦ y ∈ region),
    rootOrPoleMultiplicity f j y * (r - |y|) ^ j

/-- Partial integrated counting over genuine `j`-th roots. -/
def partialIntegratedRootCounting
    {n : ℕ} (region : Set ℝ)
    [DecidablePred (fun y : ℝ ↦ y ∈ region)]
    (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction n) : ℝ :=
  (1 / 2) * ∑ y ∈ (jthRootPoints f j r).filter (fun y ↦ y ∈ region),
    rootOrPoleMultiplicity f j y * (r - |y|) ^ j

/-- The unnormalized weighted sum over every genuine `j`-th singularity. -/
def partialSingularityMultiplicitySum
    {n : ℕ} (region : Set ℝ)
    [DecidablePred (fun y : ℝ ↦ y ∈ region)]
    (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction n) : ℝ :=
  ∑ y ∈ (jthSingularPointsIn f j (-r) r).filter (fun y ↦ y ∈ region),
    rootOrPoleMultiplicity f j y * (r - |y|) ^ j

@[simp]
theorem partialIntegratedCounting_univ
    {n : ℕ} (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction n) :
    partialIntegratedCounting Set.univ j r f = integratedCounting j r f := by
  classical
  simp [partialIntegratedCounting, integratedCounting]

@[simp]
theorem partialIntegratedCounting_radial
    {n : ℕ} (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction n) :
    partialIntegratedCounting (Ioo (-r) r) j r f = integratedCounting j r f := by
  classical
  simp only [partialIntegratedCounting, integratedCounting]
  congr 2
  ext y
  constructor
  · intro hy
    exact (Finset.mem_filter.mp hy).1
  · intro hy
    exact Finset.mem_filter.mpr ⟨hy, (mem_jthPolePoints_iff.mp hy).1⟩

theorem partialIntegratedCounting_mono_region
    {n : ℕ} {A B : Set ℝ}
    [DecidablePred (fun y : ℝ ↦ y ∈ A)]
    [DecidablePred (fun y : ℝ ↦ y ∈ B)]
    (hAB : A ⊆ B)
    (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction n) :
    partialIntegratedCounting A j r f ≤ partialIntegratedCounting B j r f := by
  classical
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro y hy
    simp only [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, hAB hy.2⟩
  · intro y hyB hyA
    have hyr := (mem_jthPolePoints_iff.mp (Finset.mem_filter.mp hyB).1).1
    have habs : |y| < r := (abs_lt).2 hyr
    have hweight : 0 ≤ r - |y| := sub_nonneg.mpr habs.le
    exact mul_nonneg (abs_nonneg _) (pow_nonneg hweight _)

theorem partialIntegratedCounting_le_integratedCounting
    {n : ℕ} (A : Set ℝ) [DecidablePred (fun y : ℝ ↦ y ∈ A)]
    (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction n) :
    partialIntegratedCounting A j r f ≤ integratedCounting j r f := by
  rw [← partialIntegratedCounting_univ j r f]
  exact partialIntegratedCounting_mono_region (Set.subset_univ A) j r f

theorem integratedCounting_nonneg
    {n : ℕ} (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction n) :
    0 ≤ integratedCounting j r f := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply Finset.sum_nonneg
  intro y hy
  have hyr := (mem_jthPolePoints_iff.mp hy).1
  have habs : |y| < r := (abs_lt).2 hyr
  have hweight : 0 ≤ r - |y| := sub_nonneg.mpr habs.le
  exact mul_nonneg (abs_nonneg _) (pow_nonneg hweight _)

theorem integratedRootCounting_nonneg
    {n : ℕ} (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction n) :
    0 ≤ integratedRootCounting j r f := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply Finset.sum_nonneg
  intro y hy
  have hyr := (mem_jthRootPoints_iff.mp hy).1
  have habs : |y| < r := (abs_lt).2 hyr
  have hweight : 0 ≤ r - |y| := sub_nonneg.mpr habs.le
  exact mul_nonneg (abs_nonneg _) (pow_nonneg hweight _)

theorem partialIntegratedCounting_nonneg
    {n : ℕ} (A : Set ℝ) [DecidablePred (fun y : ℝ ↦ y ∈ A)]
    (j : ℕ) (r : ℝ)
    (f : NthTropicalMeromorphicFunction n) :
    0 ≤ partialIntegratedCounting A j r f := by
  classical
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply Finset.sum_nonneg
  intro y hy
  have hyr := (mem_jthPolePoints_iff.mp (Finset.mem_filter.mp hy).1).1
  have habs : |y| < r := (abs_lt).2 hyr
  have hweight : 0 ≤ r - |y| := sub_nonneg.mpr habs.le
  exact mul_nonneg (abs_nonneg _) (pow_nonneg hweight _)

/-- A partial pole-counting function is monotone in the radius.  The region
is fixed; increasing the radius can only add genuine poles, and increases
the nonnegative radial weight of every pole already present. -/
theorem partialIntegratedCounting_mono_radius
    {n : ℕ} (A : Set ℝ) [DecidablePred (fun y : ℝ ↦ y ∈ A)]
    (j : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (f : NthTropicalMeromorphicFunction n) :
    partialIntegratedCounting A j a f ≤
      partialIntegratedCounting A j b f := by
  classical
  let sa := (jthPolePoints f j a).filter (fun y ↦ y ∈ A)
  let sb := (jthPolePoints f j b).filter (fun y ↦ y ∈ A)
  have hsab : sa ⊆ sb := by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hya, hyA⟩
    rcases mem_jthPolePoints_iff.mp hya with ⟨hyr, hypole⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_jthPolePoints_iff.mpr ⟨?_, hypole⟩, hyA⟩
    constructor <;> linarith [hyr.1, hyr.2]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    (∑ y ∈ sa, rootOrPoleMultiplicity f j y * (a - |y|) ^ j) ≤
        ∑ y ∈ sa, rootOrPoleMultiplicity f j y * (b - |y|) ^ j := by
      apply Finset.sum_le_sum
      intro y hy
      have hya := (mem_jthPolePoints_iff.mp (Finset.mem_filter.mp hy).1).1
      have hyabs : |y| ≤ a := (abs_lt.mpr hya).le
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact pow_le_pow_left₀ (sub_nonneg.mpr hyabs) (sub_le_sub_right hab _) j
    _ ≤ ∑ y ∈ sb, rootOrPoleMultiplicity f j y * (b - |y|) ^ j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsab
      intro y hyb hya
      have hyr := (mem_jthPolePoints_iff.mp (Finset.mem_filter.mp hyb).1).1
      have hyabs : |y| ≤ b := (abs_lt.mpr hyr).le
      exact mul_nonneg (abs_nonneg _) (pow_nonneg (sub_nonneg.mpr hyabs) _)

/-- A partial root-counting function is monotone in the radius. -/
theorem partialIntegratedRootCounting_mono_radius
    {n : ℕ} (A : Set ℝ) [DecidablePred (fun y : ℝ ↦ y ∈ A)]
    (j : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (f : NthTropicalMeromorphicFunction n) :
    partialIntegratedRootCounting A j a f ≤
      partialIntegratedRootCounting A j b f := by
  classical
  let sa := (jthRootPoints f j a).filter (fun y ↦ y ∈ A)
  let sb := (jthRootPoints f j b).filter (fun y ↦ y ∈ A)
  have hsab : sa ⊆ sb := by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hya, hyA⟩
    rcases mem_jthRootPoints_iff.mp hya with ⟨hyr, hyroot⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_jthRootPoints_iff.mpr ⟨?_, hyroot⟩, hyA⟩
    constructor <;> linarith [hyr.1, hyr.2]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    (∑ y ∈ sa, rootOrPoleMultiplicity f j y * (a - |y|) ^ j) ≤
        ∑ y ∈ sa, rootOrPoleMultiplicity f j y * (b - |y|) ^ j := by
      apply Finset.sum_le_sum
      intro y hy
      have hya := (mem_jthRootPoints_iff.mp (Finset.mem_filter.mp hy).1).1
      have hyabs : |y| ≤ a := (abs_lt.mpr hya).le
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact pow_le_pow_left₀ (sub_nonneg.mpr hyabs) (sub_le_sub_right hab _) j
    _ ≤ ∑ y ∈ sb, rootOrPoleMultiplicity f j y * (b - |y|) ^ j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsab
      intro y hyb hya
      have hyr := (mem_jthRootPoints_iff.mp (Finset.mem_filter.mp hyb).1).1
      have hyabs : |y| ≤ b := (abs_lt.mpr hyr).le
      exact mul_nonneg (abs_nonneg _) (pow_nonneg (sub_nonneg.mpr hyabs) _)

/-- A region and its complement partition the full root count. -/
theorem partialIntegratedRootCounting_add_compl
    {n : ℕ} (A : Set ℝ) [DecidablePred (fun y : ℝ ↦ y ∈ A)]
    [DecidablePred (fun y : ℝ ↦ y ∈ Aᶜ)]
    (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction n) :
    partialIntegratedRootCounting A j r f +
        partialIntegratedRootCounting Aᶜ j r f =
      integratedRootCounting j r f := by
  classical
  simp only [partialIntegratedRootCounting, integratedRootCounting]
  rw [← mul_add]
  congr 1
  simpa only [Set.mem_compl_iff] using
    (Finset.sum_filter_add_sum_filter_not
      (jthRootPoints f j r)
      (fun y ↦ y ∈ A)
      (fun y ↦ rootOrPoleMultiplicity f j y * (r - |y|) ^ j))

/-- The full pole-counting function is monotone in the radius. -/
theorem integratedCounting_mono_radius
    {n : ℕ} (j : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (f : NthTropicalMeromorphicFunction n) :
    integratedCounting j a f ≤ integratedCounting j b f := by
  rw [← partialIntegratedCounting_univ j a f,
    ← partialIntegratedCounting_univ j b f]
  exact partialIntegratedCounting_mono_radius Set.univ j ha hab f

/-- The full root-counting function is monotone in the radius. -/
theorem integratedRootCounting_mono_radius
    {n : ℕ} (j : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (f : NthTropicalMeromorphicFunction n) :
    integratedRootCounting j a f ≤ integratedRootCounting j b f := by
  simpa [partialIntegratedRootCounting, integratedRootCounting] using
    (partialIntegratedRootCounting_mono_radius Set.univ j ha hab f)

/-- The n-th max-plus characteristic `T(r,f)`. -/
def characteristic
    {n : ℕ} (r : ℝ) (f : NthTropicalMeromorphicFunction n) : ℝ :=
  proximity r f + ∑ j ∈ Finset.Icc 1 n, integratedCounting j r f

theorem maxPlusPositivePart_nonneg (x : ℝ) : 0 ≤ maxPlusPositivePart x :=
  le_max_right _ _

theorem proximity_nonneg
    {n : ℕ} (r : ℝ) (f : NthTropicalMeromorphicFunction n) :
    0 ≤ proximity r f := by
  simp only [proximity]
  apply div_nonneg
  · exact add_nonneg (maxPlusPositivePart_nonneg _) (maxPlusPositivePart_nonneg _)
  · norm_num

theorem characteristic_nonneg
    {n : ℕ} (r : ℝ) (f : NthTropicalMeromorphicFunction n) :
    0 ≤ characteristic r f := by
  apply add_nonneg (proximity_nonneg r f)
  apply Finset.sum_nonneg
  intro j hj
  exact integratedCounting_nonneg j r f

theorem maxPlusPositivePart_sub_neg (x : ℝ) :
    maxPlusPositivePart x - maxPlusPositivePart (-x) = x := by
  by_cases hx : 0 ≤ x
  · simp [maxPlusPositivePart, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    simp [maxPlusPositivePart, max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]

theorem maxPlusPositivePart_add_neg_eq_abs (x : ℝ) :
    maxPlusPositivePart x + maxPlusPositivePart (-x) = |x| := by
  rcases le_total 0 x with hx | hx
  · simp [maxPlusPositivePart, max_eq_left hx,
      max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]
  · simp [maxPlusPositivePart, max_eq_right hx,
      max_eq_left (neg_nonneg.mpr hx), abs_of_nonpos hx]

/-- The endpoint estimate used twice in the displayed shift lemma. -/
theorem abs_apply_le_two_mul_proximity_pair
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (r : ℝ) :
    |f r| ≤ 2 * (proximity r f + proximity r (-f)) := by
  have hr := maxPlusPositivePart_add_neg_eq_abs (f r)
  have hnegR := maxPlusPositivePart_add_neg_eq_abs (f (-r))
  have hnonneg : 0 ≤ |f (-r)| := abs_nonneg _
  simp only [proximity, NthTropicalMeromorphicFunction.neg_apply] at ⊢
  linarith

theorem integratedCountingSum_le_characteristic
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (r : ℝ) :
    (∑ j ∈ Finset.Icc 1 n, integratedCounting j r f) ≤
      characteristic r f := by
  simp only [characteristic]
  exact le_add_of_nonneg_left (proximity_nonneg r f)

theorem pairedIntegratedCountingSum_le_pairedCharacteristic
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (r : ℝ) :
    (∑ j ∈ Finset.Icc 1 n,
        (integratedCounting j r f + integratedCounting j r (-f))) ≤
      characteristic r f + characteristic r (-f) := by
  rw [Finset.sum_add_distrib]
  simp only [characteristic]
  have hf := proximity_nonneg r f
  have hneg := proximity_nonneg r (-f)
  linarith

theorem pairedProximity_le_pairedCharacteristic
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (r : ℝ) :
    proximity r f + proximity r (-f) ≤
      characteristic r f + characteristic r (-f) := by
  simp only [characteristic]
  have hf : 0 ≤ ∑ j ∈ Finset.Icc 1 n, integratedCounting j r f := by
    apply Finset.sum_nonneg
    intro j hj
    exact integratedCounting_nonneg j r f
  have hneg : 0 ≤ ∑ j ∈ Finset.Icc 1 n, integratedCounting j r (-f) := by
    apply Finset.sum_nonneg
    intro j hj
    exact integratedCounting_nonneg j r (-f)
  linarith

theorem pairedPartialIntegratedCountingSum_le_pairedCharacteristic
    {n : ℕ} (A : Set ℝ) [DecidablePred (fun y : ℝ ↦ y ∈ A)]
    (f : NthTropicalMeromorphicFunction n) (r : ℝ) :
    (∑ j ∈ Finset.Icc 1 n,
        (partialIntegratedCounting A j r f +
          partialIntegratedCounting A j r (-f))) ≤
      characteristic r f + characteristic r (-f) := by
  calc
    (∑ j ∈ Finset.Icc 1 n,
        (partialIntegratedCounting A j r f +
          partialIntegratedCounting A j r (-f))) ≤
        ∑ j ∈ Finset.Icc 1 n,
          (integratedCounting j r f + integratedCounting j r (-f)) := by
      apply Finset.sum_le_sum
      intro j hj
      linarith [partialIntegratedCounting_le_integratedCounting A j r f,
        partialIntegratedCounting_le_integratedCounting A j r (-f)]
    _ ≤ characteristic r f + characteristic r (-f) :=
      pairedIntegratedCountingSum_le_pairedCharacteristic f r

theorem proximity_sub_neg
    {n : ℕ} (r : ℝ) (f : NthTropicalMeromorphicFunction n) :
    proximity r f - proximity r (-f) = (f r + f (-r)) / 2 := by
  simp only [proximity, NthTropicalMeromorphicFunction.neg_apply]
  linear_combination (1 / 2) * maxPlusPositivePart_sub_neg (f r) +
    (1 / 2) * maxPlusPositivePart_sub_neg (f (-r))

@[simp]
theorem jthPolePoints_neg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (r : ℝ) :
    jthPolePoints (-f) j r = jthRootPoints f j r := by
  classical
  ext y
  simp

@[simp]
theorem jthRootPoints_neg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (r : ℝ) :
    jthRootPoints (-f) j r = jthPolePoints f j r := by
  classical
  ext y
  simp

@[simp]
theorem integratedCounting_neg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (r : ℝ) :
    integratedCounting j r (-f) = integratedRootCounting j r f := by
  simp [integratedCounting, integratedRootCounting]

@[simp]
theorem integratedRootCounting_neg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (r : ℝ) :
    integratedRootCounting j r (-f) = integratedCounting j r f := by
  simp [integratedCounting, integratedRootCounting]

@[simp]
theorem partialIntegratedCounting_neg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (region : Set ℝ) [DecidablePred (fun y : ℝ ↦ y ∈ region)]
    (j : ℕ) (r : ℝ) :
    partialIntegratedCounting region j r (-f) =
      partialIntegratedRootCounting region j r f := by
  classical
  simp [partialIntegratedCounting, partialIntegratedRootCounting]

private theorem filtered_jthSingularPointsIn_eq_poles_union_roots
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (region : Set ℝ) [DecidablePred (fun y : ℝ ↦ y ∈ region)]
    (j : ℕ) (r : ℝ) :
    (jthSingularPointsIn f j (-r) r).filter (fun y ↦ y ∈ region) =
      ((jthPolePoints f j r).filter (fun y ↦ y ∈ region)) ∪
        ((jthRootPoints f j r).filter (fun y ↦ y ∈ region)) := by
  classical
  ext y
  simp only [Finset.mem_filter, Finset.mem_union,
    mem_jthSingularPointsIn_iff, mem_jthPolePoints_iff,
    mem_jthRootPoints_iff]
  constructor
  · rintro ⟨⟨hyr, hyne⟩, hyregion⟩
    rcases lt_or_gt_of_ne hyne with hneg | hpos
    · exact Or.inl ⟨⟨hyr, hneg⟩, hyregion⟩
    · exact Or.inr ⟨⟨hyr, hpos⟩, hyregion⟩
  · rintro (⟨⟨hyr, hpole⟩, hyregion⟩ | ⟨⟨hyr, hroot⟩, hyregion⟩)
    · exact ⟨⟨hyr, ne_of_lt hpole⟩, hyregion⟩
    · exact ⟨⟨hyr, ne_of_gt hroot⟩, hyregion⟩

/--
The weighted sum over all genuine singularities is exactly twice the sum of
the partial pole counts of `f` and `-f`.  This is the counting conversion
used, but left implicit, in the displayed shift proof.
-/
theorem partialSingularityMultiplicitySum_eq_two_mul_counting_pair
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (region : Set ℝ) [DecidablePred (fun y : ℝ ↦ y ∈ region)]
    (j : ℕ) (r : ℝ) :
    partialSingularityMultiplicitySum region j r f =
      2 * (partialIntegratedCounting region j r f +
        partialIntegratedCounting region j r (-f)) := by
  classical
  let poles := (jthPolePoints f j r).filter (fun y ↦ y ∈ region)
  let roots := (jthRootPoints f j r).filter (fun y ↦ y ∈ region)
  have hdisjoint : Disjoint poles roots := by
    apply Finset.disjoint_left.mpr
    intro y hypole hyroot
    have hpole : IsJthPole f j y :=
      (mem_jthPolePoints_iff.mp (Finset.mem_filter.mp hypole).1).2
    have hroot : IsJthRoot f j y :=
      (mem_jthRootPoints_iff.mp (Finset.mem_filter.mp hyroot).1).2
    exact (not_lt_of_ge hroot.le) hpole
  rw [partialSingularityMultiplicitySum,
    filtered_jthSingularPointsIn_eq_poles_union_roots]
  rw [Finset.sum_union hdisjoint]
  rw [partialIntegratedCounting_neg f region j r]
  simp only [partialIntegratedCounting, partialIntegratedRootCounting]
  change
    (∑ y ∈ poles, rootOrPoleMultiplicity f j y * (r - |y|) ^ j) +
        ∑ y ∈ roots, rootOrPoleMultiplicity f j y * (r - |y|) ^ j =
      2 * ((1 / 2) *
          ∑ y ∈ poles, rootOrPoleMultiplicity f j y * (r - |y|) ^ j +
        (1 / 2) *
          ∑ y ∈ roots, rootOrPoleMultiplicity f j y * (r - |y|) ^ j)
  ring

/--
On a positive interval contained in `(-ρ,ρ)`, the weights in Lemma 3.1
are exactly the weights in partial counting: `|y| = y`.  Thus the absolute
intrinsic jump sum is twice the paired partial count of `f` and `-f`.
-/
theorem positiveInterval_singularitySum_eq_two_mul_counting_pair
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) {a b ρ : ℝ}
    (ha : 0 < a) (hab : a < b) (hbρ : b ≤ ρ) :
    (∑ y ∈ jthSingularPointsIn f j a b,
        |multiplicity f j y| * (ρ - y) ^ j) =
      2 * (partialIntegratedCounting (Ioo a b) j ρ f +
        partialIntegratedCounting (Ioo a b) j ρ (-f)) := by
  classical
  have hset :
      (jthSingularPointsIn f j (-ρ) ρ).filter (fun y ↦ y ∈ Ioo a b) =
        jthSingularPointsIn f j a b := by
    ext y
    simp only [Finset.mem_filter, mem_jthSingularPointsIn_iff]
    constructor
    · rintro ⟨⟨hyρ, hyne⟩, hyab⟩
      exact ⟨hyab, hyne⟩
    · rintro ⟨hyab, hyne⟩
      have hρpos : 0 < ρ := ha.trans (hab.trans_le hbρ)
      exact ⟨⟨⟨(neg_lt_zero.mpr hρpos).trans (ha.trans hyab.1),
          hyab.2.trans_le hbρ⟩, hyne⟩, hyab⟩
  rw [← partialSingularityMultiplicitySum_eq_two_mul_counting_pair
    f (Ioo a b) j ρ]
  simp only [partialSingularityMultiplicitySum]
  rw [hset]
  apply Finset.sum_congr rfl
  intro y hy
  have hypos : 0 < y := ha.trans (mem_jthSingularPointsIn_iff.mp hy).1.1
  simp [rootOrPoleMultiplicity, abs_of_pos hypos]

theorem positiveInterval_singularitySums_le_two_mul_characteristicPair
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {a b ρ : ℝ} (ha : 0 < a) (hab : a < b) (hbρ : b ≤ ρ) :
    (∑ j ∈ Finset.Icc 1 n, ∑ y ∈ jthSingularPointsIn f j a b,
        |multiplicity f j y| * (ρ - y) ^ j) ≤
      2 * (characteristic ρ f + characteristic ρ (-f)) := by
  calc
    (∑ j ∈ Finset.Icc 1 n, ∑ y ∈ jthSingularPointsIn f j a b,
        |multiplicity f j y| * (ρ - y) ^ j) =
        ∑ j ∈ Finset.Icc 1 n,
          2 * (partialIntegratedCounting (Ioo a b) j ρ f +
            partialIntegratedCounting (Ioo a b) j ρ (-f)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact positiveInterval_singularitySum_eq_two_mul_counting_pair
        f j ha hab hbρ
    _ = 2 * (∑ j ∈ Finset.Icc 1 n,
          (partialIntegratedCounting (Ioo a b) j ρ f +
            partialIntegratedCounting (Ioo a b) j ρ (-f))) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (characteristic ρ f + characteristic ρ (-f)) := by
      exact mul_le_mul_of_nonneg_left
        (pairedPartialIntegratedCountingSum_le_pairedCharacteristic
          (Ioo a b) f ρ) (by norm_num)

/-- Negative-interval counterpart of
`positiveInterval_singularitySum_eq_two_mul_counting_pair`. -/
theorem negativeInterval_singularitySum_eq_two_mul_counting_pair
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) {a b ρ : ℝ}
    (hρa : -ρ ≤ a) (hab : a < b) (hb : b < 0) :
    (∑ y ∈ jthSingularPointsIn f j a b,
        |multiplicity f j y| * (ρ + y) ^ j) =
      2 * (partialIntegratedCounting (Ioo a b) j ρ f +
        partialIntegratedCounting (Ioo a b) j ρ (-f)) := by
  classical
  have hρpos : 0 < ρ := by linarith
  have hset :
      (jthSingularPointsIn f j (-ρ) ρ).filter (fun y ↦ y ∈ Ioo a b) =
        jthSingularPointsIn f j a b := by
    ext y
    simp only [Finset.mem_filter, mem_jthSingularPointsIn_iff]
    constructor
    · rintro ⟨⟨hyρ, hyne⟩, hyab⟩
      exact ⟨hyab, hyne⟩
    · rintro ⟨hyab, hyne⟩
      exact ⟨⟨⟨hρa.trans_lt hyab.1,
          hyab.2.trans (hb.trans (by positivity))⟩, hyne⟩, hyab⟩
  rw [← partialSingularityMultiplicitySum_eq_two_mul_counting_pair
    f (Ioo a b) j ρ]
  simp only [partialSingularityMultiplicitySum]
  rw [hset]
  apply Finset.sum_congr rfl
  intro y hy
  have hyneg : y < 0 :=
    (mem_jthSingularPointsIn_iff.mp hy).1.2.trans hb
  simp [rootOrPoleMultiplicity, abs_of_neg hyneg]

theorem negativeInterval_singularitySums_le_two_mul_characteristicPair
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {a b ρ : ℝ} (hρa : -ρ ≤ a) (hab : a < b) (hb : b < 0) :
    (∑ j ∈ Finset.Icc 1 n, ∑ y ∈ jthSingularPointsIn f j a b,
        |multiplicity f j y| * (ρ + y) ^ j) ≤
      2 * (characteristic ρ f + characteristic ρ (-f)) := by
  calc
    (∑ j ∈ Finset.Icc 1 n, ∑ y ∈ jthSingularPointsIn f j a b,
        |multiplicity f j y| * (ρ + y) ^ j) =
        ∑ j ∈ Finset.Icc 1 n,
          2 * (partialIntegratedCounting (Ioo a b) j ρ f +
            partialIntegratedCounting (Ioo a b) j ρ (-f)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact negativeInterval_singularitySum_eq_two_mul_counting_pair
        f j hρa hab hb
    _ = 2 * (∑ j ∈ Finset.Icc 1 n,
          (partialIntegratedCounting (Ioo a b) j ρ f +
            partialIntegratedCounting (Ioo a b) j ρ (-f))) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (characteristic ρ f + characteristic ρ (-f)) := by
      exact mul_le_mul_of_nonneg_left
        (pairedPartialIntegratedCountingSum_le_pairedCharacteristic
          (Ioo a b) f ρ) (by norm_num)

/-! ## Reflection invariance -/

@[simp]
theorem isJthPole_reflect_iff
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (x : ℝ) :
    IsJthPole f.reflect j x ↔ IsJthPole f j (-x) := by
  simp [IsJthPole]

@[simp]
theorem isJthRoot_reflect_iff
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (x : ℝ) :
    IsJthRoot f.reflect j x ↔ IsJthRoot f j (-x) := by
  simp [IsJthRoot]

@[simp]
theorem rootOrPoleMultiplicity_reflect
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (x : ℝ) :
    rootOrPoleMultiplicity f.reflect j x =
      rootOrPoleMultiplicity f j (-x) := by
  simp [rootOrPoleMultiplicity]

theorem jthPolePoints_reflect
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (r : ℝ) :
    jthPolePoints f.reflect j r =
      (jthPolePoints f j r).image (fun x ↦ -x) := by
  classical
  ext x
  constructor
  · intro hx
    rcases mem_jthPolePoints_iff.mp hx with ⟨hxr, hpole⟩
    apply Finset.mem_image.mpr
    refine ⟨-x, ?_, by simp⟩
    apply mem_jthPolePoints_iff.mpr
    constructor
    · constructor <;> linarith [hxr.1, hxr.2]
    · simpa using hpole
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    rcases mem_jthPolePoints_iff.mp hy with ⟨hyr, hpole⟩
    apply mem_jthPolePoints_iff.mpr
    constructor
    · constructor <;> linarith [hyr.1, hyr.2]
    · simpa using hpole

theorem jthRootPoints_reflect
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (r : ℝ) :
    jthRootPoints f.reflect j r =
      (jthRootPoints f j r).image (fun x ↦ -x) := by
  classical
  ext x
  constructor
  · intro hx
    rcases mem_jthRootPoints_iff.mp hx with ⟨hxr, hroot⟩
    apply Finset.mem_image.mpr
    refine ⟨-x, ?_, by simp⟩
    apply mem_jthRootPoints_iff.mpr
    constructor
    · constructor <;> linarith [hxr.1, hxr.2]
    · simpa using hroot
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    rcases mem_jthRootPoints_iff.mp hy with ⟨hyr, hroot⟩
    apply mem_jthRootPoints_iff.mpr
    constructor
    · constructor <;> linarith [hyr.1, hyr.2]
    · simpa using hroot

@[simp]
theorem integratedCounting_reflect
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (r : ℝ) :
    integratedCounting j r f.reflect = integratedCounting j r f := by
  classical
  rw [integratedCounting, integratedCounting, jthPolePoints_reflect]
  rw [Finset.sum_image]
  · simp
  · intro x hx y hy hxy
    exact neg_injective hxy

@[simp]
theorem integratedRootCounting_reflect
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (r : ℝ) :
    integratedRootCounting j r f.reflect = integratedRootCounting j r f := by
  classical
  rw [integratedRootCounting, integratedRootCounting, jthRootPoints_reflect]
  rw [Finset.sum_image]
  · simp
  · intro x hx y hy hxy
    exact neg_injective hxy

@[simp]
theorem proximity_reflect
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (r : ℝ) :
    proximity r f.reflect = proximity r f := by
  simp [proximity, add_comm]

@[simp]
theorem characteristic_reflect
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (r : ℝ) :
    characteristic r f.reflect = characteristic r f := by
  simp [characteristic]

end

end NthTropicalNevanlinna
