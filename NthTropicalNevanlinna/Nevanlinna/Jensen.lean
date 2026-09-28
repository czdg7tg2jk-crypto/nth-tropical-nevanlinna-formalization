import NthTropicalNevanlinna.Nevanlinna.Counting
import NthTropicalNevanlinna.PoissonJensen.Main

/-!
# Intrinsic Jensen counting sums

This file identifies the finite sums in the proof of Theorem 3.3 with the
presentation-independent root and pole sets used by the counting functions.
It then derives Theorem 3.5.
-/

open Set

namespace NthTropicalNevanlinna

noncomputable section

open scoped BigOperators

private theorem zero_mem_radialInterval {r : ℝ} (hr : 0 < r) :
    (0 : ℝ) ∈ Ioo (-r) r := by
  constructor <;> linarith

/-- Every point of nonzero multiplicity in the radial interval occurs in a
complete Poisson--Jensen local presentation. -/
theorem exists_poissonJensenPoint_of_multiplicity_ne_zero
    {n : ℕ} {f : NthTropicalMeromorphicFunction n} {r x : ℝ}
    (data : PoissonJensenLocalData f r x) (hx : x ∈ Ioo (-r) r)
    {j : ℕ} {y : ℝ} (hy : y ∈ Ioo (-r) r)
    (hne : multiplicity f j y ≠ 0) :
    ∃ q : PoissonJensenPoint data.mLeft data.mRight,
      poissonJensenPointValue data.leftPresentation data.rightPresentation q = y := by
  rcases multiplicity_eq_zero_or_cutPoint_of_presentation
      f f.presentation j y with hzero | ⟨k, hycut, hk⟩
  · exact (hne hzero).elim
  · rcases lt_trichotomy y x with hyx | hyx | hxy
    · obtain ⟨i, hi⟩ := data.left_contains_globalCut k
        (by simpa [← hycut] using hy.1)
        (by simpa [← hycut] using hyx)
      exact ⟨.inl i, by simpa [poissonJensenPointValue, hycut] using hi⟩
    · exact ⟨.inr none, by simpa [poissonJensenPointValue] using hyx.symm⟩
    · obtain ⟨i, hi⟩ := data.right_contains_globalCut k
        (by simpa [← hycut] using hxy)
        (by simpa [← hycut] using hy.2)
      exact ⟨.inr (some i), by simpa [poissonJensenPointValue, hycut] using hi⟩

private theorem image_jensenRootPoints_eq
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r) (j : ℕ) :
    let data := jensenLocalData f hr
    Finset.image
        (poissonJensenPointValue data.leftPresentation data.rightPresentation)
        (jensenRootPoints f data.leftPresentation data.rightPresentation j) =
      jthRootPoints f j r := by
  classical
  let data := jensenLocalData f hr
  let value := poissonJensenPointValue data.leftPresentation data.rightPresentation
  change Finset.image value
      (jensenRootPoints f data.leftPresentation data.rightPresentation j) = _
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
    have hroot : IsJthRoot f j (value q) := by
      simpa [jensenRootPoints] using hq
    exact mem_jthRootPoints_iff.mpr
      ⟨poissonJensenPointValue_mem data.leftPresentation data.rightPresentation
        (zero_mem_radialInterval hr) q, hroot⟩
  · intro hy
    rcases mem_jthRootPoints_iff.mp hy with ⟨hyr, hroot⟩
    obtain ⟨q, hqy⟩ := exists_poissonJensenPoint_of_multiplicity_ne_zero
      data (zero_mem_radialInterval hr) hyr (ne_of_gt hroot)
    apply Finset.mem_image.mpr
    refine ⟨q, ?_, hqy⟩
    simp [jensenRootPoints, hqy, hroot]

private theorem image_jensenPolePoints_eq
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r) (j : ℕ) :
    let data := jensenLocalData f hr
    Finset.image
        (poissonJensenPointValue data.leftPresentation data.rightPresentation)
        (jensenPolePoints f data.leftPresentation data.rightPresentation j) =
      jthPolePoints f j r := by
  classical
  let data := jensenLocalData f hr
  let value := poissonJensenPointValue data.leftPresentation data.rightPresentation
  change Finset.image value
      (jensenPolePoints f data.leftPresentation data.rightPresentation j) = _
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
    have hpole : IsJthPole f j (value q) := by
      simpa [jensenPolePoints] using hq
    exact mem_jthPolePoints_iff.mpr
      ⟨poissonJensenPointValue_mem data.leftPresentation data.rightPresentation
        (zero_mem_radialInterval hr) q, hpole⟩
  · intro hy
    rcases mem_jthPolePoints_iff.mp hy with ⟨hyr, hpole⟩
    obtain ⟨q, hqy⟩ := exists_poissonJensenPoint_of_multiplicity_ne_zero
      data (zero_mem_radialInterval hr) hyr (ne_of_lt hpole)
    apply Finset.mem_image.mpr
    refine ⟨q, ?_, hqy⟩
    simp [jensenPolePoints, hqy, hpole]

private theorem jensenRootSum_eq_intrinsic
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r) (j : ℕ) :
    let data := jensenLocalData f hr
    (∑ q ∈ jensenRootPoints f data.leftPresentation data.rightPresentation j,
      rootOrPoleMultiplicity f j
          (poissonJensenPointValue data.leftPresentation data.rightPresentation q) *
        (r - |poissonJensenPointValue
          data.leftPresentation data.rightPresentation q|) ^ j) =
      ∑ y ∈ jthRootPoints f j r,
        rootOrPoleMultiplicity f j y * (r - |y|) ^ j := by
  classical
  let data := jensenLocalData f hr
  let value := poissonJensenPointValue data.leftPresentation data.rightPresentation
  let weight : ℝ → ℝ := fun y ↦
    rootOrPoleMultiplicity f j y * (r - |y|) ^ j
  have hsum := Finset.sum_image (f := weight)
    (s := jensenRootPoints f data.leftPresentation data.rightPresentation j)
    (g := value)
    (poissonJensenPointValue_injective
      data.leftPresentation data.rightPresentation).injOn
  rw [image_jensenRootPoints_eq f hr j] at hsum
  exact hsum.symm

private theorem jensenPoleSum_eq_intrinsic
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r) (j : ℕ) :
    let data := jensenLocalData f hr
    (∑ q ∈ jensenPolePoints f data.leftPresentation data.rightPresentation j,
      rootOrPoleMultiplicity f j
          (poissonJensenPointValue data.leftPresentation data.rightPresentation q) *
        (r - |poissonJensenPointValue
          data.leftPresentation data.rightPresentation q|) ^ j) =
      ∑ y ∈ jthPolePoints f j r,
        rootOrPoleMultiplicity f j y * (r - |y|) ^ j := by
  classical
  let data := jensenLocalData f hr
  let value := poissonJensenPointValue data.leftPresentation data.rightPresentation
  let weight : ℝ → ℝ := fun y ↦
    rootOrPoleMultiplicity f j y * (r - |y|) ^ j
  have hsum := Finset.sum_image (f := weight)
    (s := jensenPolePoints f data.leftPresentation data.rightPresentation j)
    (g := value)
    (poissonJensenPointValue_injective
      data.leftPresentation data.rightPresentation).injOn
  rw [image_jensenPolePoints_eq f hr j] at hsum
  exact hsum.symm

/-- The root sum in Jensen's formula is twice the integrated root count. -/
theorem jensenRootMultiplicitySum_eq
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r) :
    jensenRootMultiplicitySum f hr =
      2 * ∑ j ∈ Finset.Icc 1 n, integratedRootCounting j r f := by
  classical
  rw [Finset.mul_sum]
  simp only [jensenRootMultiplicitySum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [jensenRootSum_eq_intrinsic f hr j]
  simp [integratedRootCounting]

/-- The pole sum in Jensen's formula is twice the integrated pole count. -/
theorem jensenPoleMultiplicitySum_eq
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r) :
    jensenPoleMultiplicitySum f hr =
      2 * ∑ j ∈ Finset.Icc 1 n, integratedCounting j r f := by
  classical
  rw [Finset.mul_sum]
  simp only [jensenPoleMultiplicitySum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [jensenPoleSum_eq_intrinsic f hr j]
  simp [integratedCounting]

/-- Theorem 3.5: the characteristic of `f` and `-f` differ by `f(0)`. -/
theorem characteristic_eq_neg_add_at_zero
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r : ℝ} (hr : 0 < r) :
    characteristic r f = characteristic r (-f) + f 0 := by
  have hj := jensenFormula f hr
  rw [jensenRootMultiplicitySum_eq f hr,
    jensenPoleMultiplicitySum_eq f hr] at hj
  simp only [characteristic, integratedCounting_neg]
  have hm := proximity_sub_neg r f
  linear_combination hm - hj

end

end NthTropicalNevanlinna
