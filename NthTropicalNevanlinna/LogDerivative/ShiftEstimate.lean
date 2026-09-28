import NthTropicalNevanlinna.LogDerivative.CharacteristicMonotonicity
import NthTropicalNevanlinna.Nevanlinna.Jensen
import NthTropicalNevanlinna.PoissonJensen.IntrinsicTelescoping

/-!
# Pointwise shift estimate

This file records the exact conclusion of the displayed shift lemma and
formalizes the two intrinsic Lemma 3.1 expansions, their weighted estimates,
the reflection reductions, and the final Jensen/numerical assembly.  Its only
remaining imported mathematical dependency is the order-zero monotonicity of
the characteristic asserted by the preceding characteristic lemma.
-/

namespace NthTropicalNevanlinna

noncomputable section

open Filter Set
open scoped Topology

/-- The auxiliary radius `ρ = (α+1)(r+|c|)/2` in the paper. -/
def shiftEstimateRadius (α c r : ℝ) : ℝ :=
  (α + 1) * (r + |c|) / 2

/-- The positive gap `ρ-r-|c|`. -/
def shiftEstimateGap (α c r : ℝ) : ℝ :=
  shiftEstimateRadius α c r - r - |c|

/-- The exact pointwise conclusion of the displayed shift estimate. -/
def PointwiseShiftEstimate
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Prop :=
  ∀ α c r δ : ℝ, 1 < α → c ≠ 0 →
    max (2 * |c|) (((3 - α) / (α - 1)) * |c|) < r →
    (δ = 1 ∨ δ = -1) →
    |f (δ * r + c) - f (δ * r)| ≤
      (32 * |c|) / ((α - 1) * (r + |c|)) *
        (characteristic (α * (r + |c|)) f + |f 0| / 2)

/-- The finite telescoping/counting estimate isolated from the expanded proof. -/
def ShiftEstimateTelescopingBound
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Prop :=
  ∀ α c r δ : ℝ, 1 < α → c ≠ 0 →
    max (2 * |c|) (((3 - α) / (α - 1)) * |c|) < r →
    (δ = 1 ∨ δ = -1) →
    |f (δ * r + c) - f (δ * r)| ≤
      (8 * |c|) / shiftEstimateGap α c r *
        (characteristic (shiftEstimateRadius α c r) f +
          characteristic (shiftEstimateRadius α c r) (-f))

/-- The same finite telescoping bound restricted to positive shifts.  Both
radial signs remain present, so this is exactly the part proved by the two
right/left endpoint applications of Lemma 3.1. -/
def PositiveShiftEstimateTelescopingBound
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Prop :=
  ∀ α c r δ : ℝ, 1 < α → 0 < c →
    max (2 * c) (((3 - α) / (α - 1)) * c) < r →
    (δ = 1 ∨ δ = -1) →
    |f (δ * r + c) - f (δ * r)| ≤
      (8 * c) / shiftEstimateGap α c r *
        (characteristic (shiftEstimateRadius α c r) f +
          characteristic (shiftEstimateRadius α c r) (-f))

/-- Radial characteristic invariance under reflection. -/
def ReflectionCharacteristicInvariant
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Prop :=
  ∀ r : ℝ, characteristic r f.reflect = characteristic r f

theorem reflectionCharacteristicInvariant
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) :
    ReflectionCharacteristicInvariant f := by
  intro r
  exact characteristic_reflect f r

/-- Reflection reduces negative shifts to positive shifts without changing
the radius or the constant.  The two characteristic-invariance inputs are
kept explicit until multiplicity reflection has been connected to counting. -/
theorem shiftEstimateTelescopingBound_of_positive_of_reflection
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hpositive : PositiveShiftEstimateTelescopingBound f)
    (hpositiveReflect : PositiveShiftEstimateTelescopingBound f.reflect)
    (hreflect : ReflectionCharacteristicInvariant f)
    (hreflectNeg : ReflectionCharacteristicInvariant (-f)) :
    ShiftEstimateTelescopingBound f := by
  intro α c r δ hα hc hr hδ
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · have hnegc : 0 < -c := neg_pos.mpr hcneg
    have hδneg : -δ = 1 ∨ -δ = -1 := by
      rcases hδ with rfl | rfl
      · exact Or.inr (by norm_num)
      · exact Or.inl (by norm_num)
    have hrneg :
        max (2 * (-c)) (((3 - α) / (α - 1)) * (-c)) < r := by
      simpa [abs_of_neg hcneg] using hr
    have hbound := hpositiveReflect α (-c) r (-δ) hα hnegc hrneg hδneg
    have hρeq :
        shiftEstimateRadius α (-c) r = shiftEstimateRadius α c r := by
      simp [shiftEstimateRadius]
    rw [hρeq] at hbound
    rw [hreflect (shiftEstimateRadius α c r)] at hbound
    have hreflectNegAt := hreflectNeg (shiftEstimateRadius α c r)
    rw [NthTropicalMeromorphicFunction.neg_reflect] at hreflectNegAt
    rw [hreflectNegAt] at hbound
    simpa [abs_of_neg hcneg, shiftEstimateRadius, shiftEstimateGap, add_comm] using hbound
  · simpa [abs_of_pos hcpos] using hpositive α c r δ hα hcpos
      (by simpa [abs_of_pos hcpos] using hr) hδ

/-- After the reflection invariance of counting has been proved, only the
positive-shift estimates for `f` and its reflection remain. -/
theorem shiftEstimateTelescopingBound_of_positive
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hpositive : PositiveShiftEstimateTelescopingBound f)
    (hpositiveReflect : PositiveShiftEstimateTelescopingBound f.reflect) :
    ShiftEstimateTelescopingBound f :=
  shiftEstimateTelescopingBound_of_positive_of_reflection
    hpositive hpositiveReflect
    (reflectionCharacteristicInvariant f)
    (reflectionCharacteristicInvariant (-f))

theorem shiftEstimateGap_eq
    (α c r : ℝ) :
    shiftEstimateGap α c r = ((α - 1) * (r + |c|)) / 2 := by
  simp only [shiftEstimateGap, shiftEstimateRadius]
  ring

theorem shiftEstimateRadius_lt_target
    {α c r : ℝ} (hα : 1 < α) (hrc : 0 < r + |c|) :
    shiftEstimateRadius α c r < α * (r + |c|) := by
  simp only [shiftEstimateRadius]
  nlinarith [mul_pos (sub_pos.mpr hα) hrc]

private theorem power_le_linearFactor
    {q Q : ℝ} {j : ℕ} (hq : 0 ≤ q) (hqQ : q ≤ Q) (hQ : Q ≤ 1)
    (hj : 1 ≤ j) : q ^ j ≤ Q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hq1 : q ≤ 1 := hqQ.trans hQ
  have hpow : q ^ k ≤ 1 := by
    simpa using pow_le_pow_left₀ hq hq1 k
  rw [pow_succ]
  have hqpow : 0 ≤ q ^ k := pow_nonneg hq k
  nlinarith

private theorem abs_doubleSum_mul_pow_le
    (S : ℕ → Finset ℝ) (mu : ℕ → ℝ → ℝ)
    (u v : ℝ → ℝ) (n : ℕ) {Q : ℝ}
    (hQ1 : Q ≤ 1)
    (hu : ∀ j ∈ Finset.Icc 1 n, ∀ y ∈ S j, 0 ≤ u y)
    (hv : ∀ j ∈ Finset.Icc 1 n, ∀ y ∈ S j, 0 < v y)
    (hratio : ∀ j ∈ Finset.Icc 1 n, ∀ y ∈ S j, u y / v y ≤ Q) :
    |∑ j ∈ Finset.Icc 1 n, ∑ y ∈ S j, mu j y * (u y) ^ j| ≤
      Q * ∑ j ∈ Finset.Icc 1 n,
        ∑ y ∈ S j, |mu j y| * (v y) ^ j := by
  calc
    |∑ j ∈ Finset.Icc 1 n, ∑ y ∈ S j, mu j y * (u y) ^ j| ≤
        ∑ j ∈ Finset.Icc 1 n,
          |∑ y ∈ S j, mu j y * (u y) ^ j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 n,
          ∑ y ∈ S j, |mu j y * (u y) ^ j| := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 n,
          ∑ y ∈ S j, Q * (|mu j y| * (v y) ^ j) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro y hy
      have hj_one : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have huy : 0 ≤ u y := hu j hj y hy
      have hvy : 0 < v y := hv j hj y hy
      have hpow : (u y / v y) ^ j ≤ Q :=
        power_le_linearFactor (div_nonneg huy hvy.le)
          (hratio j hj y hy) hQ1 hj_one
      have hvpow : 0 ≤ (v y) ^ j := pow_nonneg hvy.le j
      have hm : 0 ≤ |mu j y| * (v y) ^ j :=
        mul_nonneg (abs_nonneg _) hvpow
      calc
        |mu j y * (u y) ^ j| = |mu j y| * (u y) ^ j := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg huy j)]
        _ = (|mu j y| * (v y) ^ j) * (u y / v y) ^ j := by
          rw [div_pow]
          field_simp [ne_of_gt hvy]
        _ ≤ (|mu j y| * (v y) ^ j) * Q :=
          mul_le_mul_of_nonneg_left hpow hm
        _ = Q * (|mu j y| * (v y) ^ j) := by ring
    _ = Q * ∑ j ∈ Finset.Icc 1 n,
          ∑ y ∈ S j, |mu j y| * (v y) ^ j := by
      simp only [Finset.mul_sum]

private theorem abs_nonnegative_weightedPowerSum_le
    (a : ℕ → ℝ) (n : ℕ) {q Q : ℝ}
    (hq : 0 ≤ q) (hqQ : q ≤ Q) (hQ : Q ≤ 1)
    (hnonneg : ∀ j ∈ Finset.Icc 1 n, 0 ≤ a j) :
    |∑ j ∈ Finset.Icc 1 n, a j * q ^ j| ≤
      Q * |∑ j ∈ Finset.Icc 1 n, a j| := by
  rw [Finset.abs_sum_of_nonneg]
  · rw [Finset.abs_sum_of_nonneg hnonneg, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj_one : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjpow : q ^ j ≤ Q :=
      power_le_linearFactor hq hqQ hQ hj_one
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hjpow (hnonneg j hj)
  · intro j hj
    exact mul_nonneg (hnonneg j hj) (pow_nonneg hq j)

/-- Finite common-sign Taylor sums contract by at most the linear factor
`Q` when every positive-order monomial is rescaled by `q ≤ Q ≤ 1`.
This is the sign argument used in the second inequality of the paper's
expanded shift proof. -/
theorem abs_commonSign_weightedPowerSum_le
    (a : ℕ → ℝ) (n : ℕ) {q Q : ℝ}
    (hq : 0 ≤ q) (hqQ : q ≤ Q) (hQ : Q ≤ 1)
    (hsign :
      (∀ j ∈ Finset.Icc 1 n, 0 ≤ a j) ∨
        (∀ j ∈ Finset.Icc 1 n, a j ≤ 0)) :
    |∑ j ∈ Finset.Icc 1 n, a j * q ^ j| ≤
      Q * |∑ j ∈ Finset.Icc 1 n, a j| := by
  rcases hsign with hnonneg | hnonpos
  · exact abs_nonnegative_weightedPowerSum_le a n hq hqQ hQ hnonneg
  · have hneg := abs_nonnegative_weightedPowerSum_le
      -- This branch is reduced to the already proved nonnegative case.
      (a := fun j ↦ -a j) (n := n) (q := q) (Q := Q)
      hq hqQ hQ (fun j hj ↦ neg_nonneg.mpr (hnonpos j hj))
    simpa only [neg_mul, Finset.sum_neg_distrib, abs_neg] using hneg

/-- The two-applications-of-Lemma-3.1 estimate on a positive interval. -/
theorem positiveIntervalShiftEstimate_of_monotone
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f)
    (hmono : CharacteristicMonotone f)
    {a c R : ℝ} (ha : 0 < a) (hc : 0 < c)
    (houter : a + c < R) (hcGap : c ≤ R - a - c) :
    |f (a + c) - f a| ≤
      (8 * c) / (R - a - c) *
        (characteristic R f + characteristic R (-f)) := by
  classical
  have hgap : 0 < R - a - c := lt_of_lt_of_le hc hcGap
  have hlong : 0 < R - a := by linarith
  have hR : 0 < R := by linarith
  have haR : a ≤ R := by linarith
  have hQ0 : 0 ≤ c / (R - a - c) := div_nonneg hc.le hgap.le
  have hQ1 : c / (R - a - c) ≤ 1 :=
    (div_le_one hgap).2 hcGap
  have hq0 : 0 ≤ c / (R - a) := div_nonneg hc.le hlong.le
  have hqQ : c / (R - a) ≤ c / (R - a - c) := by
    rw [div_le_div_iff₀ hlong hgap]
    nlinarith
  have hshort := endpoint_sub_eq_intrinsic_singularity_sum_of_pos
    f ha (by linarith : a < a + c)
  have hlongExpansion := endpoint_sub_eq_intrinsic_singularity_sum_of_pos
    f ha (by linarith : a < R)
  have hsignJets := hf.normalizedRightJet_commonSign ha
  have hsignScaled :
      (∀ j ∈ Finset.Icc 1 n,
          0 ≤ normalizedRightJet f j a * (R - a) ^ j) ∨
        (∀ j ∈ Finset.Icc 1 n,
          normalizedRightJet f j a * (R - a) ^ j ≤ 0) := by
    rcases hsignJets with hnonneg | hnonpos
    · left
      intro j hj
      exact mul_nonneg (hnonneg j (Finset.mem_Icc.mp hj).1)
        (pow_nonneg hlong.le j)
    · right
      intro j hj
      exact mul_nonpos_of_nonpos_of_nonneg
        (hnonpos j (Finset.mem_Icc.mp hj).1) (pow_nonneg hlong.le j)
  have hTaylorRaw := abs_commonSign_weightedPowerSum_le
    (a := fun j ↦ normalizedRightJet f j a * (R - a) ^ j)
    (n := n) (q := c / (R - a)) (Q := c / (R - a - c))
    hq0 hqQ hQ1 hsignScaled
  have hTaylorIdentity :
      (∑ j ∈ Finset.Icc 1 n,
          (normalizedRightJet f j a * (R - a) ^ j) *
            (c / (R - a)) ^ j) =
        ∑ j ∈ Finset.Icc 1 n, normalizedRightJet f j a * c ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [div_pow]
    field_simp [ne_of_gt hlong]
  have hTaylor :
      |∑ j ∈ Finset.Icc 1 n, normalizedRightJet f j a * c ^ j| ≤
        (c / (R - a - c)) *
          |∑ j ∈ Finset.Icc 1 n,
            normalizedRightJet f j a * (R - a) ^ j| := by
    rw [← hTaylorIdentity]
    exact hTaylorRaw
  have hJumpShort := abs_doubleSum_mul_pow_le
    (S := fun j ↦ jthSingularPointsIn f j a (a + c))
    (mu := fun j y ↦ multiplicity f j y)
    (u := fun y ↦ a + c - y) (v := fun y ↦ R - y) (n := n)
    (Q := c / (R - a - c)) hQ1
    (by
      intro j hj y hy
      exact sub_nonneg.mpr (mem_jthSingularPointsIn_iff.mp hy).1.2.le)
    (by
      intro j hj y hy
      exact sub_pos.mpr
        ((mem_jthSingularPointsIn_iff.mp hy).1.2.trans houter))
    (by
      intro j hj y hy
      have hyab := (mem_jthSingularPointsIn_iff.mp hy).1
      have hden : 0 < R - y := sub_pos.mpr (hyab.2.trans houter)
      rw [div_le_div_iff₀ hden hgap]
      have hleft : 0 ≤ c - (a + c - y) := by linarith [hyab.1]
      have hright : 0 ≤ (R - a - c) - c := by linarith [hcGap]
      have hprod := mul_nonneg hleft hright
      nlinarith [sq_nonneg c])
  have hJumpLong := abs_doubleSum_mul_pow_le
    (S := fun j ↦ jthSingularPointsIn f j a R)
    (mu := fun j y ↦ multiplicity f j y)
    (u := fun y ↦ R - y) (v := fun y ↦ R - y) (n := n)
    (Q := (1 : ℝ)) le_rfl
    (by
      intro j hj y hy
      exact sub_nonneg.mpr (mem_jthSingularPointsIn_iff.mp hy).1.2.le)
    (by
      intro j hj y hy
      exact sub_pos.mpr (mem_jthSingularPointsIn_iff.mp hy).1.2)
    (by
      intro j hj y hy
      rw [div_self (ne_of_gt
        (sub_pos.mpr (mem_jthSingularPointsIn_iff.mp hy).1.2))])
  have hshortSplit :
      f (a + c) - f a =
        (∑ j ∈ Finset.Icc 1 n, normalizedRightJet f j a * c ^ j) +
          ∑ j ∈ Finset.Icc 1 n,
            ∑ y ∈ jthSingularPointsIn f j a (a + c),
              multiplicity f j y * (a + c - y) ^ j := by
    simpa only [Finset.sum_add_distrib, add_sub_cancel_left,
      mul_comm] using hshort
  have hlongSplit :
      f R - f a =
        (∑ j ∈ Finset.Icc 1 n,
          normalizedRightJet f j a * (R - a) ^ j) +
          ∑ j ∈ Finset.Icc 1 n,
            ∑ y ∈ jthSingularPointsIn f j a R,
              multiplicity f j y * (R - y) ^ j := by
    rw [hlongExpansion]
    rw [Finset.sum_add_distrib]
  have hpre :
      |f (a + c) - f a| ≤
        (c / (R - a - c)) *
          (|f R| + |f a| +
            (∑ j ∈ Finset.Icc 1 n,
              ∑ y ∈ jthSingularPointsIn f j a R,
                |multiplicity f j y| * (R - y) ^ j) +
            (∑ j ∈ Finset.Icc 1 n,
              ∑ y ∈ jthSingularPointsIn f j a (a + c),
                |multiplicity f j y| * (R - y) ^ j)) := by
    rw [hshortSplit]
    calc
      |(∑ j ∈ Finset.Icc 1 n, normalizedRightJet f j a * c ^ j) +
          ∑ j ∈ Finset.Icc 1 n,
            ∑ y ∈ jthSingularPointsIn f j a (a + c),
              multiplicity f j y * (a + c - y) ^ j| ≤
          |∑ j ∈ Finset.Icc 1 n, normalizedRightJet f j a * c ^ j| +
            |∑ j ∈ Finset.Icc 1 n,
              ∑ y ∈ jthSingularPointsIn f j a (a + c),
                multiplicity f j y * (a + c - y) ^ j| := abs_add_le _ _
      _ ≤ (c / (R - a - c)) *
            |∑ j ∈ Finset.Icc 1 n,
              normalizedRightJet f j a * (R - a) ^ j| +
          (c / (R - a - c)) *
            (∑ j ∈ Finset.Icc 1 n,
              ∑ y ∈ jthSingularPointsIn f j a (a + c),
                |multiplicity f j y| * (R - y) ^ j) :=
        add_le_add hTaylor hJumpShort
      _ = (c / (R - a - c)) *
          (|∑ j ∈ Finset.Icc 1 n,
              normalizedRightJet f j a * (R - a) ^ j| +
            (∑ j ∈ Finset.Icc 1 n,
              ∑ y ∈ jthSingularPointsIn f j a (a + c),
                |multiplicity f j y| * (R - y) ^ j)) := by ring
      _ ≤ (c / (R - a - c)) *
          (|f R| + |f a| +
            (∑ j ∈ Finset.Icc 1 n,
              ∑ y ∈ jthSingularPointsIn f j a R,
                |multiplicity f j y| * (R - y) ^ j) +
            (∑ j ∈ Finset.Icc 1 n,
              ∑ y ∈ jthSingularPointsIn f j a (a + c),
                |multiplicity f j y| * (R - y) ^ j)) := by
        apply mul_le_mul_of_nonneg_left _ hQ0
        have htaylorLong :
            (∑ j ∈ Finset.Icc 1 n,
              normalizedRightJet f j a * (R - a) ^ j) =
              (f R - f a) -
                ∑ j ∈ Finset.Icc 1 n,
                  ∑ y ∈ jthSingularPointsIn f j a R,
                    multiplicity f j y * (R - y) ^ j := by
          linarith [hlongSplit]
        have htaylorBound :
            |∑ j ∈ Finset.Icc 1 n,
              normalizedRightJet f j a * (R - a) ^ j| ≤
              |f R| + |f a| +
                ∑ j ∈ Finset.Icc 1 n,
                  ∑ y ∈ jthSingularPointsIn f j a R,
                    |multiplicity f j y| * (R - y) ^ j := by
          rw [htaylorLong]
          calc
            |(f R - f a) -
                ∑ j ∈ Finset.Icc 1 n,
                  ∑ y ∈ jthSingularPointsIn f j a R,
                    multiplicity f j y * (R - y) ^ j| ≤
                |f R - f a| +
                  |∑ j ∈ Finset.Icc 1 n,
                    ∑ y ∈ jthSingularPointsIn f j a R,
                      multiplicity f j y * (R - y) ^ j| := abs_sub _ _
            _ ≤ (|f R| + |f a|) +
                  ∑ j ∈ Finset.Icc 1 n,
                    ∑ y ∈ jthSingularPointsIn f j a R,
                      |multiplicity f j y| * (R - y) ^ j :=
              add_le_add (abs_sub (f R) (f a)) (by simpa using hJumpLong)
        exact add_le_add htaylorBound le_rfl
  have hmonoNeg := hmono.neg
  have hcharA :
      characteristic a f + characteristic a (-f) ≤
        characteristic R f + characteristic R (-f) :=
    add_le_add (hmono ha hR haR) (hmonoNeg ha hR haR)
  have hendR :
      |f R| ≤ 2 * (characteristic R f + characteristic R (-f)) :=
    (abs_apply_le_two_mul_proximity_pair f R).trans
      (mul_le_mul_of_nonneg_left (pairedProximity_le_pairedCharacteristic f R)
        (by norm_num))
  have hendA :
      |f a| ≤ 2 * (characteristic R f + characteristic R (-f)) := by
    calc
      |f a| ≤ 2 * (proximity a f + proximity a (-f)) :=
        abs_apply_le_two_mul_proximity_pair f a
      _ ≤ 2 * (characteristic a f + characteristic a (-f)) :=
        mul_le_mul_of_nonneg_left (pairedProximity_le_pairedCharacteristic f a)
          (by norm_num)
      _ ≤ 2 * (characteristic R f + characteristic R (-f)) :=
        mul_le_mul_of_nonneg_left hcharA (by norm_num)
  have hcountLong := positiveInterval_singularitySums_le_two_mul_characteristicPair
    f ha (by linarith : a < R) le_rfl
  have hcountShort := positiveInterval_singularitySums_le_two_mul_characteristicPair
    f ha (by linarith : a < a + c) houter.le
  have hinside :
      |f R| + |f a| +
          (∑ j ∈ Finset.Icc 1 n,
            ∑ y ∈ jthSingularPointsIn f j a R,
              |multiplicity f j y| * (R - y) ^ j) +
          (∑ j ∈ Finset.Icc 1 n,
            ∑ y ∈ jthSingularPointsIn f j a (a + c),
              |multiplicity f j y| * (R - y) ^ j) ≤
        8 * (characteristic R f + characteristic R (-f)) := by
    linarith
  calc
    |f (a + c) - f a| ≤
        (c / (R - a - c)) *
          (|f R| + |f a| +
            (∑ j ∈ Finset.Icc 1 n,
              ∑ y ∈ jthSingularPointsIn f j a R,
                |multiplicity f j y| * (R - y) ^ j) +
            (∑ j ∈ Finset.Icc 1 n,
              ∑ y ∈ jthSingularPointsIn f j a (a + c),
                |multiplicity f j y| * (R - y) ^ j)) := hpre
    _ ≤ (c / (R - a - c)) *
          (8 * (characteristic R f + characteristic R (-f))) :=
      mul_le_mul_of_nonneg_left hinside hQ0
    _ = (8 * c) / (R - a - c) *
          (characteristic R f + characteristic R (-f)) := by ring

/-- The complete positive-shift telescoping bound, including both radial
directions.  The `δ=-1` case is obtained by applying the positive-interval
estimate to the reflected function on `[r-c,r]`. -/
theorem positiveShiftEstimateTelescopingBound_of_monotone
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f)
    (hmono : CharacteristicMonotone f) :
    PositiveShiftEstimateTelescopingBound f := by
  intro α c r δ hα hc hr hδ
  have hr_two : 2 * c < r := (le_max_left _ _).trans_lt hr
  have hr_pos : 0 < r := by linarith
  have hra_pos : 0 < r - c := by linarith
  have hdenα : 0 < α - 1 := sub_pos.mpr hα
  have hthreshold : ((3 - α) / (α - 1)) * c < r :=
    (le_max_right _ _).trans_lt hr
  have hthresholdMul : (3 - α) * c < (α - 1) * r := by
    rw [div_mul_eq_mul_div] at hthreshold
    simpa only [mul_comm] using (div_lt_iff₀ hdenα).mp hthreshold
  have hgapEq :
      shiftEstimateGap α c r = ((α - 1) * (r + c)) / 2 := by
    simpa [abs_of_pos hc] using shiftEstimateGap_eq α c r
  have hgapC : c ≤ shiftEstimateGap α c r := by
    rw [hgapEq]
    linarith
  have houter : r + c < shiftEstimateRadius α c r := by
    have hgapPos : 0 < shiftEstimateGap α c r := hc.trans_le hgapC
    rw [shiftEstimateGap, abs_of_pos hc] at hgapPos
    linarith
  rcases hδ with rfl | rfl
  · simpa [shiftEstimateGap, abs_of_pos hc] using
      positiveIntervalShiftEstimate_of_monotone hf hmono hr_pos hc houter
        (by simpa [shiftEstimateGap, abs_of_pos hc] using hgapC)
  · let g := f.reflect
    have hfg : IsWellDefinedNthTropicalMeromorphicFunction g := hf.reflect
    have hmonog : CharacteristicMonotone g := hmono.reflect
    have houterNeg : (r - c) + c < shiftEstimateRadius α c r := by
      linarith
    have hgapNeg :
        c ≤ shiftEstimateRadius α c r - (r - c) - c := by
      have hgapPos : 0 < shiftEstimateGap α c r := hc.trans_le hgapC
      simp only [shiftEstimateGap] at hgapPos
      linarith
    have hcore := positiveIntervalShiftEstimate_of_monotone
      hfg hmonog hra_pos hc houterNeg hgapNeg
    have hdenSmall : 0 < shiftEstimateGap α c r := hc.trans_le hgapC
    have hdenLarge :
        0 < shiftEstimateRadius α c r - (r - c) - c := by linarith
    have hcoeff :
        (8 * c) /
            (shiftEstimateRadius α c r - (r - c) - c) ≤
          (8 * c) / shiftEstimateGap α c r := by
      apply div_le_div_of_nonneg_left (by positivity) hdenSmall
      simp only [shiftEstimateGap, abs_of_pos hc]
      linarith
    have hpairNonneg :
        0 ≤ characteristic (shiftEstimateRadius α c r) f +
          characteristic (shiftEstimateRadius α c r) (-f) :=
      add_nonneg (characteristic_nonneg _ _) (characteristic_nonneg _ _)
    calc
      |f (-1 * r + c) - f (-1 * r)| =
          |g ((r - c) + c) - g (r - c)| := by
        simp only [g, NthTropicalMeromorphicFunction.reflect_apply,
          neg_add_rev, neg_sub]
        rw [abs_sub_comm]
        ring_nf
      _ ≤ (8 * c) /
            (shiftEstimateRadius α c r - (r - c) - c) *
          (characteristic (shiftEstimateRadius α c r) g +
            characteristic (shiftEstimateRadius α c r) (-g)) := hcore
      _ = (8 * c) /
            (shiftEstimateRadius α c r - (r - c) - c) *
          (characteristic (shiftEstimateRadius α c r) f +
            characteristic (shiftEstimateRadius α c r) (-f)) := by
        change _ * (characteristic _ f.reflect + characteristic _ (-f.reflect)) = _
        rw [characteristic_reflect]
        rw [← NthTropicalMeromorphicFunction.neg_reflect, characteristic_reflect]
      _ ≤ (8 * c) / shiftEstimateGap α c r *
          (characteristic (shiftEstimateRadius α c r) f +
            characteristic (shiftEstimateRadius α c r) (-f)) :=
        mul_le_mul_of_nonneg_right hcoeff hpairNonneg

/-- The finite two-expansion part of the shift lemma, with the negative-shift
case closed by reflection. -/
theorem shiftEstimateTelescopingBound_of_wellDefined_of_monotone
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f)
    (hmono : CharacteristicMonotone f) :
    ShiftEstimateTelescopingBound f :=
  shiftEstimateTelescopingBound_of_positive
    (positiveShiftEstimateTelescopingBound_of_monotone hf hmono)
    (positiveShiftEstimateTelescopingBound_of_monotone hf.reflect hmono.reflect)

/-- The fully verified final half of the displayed shift lemma.  Once the
finite telescoping bound is constructed, this theorem yields exactly the
paper's constant `32` and original quantified conclusion. -/
theorem shiftEstimate_of_telescopingBound
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hcore : ShiftEstimateTelescopingBound f)
    (hmono : CharacteristicMonotone f) :
    PointwiseShiftEstimate f := by
  intro α c r δ hα hc hr hδ
  have hcabs : 0 < |c| := abs_pos.mpr hc
  have hr_two : 2 * |c| < r := (le_max_left _ _).trans_lt hr
  have hrc : 0 < r + |c| := by linarith
  have hden : 0 < (α - 1) * (r + |c|) :=
    mul_pos (sub_pos.mpr hα) hrc
  have hgap : 0 < shiftEstimateGap α c r := by
    rw [shiftEstimateGap_eq]
    positivity
  have hρ : 0 < shiftEstimateRadius α c r := by
    simp only [shiftEstimateRadius]
    have hαone : 0 < α + 1 := by linarith
    positivity
  have hρR : shiftEstimateRadius α c r < α * (r + |c|) :=
    shiftEstimateRadius_lt_target hα hrc
  have hR : 0 < α * (r + |c|) := by
    have hαpos : 0 < α := by linarith
    positivity
  have hTmono :
      characteristic (shiftEstimateRadius α c r) f ≤
        characteristic (α * (r + |c|)) f := by
    exact hmono hρ hR hρR.le
  have hJensen := characteristic_eq_neg_add_at_zero f hρ
  have hsum :
      characteristic (shiftEstimateRadius α c r) f +
          characteristic (shiftEstimateRadius α c r) (-f) ≤
        2 * characteristic (shiftEstimateRadius α c r) f + |f 0| := by
    have hf0 : -(f 0) ≤ |f 0| := neg_le_abs (f 0)
    linarith
  have hinside :
      2 * characteristic (shiftEstimateRadius α c r) f + |f 0| ≤
        2 * characteristic (α * (r + |c|)) f + |f 0| := by
    linarith
  have hcoeff : 0 ≤ (8 * |c|) / shiftEstimateGap α c r := by
    positivity
  have hcoeff_eq :
      (8 * |c|) / shiftEstimateGap α c r =
        (16 * |c|) / ((α - 1) * (r + |c|)) := by
    rw [shiftEstimateGap_eq]
    field_simp [ne_of_gt hden]
    ring
  calc
    |f (δ * r + c) - f (δ * r)| ≤
        (8 * |c|) / shiftEstimateGap α c r *
          (characteristic (shiftEstimateRadius α c r) f +
            characteristic (shiftEstimateRadius α c r) (-f)) :=
      hcore α c r δ hα hc hr hδ
    _ ≤ (8 * |c|) / shiftEstimateGap α c r *
          (2 * characteristic (shiftEstimateRadius α c r) f + |f 0|) :=
      mul_le_mul_of_nonneg_left hsum hcoeff
    _ ≤ (8 * |c|) / shiftEstimateGap α c r *
          (2 * characteristic (α * (r + |c|)) f + |f 0|) :=
      mul_le_mul_of_nonneg_left hinside hcoeff
    _ = (32 * |c|) / ((α - 1) * (r + |c|)) *
          (characteristic (α * (r + |c|)) f + |f 0| / 2) := by
      rw [hcoeff_eq]
      ring

/-- Displayed shift lemma with exactly the preceding order-zero part of the
characteristic monotonicity lemma as its imported dependency.  No finite
telescoping, counting, reflection, or numerical estimate remains exposed. -/
theorem pointwiseShiftEstimate_of_wellDefined_of_characteristicMonotone
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f)
    (hmono : CharacteristicMonotone f) :
    PointwiseShiftEstimate f :=
  shiftEstimate_of_telescopingBound
    (shiftEstimateTelescopingBound_of_wellDefined_of_monotone hf hmono) hmono

/-- The displayed shift lemma as a direct corollary of the preceding full
characteristic lemma. -/
theorem pointwiseShiftEstimate_of_characteristicAbsoluteMonotonicity
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f)
    (hcharacteristic : CharacteristicAbsoluteMonotonicity f) :
    PointwiseShiftEstimate f :=
  pointwiseShiftEstimate_of_wellDefined_of_characteristicMonotone hf
    (characteristicMonotone_of_leftDerivativesMonotone hcharacteristic.2)

/-- The displayed shift lemma imported from the complete packaged conclusion
of Lemma 4.4.  Only its order-zero monotonicity field is analytically needed
here; retaining the package makes the paper-level dependency explicit. -/
theorem pointwiseShiftEstimate_of_characteristicLemma44
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f)
    (hlemma44 : CharacteristicLemma44Conclusion f) :
    PointwiseShiftEstimate f :=
  pointwiseShiftEstimate_of_wellDefined_of_characteristicMonotone hf
    hlemma44.characteristicMonotone

/-- Displayed Lemma 4.5 with the paper's original hypotheses only. -/
theorem pointwiseShiftEstimate_of_wellDefined
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f) :
    PointwiseShiftEstimate f := by
  by_cases hn : 1 ≤ n
  · exact pointwiseShiftEstimate_of_characteristicLemma44 hf
      (characteristicLemma44 hn hf)
  · -- Compatibility with Lean's extra `n = 0` case; the paper uses `n ≥ 1`.
    exact pointwiseShiftEstimate_of_characteristicAbsoluteMonotonicity hf
      (characteristicAbsoluteMonotonicity hf)

/-! ## Nonconstant functions have at least linear characteristic growth -/

/-- If the characteristic is uniformly bounded on positive radii, then the
function takes the same value at any two positive points.  The proof sends
the outer radius in the finite positive-interval shift estimate to infinity.
-/
theorem eq_on_positive_of_characteristic_bounded
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f)
    (B : ℝ) (hB : ∀ r : ℝ, 0 < r → characteristic r f ≤ B)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : f a = f b := by
  have hordered : ∀ {a b : ℝ}, 0 < a → a < b → f a = f b := by
    intro a b ha hab
    let c := b - a
    have hc : 0 < c := sub_pos.mpr hab
    let K := 2 * B + |f 0|
    have hpair : ∀ R : ℝ, 0 < R →
        characteristic R f + characteristic R (-f) ≤ K := by
      intro R hR
      have hJ := characteristic_eq_neg_add_at_zero f hR
      dsimp [K]
      linarith [hB R hR, neg_le_abs (f 0)]
    have hden : Tendsto (fun R : ℝ ↦ R - a - c) Filter.atTop Filter.atTop := by
      have h := Filter.tendsto_atTop_add_const_right Filter.atTop
        (-(a + c)) Filter.tendsto_id
      convert h using 1
      funext R
      simp only [id_eq]
      ring
    have hlim : Tendsto (fun R : ℝ ↦ (8 * c * K) / (R - a - c))
        Filter.atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop hden
    have hevent : ∀ᶠ R : ℝ in Filter.atTop,
        |f b - f a| ≤ (8 * c * K) / (R - a - c) := by
      filter_upwards [eventually_gt_atTop (a + 2 * c)] with R hR
      have houter : a + c < R := by linarith
      have hgap : c ≤ R - a - c := by linarith
      have hRpos : 0 < R := by linarith
      have hdenpos : 0 < R - a - c := by linarith
      have hcoeff : 0 ≤ (8 * c) / (R - a - c) := by positivity
      have hest := positiveIntervalShiftEstimate_of_monotone hf
        (characteristicMonotone_of_wellDefined hf) ha hc houter hgap
      change |f b - f a| ≤ _
      rw [show a + c = b by dsimp [c]; ring] at hest
      calc
        |f b - f a| ≤ (8 * c) / (R - a - c) *
            (characteristic R f + characteristic R (-f)) := hest
        _ ≤ (8 * c) / (R - a - c) * K :=
          mul_le_mul_of_nonneg_left (hpair R hRpos) hcoeff
        _ = (8 * c * K) / (R - a - c) := by ring
    have hnonpos : |f b - f a| ≤ 0 := ge_of_tendsto hlim hevent
    have hzero := abs_nonpos_iff.mp hnonpos
    linarith
  rcases lt_trichotomy a b with hab | hab | hab
  · exact hordered ha hab
  · exact congrArg f hab
  · exact (hordered hb hab).symm

/-- A bounded characteristic forces a well-defined tropical meromorphic
function to be globally constant.  Reflection gives constancy on the
negative half-line and continuity identifies both constants at the origin.
-/
theorem eq_at_zero_of_characteristic_bounded
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f)
    (B : ℝ) (hB : ∀ r : ℝ, 0 < r → characteristic r f ≤ B) :
    ∀ x : ℝ, f x = f 0 := by
  have hpos : ∀ {x : ℝ}, 0 < x → f x = f 1 := by
    intro x hx
    exact eq_on_positive_of_characteristic_bounded hf B hB hx zero_lt_one
  have hnegBound : ∀ r : ℝ, 0 < r → characteristic r f.reflect ≤ B := by
    intro r hr
    simpa only [characteristic_reflect] using hB r hr
  have hneg : ∀ {x : ℝ}, x < 0 → f x = f (-1) := by
    intro x hx
    have h := eq_on_positive_of_characteristic_bounded hf.reflect B hnegBound
      (show 0 < -x by linarith) zero_lt_one
    simpa only [NthTropicalMeromorphicFunction.reflect_apply, neg_neg,
      neg_one_mul] using h
  have hzeroPos : f 0 = f 1 := by
    have heq : Set.EqOn f (fun _x : ℝ ↦ f 1) (Set.Ioi 0) :=
      fun x hx ↦ hpos hx
    have hclosure := heq.closure f.continuous continuous_const
    exact hclosure (by simp)
  have hzeroNeg : f 0 = f (-1) := by
    have heq : Set.EqOn f (fun _x : ℝ ↦ f (-1)) (Set.Iio 0) :=
      fun x hx ↦ hneg hx
    have hclosure := heq.closure f.continuous continuous_const
    exact hclosure (by simp)
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · exact (hneg hx).trans hzeroNeg.symm
  · exact congrArg f hx
  · exact (hpos hx).trans hzeroPos.symm

/-- A nonconstant well-defined tropical meromorphic function has
`T(r,f) → ∞`.  This is the contrapositive of the preceding boundedness
rigidity theorem, combined with monotonicity from Lemma 4.4. -/
theorem characteristic_tendsto_atTop_of_wellDefined_nonconstant
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f)
    (hnonconstant : ∃ x y : ℝ, f x ≠ f y) :
    Tendsto (fun r ↦ characteristic r f) Filter.atTop Filter.atTop := by
  have hnotConstant : ¬ ∀ x : ℝ, f x = f 0 := by
    intro hconstant
    obtain ⟨x, y, hxy⟩ := hnonconstant
    exact hxy ((hconstant x).trans (hconstant y).symm)
  have hmono := characteristicMonotone_of_wellDefined hf
  apply Filter.tendsto_atTop.2
  intro B
  by_cases hex : ∃ R : ℝ, 0 < R ∧ B ≤ characteristic R f
  · obtain ⟨R, hR, hBR⟩ := hex
    filter_upwards [eventually_ge_atTop R,
      eventually_gt_atTop (0 : ℝ)] with r hRr hr
    exact hBR.trans (hmono hR hr hRr)
  · have hbound : ∀ r : ℝ, 0 < r → characteristic r f ≤ B := by
      intro r hr
      exact le_of_lt (lt_of_not_ge (fun h ↦ hex ⟨r, hr, h⟩))
    exact (hnotConstant
      (eq_at_zero_of_characteristic_bounded hf B hbound)).elim

/-- More precisely, a nonconstant well-defined function has an eventual
positive affine lower bound for its characteristic.  Convexity converts two
strictly separated characteristic values into a persistent positive secant
slope. -/
theorem characteristic_eventually_linear_lower_of_wellDefined_nonconstant
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f)
    (hnonconstant : ∃ x y : ℝ, f x ≠ f y) :
    ∃ c C : ℝ, 0 < c ∧
      ∀ᶠ r : ℝ in Filter.atTop, c * r + C ≤ characteristic r f := by
  have hT := characteristic_tendsto_atTop_of_wellDefined_nonconstant
    hf hnonconstant
  have hlarge : ∀ᶠ r : ℝ in Filter.atTop,
      characteristic 1 f + 1 ≤ characteristic r f ∧ 2 ≤ r := by
    filter_upwards [hT (eventually_ge_atTop (characteristic 1 f + 1)),
      eventually_ge_atTop (2 : ℝ)] with r hrT hr2
    exact ⟨hrT, hr2⟩
  obtain ⟨b, hbT, hb2⟩ := hlarge.exists
  let c := (characteristic b f - characteristic 1 f) / (b - 1)
  let C := characteristic 1 f - c
  have hb1 : 1 < b := by linarith
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (by linarith) (by linarith)
  refine ⟨c, C, hc, ?_⟩
  filter_upwards [eventually_ge_atTop b] with r hbr
  have hr1 : 1 < r := hb1.trans_le hbr
  have hsec :=
    (characteristicConvexOn_of_wellDefined_allOrder hf).secant_mono
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show b ∈ Set.Ioi 0 by exact zero_lt_one.trans hb1)
      (show r ∈ Set.Ioi 0 by exact zero_lt_one.trans hr1)
      (ne_of_gt hb1) (ne_of_gt hr1) hbr
  dsimp [c, C]
  have hbden : 0 < b - 1 := sub_pos.mpr hb1
  have hrden : 0 < r - 1 := sub_pos.mpr hr1
  rw [div_le_div_iff₀ hbden hrden] at hsec
  have hslope :
      ((characteristic b f - characteristic 1 f) / (b - 1)) * (r - 1) ≤
        characteristic r f - characteristic 1 f := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hbden).2
    nlinarith
  linarith

end

end NthTropicalNevanlinna
