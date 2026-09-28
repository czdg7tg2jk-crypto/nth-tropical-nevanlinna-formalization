import NthTropicalNevanlinna.Nevanlinna.Growth
import NthTropicalNevanlinna.Function.SplineAssembly
import NthTropicalNevanlinna.Function.Entire
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Tropical hyper-exponential examples

This file isolates Definition 3.7 and the analytic work needed for
Proposition 3.8.  The paper's sum from `-∞` to `⌊x⌋ - 1` is reindexed by
`k : ℕ` as the integer `⌊x⌋ - 1 - k`.
-/

namespace NthTropicalNevanlinna

noncomputable section

open Filter Set
open scoped Topology

/-- The summand in Definition 3.7 at an integer `i`. -/
def tropicalHyperExponentialTerm (n : ℕ) (α : ℝ) (i : ℤ) : ℝ :=
  rightSign (i : ℝ) ^ (n + 1) * α ^ i *
    ((((i : ℝ) + 1) ^ n) - (i : ℝ) ^ n)

/--
Definition 3.7, literally reindexed as a `ℕ`-series.  The hypothesis `α > 1`
is not needed to form the expression, but is needed to prove summability and
the properties in Proposition 3.8.
-/
def tropicalHyperExponentialRaw (n : ℕ) (α : ℝ) (x : ℝ) : ℝ :=
  rightSign x ^ (n + 1) * α ^ (⌊x⌋ : ℤ) *
      (x ^ n - (⌊x⌋ : ℝ) ^ n) +
    ∑' k : ℕ,
      tropicalHyperExponentialTerm n α (⌊x⌋ - 1 - (k : ℤ))

private theorem summable_succPow_mul_geometric
    (n : ℕ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ n * q ^ k := by
  have hbase : Summable fun k : ℕ ↦ (k : ℝ) ^ n * q ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one n (by simpa [abs_of_pos hq0] using hq1)
  have hshift : Summable fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ n * q ^ (k + 1) := by
    simpa using (summable_nat_add_iff 1).2 hbase
  have hscaled := hshift.mul_right q⁻¹
  exact hscaled.congr (fun k ↦ by
    rw [pow_succ]
    field_simp)

private theorem tropicalHyperExponentialTerm_tail_bound
    (n : ℕ) {α : ℝ} (hα : 1 < α) (m : ℤ) (k : ℕ) :
    ‖tropicalHyperExponentialTerm n α (m - 1 - (k : ℤ))‖ ≤
      (2 * |α ^ (m - 1)| * (|(m : ℝ)| + 2) ^ n) *
        (((k : ℝ) + 1) ^ n * (α⁻¹) ^ k) := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  let i : ℤ := m - 1 - (k : ℤ)
  let C : ℝ := |(m : ℝ)| + 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hi : |(i : ℝ)| ≤ C * ((k : ℝ) + 1) := by
    dsimp [i, C]
    push_cast
    calc
      |(m : ℝ) - 1 - k| ≤ |(m : ℝ)| + 1 + k := by
        calc
          |(m : ℝ) - 1 - k| ≤ |(m : ℝ)| + |(1 : ℝ)| + |(k : ℝ)| := by
            simpa [sub_eq_add_neg, add_assoc] using
              (abs_add_three (m : ℝ) (-1) (-(k : ℝ)))
          _ = |(m : ℝ)| + 1 + k := by simp [abs_of_nonneg hk0]
      _ ≤ (|(m : ℝ)| + 2) * ((k : ℝ) + 1) := by
        have h : |(m : ℝ)| + 1 + k ≤
            (|(m : ℝ)| + 2) * ((k : ℝ) + 1) := by
          nlinarith [abs_nonneg (m : ℝ)]
        exact h
  have hip : |(i : ℝ) + 1| ≤ C * ((k : ℝ) + 1) := by
    dsimp [i, C]
    push_cast
    calc
      |(m : ℝ) - 1 - k + 1| = |(m : ℝ) - k| := by ring_nf
      _ ≤ |(m : ℝ)| + |(k : ℝ)| := abs_sub _ _
      _ = |(m : ℝ)| + k := by rw [abs_of_nonneg hk0]
      _ ≤ (|(m : ℝ)| + 2) * ((k : ℝ) + 1) := by
        have h : |(m : ℝ)| + k ≤
            (|(m : ℝ)| + 2) * ((k : ℝ) + 1) := by
          nlinarith [abs_nonneg (m : ℝ)]
        exact h
  have hpowi : |(i : ℝ)| ^ n ≤ (C * ((k : ℝ) + 1)) ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) hi n
  have hpowip : |(i : ℝ) + 1| ^ n ≤
      (C * ((k : ℝ) + 1)) ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) hip n
  have hdiff : |(((i : ℝ) + 1) ^ n) - (i : ℝ) ^ n| ≤
      2 * (C * ((k : ℝ) + 1)) ^ n := by
    calc
      |(((i : ℝ) + 1) ^ n) - (i : ℝ) ^ n| ≤
          |((i : ℝ) + 1) ^ n| + |(i : ℝ) ^ n| := abs_sub _ _
      _ = |(i : ℝ) + 1| ^ n + |(i : ℝ)| ^ n := by rw [abs_pow, abs_pow]
      _ ≤ 2 * (C * ((k : ℝ) + 1)) ^ n := by linarith
  have hzpow : α ^ (m - 1 - (k : ℤ)) =
      α ^ (m - 1) * (α⁻¹) ^ k := by
    rw [zpow_sub₀ (ne_of_gt hα0), zpow_natCast]
    simp [div_eq_mul_inv, inv_pow]
  rw [tropicalHyperExponentialTerm]
  change ‖rightSign (i : ℝ) ^ (n + 1) * α ^ i *
      (((i : ℝ) + 1) ^ n - (i : ℝ) ^ n)‖ ≤ _
  rw [show i = m - 1 - (k : ℤ) by rfl, hzpow]
  simp only [Real.norm_eq_abs, abs_mul, abs_pow]
  have hsign : |rightSign (i : ℝ)| = 1 := by
    simp only [rightSign]
    split_ifs <;> norm_num
  rw [hsign, one_pow, one_mul]
  change |α ^ (m - 1)| * |α⁻¹| ^ k *
      |((i : ℝ) + 1) ^ n - (i : ℝ) ^ n| ≤ _
  rw [abs_inv, abs_of_pos hα0]
  have hqnonneg : 0 ≤ α⁻¹ ^ k := pow_nonneg (by positivity) k
  have hconst : 0 ≤ |α ^ (m - 1)| := abs_nonneg _
  have hdiff' : |(((i : ℝ) + 1) ^ n) - (i : ℝ) ^ n| ≤
      2 * C ^ n * (((k : ℝ) + 1) ^ n) := by
    simpa [mul_pow, mul_assoc] using hdiff
  calc
    |α ^ (m - 1)| * α⁻¹ ^ k *
        |((i : ℝ) + 1) ^ n - (i : ℝ) ^ n| ≤
      |α ^ (m - 1)| * α⁻¹ ^ k *
        (2 * C ^ n * (((k : ℝ) + 1) ^ n)) := by
          exact mul_le_mul_of_nonneg_left hdiff' (mul_nonneg hconst hqnonneg)
    _ = (2 * |α ^ (m - 1)| * C ^ n) *
        (((k : ℝ) + 1) ^ n * α⁻¹ ^ k) := by ring

/-- The negative-infinite tail in Definition 3.7 is absolutely summable for
the paper's hypothesis `α > 1`. -/
theorem summable_tropicalHyperExponentialTerm_tail
    (n : ℕ) {α : ℝ} (hα : 1 < α) (m : ℤ) :
    Summable fun k : ℕ ↦
      tropicalHyperExponentialTerm n α (m - 1 - (k : ℤ)) := by
  have hq0 : 0 < α⁻¹ := inv_pos.mpr (lt_trans zero_lt_one hα)
  have hq1 : α⁻¹ < 1 := inv_lt_one₀ (lt_trans zero_lt_one hα) |>.2 hα
  have hs := summable_succPow_mul_geometric n hq0 hq1
  exact (hs.mul_left (2 * |α ^ (m - 1)| * (|(m : ℝ)| + 2) ^ n)).of_norm_bounded
    (fun k ↦ by simpa using tropicalHyperExponentialTerm_tail_bound n hα m k)

/-- The convergent sum of all increments strictly to the left of the integer
`m`; this is the infinite sum in Definition 3.7 with upper endpoint `m-1`. -/
def tropicalHyperExponentialTail (n : ℕ) (α : ℝ) (m : ℤ) : ℝ :=
  ∑' k : ℕ, tropicalHyperExponentialTerm n α (m - 1 - (k : ℤ))

theorem tropicalHyperExponentialTail_succ
    (n : ℕ) {α : ℝ} (hα : 1 < α) (m : ℤ) :
    tropicalHyperExponentialTail n α (m + 1) =
      tropicalHyperExponentialTerm n α m +
        tropicalHyperExponentialTail n α m := by
  let a : ℕ → ℝ := fun k ↦ tropicalHyperExponentialTerm n α (m - (k : ℤ))
  have ha : Summable a := by
    simpa [a, sub_eq_add_neg, add_assoc] using
      summable_tropicalHyperExponentialTerm_tail n hα (m + 1)
  have hsplit := ha.sum_add_tsum_nat_add 1
  have hsplit' : a 0 + ∑' k : ℕ, a (k + 1) = ∑' k : ℕ, a k := by
    simpa using hsplit
  rw [tropicalHyperExponentialTail, tropicalHyperExponentialTail]
  simpa [a, sub_eq_add_neg, add_assoc] using hsplit'.symm

/-- In first order the increment at the integer `i` is exactly `α^i`. -/
theorem tropicalHyperExponentialTerm_one (α : ℝ) (i : ℤ) :
    tropicalHyperExponentialTerm 1 α i = α ^ i := by
  unfold tropicalHyperExponentialTerm rightSign
  split_ifs <;> push_cast <;> ring

/-- The first-order tail scales exactly by `α` under a unit shift. -/
theorem tropicalHyperExponentialTail_one_succ
    {α : ℝ} (hα : 1 < α) (m : ℤ) :
    tropicalHyperExponentialTail 1 α (m + 1) =
      α * tropicalHyperExponentialTail 1 α m := by
  have hs := summable_tropicalHyperExponentialTerm_tail 1 hα m
  unfold tropicalHyperExponentialTail
  rw [← hs.tsum_mul_left α]
  apply tsum_congr
  intro k
  rw [tropicalHyperExponentialTerm_one, tropicalHyperExponentialTerm_one]
  have hα0 : α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hα)
  calc
    α ^ (m + 1 - 1 - (k : ℤ)) =
        α ^ (1 + (m - 1 - (k : ℤ))) := by congr 1 <;> omega
    _ = α ^ (1 : ℤ) * α ^ (m - 1 - (k : ℤ)) := zpow_add₀ hα0 _ _
    _ = α * α ^ (m - 1 - (k : ℤ)) := by rw [zpow_one]

/-- Sign on the interior of the interval `[i-1,i]`. -/
def tropicalHyperExponentialIntervalSign (i : ℤ) : ℝ :=
  if i ≤ 0 then -1 else 1

theorem intervalSign_eq_rightSign_sub_one (i : ℤ) :
    tropicalHyperExponentialIntervalSign i = rightSign ((i - 1 : ℤ) : ℝ) := by
  by_cases hi : i ≤ 0
  · have hneg : ((i - 1 : ℤ) : ℝ) < 0 := by exact_mod_cast (show i - 1 < 0 by omega)
    rw [tropicalHyperExponentialIntervalSign, if_pos hi, rightSign, if_pos hneg]
  · have hnonneg : 0 ≤ ((i - 1 : ℤ) : ℝ) := by exact_mod_cast (show 0 ≤ i - 1 by omega)
    rw [tropicalHyperExponentialIntervalSign, if_neg hi, rightSign,
      if_neg (not_lt.mpr hnonneg)]

/-- Polynomial piece of `e_{n,α}` on `[i-1,i]`. -/
def tropicalHyperExponentialPiece (n : ℕ) (α : ℝ) (i : ℤ) : Polynomial ℝ :=
  Polynomial.C (tropicalHyperExponentialIntervalSign i ^ (n + 1) * α ^ (i - 1)) *
      (Polynomial.X ^ n - Polynomial.C (((i - 1 : ℤ) : ℝ) ^ n)) +
    Polynomial.C (tropicalHyperExponentialTail n α (i - 1))

theorem tropicalHyperExponentialPiece_natDegree
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) (i : ℤ) :
    (tropicalHyperExponentialPiece n α i).natDegree = n := by
  let a : ℝ := tropicalHyperExponentialIntervalSign i ^ (n + 1) * α ^ (i - 1)
  have hs : tropicalHyperExponentialIntervalSign i ≠ 0 := by
    unfold tropicalHyperExponentialIntervalSign
    split <;> norm_num
  have ha : a ≠ 0 := mul_ne_zero (pow_ne_zero _ hs) (zpow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hα)))
  have hpiece : tropicalHyperExponentialPiece n α i =
      Polynomial.C a * Polynomial.X ^ n +
        Polynomial.C (tropicalHyperExponentialTail n α (i - 1) -
          a * (((i - 1 : ℤ) : ℝ) ^ n)) := by
    unfold tropicalHyperExponentialPiece
    dsimp [a]
    push_cast
    simp only [map_sub, map_mul]
    ring
  rw [hpiece]
  have hmain : (Polynomial.C a * Polynomial.X ^ n).natDegree = n :=
    Polynomial.natDegree_C_mul_X_pow n a ha
  have hconst : (Polynomial.C (tropicalHyperExponentialTail n α (i - 1) -
      a * (((i - 1 : ℤ) : ℝ) ^ n))).natDegree <
      (Polynomial.C a * Polynomial.X ^ n).natDegree := by
    rw [hmain, Polynomial.natDegree_C]
    exact hn
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hconst, hmain]

theorem tropicalHyperExponentialTerm_at_predecessor
    (n : ℕ) (α : ℝ) (i : ℤ) :
    tropicalHyperExponentialTerm n α (i - 1) =
      tropicalHyperExponentialIntervalSign i ^ (n + 1) * α ^ (i - 1) *
        (((i : ℝ) ^ n) - (((i - 1 : ℤ) : ℝ) ^ n)) := by
  rw [tropicalHyperExponentialTerm, intervalSign_eq_rightSign_sub_one]
  congr 2
  push_cast
  ring

theorem tropicalHyperExponentialPiece_adjacent
    (n : ℕ) {α : ℝ} (hα : 1 < α) (i : ℤ) :
    (tropicalHyperExponentialPiece n α i).eval (i : ℝ) =
      (tropicalHyperExponentialPiece n α (i + 1)).eval (i : ℝ) := by
  rw [tropicalHyperExponentialPiece, tropicalHyperExponentialPiece]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  rw [show i + 1 - 1 = i by omega]
  simp only [sub_self, mul_zero, zero_add]
  have htail : tropicalHyperExponentialTail n α i =
      tropicalHyperExponentialTerm n α (i - 1) +
        tropicalHyperExponentialTail n α (i - 1) := by
    simpa using tropicalHyperExponentialTail_succ n hα (i - 1)
  rw [htail]
  rw [tropicalHyperExponentialTerm_at_predecessor]

/-- Redundant integer grid used to assemble the spline. -/
def tropicalHyperExponentialGrid (n : ℕ) :
    PolynomialPresentation n (fun x : ℝ ↦ (Polynomial.X ^ n).eval x) where
  cutPoint i := (i : ℝ)
  piece _ := Polynomial.X ^ n
  cutPoint_strictMono := by
    intro i k hik
    change (i : ℝ) < (k : ℝ)
    exact_mod_cast hik
  cutPoint_zero := by simp
  cutPoint_tendsto_atTop := tendsto_intCast_atTop_atTop
  cutPoint_tendsto_atBot := tendsto_intCast_atBot_iff.mpr Filter.tendsto_id
  piece_natDegree_le := by simp
  eq_piece := by simp
  exists_piece_natDegree_eq := ⟨0, Polynomial.natDegree_X_pow n⟩

/-- Definition 3.7 bundled as an intrinsic `n`-th tropical meromorphic
function.  The proof arguments merely record the paper's standing
conventions `n ≥ 1` and `α > 1`. -/
def tropicalHyperExponential
    (n : ℕ) (α : ℝ) (hn : 1 ≤ n) (hα : 1 < α) :
    NthTropicalMeromorphicFunction n :=
  assembleNthTropicalMeromorphicFunction (tropicalHyperExponentialGrid n)
    (tropicalHyperExponentialPiece n α)
    (fun i ↦ (tropicalHyperExponentialPiece_natDegree n hα hn i).le)
    (tropicalHyperExponentialPiece_adjacent n hα)
    ⟨0, tropicalHyperExponentialPiece_natDegree n hα hn 0⟩

theorem intervalSign_floor_add_one (x : ℝ) :
    tropicalHyperExponentialIntervalSign (⌊x⌋ + 1) = rightSign x := by
  by_cases hx : x < 0
  · have hf : ⌊x⌋ < 0 := Int.floor_lt.mpr (by simpa using hx)
    have hfi : ⌊x⌋ + 1 ≤ 0 := by omega
    simp [tropicalHyperExponentialIntervalSign, rightSign, hfi, hx]
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    have hf : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx0
    have hfi : ¬⌊x⌋ + 1 ≤ 0 := by omega
    simp [tropicalHyperExponentialIntervalSign, rightSign, hfi, hx]

/-- The bundled spline is exactly the infinite-series formula in Definition
3.7, not merely a function with the same local jumps. -/
theorem tropicalHyperExponential_apply
    (n : ℕ) (α : ℝ) (hn : 1 ≤ n) (hα : 1 < α) (x : ℝ) :
    tropicalHyperExponential n α hn hα x =
      tropicalHyperExponentialRaw n α x := by
  let i : ℤ := ⌊x⌋ + 1
  have hxmem : x ∈ Icc (((i - 1 : ℤ) : ℝ)) (i : ℝ) := by
    dsimp [i]
    constructor
    · simpa using Int.floor_le x
    · have h := Int.lt_floor_add_one x
      exact (by exact_mod_cast h.le)
  change assembledFunction (tropicalHyperExponentialGrid n)
      (tropicalHyperExponentialPiece n α) x = _
  rw [assembledFunction_eq_piece (tropicalHyperExponentialGrid n)
    (tropicalHyperExponentialPiece n α)
    (tropicalHyperExponentialPiece_adjacent n hα) i hxmem]
  simp only [tropicalHyperExponentialPiece, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X]
  rw [show i - 1 = ⌊x⌋ by dsimp [i]; omega]
  rw [intervalSign_floor_add_one]
  rfl

/-- The exact unit-shift functional equation quoted after Corollary 6.3:
`e_α(x+1)=αe_α(x)` for the first-order tropical hyper-exponential. -/
theorem tropicalHyperExponential_one_shift
    {α : ℝ} (hα : 1 < α) (x : ℝ) :
    tropicalHyperExponential 1 α (by norm_num) hα (x + 1) =
      α * tropicalHyperExponential 1 α (by norm_num) hα x := by
  rw [tropicalHyperExponential_apply, tropicalHyperExponential_apply]
  unfold tropicalHyperExponentialRaw
  have hsx : rightSign x ^ (1 + 1) = 1 := by
    unfold rightSign
    split_ifs <;> norm_num
  have hsx1 : rightSign (x + 1) ^ (1 + 1) = 1 := by
    unfold rightSign
    split_ifs <;> norm_num
  rw [hsx, hsx1, one_mul, one_mul, Int.floor_add_one]
  change α ^ (⌊x⌋ + 1) * ((x + 1) ^ 1 - ((⌊x⌋ + 1 : ℤ) : ℝ) ^ 1) +
      tropicalHyperExponentialTail 1 α (⌊x⌋ + 1) =
    α * (α ^ ⌊x⌋ * (x ^ 1 - (⌊x⌋ : ℝ) ^ 1) +
      tropicalHyperExponentialTail 1 α ⌊x⌋)
  rw [tropicalHyperExponentialTail_one_succ hα]
  have hα0 : α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hα)
  rw [zpow_add_one₀ hα0]
  push_cast
  ring

theorem normalizedPolynomialJet_tropicalHyperExponentialPiece
    (n j : ℕ) (α : ℝ) (i : ℤ) (x : ℝ) (hj : 1 ≤ j) :
    normalizedPolynomialJet (tropicalHyperExponentialPiece n α i) j x =
      tropicalHyperExponentialIntervalSign i ^ (n + 1) * α ^ (i - 1) *
        (n.choose j : ℝ) * x ^ (n - j) := by
  let a : ℝ := tropicalHyperExponentialIntervalSign i ^ (n + 1) * α ^ (i - 1)
  let c : ℝ := tropicalHyperExponentialTail n α (i - 1) -
    a * (((i - 1 : ℤ) : ℝ) ^ n)
  have hpiece : tropicalHyperExponentialPiece n α i =
      Polynomial.C a * Polynomial.X ^ n + Polynomial.C c := by
    unfold tropicalHyperExponentialPiece
    dsimp [a, c]
    push_cast
    simp only [map_sub, map_mul]
    ring
  rw [hpiece, normalizedPolynomialJet]
  simp only [map_add, Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.hasseDeriv_monomial,
    Polynomial.hasseDeriv_C j c (lt_of_lt_of_le Nat.zero_lt_one hj),
    Polynomial.eval_monomial, add_zero]
  dsimp [a]
  ring

theorem intervalSign_succ_eq_rightSign (i : ℤ) :
    tropicalHyperExponentialIntervalSign (i + 1) = rightSign (i : ℝ) := by
  by_cases hi : i < 0
  · have his : i + 1 ≤ 0 := by omega
    simp [tropicalHyperExponentialIntervalSign, rightSign, his, hi]
  · have his : ¬i + 1 ≤ 0 := by omega
    have hic : ¬(i : ℝ) < 0 := by exact_mod_cast hi
    simp [tropicalHyperExponentialIntervalSign, rightSign, his, hic]

theorem intervalSign_eq_leftSign (i : ℤ) :
    tropicalHyperExponentialIntervalSign i = leftSign (i : ℝ) := by
  by_cases hi : i ≤ 0
  · have hic : (i : ℝ) ≤ 0 := by exact_mod_cast hi
    simp [tropicalHyperExponentialIntervalSign, leftSign, hi, hic]
  · have hic : ¬(i : ℝ) ≤ 0 := by exact_mod_cast hi
    simp [tropicalHyperExponentialIntervalSign, leftSign, hi, hic]

/-- Exact integer jump formula used in Proposition 3.8(i). -/
theorem tropicalHyperExponential_cut_multiplicity
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n)
    (j : ℕ) (hj : 1 ≤ j) (i : ℤ) :
    presentationMultiplicityAtCutPoint
      (assembledPolynomialPresentation (tropicalHyperExponentialGrid n)
        (tropicalHyperExponentialPiece n α)
        (fun k ↦ (tropicalHyperExponentialPiece_natDegree n hα hn k).le)
        (tropicalHyperExponentialPiece_adjacent n hα)
        ⟨0, tropicalHyperExponentialPiece_natDegree n hα hn 0⟩)
      j i =
        (n.choose j : ℝ) * |(i : ℝ)| ^ (n - j) *
          α ^ (i - 1) * (α - 1) := by
  simp only [presentationMultiplicityAtCutPoint,
    assembledPolynomialPresentation, tropicalHyperExponentialGrid]
  rw [normalizedPolynomialJet_tropicalHyperExponentialPiece n j α (i + 1) (i : ℝ) hj,
    normalizedPolynomialJet_tropicalHyperExponentialPiece n j α i (i : ℝ) hj,
    intervalSign_succ_eq_rightSign, intervalSign_eq_leftSign]
  by_cases hjn : j ≤ n
  · have hα0 : α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hα)
    have hαpow : α ^ i = α ^ (i - 1) * α := by
      calc
        α ^ i = α ^ ((i - 1) + 1) := by congr 1 <;> omega
        _ = α ^ (i - 1) * α ^ (1 : ℤ) := zpow_add₀ hα0 _ _
        _ = α ^ (i - 1) * α := by simp
    by_cases hineg : i < 0
    · have hir : rightSign (i : ℝ) = -1 := by
        apply rightSign_of_neg
        exact_mod_cast hineg
      have hil : leftSign (i : ℝ) = -1 := by
        apply leftSign_of_nonpos
        exact_mod_cast hineg.le
      rw [hir, hil, show i + 1 - 1 = i by omega, hαpow]
      have hiabs : |(i : ℝ)| = -(i : ℝ) := abs_of_neg (by exact_mod_cast hineg)
      rw [hiabs, neg_pow]
      have hsign :
          (-1 : ℝ) ^ (j + 1) * (-1 : ℝ) ^ (n + 1) =
            (-1 : ℝ) ^ (n - j) := by
        rw [← pow_add]
        have heq : j + 1 + (n + 1) = (n - j) + 2 * (j + 1) := by omega
        rw [heq, pow_add, pow_mul]
        norm_num
      simp only [one_pow, mul_one]
      simp_rw [← mul_assoc]
      rw [hsign]
      ring
    · by_cases hizero : i = 0
      · subst i
        by_cases hjn' : j < n
        · have hsub : 0 < n - j := Nat.sub_pos_of_lt hjn'
          simp [rightSign, leftSign, zero_pow hsub.ne']
        · have hjeq : j = n := le_antisymm hjn (not_lt.mp hjn')
          subst j
          simp [rightSign, leftSign]
          have hsignsq :
              (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1) = 1 := by
            rw [← pow_add]
            have heq : n + 1 + (n + 1) = 2 * (n + 1) := by omega
            rw [heq, pow_mul]
            norm_num
          rw [← mul_assoc, hsignsq, one_mul]
          field_simp
      · have hipos : 0 < i := lt_of_le_of_ne (le_of_not_gt hineg) (Ne.symm hizero)
        have hir : rightSign (i : ℝ) = 1 := rightSign_of_nonneg (by exact_mod_cast hipos.le)
        have hil : leftSign (i : ℝ) = 1 := leftSign_of_pos (by exact_mod_cast hipos)
        rw [hir, hil, abs_of_pos (by exact_mod_cast hipos),
          show i + 1 - 1 = i by omega, hαpow]
        ring
  · have hchoose : n.choose j = 0 := Nat.choose_eq_zero_of_lt (lt_of_not_ge hjn)
    simp [hchoose]

/-- Intrinsic version of the jump formula: the genuine multiplicity of
`e_{n,α}` at the integer `i` is the nonnegative number displayed in the
paper. -/
theorem tropicalHyperExponential_multiplicity_at_int
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n)
    (j : ℕ) (hj : 1 ≤ j) (i : ℤ) :
    multiplicity (tropicalHyperExponential n α hn hα) j (i : ℝ) =
      (n.choose j : ℝ) * |(i : ℝ)| ^ (n - j) *
        α ^ (i - 1) * (α - 1) := by
  let P := assembledPolynomialPresentation (tropicalHyperExponentialGrid n)
    (tropicalHyperExponentialPiece n α)
    (fun k ↦ (tropicalHyperExponentialPiece_natDegree n hα hn k).le)
    (tropicalHyperExponentialPiece_adjacent n hα)
    ⟨0, tropicalHyperExponentialPiece_natDegree n hα hn 0⟩
  have hcut : P.cutPoint i = (i : ℝ) := rfl
  rw [← hcut, multiplicity_cutPoint_of_presentation
    (tropicalHyperExponential n α hn hα) P j i]
  exact tropicalHyperExponential_cut_multiplicity n hα hn j hj i

theorem tropicalHyperExponential_multiplicity_at_int_nonneg
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n)
    (j : ℕ) (hj : 1 ≤ j) (i : ℤ) :
    0 ≤ multiplicity (tropicalHyperExponential n α hn hα) j (i : ℝ) := by
  rw [tropicalHyperExponential_multiplicity_at_int n hα hn j hj i]
  positivity

/-- Proposition 3.8(i), pole-free part.  The proof is intrinsic: a point
outside the integer grid has multiplicity zero, while an integer has the
explicit nonnegative jump above. -/
theorem tropicalHyperExponential_isTropicalEntire
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) :
    IsTropicalEntire (tropicalHyperExponential n α hn hα) := by
  rw [isTropicalEntire_iff_multiplicity_nonneg]
  intro x j hj hjn
  let P := assembledPolynomialPresentation (tropicalHyperExponentialGrid n)
    (tropicalHyperExponentialPiece n α)
    (fun k ↦ (tropicalHyperExponentialPiece_natDegree n hα hn k).le)
    (tropicalHyperExponentialPiece_adjacent n hα)
    ⟨0, tropicalHyperExponentialPiece_natDegree n hα hn 0⟩
  rcases multiplicity_eq_zero_or_cutPoint_of_presentation
      (tropicalHyperExponential n α hn hα) P j x with hzero | ⟨i, hxi, hmul⟩
  · simp [hzero]
  · have hcut : P.cutPoint i = (i : ℝ) := rfl
    rw [hxi, hcut]
    exact tropicalHyperExponential_multiplicity_at_int_nonneg n hα hn j hj i

theorem tropicalHyperExponentialPiece_hasDerivAt
    (n : ℕ) (α : ℝ) (i : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (tropicalHyperExponentialPiece n α i).eval y)
      (tropicalHyperExponentialIntervalSign i ^ (n + 1) * α ^ (i - 1) *
        (n : ℝ) * x ^ (n - 1)) x := by
  simpa [tropicalHyperExponentialPiece, Polynomial.derivative_X_pow,
    Polynomial.derivative_pow, Polynomial.derivative_C,
    mul_assoc] using (tropicalHyperExponentialPiece n α i).hasDerivAt x

private theorem tropicalHyperExponentialPiece_deriv_nonneg
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n)
    (i : ℤ) {x : ℝ}
    (hx : x ∈ Icc (((i - 1 : ℤ) : ℝ)) (i : ℝ)) :
    0 ≤ tropicalHyperExponentialIntervalSign i ^ (n + 1) * α ^ (i - 1) *
      (n : ℝ) * x ^ (n - 1) := by
  have hαpos : 0 < α ^ (i - 1) := zpow_pos (lt_trans zero_lt_one hα) _
  by_cases hi : i ≤ 0
  · rw [tropicalHyperExponentialIntervalSign, if_pos hi]
    have hx0 : x ≤ 0 := le_trans hx.2 (by exact_mod_cast hi)
    by_cases hxzero : x = 0
    · subst x
      rcases hn.eq_or_lt with rfl | hn2
      · simp
        positivity
      · have hsub : 0 < n - 1 := Nat.sub_pos_of_lt hn2
        simp [zero_pow hsub.ne']
    · have hxneg : x < 0 := lt_of_le_of_ne hx0 hxzero
      have hsign :
          (-1 : ℝ) ^ (n + 1) * x ^ (n - 1) = (-x) ^ (n - 1) := by
        rw [neg_pow]
        have heq : n + 1 = (n - 1) + 2 := by omega
        rw [heq, pow_add]
        norm_num
        ring
      have hnegx : 0 ≤ -x := neg_nonneg.mpr hx0
      calc
        0 ≤ α ^ (i - 1) * (n : ℝ) * ((-x) ^ (n - 1)) :=
          mul_nonneg (mul_nonneg hαpos.le (Nat.cast_nonneg n))
            (pow_nonneg hnegx _)
        _ = (-1 : ℝ) ^ (n + 1) * α ^ (i - 1) *
            (n : ℝ) * x ^ (n - 1) := by rw [← hsign]; ring
  · rw [tropicalHyperExponentialIntervalSign, if_neg hi]
    simp only [one_pow, one_mul]
    have hi1 : 0 ≤ i - 1 := by omega
    have hx0 : 0 ≤ x := le_trans (by exact_mod_cast hi1) hx.1
    exact mul_nonneg (mul_nonneg hαpos.le (Nat.cast_nonneg n))
      (pow_nonneg hx0 _)

/-- Each polynomial piece is nondecreasing on its defining closed unit
interval. -/
theorem tropicalHyperExponentialPiece_monotoneOn
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) (i : ℤ) :
    MonotoneOn (fun x : ℝ ↦ (tropicalHyperExponentialPiece n α i).eval x)
      (Icc (((i - 1 : ℤ) : ℝ)) (i : ℝ)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (tropicalHyperExponentialPiece n α i).continuous.continuousOn
  · intro x hx
    exact (tropicalHyperExponentialPiece_hasDerivAt n α i x).hasDerivWithinAt
  · intro x hx
    exact tropicalHyperExponentialPiece_deriv_nonneg n hα hn i
      (interior_subset hx)

theorem tropicalHyperExponential_eq_piece
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n)
    (i : ℤ) {x : ℝ}
    (hx : x ∈ Icc (((i - 1 : ℤ) : ℝ)) (i : ℝ)) :
    tropicalHyperExponential n α hn hα x =
      (tropicalHyperExponentialPiece n α i).eval x := by
  change assembledFunction (tropicalHyperExponentialGrid n)
    (tropicalHyperExponentialPiece n α) x = _
  exact assembledFunction_eq_piece (tropicalHyperExponentialGrid n)
    (tropicalHyperExponentialPiece n α)
    (tropicalHyperExponentialPiece_adjacent n hα) i hx

private theorem tropicalHyperExponential_grid_monotone
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) :
    Monotone fun i : ℤ ↦ tropicalHyperExponential n α hn hα (i : ℝ) := by
  apply monotone_int_of_le_succ
  intro i
  let k := i + 1
  have hi : (i : ℝ) ∈ Icc (((k - 1 : ℤ) : ℝ)) (k : ℝ) := by
    dsimp [k]
    constructor <;> norm_num
  have his : ((i + 1 : ℤ) : ℝ) ∈
      Icc (((k - 1 : ℤ) : ℝ)) (k : ℝ) := by
    dsimp [k]
    constructor <;> norm_num
  rw [tropicalHyperExponential_eq_piece n hα hn k hi,
    tropicalHyperExponential_eq_piece n hα hn k his]
  exact tropicalHyperExponentialPiece_monotoneOn n hα hn k hi his
    (by exact_mod_cast (show i ≤ i + 1 by omega))

/-- Proposition 3.8(i), monotonicity assertion. -/
theorem tropicalHyperExponential_monotone
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) :
    Monotone (tropicalHyperExponential n α hn hα) := by
  intro x y hxy
  let ix : ℤ := ⌊x⌋ + 1
  let iy : ℤ := ⌊y⌋ + 1
  have hxmem : x ∈ Icc (((ix - 1 : ℤ) : ℝ)) (ix : ℝ) := by
    dsimp [ix]
    constructor
    · simpa using Int.floor_le x
    · simpa only [Int.cast_add, Int.cast_one] using (Int.lt_floor_add_one x).le
  have hymem : y ∈ Icc (((iy - 1 : ℤ) : ℝ)) (iy : ℝ) := by
    dsimp [iy]
    constructor
    · simpa using Int.floor_le y
    · simpa only [Int.cast_add, Int.cast_one] using (Int.lt_floor_add_one y).le
  have hixiy : ix ≤ iy := by
    dsimp [ix, iy]
    simpa [add_comm] using add_le_add_right (Int.floor_mono hxy) 1
  by_cases heq : ix = iy
  · have hymem' : y ∈ Icc (((ix - 1 : ℤ) : ℝ)) (ix : ℝ) := by
      simpa [heq] using hymem
    rw [tropicalHyperExponential_eq_piece n hα hn ix hxmem,
      tropicalHyperExponential_eq_piece n hα hn ix hymem']
    exact tropicalHyperExponentialPiece_monotoneOn n hα hn ix hxmem hymem' hxy
  · have hlt : ix < iy := lt_of_le_of_ne hixiy heq
    have hxendMem : (ix : ℝ) ∈
        Icc (((ix - 1 : ℤ) : ℝ)) (ix : ℝ) := by
      constructor
      · exact_mod_cast (show ix - 1 ≤ ix by omega)
      · exact le_rfl
    have hybeginMem : (((iy - 1 : ℤ) : ℝ)) ∈
        Icc (((iy - 1 : ℤ) : ℝ)) (iy : ℝ) := by
      constructor
      · exact le_rfl
      · exact_mod_cast (show iy - 1 ≤ iy by omega)
    have hxend : tropicalHyperExponential n α hn hα x ≤
        tropicalHyperExponential n α hn hα (ix : ℝ) := by
      rw [tropicalHyperExponential_eq_piece n hα hn ix hxmem,
        tropicalHyperExponential_eq_piece n hα hn ix hxendMem]
      exact tropicalHyperExponentialPiece_monotoneOn n hα hn ix hxmem hxendMem hxmem.2
    have hybegin : tropicalHyperExponential n α hn hα ((iy - 1 : ℤ) : ℝ) ≤
        tropicalHyperExponential n α hn hα y := by
      rw [tropicalHyperExponential_eq_piece n hα hn iy hybeginMem,
        tropicalHyperExponential_eq_piece n hα hn iy hymem]
      exact tropicalHyperExponentialPiece_monotoneOn n hα hn iy hybeginMem hymem hymem.1
    calc
      tropicalHyperExponential n α hn hα x ≤
          tropicalHyperExponential n α hn hα (ix : ℝ) := hxend
      _ ≤ tropicalHyperExponential n α hn hα ((iy - 1 : ℤ) : ℝ) :=
        tropicalHyperExponential_grid_monotone n hα hn (by omega)
      _ ≤ tropicalHyperExponential n α hn hα y := hybegin

private theorem tropicalHyperExponentialTerm_nonneg
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) (i : ℤ) :
    0 ≤ tropicalHyperExponentialTerm n α i := by
  let k : ℤ := i + 1
  have hleft : (i : ℝ) ∈ Icc (((k - 1 : ℤ) : ℝ)) (k : ℝ) := by
    dsimp [k]
    constructor <;> norm_num
  have hright : ((i + 1 : ℤ) : ℝ) ∈
      Icc (((k - 1 : ℤ) : ℝ)) (k : ℝ) := by
    dsimp [k]
    constructor <;> norm_num
  have hmono := tropicalHyperExponentialPiece_monotoneOn n hα hn k
    hleft hright (by exact_mod_cast (show i ≤ i + 1 by omega))
  simp only [tropicalHyperExponentialPiece, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X] at hmono
  have hterm := tropicalHyperExponentialTerm_at_predecessor n α k
  rw [show k - 1 = i by dsimp [k]; omega] at hmono hterm
  rw [hterm]
  linarith

theorem tropicalHyperExponentialTail_nonneg
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) (m : ℤ) :
    0 ≤ tropicalHyperExponentialTail n α m := by
  unfold tropicalHyperExponentialTail
  exact tsum_nonneg fun k ↦ tropicalHyperExponentialTerm_nonneg n hα hn _

/-- The finite geometric moment used to make the paper's upper `O(1)`
estimate explicit. -/
def tropicalHyperExponentialMoment (n : ℕ) (α : ℝ) : ℝ :=
  ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ n * (α⁻¹) ^ k

theorem tropicalHyperExponentialMoment_nonneg
    (n : ℕ) {α : ℝ} (hα : 1 < α) :
    0 ≤ tropicalHyperExponentialMoment n α := by
  unfold tropicalHyperExponentialMoment
  exact tsum_nonneg fun k ↦ mul_nonneg (by positivity) (by positivity)

theorem tropicalHyperExponentialTail_abs_le
    (n : ℕ) {α : ℝ} (hα : 1 < α) (m : ℤ) :
    |tropicalHyperExponentialTail n α m| ≤
      (2 * |α ^ (m - 1)| * (|(m : ℝ)| + 2) ^ n) *
        tropicalHyperExponentialMoment n α := by
  let g : ℕ → ℝ := fun k ↦ ((k + 1 : ℕ) : ℝ) ^ n * (α⁻¹) ^ k
  let C : ℝ := 2 * |α ^ (m - 1)| * (|(m : ℝ)| + 2) ^ n
  have hq0 : 0 < α⁻¹ := inv_pos.mpr (lt_trans zero_lt_one hα)
  have hq1 : α⁻¹ < 1 := inv_lt_one₀ (lt_trans zero_lt_one hα) |>.2 hα
  have hg : Summable g := by
    dsimp [g]
    exact summable_succPow_mul_geometric n hq0 hq1
  have hnorm : Summable fun k : ℕ ↦
      ‖tropicalHyperExponentialTerm n α (m - 1 - (k : ℤ))‖ :=
    (summable_tropicalHyperExponentialTerm_tail n hα m).norm
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    |tropicalHyperExponentialTail n α m| =
        ‖∑' k : ℕ, tropicalHyperExponentialTerm n α
          (m - 1 - (k : ℤ))‖ := by
            simp [tropicalHyperExponentialTail, Real.norm_eq_abs]
    _ ≤ ∑' k : ℕ, ‖tropicalHyperExponentialTerm n α
          (m - 1 - (k : ℤ))‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, C * g k := hnorm.tsum_le_tsum
      (fun k ↦ by
        simpa [C, g] using tropicalHyperExponentialTerm_tail_bound n hα m k)
      (hg.mul_left C)
    _ = C * ∑' k : ℕ, g k := hg.tsum_mul_left C
    _ = (2 * |α ^ (m - 1)| * (|(m : ℝ)| + 2) ^ n) *
        tropicalHyperExponentialMoment n α := rfl

theorem tropicalHyperExponential_at_int
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) (i : ℤ) :
    tropicalHyperExponential n α hn hα (i : ℝ) =
      tropicalHyperExponentialTail n α i := by
  let k : ℤ := i + 1
  have hi : (i : ℝ) ∈ Icc (((k - 1 : ℤ) : ℝ)) (k : ℝ) := by
    dsimp [k]
    constructor <;> norm_num
  rw [tropicalHyperExponential_eq_piece n hα hn k hi]
  simp [tropicalHyperExponentialPiece, k]

/-- Proposition 3.8(i), nonnegativity assertion. -/
theorem tropicalHyperExponential_nonneg
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) (x : ℝ) :
    0 ≤ tropicalHyperExponential n α hn hα x := by
  have hfloor : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
  calc
    0 ≤ tropicalHyperExponential n α hn hα ((⌊x⌋ : ℤ) : ℝ) := by
      rw [tropicalHyperExponential_at_int n hα hn]
      exact tropicalHyperExponentialTail_nonneg n hα hn _
    _ ≤ tropicalHyperExponential n α hn hα x :=
      tropicalHyperExponential_monotone n hα hn hfloor

private theorem one_le_succ_pow_sub_pow
    (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ n - (k : ℝ) ^ n := by
  have hp : k ^ n < (k + 1) ^ n :=
    Nat.pow_lt_pow_left (Nat.lt_succ_self k) (by omega)
  have hp' : k ^ n + 1 ≤ (k + 1) ^ n := Nat.add_one_le_iff.mpr hp
  have hpcast : (k : ℝ) ^ n + 1 ≤ ((k + 1 : ℕ) : ℝ) ^ n := by
    exact_mod_cast hp'
  linarith

theorem tropicalHyperExponentialTerm_natCast
    (n k : ℕ) (α : ℝ) :
    tropicalHyperExponentialTerm n α (k : ℤ) =
      α ^ k * ((((k + 1 : ℕ) : ℝ) ^ n) - (k : ℝ) ^ n) := by
  rw [tropicalHyperExponentialTerm, zpow_natCast]
  simp [rightSign]

/-- The elementary lower estimate behind Proposition 3.8(ii).  It is
slightly stronger than what is needed asymptotically: for `r ≥ 1`, the last
completed positive increment alone contributes `α^(⌊r⌋-1)`. -/
theorem tropicalHyperExponential_lower_bound
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n)
    {r : ℝ} (hr : 1 ≤ r) :
    α ^ (⌊r⌋ - 1) ≤ tropicalHyperExponential n α hn hα r := by
  let m : ℤ := ⌊r⌋
  have hmpos : 0 < m := by
    dsimp [m]
    exact Int.floor_pos.mpr hr
  let k : ℕ := Int.toNat (m - 1)
  have hmk : m - 1 = (k : ℤ) := by
    dsimp [k]
    rw [Int.toNat_of_nonneg (by omega)]
  have htail : tropicalHyperExponentialTail n α m =
      tropicalHyperExponentialTerm n α (m - 1) +
        tropicalHyperExponentialTail n α (m - 1) := by
    simpa using tropicalHyperExponentialTail_succ n hα (m - 1)
  have hterm : α ^ (m - 1) ≤ tropicalHyperExponentialTerm n α (m - 1) := by
    rw [hmk, tropicalHyperExponentialTerm_natCast]
    rw [zpow_natCast]
    exact le_mul_of_one_le_right (pow_nonneg (le_of_lt (lt_trans zero_lt_one hα)) _)
      (one_le_succ_pow_sub_pow n hn k)
  have htailnonneg := tropicalHyperExponentialTail_nonneg n hα hn (m - 1)
  have hmle : (m : ℝ) ≤ r := by
    dsimp [m]
    exact Int.floor_le r
  calc
    α ^ (⌊r⌋ - 1) = α ^ (m - 1) := rfl
    _ ≤ tropicalHyperExponentialTerm n α (m - 1) := hterm
    _ ≤ tropicalHyperExponentialTail n α m := by rw [htail]; linarith
    _ = tropicalHyperExponential n α hn hα (m : ℝ) :=
      (tropicalHyperExponential_at_int n hα hn m).symm
    _ ≤ tropicalHyperExponential n α hn hα r :=
      tropicalHyperExponential_monotone n hα hn hmle

/-- Explicit polynomial-times-exponential upper estimate.  The constant is
the convergent geometric moment introduced above, so no hidden `O(1)` input
is used. -/
theorem tropicalHyperExponential_upper_bound
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n)
    {r : ℝ} (hr : 1 ≤ r) :
    tropicalHyperExponential n α hn hα r ≤
      (1 + 2 * tropicalHyperExponentialMoment n α) *
        α ^ (⌊r⌋ : ℤ) * (r + 2) ^ n := by
  let m : ℤ := ⌊r⌋
  let M : ℝ := tropicalHyperExponentialMoment n α
  have hαpos : 0 < α := lt_trans zero_lt_one hα
  have hM : 0 ≤ M := tropicalHyperExponentialMoment_nonneg n hα
  have hmpos : 0 < m := by
    dsimp [m]
    exact Int.floor_pos.mpr hr
  have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast hmpos.le
  have hmr : (m : ℝ) ≤ r := by dsimp [m]; exact Int.floor_le r
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hr2 : 0 ≤ r + 2 := by linarith
  have hm2le : (m : ℝ) + 2 ≤ r + 2 := by linarith
  have hpowmr : (m : ℝ) ^ n ≤ r ^ n :=
    pow_le_pow_left₀ hm0 hmr n
  have hpowr2 : r ^ n ≤ (r + 2) ^ n :=
    pow_le_pow_left₀ hr0 (by linarith) n
  have hαstep : α ^ (m - 1) ≤ α ^ m :=
    zpow_le_zpow_right₀ hα.le (by omega)
  have hfirst : α ^ m * (r ^ n - (m : ℝ) ^ n) ≤
      α ^ m * (r + 2) ^ n := by
    apply mul_le_mul_of_nonneg_left _ (zpow_nonneg hαpos.le _)
    linarith [pow_nonneg hm0 n]
  have htail0 := tropicalHyperExponentialTail_abs_le n hα m
  have htail : tropicalHyperExponentialTail n α m ≤
      2 * α ^ m * (r + 2) ^ n * M := by
    calc
      tropicalHyperExponentialTail n α m ≤
          |tropicalHyperExponentialTail n α m| := le_abs_self _
      _ ≤ (2 * |α ^ (m - 1)| * (|(m : ℝ)| + 2) ^ n) * M := htail0
      _ = (2 * α ^ (m - 1) * ((m : ℝ) + 2) ^ n) * M := by
        rw [abs_of_pos (zpow_pos hαpos _), abs_of_nonneg hm0]
      _ ≤ (2 * α ^ m * (r + 2) ^ n) * M := by
        gcongr
  rw [tropicalHyperExponential_apply n α hn hα,
    tropicalHyperExponentialRaw]
  have hrsign : rightSign r = 1 := rightSign_of_nonneg hr0
  rw [hrsign, one_pow, one_mul]
  change α ^ m * (r ^ n - (m : ℝ) ^ n) +
      tropicalHyperExponentialTail n α m ≤
        (1 + 2 * M) * α ^ m * (r + 2) ^ n
  calc
    α ^ m * (r ^ n - (m : ℝ) ^ n) +
        tropicalHyperExponentialTail n α m ≤
      α ^ m * (r + 2) ^ n + 2 * α ^ m * (r + 2) ^ n * M :=
        add_le_add hfirst htail
    _ = (1 + 2 * M) * α ^ m * (r + 2) ^ n := by ring

private theorem tropicalHyperExponential_integratedCounting_eq_zero
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n)
    {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) (r : ℝ) :
    integratedCounting j r (tropicalHyperExponential n α hn hα) = 0 := by
  classical
  have hempty : jthPolePoints (tropicalHyperExponential n α hn hα) j r = ∅ := by
    ext x
    constructor
    · intro hx
      exact (tropicalHyperExponential_isTropicalEntire n hα hn x j hj hjn
        (mem_jthPolePoints_iff.mp hx).2).elim
    · simp
  simp [integratedCounting, hempty]

/-- For this nonnegative entire example, the characteristic is literally the
symmetric endpoint mean; the counting part vanishes. -/
theorem characteristic_tropicalHyperExponential
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) (r : ℝ) :
    characteristic r (tropicalHyperExponential n α hn hα) =
      (tropicalHyperExponential n α hn hα r +
        tropicalHyperExponential n α hn hα (-r)) / 2 := by
  classical
  rw [characteristic]
  have hsum : (∑ j ∈ Finset.Icc 1 n,
      integratedCounting j r (tropicalHyperExponential n α hn hα)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hjmem
    exact tropicalHyperExponential_integratedCounting_eq_zero n hα hn
      (Finset.mem_Icc.mp hjmem).1 (Finset.mem_Icc.mp hjmem).2 r
  rw [hsum, add_zero]
  simp only [proximity, maxPlusPositivePart]
  rw [max_eq_left (tropicalHyperExponential_nonneg n hα hn r),
    max_eq_left (tropicalHyperExponential_nonneg n hα hn (-r))]

theorem characteristic_tropicalHyperExponential_lower
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n)
    {r : ℝ} (hr : 1 ≤ r) :
    α ^ (⌊r⌋ - 1) / 2 ≤
      characteristic r (tropicalHyperExponential n α hn hα) := by
  rw [characteristic_tropicalHyperExponential n hα hn]
  have hmain := tropicalHyperExponential_lower_bound n hα hn hr
  have hneg := tropicalHyperExponential_nonneg n hα hn (-r)
  linarith

theorem characteristic_tropicalHyperExponential_upper
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n)
    {r : ℝ} (hr : 1 ≤ r) :
    characteristic r (tropicalHyperExponential n α hn hα) ≤
      (1 + 2 * tropicalHyperExponentialMoment n α) *
        α ^ (⌊r⌋ : ℤ) * (r + 2) ^ n := by
  rw [characteristic_tropicalHyperExponential n hα hn]
  have hmono : tropicalHyperExponential n α hn hα (-r) ≤
      tropicalHyperExponential n α hn hα r := by
    exact tropicalHyperExponential_monotone n hα hn (by linarith)
  have hu := tropicalHyperExponential_upper_bound n hα hn hr
  linarith

/-- The explicit estimates imply the exact eventual linear bounds on
`log T` needed for the hyper-order computation. -/
theorem eventually_linear_log_characteristic_tropicalHyperExponential
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) :
    let M := tropicalHyperExponentialMoment n α
    let K := 1 + 2 * M
    let L := Real.log α
    ∀ᶠ r in atTop,
      (L / 2) * r ≤
          Real.log (characteristic r (tropicalHyperExponential n α hn hα)) ∧
        Real.log (characteristic r (tropicalHyperExponential n α hn hα)) ≤
          (K + L + 2 * (n : ℝ)) * r := by
  let M : ℝ := tropicalHyperExponentialMoment n α
  let K : ℝ := 1 + 2 * M
  let L : ℝ := Real.log α
  have hαpos : 0 < α := lt_trans zero_lt_one hα
  have hM : 0 ≤ M := tropicalHyperExponentialMoment_nonneg n hα
  have hK : 0 < K := by dsimp [K]; linarith
  have hL : 0 < L := by dsimp [L]; exact Real.log_pos hα
  let R : ℝ := (2 * L + Real.log 2) / (L / 2)
  filter_upwards [eventually_ge_atTop (max 1 R)] with r hrmax
  have hr : 1 ≤ r := le_trans (le_max_left _ _) hrmax
  have hRr : R ≤ r := le_trans (le_max_right _ _) hrmax
  let m : ℤ := ⌊r⌋
  have hmpos : 0 < m := by dsimp [m]; exact Int.floor_pos.mpr hr
  have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast hmpos.le
  have hmr : (m : ℝ) ≤ r := by dsimp [m]; exact Int.floor_le r
  have hrm : r - 1 ≤ (m : ℝ) := by
    have h := Int.lt_floor_add_one r
    dsimp [m]
    linarith
  have hlower := characteristic_tropicalHyperExponential_lower n hα hn hr
  have hlowerpos : 0 < α ^ (m - 1) / 2 := by positivity
  have hTpos : 0 < characteristic r (tropicalHyperExponential n α hn hα) := by
    exact lt_of_lt_of_le (by simpa [m] using hlowerpos) hlower
  have hloglower : Real.log (α ^ (m - 1) / 2) ≤
      Real.log (characteristic r (tropicalHyperExponential n α hn hα)) := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hlowerpos) (Set.mem_Ioi.mpr hTpos)
      (by simpa [m] using hlower)
  have hlarge : 2 * L + Real.log 2 ≤ (L / 2) * r := by
    have hLhalf : 0 < L / 2 := by positivity
    have := (div_le_iff₀ hLhalf).mp hRr
    simpa [R, mul_comm] using this
  have hlowerLinear : (L / 2) * r ≤
      Real.log (α ^ (m - 1) / 2) := by
    rw [Real.log_div (zpow_ne_zero _ hαpos.ne') (by norm_num),
      Real.log_zpow]
    rw [Int.cast_sub, Int.cast_one]
    change (L / 2) * r ≤ ((m : ℝ) - 1) * L - Real.log 2
    nlinarith
  have hleft : (L / 2) * r ≤
      Real.log (characteristic r (tropicalHyperExponential n α hn hα)) :=
    hlowerLinear.trans hloglower

  have hu := characteristic_tropicalHyperExponential_upper n hα hn hr
  let U : ℝ := K * α ^ m * (r + 2) ^ n
  have hr2pos : 0 < r + 2 := by linarith
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hTU : characteristic r (tropicalHyperExponential n α hn hα) ≤ U := by
    simpa [U, K, M, m] using hu
  have hlogupper :
      Real.log (characteristic r (tropicalHyperExponential n α hn hα)) ≤
        Real.log U :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hTpos) (Set.mem_Ioi.mpr hUpos) hTU
  have hlogK : Real.log K ≤ K :=
    (Real.log_le_sub_one_of_pos hK).trans (by linarith)
  have hlogr2 : Real.log (r + 2) ≤ r + 1 := by
    have := Real.log_le_sub_one_of_pos hr2pos
    linarith
  have hlogU : Real.log U ≤ (K + L + 2 * (n : ℝ)) * r := by
    have hzpow : α ^ m ≠ 0 := zpow_ne_zero _ hαpos.ne'
    have hpow : (r + 2) ^ n ≠ 0 := pow_ne_zero _ hr2pos.ne'
    rw [show Real.log U = Real.log K + (m : ℝ) * L +
        (n : ℝ) * Real.log (r + 2) by
      dsimp [U, L]
      rw [Real.log_mul (mul_ne_zero hK.ne' hzpow) hpow,
        Real.log_mul hK.ne' hzpow, Real.log_zpow, Real.log_pow]]
    have hKL : (m : ℝ) * L ≤ r * L :=
      mul_le_mul_of_nonneg_right hmr hL.le
    have hKr : K ≤ K * r := by nlinarith
    have hnlog : (n : ℝ) * Real.log (r + 2) ≤
        2 * (n : ℝ) * r := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : (n : ℝ) * Real.log (r + 2) ≤ (n : ℝ) * (r + 1) :=
        mul_le_mul_of_nonneg_left hlogr2 hn0
      nlinarith
    nlinarith
  exact ⟨hleft, hlogupper.trans hlogU⟩

/-- The characteristic of the hyper-exponential tends to infinity.  This
is recorded separately because the counterexample after Corollary 6.3 uses
it to turn exact counting identities into the printed `(1+o(1))` forms. -/
theorem characteristic_tropicalHyperExponential_tendsto_atTop
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) :
    Tendsto (fun r ↦ characteristic r
      (tropicalHyperExponential n α hn hα)) atTop atTop := by
  let L : ℝ := Real.log α
  have hL : 0 < L / 2 := by
    dsimp [L]
    exact half_pos (Real.log_pos hα)
  have hlinear : Tendsto (fun r : ℝ ↦ (L / 2) * r) atTop atTop :=
    tendsto_id.const_mul_atTop' hL
  have hb := eventually_linear_log_characteristic_tropicalHyperExponential
    n hα hn
  have hlog : Tendsto (fun r ↦ Real.log (characteristic r
      (tropicalHyperExponential n α hn hα))) atTop atTop :=
    tendsto_atTop_mono' atTop (hb.mono fun r hr ↦ hr.1) hlinear
  have hexp := Real.tendsto_exp_atTop.comp hlog
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hlower := characteristic_tropicalHyperExponential_lower n hα hn hr
  have hpos : 0 < characteristic r
      (tropicalHyperExponential n α hn hα) :=
    (by positivity : 0 < α ^ (⌊r⌋ - 1) / 2).trans_le hlower
  exact Real.exp_log hpos

/-- Proposition 3.8(ii): the tropical hyper-exponential has hyper-order
exactly one. -/
theorem tropicalHyperExponential_hyperOrder
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) :
    hyperOrder (tropicalHyperExponential n α hn hα) = (1 : EReal) := by
  let M : ℝ := tropicalHyperExponentialMoment n α
  let K : ℝ := 1 + 2 * M
  let L : ℝ := Real.log α
  have hM : 0 ≤ M := tropicalHyperExponentialMoment_nonneg n hα
  have hc : 0 < L / 2 := by
    have hlog : 0 < Real.log α := Real.log_pos hα
    dsimp [L]
    linarith
  have hC : 0 < K + L + 2 * (n : ℝ) := by
    have hL : 0 < L := by dsimp [L]; exact Real.log_pos hα
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    dsimp [K]
    linarith
  apply hyperOrder_eq_one_of_eventually_linear_log_characteristic
    (tropicalHyperExponential n α hn hα) hc hC
  simpa [M, K, L] using
    eventually_linear_log_characteristic_tropicalHyperExponential n hα hn

/-- Proposition 3.8 in one statement, with the paper's convention
`n ∈ ℕ = {1,2,…}` represented explicitly by `1 ≤ n`. -/
theorem proposition_3_8
    (n : ℕ) {α : ℝ} (hα : 1 < α) (hn : 1 ≤ n) :
    (IsTropicalEntire (tropicalHyperExponential n α hn hα) ∧
      Monotone (tropicalHyperExponential n α hn hα) ∧
      (∀ x, 0 ≤ tropicalHyperExponential n α hn hα x)) ∧
      hyperOrder (tropicalHyperExponential n α hn hα) = (1 : EReal) := by
  exact ⟨⟨tropicalHyperExponential_isTropicalEntire n hα hn,
    tropicalHyperExponential_monotone n hα hn,
    tropicalHyperExponential_nonneg n hα hn⟩,
    tropicalHyperExponential_hyperOrder n hα hn⟩

/-- If `n = 0`, Definition 3.7 is identically zero.  Thus Proposition 3.8(ii)
requires the positive-integer convention `1 ≤ n`. -/
@[simp]
theorem tropicalHyperExponentialRaw_zeroOrder (α x : ℝ) :
    tropicalHyperExponentialRaw 0 α x = 0 := by
  simp [tropicalHyperExponentialRaw, tropicalHyperExponentialTerm]

end

end NthTropicalNevanlinna
