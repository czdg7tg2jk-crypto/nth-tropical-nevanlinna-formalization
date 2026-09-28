import NthTropicalNevanlinna.Function.Entire
import NthTropicalNevanlinna.Function.PolynomialJet

/-!
# Endpoint mean for tropical entire functions

This file formalizes Proposition 2.2.  The proof follows the paper's finite
Taylor telescoping argument, with redundant cutPoints contributing zero.
-/

namespace NthTropicalNevanlinna

open Set
open scoped BigOperators

private theorem right_piece_step
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) {i : ℤ} (hi : 0 < i) (y : ℝ) :
    (f.presentation.piece (i + 1)).eval y - (f.presentation.piece i).eval y =
      ∑ j ∈ Finset.range (n + 1),
        multiplicityAtCutPoint f j i * (y - f.presentation.cutPoint i) ^ j := by
  rw [polynomial_eval_sub_eq_sum_jet_sub
    (f.presentation.piece i) (f.presentation.piece (i + 1))
    (f.presentation.piece_natDegree_le i)
    (f.presentation.piece_natDegree_le (i + 1))
    (f.presentation.cutPoint i) y]
  apply Finset.sum_congr rfl
  intro j hj
  rw [multiplicityAtCutPoint_of_pos_index f j hi]

private theorem left_piece_step
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) {i : ℤ} (hi : i < 0) (y : ℝ) :
    (f.presentation.piece i).eval y - (f.presentation.piece (i + 1)).eval y =
      ∑ j ∈ Finset.range (n + 1),
        multiplicityAtCutPoint f j i * (f.presentation.cutPoint i - y) ^ j := by
  rw [polynomial_eval_sub_eq_sum_jet_sub
    (f.presentation.piece (i + 1)) (f.presentation.piece i)
    (f.presentation.piece_natDegree_le (i + 1))
    (f.presentation.piece_natDegree_le i)
    (f.presentation.cutPoint i) y]
  apply Finset.sum_congr rfl
  intro j hj
  rw [multiplicityAtCutPoint_of_neg_index' f j hi]
  have hsub : y - f.presentation.cutPoint i =
      -(f.presentation.cutPoint i - y) := by ring
  rw [hsub, neg_pow]
  ring

private theorem central_piece_sum
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (r : ℝ) :
    (f.presentation.piece 1).eval r + (f.presentation.piece 0).eval (-r) =
      ∑ j ∈ Finset.range (n + 1), multiplicityAtCutPoint f j 0 * r ^ j := by
  rw [polynomial_eval_add_reflection_eq_sum_signedJets
    (f.presentation.piece 1) (f.presentation.piece 0)
    (f.presentation.piece_natDegree_le 1)
    (f.presentation.piece_natDegree_le 0) r]
  apply Finset.sum_congr rfl
  intro j hj
  rw [multiplicityAtCutPoint_zero]

private theorem multiplicity_zero_zero_mul
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (r : ℝ) :
    multiplicityAtCutPoint f 0 0 * r ^ 0 = 2 * f 0 := by
  rw [multiplicityAtCutPoint_zero]
  have hleft := f.presentation.eq_piece 0
    (show 0 ∈ Icc (f.presentation.cutPoint (0 - 1))
      (f.presentation.cutPoint 0) by
      constructor
      · rw [← f.presentation.cutPoint_zero]
        exact (f.presentation.cutPoint_strictMono (by omega)).le
      · exact f.presentation.cutPoint_zero.ge)
  have hright := f.presentation.eq_piece 1
    (show 0 ∈ Icc (f.presentation.cutPoint (1 - 1))
      (f.presentation.cutPoint 1) by
      constructor
      · simp [f.presentation.cutPoint_zero]
      · rw [← f.presentation.cutPoint_zero]
        exact (f.presentation.cutPoint_strictMono (by omega)).le)
  simp only [normalizedPolynomialJet, Polynomial.hasseDeriv_zero, LinearMap.id_coe,
    id_eq, pow_zero, mul_one]
  rw [← hleft, ← hright]
  ring

private theorem right_step_nonneg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (hf : IsTropicalEntire f)
    {i : ℤ} (hi : 0 < i) {y : ℝ} (hiy : f.presentation.cutPoint i ≤ y) :
    (f.presentation.piece i).eval y ≤ (f.presentation.piece (i + 1)).eval y := by
  rw [← sub_nonneg, right_piece_step f hi y]
  apply Finset.sum_nonneg
  intro j hj
  rcases j.eq_zero_or_pos with rfl | hjpos
  · simp only [pow_zero, mul_one, multiplicityAtCutPoint_of_pos_index f 0 hi,
      normalizedPolynomialJet, Polynomial.hasseDeriv_zero, LinearMap.id_coe, id_eq]
    rw [f.presentation.piece_eval_cutPoint_eq i]
    simp
  · apply mul_nonneg
    · rw [← multiplicity_cutPoint]
      exact (isTropicalEntire_iff_multiplicity_nonneg f).mp hf _ j hjpos
        (by have := Finset.mem_range.mp hj; omega)
    · exact pow_nonneg (sub_nonneg.mpr hiy) j

private theorem left_step_nonneg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (hf : IsTropicalEntire f)
    {i : ℤ} (hi : i < 0) {y : ℝ} (hyi : y ≤ f.presentation.cutPoint i) :
    (f.presentation.piece (i + 1)).eval y ≤ (f.presentation.piece i).eval y := by
  rw [← sub_nonneg, left_piece_step f hi y]
  apply Finset.sum_nonneg
  intro j hj
  rcases j.eq_zero_or_pos with rfl | hjpos
  · simp only [pow_zero, mul_one, multiplicityAtCutPoint_of_neg_index' f 0 hi,
      normalizedPolynomialJet, Polynomial.hasseDeriv_zero, LinearMap.id_coe, id_eq]
    rw [f.presentation.piece_eval_cutPoint_eq i]
    norm_num
  · apply mul_nonneg
    · rw [← multiplicity_cutPoint]
      exact (isTropicalEntire_iff_multiplicity_nonneg f).mp hf _ j hjpos
        (by have := Finset.mem_range.mp hj; omega)
    · exact pow_nonneg (sub_nonneg.mpr hyi) j

private theorem right_central_piece_le
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (hf : IsTropicalEntire f)
    (m : ℕ) {y : ℝ} (hy : f.presentation.cutPoint (m : ℤ) ≤ y) :
    (f.presentation.piece 1).eval y ≤
      (f.presentation.piece ((m : ℤ) + 1)).eval y := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm : f.presentation.cutPoint (m : ℤ) ≤ y :=
        (f.presentation.cutPoint_strictMono (by omega)).le.trans hy
      exact ih hm |>.trans (right_step_nonneg f hf (i := (m : ℤ) + 1) (by omega) hy)

private theorem left_central_piece_le
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (hf : IsTropicalEntire f)
    (m : ℕ) {y : ℝ} (hy : y ≤ f.presentation.cutPoint (-(m : ℤ))) :
    (f.presentation.piece 0).eval y ≤
      (f.presentation.piece (-(m : ℤ))).eval y := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm : y ≤ f.presentation.cutPoint (-(m : ℤ)) :=
        hy.trans (f.presentation.cutPoint_strictMono (by omega)).le
      have hs := left_step_nonneg f hf
        (i := -((m : ℤ) + 1)) (by omega) (by simpa using hy)
      have hidxRight : -((m : ℤ) + 1) + 1 = -(m : ℤ) := by omega
      have hidxLeft : -((m : ℤ) + 1) = -((m + 1 : ℕ) : ℤ) := by omega
      have hidxRight' : -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by omega
      have hs' : (f.presentation.piece (-(m : ℤ))).eval y ≤
          (f.presentation.piece (-((m + 1 : ℕ) : ℤ))).eval y := by
        simpa [hidxRight, hidxLeft, hidxRight'] using hs
      exact (ih hm).trans hs'

private theorem central_mean_bound
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (hf : IsTropicalEntire f)
    {r : ℝ} (hr : 0 ≤ r) :
    2 * f 0 ≤ (f.presentation.piece 1).eval r + (f.presentation.piece 0).eval (-r) := by
  rw [central_piece_sum]
  rw [← multiplicity_zero_zero_mul f r]
  rw [← Finset.add_sum_erase (a := 0) (Finset.range (n + 1))
    (fun j ↦ multiplicityAtCutPoint f j 0 * r ^ j) (by simp)]
  exact le_add_of_nonneg_right <| Finset.sum_nonneg fun j hj ↦ by
    have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
    have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    apply mul_nonneg
    · rw [← multiplicity_cutPoint]
      exact (isTropicalEntire_iff_multiplicity_nonneg f).mp hf _ j hjpos
        (by have := Finset.mem_range.mp (Finset.mem_erase.mp hj).2; omega)
    · exact pow_nonneg hr j

/-- Proposition 2.2: an entire function lies below its symmetric endpoint mean. -/
theorem entire_midpoint_le_endpointMean
    {n : ℕ} (_hn : 0 < n) (f : NthTropicalMeromorphicFunction n) (hf : IsTropicalEntire f)
    {r : ℝ} (hr : 0 < r) :
    f 0 ≤ (f r + f (-r)) / 2 := by
  obtain ⟨ir, hirLower, hirUpper⟩ := f.presentation.exists_mem_interval r
  have hir : 1 ≤ ir := by
    by_contra h
    have hi0 : ir ≤ 0 := by omega
    have hbp : f.presentation.cutPoint ir ≤ 0 := by
      rw [← f.presentation.cutPoint_zero]
      exact f.presentation.cutPoint_strictMono.monotone hi0
    linarith
  let mr := (ir - 1).toNat
  have hmr : (mr : ℤ) = ir - 1 := Int.toNat_of_nonneg (by omega)
  have hright : (f.presentation.piece 1).eval r ≤ f r := by
    rw [f.presentation.eq_piece ir ⟨hirLower.le, hirUpper⟩]
    have hb : f.presentation.cutPoint (mr : ℤ) ≤ r := by
      rw [hmr]
      exact hirLower.le
    have h := right_central_piece_le f hf mr hb
    have hidx : (mr : ℤ) + 1 = ir := by omega
    simpa [hidx] using h

  obtain ⟨il, hilLower, hilUpper⟩ := f.presentation.exists_mem_interval (-r)
  have hil : il ≤ 0 := by
    by_contra h
    have hi1 : 1 ≤ il := by omega
    have hbp : 0 ≤ f.presentation.cutPoint (il - 1) := by
      rw [← f.presentation.cutPoint_zero]
      exact f.presentation.cutPoint_strictMono.monotone (by omega)
    linarith
  let ml := (-il).toNat
  have hml : (ml : ℤ) = -il := Int.toNat_of_nonneg (by omega)
  have hleft : (f.presentation.piece 0).eval (-r) ≤ f (-r) := by
    rw [f.presentation.eq_piece il ⟨hilLower.le, hilUpper⟩]
    have hidx : -(ml : ℤ) = il := by omega
    have hb : -r ≤ f.presentation.cutPoint (-(ml : ℤ)) := by
      simpa [hidx] using hilUpper
    have h := left_central_piece_le f hf ml hb
    simpa [hidx] using h

  have hcentral := central_mean_bound f hf hr.le
  have hsum : 2 * f 0 ≤ f r + f (-r) := by linarith
  linarith

private theorem right_step_eq
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (hf : IsTropicalNowhereVanishingEntire f) {i : ℤ} (hi : 0 < i) (y : ℝ) :
    (f.presentation.piece i).eval y = (f.presentation.piece (i + 1)).eval y := by
  symm
  rw [← sub_eq_zero, right_piece_step f hi y]
  apply Finset.sum_eq_zero
  intro j hj
  rcases j.eq_zero_or_pos with rfl | hjpos
  · simp only [pow_zero, mul_one, multiplicityAtCutPoint_of_pos_index f 0 hi,
      normalizedPolynomialJet, Polynomial.hasseDeriv_zero, LinearMap.id_coe, id_eq]
    rw [f.presentation.piece_eval_cutPoint_eq i]
    simp
  · rw [← multiplicity_cutPoint,
      (isTropicalNowhereVanishingEntire_iff_multiplicity_eq_zero f).mp hf
        _ j hjpos (by have := Finset.mem_range.mp hj; omega)]
    simp

private theorem left_step_eq
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (hf : IsTropicalNowhereVanishingEntire f) {i : ℤ} (hi : i < 0) (y : ℝ) :
    (f.presentation.piece (i + 1)).eval y = (f.presentation.piece i).eval y := by
  symm
  rw [← sub_eq_zero, left_piece_step f hi y]
  apply Finset.sum_eq_zero
  intro j hj
  rcases j.eq_zero_or_pos with rfl | hjpos
  · simp only [pow_zero, mul_one, multiplicityAtCutPoint_of_neg_index' f 0 hi,
      normalizedPolynomialJet, Polynomial.hasseDeriv_zero, LinearMap.id_coe, id_eq]
    rw [f.presentation.piece_eval_cutPoint_eq i]
    norm_num
  · rw [← multiplicity_cutPoint,
      (isTropicalNowhereVanishingEntire_iff_multiplicity_eq_zero f).mp hf
        _ j hjpos (by have := Finset.mem_range.mp hj; omega)]
    simp

private theorem right_central_piece_eq
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (hf : IsTropicalNowhereVanishingEntire f) (m : ℕ) (y : ℝ) :
    (f.presentation.piece 1).eval y =
      (f.presentation.piece ((m : ℤ) + 1)).eval y := by
  induction m with
  | zero => simp
  | succ m ih =>
      exact ih.trans (right_step_eq f hf (i := (m : ℤ) + 1) (by omega) y)

private theorem left_central_piece_eq
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (hf : IsTropicalNowhereVanishingEntire f) (m : ℕ) (y : ℝ) :
    (f.presentation.piece 0).eval y =
      (f.presentation.piece (-(m : ℤ))).eval y := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hs := left_step_eq f hf (i := -((m : ℤ) + 1)) (by omega) y
      have hidxRight : -((m : ℤ) + 1) + 1 = -(m : ℤ) := by omega
      have hidxLeft : -((m : ℤ) + 1) = -((m + 1 : ℕ) : ℤ) := by omega
      have hidxRight' : -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by omega
      have hs' : (f.presentation.piece (-(m : ℤ))).eval y =
          (f.presentation.piece (-((m + 1 : ℕ) : ℤ))).eval y := by
        simpa [hidxRight, hidxLeft, hidxRight'] using hs
      exact ih.trans hs'

private theorem central_mean_eq
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (hf : IsTropicalNowhereVanishingEntire f) (r : ℝ) :
    (f.presentation.piece 1).eval r + (f.presentation.piece 0).eval (-r) = 2 * f 0 := by
  rw [central_piece_sum]
  rw [← Finset.add_sum_erase (a := 0) (Finset.range (n + 1))
    (fun j ↦ multiplicityAtCutPoint f j 0 * r ^ j) (by simp)]
  rw [multiplicity_zero_zero_mul]
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  intro j hj
  have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
  have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
  rw [← multiplicity_cutPoint,
    (isTropicalNowhereVanishingEntire_iff_multiplicity_eq_zero f).mp hf
      _ j hjpos (by have := Finset.mem_range.mp (Finset.mem_erase.mp hj).2; omega)]
  simp

/-- The equality clause of Proposition 2.2, strengthened to include order
zero (the proof does not use positivity of the order). -/
theorem nowhereVanishingEntire_endpointMean_eq_allOrder
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (hf : IsTropicalNowhereVanishingEntire f) {r : ℝ} (hr : 0 < r) :
    (f r + f (-r)) / 2 = f 0 := by
  obtain ⟨ir, hirLower, hirUpper⟩ := f.presentation.exists_mem_interval r
  have hir : 1 ≤ ir := by
    by_contra h
    have hi0 : ir ≤ 0 := by omega
    have hbp : f.presentation.cutPoint ir ≤ 0 := by
      rw [← f.presentation.cutPoint_zero]
      exact f.presentation.cutPoint_strictMono.monotone hi0
    linarith
  let mr := (ir - 1).toNat
  have hmr : (mr : ℤ) = ir - 1 := Int.toNat_of_nonneg (by omega)
  have hright : (f.presentation.piece 1).eval r = f r := by
    rw [f.presentation.eq_piece ir ⟨hirLower.le, hirUpper⟩]
    have h := right_central_piece_eq f hf mr r
    have hidx : (mr : ℤ) + 1 = ir := by omega
    simpa [hidx] using h

  obtain ⟨il, hilLower, hilUpper⟩ := f.presentation.exists_mem_interval (-r)
  have hil : il ≤ 0 := by
    by_contra h
    have hi1 : 1 ≤ il := by omega
    have hbp : 0 ≤ f.presentation.cutPoint (il - 1) := by
      rw [← f.presentation.cutPoint_zero]
      exact f.presentation.cutPoint_strictMono.monotone (by omega)
    linarith
  let ml := (-il).toNat
  have hml : (ml : ℤ) = -il := Int.toNat_of_nonneg (by omega)
  have hleft : (f.presentation.piece 0).eval (-r) = f (-r) := by
    rw [f.presentation.eq_piece il ⟨hilLower.le, hilUpper⟩]
    have hidx : -(ml : ℤ) = il := by omega
    have h := left_central_piece_eq f hf ml (-r)
    simpa [hidx] using h

  have hcentral := central_mean_eq f hf r
  rw [← hright, ← hleft]
  linarith

/-- The equality clause of Proposition 2.2 with the paper's positive-order
hypothesis retained in the public statement. -/
theorem nowhereVanishingEntire_endpointMean_eq
    {n : ℕ} (_hn : 0 < n) (f : NthTropicalMeromorphicFunction n)
    (hf : IsTropicalNowhereVanishingEntire f) {r : ℝ} (hr : 0 < r) :
    (f r + f (-r)) / 2 = f 0 :=
  nowhereVanishingEntire_endpointMean_eq_allOrder f hf hr

end NthTropicalNevanlinna
