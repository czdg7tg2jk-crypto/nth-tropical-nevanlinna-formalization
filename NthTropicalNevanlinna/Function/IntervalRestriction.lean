import NthTropicalNevanlinna.Function.IntervalPresentation

/-!
# Restricting a global presentation to a bounded interval

This file supplies the bookkeeping bridge between the globally indexed
`PolynomialPresentation` and the finite `IntervalPolynomialPresentation`
used in the Poisson--Jensen proof.
-/

open Set

namespace NthTropicalNevanlinna

noncomputable section

private def restrictedCutPoint
    {n m : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    (a b : ℝ) (s : ℤ) (i : Fin (m + 2)) : ℝ :=
  if i.val = 0 then a
  else if i.val = m + 1 then b
  else P.cutPoint (s + (i.val - 1 : ℕ))

private def restrictedPiece
    {n m : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    (s : ℤ) (i : Fin (m + 1)) : Polynomial ℝ :=
  P.piece (s + i.val)

/--
Restrict consecutive global pieces `s,...,t` to arbitrary endpoints `a<b`.
The four endpoint inequalities say precisely that `a` lies in piece `s`
and `b` lies in piece `t`.  The equality `hm` records `m=t-s`.
-/
def intervalPresentationOfGlobalRange
    {n m : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    {a b : ℝ} {s t : ℤ}
    (hm : (m : ℤ) = t - s) (hab : a < b)
    (haLower : P.cutPoint (s - 1) ≤ a) (haUpper : a < P.cutPoint s)
    (hbLower : P.cutPoint (t - 1) < b) (hbUpper : b ≤ P.cutPoint t) :
    IntervalPolynomialPresentation n m f a b where
  cutPoint := restrictedCutPoint P a b s
  piece := restrictedPiece P s
  cutPoint_strictMono := by
    intro i j hij
    have hijv : i.val < j.val := hij
    have hjpos : j.val ≠ 0 := by omega
    have hilast : i.val ≠ m + 1 := by omega
    by_cases hi0 : i.val = 0
    · rw [restrictedCutPoint, if_pos hi0]
      by_cases hjlast : j.val = m + 1
      · rw [restrictedCutPoint, if_neg hjpos, if_pos hjlast]
        exact hab
      · rw [restrictedCutPoint, if_neg hjpos, if_neg hjlast]
        have hsle : s ≤ s + (j.val - 1 : ℕ) := by omega
        exact haUpper.trans_le (P.cutPoint_strictMono.monotone hsle)
    · rw [restrictedCutPoint, if_neg hi0, if_neg hilast]
      by_cases hjlast : j.val = m + 1
      · rw [restrictedCutPoint, if_neg hjpos, if_pos hjlast]
        have hindex : s + (i.val - 1 : ℕ) ≤ t - 1 := by omega
        exact (P.cutPoint_strictMono.monotone hindex).trans_lt hbLower
      · rw [restrictedCutPoint, if_neg hjpos, if_neg hjlast]
        apply P.cutPoint_strictMono
        omega
  cutPoint_first := by
    simp [restrictedCutPoint]
  cutPoint_last := by
    simp [restrictedCutPoint]
  piece_natDegree_le := by
    intro i
    exact P.piece_natDegree_le (s + i.val)
  eq_piece := by
    intro i y hy
    apply P.eq_piece (s + i.val)
    constructor
    · by_cases hi0 : i.val = 0
      · have hlocal : a ≤ y := by
          simpa [restrictedCutPoint, hi0] using hy.1
        have hindex : s + (i.val : ℤ) - 1 = s - 1 := by omega
        rw [hindex]
        exact haLower.trans hlocal
      · have hlocal :
            P.cutPoint (s + (i.val - 1 : ℕ)) ≤ y := by
          have hilast : i.val ≠ m + 1 := by omega
          simpa [restrictedCutPoint, hi0, hilast] using hy.1
        have hindex :
            s + (i.val : ℤ) - 1 = s + ((i.val - 1 : ℕ) : ℤ) := by
          omega
        rw [hindex]
        exact hlocal
    · by_cases hilast : i.val = m
      · have hlocal : y ≤ b := by
          have hpos : i.val + 1 ≠ 0 := by omega
          simpa [restrictedCutPoint, hilast, hpos] using hy.2
        have hindex : s + (i.val : ℤ) = t := by omega
        rw [hindex]
        exact hlocal.trans hbUpper
      · have hlocal : y ≤ P.cutPoint (s + i.val) := by
          have hpos : i.val + 1 ≠ 0 := by omega
          have hnotlast : i.val + 1 ≠ m + 1 := by omega
          simpa [restrictedCutPoint, hpos, hnotlast, hilast] using hy.2
        exact hlocal

@[simp]
theorem intervalPresentationOfGlobalRange_internalCut
    {n m : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    {a b : ℝ} {s t : ℤ}
    (hm : (m : ℤ) = t - s) (hab : a < b)
    (haLower : P.cutPoint (s - 1) ≤ a) (haUpper : a < P.cutPoint s)
    (hbLower : P.cutPoint (t - 1) < b) (hbUpper : b ≤ P.cutPoint t)
    (i : Fin m) :
    (intervalPresentationOfGlobalRange P hm hab haLower haUpper hbLower hbUpper).internalCut i =
      P.cutPoint (s + i.val) := by
  have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
  simp [intervalPresentationOfGlobalRange,
    IntervalPolynomialPresentation.internalCut, restrictedCutPoint, hi]

/-- Every nondegenerate bounded interval admits a finite presentation. -/
theorem PolynomialPresentation.exists_intervalPresentation
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    {a b : ℝ} (hab : a < b) :
    ∃ m : ℕ, Nonempty (IntervalPolynomialPresentation n m f a b) := by
  let ia := presentationIntervalIndex P a
  let ib := presentationIntervalIndex P b
  have ha := presentationIntervalIndex_mem P a
  have hb := presentationIntervalIndex_mem P b
  change a ∈ Ioc (P.cutPoint (ia - 1)) (P.cutPoint ia) at ha
  change b ∈ Ioc (P.cutPoint (ib - 1)) (P.cutPoint ib) at hb
  have hiab : ia ≤ ib := by
    by_contra h
    have hibia : ib < ia := lt_of_not_ge h
    have hcut : P.cutPoint ib ≤ P.cutPoint (ia - 1) :=
      P.cutPoint_strictMono.monotone (by omega)
    linarith [ha.1, hb.2]
  let s := if a = P.cutPoint ia then ia + 1 else ia
  have hsib : s ≤ ib := by
    dsimp [s]
    split_ifs with heq
    · have hstrict : ia < ib := by
        by_contra h
        have hib : ib ≤ ia := le_of_not_gt h
        have hcut : P.cutPoint ib ≤ P.cutPoint ia :=
          P.cutPoint_strictMono.monotone hib
        linarith [hb.2]
      omega
    · exact hiab
  let m := Int.toNat (ib - s)
  have hm : (m : ℤ) = ib - s := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hsib)
  have haLower : P.cutPoint (s - 1) ≤ a := by
    dsimp [s]
    split_ifs with heq
    · simp [heq]
    · exact ha.1.le
  have haUpper : a < P.cutPoint s := by
    dsimp [s]
    split_ifs with heq
    · rw [heq]
      exact P.cutPoint_strictMono (by omega)
    · exact lt_of_le_of_ne ha.2 heq
  exact ⟨m, ⟨intervalPresentationOfGlobalRange P hm hab
    haLower haUpper hb.1 hb.2⟩⟩

/--
If a global cut lies strictly inside `[a,b]`, the restricted finite
presentation can be chosen with that cut among its internal cuts.
-/
theorem PolynomialPresentation.exists_intervalPresentation_with_cut
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    {a b : ℝ} (hab : a < b) (k : ℤ)
    (hak : a < P.cutPoint k) (hkb : P.cutPoint k < b) :
    ∃ m : ℕ, ∃ Q : IntervalPolynomialPresentation n m f a b,
      ∃ i : Fin m, Q.internalCut i = P.cutPoint k := by
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
    exact (not_lt_of_ge hak.le) (hcut.trans_lt ha.1)
  have hkib : k < ib := by
    by_contra h
    have hibk : ib ≤ k := le_of_not_gt h
    have hcut : P.cutPoint ib ≤ P.cutPoint k :=
      P.cutPoint_strictMono.monotone hibk
    exact (not_lt_of_ge (hb.2.trans hcut)) hkb
  let s := if a = P.cutPoint ia then ia + 1 else ia
  have hsk : s ≤ k := by
    dsimp [s]
    split_ifs with heq
    · have hne : ia ≠ k := by
        intro hik
        subst k
        linarith
      omega
    · exact hiak
  have hsib : s ≤ ib := hsk.trans hkib.le
  let m := Int.toNat (ib - s)
  have hm : (m : ℤ) = ib - s :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hsib)
  have haLower : P.cutPoint (s - 1) ≤ a := by
    dsimp [s]
    split_ifs with heq
    · simp [heq]
    · exact ha.1.le
  have haUpper : a < P.cutPoint s := by
    dsimp [s]
    split_ifs with heq
    · rw [heq]
      exact P.cutPoint_strictMono (by omega)
    · exact lt_of_le_of_ne ha.2 heq
  let Q := intervalPresentationOfGlobalRange P hm hab
    haLower haUpper hb.1 hb.2
  have hnonneg : 0 ≤ k - s := sub_nonneg.mpr hsk
  have hkmz : (Int.toNat (k - s) : ℤ) < (m : ℤ) := by
    rw [Int.toNat_of_nonneg hnonneg, hm]
    omega
  have hkm : Int.toNat (k - s) < m := by exact_mod_cast hkmz
  let i : Fin m := ⟨Int.toNat (k - s), hkm⟩
  refine ⟨m, Q, i, ?_⟩
  rw [intervalPresentationOfGlobalRange_internalCut]
  congr 1
  rw [Int.toNat_of_nonneg hnonneg]
  omega

/--
A bounded restriction which retains every global cut strictly between its
endpoints.  This completeness clause is what makes finite counting sums
independent of the auxiliary mesh.
-/
theorem PolynomialPresentation.exists_intervalPresentation_complete
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    {a b : ℝ} (hab : a < b) :
    ∃ m : ℕ, ∃ Q : IntervalPolynomialPresentation n m f a b,
      ∀ k : ℤ, a < P.cutPoint k → P.cutPoint k < b →
        ∃ i : Fin m, Q.internalCut i = P.cutPoint k := by
  let ia := presentationIntervalIndex P a
  let ib := presentationIntervalIndex P b
  have ha := presentationIntervalIndex_mem P a
  have hb := presentationIntervalIndex_mem P b
  change a ∈ Ioc (P.cutPoint (ia - 1)) (P.cutPoint ia) at ha
  change b ∈ Ioc (P.cutPoint (ib - 1)) (P.cutPoint ib) at hb
  have hiab : ia ≤ ib := by
    by_contra h
    have hibia : ib < ia := lt_of_not_ge h
    have hcut : P.cutPoint ib ≤ P.cutPoint (ia - 1) :=
      P.cutPoint_strictMono.monotone (by omega)
    linarith [ha.1, hb.2]
  let s := if a = P.cutPoint ia then ia + 1 else ia
  have hsib : s ≤ ib := by
    dsimp [s]
    split_ifs with heq
    · have hstrict : ia < ib := by
        by_contra h
        have hib : ib ≤ ia := le_of_not_gt h
        have hcut : P.cutPoint ib ≤ P.cutPoint ia :=
          P.cutPoint_strictMono.monotone hib
        linarith [hb.2]
      omega
    · exact hiab
  let m := Int.toNat (ib - s)
  have hm : (m : ℤ) = ib - s :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hsib)
  have haLower : P.cutPoint (s - 1) ≤ a := by
    dsimp [s]
    split_ifs with heq
    · simp [heq]
    · exact ha.1.le
  have haUpper : a < P.cutPoint s := by
    dsimp [s]
    split_ifs with heq
    · rw [heq]
      exact P.cutPoint_strictMono (by omega)
    · exact lt_of_le_of_ne ha.2 heq
  let Q := intervalPresentationOfGlobalRange P hm hab
    haLower haUpper hb.1 hb.2
  refine ⟨m, Q, ?_⟩
  intro k hak hkb
  have hiak : ia ≤ k := by
    by_contra h
    have hki : k < ia := lt_of_not_ge h
    have hcut : P.cutPoint k ≤ P.cutPoint (ia - 1) :=
      P.cutPoint_strictMono.monotone (by omega)
    exact (not_lt_of_ge hak.le) (hcut.trans_lt ha.1)
  have hkib : k < ib := by
    by_contra h
    have hibk : ib ≤ k := le_of_not_gt h
    have hcut : P.cutPoint ib ≤ P.cutPoint k :=
      P.cutPoint_strictMono.monotone hibk
    exact (not_lt_of_ge (hb.2.trans hcut)) hkb
  have hsk : s ≤ k := by
    dsimp [s]
    split_ifs with heq
    · have hne : ia ≠ k := by
        intro hik
        subst k
        linarith
      omega
    · exact hiak
  have hnonneg : 0 ≤ k - s := sub_nonneg.mpr hsk
  have hkmz : (Int.toNat (k - s) : ℤ) < (m : ℤ) := by
    rw [Int.toNat_of_nonneg hnonneg, hm]
    omega
  have hkm : Int.toNat (k - s) < m := by exact_mod_cast hkmz
  let i : Fin m := ⟨Int.toNat (k - s), hkm⟩
  refine ⟨i, ?_⟩
  rw [intervalPresentationOfGlobalRange_internalCut]
  congr 1
  rw [Int.toNat_of_nonneg hnonneg]
  omega

end

end NthTropicalNevanlinna
