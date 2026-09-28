import NthTropicalNevanlinna.Function.PiecewisePolynomial

/-!
# Polynomial presentations on a bounded interval

`IntervalPolynomialPresentation n m f a b` records `m` internal cut points
and `m + 1` polynomial pieces on `[a,b]`.  Unlike the global presentation,
there is no infinite grid, no normalization at zero, and no condition at
infinity.  Only a degree bound is required: restriction to a small interval
need not attain the global degree.
-/

open Set

namespace NthTropicalNevanlinna

/-- A finite polynomial mesh on the bounded interval `[a,b]`. -/
structure IntervalPolynomialPresentation
    (n m : ℕ) (f : ℝ → ℝ) (a b : ℝ) where
  /-- The `m + 2` points consisting of both endpoints and `m` internal cuts. -/
  cutPoint : Fin (m + 2) → ℝ
  /-- The `m + 1` polynomial pieces between consecutive cut points. -/
  piece : Fin (m + 1) → Polynomial ℝ
  cutPoint_strictMono : StrictMono cutPoint
  cutPoint_first : cutPoint 0 = a
  cutPoint_last : cutPoint (Fin.last (m + 1)) = b
  piece_natDegree_le : ∀ i, (piece i).natDegree ≤ n
  eq_piece : ∀ (i : Fin (m + 1)) {x : ℝ},
    x ∈ Icc (cutPoint i.castSucc) (cutPoint i.succ) → f x = (piece i).eval x

namespace IntervalPolynomialPresentation

variable {n m : ℕ} {f : ℝ → ℝ} {a b : ℝ}

/-- The internal cut indexed from `0` through `m-1`. -/
def internalCut (P : IntervalPolynomialPresentation n m f a b) (i : Fin m) : ℝ :=
  P.cutPoint i.succ.castSucc

/-- Polynomial immediately to the left of an internal cut. -/
def leftPiece (P : IntervalPolynomialPresentation n m f a b)
    (i : Fin m) : Polynomial ℝ :=
  P.piece i.castSucc

/-- Polynomial immediately to the right of an internal cut. -/
def rightPiece (P : IntervalPolynomialPresentation n m f a b)
    (i : Fin m) : Polynomial ℝ :=
  P.piece i.succ

/-- The polynomial piece adjacent to the left endpoint. -/
def firstPiece (P : IntervalPolynomialPresentation n m f a b) : Polynomial ℝ :=
  P.piece 0

/-- The polynomial piece adjacent to the right endpoint. -/
def lastPiece (P : IntervalPolynomialPresentation n m f a b) : Polynomial ℝ :=
  P.piece (Fin.last m)

theorem leftEndpoint_lt_internalCut
    (P : IntervalPolynomialPresentation n m f a b) (i : Fin m) :
    a < P.internalCut i := by
  calc
    a = P.cutPoint 0 := P.cutPoint_first.symm
    _ < P.internalCut i := P.cutPoint_strictMono (by simp [internalCut])

theorem internalCut_lt_rightEndpoint
    (P : IntervalPolynomialPresentation n m f a b) (i : Fin m) :
    P.internalCut i < b := by
  calc
    P.internalCut i < P.cutPoint (Fin.last (m + 1)) :=
      P.cutPoint_strictMono
        (Fin.mk_lt_mk.mpr (Nat.succ_lt_succ i.isLt))
    _ = b := P.cutPoint_last

theorem internalCut_strictMono
    (P : IntervalPolynomialPresentation n m f a b) : StrictMono P.internalCut := by
  intro i k hik
  exact P.cutPoint_strictMono (by simpa [internalCut] using hik)

theorem leftPiece_eval_internalCut_eq_rightPiece
    (P : IntervalPolynomialPresentation n m f a b) (i : Fin m) :
    (P.leftPiece i).eval (P.internalCut i) =
      (P.rightPiece i).eval (P.internalCut i) := by
  have hleft : f (P.internalCut i) = (P.leftPiece i).eval (P.internalCut i) := by
    apply P.eq_piece i.castSucc
    constructor
    · exact (P.cutPoint_strictMono (by simp)).le
    · exact le_rfl
  have hright : f (P.internalCut i) = (P.rightPiece i).eval (P.internalCut i) := by
    apply P.eq_piece i.succ
    constructor
    · exact le_rfl
    · exact (P.cutPoint_strictMono (by simp)).le
  exact hleft.symm.trans hright

theorem apply_leftEndpoint
    (P : IntervalPolynomialPresentation n m f a b) : f a = (P.firstPiece).eval a := by
  have h := P.eq_piece (0 : Fin (m + 1))
    (show a ∈ Icc (P.cutPoint (0 : Fin (m + 2)))
        (P.cutPoint (Fin.succ 0)) by
      constructor
      · exact P.cutPoint_first.le
      · calc
          a = P.cutPoint 0 := P.cutPoint_first.symm
          _ ≤ P.cutPoint (Fin.succ 0) := (P.cutPoint_strictMono (by simp)).le)
  simpa [firstPiece] using h

theorem apply_rightEndpoint
    (P : IntervalPolynomialPresentation n m f a b) : f b = (P.lastPiece).eval b := by
  have h := P.eq_piece (Fin.last m)
    (show b ∈ Icc (P.cutPoint (Fin.last m).castSucc)
        (P.cutPoint (Fin.last m).succ) by
      constructor
      · calc
          P.cutPoint (Fin.last m).castSucc ≤ P.cutPoint (Fin.last (m + 1)) :=
            (P.cutPoint_strictMono (by simp)).le
          _ = b := P.cutPoint_last
      · calc
          b = P.cutPoint (Fin.last (m + 1)) := P.cutPoint_last.symm
          _ ≤ P.cutPoint (Fin.last m).succ := by
            apply le_of_eq
            congr 1
            )
  simpa [lastPiece] using h

private theorem polynomial_eq_of_eqOn_Ioo
    (p q : Polynomial ℝ) {c d : ℝ} (hcd : c < d)
    (h : ∀ x ∈ Ioo c d, p.eval x = q.eval x) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq p q
  apply (Ioo_infinite hcd).mono
  intro x hx
  exact h x hx

/-- A bounded presentation computes the same intrinsic left polynomial germ. -/
theorem leftPiece_eq_intrinsic
    {n m : ℕ} {F : NthTropicalMeromorphicFunction n} {a b : ℝ}
    (P : IntervalPolynomialPresentation n m F a b) (i : Fin m) :
    P.leftPiece i = F.presentation.leftPieceAt (P.internalCut i) := by
  let c := P.internalCut i
  let aP := P.cutPoint i.castSucc.castSucc
  obtain ⟨aF, haF, hF⟩ := F.presentation.exists_left_germ_interval c
  have haP : aP < c := P.cutPoint_strictMono (by simp [aP, c, internalCut])
  apply polynomial_eq_of_eqOn_Ioo _ _ (max_lt haP haF)
  intro y hy
  have hyP : y ∈ Ioo aP c := ⟨(le_max_left _ _).trans_lt hy.1, hy.2⟩
  have hyF : y ∈ Ioo aF c := ⟨(le_max_right _ _).trans_lt hy.1, hy.2⟩
  have hP := P.eq_piece i.castSucc
    (show y ∈ Icc (P.cutPoint i.castSucc.castSucc) (P.cutPoint i.castSucc.succ) by
      constructor
      · exact hyP.1.le
      · simpa [c, internalCut] using hyP.2.le)
  exact hP.symm.trans (hF y hyF)

/-- A bounded presentation computes the same intrinsic right polynomial germ. -/
theorem rightPiece_eq_intrinsic
    {n m : ℕ} {F : NthTropicalMeromorphicFunction n} {a b : ℝ}
    (P : IntervalPolynomialPresentation n m F a b) (i : Fin m) :
    P.rightPiece i = F.presentation.rightPieceAt (P.internalCut i) := by
  let c := P.internalCut i
  let bP := P.cutPoint i.succ.succ
  obtain ⟨bF, hbF, hF⟩ := F.presentation.exists_right_germ_interval c
  have hbP : c < bP := P.cutPoint_strictMono (by simp [bP, c, internalCut])
  apply polynomial_eq_of_eqOn_Ioo _ _ (lt_min hbP hbF)
  intro y hy
  have hyP : y ∈ Ioo c bP := ⟨hy.1, hy.2.trans_le (min_le_left _ _)⟩
  have hyF : y ∈ Ioo c bF := ⟨hy.1, hy.2.trans_le (min_le_right _ _)⟩
  have hP := P.eq_piece i.succ
    (show y ∈ Icc (P.cutPoint i.succ.castSucc) (P.cutPoint i.succ.succ) by
      constructor
      · simpa [c, internalCut] using hyP.1.le
      · exact hyP.2.le)
  exact hP.symm.trans (hF y hyF)

end IntervalPolynomialPresentation

end NthTropicalNevanlinna
