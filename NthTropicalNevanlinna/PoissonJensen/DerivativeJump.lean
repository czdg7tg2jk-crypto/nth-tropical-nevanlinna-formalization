import NthTropicalNevanlinna.Function.IntervalPresentation
import NthTropicalNevanlinna.Function.PolynomialJet

/-!
# One-sided polynomial jets and derivative jumps

These are the local quantities used in Lemmas 3.1 and 3.2.  The jets are
normalized by `j!`, exactly as in the paper.
-/

namespace NthTropicalNevanlinna

noncomputable section

/-- Intrinsic normalized polynomial jet immediately to the right of `x`. -/
def normalizedRightJet {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (x : ℝ) : ℝ :=
  normalizedPolynomialJet (f.presentation.rightPieceAt x) j x

/-- Intrinsic normalized polynomial jet immediately to the left of `x`. -/
def normalizedLeftJet {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (x : ℝ) : ℝ :=
  normalizedPolynomialJet (f.presentation.leftPieceAt x) j x

theorem normalizedRightJet_eq_usingPresentation
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (P : PolynomialPresentation n f) (j : ℕ) (x : ℝ) :
    normalizedRightJet f j x = normalizedPolynomialJet (P.rightPieceAt x) j x := by
  rw [normalizedRightJet, f.presentation.rightPieceAt_eq P x]

theorem normalizedLeftJet_eq_usingPresentation
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (P : PolynomialPresentation n f) (j : ℕ) (x : ℝ) :
    normalizedLeftJet f j x = normalizedPolynomialJet (P.leftPieceAt x) j x := by
  rw [normalizedLeftJet, f.presentation.leftPieceAt_eq P x]

/-- The paper's normalized ordinary derivative jump `τ_f^(j)`. -/
def derivativeJump {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (x : ℝ) : ℝ :=
  normalizedRightJet f j x - normalizedLeftJet f j x

/-- Normalized derivative jump at an internal cut of a finite presentation. -/
def IntervalPolynomialPresentation.derivativeJumpAt
    {n m : ℕ} {f : ℝ → ℝ} {a b : ℝ}
    (P : IntervalPolynomialPresentation n m f a b) (j : ℕ) (i : Fin m) : ℝ :=
  normalizedPolynomialJet (P.rightPiece i) j (P.internalCut i) -
    normalizedPolynomialJet (P.leftPiece i) j (P.internalCut i)

theorem IntervalPolynomialPresentation.derivativeJumpAt_eq_intrinsic
    {n m : ℕ} {f : NthTropicalMeromorphicFunction n} {a b : ℝ}
    (P : IntervalPolynomialPresentation n m f a b) (j : ℕ) (i : Fin m) :
    P.derivativeJumpAt j i = derivativeJump f j (P.internalCut i) := by
  rw [IntervalPolynomialPresentation.derivativeJumpAt, derivativeJump,
    normalizedRightJet, normalizedLeftJet, P.rightPiece_eq_intrinsic,
    P.leftPiece_eq_intrinsic]

theorem IntervalPolynomialPresentation.firstPiece_eq_intrinsicRight
    {n m : ℕ} {f : NthTropicalMeromorphicFunction n} {a b : ℝ}
    (P : IntervalPolynomialPresentation n m f a b) :
    P.firstPiece = f.presentation.rightPieceAt a := by
  obtain ⟨bf, hbf, hf⟩ := f.presentation.exists_right_germ_interval a
  let bp := P.cutPoint (Fin.succ 0)
  have hab : a < bp := by
    rw [← P.cutPoint_first]
    exact P.cutPoint_strictMono (by simp [bp])
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioo_infinite (lt_min hab hbf)).mono
  intro y hy
  have hyp : y ∈ Set.Ioo a bp := ⟨hy.1, hy.2.trans_le (min_le_left _ _)⟩
  have hyf : y ∈ Set.Ioo a bf := ⟨hy.1, hy.2.trans_le (min_le_right _ _)⟩
  have hp := P.eq_piece (0 : Fin (m + 1))
    (show y ∈ Set.Icc (P.cutPoint (0 : Fin (m + 2))) (P.cutPoint (Fin.succ 0)) by
      constructor
      · simpa [P.cutPoint_first] using hyp.1.le
      · exact hyp.2.le)
  exact hp.symm.trans (hf y hyf)

theorem IntervalPolynomialPresentation.lastPiece_eq_intrinsicLeft
    {n m : ℕ} {f : NthTropicalMeromorphicFunction n} {a b : ℝ}
    (P : IntervalPolynomialPresentation n m f a b) :
    P.lastPiece = f.presentation.leftPieceAt b := by
  obtain ⟨af, haf, hf⟩ := f.presentation.exists_left_germ_interval b
  let ap := P.cutPoint (Fin.last m).castSucc
  have hab : ap < b := by
    rw [← P.cutPoint_last]
    exact P.cutPoint_strictMono (by simp [ap])
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioo_infinite (max_lt hab haf)).mono
  intro y hy
  have hyp : y ∈ Set.Ioo ap b := ⟨(le_max_left _ _).trans_lt hy.1, hy.2⟩
  have hyf : y ∈ Set.Ioo af b := ⟨(le_max_right _ _).trans_lt hy.1, hy.2⟩
  have hp := P.eq_piece (Fin.last m)
    (show y ∈ Set.Icc (P.cutPoint (Fin.last m).castSucc)
        (P.cutPoint (Fin.last m).succ) by
      constructor
      · exact hyp.1.le
      · simpa [P.cutPoint_last] using hyp.2.le)
  exact hp.symm.trans (hf y hyf)

theorem multiplicity_eq_derivativeJump_of_pos
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ)
    {x : ℝ} (hx : 0 < x) : multiplicity f j x = derivativeJump f j x := by
  simp [multiplicity, multiplicityUsingPresentation, derivativeJump,
    normalizedRightJet, normalizedLeftJet, rightSign_of_nonneg hx.le,
    leftSign_of_pos hx]

theorem multiplicity_eq_pow_mul_derivativeJump_of_neg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ)
    {x : ℝ} (hx : x < 0) :
    multiplicity f j x = (-1 : ℝ) ^ (j + 1) * derivativeJump f j x := by
  simp only [multiplicity, multiplicityUsingPresentation, derivativeJump,
    normalizedRightJet, normalizedLeftJet, rightSign_of_neg hx,
    leftSign_of_nonpos hx.le]
  ring

end

end NthTropicalNevanlinna
