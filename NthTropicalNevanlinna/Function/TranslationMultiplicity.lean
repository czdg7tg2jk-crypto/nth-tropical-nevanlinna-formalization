import NthTropicalNevanlinna.Function.PresentationClosure
import NthTropicalNevanlinna.PoissonJensen.DerivativeJump

/-!
# Multiplicity under translation

This file supplies the intrinsic local statement needed in the shifted-root
comparison of Theorem 6.2.  Translation preserves the ordinary normalized
derivative jump.  The radial multiplicity therefore agrees whenever the
source and translated points have the same sign, and it agrees everywhere
in odd order.
-/

namespace NthTropicalNevanlinna

noncomputable section

open Set

private theorem iterateDerivative_comp_X_add_C
    (p : Polynomial ℝ) (j : ℕ) (c : ℝ) :
    (Polynomial.derivative^[j])
        (p.comp (Polynomial.X + Polynomial.C c)) =
      ((Polynomial.derivative^[j]) p).comp
        (Polynomial.X + Polynomial.C c) := by
  induction j generalizing p with
  | zero => simp
  | succ j ih =>
      simp [Function.iterate_succ_apply, ih (Polynomial.derivative p),
        Polynomial.derivative_comp]

/-- Normalized polynomial jets commute with translation. -/
theorem normalizedPolynomialJet_comp_X_add_C
    (p : Polynomial ℝ) (j : ℕ) (x c : ℝ) :
    normalizedPolynomialJet
        (p.comp (Polynomial.X + Polynomial.C c)) j x =
      normalizedPolynomialJet p j (x + c) := by
  rw [normalizedPolynomialJet_eq_iterateDerivative_div,
    normalizedPolynomialJet_eq_iterateDerivative_div,
    iterateDerivative_comp_X_add_C]
  simp [Polynomial.eval_comp]

/-- The left polynomial germ of the canonical translated realization is the
translated left germ of the original function. -/
theorem translateRealization_leftPieceAt
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (c x : ℝ) :
    (translateRealization f c).function.presentation.leftPieceAt x =
      (f.presentation.leftPieceAt (x + c)).comp
        (Polynomial.X + Polynomial.C c) := by
  let R := translateRealization f c
  obtain ⟨aR, haR, hR⟩ :=
    R.function.presentation.exists_left_germ_interval x
  obtain ⟨aF, haF, hF⟩ :=
    f.presentation.exists_left_germ_interval (x + c)
  apply Polynomial.eq_of_infinite_eval_eq
  have haFc : aF - c < x := by linarith [haF]
  apply (Ioo_infinite (max_lt haR haFc)).mono
  intro y hy
  have hyR : y ∈ Ioo aR x :=
    ⟨(le_max_left _ _).trans_lt hy.1, hy.2⟩
  have hyF : y + c ∈ Ioo aF (x + c) :=
    ⟨by linarith [(le_max_right aR (aF - c)).trans_lt hy.1], by linarith [hy.2]⟩
  change Polynomial.eval y
      ((translateRealization f c).function.presentation.leftPieceAt x) =
    Polynomial.eval y
      ((f.presentation.leftPieceAt (x + c)).comp
        (Polynomial.X + Polynomial.C c))
  calc
    ((translateRealization f c).function.presentation.leftPieceAt x).eval y =
        R.function y := (hR y hyR).symm
    _ = f (y + c) := R.eq_fun y
    _ = (f.presentation.leftPieceAt (x + c)).eval (y + c) := hF (y + c) hyF
    _ = ((f.presentation.leftPieceAt (x + c)).comp
        (Polynomial.X + Polynomial.C c)).eval y := by
      simp [Polynomial.eval_comp]

/-- The right polynomial germ of the canonical translated realization is
the translated right germ of the original function. -/
theorem translateRealization_rightPieceAt
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (c x : ℝ) :
    (translateRealization f c).function.presentation.rightPieceAt x =
      (f.presentation.rightPieceAt (x + c)).comp
        (Polynomial.X + Polynomial.C c) := by
  let R := translateRealization f c
  obtain ⟨bR, hbR, hR⟩ :=
    R.function.presentation.exists_right_germ_interval x
  obtain ⟨bF, hbF, hF⟩ :=
    f.presentation.exists_right_germ_interval (x + c)
  apply Polynomial.eq_of_infinite_eval_eq
  have hxbFc : x < bF - c := by linarith [hbF]
  apply (Ioo_infinite (lt_min hbR hxbFc)).mono
  intro y hy
  have hyR : y ∈ Ioo x bR :=
    ⟨hy.1, hy.2.trans_le (min_le_left _ _)⟩
  have hyF : y + c ∈ Ioo (x + c) bF :=
    ⟨by linarith [hy.1], by linarith [hy.2.trans_le (min_le_right bR (bF - c))]⟩
  change Polynomial.eval y
      ((translateRealization f c).function.presentation.rightPieceAt x) =
    Polynomial.eval y
      ((f.presentation.rightPieceAt (x + c)).comp
        (Polynomial.X + Polynomial.C c))
  calc
    ((translateRealization f c).function.presentation.rightPieceAt x).eval y =
        R.function y := (hR y hyR).symm
    _ = f (y + c) := R.eq_fun y
    _ = (f.presentation.rightPieceAt (x + c)).eval (y + c) := hF (y + c) hyF
    _ = ((f.presentation.rightPieceAt (x + c)).comp
        (Polynomial.X + Polynomial.C c)).eval y := by
      simp [Polynomial.eval_comp]

/-- Translation preserves the intrinsic ordinary normalized derivative
jump. -/
theorem derivativeJump_translateRealization
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (c : ℝ)
    (j : ℕ) (x : ℝ) :
    derivativeJump (translateRealization f c).function j x =
      derivativeJump f j (x + c) := by
  unfold derivativeJump normalizedRightJet normalizedLeftJet
  rw [translateRealization_rightPieceAt,
    translateRealization_leftPieceAt,
    normalizedPolynomialJet_comp_X_add_C,
    normalizedPolynomialJet_comp_X_add_C]

/-- On a positive-to-positive translation, radial multiplicity is
unchanged. -/
theorem multiplicity_translateRealization_of_pos
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (c : ℝ)
    (j : ℕ) {x : ℝ} (hx : 0 < x) (hxc : 0 < x + c) :
    multiplicity (translateRealization f c).function j x =
      multiplicity f j (x + c) := by
  rw [multiplicity_eq_derivativeJump_of_pos _ j hx,
    multiplicity_eq_derivativeJump_of_pos f j hxc,
    derivativeJump_translateRealization]

/-- On a negative-to-negative translation, radial multiplicity is
unchanged. -/
theorem multiplicity_translateRealization_of_neg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (c : ℝ)
    (j : ℕ) {x : ℝ} (hx : x < 0) (hxc : x + c < 0) :
    multiplicity (translateRealization f c).function j x =
      multiplicity f j (x + c) := by
  rw [multiplicity_eq_pow_mul_derivativeJump_of_neg _ j hx,
    multiplicity_eq_pow_mul_derivativeJump_of_neg f j hxc,
    derivativeJump_translateRealization]

/-- In odd order the radial sign exponent is even, so multiplicity equals
the ordinary derivative jump at every point, including the origin. -/
theorem multiplicity_eq_derivativeJump_of_odd
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {j : ℕ} (hj : Odd j) (x : ℝ) :
    multiplicity f j x = derivativeJump f j x := by
  obtain ⟨k, rfl⟩ := hj
  unfold multiplicity multiplicityUsingPresentation derivativeJump
    normalizedRightJet normalizedLeftJet
  have hright : rightSign x ^ (2 * k + 1 + 1) = 1 := by
    have hr : rightSign x = 1 ∨ rightSign x = -1 := by
      unfold rightSign
      split <;> simp
    rcases hr with hr | hr <;> rw [hr] <;> simp [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
  have hleft : leftSign x ^ (2 * k + 1 + 1) = 1 := by
    have hl : leftSign x = 1 ∨ leftSign x = -1 := by
      unfold leftSign
      split <;> simp
    rcases hl with hl | hl <;> rw [hl] <;> simp [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
  rw [hright, hleft]
  ring

/-- Odd-order multiplicity is invariant under translation at every point. -/
theorem multiplicity_translateRealization_of_odd
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (c : ℝ)
    {j : ℕ} (hj : Odd j) (x : ℝ) :
    multiplicity (translateRealization f c).function j x =
      multiplicity f j (x + c) := by
  rw [multiplicity_eq_derivativeJump_of_odd _ hj,
    multiplicity_eq_derivativeJump_of_odd f hj,
    derivativeJump_translateRealization]

/-- In odd order, translation transports the root predicate exactly. -/
theorem isJthRoot_translateRealization_of_odd
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (c : ℝ)
    {j : ℕ} (hj : Odd j) (x : ℝ) :
    IsJthRoot (translateRealization f c).function j x ↔
      IsJthRoot f j (x + c) := by
  unfold IsJthRoot
  rw [multiplicity_translateRealization_of_odd f c hj x]

/-- In odd order, translation also preserves the unsigned root/pole
multiplicity exactly. -/
theorem rootOrPoleMultiplicity_translateRealization_of_odd
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (c : ℝ)
    {j : ℕ} (hj : Odd j) (x : ℝ) :
    rootOrPoleMultiplicity (translateRealization f c).function j x =
      rootOrPoleMultiplicity f j (x + c) := by
  unfold rootOrPoleMultiplicity
  rw [multiplicity_translateRealization_of_odd f c hj x]

/-- On a positive-to-positive translation, the root predicate is transported
exactly. -/
theorem isJthRoot_translateRealization_of_pos
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (c : ℝ)
    (j : ℕ) {x : ℝ} (hx : 0 < x) (hxc : 0 < x + c) :
    IsJthRoot (translateRealization f c).function j x ↔
      IsJthRoot f j (x + c) := by
  unfold IsJthRoot
  rw [multiplicity_translateRealization_of_pos f c j hx hxc]

/-- On a negative-to-negative translation, the root predicate is transported
exactly. -/
theorem isJthRoot_translateRealization_of_neg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (c : ℝ)
    (j : ℕ) {x : ℝ} (hx : x < 0) (hxc : x + c < 0) :
    IsJthRoot (translateRealization f c).function j x ↔
      IsJthRoot f j (x + c) := by
  unfold IsJthRoot
  rw [multiplicity_translateRealization_of_neg f c j hx hxc]

/-- Same-sign translation preserves unsigned root/pole multiplicity. -/
theorem rootOrPoleMultiplicity_translateRealization_of_sameSign
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (c : ℝ)
    (j : ℕ) {x : ℝ}
    (h : (0 < x ∧ 0 < x + c) ∨ (x < 0 ∧ x + c < 0)) :
    rootOrPoleMultiplicity (translateRealization f c).function j x =
      rootOrPoleMultiplicity f j (x + c) := by
  rcases h with h | h
  · unfold rootOrPoleMultiplicity
    rw [multiplicity_translateRealization_of_pos f c j h.1 h.2]
  · unfold rootOrPoleMultiplicity
    rw [multiplicity_translateRealization_of_neg f c j h.1 h.2]

end

end NthTropicalNevanlinna
