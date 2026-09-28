import NthTropicalNevanlinna.Function.PiecewisePolynomial

/-!
# Higher tropical multiplicities

The multiplicity is defined from the intrinsic left and right polynomial germs
at a point.  A normalized presentation is used only to obtain those germs;
`multiplicityUsingPresentation_eq` proves that the result does not depend on
that choice.
-/

open Function Set

namespace NthTropicalNevanlinna

noncomputable section

/-- The normalized `j`-th polynomial derivative, i.e. the Hasse derivative. -/
def normalizedPolynomialJet (p : Polynomial ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.hasseDeriv j p).eval x

theorem normalizedPolynomialJet_eq_iterateDerivative_div
    (p : Polynomial ℝ) (j : ℕ) (x : ℝ) :
    normalizedPolynomialJet p j x =
      ((Polynomial.derivative^[j]) p).eval x / (j.factorial : ℝ) := by
  apply (eq_div_iff (by positivity : (j.factorial : ℝ) ≠ 0)).2
  have hp := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) j) p
  have hx := congrArg (Polynomial.eval x) hp
  simpa [normalizedPolynomialJet, mul_comm] using hx

/-- Sign seen from the right; at zero this is `+1`. -/
def rightSign (x : ℝ) : ℝ := if x < 0 then -1 else 1

/-- Sign seen from the left; at zero this is `-1`. -/
def leftSign (x : ℝ) : ℝ := if x ≤ 0 then -1 else 1

@[simp] theorem rightSign_of_nonneg {x : ℝ} (hx : 0 ≤ x) : rightSign x = 1 := by
  simp [rightSign, not_lt.mpr hx]

@[simp] theorem leftSign_of_pos {x : ℝ} (hx : 0 < x) : leftSign x = 1 := by
  simp [leftSign, not_le.mpr hx]

@[simp] theorem rightSign_of_neg {x : ℝ} (hx : x < 0) : rightSign x = -1 := by
  simp [rightSign, hx]

@[simp] theorem leftSign_of_nonpos {x : ℝ} (hx : x ≤ 0) : leftSign x = -1 := by
  simp [leftSign, hx]

/-- Multiplicity computed from one presentation's local polynomial germs. -/
def multiplicityUsingPresentation
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    (j : ℕ) (x : ℝ) : ℝ :=
  rightSign x ^ (j + 1) * normalizedPolynomialJet (P.rightPieceAt x) j x -
    leftSign x ^ (j + 1) * normalizedPolynomialJet (P.leftPieceAt x) j x

/-- The local multiplicity formula at the `i`-th cut point of a presentation. -/
def presentationMultiplicityAtCutPoint
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    (j : ℕ) (i : ℤ) : ℝ :=
  let x := P.cutPoint i
  rightSign x ^ (j + 1) * normalizedPolynomialJet (P.piece (i + 1)) j x -
    leftSign x ^ (j + 1) * normalizedPolynomialJet (P.piece i) j x

theorem multiplicityUsingPresentation_at_cutPoint
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    (j : ℕ) (i : ℤ) :
    multiplicityUsingPresentation P j (P.cutPoint i) =
      presentationMultiplicityAtCutPoint P j i := by
  have hmem : P.cutPoint i ∈ Ioc (P.cutPoint (i - 1)) (P.cutPoint i) :=
    ⟨P.cutPoint_strictMono (by omega), le_rfl⟩
  have hindex := presentationIntervalIndex_eq_of_mem P hmem
  simp [multiplicityUsingPresentation, presentationMultiplicityAtCutPoint,
    PolynomialPresentation.leftPieceAt, PolynomialPresentation.rightPieceAt, hindex]

/-- Multiplicity computed from two presentations of the same function agrees. -/
theorem multiplicityUsingPresentation_eq
    {n : ℕ} {f : ℝ → ℝ} (P Q : PolynomialPresentation n f)
    (j : ℕ) (x : ℝ) :
    multiplicityUsingPresentation P j x = multiplicityUsingPresentation Q j x := by
  simp only [multiplicityUsingPresentation]
  rw [P.rightPieceAt_eq Q x, P.leftPieceAt_eq Q x]

/-- The intrinsic `j`-th tropical multiplicity function `ω_f^(j)`. -/
def multiplicity {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (x : ℝ) : ℝ :=
  multiplicityUsingPresentation f.presentation j x

/-- Multiplicities above the exact polynomial order vanish. -/
theorem multiplicity_eq_zero_of_order_lt
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {j : ℕ} (hnj : n < j) (x : ℝ) :
    multiplicity f j x = 0 := by
  have hleft : normalizedPolynomialJet (f.presentation.leftPieceAt x) j x = 0 := by
    rw [normalizedPolynomialJet,
      Polynomial.hasseDeriv_eq_zero_of_lt_natDegree
        _ _ ((f.presentation.leftPieceAt_natDegree_le x).trans_lt hnj)]
    simp
  have hright : normalizedPolynomialJet (f.presentation.rightPieceAt x) j x = 0 := by
    rw [normalizedPolynomialJet,
      Polynomial.hasseDeriv_eq_zero_of_lt_natDegree
        _ _ ((f.presentation.rightPieceAt_natDegree_le x).trans_lt hnj)]
    simp
  simp [multiplicity, multiplicityUsingPresentation, hleft, hright]

/-- Any presentation may be used to compute the intrinsic multiplicity. -/
theorem multiplicity_eq_usingPresentation
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (P : PolynomialPresentation n f) (j : ℕ) (x : ℝ) :
    multiplicity f j x = multiplicityUsingPresentation P j x :=
  multiplicityUsingPresentation_eq f.presentation P j x

/-- Intrinsic multiplicity evaluated at a cut point of any presentation. -/
theorem multiplicity_cutPoint_of_presentation
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (P : PolynomialPresentation n f) (j : ℕ) (i : ℤ) :
    multiplicity f j (P.cutPoint i) = presentationMultiplicityAtCutPoint P j i := by
  rw [multiplicity_eq_usingPresentation f P]
  exact multiplicityUsingPresentation_at_cutPoint P j i

/-- The cut-point formula for the internal presentation witness. -/
def multiplicityAtCutPoint {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (i : ℤ) : ℝ :=
  presentationMultiplicityAtCutPoint f.presentation j i

@[simp]
theorem multiplicity_cutPoint {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (i : ℤ) :
    multiplicity f j (f.presentation.cutPoint i) = multiplicityAtCutPoint f j i :=
  multiplicity_cutPoint_of_presentation f f.presentation j i

theorem presentationMultiplicityAtCutPoint_of_pos_index
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    (j : ℕ) {i : ℤ} (hi : 0 < i) :
    presentationMultiplicityAtCutPoint P j i =
      normalizedPolynomialJet (P.piece (i + 1)) j (P.cutPoint i) -
        normalizedPolynomialJet (P.piece i) j (P.cutPoint i) := by
  have hx : 0 < P.cutPoint i := by
    rw [← P.cutPoint_zero]
    exact P.cutPoint_strictMono hi
  simp [presentationMultiplicityAtCutPoint,
    rightSign_of_nonneg hx.le, leftSign_of_pos hx]

theorem presentationMultiplicityAtCutPoint_of_neg_index
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    (j : ℕ) {i : ℤ} (hi : i < 0) :
    presentationMultiplicityAtCutPoint P j i =
      (-1 : ℝ) ^ (j + 1) *
        (normalizedPolynomialJet (P.piece (i + 1)) j (P.cutPoint i) -
          normalizedPolynomialJet (P.piece i) j (P.cutPoint i)) := by
  have hx : P.cutPoint i < 0 := by
    rw [← P.cutPoint_zero]
    exact P.cutPoint_strictMono hi
  simp only [presentationMultiplicityAtCutPoint,
    rightSign_of_neg hx, leftSign_of_nonpos hx.le]
  ring

theorem presentationMultiplicityAtCutPoint_of_neg_index'
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    (j : ℕ) {i : ℤ} (hi : i < 0) :
    presentationMultiplicityAtCutPoint P j i =
      (-1 : ℝ) ^ j *
        (normalizedPolynomialJet (P.piece i) j (P.cutPoint i) -
          normalizedPolynomialJet (P.piece (i + 1)) j (P.cutPoint i)) := by
  rw [presentationMultiplicityAtCutPoint_of_neg_index P j hi, pow_succ]
  ring

theorem presentationMultiplicityAtCutPoint_zero
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (j : ℕ) :
    presentationMultiplicityAtCutPoint P j 0 =
      normalizedPolynomialJet (P.piece 1) j 0 -
        (-1 : ℝ) ^ (j + 1) * normalizedPolynomialJet (P.piece 0) j 0 := by
  simp [presentationMultiplicityAtCutPoint, P.cutPoint_zero, rightSign, leftSign]

theorem multiplicityAtCutPoint_of_pos_index
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) {i : ℤ} (hi : 0 < i) :
    multiplicityAtCutPoint f j i =
      normalizedPolynomialJet (f.presentation.piece (i + 1)) j
          (f.presentation.cutPoint i) -
        normalizedPolynomialJet (f.presentation.piece i) j
          (f.presentation.cutPoint i) := by
  exact presentationMultiplicityAtCutPoint_of_pos_index f.presentation j hi

theorem multiplicityAtCutPoint_of_neg_index
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) {i : ℤ} (hi : i < 0) :
    multiplicityAtCutPoint f j i =
      (-1 : ℝ) ^ (j + 1) *
        (normalizedPolynomialJet (f.presentation.piece (i + 1)) j
            (f.presentation.cutPoint i) -
          normalizedPolynomialJet (f.presentation.piece i) j
            (f.presentation.cutPoint i)) := by
  exact presentationMultiplicityAtCutPoint_of_neg_index f.presentation j hi

theorem multiplicityAtCutPoint_of_neg_index'
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) {i : ℤ} (hi : i < 0) :
    multiplicityAtCutPoint f j i =
      (-1 : ℝ) ^ j *
        (normalizedPolynomialJet (f.presentation.piece i) j
            (f.presentation.cutPoint i) -
          normalizedPolynomialJet (f.presentation.piece (i + 1)) j
            (f.presentation.cutPoint i)) := by
  exact presentationMultiplicityAtCutPoint_of_neg_index' f.presentation j hi

theorem multiplicityAtCutPoint_zero
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) :
    multiplicityAtCutPoint f j 0 =
      normalizedPolynomialJet (f.presentation.piece 1) j 0 -
        (-1 : ℝ) ^ (j + 1) * normalizedPolynomialJet (f.presentation.piece 0) j 0 := by
  exact presentationMultiplicityAtCutPoint_zero f.presentation j

private theorem rightSign_eq_leftSign_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    rightSign x = leftSign x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · rw [rightSign_of_neg hneg, leftSign_of_nonpos hneg.le]
  · rw [rightSign_of_nonneg hpos.le, leftSign_of_pos hpos]

/--
Away from the cut points of any fixed presentation, both local polynomial
germs coincide and multiplicity is zero.  This says only that singular points
are among the chosen cuts; it does not say that every cut is singular.
-/
theorem multiplicity_eq_zero_or_cutPoint_of_presentation
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (P : PolynomialPresentation n f) (j : ℕ) (x : ℝ) :
    multiplicity f j x = 0 ∨
      ∃ i : ℤ, x = P.cutPoint i ∧
        multiplicity f j x = presentationMultiplicityAtCutPoint P j i := by
  let i := presentationIntervalIndex P x
  by_cases hcut : x = P.cutPoint i
  · right
    refine ⟨i, hcut, ?_⟩
    rw [hcut, multiplicity_cutPoint_of_presentation]
  · left
    have hx0 : x ≠ 0 := by
      intro hx
      have hzeroMem : (0 : ℝ) ∈ Ioc (P.cutPoint (0 - 1)) (P.cutPoint 0) := by
        constructor
        · calc
            P.cutPoint (0 - 1) < P.cutPoint 0 :=
              P.cutPoint_strictMono (show (0 : ℤ) - 1 < 0 by omega)
            _ = 0 := P.cutPoint_zero
        · exact P.cutPoint_zero.ge
      have hi0 : i = 0 := by
        dsimp [i]
        exact presentationIntervalIndex_eq_of_mem P (by simpa [hx] using hzeroMem)
      apply hcut
      rw [hi0, P.cutPoint_zero, hx]
    have hsign := rightSign_eq_leftSign_of_ne_zero hx0
    rw [multiplicity_eq_usingPresentation f P]
    simp [multiplicityUsingPresentation, PolynomialPresentation.leftPieceAt,
      PolynomialPresentation.rightPieceAt, i, hcut, hsign]

theorem multiplicity_eq_zero_or_cutPoint
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (x : ℝ) :
    multiplicity f j x = 0 ∨
      ∃ i : ℤ, x = f.presentation.cutPoint i ∧
        multiplicity f j x = multiplicityAtCutPoint f j i :=
  multiplicity_eq_zero_or_cutPoint_of_presentation f f.presentation j x

/-- `x` is a `j`-th tropical root when its `j`-th multiplicity is positive. -/
def IsJthRoot {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (x : ℝ) : Prop :=
  0 < multiplicity f j x

/-- `x` is a `j`-th tropical pole when its `j`-th multiplicity is negative. -/
def IsJthPole {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (x : ℝ) : Prop :=
  multiplicity f j x < 0

/-- The nonnegative multiplicity attached to a root or pole. -/
def rootOrPoleMultiplicity {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (j : ℕ) (x : ℝ) : ℝ :=
  |multiplicity f j x|

/-- A singularity is a root or pole of some order `1 ≤ j ≤ n`. -/
def IsSingularity {n : ℕ} (f : NthTropicalMeromorphicFunction n) (x : ℝ) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ n ∧ (IsJthRoot f j x ∨ IsJthPole f j x)

end

end NthTropicalNevanlinna
