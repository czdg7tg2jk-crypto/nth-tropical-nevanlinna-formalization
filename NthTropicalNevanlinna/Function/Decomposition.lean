import NthTropicalNevanlinna.Function.Entire
import NthTropicalNevanlinna.Function.PolynomialJet
import NthTropicalNevanlinna.Function.SplineAssembly

/-!
# Entire quotient decomposition

This file formalizes Proposition 2.3.  The denominator is constructed by
replacing every negative multiplicity of `f` by its positive part.  Polynomial
jet corrections realize those prescribed jumps, and `SplineAssembly` proves
that the resulting two-sided family is a continuous spline.
-/

namespace NthTropicalNevanlinna

open scoped BigOperators

noncomputable section

/-- Positive correction that cancels a negative multiplicity. -/
def polePart (a : ℝ) : ℝ := max (-a) 0

theorem polePart_nonneg (a : ℝ) : 0 ≤ polePart a := le_max_right _ _

theorem add_polePart_nonneg (a : ℝ) : 0 ≤ a + polePart a := by
  simp [polePart, max_def]
  split_ifs <;> linarith

theorem polePart_add_eq_zero_or_original_eq_zero (a : ℝ) :
    polePart a = 0 ∨ a + polePart a = 0 := by
  rcases le_total 0 a with ha | ha
  · left
    simp [polePart, ha]
  · right
    simp [polePart, ha]

private def decompositionTarget {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (i : ℤ) (j : ℕ) : ℝ :=
  polePart (multiplicityAtCutPoint f j i)

private def avoidingLeadingCoefficient {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) : ℝ :=
  if (f.presentation.piece 1).coeff n = -1 then 2 else 1

private theorem avoidingLeadingCoefficient_ne_zero {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) : avoidingLeadingCoefficient f ≠ 0 := by
  unfold avoidingLeadingCoefficient
  split_ifs <;> norm_num

private theorem coeff_add_avoidingLeadingCoefficient_ne_zero {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) :
    (f.presentation.piece 1).coeff n + avoidingLeadingCoefficient f ≠ 0 := by
  unfold avoidingLeadingCoefficient
  split_ifs with h
  · rw [h]
    norm_num
  · intro hz
    apply h
    linarith

private def denominatorBase {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Polynomial ℝ :=
  Polynomial.C (avoidingLeadingCoefficient f) * Polynomial.X ^ n

private theorem denominatorBase_natDegree {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) : (denominatorBase f).natDegree = n := by
  simp [denominatorBase, avoidingLeadingCoefficient_ne_zero f]

private def denominatorCentralLeft {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) : Polynomial ℝ :=
  Polynomial.C ((denominatorBase f).eval 0) +
    jetCorrection n 0 (fun j ↦
      (-1 : ℝ) ^ (j + 1) *
        (normalizedPolynomialJet (denominatorBase f) j 0 - decompositionTarget f 0 j))

private def rightDenominatorPieces {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) : ℕ → Polynomial ℝ
  | 0 => denominatorBase f
  | k + 1 => rightDenominatorPieces f k +
      jetCorrection n (f.presentation.cutPoint ((k : ℤ) + 1))
        (decompositionTarget f ((k : ℤ) + 1))

private def leftDenominatorPieces {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) : ℕ → Polynomial ℝ
  | 0 => denominatorCentralLeft f
  | k + 1 => leftDenominatorPieces f k +
      jetCorrection n (f.presentation.cutPoint (-((k : ℤ) + 1)))
        (fun j ↦ (-1 : ℝ) ^ j * decompositionTarget f (-((k : ℤ) + 1)) j)

private def denominatorPiece {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) : ℤ → Polynomial ℝ
  | Int.ofNat 0 => leftDenominatorPieces f 0
  | Int.ofNat (k + 1) => rightDenominatorPieces f k
  | Int.negSucc k => leftDenominatorPieces f (k + 1)

private theorem rightDenominatorPieces_natDegree_le {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) :
    ∀ k, (rightDenominatorPieces f k).natDegree ≤ n := by
  intro k
  induction k with
  | zero => rw [rightDenominatorPieces, denominatorBase_natDegree]
  | succ k ih =>
      rw [rightDenominatorPieces]
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le ih (jetCorrection_natDegree_le n _ _))

private theorem denominatorCentralLeft_natDegree_le {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) :
    (denominatorCentralLeft f).natDegree ≤ n := by
  unfold denominatorCentralLeft
  exact (Polynomial.natDegree_add_le _ _).trans <| max_le (by simp)
    (jetCorrection_natDegree_le n 0 _)

private theorem leftDenominatorPieces_natDegree_le {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) :
    ∀ k, (leftDenominatorPieces f k).natDegree ≤ n := by
  intro k
  induction k with
  | zero => exact denominatorCentralLeft_natDegree_le f
  | succ k ih =>
      rw [leftDenominatorPieces]
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le ih (jetCorrection_natDegree_le n _ _))

private theorem denominatorPiece_natDegree_le {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (i : ℤ) :
    (denominatorPiece f i).natDegree ≤ n := by
  cases i with
  | ofNat k =>
      cases k with
      | zero => exact leftDenominatorPieces_natDegree_le f 0
      | succ k => exact rightDenominatorPieces_natDegree_le f k
  | negSucc k => exact leftDenominatorPieces_natDegree_le f (k + 1)

private theorem denominatorPiece_one {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) : denominatorPiece f 1 = denominatorBase f := by
  rfl

private theorem denominatorPiece_negSucc_add_one {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (k : ℕ) :
    denominatorPiece f (Int.negSucc k + 1) = leftDenominatorPieces f k := by
  cases k with
  | zero => rfl
  | succ k => rfl

private theorem denominatorPiece_right_transition {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (k : ℕ) :
    denominatorPiece f ((k : ℤ) + 1 + 1) =
      denominatorPiece f ((k : ℤ) + 1) +
        jetCorrection n (f.presentation.cutPoint ((k : ℤ) + 1))
          (decompositionTarget f ((k : ℤ) + 1)) := by
  have hleft : (k : ℤ) + 1 = Int.ofNat (k + 1) := by
    rw [Int.ofNat_eq_natCast]
    push_cast
    ring
  have hright : (k : ℤ) + 1 + 1 = Int.ofNat (k + 2) := by
    rw [Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [hright]
  change rightDenominatorPieces f (k + 1) =
    denominatorPiece f ((k : ℤ) + 1) +
      jetCorrection n (f.presentation.cutPoint ((k : ℤ) + 1))
        (decompositionTarget f ((k : ℤ) + 1))
  rw [hleft]
  change rightDenominatorPieces f (k + 1) =
    rightDenominatorPieces f k +
      jetCorrection n (f.presentation.cutPoint ((k : ℤ) + 1))
        (decompositionTarget f ((k : ℤ) + 1))
  rw [rightDenominatorPieces]

private theorem denominatorPiece_left_transition {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (k : ℕ) :
    denominatorPiece f (Int.negSucc k) =
      denominatorPiece f (Int.negSucc k + 1) +
        jetCorrection n (f.presentation.cutPoint (Int.negSucc k))
          (fun j ↦ (-1 : ℝ) ^ j * decompositionTarget f (Int.negSucc k) j) := by
  rw [denominatorPiece, denominatorPiece_negSucc_add_one, leftDenominatorPieces]
  have hidx : -((k : ℤ) + 1) = Int.negSucc k := by omega
  rw [hidx]

private theorem denominatorPiece_adjacent {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (i : ℤ) :
    (denominatorPiece f i).eval (f.presentation.cutPoint i) =
      (denominatorPiece f (i + 1)).eval (f.presentation.cutPoint i) := by
  cases i with
  | ofNat k =>
      cases k with
      | zero =>
          have hidx : Int.ofNat 0 + 1 = 1 := by norm_num
          rw [denominatorPiece, hidx, denominatorPiece_one]
          change (leftDenominatorPieces f 0).eval (f.presentation.cutPoint 0) =
            (denominatorBase f).eval (f.presentation.cutPoint 0)
          rw [f.presentation.cutPoint_zero]
          simp [leftDenominatorPieces, denominatorCentralLeft]
      | succ k =>
          change (rightDenominatorPieces f k).eval
              (f.presentation.cutPoint ((k : ℤ) + 1)) =
            (denominatorPiece f ((k : ℤ) + 1 + 1)).eval
              (f.presentation.cutPoint ((k : ℤ) + 1))
          have hidx : (k : ℤ) + 1 + 1 = Int.ofNat (k + 2) := by
            rw [Int.ofNat_eq_natCast]
            push_cast
            ring
          rw [hidx, denominatorPiece, rightDenominatorPieces]
          simp
  | negSucc k =>
      rw [denominatorPiece, leftDenominatorPieces, denominatorPiece_negSucc_add_one]
      have hidx : -((k : ℤ) + 1) = Int.negSucc k := by omega
      rw [hidx]
      simp

private def denominator {n : ℕ} (f : NthTropicalMeromorphicFunction n) :
    NthTropicalMeromorphicFunction n :=
  assembleNthTropicalMeromorphicFunction f.presentation (denominatorPiece f)
    (denominatorPiece_natDegree_le f) (denominatorPiece_adjacent f)
    ⟨1, by rw [denominatorPiece_one, denominatorBase_natDegree]⟩

private def denominatorPresentation {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) :
    PolynomialPresentation n (denominator f) :=
  assembledPolynomialPresentation f.presentation (denominatorPiece f)
    (denominatorPiece_natDegree_le f) (denominatorPiece_adjacent f)
    ⟨1, by rw [denominatorPiece_one, denominatorBase_natDegree]⟩

@[simp] private theorem denominatorPresentation_cutPoint {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (i : ℤ) :
    (denominatorPresentation f).cutPoint i = f.presentation.cutPoint i := rfl

private theorem denominator_multiplicityAtCutPoint {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n)
    (i : ℤ) :
    multiplicity (denominator f) j (f.presentation.cutPoint i) =
      decompositionTarget f i j := by
  have hmult := multiplicity_cutPoint_of_presentation
    (denominator f) (denominatorPresentation f) j i
  rw [denominatorPresentation_cutPoint] at hmult
  rw [hmult]
  cases i with
  | ofNat k =>
      cases k with
      | zero =>
          change presentationMultiplicityAtCutPoint (denominatorPresentation f) j 0 =
            decompositionTarget f 0 j
          rw [presentationMultiplicityAtCutPoint_zero]
          change normalizedPolynomialJet (denominatorPiece f 1) j 0 -
              (-1 : ℝ) ^ (j + 1) * normalizedPolynomialJet (denominatorPiece f 0) j 0 =
            decompositionTarget f 0 j
          rw [denominatorPiece_one]
          change normalizedPolynomialJet (denominatorBase f) j 0 -
              (-1 : ℝ) ^ (j + 1) *
                normalizedPolynomialJet (denominatorCentralLeft f) j 0 =
            decompositionTarget f 0 j
          simp only [denominatorCentralLeft, normalizedPolynomialJet_add]
          have hconst : normalizedPolynomialJet
              (Polynomial.C ((denominatorBase f).eval 0)) j 0 = 0 := by
            rw [normalizedPolynomialJet,
              Polynomial.hasseDeriv_C (k := j) _ (by omega)]
            simp
          rw [hconst, zero_add,
            normalizedPolynomialJet_jetCorrection hj hjn]
          have hs : (-1 : ℝ) ^ (j + 1) * (-1 : ℝ) ^ (j + 1) = 1 := by
            rw [← pow_add, (Even.add_self (j + 1)).neg_one_pow]
          calc
            normalizedPolynomialJet (denominatorBase f) j 0 -
                (-1 : ℝ) ^ (j + 1) *
                  ((-1 : ℝ) ^ (j + 1) *
                    (normalizedPolynomialJet (denominatorBase f) j 0 -
                      decompositionTarget f 0 j)) =
              normalizedPolynomialJet (denominatorBase f) j 0 -
                ((-1 : ℝ) ^ (j + 1) * (-1 : ℝ) ^ (j + 1)) *
                  (normalizedPolynomialJet (denominatorBase f) j 0 -
                    decompositionTarget f 0 j) := by ring
            _ = decompositionTarget f 0 j := by rw [hs]; ring
      | succ k =>
          have hidx : Int.ofNat (k + 1) = (k : ℤ) + 1 := by
            rw [Int.ofNat_eq_natCast]
            push_cast
            ring
          have hi : (0 : ℤ) < Int.ofNat (k + 1) := by rw [hidx]; omega
          rw [presentationMultiplicityAtCutPoint_of_pos_index
            (denominatorPresentation f) j hi]
          change normalizedPolynomialJet
              (denominatorPiece f (Int.ofNat (k + 1) + 1)) j
                (f.presentation.cutPoint (Int.ofNat (k + 1))) -
              normalizedPolynomialJet (denominatorPiece f (Int.ofNat (k + 1))) j
                (f.presentation.cutPoint (Int.ofNat (k + 1))) =
            decompositionTarget f (Int.ofNat (k + 1)) j
          rw [hidx, denominatorPiece_right_transition]
          simp [normalizedPolynomialJet_jetCorrection hj hjn]
  | negSucc k =>
      have hi : Int.negSucc k < 0 := by omega
      rw [presentationMultiplicityAtCutPoint_of_neg_index'
        (denominatorPresentation f) j hi]
      change (-1 : ℝ) ^ j *
          (normalizedPolynomialJet (denominatorPiece f (Int.negSucc k)) j
              (f.presentation.cutPoint (Int.negSucc k)) -
            normalizedPolynomialJet (denominatorPiece f (Int.negSucc k + 1)) j
              (f.presentation.cutPoint (Int.negSucc k))) =
        decompositionTarget f (Int.negSucc k) j
      rw [denominatorPiece_left_transition]
      simp only [normalizedPolynomialJet_add,
        normalizedPolynomialJet_jetCorrection hj hjn]
      rw [add_sub_cancel_left, ← mul_assoc, ← pow_add,
        (Even.add_self j).neg_one_pow, one_mul]

private def numeratorPiece {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (i : ℤ) : Polynomial ℝ :=
  f.presentation.piece i + denominatorPiece f i

private theorem numeratorPiece_natDegree_le {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (i : ℤ) :
    (numeratorPiece f i).natDegree ≤ n :=
  (Polynomial.natDegree_add_le _ _).trans <|
    max_le (f.presentation.piece_natDegree_le i) (denominatorPiece_natDegree_le f i)

private theorem numeratorPiece_adjacent {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (i : ℤ) :
    (numeratorPiece f i).eval (f.presentation.cutPoint i) =
      (numeratorPiece f (i + 1)).eval (f.presentation.cutPoint i) := by
  simp only [numeratorPiece, Polynomial.eval_add]
  rw [f.presentation.piece_eval_cutPoint_eq, denominatorPiece_adjacent]

private theorem denominatorBase_coeff_degree {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) :
    (denominatorBase f).coeff n = avoidingLeadingCoefficient f := by
  simp [denominatorBase]

private theorem numeratorPiece_one_natDegree {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) :
    (numeratorPiece f 1).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (numeratorPiece_natDegree_le f 1)
  rw [numeratorPiece, denominatorPiece_one, Polynomial.coeff_add,
    denominatorBase_coeff_degree]
  exact coeff_add_avoidingLeadingCoefficient_ne_zero f

private def numerator {n : ℕ} (f : NthTropicalMeromorphicFunction n) :
    NthTropicalMeromorphicFunction n :=
  assembleNthTropicalMeromorphicFunction f.presentation (numeratorPiece f)
    (numeratorPiece_natDegree_le f) (numeratorPiece_adjacent f)
    ⟨1, numeratorPiece_one_natDegree f⟩

private def numeratorPresentation {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) :
    PolynomialPresentation n (numerator f) :=
  assembledPolynomialPresentation f.presentation (numeratorPiece f)
    (numeratorPiece_natDegree_le f) (numeratorPiece_adjacent f)
    ⟨1, numeratorPiece_one_natDegree f⟩

@[simp] private theorem numeratorPresentation_cutPoint {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (i : ℤ) :
    (numeratorPresentation f).cutPoint i = f.presentation.cutPoint i := rfl

private theorem numerator_apply {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (x : ℝ) :
    numerator f x = f x + denominator f x := by
  let i := presentationIntervalIndex f.presentation x
  have hi := presentationIntervalIndex_mem f.presentation x
  have hfPiece := f.presentation.eq_piece i ⟨hi.1.le, hi.2⟩
  change (numeratorPiece f i).eval x = f x + (denominatorPiece f i).eval x
  rw [numeratorPiece, Polynomial.eval_add, hfPiece]

private theorem numerator_multiplicityAtCutPoint_add {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (j : ℕ) (i : ℤ) :
    multiplicity (numerator f) j (f.presentation.cutPoint i) =
      multiplicity f j (f.presentation.cutPoint i) +
        multiplicity (denominator f) j (f.presentation.cutPoint i) := by
  have hnum := multiplicity_cutPoint_of_presentation
    (numerator f) (numeratorPresentation f) j i
  have hf := multiplicity_cutPoint_of_presentation f f.presentation j i
  have hden := multiplicity_cutPoint_of_presentation
    (denominator f) (denominatorPresentation f) j i
  rw [numeratorPresentation_cutPoint] at hnum
  rw [denominatorPresentation_cutPoint] at hden
  rw [hnum, hf, hden]
  simp only [presentationMultiplicityAtCutPoint]
  change
    rightSign (f.presentation.cutPoint i) ^ (j + 1) *
          normalizedPolynomialJet (numeratorPiece f (i + 1)) j
            (f.presentation.cutPoint i) -
        leftSign (f.presentation.cutPoint i) ^ (j + 1) *
          normalizedPolynomialJet (numeratorPiece f i) j
            (f.presentation.cutPoint i) =
      (rightSign (f.presentation.cutPoint i) ^ (j + 1) *
            normalizedPolynomialJet (f.presentation.piece (i + 1)) j
              (f.presentation.cutPoint i) -
          leftSign (f.presentation.cutPoint i) ^ (j + 1) *
            normalizedPolynomialJet (f.presentation.piece i) j
              (f.presentation.cutPoint i)) +
        (rightSign (f.presentation.cutPoint i) ^ (j + 1) *
            normalizedPolynomialJet (denominatorPiece f (i + 1)) j
              (f.presentation.cutPoint i) -
          leftSign (f.presentation.cutPoint i) ^ (j + 1) *
            normalizedPolynomialJet (denominatorPiece f i) j
              (f.presentation.cutPoint i))
  simp only [numeratorPiece, normalizedPolynomialJet_add]
  ring

private theorem denominator_isTropicalEntire {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) : IsTropicalEntire (denominator f) := by
  rw [isTropicalEntire_iff_multiplicity_nonneg]
  intro x j hj hjn
  rcases multiplicity_eq_zero_or_cutPoint_of_presentation
      (denominator f) (denominatorPresentation f) j x with
    hzero | ⟨i, hxi, _hi⟩
  · rw [hzero]
  · rw [hxi, denominatorPresentation_cutPoint,
      denominator_multiplicityAtCutPoint f hj hjn]
    exact polePart_nonneg _

private theorem numerator_isTropicalEntire {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) : IsTropicalEntire (numerator f) := by
  rw [isTropicalEntire_iff_multiplicity_nonneg]
  intro x j hj hjn
  rcases multiplicity_eq_zero_or_cutPoint_of_presentation
      (numerator f) (numeratorPresentation f) j x with
    hzero | ⟨i, hxi, _hi⟩
  · rw [hzero]
  · rw [hxi, numeratorPresentation_cutPoint, numerator_multiplicityAtCutPoint_add,
      denominator_multiplicityAtCutPoint f hj hjn]
    rw [multiplicity_cutPoint]
    exact add_polePart_nonneg _

/-- Two functions have no common roots or poles through order `upTo`. -/
def NoCommonRootsOrPoles {n₁ n₂ : ℕ}
    (h : NthTropicalMeromorphicFunction n₁)
    (g : NthTropicalMeromorphicFunction n₂) (upTo : ℕ) : Prop :=
  ∀ x j, 1 ≤ j → j ≤ upTo →
    (¬(IsJthRoot h j x ∧ IsJthRoot g j x)) ∧
      ¬(IsJthPole h j x ∧ IsJthPole g j x)

private theorem numerator_denominator_noCommonRootsOrPoles {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) :
    NoCommonRootsOrPoles (numerator f) (denominator f) n := by
  intro x j hj hjn
  constructor
  · intro hroots
    simp only [IsJthRoot] at hroots
    rcases multiplicity_eq_zero_or_cutPoint_of_presentation
        (denominator f) (denominatorPresentation f) j x with
      hzero | ⟨i, hxi, _hi⟩
    · exact (not_lt_of_ge (by rw [hzero])) hroots.2
    · rw [hxi, denominatorPresentation_cutPoint,
        denominator_multiplicityAtCutPoint f hj hjn] at hroots
      change 0 < multiplicity (numerator f) j (f.presentation.cutPoint i) ∧
        0 < polePart (multiplicityAtCutPoint f j i) at hroots
      have hnum : multiplicity (numerator f) j (f.presentation.cutPoint i) =
          multiplicityAtCutPoint f j i +
            polePart (multiplicityAtCutPoint f j i) := by
        rw [numerator_multiplicityAtCutPoint_add, multiplicity_cutPoint,
          denominator_multiplicityAtCutPoint f hj hjn]
        rfl
      rw [hnum] at hroots
      rcases polePart_add_eq_zero_or_original_eq_zero
        (multiplicityAtCutPoint f j i) with hg | hh
      · linarith
      · linarith
  · intro hpoles
    exact (denominator_isTropicalEntire f x j hj hjn hpoles.2)

/--
Proposition 2.3, in the slightly stronger fixed-degree form produced by the
construction: both entire functions may be chosen of degree exactly `n`.
-/
theorem exists_entire_quotient_decomposition_fixedDegree
    {n : ℕ} (_hn : 0 < n) (f : NthTropicalMeromorphicFunction n) :
    ∃ g h : NthTropicalMeromorphicFunction n,
      IsTropicalEntire g ∧ IsTropicalEntire h ∧
      (∀ x, f x = h x - g x) ∧ NoCommonRootsOrPoles h g n := by
  refine ⟨denominator f, numerator f, denominator_isTropicalEntire f,
    numerator_isTropicalEntire f, ?_, numerator_denominator_noCommonRootsOrPoles f⟩
  intro x
  rw [numerator_apply]
  ring

/-- Proposition 2.3 with the paper's explicit degree parameters. -/
theorem exists_entire_quotient_decomposition
    {n : ℕ} (hn : 0 < n) (f : NthTropicalMeromorphicFunction n) :
    ∃ n₁ n₂ : ℕ, max n₁ n₂ = n ∧
      ∃ g : NthTropicalMeromorphicFunction n₁,
        ∃ h : NthTropicalMeromorphicFunction n₂,
          IsTropicalEntire g ∧ IsTropicalEntire h ∧
          (∀ x, f x = h x - g x) ∧ NoCommonRootsOrPoles h g n := by
  obtain ⟨g, h, hg, hh, hquot, hcommon⟩ :=
    exists_entire_quotient_decomposition_fixedDegree hn f
  exact ⟨n, n, max_self n, g, h, hg, hh, hquot, hcommon⟩

end

end NthTropicalNevanlinna
