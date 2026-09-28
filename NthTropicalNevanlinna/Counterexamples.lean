import NthTropicalNevanlinna.Nevanlinna.Examples
import NthTropicalNevanlinna.Curves.FermatExamples
import NthTropicalNevanlinna.Truncated.Main

/-!
# Concrete examples and counterexamples from the paper

This file collects the examples whose purpose is to show that a tempting
strengthening of one of the main results is false.  They are kept separate
from the theorem files so that the main API does not depend on concrete
piecewise-polynomial calculations.
-/

namespace NthTropicalNevanlinna

noncomputable section

open Filter Set
open scoped Topology

/-! ## Example 2.1: entire functions are not closed under max or translation -/

/-- The polynomial pieces of `f(x) = sgn(x)x²`. -/
def example21SignedQuadraticPiece (i : ℤ) : Polynomial ℝ :=
  if i ≤ 0 then -(Polynomial.X ^ 2) else Polynomial.X ^ 2

theorem example21SignedQuadraticPiece_degree (i : ℤ) :
    (example21SignedQuadraticPiece i).natDegree = 2 := by
  unfold example21SignedQuadraticPiece
  split <;> simp

theorem example21SignedQuadraticPiece_adjacent (i : ℤ) :
    (example21SignedQuadraticPiece i).eval (i : ℝ) =
      (example21SignedQuadraticPiece (i + 1)).eval (i : ℝ) := by
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · have hi0 : i ≤ 0 := hi.le
    have his : i + 1 ≤ 0 := by omega
    simp [example21SignedQuadraticPiece, hi0, his]
  · simp [example21SignedQuadraticPiece]
  · have hi0 : ¬i ≤ 0 := not_le.mpr hi
    have his : ¬i + 1 ≤ 0 := by omega
    simp [example21SignedQuadraticPiece, hi0, his]

/-- The paper's `f(x)=sgn(x)x²`, bundled as a second-order tropical
meromorphic function. -/
def example21SignedQuadratic : NthTropicalMeromorphicFunction 2 :=
  assembleNthTropicalMeromorphicFunction (tropicalHyperExponentialGrid 2)
    example21SignedQuadraticPiece
    (fun i ↦ (example21SignedQuadraticPiece_degree i).le)
    example21SignedQuadraticPiece_adjacent
    ⟨0, example21SignedQuadraticPiece_degree 0⟩

private def example21SignedQuadraticPresentation :
    PolynomialPresentation 2 example21SignedQuadratic :=
  assembledPolynomialPresentation (tropicalHyperExponentialGrid 2)
    example21SignedQuadraticPiece
    (fun i ↦ (example21SignedQuadraticPiece_degree i).le)
    example21SignedQuadraticPiece_adjacent
    ⟨0, example21SignedQuadraticPiece_degree 0⟩

@[simp] theorem example21SignedQuadratic_apply (x : ℝ) :
    example21SignedQuadratic x = if x ≤ 0 then -x ^ 2 else x ^ 2 := by
  let i := presentationIntervalIndex (tropicalHyperExponentialGrid 2) x
  have hx := presentationIntervalIndex_mem (tropicalHyperExponentialGrid 2) x
  change x ∈ Ioc ((i - 1 : ℤ) : ℝ) (i : ℝ) at hx
  rw [show example21SignedQuadratic x =
      (example21SignedQuadraticPiece i).eval x by
    exact assembledFunction_eq_piece (tropicalHyperExponentialGrid 2)
      example21SignedQuadraticPiece example21SignedQuadraticPiece_adjacent i
      ⟨hx.1.le, hx.2⟩]
  by_cases hnonpos : x ≤ 0
  · have hi : i ≤ 0 := by
      by_contra hnot
      have hint : (0 : ℤ) ≤ i - 1 := by omega
      have hcast : (0 : ℝ) ≤ ((i - 1 : ℤ) : ℝ) := by exact_mod_cast hint
      linarith [hx.1]
    simp [example21SignedQuadraticPiece, hi, hnonpos]
  · have hxpos : 0 < x := lt_of_not_ge hnonpos
    have hi : ¬i ≤ 0 := by
      intro hi0
      have hcast : (i : ℝ) ≤ 0 := by exact_mod_cast hi0
      linarith [hx.2]
    simp [example21SignedQuadraticPiece, hi, hnonpos]

private theorem example21SignedQuadratic_multiplicity_one_at_cut (i : ℤ) :
    presentationMultiplicityAtCutPoint example21SignedQuadraticPresentation 1 i = 0 := by
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · have hi0 : i ≤ 0 := hi.le
    have his : i + 1 ≤ 0 := by omega
    norm_num [example21SignedQuadraticPresentation, assembledPolynomialPresentation,
      tropicalHyperExponentialGrid,
      presentationMultiplicityAtCutPoint, example21SignedQuadraticPiece,
      hi0, his, normalizedPolynomialJet, rightSign, leftSign]
  · norm_num [example21SignedQuadraticPresentation, assembledPolynomialPresentation,
      tropicalHyperExponentialGrid, presentationMultiplicityAtCutPoint,
      example21SignedQuadraticPiece, normalizedPolynomialJet, rightSign, leftSign]
  · have hi0 : ¬i ≤ 0 := not_le.mpr hi
    have his : ¬i + 1 ≤ 0 := by omega
    norm_num [example21SignedQuadraticPresentation, assembledPolynomialPresentation,
      tropicalHyperExponentialGrid,
      presentationMultiplicityAtCutPoint, example21SignedQuadraticPiece,
      hi0, his, normalizedPolynomialJet, rightSign, leftSign]

private theorem example21SignedQuadratic_multiplicity_two_at_cut (i : ℤ) :
    presentationMultiplicityAtCutPoint example21SignedQuadraticPresentation 2 i = 0 := by
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · have hi0 : i ≤ 0 := hi.le
    have his : i + 1 ≤ 0 := by omega
    norm_num [example21SignedQuadraticPresentation, assembledPolynomialPresentation,
      tropicalHyperExponentialGrid, presentationMultiplicityAtCutPoint,
      example21SignedQuadraticPiece, hi0, his, normalizedPolynomialJet,
      rightSign, leftSign, hi]
  · norm_num [example21SignedQuadraticPresentation, assembledPolynomialPresentation,
      tropicalHyperExponentialGrid, presentationMultiplicityAtCutPoint,
      example21SignedQuadraticPiece, normalizedPolynomialJet, rightSign, leftSign]
  · have hi0 : ¬i ≤ 0 := not_le.mpr hi
    have his : ¬i + 1 ≤ 0 := by omega
    norm_num [example21SignedQuadraticPresentation, assembledPolynomialPresentation,
      tropicalHyperExponentialGrid, presentationMultiplicityAtCutPoint,
      example21SignedQuadraticPiece, hi0, his, normalizedPolynomialJet,
      rightSign, leftSign, not_lt.mpr hi.le]

theorem example21SignedQuadratic_multiplicity_one (x : ℝ) :
    multiplicity example21SignedQuadratic 1 x = 0 := by
  rcases multiplicity_eq_zero_or_cutPoint_of_presentation
      example21SignedQuadratic example21SignedQuadraticPresentation 1 x with
    hzero | ⟨i, hxi, hmul⟩
  · exact hzero
  · rw [hmul, example21SignedQuadratic_multiplicity_one_at_cut]

theorem example21SignedQuadratic_multiplicity_two (x : ℝ) :
    multiplicity example21SignedQuadratic 2 x = 0 := by
  rcases multiplicity_eq_zero_or_cutPoint_of_presentation
      example21SignedQuadratic example21SignedQuadraticPresentation 2 x with
    hzero | ⟨i, hxi, hmul⟩
  · exact hzero
  · rw [hmul, example21SignedQuadratic_multiplicity_two_at_cut]

theorem example21SignedQuadratic_entire :
    IsTropicalEntire example21SignedQuadratic := by
  rw [isTropicalEntire_iff_multiplicity_nonneg]
  intro x j hj hj2
  interval_cases j
  · rw [example21SignedQuadratic_multiplicity_one]
  · rw [example21SignedQuadratic_multiplicity_two]

/-- Explicit `f ⊕ g` from Example 2.1, where `g(x)=x`. -/
def example21MaximumPiece (i : ℤ) : Polynomial ℝ :=
  if i ≤ -1 then Polynomial.X
  else if i = 0 then -(Polynomial.X ^ 2)
  else if i = 1 then Polynomial.X
  else Polynomial.X ^ 2

theorem example21MaximumPiece_degree (i : ℤ) :
    (example21MaximumPiece i).natDegree ≤ 2 := by
  unfold example21MaximumPiece
  by_cases h1 : i ≤ -1
  · simp [h1]
  by_cases h0 : i = 0
  · simp [h1, h0]
  by_cases hi : i = 1
  · simp [h1, h0, hi]
  · simp [h1, h0, hi]

theorem example21MaximumPiece_adjacent (i : ℤ) :
    (example21MaximumPiece i).eval (i : ℝ) =
      (example21MaximumPiece (i + 1)).eval (i : ℝ) := by
  by_cases hle : i ≤ -2
  · have hi : i ≤ -1 := by omega
    have his : i + 1 ≤ -1 := by omega
    simp [example21MaximumPiece, hi, his]
  · have hilower : -1 ≤ i := by omega
    by_cases hiupper : i ≤ 1
    · interval_cases i <;> norm_num [example21MaximumPiece]
    · have hi : (2 : ℤ) ≤ i := by omega
      have hi1 : ¬i ≤ -1 := by omega
      have hi0 : i ≠ 0 := by omega
      have hii : i ≠ 1 := by omega
      have hs1 : ¬i + 1 ≤ -1 := by omega
      have hs0 : i + 1 ≠ 0 := by omega
      have hsi : i + 1 ≠ 1 := by omega
      simp [example21MaximumPiece, hi1, hi0, hii, hs1, hs0, hsi]

def example21Maximum : NthTropicalMeromorphicFunction 2 :=
  assembleNthTropicalMeromorphicFunction (tropicalHyperExponentialGrid 2)
    example21MaximumPiece example21MaximumPiece_degree
    example21MaximumPiece_adjacent
    ⟨2, by norm_num [example21MaximumPiece]⟩

private def example21MaximumPresentation : PolynomialPresentation 2 example21Maximum :=
  assembledPolynomialPresentation (tropicalHyperExponentialGrid 2)
    example21MaximumPiece example21MaximumPiece_degree
    example21MaximumPiece_adjacent
    ⟨2, by norm_num [example21MaximumPiece]⟩

theorem example21Maximum_multiplicity_two_at_zero :
    multiplicity example21Maximum 2 0 = -1 := by
  have hcut : example21MaximumPresentation.cutPoint 0 = 0 := by
    simp [example21MaximumPresentation, assembledPolynomialPresentation,
      tropicalHyperExponentialGrid]
  rw [← hcut, multiplicity_cutPoint_of_presentation]
  unfold presentationMultiplicityAtCutPoint
  dsimp [example21MaximumPresentation, assembledPolynomialPresentation,
    tropicalHyperExponentialGrid]
  simp_rw [normalizedPolynomialJet_eq_iterateDerivative_div]
  norm_num [example21MaximumPiece, rightSign, leftSign]

theorem example21Maximum_secondOrderPole_at_zero :
    IsJthPole example21Maximum 2 0 ∧
      rootOrPoleMultiplicity example21Maximum 2 0 = 1 := by
  rw [IsJthPole, rootOrPoleMultiplicity,
    example21Maximum_multiplicity_two_at_zero]
  norm_num

/-- Polynomial pieces of the translated function `f(x+1)`. -/
def example21TranslatePiece (i : ℤ) : Polynomial ℝ :=
  if i ≤ -1 then
    -(Polynomial.X ^ 2 + 2 * Polynomial.X + 1)
  else Polynomial.X ^ 2 + 2 * Polynomial.X + 1

theorem example21TranslatePiece_degree (i : ℤ) :
    (example21TranslatePiece i).natDegree = 2 := by
  have hquadlinear :
      (Polynomial.X ^ 2 + 2 * Polynomial.X : Polynomial ℝ).natDegree = 2 := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · norm_num
  have hq :
      (Polynomial.X ^ 2 + 2 * Polynomial.X + 1 : Polynomial ℝ).natDegree = 2 := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact hquadlinear
    · simpa [hquadlinear]
  have hnq :
      (-(Polynomial.X ^ 2 + 2 * Polynomial.X + 1) : Polynomial ℝ).natDegree = 2 := by
    rw [Polynomial.natDegree_neg]
    exact hq
  unfold example21TranslatePiece
  split
  · exact hnq
  · exact hq

theorem example21TranslatePiece_adjacent (i : ℤ) :
    (example21TranslatePiece i).eval (i : ℝ) =
      (example21TranslatePiece (i + 1)).eval (i : ℝ) := by
  rcases lt_trichotomy i (-1) with hi | rfl | hi
  · have hi0 : i ≤ -1 := hi.le
    have his : i + 1 ≤ -1 := by omega
    simp [example21TranslatePiece, hi0, his]
  · norm_num [example21TranslatePiece]
  · have hi0 : ¬i ≤ -1 := not_le.mpr hi
    have his : ¬i + 1 ≤ -1 := by omega
    simp [example21TranslatePiece, hi0, his]

/-- The translated function `f(x+1)` in Example 2.1. -/
def example21Translate : NthTropicalMeromorphicFunction 2 :=
  assembleNthTropicalMeromorphicFunction (tropicalHyperExponentialGrid 2)
    example21TranslatePiece (fun i ↦ (example21TranslatePiece_degree i).le)
    example21TranslatePiece_adjacent ⟨0, example21TranslatePiece_degree 0⟩

private def example21TranslatePresentation : PolynomialPresentation 2 example21Translate :=
  assembledPolynomialPresentation (tropicalHyperExponentialGrid 2)
    example21TranslatePiece (fun i ↦ (example21TranslatePiece_degree i).le)
    example21TranslatePiece_adjacent ⟨0, example21TranslatePiece_degree 0⟩

theorem example21Translate_multiplicity_two_at_neg_one :
    multiplicity example21Translate 2 (-1) = -2 := by
  have hcut : example21TranslatePresentation.cutPoint (-1) = -1 := by
    simp [example21TranslatePresentation, assembledPolynomialPresentation,
      tropicalHyperExponentialGrid]
  rw [← hcut, multiplicity_cutPoint_of_presentation]
  unfold presentationMultiplicityAtCutPoint
  dsimp [example21TranslatePresentation, assembledPolynomialPresentation,
    tropicalHyperExponentialGrid]
  simp_rw [normalizedPolynomialJet_eq_iterateDerivative_div]
  have hpos :
      (Polynomial.derivative^[2]) (example21TranslatePiece 0) = Polynomial.C 2 := by
    norm_num [example21TranslatePiece, Function.iterate_succ_apply,
      Polynomial.derivative_pow, Polynomial.derivative_mul]
  have hneg :
      (Polynomial.derivative^[2]) (example21TranslatePiece (-1)) = Polynomial.C (-2) := by
    norm_num [example21TranslatePiece, Function.iterate_succ_apply,
      Polynomial.derivative_pow, Polynomial.derivative_mul]
  rw [hpos, hneg]
  norm_num [example21TranslatePiece, rightSign, leftSign]

theorem example21Translate_secondOrderPole_at_neg_one :
    IsJthPole example21Translate 2 (-1) ∧
      rootOrPoleMultiplicity example21Translate 2 (-1) = 2 := by
  rw [IsJthPole, rootOrPoleMultiplicity,
    example21Translate_multiplicity_two_at_neg_one]
  norm_num

/-- The two closure failures asserted in Example 2.1. -/
theorem example_2_1_counterexamples :
    IsTropicalEntire example21SignedQuadratic ∧
      IsJthPole example21Maximum 2 0 ∧
      IsJthPole example21Translate 2 (-1) := by
  exact ⟨example21SignedQuadratic_entire,
    example21Maximum_secondOrderPole_at_zero.1,
    example21Translate_secondOrderPole_at_neg_one.1⟩

/-! ## The converse following Proposition 2.2 is false -/

/-- Polynomial pieces for the paper's function which vanishes on `[-1,1]`
and equals `-x + sgn(x)` outside that interval. -/
def proposition22ConversePiece (i : ℤ) : Polynomial ℝ :=
  if i ≤ -1 then -Polynomial.X - 1
  else if i ≤ 1 then 0
  else -Polynomial.X + 1

theorem proposition22ConversePiece_degree (i : ℤ) :
    (proposition22ConversePiece i).natDegree ≤ 1 := by
  unfold proposition22ConversePiece
  split_ifs <;> compute_degree!

theorem proposition22ConversePiece_adjacent (i : ℤ) :
    (proposition22ConversePiece i).eval (i : ℝ) =
      (proposition22ConversePiece (i + 1)).eval (i : ℝ) := by
  by_cases hlow : i ≤ -2
  · have hi : i ≤ -1 := by omega
    have his : i + 1 ≤ -1 := by omega
    simp [proposition22ConversePiece, hi, his]
  · have hilow : -1 ≤ i := by omega
    by_cases hhigh : i ≤ 1
    · interval_cases i <;> norm_num [proposition22ConversePiece]
    · have hi : 2 ≤ i := by omega
      have hi1 : ¬i ≤ -1 := by omega
      have hi2 : ¬i ≤ 1 := by omega
      have hs1 : ¬i + 1 ≤ -1 := by omega
      have hs2 : ¬i + 1 ≤ 1 := by omega
      simp [proposition22ConversePiece, hi1, hi2, hs1, hs2]

/-- The counterexample immediately after Proposition 2.2. -/
def proposition22ConverseCounterexample : NthTropicalMeromorphicFunction 1 :=
  assembleNthTropicalMeromorphicFunction (tropicalHyperExponentialGrid 1)
    proposition22ConversePiece proposition22ConversePiece_degree
    proposition22ConversePiece_adjacent
    ⟨-1, by simp [proposition22ConversePiece]; compute_degree!⟩

private def proposition22ConversePresentation :
    PolynomialPresentation 1 proposition22ConverseCounterexample :=
  assembledPolynomialPresentation (tropicalHyperExponentialGrid 1)
    proposition22ConversePiece proposition22ConversePiece_degree
    proposition22ConversePiece_adjacent
    ⟨-1, by simp [proposition22ConversePiece]; compute_degree!⟩

@[simp] theorem proposition22ConverseCounterexample_apply (x : ℝ) :
    proposition22ConverseCounterexample x =
      if x ≤ -1 then -x - 1 else if x ≤ 1 then 0 else -x + 1 := by
  let i := presentationIntervalIndex (tropicalHyperExponentialGrid 1) x
  have hx := presentationIntervalIndex_mem (tropicalHyperExponentialGrid 1) x
  change x ∈ Ioc ((i - 1 : ℤ) : ℝ) (i : ℝ) at hx
  rw [show proposition22ConverseCounterexample x =
      (proposition22ConversePiece i).eval x by
    exact assembledFunction_eq_piece (tropicalHyperExponentialGrid 1)
      proposition22ConversePiece proposition22ConversePiece_adjacent i
      ⟨hx.1.le, hx.2⟩]
  by_cases hleft : x ≤ -1
  · have hi : i ≤ -1 := by
      by_contra hnot
      have hint : (-1 : ℤ) ≤ i - 1 := by omega
      have hcast : (-1 : ℝ) ≤ ((i - 1 : ℤ) : ℝ) := by exact_mod_cast hint
      linarith [hx.1]
    simp [proposition22ConversePiece, hi, hleft]
  · have hxleft : -1 < x := lt_of_not_ge hleft
    by_cases hmiddle : x ≤ 1
    · have hi1 : ¬i ≤ -1 := by
        intro hi
        have hcast : (i : ℝ) ≤ -1 := by exact_mod_cast hi
        linarith [hx.2]
      have hi2 : i ≤ 1 := by
        by_contra hnot
        have hint : (1 : ℤ) ≤ i - 1 := by omega
        have hcast : (1 : ℝ) ≤ ((i - 1 : ℤ) : ℝ) := by exact_mod_cast hint
        linarith [hx.1]
      simp [proposition22ConversePiece, hi1, hi2, hleft, hmiddle]
    · have hxright : 1 < x := lt_of_not_ge hmiddle
      have hi1 : ¬i ≤ -1 := by
        intro hi
        have hcast : (i : ℝ) ≤ -1 := by exact_mod_cast hi
        linarith [hx.2]
      have hi2 : ¬i ≤ 1 := by
        intro hi
        have hcast : (i : ℝ) ≤ 1 := by exact_mod_cast hi
        linarith [hx.2]
      simp [proposition22ConversePiece, hi1, hi2, hleft, hmiddle]

theorem proposition22ConverseCounterexample_mean_equality {r : ℝ} (hr : 0 < r) :
    (proposition22ConverseCounterexample r +
        proposition22ConverseCounterexample (-r)) / 2 =
      proposition22ConverseCounterexample 0 := by
  rw [proposition22ConverseCounterexample_apply,
    proposition22ConverseCounterexample_apply,
    proposition22ConverseCounterexample_apply]
  by_cases hr1 : r ≤ 1
  · by_cases hre : r = 1
    · subst r
      norm_num
    · have hrlt : r < 1 := lt_of_le_of_ne hr1 hre
      have hnleft : ¬r ≤ -1 := by linarith
      have hnfar : ¬-r ≤ -1 := by linarith
      have hnegmid : -r ≤ 1 := by linarith
      simp [hnleft, hr1, hnfar, hnegmid]
  · have hrgt : 1 < r := lt_of_not_ge hr1
    have hnleft : ¬r ≤ -1 := by linarith
    have hnmid : ¬r ≤ 1 := by linarith
    have hnegleft : -r ≤ -1 := by linarith
    simp [hnleft, hnmid, hnegleft]

theorem proposition22ConverseCounterexample_pole_at_one :
    IsJthPole proposition22ConverseCounterexample 1 1 := by
  have hcut : proposition22ConversePresentation.cutPoint 1 = 1 := by
    simp [proposition22ConversePresentation, assembledPolynomialPresentation,
      tropicalHyperExponentialGrid]
  rw [IsJthPole, ← hcut, multiplicity_cutPoint_of_presentation]
  norm_num [presentationMultiplicityAtCutPoint,
    proposition22ConversePresentation, assembledPolynomialPresentation,
    tropicalHyperExponentialGrid, proposition22ConversePiece,
    normalizedPolynomialJet, rightSign, leftSign]

theorem proposition22_converse_is_false :
    (∀ r > 0,
      (proposition22ConverseCounterexample r +
          proposition22ConverseCounterexample (-r)) / 2 =
        proposition22ConverseCounterexample 0) ∧
      ¬ IsTropicalEntire proposition22ConverseCounterexample := by
  refine ⟨fun r hr ↦ proposition22ConverseCounterexample_mean_equality hr, ?_⟩
  intro hentire
  exact (hentire 1 1 (by norm_num) (by norm_num))
    proposition22ConverseCounterexample_pole_at_one

/-! ## Example 3.4: the complete multiplicity table -/

/-- The five polynomial pieces in Example 3.4, extended harmlessly outside
`(-3,3)` in order to use the global function API. -/
def example34Piece (i : ℤ) : Polynomial ℝ :=
  if i ≤ -2 then -2 * Polynomial.X ^ 3 - 17 * Polynomial.X ^ 2 -
      46 * Polynomial.X - 40
  else if i = -1 then 2 * Polynomial.X ^ 2 + 6 * Polynomial.X + 4
  else if i ≤ 1 then Polynomial.X ^ 2 + 2 * Polynomial.X + 1
  else if i = 2 then -Polynomial.X + 5
  else 3 * Polynomial.X ^ 3 - 15 * Polynomial.X ^ 2 +
      18 * Polynomial.X + 3

theorem example34Piece_degree (i : ℤ) : (example34Piece i).natDegree ≤ 3 := by
  unfold example34Piece
  split_ifs <;> compute_degree!

theorem example34Piece_adjacent (i : ℤ) :
    (example34Piece i).eval (i : ℝ) =
      (example34Piece (i + 1)).eval (i : ℝ) := by
  by_cases hlow : i ≤ -3
  · have hi : i ≤ -2 := by omega
    have his : i + 1 ≤ -2 := by omega
    simp [example34Piece, hi, his]
  · have hilow : -2 ≤ i := by omega
    by_cases hhigh : i ≤ 2
    · interval_cases i <;> norm_num [example34Piece]
    · have hi : 3 ≤ i := by omega
      have hi2 : ¬i ≤ -2 := by omega
      have him1 : i ≠ -1 := by omega
      have hi1 : ¬i ≤ 1 := by omega
      have hieq2 : i ≠ 2 := by omega
      have hs2 : ¬i + 1 ≤ -2 := by omega
      have hsm1 : i + 1 ≠ -1 := by omega
      have hs1 : ¬i + 1 ≤ 1 := by omega
      have hseq2 : i + 1 ≠ 2 := by omega
      simp [example34Piece, hi2, him1, hi1, hieq2,
        hs2, hsm1, hs1, hseq2]

/-- A global realization of the function from Example 3.4.  All results below
only concern the original interval `(-3,3)`. -/
def example34Function : NthTropicalMeromorphicFunction 3 :=
  assembleNthTropicalMeromorphicFunction (tropicalHyperExponentialGrid 3)
    example34Piece example34Piece_degree example34Piece_adjacent
    ⟨-2, by simp [example34Piece]; compute_degree!⟩

private def example34Presentation : PolynomialPresentation 3 example34Function :=
  assembledPolynomialPresentation (tropicalHyperExponentialGrid 3)
    example34Piece example34Piece_degree example34Piece_adjacent
    ⟨-2, by simp [example34Piece]; compute_degree!⟩

/-- Signed entries of Table 1: positive entries are roots and negative entries
are poles.  Zero entries include the fact that `x=0` is not automatically a
singularity. -/
def example34ExpectedMultiplicity (j : ℕ) (i : ℤ) : ℝ :=
  if j = 1 then
    if i = -1 then -2 else if i = 1 then -5 else if i = 2 then -5 else 0
  else if j = 2 then
    if i = -2 then -7 else if i = -1 then 1 else if i = 0 then 2
    else if i = 1 then -1 else if i = 2 then 3 else 0
  else if j = 3 then
    if i = -2 then 2 else if i = 2 then 3 else 0
  else 0

theorem example34_complete_multiplicity_table
    (j : ℕ) (i : ℤ) (hj : j ∈ Set.Icc 1 3) (hi : i ∈ Set.Icc (-2) 2) :
    multiplicity example34Function j (i : ℝ) =
      example34ExpectedMultiplicity j i := by
  have hcut : example34Presentation.cutPoint i = (i : ℝ) := by
    simp [example34Presentation, assembledPolynomialPresentation,
      tropicalHyperExponentialGrid]
  rcases hj with ⟨hj1, hj3⟩
  rcases hi with ⟨hi2, hi2'⟩
  rw [← hcut, multiplicity_cutPoint_of_presentation]
  interval_cases j <;> interval_cases i <;>
    norm_num [presentationMultiplicityAtCutPoint, example34Presentation,
      assembledPolynomialPresentation, tropicalHyperExponentialGrid,
      example34Piece, example34ExpectedMultiplicity,
      normalizedPolynomialJet_eq_iterateDerivative_div,
      Function.iterate_succ_apply, Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_pow, rightSign, leftSign] at *

/-- The displayed Jensen calculation following Table 1.  Together with
`example34_complete_multiplicity_table`, this checks both the signed data and
the final numerical identity, rather than merely copying the table. -/
theorem example34_jensen_numerical_identity (r : ℝ) :
    ((3 * r ^ 3 - 15 * r ^ 2 + 18 * r + 3) +
        (2 * r ^ 3 - 17 * r ^ 2 + 46 * r - 40)) / 2 -
      ((r - 1) ^ 2 + 2 * r ^ 2 + 3 * (r - 2) ^ 2 +
        2 * (r - 2) ^ 3 + 3 * (r - 2) ^ 3) / 2 +
      (2 * (r - 1) + 5 * (r - 1) + 5 * (r - 2) +
        7 * (r - 2) ^ 2 + (r - 1) ^ 2) / 2 = 1 := by
  ring

/-! ## Example 4.1: the characteristic need not be monotone or convex -/

/-- Polynomial arcs used in Example 4.1.  The index convention is chosen so
that piece `i` lives on `[i-1,i]`. -/
def example41Piece (i : ℤ) : Polynomial ℝ :=
  if i ≤ 0 then
    (Polynomial.X - Polynomial.C (i : ℝ)) *
      (Polynomial.X - Polynomial.C (i : ℝ) + 1)
  else
    -(Polynomial.X - Polynomial.C ((i - 1 : ℤ) : ℝ)) *
      (Polynomial.X - Polynomial.C (i : ℝ))

theorem example41Piece_degree (i : ℤ) : (example41Piece i).natDegree = 2 := by
  unfold example41Piece
  split_ifs
  · have hsecond :
        (Polynomial.X - Polynomial.C (i : ℝ) + 1 : Polynomial ℝ).natDegree = 1 := by
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_sub_C _
      · rw [Polynomial.natDegree_X_sub_C]
        norm_num
    have hsecond_ne :
        (Polynomial.X - Polynomial.C (i : ℝ) + 1 : Polynomial ℝ) ≠ 0 := by
      intro hzero
      rw [hzero] at hsecond
      norm_num at hsecond
    rw [Polynomial.natDegree_mul]
    · rw [Polynomial.natDegree_X_sub_C, hsecond]
    · exact Polynomial.X_sub_C_ne_zero _
    · exact hsecond_ne
  · rw [Polynomial.natDegree_mul]
    · rw [Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C,
        Polynomial.natDegree_X_sub_C]
    · exact neg_ne_zero.mpr (Polynomial.X_sub_C_ne_zero _)
    · exact Polynomial.X_sub_C_ne_zero _

theorem example41Piece_adjacent (i : ℤ) :
    (example41Piece i).eval (i : ℝ) =
      (example41Piece (i + 1)).eval (i : ℝ) := by
  by_cases hi : i < 0
  · have hi0 : i ≤ 0 := hi.le
    have his : i + 1 ≤ 0 := by omega
    simp [example41Piece, hi0, his]
  · by_cases hiz : i = 0
    · subst i
      norm_num [example41Piece]
    · have hipos : 0 < i := lt_of_le_of_ne (not_lt.mp hi) (Ne.symm hiz)
      have hi0 : ¬i ≤ 0 := not_le.mpr hipos
      have his : ¬i + 1 ≤ 0 := by omega
      simp [example41Piece, hi0, his]

def example41Function : NthTropicalMeromorphicFunction 2 :=
  assembleNthTropicalMeromorphicFunction (tropicalHyperExponentialGrid 2)
    example41Piece (fun i ↦ (example41Piece_degree i).le)
    example41Piece_adjacent ⟨0, example41Piece_degree 0⟩

private def example41Presentation : PolynomialPresentation 2 example41Function :=
  assembledPolynomialPresentation (tropicalHyperExponentialGrid 2)
    example41Piece (fun i ↦ (example41Piece_degree i).le)
    example41Piece_adjacent ⟨0, example41Piece_degree 0⟩

private theorem example41_multiplicity_eq_zero_of_abs_lt_one
    {y : ℝ} (hy : |y| < 1) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ 2) :
    multiplicity example41Function j y = 0 := by
  rcases multiplicity_eq_zero_or_cutPoint_of_presentation
      example41Function example41Presentation j y with hzero | ⟨i, hyi, hmul⟩
  · exact hzero
  · have hiLower : (-1 : ℤ) < i := by
      have : (-1 : ℝ) < (i : ℝ) := by
        have hycast : y = (i : ℝ) := by
          simpa [example41Presentation, assembledPolynomialPresentation,
            tropicalHyperExponentialGrid] using hyi
        rw [← hycast]
        exact (abs_lt.mp hy).1
      exact_mod_cast this
    have hiUpper : i < (1 : ℤ) := by
      have : (i : ℝ) < 1 := by
        have hycast : y = (i : ℝ) := by
          simpa [example41Presentation, assembledPolynomialPresentation,
            tropicalHyperExponentialGrid] using hyi
        rw [← hycast]
        exact (abs_lt.mp hy).2
      exact_mod_cast this
    have hi : i = 0 := by omega
    subst i
    rw [hmul]
    interval_cases j <;>
      norm_num [presentationMultiplicityAtCutPoint, example41Presentation,
        assembledPolynomialPresentation, tropicalHyperExponentialGrid,
        example41Piece, normalizedPolynomialJet_eq_iterateDerivative_div,
        Function.iterate_succ_apply, Polynomial.derivative_add,
        Polynomial.derivative_sub, Polynomial.derivative_mul,
        rightSign, leftSign]

private theorem example41_integratedCounting_eq_zero
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {j : ℕ}
    (hj1 : 1 ≤ j) (hj2 : j ≤ 2) :
    integratedCounting j r example41Function = 0 := by
  have hpoles : jthPolePoints example41Function j r = ∅ := by
    classical
    rw [Finset.eq_empty_iff_forall_notMem]
    intro y hyPoleMem
    rw [mem_jthPolePoints_iff] at hyPoleMem
    rcases hyPoleMem with ⟨hyr, hpole⟩
    have hyabs : |y| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hyr.1, hyr.2]
    have hzero := example41_multiplicity_eq_zero_of_abs_lt_one
      hyabs hj1 hj2
    rw [IsJthPole, hzero] at hpole
    linarith
  simp [integratedCounting, hpoles]

theorem example41_characteristic_on_unit_interval
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    characteristic r example41Function = (-r ^ 2 + r) / 2 := by
  have hpos : example41Function r = -r * (r - 1) := by
    change assembledFunction (tropicalHyperExponentialGrid 2) example41Piece r = _
    rw [assembledFunction_eq_piece (tropicalHyperExponentialGrid 2)
      example41Piece example41Piece_adjacent 1 (by simpa [tropicalHyperExponentialGrid]
        using (show r ∈ Set.Icc (0 : ℝ) 1 from ⟨hr0, hr1⟩))]
    norm_num [example41Piece]
  have hneg : example41Function (-r) = r * (r - 1) := by
    change assembledFunction (tropicalHyperExponentialGrid 2) example41Piece (-r) = _
    rw [assembledFunction_eq_piece (tropicalHyperExponentialGrid 2)
      example41Piece example41Piece_adjacent 0 (by
        simpa [tropicalHyperExponentialGrid] using
          (show -r ∈ Set.Icc (-1 : ℝ) 0 by constructor <;> linarith))]
    norm_num [example41Piece]
    ring
  have hpositive : 0 ≤ -r * (r - 1) :=
    mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hr0) (sub_nonpos.mpr hr1)
  have hnegative : r * (r - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0 (sub_nonpos.mpr hr1)
  have hN1 := example41_integratedCounting_eq_zero hr0 hr1 (j := 1) (by norm_num) (by norm_num)
  have hN2 := example41_integratedCounting_eq_zero hr0 hr1 (j := 2) (by norm_num) (by norm_num)
  have hsum :
      ∑ j ∈ Finset.Icc 1 2, integratedCounting j r example41Function = 0 := by
    rw [show Finset.Icc 1 2 = {1, 2} by decide]
    simp [hN1, hN2]
  rw [characteristic, hsum, add_zero]
  unfold proximity maxPlusPositivePart
  rw [hpos, hneg, max_eq_left hpositive, max_eq_right hnegative]
  ring

theorem example41_characteristic_not_monotone :
    ¬ Monotone (fun r : ℝ ↦ characteristic r example41Function) := by
  intro hmono
  have h := hmono (show (1 / 2 : ℝ) ≤ 3 / 4 by norm_num)
  change characteristic (1 / 2) example41Function ≤
    characteristic (3 / 4) example41Function at h
  rw [example41_characteristic_on_unit_interval (by norm_num) (by norm_num),
    example41_characteristic_on_unit_interval (by norm_num) (by norm_num)] at h
  norm_num at h

theorem example41_characteristic_midpoint_violation :
    characteristic (1 / 2) example41Function >
      (characteristic 0 example41Function + characteristic 1 example41Function) / 2 := by
  rw [example41_characteristic_on_unit_interval (by norm_num) (by norm_num),
    example41_characteristic_on_unit_interval (by norm_num) (by norm_num),
    example41_characteristic_on_unit_interval (by norm_num) (by norm_num)]
  norm_num

theorem example41_characteristic_not_convex :
    ¬ ConvexOn ℝ (Set.Icc 0 1)
      (fun r : ℝ ↦ characteristic r example41Function) := by
  intro hconv
  have hmid := hconv.2 (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hviolate := example41_characteristic_midpoint_violation
  norm_num at hmid
  linarith

/-! ## Example 5.5: global max spline, cubic counting, and quadratic growth -/

/-- The affine piece of `f₁` on `[2k,2k+2]` in Example 5.5. -/
def example55AffinePiece (k : ℕ) : Polynomial ℝ :=
  Polynomial.C (4 * (k : ℝ) + 2) * Polynomial.X -
    Polynomial.C (2 * (k : ℝ) * (2 * (k : ℝ) + 2) + 1 / 2)

def example55LowerCrossing (k : ℕ) : ℝ :=
  2 * (k : ℝ) + 1 - Real.sqrt 2 / 2

def example55UpperCrossing (k : ℕ) : ℝ :=
  2 * (k : ℝ) + 1 + Real.sqrt 2 / 2

theorem example55_crossing_equation (k : ℕ) (x : ℝ) :
    x ^ 2 = (example55AffinePiece k).eval x ↔
      x = example55LowerCrossing k ∨ x = example55UpperCrossing k := by
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  simp only [example55AffinePiece, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_natCast, Polynomial.eval_X,
    Polynomial.eval_C]
  dsimp [example55LowerCrossing, example55UpperCrossing]
  constructor
  · intro h
    have hfactor :
        (x - (2 * (k : ℝ) + 1)) ^ 2 = (Real.sqrt 2 / 2) ^ 2 := by
      nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hfactor with hpos | hneg
    · right; linarith
    · left; linarith
  · rintro (rfl | rfl) <;> nlinarith

theorem example55_lowerCrossing_mem_interval (k : ℕ) :
    example55LowerCrossing k ∈
      Set.Ioo (2 * (k : ℝ)) (2 * (k : ℝ) + 2) := by
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsqrtlt : Real.sqrt 2 < 2 := by nlinarith
  constructor <;> dsimp [example55LowerCrossing] <;> linarith

/-- At the lower crossing, the max switches from the quadratic germ to the
affine germ.  Their intrinsic normalized second-jet jump is `-1`, exactly the
multiplicity printed in Example 5.5. -/
theorem example55_lowerCrossing_secondJetJump (k : ℕ) :
    normalizedPolynomialJet (example55AffinePiece k) 2
        (example55LowerCrossing k) -
      normalizedPolynomialJet (Polynomial.X ^ 2) 2
        (example55LowerCrossing k) = -1 := by
  simp_rw [normalizedPolynomialJet_eq_iterateDerivative_div]
  norm_num [example55AffinePiece,
    Function.iterate_succ_apply, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow]

theorem example55_local_secondOrderPole_data (k : ℕ) :
    (example55LowerCrossing k ∈
      Set.Ioo (2 * (k : ℝ)) (2 * (k : ℝ) + 2)) ∧
      (example55LowerCrossing k) ^ 2 =
        (example55AffinePiece k).eval (example55LowerCrossing k) ∧
      normalizedPolynomialJet (example55AffinePiece k) 2
          (example55LowerCrossing k) -
        normalizedPolynomialJet (Polynomial.X ^ 2) 2
          (example55LowerCrossing k) = -1 := by
  exact ⟨example55_lowerCrossing_mem_interval k,
    (example55_crossing_equation k _).2 (Or.inl rfl),
    example55_lowerCrossing_secondJetJump k⟩

/-- Even cut grid `2i` used by the paper's piecewise-linear coordinate `f₁`. -/
def example55Cut (i : ℤ) : ℝ := 2 * (i : ℝ)

theorem example55Cut_strictMono : StrictMono example55Cut := by
  intro i l hil
  dsimp [example55Cut]
  exact mul_lt_mul_of_pos_left (by exact_mod_cast hil) (by norm_num)

@[simp] theorem example55Cut_zero : example55Cut 0 = 0 := by
  simp [example55Cut]

theorem example55Cut_tendsto_atTop : Tendsto example55Cut atTop atTop := by
  change Tendsto (fun i : ℤ ↦ 2 * (i : ℝ)) atTop atTop
  exact tendsto_intCast_atTop_atTop.const_mul_atTop' (by norm_num)

theorem example55Cut_tendsto_atBot : Tendsto example55Cut atBot atBot := by
  change Tendsto (fun i : ℤ ↦ 2 * (i : ℝ)) atBot atBot
  exact (tendsto_const_mul_atBot_of_pos (f := fun i : ℤ ↦ (i : ℝ))
    (by norm_num : (0 : ℝ) < 2)).2
      (tendsto_intCast_atBot_iff.mpr Filter.tendsto_id)

def example55Grid : PolynomialPresentation 1 (fun x : ℝ ↦ x) where
  cutPoint := example55Cut
  piece _ := Polynomial.X
  cutPoint_strictMono := example55Cut_strictMono
  cutPoint_zero := example55Cut_zero
  cutPoint_tendsto_atTop := example55Cut_tendsto_atTop
  cutPoint_tendsto_atBot := example55Cut_tendsto_atBot
  piece_natDegree_le := by simp
  eq_piece := by simp
  exists_piece_natDegree_eq := ⟨0, by simp⟩

/-- The affine pieces of `f₁`; piece `i>0` corresponds to `k=i-1`. -/
def example55SecondCoordinatePiece (i : ℤ) : Polynomial ℝ :=
  if i ≤ 0 then Polynomial.C (-1 / 2)
  else Polynomial.C (4 * (i : ℝ) - 2) * Polynomial.X -
    Polynomial.C (2 * ((i : ℝ) - 1) * (2 * (i : ℝ)) + 1 / 2)

theorem example55SecondCoordinatePiece_degree (i : ℤ) :
    (example55SecondCoordinatePiece i).natDegree ≤ 1 := by
  unfold example55SecondCoordinatePiece
  split_ifs
  · simp
  · let a : ℝ := 4 * (i : ℝ) - 2
    let b : ℝ := 2 * ((i : ℝ) - 1) * (2 * (i : ℝ)) + 1 / 2
    change (Polynomial.C a * Polynomial.X - Polynomial.C b).natDegree ≤ 1
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (Polynomial.natDegree_mul_le.trans (by simp)) (by simp))

theorem example55SecondCoordinatePiece_adjacent (i : ℤ) :
    (example55SecondCoordinatePiece i).eval (example55Cut i) =
      (example55SecondCoordinatePiece (i + 1)).eval (example55Cut i) := by
  by_cases hi : i < 0
  · have hi0 : i ≤ 0 := hi.le
    have his : i + 1 ≤ 0 := by omega
    simp [example55SecondCoordinatePiece, hi0, his]
  · by_cases hiz : i = 0
    · subst i
      norm_num [example55SecondCoordinatePiece, example55Cut]
    · have hipos : 0 < i := lt_of_le_of_ne (not_lt.mp hi) (Ne.symm hiz)
      have hi0 : ¬i ≤ 0 := not_le.mpr hipos
      have his : ¬i + 1 ≤ 0 := by omega
      rw [example55SecondCoordinatePiece, if_neg hi0,
        example55SecondCoordinatePiece, if_neg his]
      simp only [example55Cut, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      push_cast
      ring

def example55SecondCoordinate : NthTropicalMeromorphicFunction 1 :=
  assembleNthTropicalMeromorphicFunction example55Grid
    example55SecondCoordinatePiece example55SecondCoordinatePiece_degree
    example55SecondCoordinatePiece_adjacent
    ⟨1, by simp [example55SecondCoordinatePiece]; compute_degree!⟩

private def example55SecondCoordinatePresentation :
    PolynomialPresentation 1 example55SecondCoordinate :=
  assembledPolynomialPresentation example55Grid
    example55SecondCoordinatePiece example55SecondCoordinatePiece_degree
    example55SecondCoordinatePiece_adjacent
    ⟨1, by simp [example55SecondCoordinatePiece]; compute_degree!⟩

private theorem example55SecondCoordinate_multiplicity_one_at_cut (i : ℤ) :
    0 ≤ presentationMultiplicityAtCutPoint
      example55SecondCoordinatePresentation 1 i := by
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · have hi0 : i ≤ 0 := hi.le
    have his : i + 1 ≤ 0 := by omega
    norm_num [presentationMultiplicityAtCutPoint,
      example55SecondCoordinatePresentation, assembledPolynomialPresentation,
      example55Grid, example55SecondCoordinatePiece, hi0, his,
      normalizedPolynomialJet_eq_iterateDerivative_div,
      Function.iterate_succ_apply, rightSign, leftSign]
  · norm_num [presentationMultiplicityAtCutPoint,
      example55SecondCoordinatePresentation, assembledPolynomialPresentation,
      example55Grid, example55SecondCoordinatePiece,
      normalizedPolynomialJet_eq_iterateDerivative_div,
      Function.iterate_succ_apply, rightSign, leftSign]
  · have hi0 : ¬i ≤ 0 := not_le.mpr hi
    have his : ¬i + 1 ≤ 0 := by omega
    norm_num [presentationMultiplicityAtCutPoint,
      example55SecondCoordinatePresentation, assembledPolynomialPresentation,
      example55Grid, example55SecondCoordinatePiece, hi0, his,
      normalizedPolynomialJet_eq_iterateDerivative_div,
      Function.iterate_succ_apply, rightSign, leftSign]

theorem example55SecondCoordinate_entire :
    IsTropicalEntire example55SecondCoordinate := by
  rw [isTropicalEntire_iff_multiplicity_nonneg]
  intro x j hj hj1
  have hjEq : j = 1 := by omega
  subst j
  rcases multiplicity_eq_zero_or_cutPoint_of_presentation
      example55SecondCoordinate example55SecondCoordinatePresentation 1 x with
    hzero | ⟨i, hxi, hmul⟩
  · rw [hzero]
  · rw [hmul]
    exact example55SecondCoordinate_multiplicity_one_at_cut i

theorem example55SecondCoordinate_eq_affinePiece (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (2 * (k : ℝ)) (2 * (k : ℝ) + 2)) :
    example55SecondCoordinate x = (example55AffinePiece k).eval x := by
  have hk0 : (0 : ℤ) ≤ Int.ofNat k := Int.natCast_nonneg k
  have hkpos : ¬(Int.ofNat k + 1 ≤ 0) := by omega
  have hx' : x ∈ Set.Icc (example55Cut ((Int.ofNat k + 1) - 1))
      (example55Cut (Int.ofNat k + 1)) := by
    constructor
    · simpa [example55Cut] using hx.1
    · have hcut : example55Cut (Int.ofNat k + 1) = 2 * (k : ℝ) + 2 := by
        simp [example55Cut]
        ring
      rw [hcut]
      exact hx.2
  change assembledFunction example55Grid example55SecondCoordinatePiece x = _
  rw [assembledFunction_eq_piece example55Grid example55SecondCoordinatePiece
    example55SecondCoordinatePiece_adjacent (Int.ofNat k + 1) (by
      simpa [example55Grid] using hx')]
  simp only [example55SecondCoordinatePiece, if_neg hkpos, example55AffinePiece,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  norm_num
  ring

theorem example55SecondCoordinate_apply_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    example55SecondCoordinate x = -1 / 2 := by
  let i := presentationIntervalIndex example55Grid x
  have hxmem := presentationIntervalIndex_mem example55Grid x
  have hi : i ≤ 0 := by
    by_contra hnot
    have hi1 : 1 ≤ i := by omega
    have him1 : (0 : ℤ) ≤ i - 1 := by omega
    have hcut : 0 ≤ example55Cut (i - 1) := by
      dsimp [example55Cut]
      exact mul_nonneg (by norm_num) (by exact_mod_cast him1)
    change x ∈ Set.Ioc (example55Cut (i - 1)) (example55Cut i) at hxmem
    linarith [hxmem.1]
  change assembledFunction example55Grid example55SecondCoordinatePiece x = _
  rw [assembledFunction_eq_piece example55Grid example55SecondCoordinatePiece
    example55SecondCoordinatePiece_adjacent i ⟨hxmem.1.le, hxmem.2⟩]
  simp [example55SecondCoordinatePiece, hi]

/-- On the positive half-line the piecewise-linear coordinate lies at most
`1/2` above the quadratic coordinate. -/
theorem example55SecondCoordinate_le_quadratic_add_half
    {x : ℝ} (_hx : 0 ≤ x) :
    example55SecondCoordinate x ≤ x ^ 2 + 1 / 2 := by
  let i := presentationIntervalIndex example55Grid x
  have hxmem := presentationIntervalIndex_mem example55Grid x
  change assembledFunction example55Grid example55SecondCoordinatePiece x ≤ _
  rw [assembledFunction_eq_piece example55Grid example55SecondCoordinatePiece
    example55SecondCoordinatePiece_adjacent i ⟨hxmem.1.le, hxmem.2⟩]
  by_cases hi : i ≤ 0
  · simp [example55SecondCoordinatePiece, hi]
    nlinarith [sq_nonneg x]
  · have hipos : 0 < (i : ℝ) := by exact_mod_cast (lt_of_not_ge hi)
    rw [example55SecondCoordinatePiece, if_neg hi]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    have hsquare : 0 ≤ (x - (2 * (i : ℝ) - 1)) ^ 2 := sq_nonneg _
    nlinarith

/-- The global realization of `P∘f=max(f₀,f₁)` in Example 5.5. -/
def example55CompositionRealization :=
  maxRealization example21SignedQuadratic example55SecondCoordinate

def example55Composition : NthTropicalMeromorphicFunction
    example55CompositionRealization.order :=
  example55CompositionRealization.function

@[simp] theorem example55Composition_apply (x : ℝ) :
    example55Composition x =
      max (example21SignedQuadratic x) (example55SecondCoordinate x) :=
  example55CompositionRealization.eq_fun x

/-- The paper's heterogeneous-order curve `[f₀:f₁]`: the coordinates have
exact orders two and one, respectively. -/
def example55Curve : TropicalHolomorphicCurveRepresentation 2 1 :=
  projectivePairRepresentationOfOrders example21SignedQuadratic
    example55SecondCoordinate example21SignedQuadratic_entire
    example55SecondCoordinate_entire (by norm_num)

theorem example55Curve_coordinateMaximum (x : ℝ) :
    curveCoordinateMaximum example55Curve x = example55Composition x := by
  rw [example55Curve,
    curveCoordinateMaximum_projectivePairOfOrders]
  exact (example55Composition_apply x).symm

@[simp] theorem example55Composition_zero : example55Composition 0 = 0 := by
  rw [example55Composition_apply, example21SignedQuadratic_apply,
    example55SecondCoordinate_apply_of_nonpos (le_refl 0)]
  norm_num

theorem example55Composition_positive_bounds {r : ℝ} (hr : 0 ≤ r) :
    r ^ 2 ≤ example55Composition r ∧
      example55Composition r ≤ r ^ 2 + 1 / 2 := by
  by_cases hr0 : r = 0
  · subst r
    constructor <;> rw [example55Composition_zero] <;> norm_num
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    rw [example55Composition_apply, example21SignedQuadratic_apply,
      if_neg (not_le.mpr hrpos)]
    exact ⟨le_max_left _ _, max_le (by norm_num)
      (example55SecondCoordinate_le_quadratic_add_half hr)⟩

theorem example55Composition_negative_bounds {r : ℝ} (hr : 0 ≤ r) :
    (-1 / 2 : ℝ) ≤ example55Composition (-r) ∧
      example55Composition (-r) ≤ 0 := by
  rw [example55Composition_apply, example21SignedQuadratic_apply,
    if_pos (neg_nonpos.mpr hr),
    example55SecondCoordinate_apply_of_nonpos (neg_nonpos.mpr hr)]
  constructor
  · exact le_max_right _ _
  · exact max_le (neg_nonpos.mpr (sq_nonneg (-r))) (by norm_num)

/-- The paper's `T_f(r)=r²/2+O(1)` estimate, with an explicit uniform
error `1/4`. -/
theorem example55Curve_characteristic_error_bound {r : ℝ} (hr : 0 ≤ r) :
    |cartanCharacteristic example55Curve r - (1 / 2 : ℝ) * r ^ 2| ≤ 1 / 4 := by
  have hp := example55Composition_positive_bounds hr
  have hn := example55Composition_negative_bounds hr
  rw [cartanCharacteristic, example55Curve_coordinateMaximum,
    example55Curve_coordinateMaximum, example55Curve_coordinateMaximum,
    example55Composition_zero, sub_zero]
  rw [abs_le]
  constructor <;> linarith

/-- Hence the exact curve object satisfies the quadratic asymptotic asserted
in Example 5.5. -/
theorem example55Curve_characteristic_quadratic :
    HasQuadraticAsymptotic
      (fun r ↦ cartanCharacteristic example55Curve r) (1 / 2) := by
  have hbig :
      (fun r ↦ cartanCharacteristic example55Curve r - (1 / 2 : ℝ) * r ^ 2)
        =O[atTop] (fun _ : ℝ ↦ (1 : ℝ)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1 / 4, ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    simpa [Real.norm_eq_abs] using example55Curve_characteristic_error_bound hr
  have hone : (fun r : ℝ ↦ r ^ 0) =o[atTop] fun r : ℝ ↦ r ^ 2 :=
    Asymptotics.isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (p := 0) (q := 2)
      (by omega)
  exact hbig.trans_isLittleO (by simpa using hone)

private theorem example55_quadratic_sub_affine (k : ℕ) (x : ℝ) :
    x ^ 2 - (example55AffinePiece k).eval x =
      (x - (2 * (k : ℝ) + 1)) ^ 2 - (Real.sqrt 2 / 2) ^ 2 := by
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  simp [example55AffinePiece]
  nlinarith

private theorem example55Composition_left_germ (k : ℕ) :
    example55Composition.presentation.leftPieceAt (example55LowerCrossing k) =
      Polynomial.X ^ 2 := by
  let x := example55LowerCrossing k
  let s := Real.sqrt 2 / 2
  have hs : 0 < s := div_pos (Real.sqrt_pos.2 (by norm_num)) (by norm_num)
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtlt : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hxmem := example55_lowerCrossing_mem_interval k
  have hlocal : ∀ y ∈ Set.Ioo (x - s / 4) x,
      example55Composition y = (Polynomial.X ^ 2).eval y := by
    intro y hy
    have hylower : 2 * (k : ℝ) < y := by
      dsimp [x, example55LowerCrossing, s] at hy
      norm_num at hy hsqrtlt ⊢
      linarith
    have hypos : 0 < y := lt_of_le_of_lt (by positivity) hylower
    have hyinterval : y ∈ Set.Icc (2 * (k : ℝ)) (2 * (k : ℝ) + 2) := by
      constructor
      · exact hylower.le
      · exact hy.2.le.trans hxmem.2.le
    rw [example55Composition_apply, example21SignedQuadratic_apply,
      if_neg (not_le.mpr hypos), example55SecondCoordinate_eq_affinePiece k hyinterval]
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    apply max_eq_left
    have hdiff := example55_quadratic_sub_affine k y
    dsimp [x, example55LowerCrossing, s] at hy
    have ht : y - (2 * (k : ℝ) + 1) < -(Real.sqrt 2 / 2) := by
      norm_num at hy ⊢
      linarith
    have hprod : 0 <
        (y - (2 * (k : ℝ) + 1) - Real.sqrt 2 / 2) *
          (y - (2 * (k : ℝ) + 1) + Real.sqrt 2 / 2) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    nlinarith
  obtain ⟨a, ha, hpiece⟩ :=
    example55Composition.presentation.exists_left_germ_interval x
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioo_infinite (max_lt ha
    (sub_lt_self x (div_pos hs (by norm_num : (0 : ℝ) < 4))))).mono
  intro y hy
  have hya : y ∈ Set.Ioo a x := ⟨(le_max_left _ _).trans_lt hy.1, hy.2⟩
  have hylocal : y ∈ Set.Ioo (x - s / 4) x :=
    ⟨(le_max_right _ _).trans_lt hy.1, hy.2⟩
  exact (hpiece y hya).symm.trans (hlocal y hylocal)

private theorem example55Composition_right_germ (k : ℕ) :
    example55Composition.presentation.rightPieceAt (example55LowerCrossing k) =
      example55AffinePiece k := by
  let x := example55LowerCrossing k
  let s := Real.sqrt 2 / 2
  have hs : 0 < s := div_pos (Real.sqrt_pos.2 (by norm_num)) (by norm_num)
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtlt : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hxmem := example55_lowerCrossing_mem_interval k
  have hlocal : ∀ y ∈ Set.Ioo x (x + s / 4),
      example55Composition y = (example55AffinePiece k).eval y := by
    intro y hy
    have hypos : 0 < y :=
      (show 0 ≤ 2 * (k : ℝ) by positivity).trans_lt (hxmem.1.trans hy.1)
    have hyinterval : y ∈ Set.Icc (2 * (k : ℝ)) (2 * (k : ℝ) + 2) := by
      constructor
      · exact hxmem.1.le.trans hy.1.le
      · dsimp [x, example55LowerCrossing, s] at hy ⊢
        norm_num at hy hsqrtlt ⊢
        linarith
    rw [example55Composition_apply, example21SignedQuadratic_apply,
      if_neg (not_le.mpr hypos), example55SecondCoordinate_eq_affinePiece k hyinterval]
    apply max_eq_right
    have hdiff := example55_quadratic_sub_affine k y
    dsimp [x, example55LowerCrossing, s] at hy
    have htlow : -(Real.sqrt 2 / 2) < y - (2 * (k : ℝ) + 1) := by
      norm_num at hy ⊢
      linarith
    have hthigh : y - (2 * (k : ℝ) + 1) < 0 := by
      norm_num at hy ⊢
      linarith
    have hprod : 0 <
        (Real.sqrt 2 / 2 - (y - (2 * (k : ℝ) + 1))) *
          (Real.sqrt 2 / 2 + (y - (2 * (k : ℝ) + 1))) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  obtain ⟨b, hb, hpiece⟩ :=
    example55Composition.presentation.exists_right_germ_interval x
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioo_infinite
    (lt_min hb (lt_add_of_pos_right x
      (div_pos hs (by norm_num : (0 : ℝ) < 4))))).mono
  intro y hy
  have hyb : y ∈ Set.Ioo x b := ⟨hy.1, hy.2.trans_le (min_le_left _ _)⟩
  have hylocal : y ∈ Set.Ioo x (x + s / 4) :=
    ⟨hy.1, hy.2.trans_le (min_le_right _ _)⟩
  exact (hpiece y hyb).symm.trans (hlocal y hylocal)

theorem example55Composition_lowerCrossing_isSecondOrderPole (k : ℕ) :
    IsJthPole example55Composition 2 (example55LowerCrossing k) ∧
      rootOrPoleMultiplicity example55Composition 2
        (example55LowerCrossing k) = 1 := by
  have hxpos : 0 < example55LowerCrossing k :=
    (show 0 ≤ 2 * (k : ℝ) by positivity).trans_lt
      (example55_lowerCrossing_mem_interval k).1
  rw [IsJthPole, rootOrPoleMultiplicity, multiplicity,
    multiplicityUsingPresentation, example55Composition_left_germ k,
    example55Composition_right_germ k, rightSign_of_nonneg hxpos.le,
    leftSign_of_pos hxpos]
  have hjump := example55_lowerCrossing_secondJetJump k
  simp only [one_pow, one_mul]
  constructor
  · linarith
  · rw [hjump]
    norm_num

/-- The lower crossings form a strictly increasing infinite family. -/
theorem example55LowerCrossing_strictMono : StrictMono example55LowerCrossing := by
  intro a b hab
  dsimp [example55LowerCrossing]
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  linarith

theorem example55LowerCrossing_injective : Function.Injective example55LowerCrossing :=
  example55LowerCrossing_strictMono.injective

/-- If the first `M` lower crossings fit inside the radial interval, each of
them occurs in the intrinsic second-order pole Finset. -/
theorem example55LowerCrossing_mem_polePoints
    {M i : ℕ} {r : ℝ} (hi : i ∈ Finset.range M)
    (hMr : 2 * (M : ℝ) ≤ r) :
    example55LowerCrossing i ∈ jthPolePoints example55Composition 2 r := by
  have hiM : i + 1 ≤ M := Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
  have hiM' : 2 * ((i + 1 : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
    gcongr
  have hxmem := example55_lowerCrossing_mem_interval i
  have hxpos : 0 < example55LowerCrossing i :=
    (show 0 ≤ 2 * (i : ℝ) by positivity).trans_lt hxmem.1
  apply mem_jthPolePoints_iff.mpr
  constructor
  · constructor
    · have hr0 : 0 ≤ r := (by positivity : 0 ≤ 2 * (M : ℝ)).trans hMr
      linarith
    · calc
        example55LowerCrossing i < 2 * (i : ℝ) + 2 := hxmem.2
        _ = 2 * ((i + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ 2 * (M : ℝ) := hiM'
        _ ≤ r := hMr
  · exact (example55Composition_lowerCrossing_isSecondOrderPole i).1

/-- The paper's finite-family lower bound, with the actual lower crossings
first inserted into the intrinsic pole sum and then bounded by the simpler
locations `2(i+1)`. -/
theorem example55_integratedCounting_lowerBound
    (M : ℕ) (r : ℝ) (hMr : 2 * (M : ℝ) ≤ r) :
    (1 / 2 : ℝ) * ∑ i ∈ Finset.range M,
        (r - 2 * ((i + 1 : ℕ) : ℝ)) ^ 2 ≤
      integratedCounting 2 r example55Composition := by
  classical
  let S : Finset ℝ := (Finset.range M).image example55LowerCrossing
  have hsubset : S ⊆ jthPolePoints example55Composition 2 r := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
    exact example55LowerCrossing_mem_polePoints hi hMr
  unfold integratedCounting
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    (∑ i ∈ Finset.range M, (r - 2 * ((i + 1 : ℕ) : ℝ)) ^ 2) ≤
        ∑ i ∈ Finset.range M,
          rootOrPoleMultiplicity example55Composition 2
              (example55LowerCrossing i) *
            (r - |example55LowerCrossing i|) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [(example55Composition_lowerCrossing_isSecondOrderPole i).2]
      simp only [one_mul]
      have hiM : i + 1 ≤ M := Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
      have hiM' : 2 * ((i + 1 : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
        gcongr
      have hxmem := example55_lowerCrossing_mem_interval i
      have hxpos : 0 < example55LowerCrossing i :=
        (show 0 ≤ 2 * (i : ℝ) by positivity).trans_lt hxmem.1
      rw [abs_of_pos hxpos]
      have hxle : example55LowerCrossing i ≤ 2 * ((i + 1 : ℕ) : ℝ) := by
        calc
          example55LowerCrossing i ≤ 2 * (i : ℝ) + 2 := hxmem.2.le
          _ = 2 * ((i + 1 : ℕ) : ℝ) := by push_cast; ring
      have hbase : 0 ≤ r - 2 * ((i + 1 : ℕ) : ℝ) := by linarith
      exact pow_le_pow_left₀ hbase (sub_le_sub_left hxle r) 2
    _ = ∑ y ∈ S,
        rootOrPoleMultiplicity example55Composition 2 y * (r - |y|) ^ 2 := by
      dsimp [S]
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact example55LowerCrossing_injective hab
    _ ≤ ∑ y ∈ jthPolePoints example55Composition 2 r,
        rootOrPoleMultiplicity example55Composition 2 y * (r - |y|) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro y hyPole hyS
      have hyr := (mem_jthPolePoints_iff.mp hyPole).1
      exact mul_nonneg (abs_nonneg _)
        (pow_nonneg (sub_nonneg.mpr (abs_lt.mpr hyr).le) _)

/-- Reversing the first `M` natural numbers identifies the square sum which
occurs at radius `2M` with the standard sum of squares. -/
theorem example55_reverseSquareSum (M : ℕ) :
    (∑ i ∈ Finset.range M,
        ((M : ℝ) - ((i + 1 : ℕ) : ℝ)) ^ 2) =
      ∑ i ∈ Finset.range M, (i : ℝ) ^ 2 := by
  classical
  apply Finset.sum_bij (fun i _ ↦ M - 1 - i)
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi j hj hij
    simp only [Finset.mem_range] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    refine ⟨M - 1 - j, by simp only [Finset.mem_range]; omega, ?_⟩
    omega
  · intro i hi
    have hiM : i + 1 ≤ M := Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
    have hnat : M - 1 - i = M - (i + 1) := by omega
    rw [hnat, Nat.cast_sub hiM]

/-- Closed form for the real-valued sum of the first `M` squares. -/
theorem example55_sumRangeSquares (M : ℕ) :
    (∑ i ∈ Finset.range M, (i : ℝ) ^ 2) =
      (M : ℝ) * ((M : ℝ) - 1) * (2 * (M : ℝ) - 1) / 6 := by
  induction M with
  | zero => norm_num
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- At the even radius `r=2M`, the elementary finite sum in the paper is
exactly a cubic polynomial in `M`. -/
theorem example55_evenRadius_explicitSum (M : ℕ) :
    (1 / 2 : ℝ) * ∑ i ∈ Finset.range M,
        (2 * (M : ℝ) - 2 * ((i + 1 : ℕ) : ℝ)) ^ 2 =
      (M : ℝ) * ((M : ℝ) - 1) * (2 * (M : ℝ) - 1) / 3 := by
  have hsum :
      (∑ i ∈ Finset.range M,
          (2 * (M : ℝ) - 2 * ((i + 1 : ℕ) : ℝ)) ^ 2) =
        4 * ∑ i ∈ Finset.range M,
          ((M : ℝ) - ((i + 1 : ℕ) : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    (1 / 2 : ℝ) * ∑ i ∈ Finset.range M,
        (2 * (M : ℝ) - 2 * ((i + 1 : ℕ) : ℝ)) ^ 2 =
        2 * ∑ i ∈ Finset.range M,
          ((M : ℝ) - ((i + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [hsum]
      ring
    _ = 2 * ∑ i ∈ Finset.range M, (i : ℝ) ^ 2 := by
      rw [example55_reverseSquareSum]
    _ = (M : ℝ) * ((M : ℝ) - 1) * (2 * (M : ℝ) - 1) / 3 := by
      rw [example55_sumRangeSquares]
      ring

/-- The intrinsic counting function therefore dominates the exact cubic
finite sum at every even radius. -/
theorem example55_evenRadius_cubicLowerBound (M : ℕ) :
    (M : ℝ) * ((M : ℝ) - 1) * (2 * (M : ℝ) - 1) / 3 ≤
      integratedCounting 2 (2 * (M : ℝ)) example55Composition := by
  rw [← example55_evenRadius_explicitSum M]
  exact example55_integratedCounting_lowerBound M (2 * (M : ℝ)) le_rfl

/-- This exact cubic lower-bound polynomial is asymptotic to the paper's
`r³/12` after the substitution `r=2M`. -/
theorem example55_cubicLowerBound_ratio_tendsto_one :
    Tendsto (fun M : ℕ ↦
        ((M : ℝ) * ((M : ℝ) - 1) * (2 * (M : ℝ) - 1) / 3) /
          ((2 * (M : ℝ)) ^ 3 / 12)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun M : ℕ ↦ ((M : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hprod : Tendsto (fun M : ℕ ↦
      (1 - (M : ℝ)⁻¹) * (1 - (1 / 2 : ℝ) * (M : ℝ)⁻¹)) atTop (𝓝 1) := by
    convert (tendsto_const_nhds.sub hinv).mul
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)) using 1 <;> norm_num
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The paper's cubic comparison term at an arbitrary real radius, with
`M=⌊r/2⌋`. -/
def example55RealRadiusCubicLowerBound (r : ℝ) : ℝ :=
  let M : ℕ := ⌊r / 2⌋₊
  (M : ℝ) * ((M : ℝ) - 1) * (2 * (M : ℝ) - 1) / 3

/-- The intrinsic second-order pole count dominates the paper's real-radius
cubic comparison term. -/
theorem example55_realRadius_cubicLowerBound {r : ℝ} (hr : 0 ≤ r) :
    example55RealRadiusCubicLowerBound r ≤
      integratedCounting 2 r example55Composition := by
  let M : ℕ := ⌊r / 2⌋₊
  have hMle : (M : ℝ) ≤ r / 2 := by
    dsimp [M]
    exact Nat.floor_le (by positivity)
  have hMr : 2 * (M : ℝ) ≤ r := by linarith
  change (M : ℝ) * ((M : ℝ) - 1) * (2 * (M : ℝ) - 1) / 3 ≤ _
  exact (example55_evenRadius_cubicLowerBound M).trans
    (integratedCounting_mono_radius 2 (by positivity) hMr example55Composition)

/-- The arbitrary-real-radius comparison term is asymptotic to `r³/12`,
which is the precise `(1+o(1))` calculation printed in Example 5.5. -/
theorem example55_realRadius_cubicLowerBound_ratio_tendsto_one :
    Tendsto (fun r : ℝ ↦
      example55RealRadiusCubicLowerBound r / (r ^ 3 / 12))
      atTop (𝓝 1) := by
  have hhalfTop : Tendsto (fun r : ℝ ↦ r / 2) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id
  have hfloorHalf : Tendsto (fun r : ℝ ↦
      (⌊r / 2⌋₊ : ℝ) / (r / 2)) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp hhalfTop
  have hratio : Tendsto (fun r : ℝ ↦ (⌊r / 2⌋₊ : ℝ) / r)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := hfloorHalf.mul
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)))
    have heq :
        (fun r : ℝ ↦ (⌊r / 2⌋₊ : ℝ) / (r / 2) * (1 / 2)) =ᶠ[atTop]
          (fun r : ℝ ↦ (⌊r / 2⌋₊ : ℝ) / r) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      change (⌊r / 2⌋₊ : ℝ) / (r / 2) * (1 / 2) =
        (⌊r / 2⌋₊ : ℝ) / r
      field_simp [ne_of_gt hr]
    have h' := h.congr' heq
    simpa using h'
  have hinv : Tendsto (fun r : ℝ ↦ 1 / r) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop 1
  have hfour : Tendsto (fun _ : ℝ ↦ (4 : ℝ)) atTop (𝓝 4) :=
    tendsto_const_nhds
  have htwo : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) atTop (𝓝 2) :=
    tendsto_const_nhds
  have hlimit : Tendsto (fun r : ℝ ↦
      4 * ((⌊r / 2⌋₊ : ℝ) / r) *
        ((⌊r / 2⌋₊ : ℝ) / r - 1 / r) *
        (2 * ((⌊r / 2⌋₊ : ℝ) / r) - 1 / r)) atTop (𝓝 1) := by
    convert ((hfour.mul hratio).mul (hratio.sub hinv)).mul
      ((htwo.mul hratio).sub hinv) using 1 <;> norm_num
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  simp only [example55RealRadiusCubicLowerBound]
  field_simp
  ring

/-- The final conclusion of Example 5.5 on the original real-radius filter:
the curve characteristic is little-o of the intrinsic second-order pole
counting function of `P∘f`.  The proof implements the paper's
`M=⌊r/2⌋` comparison with explicit constants. -/
theorem example55_characteristic_isLittleO_integratedCounting :
    (fun r : ℝ ↦ cartanCharacteristic example55Curve r) =o[atTop]
      fun r : ℝ ↦ integratedCounting 2 r example55Composition := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  let R : ℝ := max 8 (384 / ε)
  filter_upwards [eventually_ge_atTop R] with r hrR
  have hr8 : 8 ≤ r := (le_max_left _ _).trans hrR
  have hrε : 384 / ε ≤ r := (le_max_right _ _).trans hrR
  have hr0 : 0 ≤ r := by linarith
  let M : ℕ := ⌊r / 2⌋₊
  have hMle : (M : ℝ) ≤ r / 2 := by
    dsimp [M]
    exact Nat.floor_le (by positivity)
  have hMr : 2 * (M : ℝ) ≤ r := by linarith
  have hrM : r / 2 < (M : ℝ) + 1 := by
    dsimp [M]
    simpa using Nat.lt_floor_add_one (r / 2)
  have hMlower : r / 4 ≤ (M : ℝ) := by linarith
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by linarith
  let L : ℝ :=
    (M : ℝ) * ((M : ℝ) - 1) * (2 * (M : ℝ) - 1) / 3
  have hL_M : (M : ℝ) ^ 3 / 6 ≤ L := by
    have hhalf : (M : ℝ) / 2 ≤ (M : ℝ) - 1 := by linarith
    have hlast : (M : ℝ) ≤ 2 * (M : ℝ) - 1 := by linarith
    have hprod :
        (M : ℝ) * ((M : ℝ) / 2) * (M : ℝ) ≤
          (M : ℝ) * ((M : ℝ) - 1) * (2 * (M : ℝ) - 1) := by
      gcongr
      exact mul_nonneg (by positivity) (by linarith)
    dsimp [L]
    nlinarith
  have hpow : (r / 4) ^ 3 ≤ (M : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hMlower 3
  have hLr : r ^ 3 / 384 ≤ L := by
    calc
      r ^ 3 / 384 = (r / 4) ^ 3 / 6 := by ring
      _ ≤ (M : ℝ) ^ 3 / 6 := by gcongr
      _ ≤ L := hL_M
  have hN : L ≤ integratedCounting 2 r example55Composition := by
    calc
      L ≤ integratedCounting 2 (2 * (M : ℝ)) example55Composition :=
        example55_evenRadius_cubicLowerBound M
      _ ≤ integratedCounting 2 r example55Composition :=
        integratedCounting_mono_radius 2 (by positivity) hMr example55Composition
  have herr := example55Curve_characteristic_error_bound hr0
  have hTupper : cartanCharacteristic example55Curve r ≤ r ^ 2 := by
    have hu := (abs_le.mp herr).2
    nlinarith [sq_nonneg r]
  have hTnonneg : 0 ≤ cartanCharacteristic example55Curve r := by
    have hl := (abs_le.mp herr).1
    nlinarith [sq_nonneg r]
  have hNnonneg : 0 ≤ integratedCounting 2 r example55Composition :=
    integratedCounting_nonneg 2 r example55Composition
  have hεr : 384 ≤ ε * r := by
    have := (div_le_iff₀ hε).mp hrε
    nlinarith
  have hrSq : r ^ 2 ≤ ε * (r ^ 3 / 384) := by
    have hmul := mul_le_mul_of_nonneg_right hεr (sq_nonneg r)
    nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hTnonneg,
    abs_of_nonneg hNnonneg]
  calc
    cartanCharacteristic example55Curve r ≤ r ^ 2 := hTupper
    _ ≤ ε * (r ^ 3 / 384) := hrSq
    _ ≤ ε * L := mul_le_mul_of_nonneg_left hLr hε.le
    _ ≤ ε * integratedCounting 2 r example55Composition :=
      mul_le_mul_of_nonneg_left hN hε.le

/-! ## The counterexample after Theorem 6.2 -/

/-- The three polynomial pieces of the displayed Casoratian
`C₀(f₀,f₁)`. -/
def section6CounterexampleCasoratianPiece (i : ℤ) : Polynomial ℝ :=
  if i ≤ -1 then -2 * Polynomial.X - 1
  else if i = 0 then 2 * Polynomial.X ^ 2 + 2 * Polynomial.X + 1
  else 2 * Polynomial.X + 1

theorem section6CounterexampleCasoratianPiece_degree (i : ℤ) :
    (section6CounterexampleCasoratianPiece i).natDegree ≤ 2 := by
  unfold section6CounterexampleCasoratianPiece
  split_ifs <;> compute_degree!

theorem section6CounterexampleCasoratianPiece_adjacent (i : ℤ) :
    (section6CounterexampleCasoratianPiece i).eval (i : ℝ) =
      (section6CounterexampleCasoratianPiece (i + 1)).eval (i : ℝ) := by
  by_cases hlow : i ≤ -2
  · have hi : i ≤ -1 := by omega
    have his : i + 1 ≤ -1 := by omega
    simp [section6CounterexampleCasoratianPiece, hi, his]
  · have hilow : -1 ≤ i := by omega
    by_cases hhigh : i ≤ 0
    · interval_cases i <;> norm_num [section6CounterexampleCasoratianPiece]
    · have hi : 1 ≤ i := by omega
      have hi1 : ¬i ≤ -1 := by omega
      have hi0 : i ≠ 0 := by omega
      have hs1 : ¬i + 1 ≤ -1 := by omega
      have hs0 : i + 1 ≠ 0 := by omega
      simp [section6CounterexampleCasoratianPiece, hi1, hi0, hs1, hs0]

/-- The explicit max-plus Casoratian from the paper's Section 6 example. -/
def section6CounterexampleCasoratian : NthTropicalMeromorphicFunction 2 :=
  assembleNthTropicalMeromorphicFunction (tropicalHyperExponentialGrid 2)
    section6CounterexampleCasoratianPiece
    section6CounterexampleCasoratianPiece_degree
    section6CounterexampleCasoratianPiece_adjacent
    ⟨0, by simp [section6CounterexampleCasoratianPiece]; compute_degree!⟩

private def section6CounterexampleCasoratianPresentation :
    PolynomialPresentation 2 section6CounterexampleCasoratian :=
  assembledPolynomialPresentation (tropicalHyperExponentialGrid 2)
    section6CounterexampleCasoratianPiece
    section6CounterexampleCasoratianPiece_degree
    section6CounterexampleCasoratianPiece_adjacent
    ⟨0, by simp [section6CounterexampleCasoratianPiece]; compute_degree!⟩

private theorem section6CounterexampleCasoratian_cut_multiplicity_one (i : ℤ) :
    presentationMultiplicityAtCutPoint
      section6CounterexampleCasoratianPresentation 1 i = 0 := by
  by_cases hlow : i ≤ -2
  · have hi : i ≤ -1 := by omega
    have his : i + 1 ≤ -1 := by omega
    norm_num [presentationMultiplicityAtCutPoint,
      section6CounterexampleCasoratianPresentation,
      assembledPolynomialPresentation, tropicalHyperExponentialGrid,
      section6CounterexampleCasoratianPiece, hi, his,
      normalizedPolynomialJet, rightSign, leftSign]
  · have hilow : -1 ≤ i := by omega
    by_cases hhigh : i ≤ 0
    · interval_cases i <;>
        norm_num [presentationMultiplicityAtCutPoint,
          section6CounterexampleCasoratianPresentation,
          assembledPolynomialPresentation, tropicalHyperExponentialGrid,
          section6CounterexampleCasoratianPiece,
          normalizedPolynomialJet, rightSign, leftSign]
    · have hi : 1 ≤ i := by omega
      have hi1 : ¬i ≤ -1 := by omega
      have hi0 : i ≠ 0 := by omega
      have hs1 : ¬i + 1 ≤ -1 := by omega
      have hs0 : i + 1 ≠ 0 := by omega
      norm_num [presentationMultiplicityAtCutPoint,
        section6CounterexampleCasoratianPresentation,
        assembledPolynomialPresentation, tropicalHyperExponentialGrid,
        section6CounterexampleCasoratianPiece, hi1, hi0, hs1, hs0,
        normalizedPolynomialJet, rightSign, leftSign]

private theorem section6CounterexampleCasoratian_cut_multiplicity_two (i : ℤ) :
    presentationMultiplicityAtCutPoint
      section6CounterexampleCasoratianPresentation 2 i =
        if i = -1 then -2 else if i = 0 then 2 else 0 := by
  by_cases hlow : i ≤ -2
  · have hi : i ≤ -1 := by omega
    have his : i + 1 ≤ -1 := by omega
    have him1 : i ≠ -1 := by omega
    have hi0 : i ≠ 0 := by omega
    norm_num [presentationMultiplicityAtCutPoint,
      section6CounterexampleCasoratianPresentation,
      assembledPolynomialPresentation, tropicalHyperExponentialGrid,
      section6CounterexampleCasoratianPiece, hi, his, him1, hi0,
      normalizedPolynomialJet_eq_iterateDerivative_div,
      Function.iterate_succ_apply, Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_pow, rightSign, leftSign]
  · have hilow : -1 ≤ i := by omega
    by_cases hhigh : i ≤ 0
    · interval_cases i <;>
        norm_num [presentationMultiplicityAtCutPoint,
          section6CounterexampleCasoratianPresentation,
          assembledPolynomialPresentation, tropicalHyperExponentialGrid,
          section6CounterexampleCasoratianPiece,
          normalizedPolynomialJet_eq_iterateDerivative_div,
          Function.iterate_succ_apply, Polynomial.derivative_add,
          Polynomial.derivative_sub, Polynomial.derivative_mul,
          Polynomial.derivative_pow, rightSign, leftSign]
    · have hi : 1 ≤ i := by omega
      have hi1 : ¬i ≤ -1 := by omega
      have hi0 : i ≠ 0 := by omega
      have him1 : i ≠ -1 := by omega
      have hs1 : ¬i + 1 ≤ -1 := by omega
      have hs0 : i + 1 ≠ 0 := by omega
      norm_num [presentationMultiplicityAtCutPoint,
        section6CounterexampleCasoratianPresentation,
        assembledPolynomialPresentation, tropicalHyperExponentialGrid,
        section6CounterexampleCasoratianPiece, hi1, hi0, him1, hs1, hs0,
        normalizedPolynomialJet_eq_iterateDerivative_div,
        Function.iterate_succ_apply, Polynomial.derivative_add,
        Polynomial.derivative_sub, Polynomial.derivative_mul,
        Polynomial.derivative_pow, rightSign, leftSign]

theorem section6CounterexampleCasoratian_multiplicity_one (x : ℝ) :
    multiplicity section6CounterexampleCasoratian 1 x = 0 := by
  rcases multiplicity_eq_zero_or_cutPoint_of_presentation
      section6CounterexampleCasoratian
      section6CounterexampleCasoratianPresentation 1 x with
    hzero | ⟨i, hxi, hmul⟩
  · exact hzero
  · rw [hmul, section6CounterexampleCasoratian_cut_multiplicity_one]

theorem section6CounterexampleCasoratian_multiplicity_two (x : ℝ) :
    multiplicity section6CounterexampleCasoratian 2 x =
      if x = -1 then -2 else if x = 0 then 2 else 0 := by
  rcases multiplicity_eq_zero_or_cutPoint_of_presentation
      section6CounterexampleCasoratian
      section6CounterexampleCasoratianPresentation 2 x with
    hzero | ⟨i, hxi, hmul⟩
  · rw [hzero]
    by_cases hx1 : x = -1
    · subst x
      exfalso
      have := hzero
      have hcut : section6CounterexampleCasoratianPresentation.cutPoint (-1) = -1 := by
        simp [section6CounterexampleCasoratianPresentation,
          assembledPolynomialPresentation, tropicalHyperExponentialGrid]
      rw [← hcut, multiplicity_cutPoint_of_presentation,
        section6CounterexampleCasoratian_cut_multiplicity_two] at this
      norm_num at this
    · by_cases hx0 : x = 0
      · subst x
        exfalso
        have hcut : section6CounterexampleCasoratianPresentation.cutPoint 0 = 0 := by
          simp [section6CounterexampleCasoratianPresentation,
            assembledPolynomialPresentation, tropicalHyperExponentialGrid]
        have hactual := multiplicity_cutPoint_of_presentation
          section6CounterexampleCasoratian
          section6CounterexampleCasoratianPresentation 2 0
        rw [section6CounterexampleCasoratian_cut_multiplicity_two, hcut] at hactual
        norm_num at hactual
        linarith
      · simp [hx1, hx0]
  · have hxcast : x = (i : ℝ) := by
      simpa [section6CounterexampleCasoratianPresentation,
        assembledPolynomialPresentation, tropicalHyperExponentialGrid] using hxi
    rw [hmul, section6CounterexampleCasoratian_cut_multiplicity_two]
    rw [hxcast]
    norm_cast

theorem section6CounterexampleCasoratian_reciprocalCounting
    {r : ℝ} (hr : 0 < r) :
    ambientReciprocalCounting 2 r section6CounterexampleCasoratian = r ^ 2 := by
  have hpoles1 : jthPolePoints (-section6CounterexampleCasoratian) 1 r = ∅ := by
    classical
    rw [Finset.eq_empty_iff_forall_notMem]
    intro y hy
    rw [mem_jthPolePoints_iff, IsJthPole, multiplicity_neg,
      section6CounterexampleCasoratian_multiplicity_one] at hy
    linarith [hy.2]
  have hpoles2 : jthPolePoints (-section6CounterexampleCasoratian) 2 r = {0} := by
    classical
    ext y
    rw [mem_jthPolePoints_iff]
    simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨hyr, hpole⟩
      rw [IsJthPole, multiplicity_neg,
        section6CounterexampleCasoratian_multiplicity_two] at hpole
      by_cases hy1 : y = -1
      · norm_num [hy1] at hpole
      · by_cases hy0 : y = 0
        · exact hy0
        · norm_num [hy1, hy0] at hpole
    · intro hy0
      subst y
      constructor
      · simp [hr]
      · simp [IsJthPole,
          section6CounterexampleCasoratian_multiplicity_two]
  have hN1 : integratedCounting 1 r (-section6CounterexampleCasoratian) = 0 := by
    simp [integratedCounting, hpoles1]
  have hN2 : integratedCounting 2 r (-section6CounterexampleCasoratian) = r ^ 2 := by
    rw [integratedCounting, hpoles2]
    simp [rootOrPoleMultiplicity,
      section6CounterexampleCasoratian_multiplicity_two]
  rw [ambientReciprocalCounting,
    show Finset.Icc 1 2 = {1, 2} by decide]
  norm_num only [Finset.sum_insert, Finset.mem_singleton, Finset.sum_singleton]
  rw [hN1, hN2]
  simp

/-- The paper's curve `[f₀:f₁]`, with `f₁=-f₀`. -/
def section6CounterexampleCurve : TropicalHolomorphicCurveRepresentation 2 1 where
  order := fun _ ↦ 2
  order_le := by simp
  order_attained := ⟨0, rfl⟩
  coordinate := fun i ↦ if i = 0 then example21SignedQuadratic
    else -example21SignedQuadratic
  coordinate_multiplicity_nonneg := by
    intro i x j hj1 hj2
    fin_cases i <;> interval_cases j <;>
      simp [example21SignedQuadratic_multiplicity_one,
        example21SignedQuadratic_multiplicity_two]

theorem section6CounterexampleCurve_coordinateMaximum (x : ℝ) :
    curveCoordinateMaximum section6CounterexampleCurve x = x ^ 2 := by
  have hsq : 0 ≤ x ^ 2 := sq_nonneg x
  unfold curveCoordinateMaximum TropicalHolomorphicCurveRepresentation.eval
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
    intro i hi
    fin_cases i <;> by_cases hx : x ≤ 0 <;>
      simp [section6CounterexampleCurve, example21SignedQuadratic_apply, hx, hsq]
  · by_cases hx : x ≤ 0
    · have hcoordinate := Finset.le_sup'
        (fun i : Fin 2 ↦ (section6CounterexampleCurve.coordinate i) x)
        (Finset.mem_univ (1 : Fin 2))
      simpa [section6CounterexampleCurve,
        example21SignedQuadratic_apply, hx] using hcoordinate
    · have hcoordinate := Finset.le_sup'
        (fun i : Fin 2 ↦ (section6CounterexampleCurve.coordinate i) x)
        (Finset.mem_univ (0 : Fin 2))
      simpa [section6CounterexampleCurve,
        example21SignedQuadratic_apply, hx] using hcoordinate

theorem section6CounterexampleCurve_characteristic (r : ℝ) :
    cartanCharacteristic section6CounterexampleCurve r = r ^ 2 := by
  simp [cartanCharacteristic,
    section6CounterexampleCurve_coordinateMaximum]

private theorem section6CounterexampleCurve_negCoordinate_entire (i : Fin 2) :
    IsTropicalEntire (-section6CounterexampleCurve.coordinate i) := by
  rw [isTropicalEntire_iff_multiplicity_nonneg]
  intro x j hj1 hj2
  have hzero : multiplicity example21SignedQuadratic j x = 0 := by
    have hj2' : j ≤ 2 := by
      simpa [section6CounterexampleCurve] using hj2
    interval_cases j
    · exact example21SignedQuadratic_multiplicity_one x
    · exact example21SignedQuadratic_multiplicity_two x
  fin_cases i
  · change 0 ≤ multiplicity (-example21SignedQuadratic) j x
    rw [multiplicity_neg, hzero]
    simp
  · change 0 ≤ multiplicity (-(-example21SignedQuadratic)) j x
    rw [multiplicity_neg, multiplicity_neg, hzero]
    simp

theorem section6CounterexampleCurve_coordinate_reciprocalCounting
    (i : Fin 2) (r : ℝ) :
    ambientReciprocalCounting 2 r (section6CounterexampleCurve.coordinate i) = 0 := by
  have hN1 := integratedCounting_eq_zero_of_entire_any_order
    (-section6CounterexampleCurve.coordinate i)
    (section6CounterexampleCurve_negCoordinate_entire i)
    (j := 1) (by norm_num) r
  have hN2 := integratedCounting_eq_zero_of_entire_any_order
    (-section6CounterexampleCurve.coordinate i)
    (section6CounterexampleCurve_negCoordinate_entire i)
    (j := 2) (by norm_num) r
  unfold ambientReciprocalCounting
  rw [show Finset.Icc 1 2 = {1, 2} by decide]
  norm_num only [Finset.sum_insert, Finset.mem_singleton, Finset.sum_singleton]
  rw [hN1, hN2]
  simp

/-- Exact obstruction asserted by the example after Theorem 6.2.  The paper
prints `∑ i=0²` although the displayed curve has only two coordinates; the
formal statement uses the mathematically typed sum over `Fin 2`. -/
theorem section6Counterexample_exact_obstruction {r : ℝ} (hr : 0 < r) :
    cartanCharacteristic section6CounterexampleCurve r = r ^ 2 ∧
      (∑ i : Fin 2,
        ambientReciprocalCounting 2 r
          (section6CounterexampleCurve.coordinate i)) = 0 ∧
      ambientReciprocalCounting 2 r section6CounterexampleCasoratian = r ^ 2 := by
  refine ⟨section6CounterexampleCurve_characteristic r, ?_,
    section6CounterexampleCasoratian_reciprocalCounting hr⟩
  simp [section6CounterexampleCurve_coordinate_reciprocalCounting]

/-! ## The growth hypothesis after Corollary 6.3 cannot be dropped -/

/-- The first-order hyper-exponential in the example after Corollary 6.3. -/
def corollary63HyperExponential (α : ℝ) (hα : 1 < α) :
    NthTropicalMeromorphicFunction 1 :=
  tropicalHyperExponential 1 α (by norm_num) hα

/-- The two homogeneous coordinates `[0:e_α]` from the example after
Corollary 6.3. -/
def corollary63Coordinates (α : ℝ) (hα : 1 < α) : Fin 2 → ℝ → ℝ :=
  fun i ↦ if i = 0 then (fun _ ↦ 0) else corollary63HyperExponential α hα

@[simp] theorem corollary63Coordinates_zero
    {α : ℝ} (hα : 1 < α) :
    corollary63Coordinates α hα 0 = (fun _ ↦ 0) := by
  simp [corollary63Coordinates]

@[simp] theorem corollary63Coordinates_one
    {α : ℝ} (hα : 1 < α) :
    corollary63Coordinates α hα 1 = corollary63HyperExponential α hα := by
  simp [corollary63Coordinates]

/-- The raw tropical Casoratian of `[0:e_α]` is exactly
`e_α(x+1)=αe_α(x)`.  Thus the later bundled realization is connected to
the project's actual `tropicalCasoratian`, rather than merely assigned the
same displayed formula. -/
theorem corollary63_tropicalCasoratian_eq_scaled
    {α : ℝ} (hα : 1 < α) (x : ℝ) :
    tropicalCasoratian (corollary63Coordinates α hα) x =
      α * corollary63HyperExponential α hα x := by
  classical
  apply le_antisymm
  · unfold tropicalCasoratian
    apply Finset.sup'_le Finset.univ_nonempty
    intro π _hπ
    rw [Fin.sum_univ_two]
    have hcases : (π 1).val = 0 ∨ (π 1).val = 1 := by omega
    rcases hcases with hzero | hone
    · have hπ1 : π 1 = 0 := Fin.ext hzero
      simp [hπ1, forwardShift]
      have hnonneg : 0 ≤ corollary63HyperExponential α hα x := by
        simpa [corollary63HyperExponential] using
          tropicalHyperExponential_nonneg 1 hα (by norm_num) x
      nlinarith [mul_nonneg (sub_nonneg.mpr hα.le) hnonneg]
    · have hπ1 : π 1 = 1 := Fin.ext hone
      simpa [hπ1, forwardShift, corollary63HyperExponential] using
        (tropicalHyperExponential_one_shift hα x).le
  · calc
      α * corollary63HyperExponential α hα x =
          ∑ i : Fin 2,
            forwardShift (corollary63Coordinates α hα i) i x := by
        rw [Fin.sum_univ_two]
        simpa [forwardShift, corollary63HyperExponential] using
          (tropicalHyperExponential_one_shift hα x).symm
      _ ≤ tropicalCasoratian (corollary63Coordinates α hα) x :=
        diagonalShiftSum_le_tropicalCasoratian _ _

/-- A concrete realization of the Casoratian in that example.  The theorem
below identifies it pointwise with the unit shift, so this definition does
not assume the claimed scaling relation. -/
def corollary63CasoratianRealization (α : ℝ) (hα : 1 < α) :=
  smulRealization α (corollary63HyperExponential α hα)

def corollary63Casoratian (α : ℝ) (hα : 1 < α) :
    NthTropicalMeromorphicFunction
      (corollary63CasoratianRealization α hα).order :=
  (corollary63CasoratianRealization α hα).function

@[simp] theorem corollary63Casoratian_apply
    {α : ℝ} (hα : 1 < α) (x : ℝ) :
    corollary63Casoratian α hα x =
      α * corollary63HyperExponential α hα x :=
  (corollary63CasoratianRealization α hα).eq_fun x

/-- The actual tropical Casoratian and its bundled meromorphic realization
agree pointwise. -/
theorem corollary63_tropicalCasoratian_eq_bundled
    {α : ℝ} (hα : 1 < α) (x : ℝ) :
    tropicalCasoratian (corollary63Coordinates α hα) x =
      corollary63Casoratian α hα x := by
  rw [corollary63_tropicalCasoratian_eq_scaled,
    corollary63Casoratian_apply]

/-- The Casoratian realization is exactly the unit forward shift occurring
in the paper, by the newly proved functional equation `e_α(x+1)=αe_α(x)`. -/
theorem corollary63Casoratian_eq_forwardShift
    {α : ℝ} (hα : 1 < α) (x : ℝ) :
    corollary63Casoratian α hα x =
      forwardShift (corollary63HyperExponential α hα) 1 x := by
  rw [corollary63Casoratian_apply]
  simpa [corollary63HyperExponential, forwardShift] using
    (tropicalHyperExponential_one_shift hα x).symm

/-- For the entire source, Jensen gives the reciprocal count exactly as its
characteristic minus the fixed central value; no asymptotic notation is
needed. -/
theorem corollary63_sourceReciprocalCounting_exact
    {α : ℝ} (hα : 1 < α) {r : ℝ} (hr : 0 < r) :
    ambientReciprocalCounting 1 r (corollary63HyperExponential α hα) =
      characteristic r (corollary63HyperExponential α hα) -
        corollary63HyperExponential α hα 0 := by
  let e := corollary63HyperExponential α hα
  have hsigned := ambientSignedCountingDifference_eq_endpointMean_sub e le_rfl hr
  have hpole : integratedCounting 1 r e = 0 :=
    integratedCounting_eq_zero_of_entire_any_order e
      (tropicalHyperExponential_isTropicalEntire 1 hα (by norm_num))
      (by norm_num) r
  have hchar : characteristic r e = (e r + e (-r)) / 2 := by
    simpa [e, corollary63HyperExponential] using
      (characteristic_tropicalHyperExponential 1 hα (by norm_num) r)
  simp only [ambientSignedCountingDifference, ambientReciprocalCounting,
    ambientPoleCounting] at hsigned ⊢
  norm_num at hsigned ⊢
  change integratedRootCounting 1 r e = characteristic r e - e 0
  change integratedRootCounting 1 r e - integratedCounting 1 r e =
    (e r + e (-r)) / 2 - e 0 at hsigned
  rw [hpole, sub_zero, ← hchar] at hsigned
  exact hsigned

/-- Positive scalar multiplication pulls exactly out of the reciprocal
count.  Combined with the preceding theorem, this is stronger than both
`(1+o(1))` assertions printed after Corollary 6.3. -/
theorem corollary63_CasoratianReciprocalCounting_exact
    {α : ℝ} (hα : 1 < α) (r : ℝ) :
    ambientReciprocalCounting 1 r (corollary63Casoratian α hα) =
      α * ambientReciprocalCounting 1 r
        (corollary63HyperExponential α hα) := by
  have hαpos : 0 < α := lt_trans zero_lt_one hα
  have hscale := integratedCounting_smul
    (-(corollary63Casoratian α hα))
    (-(corollary63HyperExponential α hα)) α hαpos
    (fun x ↦ by simp [corollary63Casoratian_apply hα]) 1 r
  simpa [ambientReciprocalCounting] using hscale

/-- The first `(1+o(1))` assertion in the paper, now stated with Mathlib's
standard asymptotic equivalence relation. -/
theorem corollary63_sourceReciprocalCounting_isEquivalent_characteristic
    {α : ℝ} (hα : 1 < α) :
    Asymptotics.IsEquivalent atTop
      (fun r ↦ ambientReciprocalCounting 1 r
        (corollary63HyperExponential α hα))
      (fun r ↦ characteristic r (corollary63HyperExponential α hα)) := by
  let e := corollary63HyperExponential α hα
  have hT : Tendsto (fun r ↦ characteristic r e) atTop atTop := by
    simpa [e, corollary63HyperExponential] using
      (characteristic_tropicalHyperExponential_tendsto_atTop 1 hα (by norm_num))
  have hnorm : Tendsto (norm ∘ fun r ↦ characteristic r e) atTop atTop := by
    apply hT.congr'
    exact Eventually.of_forall fun r ↦ by
      simp [Function.comp_def, Real.norm_eq_abs,
        abs_of_nonneg (characteristic_nonneg r e)]
  have hequiv : Asymptotics.IsEquivalent atTop
      (fun r ↦ characteristic r e - e 0)
      (fun r ↦ characteristic r e) := by
    simpa [sub_eq_add_neg] using
      (Asymptotics.IsEquivalent.refl.add_const_of_norm_tendsto_atTop
        hnorm (c := -(e 0)))
  apply hequiv.congr_left
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  simpa [e] using (corollary63_sourceReciprocalCounting_exact hα hr).symm

/-- The second `(1+o(1))` assertion: the Casoratian reciprocal count is
asymptotic to `α T(r,e_α)`. -/
theorem corollary63_CasoratianReciprocalCounting_isEquivalent_scaledCharacteristic
    {α : ℝ} (hα : 1 < α) :
    Asymptotics.IsEquivalent atTop
      (fun r ↦ ambientReciprocalCounting 1 r
        (corollary63Casoratian α hα))
      (fun r ↦ α * characteristic r (corollary63HyperExponential α hα)) := by
  have hsource :=
    corollary63_sourceReciprocalCounting_isEquivalent_characteristic hα
  have hconst : Asymptotics.IsEquivalent atTop
      (fun _ : ℝ ↦ α) (fun _ : ℝ ↦ α) :=
    Asymptotics.IsEquivalent.refl
  have hscaled := hconst.mul hsource
  apply hscaled.congr_left
  exact Eventually.of_forall fun r ↦ by
    simpa using (corollary63_CasoratianReciprocalCounting_exact hα r).symm

/-- The hyper-exponential used after Corollary 6.3 violates the strict
hyper-order hypothesis. -/
theorem corollary63_growthHypothesis_counterexample
    {α : ℝ} (hα : 1 < α) :
    hyperOrder (tropicalHyperExponential 1 α (by norm_num) hα) = (1 : EReal) ∧
      ¬ hyperOrder (tropicalHyperExponential 1 α (by norm_num) hα) < (1 : EReal) := by
  have horder := tropicalHyperExponential_hyperOrder 1 hα (by norm_num)
  exact ⟨horder, by rw [horder]; exact lt_irrefl _⟩

end

end NthTropicalNevanlinna
