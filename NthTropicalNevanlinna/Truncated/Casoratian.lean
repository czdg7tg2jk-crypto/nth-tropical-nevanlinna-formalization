import NthTropicalNevanlinna.Function.Entire
import NthTropicalNevanlinna.Function.PresentationClosure
import NthTropicalNevanlinna.Function.FirstOrderConvexity
import NthTropicalNevanlinna.Function.TranslationMultiplicity

/-!
# Shifts and the tropical Casoratian

This file formalizes the max-plus Casoratian and proves Lemma 6.1.  The
entirety assumptions in the paper are not needed for the algebraic identity;
they are retained in `casoratian_commonFactor_of_entire` as the paper-facing
interface.
-/

namespace NthTropicalNevanlinna

noncomputable section

open scoped BigOperators

/-- The forward shift `\bar f^[k](x) = f(x+k)`. -/
def forwardShift (f : ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  f (x + k)

/-- A forward shift has an automatically constructed global polynomial
presentation under the same ambient order bound. -/
def forwardShiftRealization {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (k : ℕ) :
    NthTropicalMeromorphicRealization n
      (fun x ↦ forwardShift (fun y ↦ f y) k x) := by
  simpa [forwardShift] using translateRealization f (k : ℝ)

/-- Odd-order radial multiplicity is transported exactly by a forward
shift. -/
theorem multiplicity_forwardShiftRealization_of_odd
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (k : ℕ)
    {j : ℕ} (hj : Odd j) (x : ℝ) :
    multiplicity (forwardShiftRealization f k).function j x =
      multiplicity f j (x + k) := by
  simpa [forwardShiftRealization] using
    multiplicity_translateRealization_of_odd f (k : ℝ) hj x

/-- Forward-shift multiplicity is transported exactly when both the shifted
point and its source are positive. -/
theorem multiplicity_forwardShiftRealization_of_pos
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (k : ℕ)
    (j : ℕ) {x : ℝ} (hx : 0 < x) (hxk : 0 < x + k) :
    multiplicity (forwardShiftRealization f k).function j x =
      multiplicity f j (x + k) := by
  simpa [forwardShiftRealization] using
    multiplicity_translateRealization_of_pos f (k : ℝ) j hx hxk

/-- Forward-shift multiplicity is transported exactly when both the shifted
point and its source are negative. -/
theorem multiplicity_forwardShiftRealization_of_neg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (k : ℕ)
    (j : ℕ) {x : ℝ} (hx : x < 0) (hxk : x + k < 0) :
    multiplicity (forwardShiftRealization f k).function j x =
      multiplicity f j (x + k) := by
  simpa [forwardShiftRealization] using
    multiplicity_translateRealization_of_neg f (k : ℝ) j hx hxk

/-- Odd-order roots of a forward shift correspond exactly to roots of the
source at the translated point. -/
theorem isJthRoot_forwardShiftRealization_of_odd
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (k : ℕ)
    {j : ℕ} (hj : Odd j) (x : ℝ) :
    IsJthRoot (forwardShiftRealization f k).function j x ↔
      IsJthRoot f j (x + k) := by
  simpa [forwardShiftRealization] using
    isJthRoot_translateRealization_of_odd f (k : ℝ) hj x

/-- Odd-order unsigned multiplicities are transported exactly by a forward
shift. -/
theorem rootOrPoleMultiplicity_forwardShiftRealization_of_odd
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (k : ℕ)
    {j : ℕ} (hj : Odd j) (x : ℝ) :
    rootOrPoleMultiplicity (forwardShiftRealization f k).function j x =
      rootOrPoleMultiplicity f j (x + k) := by
  simpa [forwardShiftRealization] using
    rootOrPoleMultiplicity_translateRealization_of_odd f (k : ℝ) hj x

/-- Same-sign unsigned multiplicities are transported exactly by a forward
shift. -/
theorem rootOrPoleMultiplicity_forwardShiftRealization_of_sameSign
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (k : ℕ)
    (j : ℕ) {x : ℝ}
    (h : (0 < x ∧ 0 < x + k) ∨ (x < 0 ∧ x + k < 0)) :
    rootOrPoleMultiplicity (forwardShiftRealization f k).function j x =
      rootOrPoleMultiplicity f j (x + k) := by
  simpa [forwardShiftRealization] using
    rootOrPoleMultiplicity_translateRealization_of_sameSign
      f (k : ℝ) j h

/-- At same-sign source/target points, forward shift transports the root
predicate exactly in every order. -/
theorem isJthRoot_forwardShiftRealization_of_sameSign
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (k : ℕ)
    (j : ℕ) {x : ℝ}
    (h : (0 < x ∧ 0 < x + k) ∨ (x < 0 ∧ x + k < 0)) :
    IsJthRoot (forwardShiftRealization f k).function j x ↔
      IsJthRoot f j (x + k) := by
  unfold IsJthRoot
  rcases h with h | h
  · rw [multiplicity_forwardShiftRealization_of_pos f k j h.1 h.2]
  · rw [multiplicity_forwardShiftRealization_of_neg f k j h.1 h.2]

/-- First-order entire functions remain entire after a forward shift. -/
theorem forwardShiftRealization_isTropicalEntire
    {q : ℕ} (f : NthTropicalMeromorphicFunction q) (hq : q ≤ 1)
    (hf : IsTropicalEntire f) (k : ℕ) :
    IsTropicalEntire (forwardShiftRealization f k).function := by
  simpa [forwardShiftRealization] using
    translateRealization_isTropicalEntire f hq hf (k : ℝ)

/-- The tropical product of real-valued functions, i.e. pointwise addition. -/
def tropicalTensor (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x + g x

@[simp]
theorem forwardShift_tropicalTensor (f g : ℝ → ℝ) (k : ℕ) (x : ℝ) :
    forwardShift (tropicalTensor f g) k x =
      forwardShift f k x + forwardShift g k x := by
  rfl

/-- The tropical Casoratian `C₀(f₀,…,fₘ)`. -/
def tropicalCasoratian {m : ℕ} (f : Fin (m + 1) → ℝ → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun π : Equiv.Perm (Fin (m + 1)) ↦
    ∑ i, forwardShift (f i) (π i) x

/-- A finite majorant for the change from the diagonal shifts to an
arbitrary permutation of the shifts. -/
def casoratianPairwiseShiftVariation {m : ℕ}
    (f : Fin (m + 1) → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin (m + 1), ∑ k : Fin (m + 1),
    |forwardShift (f i) k x - forwardShift (f i) i x|

/-- The diagonal permutation is one of the terms in the tropical
Casoratian. -/
theorem diagonalShiftSum_le_tropicalCasoratian {m : ℕ}
    (f : Fin (m + 1) → ℝ → ℝ) (x : ℝ) :
    (∑ i : Fin (m + 1), forwardShift (f i) i x) ≤
      tropicalCasoratian f x := by
  classical
  unfold tropicalCasoratian
  simpa using
    (Finset.le_sup'
      (fun π : Equiv.Perm (Fin (m + 1)) ↦
        ∑ i : Fin (m + 1), forwardShift (f i) (π i) x)
      (Finset.mem_univ (Equiv.refl (Fin (m + 1)))))

/-- Every permutation summand differs from the diagonal summand by at most
the sum of all pairwise coordinate-shift variations. -/
theorem permutationShiftSum_sub_diagonal_le_pairwiseVariation {m : ℕ}
    (f : Fin (m + 1) → ℝ → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) (x : ℝ) :
    (∑ i : Fin (m + 1), forwardShift (f i) (π i) x) -
        (∑ i : Fin (m + 1), forwardShift (f i) i x) ≤
      casoratianPairwiseShiftVariation f x := by
  classical
  rw [← Finset.sum_sub_distrib]
  unfold casoratianPairwiseShiftVariation
  apply Finset.sum_le_sum
  intro i _hi
  calc
    forwardShift (f i) (π i) x - forwardShift (f i) i x ≤
        |forwardShift (f i) (π i) x - forwardShift (f i) i x| :=
      le_abs_self _
    _ ≤ ∑ k : Fin (m + 1),
        |forwardShift (f i) k x - forwardShift (f i) i x| :=
      Finset.single_le_sum
        (f := fun k : Fin (m + 1) ↦
          |forwardShift (f i) k x - forwardShift (f i) i x|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ (π i))

/-- Exact finite maximum estimate used in `(equa2)`: no choice of a
maximizing permutation has to be exposed. -/
theorem abs_tropicalCasoratian_sub_diagonal_le_pairwiseVariation {m : ℕ}
    (f : Fin (m + 1) → ℝ → ℝ) (x : ℝ) :
    |tropicalCasoratian f x -
        ∑ i : Fin (m + 1), forwardShift (f i) i x| ≤
      casoratianPairwiseShiftVariation f x := by
  classical
  have hnonneg :
      0 ≤ tropicalCasoratian f x -
        ∑ i : Fin (m + 1), forwardShift (f i) i x :=
    sub_nonneg.mpr (diagonalShiftSum_le_tropicalCasoratian f x)
  rw [abs_of_nonneg hnonneg]
  unfold tropicalCasoratian
  have hsup :
      (Finset.univ : Finset (Equiv.Perm (Fin (m + 1)))).sup'
          Finset.univ_nonempty
          (fun π ↦ ∑ i : Fin (m + 1), forwardShift (f i) (π i) x) ≤
        (∑ i : Fin (m + 1), forwardShift (f i) i x) +
          casoratianPairwiseShiftVariation f x := by
    apply Finset.sup'_le Finset.univ_nonempty
    intro π _hπ
    linarith [permutationShiftSum_sub_diagonal_le_pairwiseVariation f π x]
  linarith

private theorem sum_forwardShift_comp_perm {m : ℕ}
    (g : ℝ → ℝ) (x : ℝ) (π : Equiv.Perm (Fin (m + 1))) :
    (∑ i : Fin (m + 1), forwardShift g (π i) x) =
      ∑ i : Fin (m + 1), forwardShift g i x := by
  simpa [forwardShift] using
    Equiv.sum_comp π (fun i : Fin (m + 1) ↦ g (x + (i : ℕ)))

/-- Algebraic core of Lemma 6.1: a common tropical factor can be pulled out
of the Casoratian together with all its shifts. -/
theorem tropicalCasoratian_commonFactor {m : ℕ}
    (f : Fin (m + 1) → ℝ → ℝ) (g : ℝ → ℝ) (x : ℝ) :
    tropicalCasoratian (fun i ↦ tropicalTensor (f i) g) x =
      (∑ k : Fin (m + 1), forwardShift g k x) + tropicalCasoratian f x := by
  classical
  unfold tropicalCasoratian
  simp_rw [forwardShift_tropicalTensor, Finset.sum_add_distrib,
    sum_forwardShift_comp_perm g x]
  let c : ℝ := ∑ k : Fin (m + 1), forwardShift g k x
  have h := (Finset.sup'_add
    (Finset.univ : Finset (Equiv.Perm (Fin (m + 1))))
    (fun π ↦ ∑ i : Fin (m + 1), forwardShift (f i) (π i) x)
    c Finset.univ_nonempty).symm
  simpa [c, add_comm] using h

/-- Subtracting the diagonal shift sum removes a common tropical factor
from the Casoratian exactly. -/
theorem tropicalCasoratian_sub_diagonal_commonFactor {m : ℕ}
    (f : Fin (m + 1) → ℝ → ℝ) (g : ℝ → ℝ) (x : ℝ) :
    tropicalCasoratian (fun i ↦ tropicalTensor (f i) g) x -
        ∑ i : Fin (m + 1),
          forwardShift (tropicalTensor (f i) g) i x =
      tropicalCasoratian f x -
        ∑ i : Fin (m + 1), forwardShift (f i) i x := by
  rw [tropicalCasoratian_commonFactor]
  simp_rw [forwardShift_tropicalTensor, Finset.sum_add_distrib]
  have hcommon :
      (∑ i : Fin (m + 1), forwardShift g i x) =
        ∑ i : Fin (m + 1), forwardShift g i x := rfl
  rw [hcommon]
  ring

/-- Projective form of the preceding identity.  If `qᵢ=fᵢ-g`, the
Casoratian-minus-diagonal expression can be computed entirely from the
quotients `qᵢ`. -/
theorem tropicalCasoratian_sub_diagonal_eq_of_referenceQuotients {m : ℕ}
    (f q : Fin (m + 1) → ℝ → ℝ) (g : ℝ → ℝ)
    (hquotient : ∀ i x, q i x = f i x - g x) (x : ℝ) :
    tropicalCasoratian f x -
        ∑ i : Fin (m + 1), forwardShift (f i) i x =
      tropicalCasoratian q x -
        ∑ i : Fin (m + 1), forwardShift (q i) i x := by
  have hfactor :
      f = fun i ↦ tropicalTensor (q i) g := by
    funext i y
    dsimp [tropicalTensor]
    rw [hquotient]
    ring
  rw [hfactor]
  exact tropicalCasoratian_sub_diagonal_commonFactor q g x

/-- If every shifted coordinate changes by an amount independent of the
permutation, then the Casoratian changes by the sum of those amounts. -/
theorem tropicalCasoratian_eq_add_of_coordinateShift {m : ℕ}
    (f : Fin (m + 1) → ℝ → ℝ) (a : Fin (m + 1) → ℝ) (x y : ℝ)
    (h : ∀ i (k : Fin (m + 1)),
      f i (y + (k : ℕ)) = f i (x + (k : ℕ)) + a i) :
    tropicalCasoratian f y = (∑ i, a i) + tropicalCasoratian f x := by
  classical
  unfold tropicalCasoratian forwardShift
  simp_rw [h, Finset.sum_add_distrib]
  let c : ℝ := ∑ i, a i
  have hsup := (Finset.sup'_add
    (Finset.univ : Finset (Equiv.Perm (Fin (m + 1))))
    (fun π ↦ ∑ i : Fin (m + 1), f i (x + ((π i : Fin (m + 1)) : ℕ)))
    c Finset.univ_nonempty).symm
  simpa [c, add_comm] using hsup

/-- Lemma 6.1 in the paper's quantifiers.  The hypotheses record that all
functions are `n`-th tropical entire functions; the displayed identity
is pointwise and follows from the stronger algebraic theorem above. -/
theorem casoratian_commonFactor_of_entire {n m : ℕ}
    (f : Fin (m + 1) → NthTropicalMeromorphicFunction n)
    (g : NthTropicalMeromorphicFunction n)
    (_hf : ∀ i, IsTropicalEntire (f i)) (_hg : IsTropicalEntire g) (x : ℝ) :
    tropicalCasoratian
        (fun i ↦ tropicalTensor (fun y ↦ f i y) (fun y ↦ g y)) x =
      (∑ k : Fin (m + 1), forwardShift (fun y ↦ g y) k x) +
        tropicalCasoratian (fun i y ↦ f i y) x := by
  exact tropicalCasoratian_commonFactor
    (fun i y ↦ f i y) (fun y ↦ g y) x

end

end NthTropicalNevanlinna
