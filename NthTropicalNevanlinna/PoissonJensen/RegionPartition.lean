import Mathlib

/-!
# The nine regions in Lemma 3.2

The paper's sets `F₁,...,F₉` are represented by one finite type and a
membership predicate.  This keeps the subsequent nine-case proof finite and
explicit without making the regions part of the top-level theory API.
-/

open Set

namespace NthTropicalNevanlinna

/-- Labels for the nine mutually exclusive relative-position regions. -/
inductive RelativeRegion
  | f1 | f2 | f3 | f4 | f5 | f6 | f7 | f8 | f9
  deriving DecidableEq, Fintype

/-- Membership in the paper's region `F₁,...,F₉`. -/
def InRelativeRegion (region : RelativeRegion) (r x y : ℝ) : Prop :=
  y ∈ Ioo (-r) r ∧ match region with
    | .f1 => y < min 0 x
    | .f2 => max 0 x < y
    | .f3 => y = 0 ∧ x = 0
    | .f4 => 0 < y ∧ y < x
    | .f5 => x < y ∧ y < 0
    | .f6 => x < y ∧ y = 0
    | .f7 => y = 0 ∧ 0 < x
    | .f8 => 0 < y ∧ y = x
    | .f9 => y = x ∧ x < 0

/-- The subset `F_region(r,x)` of the open interval `(-r,r)`. -/
def relativeRegionSet (region : RelativeRegion) (r x : ℝ) : Set ℝ :=
  {y | InRelativeRegion region r x y}

/-- Every `y ∈ (-r,r)` lies in one of the nine regions for fixed `x`. -/
theorem exists_relativeRegion {r x y : ℝ}
    (hy : y ∈ Ioo (-r) r) : ∃ region, InRelativeRegion region r x y := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rcases lt_trichotomy y x with hyx | hyx | hyx
    · exact ⟨.f1, hy, by simp [min_eq_right hx.le, hyx]⟩
    · exact ⟨.f9, hy, hyx, hx⟩
    · rcases lt_trichotomy y 0 with hy0 | hy0 | hy0
      · exact ⟨.f5, hy, hyx, hy0⟩
      · exact ⟨.f6, hy, by linarith, hy0⟩
      · exact ⟨.f2, hy, by simp [max_eq_left hx.le, hy0]⟩
  · subst x
    rcases lt_trichotomy y 0 with hy0 | hy0 | hy0
    · exact ⟨.f1, hy, by simpa using hy0⟩
    · exact ⟨.f3, hy, hy0, rfl⟩
    · exact ⟨.f2, hy, by simpa using hy0⟩
  · rcases lt_trichotomy y 0 with hy0 | hy0 | hy0
    · exact ⟨.f1, hy, by simp [min_eq_left hx.le, hy0]⟩
    · exact ⟨.f7, hy, hy0, hx⟩
    · rcases lt_trichotomy y x with hyx | hyx | hyx
      · exact ⟨.f4, hy, hy0, hyx⟩
      · exact ⟨.f8, hy, hy0, hyx⟩
      · exact ⟨.f2, hy, by simp [max_eq_right hx.le, hyx]⟩

/-- The nine region predicates are pairwise disjoint. -/
theorem relativeRegion_unique {r x y : ℝ} {region₁ region₂ : RelativeRegion}
    (h₁ : InRelativeRegion region₁ r x y)
    (h₂ : InRelativeRegion region₂ r x y) : region₁ = region₂ := by
  rcases h₁ with ⟨_, h₁⟩
  rcases h₂ with ⟨_, h₂⟩
  cases region₁ <;> cases region₂ <;>
    simp_all [lt_min_iff, max_lt_iff] <;> linarith

end NthTropicalNevanlinna
