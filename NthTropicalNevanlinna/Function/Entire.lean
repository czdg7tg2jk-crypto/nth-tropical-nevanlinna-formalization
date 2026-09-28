import NthTropicalNevanlinna.Function.Multiplicity

/-!
# Tropical entire functions
-/

namespace NthTropicalNevanlinna

/-- An `n`-th tropical meromorphic function is entire when it has no poles. -/
def IsTropicalEntire {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Prop :=
  ∀ x j, 1 ≤ j → j ≤ n → ¬ IsJthPole f j x

/-- It is nowhere vanishing entire when it has neither poles nor roots. -/
def IsTropicalNowhereVanishingEntire {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) : Prop :=
  IsTropicalEntire f ∧ ∀ x j, 1 ≤ j → j ≤ n → ¬ IsJthRoot f j x

theorem isTropicalEntire_iff_multiplicity_nonneg {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) :
    IsTropicalEntire f ↔ ∀ x j, 1 ≤ j → j ≤ n → 0 ≤ multiplicity f j x := by
  simp only [IsTropicalEntire, IsJthPole, not_lt]

theorem isTropicalNowhereVanishingEntire_iff_multiplicity_eq_zero {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) :
    IsTropicalNowhereVanishingEntire f ↔
      ∀ x j, 1 ≤ j → j ≤ n → multiplicity f j x = 0 := by
  constructor
  · intro hf x j hj hjn
    exact le_antisymm
      (not_lt.mp (hf.2 x j hj hjn))
      (not_lt.mp (hf.1 x j hj hjn))
  · intro hf
    constructor
    · intro x j hj hjn
      simp [IsJthPole, hf x j hj hjn]
    · intro x j hj hjn
      simp [IsJthRoot, hf x j hj hjn]

end NthTropicalNevanlinna
