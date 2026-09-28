import NthTropicalNevanlinna.Function.Entire

/-!
# n-th tropical holomorphic curves

The coordinates of a curve need not all have the same exact polynomial
degree.  Accordingly, a representation stores an order `order i ≤ n` for
each coordinate, together with the requirement that one coordinate attains
`n`.  This is the literal formal counterpart of `max_i n_i = n` in the
paper.
-/

namespace NthTropicalNevanlinna

noncomputable section

/-- Two finite real vectors represent the same tropical projective point when
they differ by a common additive scalar. -/
def TropicalProjectiveEquivalent {m : ℕ}
    (a b : Fin (m + 1) → ℝ) : Prop :=
  ∃ c : ℝ, ∀ i, a i = b i + c

theorem tropicalProjectiveEquivalent_refl {m : ℕ}
    (a : Fin (m + 1) → ℝ) : TropicalProjectiveEquivalent a a := by
  exact ⟨0, by simp⟩

theorem tropicalProjectiveEquivalent_symm {m : ℕ}
    {a b : Fin (m + 1) → ℝ} (h : TropicalProjectiveEquivalent a b) :
    TropicalProjectiveEquivalent b a := by
  obtain ⟨c, hc⟩ := h
  refine ⟨-c, fun i ↦ ?_⟩
  linarith [hc i]

theorem tropicalProjectiveEquivalent_trans {m : ℕ}
    {a b c : Fin (m + 1) → ℝ}
    (hab : TropicalProjectiveEquivalent a b)
    (hbc : TropicalProjectiveEquivalent b c) :
    TropicalProjectiveEquivalent a c := by
  obtain ⟨c, hc⟩ := hab
  obtain ⟨d, hd⟩ := hbc
  refine ⟨d + c, fun i ↦ ?_⟩
  rw [hc i, hd i]
  ring

/-- The real-valued part of tropical projective `m`-space.  The paper's
coordinate functions are real-valued, so the excluded all-`-∞` vector never
occurs in the present development. -/
def TropicalProjectiveSpace (m : ℕ) :=
  Quotient (⟨TropicalProjectiveEquivalent,
    tropicalProjectiveEquivalent_refl,
    tropicalProjectiveEquivalent_symm,
    tropicalProjectiveEquivalent_trans⟩ : Setoid (Fin (m + 1) → ℝ))

/-- A coordinate representation of an `n`-th tropical holomorphic curve. -/
structure TropicalHolomorphicCurveRepresentation (n m : ℕ) where
  /-- Exact order of each coordinate. -/
  order : Fin (m + 1) → ℕ
  /-- No coordinate has order above the curve order. -/
  order_le : ∀ i, order i ≤ n
  /-- At least one coordinate has exact order `n`. -/
  order_attained : ∃ i, order i = n
  /-- The heterogeneous family of coordinate functions. -/
  coordinate : ∀ i, NthTropicalMeromorphicFunction (order i)
  /-- Every coordinate is entire through the common ambient order `n`.

  The clauses above its exact order are mathematically automatic from the
  degree bound, but retaining the uniform statement is the useful public API
  for projective arguments. -/
  coordinate_multiplicity_nonneg :
    ∀ i x j, 1 ≤ j → j ≤ n → 0 ≤ multiplicity (coordinate i) j x

namespace TropicalHolomorphicCurveRepresentation

/-- Evaluation of one coordinate. -/
def eval {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (i : Fin (m + 1)) (x : ℝ) : ℝ :=
  F.coordinate i x

/-- The projective point represented at `x`. -/
def projectiveValue {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) (x : ℝ) :
    TropicalProjectiveSpace m :=
  Quotient.mk _ (fun i ↦ F.eval i x)

/-- The coordinate functions have no common `j`-th root, for every
`1 ≤ j ≤ n`. -/
def IsReduced {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) : Prop :=
  ∀ x j, 1 ≤ j → j ≤ n →
    ¬ ∀ i, IsJthRoot (F.coordinate i) j x

/-- The represented projective map is nonconstant. -/
def IsNonconstant {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) : Prop :=
  ∃ x y, F.projectiveValue x ≠ F.projectiveValue y

theorem coordinate_isTropicalEntire {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) (i : Fin (m + 1)) :
    IsTropicalEntire (F.coordinate i) := by
  rw [isTropicalEntire_iff_multiplicity_nonneg]
  intro x j hj hji
  exact F.coordinate_multiplicity_nonneg i x j hj
    (hji.trans (F.order_le i))

end TropicalHolomorphicCurveRepresentation

/-- An `n`-th tropical holomorphic curve is a projective-valued map admitting
a coordinate representation whose maximum coordinate order is `n`. -/
structure NthTropicalHolomorphicCurve (n m : ℕ) where
  toFun : ℝ → TropicalProjectiveSpace m
  has_representation :
    ∃ F : TropicalHolomorphicCurveRepresentation n m,
      ∀ x, toFun x = F.projectiveValue x

instance (n m : ℕ) : CoeFun (NthTropicalHolomorphicCurve n m)
    (fun _ ↦ ℝ → TropicalProjectiveSpace m) :=
  ⟨NthTropicalHolomorphicCurve.toFun⟩

/-- `F` is a coordinate representation of the projective curve `f`. -/
def IsCurveRepresentation {n m : ℕ}
    (f : NthTropicalHolomorphicCurve n m)
    (F : TropicalHolomorphicCurveRepresentation n m) : Prop :=
  ∀ x, f x = F.projectiveValue x

/-- A reduced coordinate representation of a fixed curve. -/
structure ReducedCurveRepresentation {n m : ℕ}
    (f : NthTropicalHolomorphicCurve n m) where
  representation : TropicalHolomorphicCurveRepresentation n m
  represents : IsCurveRepresentation f representation
  reduced : representation.IsReduced

/-- A regular common rescaling between two curve representations.  It records
the paper's identity `F_i(x) = G_i(x) + λ(x)` and the fact that `λ` still has
order at most `n`. -/
structure ProjectiveRescaling {n m : ℕ}
    (F G : TropicalHolomorphicCurveRepresentation n m) where
  scalarOrder : ℕ
  scalarOrder_le : scalarOrder ≤ n
  scalar : NthTropicalMeromorphicFunction scalarOrder
  eq_coordinate : ∀ i x, F.eval i x = G.eval i x + scalar x

theorem ProjectiveRescaling.projectiveValue_eq {n m : ℕ}
    {F G : TropicalHolomorphicCurveRepresentation n m}
    (h : ProjectiveRescaling F G) (x : ℝ) :
    F.projectiveValue x = G.projectiveValue x := by
  apply Quotient.sound
  exact ⟨h.scalar x, fun i ↦ h.eq_coordinate i x⟩

end

end NthTropicalNevanlinna
