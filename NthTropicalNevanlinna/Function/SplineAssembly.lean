import NthTropicalNevanlinna.Function.PiecewisePolynomial

/-!
# Assembly of a two-sided polynomial spline

This is infrastructure for Proposition 2.3.  It proves continuity rather than
including continuity of the assembled function as an extra hypothesis.
-/

open Filter Set
open scoped Topology

namespace NthTropicalNevanlinna

noncomputable section

/-- Evaluate a family of polynomial pieces on the intervals of `P`. -/
def assembledFunction
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    (piece : ℤ → Polynomial ℝ) (x : ℝ) : ℝ :=
  (piece (presentationIntervalIndex P x)).eval x

theorem assembledFunction_eq_piece
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    (piece : ℤ → Polynomial ℝ)
    (hadj : ∀ i, (piece i).eval (P.cutPoint i) =
      (piece (i + 1)).eval (P.cutPoint i))
    (i : ℤ) {x : ℝ} (hx : x ∈ Icc (P.cutPoint (i - 1)) (P.cutPoint i)) :
    assembledFunction P piece x = (piece i).eval x := by
  by_cases hstrict : P.cutPoint (i - 1) < x
  · rw [assembledFunction, presentationIntervalIndex_eq_of_mem P ⟨hstrict, hx.2⟩]
  · have hxeq : x = P.cutPoint (i - 1) :=
      le_antisymm (le_of_not_gt hstrict) hx.1
    have hmem : x ∈ Ioc (P.cutPoint ((i - 1) - 1)) (P.cutPoint (i - 1)) := by
      rw [hxeq]
      exact ⟨P.cutPoint_strictMono (by omega), le_rfl⟩
    rw [assembledFunction, presentationIntervalIndex_eq_of_mem P hmem, hxeq]
    simpa only [sub_add_cancel] using hadj (i - 1)

theorem continuous_assembledFunction
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    (piece : ℤ → Polynomial ℝ)
    (hadj : ∀ i, (piece i).eval (P.cutPoint i) =
      (piece (i + 1)).eval (P.cutPoint i)) :
    Continuous (assembledFunction P piece) := by
  rw [continuous_iff_continuousAt]
  intro x
  let i := presentationIntervalIndex P x
  have hx := presentationIntervalIndex_mem P x
  change x ∈ Ioc (P.cutPoint (i - 1)) (P.cutPoint i) at hx
  by_cases htop : x < P.cutPoint i
  · have hnhds : Ioo (P.cutPoint (i - 1)) (P.cutPoint i) ∈ 𝓝 x :=
      Ioo_mem_nhds hx.1 htop
    apply (Polynomial.continuous (piece i)).continuousAt.congr
    filter_upwards [hnhds] with y hy
    rw [assembledFunction, presentationIntervalIndex_eq_of_mem P ⟨hy.1, hy.2.le⟩]
  · have hxeq : x = P.cutPoint i :=
      le_antisymm hx.2 (le_of_not_gt htop)
    let localPiece : ℝ → ℝ := fun y ↦
      if y ≤ P.cutPoint i then (piece i).eval y else (piece (i + 1)).eval y
    have hlocal : Continuous localPiece := by
      dsimp [localPiece]
      apply Continuous.if_le (f := fun y : ℝ ↦ y) (g := fun _ ↦ P.cutPoint i)
        (Polynomial.continuous (piece i)) (Polynomial.continuous (piece (i + 1)))
        continuous_id continuous_const
      intro y hy
      simpa [hy] using hadj i
    have hnhds : Ioo (P.cutPoint (i - 1)) (P.cutPoint (i + 1)) ∈ 𝓝 x := by
      apply Ioo_mem_nhds
      · simpa [hxeq] using P.cutPoint_strictMono (show i - 1 < i by omega)
      · simpa [hxeq] using P.cutPoint_strictMono (show i < i + 1 by omega)
    apply hlocal.continuousAt.congr
    filter_upwards [hnhds] with y hy
    dsimp [localPiece]
    by_cases hyi : y ≤ P.cutPoint i
    · rw [if_pos hyi, assembledFunction,
        presentationIntervalIndex_eq_of_mem P ⟨hy.1, hyi⟩]
    · have hymem : y ∈ Ioc (P.cutPoint ((i + 1) - 1))
          (P.cutPoint (i + 1)) := by
        constructor
        · simpa using lt_of_not_ge hyi
        · exact hy.2.le
      rw [if_neg hyi, assembledFunction,
        presentationIntervalIndex_eq_of_mem P hymem]

/-- The explicit presentation carried by an assembled polynomial spline. -/
def assembledPolynomialPresentation
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    (piece : ℤ → Polynomial ℝ)
    (hdegree : ∀ i, (piece i).natDegree ≤ n)
    (hadj : ∀ i, (piece i).eval (P.cutPoint i) =
      (piece (i + 1)).eval (P.cutPoint i))
    (hexact : ∃ i, (piece i).natDegree = n) :
    PolynomialPresentation n (assembledFunction P piece) where
  cutPoint := P.cutPoint
  piece := piece
  cutPoint_strictMono := P.cutPoint_strictMono
  cutPoint_zero := P.cutPoint_zero
  cutPoint_tendsto_atTop := P.cutPoint_tendsto_atTop
  cutPoint_tendsto_atBot := P.cutPoint_tendsto_atBot
  piece_natDegree_le := hdegree
  eq_piece := fun i _ hx ↦ assembledFunction_eq_piece P piece hadj i hx
  exists_piece_natDegree_eq := hexact

/-- Assemble degree-`n` polynomial pieces into an `n`-th tropical meromorphic function. -/
def assembleNthTropicalMeromorphicFunction
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    (piece : ℤ → Polynomial ℝ)
    (hdegree : ∀ i, (piece i).natDegree ≤ n)
    (hadj : ∀ i, (piece i).eval (P.cutPoint i) =
      (piece (i + 1)).eval (P.cutPoint i))
    (hexact : ∃ i, (piece i).natDegree = n) :
    NthTropicalMeromorphicFunction n where
  toFun := assembledFunction P piece
  continuous_toFun := continuous_assembledFunction P piece hadj
  hasPolynomialPresentation :=
    ⟨assembledPolynomialPresentation P piece hdegree hadj hexact⟩

end

end NthTropicalNevanlinna
