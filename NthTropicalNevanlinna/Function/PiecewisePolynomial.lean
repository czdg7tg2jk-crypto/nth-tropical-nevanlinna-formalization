import Mathlib

/-!
# n-th tropical meromorphic functions

This file separates an intrinsic function from one of its polynomial
presentations.  A presentation uses a locally finite, two-sided sequence of
*cut points*.  A cut point need not be a genuine singularity: adjacent
polynomial pieces may agree.  The normalization `cutPoint 0 = 0` therefore
marks an interval boundary, not a singular point of the function.
-/

open Filter Set

namespace NthTropicalNevanlinna

/--
A normalized polynomial presentation of a real function of degree exactly
`n`.  The interval indexed by `i : ℤ` is
`Icc (cutPoint (i - 1)) (cutPoint i)`, i.e. the closed interval
`[cutPoint (i - 1), cutPoint i]`.

The cut-point sequence is presentation data.  It may contain points where the
two adjacent polynomial pieces are equal, and hence should not be confused
with the intrinsic singular set of the represented function.
-/
structure PolynomialPresentation (n : ℕ) (f : ℝ → ℝ) where
  /-- The strictly increasing, two-sided sequence of interval cut points. -/
  cutPoint : ℤ → ℝ
  /-- The polynomial used on each interval. -/
  piece : ℤ → Polynomial ℝ
  /-- Cut points occur in their indexing order. -/
  cutPoint_strictMono : StrictMono cutPoint
  /-- Index normalization; this does not assert that zero is singular. -/
  cutPoint_zero : cutPoint 0 = 0
  /-- Cut points eventually leave every bounded interval on the right. -/
  cutPoint_tendsto_atTop : Tendsto cutPoint atTop atTop
  /-- Cut points eventually leave every bounded interval on the left. -/
  cutPoint_tendsto_atBot : Tendsto cutPoint atBot atBot
  /-- Every polynomial piece has degree at most `n`. -/
  piece_natDegree_le : ∀ i, (piece i).natDegree ≤ n
  /-- On each closed interval, the function agrees with the chosen piece. -/
  eq_piece : ∀ (i : ℤ) {x : ℝ},
    x ∈ Icc (cutPoint (i - 1)) (cutPoint i) → f x = (piece i).eval x
  /-- The degree bound is attained, matching `supᵢ nᵢ = n` in the paper. -/
  exists_piece_natDegree_eq : ∃ i, (piece i).natDegree = n

theorem PolynomialPresentation.exists_mem_interval
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) :
    ∃ i : ℤ, x ∈ Ioc (P.cutPoint (i - 1)) (P.cutPoint i) := by
  obtain ⟨u, hu⟩ := (tendsto_atTop_atTop.mp P.cutPoint_tendsto_atTop) x
  obtain ⟨b, hb⟩ := (tendsto_atBot_atBot.mp P.cutPoint_tendsto_atBot) x
  have hnonempty : ∃ z : ℤ, x ≤ P.cutPoint z := ⟨u, hu u le_rfl⟩
  have hlower : ∃ b : ℤ, ∀ z : ℤ, x ≤ P.cutPoint z → b ≤ z := by
    refine ⟨b, fun z hz ↦ ?_⟩
    by_contra hzb
    have hzb' : z < b := lt_of_not_ge hzb
    have hlt := P.cutPoint_strictMono hzb'
    have hbx : P.cutPoint b ≤ x := hb b le_rfl
    linarith
  obtain ⟨i, hxi, hi⟩ := Int.exists_least_of_bdd hlower hnonempty
  refine ⟨i, ?_, hxi⟩
  by_contra hx
  have hx' : x ≤ P.cutPoint (i - 1) := le_of_not_gt hx
  have hii := hi (i - 1) hx'
  omega

/-- The unique right-closed presentation interval containing `x`. -/
noncomputable def presentationIntervalIndex
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) : ℤ :=
  Classical.choose (P.exists_mem_interval x)

theorem presentationIntervalIndex_mem
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) :
    x ∈ Ioc (P.cutPoint (presentationIntervalIndex P x - 1))
      (P.cutPoint (presentationIntervalIndex P x)) :=
  Classical.choose_spec (P.exists_mem_interval x)

theorem presentationIntervalIndex_eq_of_mem
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    {x : ℝ} {i : ℤ} (hx : x ∈ Ioc (P.cutPoint (i - 1)) (P.cutPoint i)) :
    presentationIntervalIndex P x = i := by
  let k := presentationIntervalIndex P x
  have hk := presentationIntervalIndex_mem P x
  change x ∈ Ioc (P.cutPoint (k - 1)) (P.cutPoint k) at hk
  apply le_antisymm
  · by_contra h
    have hik : i < k := lt_of_not_ge h
    have hmono : P.cutPoint i ≤ P.cutPoint (k - 1) :=
      P.cutPoint_strictMono.monotone (by omega)
    exact (not_lt_of_ge hx.2) (hmono.trans_lt hk.1)
  · by_contra h
    have hki : k < i := lt_of_not_ge h
    have hmono : P.cutPoint k ≤ P.cutPoint (i - 1) :=
      P.cutPoint_strictMono.monotone (by omega)
    exact (not_lt_of_ge hk.2) (hmono.trans_lt hx.1)

theorem PolynomialPresentation.piece_eval_cutPoint_eq
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (i : ℤ) :
    (P.piece i).eval (P.cutPoint i) =
      (P.piece (i + 1)).eval (P.cutPoint i) := by
  have him1 : P.cutPoint (i - 1) ≤ P.cutPoint i :=
    (P.cutPoint_strictMono (by omega)).le
  have hii1 : P.cutPoint i ≤ P.cutPoint (i + 1) :=
    (P.cutPoint_strictMono (by omega)).le
  rw [← P.eq_piece i ⟨him1, le_rfl⟩]
  rw [← P.eq_piece (i + 1) ⟨by simp, hii1⟩]

/-- The polynomial germ immediately to the left of `x` in a presentation. -/
noncomputable def PolynomialPresentation.leftPieceAt
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) : Polynomial ℝ :=
  P.piece (presentationIntervalIndex P x)

/-- The polynomial germ immediately to the right of `x` in a presentation. -/
noncomputable def PolynomialPresentation.rightPieceAt
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) : Polynomial ℝ :=
  let i := presentationIntervalIndex P x
  if x = P.cutPoint i then P.piece (i + 1) else P.piece i

theorem PolynomialPresentation.leftPieceAt_natDegree_le
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) :
    (P.leftPieceAt x).natDegree ≤ n := by
  exact P.piece_natDegree_le (presentationIntervalIndex P x)

theorem PolynomialPresentation.rightPieceAt_natDegree_le
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) :
    (P.rightPieceAt x).natDegree ≤ n := by
  simp only [PolynomialPresentation.rightPieceAt]
  split_ifs
  · exact P.piece_natDegree_le (presentationIntervalIndex P x + 1)
  · exact P.piece_natDegree_le (presentationIntervalIndex P x)

theorem PolynomialPresentation.leftPieceAt_eval
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) :
    (P.leftPieceAt x).eval x = f x := by
  let i := presentationIntervalIndex P x
  have hx := presentationIntervalIndex_mem P x
  change x ∈ Ioc (P.cutPoint (i - 1)) (P.cutPoint i) at hx
  exact (P.eq_piece i ⟨hx.1.le, hx.2⟩).symm

theorem PolynomialPresentation.exists_left_germ_interval
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) :
    ∃ a < x, ∀ y ∈ Ioo a x, f y = (P.leftPieceAt x).eval y := by
  let i := presentationIntervalIndex P x
  have hx := presentationIntervalIndex_mem P x
  change x ∈ Ioc (P.cutPoint (i - 1)) (P.cutPoint i) at hx
  refine ⟨P.cutPoint (i - 1), hx.1, ?_⟩
  intro y hy
  exact P.eq_piece i ⟨hy.1.le, (hy.2.le.trans hx.2)⟩

theorem PolynomialPresentation.exists_right_germ_interval
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) :
    ∃ b > x, ∀ y ∈ Ioo x b, f y = (P.rightPieceAt x).eval y := by
  let i := presentationIntervalIndex P x
  have hx := presentationIntervalIndex_mem P x
  change x ∈ Ioc (P.cutPoint (i - 1)) (P.cutPoint i) at hx
  by_cases htop : x = P.cutPoint i
  · refine ⟨P.cutPoint (i + 1), ?_, ?_⟩
    · rw [htop]
      exact P.cutPoint_strictMono (by omega)
    · intro y hy
      rw [PolynomialPresentation.rightPieceAt, if_pos htop]
      exact P.eq_piece (i + 1) ⟨by simpa [htop] using hy.1.le, hy.2.le⟩
  · have hxlt : x < P.cutPoint i := lt_of_le_of_ne hx.2 htop
    refine ⟨P.cutPoint i, hxlt, ?_⟩
    intro y hy
    rw [PolynomialPresentation.rightPieceAt, if_neg htop]
    exact P.eq_piece i ⟨hx.1.le.trans hy.1.le, hy.2.le⟩

private theorem polynomial_eq_of_eqOn_Ioo
    (p q : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (h : ∀ x ∈ Ioo a b, p.eval x = q.eval x) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq p q
  apply (Ioo_infinite hab).mono
  intro x hx
  exact h x hx

/-- The left polynomial germ is independent of the chosen presentation. -/
theorem PolynomialPresentation.leftPieceAt_eq
    {n : ℕ} {f : ℝ → ℝ} (P Q : PolynomialPresentation n f) (x : ℝ) :
    P.leftPieceAt x = Q.leftPieceAt x := by
  obtain ⟨aP, haP, hP⟩ := P.exists_left_germ_interval x
  obtain ⟨aQ, haQ, hQ⟩ := Q.exists_left_germ_interval x
  apply polynomial_eq_of_eqOn_Ioo _ _ (max_lt haP haQ)
  intro y hy
  have hyP : y ∈ Ioo aP x := ⟨(le_max_left _ _).trans_lt hy.1, hy.2⟩
  have hyQ : y ∈ Ioo aQ x := ⟨(le_max_right _ _).trans_lt hy.1, hy.2⟩
  exact (hP y hyP).symm.trans (hQ y hyQ)

/-- The right polynomial germ is independent of the chosen presentation. -/
theorem PolynomialPresentation.rightPieceAt_eq
    {n : ℕ} {f : ℝ → ℝ} (P Q : PolynomialPresentation n f) (x : ℝ) :
    P.rightPieceAt x = Q.rightPieceAt x := by
  obtain ⟨bP, hbP, hP⟩ := P.exists_right_germ_interval x
  obtain ⟨bQ, hbQ, hQ⟩ := Q.exists_right_germ_interval x
  apply polynomial_eq_of_eqOn_Ioo _ _ (lt_min hbP hbQ)
  intro y hy
  have hyP : y ∈ Ioo x bP := ⟨hy.1, hy.2.trans_le (min_le_left _ _)⟩
  have hyQ : y ∈ Ioo x bQ := ⟨hy.1, hy.2.trans_le (min_le_right _ _)⟩
  exact (hP y hyP).symm.trans (hQ y hyQ)

/-- The paper's predicate, with continuity and existence of a presentation. -/
def IsNthTropicalMeromorphicFunction (n : ℕ) (f : ℝ → ℝ) : Prop :=
  Continuous f ∧ Nonempty (PolynomialPresentation n f)

/--
An intrinsic real-valued `n`-th tropical meromorphic function.  A presentation
is stored only through the proposition that one exists, so equality of this
structure is equality of the underlying functions and does not remember a cut
grid or a family of polynomial pieces.
-/
structure NthTropicalMeromorphicFunction (n : ℕ) where
  toFun : ℝ → ℝ
  continuous_toFun : Continuous toFun
  hasPolynomialPresentation : Nonempty (PolynomialPresentation n toFun)

instance (n : ℕ) : CoeFun (NthTropicalMeromorphicFunction n) (fun _ ↦ ℝ → ℝ) :=
  ⟨NthTropicalMeromorphicFunction.toFun⟩

@[ext]
theorem NthTropicalMeromorphicFunction.ext
    {n : ℕ} {f g : NthTropicalMeromorphicFunction n}
    (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk ff hfc hfp =>
      cases g with
      | mk gg hgc hgp =>
          have hfg : ff = gg := funext h
          subst gg
          rfl

@[simp]
theorem NthTropicalMeromorphicFunction.coe_mk
    {n : ℕ} (f : ℝ → ℝ) (hf : Continuous f) (P : PolynomialPresentation n f) :
    ((⟨f, hf, ⟨P⟩⟩ : NthTropicalMeromorphicFunction n) : ℝ → ℝ) = f := rfl

theorem NthTropicalMeromorphicFunction.continuous
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Continuous f :=
  f.continuous_toFun

theorem NthTropicalMeromorphicFunction.isNthTropicalMeromorphic
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) :
    IsNthTropicalMeromorphicFunction n f :=
  ⟨f.continuous_toFun, f.hasPolynomialPresentation⟩

theorem NthTropicalMeromorphicFunction.exists_polynomialPresentation
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) :
    Nonempty (PolynomialPresentation n f) :=
  f.hasPolynomialPresentation

/--
An internal witness used to run constructions.  Public definitions are proved
independent of this classical choice before they are treated as intrinsic.
-/
noncomputable def NthTropicalMeromorphicFunction.presentation
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : PolynomialPresentation n f :=
  Classical.choice f.hasPolynomialPresentation

end NthTropicalNevanlinna
