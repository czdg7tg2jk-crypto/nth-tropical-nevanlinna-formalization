import NthTropicalNevanlinna.Function.PiecewisePolynomial

/-!
# Constructing global presentations from locally finite cut sets

This file supplies the order-theoretic bookkeeping needed by the closure
operations used in Chapter 5.  A `PolynomialCutModelLE` has a locally finite,
two-sided unbounded cut set containing zero and a polynomial on every pair of
consecutive cuts.  The cut set is canonically order-isomorphic to `ℤ`; after
normalizing the index of zero, this gives the paper's global presentation.

The intermediate `PolynomialPresentationLE` records only a degree bound.  Its
`tighten` construction chooses the largest degree actually occurring, so the
final `PolynomialPresentation` still has the exact-order semantics used in
the rest of the development.
-/

open Filter Set

namespace NthTropicalNevanlinna

noncomputable section

/-- A global polynomial presentation with degree bounded by `n`, without an
attainment requirement. -/
structure PolynomialPresentationLE (n : ℕ) (f : ℝ → ℝ) where
  cutPoint : ℤ → ℝ
  piece : ℤ → Polynomial ℝ
  cutPoint_strictMono : StrictMono cutPoint
  cutPoint_zero : cutPoint 0 = 0
  cutPoint_tendsto_atTop : Tendsto cutPoint atTop atTop
  cutPoint_tendsto_atBot : Tendsto cutPoint atBot atBot
  piece_natDegree_le : ∀ i, (piece i).natDegree ≤ n
  eq_piece : ∀ (i : ℤ) {x : ℝ},
    x ∈ Icc (cutPoint (i - 1)) (cutPoint i) → f x = (piece i).eval x

namespace PolynomialPresentationLE

variable {n : ℕ} {f : ℝ → ℝ}

/-- Degrees which actually occur among the pieces. -/
def occurringDegrees (P : PolynomialPresentationLE n f) : Finset ℕ :=
  by
    classical
    exact (Finset.range (n + 1)).filter fun d ↦
      ∃ i, (P.piece i).natDegree = d

theorem occurringDegrees_nonempty (P : PolynomialPresentationLE n f) :
    P.occurringDegrees.Nonempty := by
  classical
  refine ⟨(P.piece 0).natDegree, ?_⟩
  simp [occurringDegrees, Nat.lt_succ_iff, P.piece_natDegree_le 0]

/-- The exact order attained by an at-most-`n` presentation. -/
def exactOrder (P : PolynomialPresentationLE n f) : ℕ :=
  P.occurringDegrees.max' P.occurringDegrees_nonempty

theorem exactOrder_le (P : PolynomialPresentationLE n f) : P.exactOrder ≤ n := by
  classical
  have hmem := P.occurringDegrees.max'_mem P.occurringDegrees_nonempty
  have hrange : P.exactOrder ∈ Finset.range (n + 1) :=
    (Finset.mem_filter.mp hmem).1
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)

theorem piece_natDegree_le_exactOrder (P : PolynomialPresentationLE n f) (i : ℤ) :
    (P.piece i).natDegree ≤ P.exactOrder := by
  classical
  apply Finset.le_max' P.occurringDegrees (P.piece i).natDegree
  simp [occurringDegrees, Nat.lt_succ_iff, P.piece_natDegree_le i]

theorem exists_piece_natDegree_eq_exactOrder (P : PolynomialPresentationLE n f) :
    ∃ i, (P.piece i).natDegree = P.exactOrder := by
  classical
  have hmem := P.occurringDegrees.max'_mem P.occurringDegrees_nonempty
  exact (Finset.mem_filter.mp hmem).2

/-- Tighten a degree bound to the largest degree actually attained. -/
def tighten (P : PolynomialPresentationLE n f) :
    PolynomialPresentation P.exactOrder f where
  cutPoint := P.cutPoint
  piece := P.piece
  cutPoint_strictMono := P.cutPoint_strictMono
  cutPoint_zero := P.cutPoint_zero
  cutPoint_tendsto_atTop := P.cutPoint_tendsto_atTop
  cutPoint_tendsto_atBot := P.cutPoint_tendsto_atBot
  piece_natDegree_le := P.piece_natDegree_le_exactOrder
  eq_piece := P.eq_piece
  exists_piece_natDegree_eq := P.exists_piece_natDegree_eq_exactOrder

end PolynomialPresentationLE

/-- A locally finite cut-set description with a degree bound.  `piece` is
only requested for consecutive cuts (`a ⋖ b`). -/
structure PolynomialCutModelLE (n : ℕ) (f : ℝ → ℝ) where
  cutSet : Set ℝ
  zero_mem : 0 ∈ cutSet
  finite_Icc : ∀ a b : ℝ, (cutSet ∩ Icc a b).Finite
  unbounded_above : ∀ a : ℝ, ∃ b ∈ cutSet, a < b
  unbounded_below : ∀ b : ℝ, ∃ a ∈ cutSet, a < b
  piece : ∀ (a b : cutSet), a ⋖ b → Polynomial ℝ
  piece_natDegree_le : ∀ (a b : cutSet) (h : a ⋖ b),
    (piece a b h).natDegree ≤ n
  eq_piece : ∀ (a b : cutSet) (h : a ⋖ b) {x : ℝ},
    x ∈ Icc (a : ℝ) (b : ℝ) → f x = (piece a b h).eval x

namespace PolynomialCutModelLE

variable {n : ℕ} {f : ℝ → ℝ}

private theorem subtype_Icc_finite (M : PolynomialCutModelLE n f)
    (a b : M.cutSet) : Set.Finite (Set.Icc a b) := by
  let e : M.cutSet → ℝ := fun x ↦ x
  apply Set.Finite.of_finite_image
    ((M.finite_Icc (a : ℝ) (b : ℝ)).subset ?_)
    (Set.injOn_of_injective Subtype.coe_injective)
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y.property, hy⟩

private noncomputable def cutOrderIsoInt (M : PolynomialCutModelLE n f) :
    M.cutSet ≃o ℤ := by
  letI : Nonempty M.cutSet := ⟨⟨0, M.zero_mem⟩⟩
  letI : LocallyFiniteOrder M.cutSet :=
    LocallyFiniteOrder.ofFiniteIcc M.subtype_Icc_finite
  letI : SuccOrder M.cutSet := LinearLocallyFiniteOrder.succOrder M.cutSet
  letI : PredOrder M.cutSet := LinearLocallyFiniteOrder.predOrder M.cutSet
  letI : IsSuccArchimedean M.cutSet := inferInstance
  letI : NoMaxOrder M.cutSet := ⟨fun a ↦ by
    obtain ⟨b, hbS, hab⟩ := M.unbounded_above a
    exact ⟨⟨b, hbS⟩, hab⟩⟩
  letI : NoMinOrder M.cutSet := ⟨fun b ↦ by
    obtain ⟨a, haS, hab⟩ := M.unbounded_below b
    exact ⟨⟨a, haS⟩, hab⟩⟩
  exact orderIsoIntOfLinearSuccPredArch

private def zeroCut (M : PolynomialCutModelLE n f) : M.cutSet :=
  ⟨0, M.zero_mem⟩

private noncomputable def normalizedCut (M : PolynomialCutModelLE n f)
    (i : ℤ) : M.cutSet :=
  M.cutOrderIsoInt.symm (M.cutOrderIsoInt M.zeroCut + i)

private theorem normalizedCut_strictMono (M : PolynomialCutModelLE n f) :
    StrictMono M.normalizedCut := by
  intro i j hij
  apply M.cutOrderIsoInt.symm.strictMono
  omega

@[simp] private theorem normalizedCut_zero (M : PolynomialCutModelLE n f) :
    (M.normalizedCut 0 : ℝ) = 0 := by
  change ((M.cutOrderIsoInt.symm (M.cutOrderIsoInt M.zeroCut + 0) : M.cutSet) : ℝ) = 0
  simp [zeroCut]

private theorem coe_tendsto_atTop (M : PolynomialCutModelLE n f) :
    Tendsto (fun x : M.cutSet ↦ (x : ℝ)) atTop atTop := by
  letI : Nonempty M.cutSet := ⟨M.zeroCut⟩
  rw [tendsto_atTop_atTop]
  intro a
  obtain ⟨b, hbS, hab⟩ := M.unbounded_above a
  refine ⟨⟨b, hbS⟩, fun x hbx ↦ ?_⟩
  change a ≤ (x : ℝ)
  exact hab.le.trans hbx

private theorem coe_tendsto_atBot (M : PolynomialCutModelLE n f) :
    Tendsto (fun x : M.cutSet ↦ (x : ℝ)) atBot atBot := by
  letI : Nonempty M.cutSet := ⟨M.zeroCut⟩
  rw [tendsto_atBot_atBot]
  intro b
  obtain ⟨a, haS, hab⟩ := M.unbounded_below b
  refine ⟨⟨a, haS⟩, fun x hxa ↦ ?_⟩
  change (x : ℝ) ≤ a at hxa
  change (x : ℝ) ≤ b
  exact hxa.trans hab.le

private theorem normalizedCut_tendsto_atTop (M : PolynomialCutModelLE n f) :
    Tendsto (fun i ↦ (M.normalizedCut i : ℝ)) atTop atTop := by
  change Tendsto ((fun x : M.cutSet ↦ (x : ℝ)) ∘
    M.cutOrderIsoInt.symm ∘
      (fun i : ℤ ↦ M.cutOrderIsoInt M.zeroCut + i)) atTop atTop
  exact M.coe_tendsto_atTop.comp
    (M.cutOrderIsoInt.symm.tendsto_atTop.comp
      (tendsto_const_nhds.add_atTop tendsto_id))

private theorem normalizedCut_tendsto_atBot (M : PolynomialCutModelLE n f) :
    Tendsto (fun i ↦ (M.normalizedCut i : ℝ)) atBot atBot := by
  change Tendsto ((fun x : M.cutSet ↦ (x : ℝ)) ∘
    M.cutOrderIsoInt.symm ∘
      (fun i : ℤ ↦ M.cutOrderIsoInt M.zeroCut + i)) atBot atBot
  exact M.coe_tendsto_atBot.comp
    (M.cutOrderIsoInt.symm.tendsto_atBot.comp
      (tendsto_const_nhds.add_atBot tendsto_id))

private theorem normalizedCut_covBy (M : PolynomialCutModelLE n f) (i : ℤ) :
    M.normalizedCut (i - 1) ⋖ M.normalizedCut i := by
  constructor
  · exact M.normalizedCut_strictMono (by omega)
  · intro c hac hcb
    have h1 := M.cutOrderIsoInt.strictMono hac
    have h2 := M.cutOrderIsoInt.strictMono hcb
    simp only [normalizedCut, OrderIso.apply_symm_apply] at h1 h2
    omega

private noncomputable def normalizedPiece (M : PolynomialCutModelLE n f)
    (i : ℤ) : Polynomial ℝ :=
  M.piece (M.normalizedCut (i - 1)) (M.normalizedCut i) (M.normalizedCut_covBy i)

/-- Enumerate the locally finite cut set by `ℤ`, normalized so that index zero
is the cut at the origin. -/
def toPresentationLE (M : PolynomialCutModelLE n f) :
    PolynomialPresentationLE n f where
  cutPoint i := M.normalizedCut i
  piece := M.normalizedPiece
  cutPoint_strictMono := fun _ _ h ↦ M.normalizedCut_strictMono h
  cutPoint_zero := M.normalizedCut_zero
  cutPoint_tendsto_atTop := M.normalizedCut_tendsto_atTop
  cutPoint_tendsto_atBot := M.normalizedCut_tendsto_atBot
  piece_natDegree_le := fun i ↦
    M.piece_natDegree_le _ _ (M.normalizedCut_covBy i)
  eq_piece := fun i _ hx ↦
    M.eq_piece _ _ (M.normalizedCut_covBy i) hx

/-- A locally finite cut model yields an exact-order tropical meromorphic
function of some order `q ≤ n`. -/
def toNthTropicalMeromorphicFunction (M : PolynomialCutModelLE n f)
    (hf : Continuous f) :
    NthTropicalMeromorphicFunction M.toPresentationLE.exactOrder where
  toFun := f
  continuous_toFun := hf
  hasPolynomialPresentation := ⟨M.toPresentationLE.tighten⟩

@[simp] theorem toNthTropicalMeromorphicFunction_apply
    (M : PolynomialCutModelLE n f) (hf : Continuous f) (x : ℝ) :
    M.toNthTropicalMeromorphicFunction hf x = f x := rfl

theorem toNthTropicalMeromorphicFunction_order_le
    (M : PolynomialCutModelLE n f) : M.toPresentationLE.exactOrder ≤ n :=
  M.toPresentationLE.exactOrder_le

end PolynomialCutModelLE

/-! ## Finite ordinary algebra -/

/-- Cut points occurring in a presentation. -/
def PolynomialPresentation.cutSet {n : ℕ} {f : ℝ → ℝ}
    (P : PolynomialPresentation n f) : Set ℝ := Set.range P.cutPoint

theorem PolynomialPresentation.finite_cutSet_inter_Icc
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (a b : ℝ) :
    (P.cutSet ∩ Icc a b).Finite := by
  let ia := presentationIntervalIndex P a
  let ib := presentationIntervalIndex P b
  have ha := presentationIntervalIndex_mem P a
  have hb := presentationIntervalIndex_mem P b
  let indices : Set ℤ := Set.Icc (ia - 1) ib
  have hindices : indices.Finite := Set.finite_Icc _ _
  apply (hindices.image P.cutPoint).subset
  rintro x ⟨⟨i, rfl⟩, hai, hib⟩
  refine ⟨i, ?_, rfl⟩
  constructor
  · by_contra h
    have hi : i < ia - 1 := lt_of_not_ge h
    have hcut := P.cutPoint_strictMono hi
    exact (not_lt_of_ge hai) (hcut.trans ha.1)
  · by_contra h
    have hi : ib < i := lt_of_not_ge h
    have hcut := P.cutPoint_strictMono hi
    exact (not_lt_of_ge hib) (hb.2.trans_lt hcut)

private theorem exists_piece_index_on_covBy_of_cut_mem
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    {S : Set ℝ} (hcuts : P.cutSet ⊆ S)
    (a b : S) (hab : a ⋖ b) :
    ∃ i : ℤ, (P.piece i).natDegree ≤ n ∧
      (∀ x ∈ Icc (a : ℝ) (b : ℝ),
        x ∈ Icc (P.cutPoint (i - 1)) (P.cutPoint i)) ∧
      ∀ x ∈ Icc (a : ℝ) (b : ℝ), f x = (P.piece i).eval x := by
  let m : ℝ := ((a : ℝ) + (b : ℝ)) / 2
  have habReal : (a : ℝ) < (b : ℝ) := hab.1
  have ham : (a : ℝ) < m := by dsimp [m]; linarith
  have hmb : m < (b : ℝ) := by dsimp [m]; linarith
  let i := presentationIntervalIndex P m
  have hm := presentationIntervalIndex_mem P m
  change m ∈ Ioc (P.cutPoint (i - 1)) (P.cutPoint i) at hm
  have hlower : P.cutPoint (i - 1) ≤ (a : ℝ) := by
    by_contra h
    have hac : (a : ℝ) < P.cutPoint (i - 1) := lt_of_not_ge h
    let c : S := ⟨P.cutPoint (i - 1), hcuts ⟨i - 1, rfl⟩⟩
    exact hab.2 (show a < c from hac) (show c < b from hm.1.trans hmb)
  have hupper : (b : ℝ) ≤ P.cutPoint i := by
    by_contra h
    have hcb : P.cutPoint i < (b : ℝ) := lt_of_not_ge h
    let c : S := ⟨P.cutPoint i, hcuts ⟨i, rfl⟩⟩
    exact hab.2 (show a < c from ham.trans_le hm.2) (show c < b from hcb)
  refine ⟨i, P.piece_natDegree_le i, fun x hx ↦
    ⟨hlower.trans hx.1, hx.2.trans hupper⟩, fun x hx ↦ ?_⟩
  exact P.eq_piece i ⟨hlower.trans hx.1, hx.2.trans hupper⟩

private theorem eq_piece_on_covBy_of_cut_mem
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    {S : Set ℝ} (hcuts : P.cutSet ⊆ S)
    (a b : S) (hab : a ⋖ b) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ n ∧
      ∀ x ∈ Icc (a : ℝ) (b : ℝ), f x = p.eval x := by
  obtain ⟨i, hiDegree, _hiMem, hiEq⟩ :=
    exists_piece_index_on_covBy_of_cut_mem P hcuts a b hab
  exact ⟨P.piece i, hiDegree, hiEq⟩

/-! ## Translation -/

/-- A function together with an automatically chosen exact order no larger
than the ambient bound.  It is placed before the closure constructions so
translation can use the same public realization interface as addition and
the later operations. -/
structure NthTropicalMeromorphicRealization (n : ℕ) (f : ℝ → ℝ) where
  order : ℕ
  order_le : order ≤ n
  function : NthTropicalMeromorphicFunction order
  eq_fun : ∀ x, function x = f x

/-- Insert the translated cut set together with the origin.  The extra origin
is only the normalization cut required by `PolynomialPresentation`; it need
not be a singularity. -/
def PolynomialPresentation.translateCutModel
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (c : ℝ) :
    PolynomialCutModelLE n (fun x ↦ f (x + c)) where
  cutSet := {x | x + c ∈ P.cutSet} ∪ {0}
  zero_mem := Or.inr (Set.mem_singleton 0)
  finite_Icc := by
    intro a b
    have hbase := P.finite_cutSet_inter_Icc (a + c) (b + c)
    have himage : ((P.cutSet ∩ Icc (a + c) (b + c)).image
        (fun y : ℝ ↦ y - c)).Finite := hbase.image _
    apply (himage.union (Set.finite_singleton 0)).subset
    rintro x ⟨hx, hxab⟩
    rcases hx with hx | hx
    · left
      refine ⟨x + c, ⟨hx, ?_⟩, by ring⟩
      exact ⟨by linarith [hxab.1], by linarith [hxab.2]⟩
    · right
      exact hx
  unbounded_above := by
    intro a
    obtain ⟨i, hi⟩ := (tendsto_atTop_atTop.mp P.cutPoint_tendsto_atTop) (a + c)
    refine ⟨P.cutPoint (i + 1) - c, Or.inl ⟨i + 1, by ring⟩, ?_⟩
    have hii : P.cutPoint i < P.cutPoint (i + 1) :=
      P.cutPoint_strictMono (by omega)
    linarith [hi i le_rfl]
  unbounded_below := by
    intro b
    obtain ⟨i, hi⟩ := (tendsto_atBot_atBot.mp P.cutPoint_tendsto_atBot) (b + c)
    refine ⟨P.cutPoint (i - 1) - c, Or.inl ⟨i - 1, by ring⟩, ?_⟩
    have hii : P.cutPoint (i - 1) < P.cutPoint i :=
      P.cutPoint_strictMono (by omega)
    linarith [hi i le_rfl]
  piece := fun a b _hab ↦
    (P.piece (presentationIntervalIndex P (((a : ℝ) + (b : ℝ)) / 2 + c))).comp
      (Polynomial.X + Polynomial.C c)
  piece_natDegree_le := by
    intro a b hab
    let t : ℝ := ((a : ℝ) + (b : ℝ)) / 2
    let i := presentationIntervalIndex P (t + c)
    have hlinear : (Polynomial.X + Polynomial.C c).natDegree ≤ 1 := by
      exact (Polynomial.natDegree_add_le _ _).trans (by simp)
    have hcomp :
        ((P.piece i).comp (Polynomial.X + Polynomial.C c)).natDegree ≤
          (P.piece i).natDegree * (Polynomial.X + Polynomial.C c).natDegree :=
      Polynomial.natDegree_comp_le
    calc
      ((P.piece i).comp (Polynomial.X + Polynomial.C c)).natDegree ≤
          (P.piece i).natDegree * (Polynomial.X + Polynomial.C c).natDegree := hcomp
      _ ≤ (P.piece i).natDegree * 1 :=
        Nat.mul_le_mul_left _ hlinear
      _ = (P.piece i).natDegree := by simp
      _ ≤ n := P.piece_natDegree_le i
  eq_piece := by
    intro a b hab x hxab
    let t : ℝ := ((a : ℝ) + (b : ℝ)) / 2
    let i := presentationIntervalIndex P (t + c)
    have habReal : (a : ℝ) < (b : ℝ) := hab.1
    have hat : (a : ℝ) < t := by dsimp [t]; linarith
    have htb : t < (b : ℝ) := by dsimp [t]; linarith
    have ht := presentationIntervalIndex_mem P (t + c)
    change t + c ∈ Ioc (P.cutPoint (i - 1)) (P.cutPoint i) at ht
    have hlower : P.cutPoint (i - 1) - c ≤ (a : ℝ) := by
      by_contra hnot
      have hal : (a : ℝ) < P.cutPoint (i - 1) - c := lt_of_not_ge hnot
      have hlt : P.cutPoint (i - 1) - c < t := by linarith [ht.1]
      let z : {x : ℝ // x ∈ {x | x + c ∈ P.cutSet} ∪ {0}} :=
        ⟨P.cutPoint (i - 1) - c, Or.inl ⟨i - 1, by ring⟩⟩
      exact hab.2 (show a < z from hal) (show z < b from hlt.trans htb)
    have hupper : (b : ℝ) ≤ P.cutPoint i - c := by
      by_contra hnot
      have hub : P.cutPoint i - c < (b : ℝ) := lt_of_not_ge hnot
      have htu : t ≤ P.cutPoint i - c := by linarith [ht.2]
      let z : {x : ℝ // x ∈ {x | x + c ∈ P.cutSet} ∪ {0}} :=
        ⟨P.cutPoint i - c, Or.inl ⟨i, by ring⟩⟩
      exact hab.2 (show a < z from hat.trans_le htu) (show z < b from hub)
    have hxcuts : x + c ∈ Icc (P.cutPoint (i - 1)) (P.cutPoint i) :=
      ⟨by linarith [hlower, hxab.1], by linarith [hupper, hxab.2]⟩
    change f (x + c) =
      ((P.piece i).comp (Polynomial.X + Polynomial.C c)).eval x
    rw [P.eq_piece i hxcuts]
    simp [Polynomial.eval_comp]

/-- Translation preserves the ambient polynomial order bound. -/
def translateRealization {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (c : ℝ) :
    NthTropicalMeromorphicRealization n (fun x ↦ f (x + c)) := by
  let M := f.presentation.translateCutModel c
  exact
    { order := M.toPresentationLE.exactOrder
      order_le := M.toNthTropicalMeromorphicFunction_order_le
      function := M.toNthTropicalMeromorphicFunction
        (f.continuous.comp (continuous_id.add continuous_const))
      eq_fun := fun _ ↦ rfl }

/-- The union of two presentation cut sets, carrying the sum polynomial on
each consecutive interval. -/
def PolynomialPresentation.addCutModel
    {n k : ℕ} {f g : ℝ → ℝ}
    (P : PolynomialPresentation n f) (Q : PolynomialPresentation k g) :
    PolynomialCutModelLE (max n k) (fun x ↦ f x + g x) where
  cutSet := P.cutSet ∪ Q.cutSet
  zero_mem := Or.inl ⟨0, P.cutPoint_zero⟩
  finite_Icc := by
    intro a b
    rw [Set.union_inter_distrib_right]
    exact (P.finite_cutSet_inter_Icc a b).union (Q.finite_cutSet_inter_Icc a b)
  unbounded_above := by
    intro a
    obtain ⟨i, hi⟩ := (tendsto_atTop_atTop.mp P.cutPoint_tendsto_atTop) a
    refine ⟨P.cutPoint (i + 1), Or.inl ⟨i + 1, rfl⟩, ?_⟩
    exact (hi i le_rfl).trans_lt (P.cutPoint_strictMono (by omega))
  unbounded_below := by
    intro b
    obtain ⟨i, hi⟩ := (tendsto_atBot_atBot.mp P.cutPoint_tendsto_atBot) b
    refine ⟨P.cutPoint (i - 1), Or.inl ⟨i - 1, rfl⟩, ?_⟩
    exact (P.cutPoint_strictMono (by omega)).trans_le (hi i le_rfl)
  piece := fun a b h ↦
    Classical.choose (eq_piece_on_covBy_of_cut_mem P (fun _ h ↦ Or.inl h) a b h) +
      Classical.choose (eq_piece_on_covBy_of_cut_mem Q (fun _ h ↦ Or.inr h) a b h)
  piece_natDegree_le := by
    intro a b h
    let hP := eq_piece_on_covBy_of_cut_mem P (fun _ h ↦ Or.inl h) a b h
    let hQ := eq_piece_on_covBy_of_cut_mem Q (fun _ h ↦ Or.inr h) a b h
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le_max (Classical.choose_spec hP).1 (Classical.choose_spec hQ).1)
  eq_piece := by
    intro a b h x hx
    let hP := eq_piece_on_covBy_of_cut_mem P (fun _ h ↦ Or.inl h) a b h
    let hQ := eq_piece_on_covBy_of_cut_mem Q (fun _ h ↦ Or.inr h) a b h
    rw [(Classical.choose_spec hP).2 x hx, (Classical.choose_spec hQ).2 x hx]
    simp

/-- Ordinary addition is closed in the union of the two order bounds. -/
def addRealization
    {n k : ℕ} (f : NthTropicalMeromorphicFunction n)
    (g : NthTropicalMeromorphicFunction k) :
    NthTropicalMeromorphicRealization (max n k) (fun x ↦ f x + g x) := by
  let M := f.presentation.addCutModel g.presentation
  exact
    { order := M.toPresentationLE.exactOrder
      order_le := M.toNthTropicalMeromorphicFunction_order_le
      function := M.toNthTropicalMeromorphicFunction (f.continuous.add g.continuous)
      eq_fun := fun _ ↦ rfl }

/-- Multiplying all pieces by a real scalar. -/
def PolynomialPresentation.smulCutModel
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (c : ℝ) :
    PolynomialCutModelLE n (fun x ↦ c * f x) where
  cutSet := P.cutSet
  zero_mem := ⟨0, P.cutPoint_zero⟩
  finite_Icc := P.finite_cutSet_inter_Icc
  unbounded_above := by
    intro a
    obtain ⟨i, hi⟩ := (tendsto_atTop_atTop.mp P.cutPoint_tendsto_atTop) a
    refine ⟨P.cutPoint (i + 1), ⟨i + 1, rfl⟩, ?_⟩
    exact (hi i le_rfl).trans_lt (P.cutPoint_strictMono (by omega))
  unbounded_below := by
    intro b
    obtain ⟨i, hi⟩ := (tendsto_atBot_atBot.mp P.cutPoint_tendsto_atBot) b
    refine ⟨P.cutPoint (i - 1), ⟨i - 1, rfl⟩, ?_⟩
    exact (P.cutPoint_strictMono (by omega)).trans_le (hi i le_rfl)
  piece := fun a b h ↦ Polynomial.C c *
    Classical.choose (eq_piece_on_covBy_of_cut_mem P (fun _ h ↦ h) a b h)
  piece_natDegree_le := by
    intro a b h
    let hP := eq_piece_on_covBy_of_cut_mem P (fun _ h ↦ h) a b h
    exact Polynomial.natDegree_mul_le.trans (by
      simpa using add_le_add (show (Polynomial.C c).natDegree ≤ 0 by simp)
        (Classical.choose_spec hP).1)
  eq_piece := by
    intro a b h x hx
    let hP := eq_piece_on_covBy_of_cut_mem P (fun _ h ↦ h) a b h
    rw [(Classical.choose_spec hP).2 x hx]
    simp

/-- Taking a natural power multiplies the degree bound. -/
def PolynomialPresentation.powCutModel
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (d : ℕ) :
    PolynomialCutModelLE (n * d) (fun x ↦ (f x) ^ d) where
  cutSet := P.cutSet
  zero_mem := ⟨0, P.cutPoint_zero⟩
  finite_Icc := P.finite_cutSet_inter_Icc
  unbounded_above := by
    intro a
    obtain ⟨i, hi⟩ := (tendsto_atTop_atTop.mp P.cutPoint_tendsto_atTop) a
    refine ⟨P.cutPoint (i + 1), ⟨i + 1, rfl⟩, ?_⟩
    exact (hi i le_rfl).trans_lt (P.cutPoint_strictMono (by omega))
  unbounded_below := by
    intro b
    obtain ⟨i, hi⟩ := (tendsto_atBot_atBot.mp P.cutPoint_tendsto_atBot) b
    refine ⟨P.cutPoint (i - 1), ⟨i - 1, rfl⟩, ?_⟩
    exact (P.cutPoint_strictMono (by omega)).trans_le (hi i le_rfl)
  piece := fun a b h ↦
    Classical.choose (eq_piece_on_covBy_of_cut_mem P (fun _ h ↦ h) a b h) ^ d
  piece_natDegree_le := by
    intro a b h
    let hP := eq_piece_on_covBy_of_cut_mem P (fun _ h ↦ h) a b h
    exact Polynomial.natDegree_pow_le.trans (by
      calc
        d * (Classical.choose hP).natDegree ≤ d * n :=
          Nat.mul_le_mul_left d (Classical.choose_spec hP).1
        _ = n * d := Nat.mul_comm _ _)
  eq_piece := by
    intro a b h x hx
    let hP := eq_piece_on_covBy_of_cut_mem P (fun _ h ↦ h) a b h
    rw [(Classical.choose_spec hP).2 x hx]
    simp

/-- Scalar multiplication with automatic exact-order tightening. -/
def smulRealization {n : ℕ} (c : ℝ)
    (f : NthTropicalMeromorphicFunction n) :
    NthTropicalMeromorphicRealization n (fun x ↦ c * f x) := by
  let M := f.presentation.smulCutModel c
  exact
    { order := M.toPresentationLE.exactOrder
      order_le := M.toNthTropicalMeromorphicFunction_order_le
      function := M.toNthTropicalMeromorphicFunction (continuous_const.mul f.continuous)
      eq_fun := fun _ ↦ rfl }

/-- Natural powers with automatic exact-order tightening. -/
def powRealization {n : ℕ} (f : NthTropicalMeromorphicFunction n) (d : ℕ) :
    NthTropicalMeromorphicRealization (n * d) (fun x ↦ (f x) ^ d) := by
  let M := f.presentation.powCutModel d
  exact
    { order := M.toPresentationLE.exactOrder
      order_le := M.toNthTropicalMeromorphicFunction_order_le
      function := M.toNthTropicalMeromorphicFunction (f.continuous.pow d)
      eq_fun := fun _ ↦ rfl }

namespace NthTropicalMeromorphicRealization

/-- Regard a realization under a larger ambient order bound. -/
def promote {n k : ℕ} {f : ℝ → ℝ}
    (R : NthTropicalMeromorphicRealization n f) (hnk : n ≤ k) :
    NthTropicalMeromorphicRealization k f where
  order := R.order
  order_le := R.order_le.trans hnk
  function := R.function
  eq_fun := R.eq_fun

/-- Add two realizations carrying the same ambient bound. -/
def add {n : ℕ} {f g : ℝ → ℝ}
    (R : NthTropicalMeromorphicRealization n f)
    (S : NthTropicalMeromorphicRealization n g) :
    NthTropicalMeromorphicRealization n (fun x ↦ f x + g x) := by
  let A := addRealization R.function S.function
  exact
    { order := A.order
      order_le := A.order_le.trans (max_le R.order_le S.order_le)
      function := A.function
      eq_fun := fun x ↦ by rw [A.eq_fun, R.eq_fun, S.eq_fun] }

/-- Multiply a realization by a scalar. -/
def smul {n : ℕ} {f : ℝ → ℝ}
    (R : NthTropicalMeromorphicRealization n f) (c : ℝ) :
    NthTropicalMeromorphicRealization n (fun x ↦ c * f x) := by
  let A := smulRealization c R.function
  exact
    { order := A.order
      order_le := A.order_le.trans R.order_le
      function := A.function
      eq_fun := fun x ↦ by rw [A.eq_fun, R.eq_fun] }

/-- Raise a realization to a natural power. -/
def pow {n : ℕ} {f : ℝ → ℝ}
    (R : NthTropicalMeromorphicRealization n f) (d : ℕ) :
    NthTropicalMeromorphicRealization (n * d) (fun x ↦ (f x) ^ d) := by
  let A := powRealization R.function d
  exact
    { order := A.order
      order_le := A.order_le.trans (Nat.mul_le_mul_right d R.order_le)
      function := A.function
      eq_fun := fun x ↦ by rw [A.eq_fun, R.eq_fun] }

end NthTropicalMeromorphicRealization

/-- The identically zero function, at exact order zero and under any ambient
bound. -/
def zeroRealization (n : ℕ) :
    NthTropicalMeromorphicRealization n (fun _x : ℝ ↦ 0) := by
  let P : PolynomialPresentation 0 (fun _x : ℝ ↦ 0) :=
    { cutPoint := fun i ↦ (i : ℝ)
      piece := fun _ ↦ 0
      cutPoint_strictMono := by
        intro i j hij
        change (i : ℝ) < (j : ℝ)
        exact_mod_cast hij
      cutPoint_zero := by simp
      cutPoint_tendsto_atTop := tendsto_intCast_atTop_atTop
      cutPoint_tendsto_atBot := tendsto_intCast_atBot_iff.mpr tendsto_id
      piece_natDegree_le := by simp
      eq_piece := by simp
      exists_piece_natDegree_eq := ⟨0, by simp⟩ }
  let z : NthTropicalMeromorphicFunction 0 :=
    { toFun := fun _ ↦ 0
      continuous_toFun := continuous_const
      hasPolynomialPresentation := ⟨P⟩ }
  exact
    { order := 0
      order_le := Nat.zero_le n
      function := z
      eq_fun := fun _ ↦ rfl }

/-- A constant real function, at exact order zero under any ambient bound. -/
def constantRealization (n : ℕ) (c : ℝ) :
    NthTropicalMeromorphicRealization n (fun _x : ℝ ↦ c) := by
  let P : PolynomialPresentation 0 (fun _x : ℝ ↦ c) :=
    { cutPoint := fun i ↦ (i : ℝ)
      piece := fun _ ↦ Polynomial.C c
      cutPoint_strictMono := by
        intro i j hij
        change (i : ℝ) < (j : ℝ)
        exact_mod_cast hij
      cutPoint_zero := by simp
      cutPoint_tendsto_atTop := tendsto_intCast_atTop_atTop
      cutPoint_tendsto_atBot := tendsto_intCast_atBot_iff.mpr tendsto_id
      piece_natDegree_le := by simp
      eq_piece := by simp
      exists_piece_natDegree_eq := ⟨0, by simp⟩ }
  let z : NthTropicalMeromorphicFunction 0 :=
    { toFun := fun _ ↦ c
      continuous_toFun := continuous_const
      hasPolynomialPresentation := ⟨P⟩ }
  exact
    { order := 0
      order_le := Nat.zero_le n
      function := z
      eq_fun := fun _ ↦ rfl }

/-- A finite ordinary sum of realizable functions is realizable under the
same ambient order bound. -/
def finsetSumRealization {ι : Type*} [DecidableEq ι]
    {n : ℕ} (s : Finset ι) (f : ι → ℝ → ℝ)
    (R : ∀ i, NthTropicalMeromorphicRealization n (f i)) :
    NthTropicalMeromorphicRealization n (fun x ↦ ∑ i ∈ s, f i x) := by
  classical
  let property : Finset ι → Prop := fun t ↦ Nonempty
    (NthTropicalMeromorphicRealization n (fun x ↦ ∑ i ∈ t, f i x))
  have hs : property s := by
    induction s using Finset.induction with
    | empty =>
        exact ⟨by simpa using zeroRealization n⟩
    | @insert a s ha ih =>
        exact ⟨by
          simpa [Finset.sum_insert, ha] using
            (R a).add (Classical.choice ih)⟩
  exact Classical.choice hs

/-! ## Crossing cuts for pointwise maxima -/

/-- Indices of pieces which can meet `[a,b]`; the one-index padding handles
closed endpoint overlap. -/
private def relevantPieceIndices {n : ℕ} {f : ℝ → ℝ}
    (P : PolynomialPresentation n f) (a b : ℝ) : Finset ℤ :=
  Finset.Icc (presentationIntervalIndex P a)
    (presentationIntervalIndex P b + 1)

private theorem mem_relevantPieceIndices_of_mem_interval
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f)
    {a b x : ℝ} {i : ℤ} (hx : x ∈ Icc a b)
    (hxi : x ∈ Icc (P.cutPoint (i - 1)) (P.cutPoint i)) :
    i ∈ relevantPieceIndices P a b := by
  let ia := presentationIntervalIndex P a
  let ib := presentationIntervalIndex P b
  have ha := presentationIntervalIndex_mem P a
  have hb := presentationIntervalIndex_mem P b
  change a ∈ Ioc (P.cutPoint (ia - 1)) (P.cutPoint ia) at ha
  change b ∈ Ioc (P.cutPoint (ib - 1)) (P.cutPoint ib) at hb
  simp only [relevantPieceIndices, Finset.mem_Icc]
  constructor
  · by_contra h
    have hii : i < ia := lt_of_not_ge h
    have hcut := P.cutPoint_strictMono.monotone (show i ≤ ia - 1 by omega)
    linarith [hxi.2, hx.1, ha.1]
  · by_contra h
    have hii : ib + 1 < i := lt_of_not_ge h
    have hcut := P.cutPoint_strictMono
      (show ib < i - 1 by omega)
    linarith [hb.2, hx.2, hxi.1]

/-- A genuine crossing of two nonidentical active polynomial pieces.  For an
identically zero difference, Mathlib's `rootSet` is empty, so coincident
pieces do not create infinitely many artificial cuts. -/
def PolynomialPresentation.crossingSet
    {n k : ℕ} {f g : ℝ → ℝ}
    (P : PolynomialPresentation n f) (Q : PolynomialPresentation k g) : Set ℝ :=
  {x | ∃ i j : ℤ,
    x ∈ Icc (P.cutPoint (i - 1)) (P.cutPoint i) ∧
    x ∈ Icc (Q.cutPoint (j - 1)) (Q.cutPoint j) ∧
    x ∈ (P.piece i - Q.piece j).rootSet ℝ}

theorem PolynomialPresentation.finite_crossingSet_inter_Icc
    {n k : ℕ} {f g : ℝ → ℝ}
    (P : PolynomialPresentation n f) (Q : PolynomialPresentation k g)
    (a b : ℝ) : (P.crossingSet Q ∩ Icc a b).Finite := by
  classical
  let roots (i j : ℤ) : Finset ℝ :=
    ((P.piece i - Q.piece j).rootSet ℝ).toFinite.toFinset
  let container : Finset ℝ :=
    (relevantPieceIndices P a b).biUnion fun i ↦
      (relevantPieceIndices Q a b).biUnion fun j ↦ roots i j
  apply container.finite_toSet.subset
  rintro x ⟨⟨i, j, hPi, hQj, hroot⟩, hxab⟩
  change x ∈ container
  apply Finset.mem_biUnion.mpr
  refine ⟨i, mem_relevantPieceIndices_of_mem_interval P hxab hPi, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨j, mem_relevantPieceIndices_of_mem_interval Q hxab hQj, ?_⟩
  simpa [roots] using hroot

private theorem max_eq_polynomial_on_covBy
    {n k : ℕ} {f g : ℝ → ℝ}
    (P : PolynomialPresentation n f) (Q : PolynomialPresentation k g)
    (a b : {x : ℝ // x ∈ P.cutSet ∪ Q.cutSet ∪ P.crossingSet Q})
    (hab : a ⋖ b) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ max n k ∧
      ∀ x ∈ Icc (a : ℝ) (b : ℝ), max (f x) (g x) = p.eval x := by
  let S := P.cutSet ∪ Q.cutSet ∪ P.crossingSet Q
  have hPsub : P.cutSet ⊆ S := fun _ hx ↦ Or.inl (Or.inl hx)
  have hQsub : Q.cutSet ⊆ S := fun _ hx ↦ Or.inl (Or.inr hx)
  obtain ⟨i, hiDegree, hiMem, hiEq⟩ :=
    exists_piece_index_on_covBy_of_cut_mem P hPsub a b hab
  obtain ⟨j, hjDegree, hjMem, hjEq⟩ :=
    exists_piece_index_on_covBy_of_cut_mem Q hQsub a b hab
  let p := P.piece i
  let q := Q.piece j
  let m : ℝ := ((a : ℝ) + (b : ℝ)) / 2
  have habReal : (a : ℝ) < (b : ℝ) := hab.1
  have ham : (a : ℝ) < m := by dsimp [m]; linarith
  have hmb : m < (b : ℝ) := by dsimp [m]; linarith
  have hmab : m ∈ Icc (a : ℝ) (b : ℝ) := ⟨ham.le, hmb.le⟩
  have no_positive_after_nonpositive
      (hpq : p ≠ q) (hmid : p.eval m ≤ q.eval m) :
      ∀ x ∈ Icc (a : ℝ) (b : ℝ), p.eval x ≤ q.eval x := by
    intro x hxab
    by_contra hnot
    have hxpos : 0 < (p - q).eval x := by
      simp only [Polynomial.eval_sub]
      linarith
    have hmnonpos : (p - q).eval m ≤ 0 := by
      simp only [Polynomial.eval_sub]
      linarith
    have hzero : (0 : ℝ) ∈ Set.uIcc ((p - q).eval m) ((p - q).eval x) := by
      rw [Set.mem_uIcc]
      exact Or.inl ⟨hmnonpos, hxpos.le⟩
    obtain ⟨z, hzseg, hzeval⟩ :=
      intermediate_value_uIcc (p - q).continuous.continuousOn hzero
    have hzroot : (p - q).eval z = 0 := by simpa using hzeval
    rw [Set.mem_uIcc] at hzseg
    have hzab : z ∈ Icc (a : ℝ) (b : ℝ) := by
      rcases hzseg with hz | hz
      · exact ⟨ham.le.trans hz.1, hz.2.trans hxab.2⟩
      · exact ⟨hxab.1.trans hz.1, hz.2.trans hmb.le⟩
    have haz : (a : ℝ) < z := by
      rcases hzseg with hz | hz
      · exact ham.trans_le hz.1
      · apply lt_of_le_of_ne (hxab.1.trans hz.1)
        intro hza
        have hzx : x = z := le_antisymm hz.1 (by
          rw [← hza]
          exact hxab.1)
        subst x
        linarith
    have hzb : z < (b : ℝ) := by
      rcases hzseg with hz | hz
      · apply lt_of_le_of_ne (hz.2.trans hxab.2)
        intro hzbEq
        have hzx : x = z := le_antisymm (by
          rw [hzbEq]
          exact hxab.2) hz.2
        subst x
        linarith
      · exact hz.2.trans_lt hmb
    have hzP := hiMem z hzab
    have hzQ := hjMem z hzab
    have hzRootSet : z ∈ (P.piece i - Q.piece j).rootSet ℝ := by
      have hne : P.piece i - Q.piece j ≠ 0 := sub_ne_zero.mpr (by
        simpa [p, q] using hpq)
      rw [Polynomial.mem_rootSet_of_ne hne]
      simpa [Polynomial.aeval_def, p, q] using hzroot
    let c : S := ⟨z, Or.inr ⟨i, j, hzP, hzQ, hzRootSet⟩⟩
    exact hab.2 (show a < c from haz) (show c < b from hzb)
  by_cases hpq : p = q
  · refine ⟨p, hiDegree.trans (le_max_left _ _), fun x hx ↦ ?_⟩
    rw [hiEq x hx, hjEq x hx]
    simpa [p, q, hpq]
  · by_cases hmid : p.eval m ≤ q.eval m
    · refine ⟨q, hjDegree.trans (le_max_right _ _), fun x hx ↦ ?_⟩
      rw [hiEq x hx, hjEq x hx, max_eq_right
        (no_positive_after_nonpositive hpq hmid x hx)]
    · have hreverse : q ≠ p := Ne.symm hpq
      have hmid' : q.eval m ≤ p.eval m := le_of_not_ge hmid
      have hle : ∀ x ∈ Icc (a : ℝ) (b : ℝ), q.eval x ≤ p.eval x := by
        -- Apply the preceding argument after swapping the two presentations.
        intro x hx
        by_contra hnot
        have hxpos : 0 < (q - p).eval x := by
          simp only [Polynomial.eval_sub]
          linarith
        have hmnonpos : (q - p).eval m ≤ 0 := by
          simp only [Polynomial.eval_sub]
          linarith
        have hzero : (0 : ℝ) ∈ Set.uIcc ((q - p).eval m) ((q - p).eval x) := by
          rw [Set.mem_uIcc]
          exact Or.inl ⟨hmnonpos, hxpos.le⟩
        obtain ⟨z, hzseg, hzeval⟩ :=
          intermediate_value_uIcc (q - p).continuous.continuousOn hzero
        have hzroot : (q - p).eval z = 0 := by simpa using hzeval
        rw [Set.mem_uIcc] at hzseg
        have hzab : z ∈ Icc (a : ℝ) (b : ℝ) := by
          rcases hzseg with hz | hz
          · exact ⟨ham.le.trans hz.1, hz.2.trans hx.2⟩
          · exact ⟨hx.1.trans hz.1, hz.2.trans hmb.le⟩
        have haz : (a : ℝ) < z := by
          rcases hzseg with hz | hz
          · exact ham.trans_le hz.1
          · apply lt_of_le_of_ne (hx.1.trans hz.1)
            intro hza
            have hzx : x = z := le_antisymm hz.1 (by
              rw [← hza]
              exact hx.1)
            subst x
            linarith
        have hzb : z < (b : ℝ) := by
          rcases hzseg with hz | hz
          · apply lt_of_le_of_ne (hz.2.trans hx.2)
            intro hzbEq
            have hzx : x = z := le_antisymm (by
              rw [hzbEq]
              exact hx.2) hz.2
            subst x
            linarith
          · exact hz.2.trans_lt hmb
        have hzP := hiMem z hzab
        have hzQ := hjMem z hzab
        have hzRootSet : z ∈ (P.piece i - Q.piece j).rootSet ℝ := by
          have hne : P.piece i - Q.piece j ≠ 0 := sub_ne_zero.mpr (by
            simpa [p, q] using hpq)
          rw [Polynomial.mem_rootSet_of_ne hne]
          have : (p - q).eval z = 0 := by
            simpa [Polynomial.eval_sub] using neg_eq_zero.mpr hzroot
          simpa [Polynomial.aeval_def, p, q] using this
        let c : S := ⟨z, Or.inr ⟨i, j, hzP, hzQ, hzRootSet⟩⟩
        exact hab.2 (show a < c from haz) (show c < b from hzb)
      refine ⟨p, hiDegree.trans (le_max_left _ _), fun x hx ↦ ?_⟩
      rw [hiEq x hx, hjEq x hx, max_eq_left (hle x hx)]

/-- Pointwise maximum, with all genuine polynomial crossings inserted into
the union cut set. -/
def PolynomialPresentation.maxCutModel
    {n k : ℕ} {f g : ℝ → ℝ}
    (P : PolynomialPresentation n f) (Q : PolynomialPresentation k g) :
    PolynomialCutModelLE (max n k) (fun x ↦ max (f x) (g x)) where
  cutSet := P.cutSet ∪ Q.cutSet ∪ P.crossingSet Q
  zero_mem := Or.inl (Or.inl ⟨0, P.cutPoint_zero⟩)
  finite_Icc := by
    intro a b
    rw [Set.union_inter_distrib_right, Set.union_inter_distrib_right]
    exact ((P.finite_cutSet_inter_Icc a b).union
      (Q.finite_cutSet_inter_Icc a b)).union
        (P.finite_crossingSet_inter_Icc Q a b)
  unbounded_above := by
    intro a
    obtain ⟨i, hi⟩ := (tendsto_atTop_atTop.mp P.cutPoint_tendsto_atTop) a
    refine ⟨P.cutPoint (i + 1), Or.inl (Or.inl ⟨i + 1, rfl⟩), ?_⟩
    exact (hi i le_rfl).trans_lt (P.cutPoint_strictMono (by omega))
  unbounded_below := by
    intro b
    obtain ⟨i, hi⟩ := (tendsto_atBot_atBot.mp P.cutPoint_tendsto_atBot) b
    refine ⟨P.cutPoint (i - 1), Or.inl (Or.inl ⟨i - 1, rfl⟩), ?_⟩
    exact (P.cutPoint_strictMono (by omega)).trans_le (hi i le_rfl)
  piece := fun a b h ↦ Classical.choose (max_eq_polynomial_on_covBy P Q a b h)
  piece_natDegree_le := fun a b h ↦ (Classical.choose_spec
    (max_eq_polynomial_on_covBy P Q a b h)).1
  eq_piece := fun a b h x hx ↦ (Classical.choose_spec
    (max_eq_polynomial_on_covBy P Q a b h)).2 x hx

/-- Pointwise maximum is closed, with automatic exact-order tightening. -/
def maxRealization
    {n k : ℕ} (f : NthTropicalMeromorphicFunction n)
    (g : NthTropicalMeromorphicFunction k) :
    NthTropicalMeromorphicRealization (max n k) (fun x ↦ max (f x) (g x)) := by
  let M := f.presentation.maxCutModel g.presentation
  exact
    { order := M.toPresentationLE.exactOrder
      order_le := M.toNthTropicalMeromorphicFunction_order_le
      function := M.toNthTropicalMeromorphicFunction (f.continuous.max g.continuous)
      eq_fun := fun _ ↦ rfl }

namespace NthTropicalMeromorphicRealization

/-- Pointwise maximum of two realizations under a common ambient bound. -/
def max {n : ℕ} {f g : ℝ → ℝ}
    (R : NthTropicalMeromorphicRealization n f)
    (S : NthTropicalMeromorphicRealization n g) :
    NthTropicalMeromorphicRealization n (fun x ↦ max (f x) (g x)) := by
  let A := maxRealization R.function S.function
  exact
    { order := A.order
      order_le := A.order_le.trans (max_le R.order_le S.order_le)
      function := A.function
      eq_fun := fun x ↦ by rw [A.eq_fun, R.eq_fun, S.eq_fun] }

end NthTropicalMeromorphicRealization

/-- A nonempty finite pointwise supremum of realizable functions. -/
def finsetSupRealization {ι : Type*} [DecidableEq ι]
    {n : ℕ} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ → ℝ)
    (R : ∀ i, NthTropicalMeromorphicRealization n (f i)) :
    NthTropicalMeromorphicRealization n (s.sup' hs f) := by
  classical
  let property : (ℝ → ℝ) → Prop := fun h ↦
    Nonempty (NthTropicalMeromorphicRealization n h)
  have hproperty : property (s.sup' hs f) := by
    apply Finset.sup'_induction (s := s) (f := f)
    · intro u hu v hv
      exact ⟨(Classical.choice hu).max (Classical.choice hv)⟩
    · intro i hi
      exact ⟨R i⟩
  exact Classical.choice hproperty

end

end NthTropicalNevanlinna
