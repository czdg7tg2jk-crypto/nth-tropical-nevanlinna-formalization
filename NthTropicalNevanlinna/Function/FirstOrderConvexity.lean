import NthTropicalNevanlinna.Function.PresentationClosure
import NthTropicalNevanlinna.Function.Entire
import NthTropicalNevanlinna.LogDerivative.CharacteristicMonotonicity

/-!
# First-order entirety and convexity

For continuous piecewise-linear functions, nonnegative first multiplicities
are exactly the nonnegative jumps of slope.  This file packages the standard
equivalence with convexity and derives closure of first-order entirety under
finite pointwise maxima.
-/

open Set

namespace NthTropicalNevanlinna

noncomputable section

private theorem firstMultiplicity_eq_rightJet_sub_leftJet
    (f : NthTropicalMeromorphicFunction 1) (x : ℝ) :
    multiplicity f 1 x =
      normalizedPolynomialJet (f.presentation.rightPieceAt x) 1 x -
        normalizedPolynomialJet (f.presentation.leftPieceAt x) 1 x := by
  rw [multiplicity_eq_usingPresentation f f.presentation]
  simp only [multiplicityUsingPresentation]
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [rightSign_of_neg hx, leftSign_of_nonpos hx.le]
    norm_num
  · simp [rightSign, leftSign]
  · rw [rightSign_of_nonneg hx.le, leftSign_of_pos hx]
    norm_num

private theorem shiftedPositiveSplineEventData
    {qOrder : ℕ} (f : NthTropicalMeromorphicFunction qOrder)
    (hqOrder : qOrder ≤ 1) (hf : IsTropicalEntire f) (c : ℝ) :
    PositivePolynomialSplineEventData 1 (fun x ↦ f (x + c)) := by
  intro x hx
  let t := x + c
  let p := f.presentation.leftPieceAt t
  let q := f.presentation.rightPieceAt t
  obtain ⟨a, hat, hleft⟩ := f.presentation.exists_left_germ_interval t
  obtain ⟨b, htb, hright⟩ := f.presentation.exists_right_germ_interval t
  let shift : Polynomial ℝ := Polynomial.X + Polynomial.C c
  let pShift := p.comp shift
  let qShift := q.comp shift
  have hshift : shift.natDegree ≤ 1 := by
    dsimp [shift]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (by simp) (by simp))
  refine ⟨a - c, b - c, pShift, qShift, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [t] at hat
    linarith
  · dsimp [t] at htb
    linarith
  · exact Polynomial.natDegree_comp_le.trans (by
      exact Nat.mul_le_mul
        ((f.presentation.leftPieceAt_natDegree_le t).trans hqOrder)
        hshift)
  · exact Polynomial.natDegree_comp_le.trans (by
      exact Nat.mul_le_mul
        ((f.presentation.rightPieceAt_natDegree_le t).trans hqOrder)
        hshift)
  · intro y hy
    change f (y + c) = pShift.eval y
    simp only [pShift, Polynomial.eval_comp, shift, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    have hyt : y + c ≤ t := by
      dsimp [t]
      simpa [add_comm] using add_le_add_right hy.2 c
    by_cases hytEq : y + c = t
    · rw [hytEq]
      exact (f.presentation.leftPieceAt_eval t).symm
    · have hymem : y + c ∈ Ioo a t := ⟨by linarith [hy.1], lt_of_le_of_ne hyt hytEq⟩
      exact hleft _ hymem
  · intro y hy
    change f (y + c) = qShift.eval y
    simp only [qShift, Polynomial.eval_comp, shift, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    have hymem : y + c ∈ Ioo t b := by
      dsimp [t]
      constructor <;> linarith [hy.1, hy.2]
    exact hright _ hymem
  · simp only [pShift, qShift, Polynomial.eval_comp, shift,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    have hp := f.presentation.leftPieceAt_eval t
    have hq := f.presentation.rightPieceAt_eval t
    simpa [p, q, t] using hp.trans hq.symm
  · intro l hl
    interval_cases l
    · exact le_of_eq (by
        simp only [Function.iterate_zero, id_eq]
        have hp := f.presentation.leftPieceAt_eval t
        have hq := f.presentation.rightPieceAt_eval t
        simpa [pShift, qShift, p, q, shift, t, Polynomial.eval_comp] using
          hp.trans hq.symm)
    · by_cases hqZero : qOrder = 0
      · have hpZero : p = Polynomial.C (p.coeff 0) :=
          Polynomial.eq_C_of_natDegree_le_zero (by
            simpa [hqZero] using f.presentation.leftPieceAt_natDegree_le t)
        have hqZeroPoly : q = Polynomial.C (q.coeff 0) :=
          Polynomial.eq_C_of_natDegree_le_zero (by
            simpa [hqZero] using f.presentation.rightPieceAt_natDegree_le t)
        simp only [Function.iterate_one]
        have hpShiftZero : pShift = Polynomial.C (p.coeff 0) := by
          dsimp [pShift]
          rw [hpZero]
          simp
        have hqShiftZero : qShift = Polynomial.C (q.coeff 0) := by
          dsimp [qShift]
          rw [hqZeroPoly]
          simp
        rw [hpShiftZero, hqShiftZero]
        simp
      · have hqOne : qOrder = 1 := by omega
        subst qOrder
        have hmult : 0 ≤ multiplicity f 1 t :=
          (isTropicalEntire_iff_multiplicity_nonneg f).mp hf t 1 le_rfl le_rfl
        rw [firstMultiplicity_eq_rightJet_sub_leftJet] at hmult
        simp only [normalizedPolynomialJet_eq_iterateDerivative_div,
          Function.iterate_one, Nat.factorial_one, Nat.cast_one, div_one] at hmult
        simpa [pShift, qShift, p, q, shift, Polynomial.derivative_comp] using hmult

/-- A tropical entire function of exact order at most one is convex on the
whole real line.  Exact order zero is included rather than silently promoted
to exact order one. -/
theorem convexOn_univ_of_order_le_one_entire
    {q : ℕ} (f : NthTropicalMeromorphicFunction q) (hq : q ≤ 1)
    (hf : IsTropicalEntire f) :
    ConvexOn ℝ Set.univ f := by
  rw [convexOn_iff_slope_mono_adjacent]
  refine ⟨convex_univ, ?_⟩
  intro x y z _hx _hz hxy hyz
  let c := x - 1
  let g : ℝ → ℝ := fun r ↦ f (r + c)
  have hevents := shiftedPositiveSplineEventData f hq hf c
  have hmono : MonotoneOn (iteratedLeftDeriv 1 g) (Set.Ioi 0) :=
    monotoneOn_Ioi_of_locally_monotoneOn _
      (topIteratedLeftDeriv_locallyMonotone_of_splineEventData hevents)
  have hconv := positivePolynomialSpline_convexOn (show 1 ≤ 1 by rfl) hevents hmono
  have hxpos : 0 < x - c := by dsimp [c]; linarith
  have hzpos : 0 < z - c := by dsimp [c]; linarith
  have hslope := (convexOn_iff_slope_mono_adjacent.mp hconv).2
    (x := x - c) (y := y - c) (z := z - c)
    hxpos hzpos (by linarith) (by linarith)
  rw [sub_add_cancel x c, sub_add_cancel y c, sub_add_cancel z c] at hslope
  convert hslope using 1 <;> ring

/-- Exact first order specialization of
`convexOn_univ_of_order_le_one_entire`. -/
theorem convexOn_univ_of_firstOrder_entire
    (f : NthTropicalMeromorphicFunction 1) (hf : IsTropicalEntire f) :
    ConvexOn ℝ Set.univ f :=
  convexOn_univ_of_order_le_one_entire f le_rfl hf

/-- Convexity forces the unique possible first-order jump to be
nonnegative.  The statement permits exact order zero as well. -/
theorem isTropicalEntire_of_order_le_one_of_convex
    {q : ℕ} (f : NthTropicalMeromorphicFunction q) (hq : q ≤ 1)
    (hf : ConvexOn ℝ Set.univ f) : IsTropicalEntire f := by
  rw [isTropicalEntire_iff_multiplicity_nonneg]
  intro x j hj hjq
  have hqeq : q = 1 := by omega
  subst q
  have hjeq : j = 1 := by omega
  subst j
  obtain ⟨a, hax, hleft⟩ := f.presentation.exists_left_germ_interval x
  obtain ⟨b, hxb, hright⟩ := f.presentation.exists_right_germ_interval x
  let u := (a + x) / 2
  let v := (x + b) / 2
  have hau : a < u := by dsimp [u]; linarith
  have hux : u < x := by dsimp [u]; linarith
  have hxv : x < v := by dsimp [v]; linarith
  have hvb : v < b := by dsimp [v]; linarith
  have hslope := (convexOn_iff_slope_mono_adjacent.mp hf).2
    (Set.mem_univ u) (Set.mem_univ v) hux hxv
  have hleftU := hleft u ⟨hau, hux⟩
  have hleftX := f.presentation.leftPieceAt_eval x
  have hrightX := f.presentation.rightPieceAt_eval x
  have hrightV := hright v ⟨hxv, hvb⟩
  have hslope' :
      ((f.presentation.leftPieceAt x).eval x -
          (f.presentation.leftPieceAt x).eval u) / (x - u) ≤
        ((f.presentation.rightPieceAt x).eval v -
          (f.presentation.rightPieceAt x).eval x) / (v - x) := by
    rw [hleftX, ← hleftU, ← hrightV, hrightX]
    exact hslope
  have hlinearLeft :
      ((f.presentation.leftPieceAt x).eval x -
          (f.presentation.leftPieceAt x).eval u) / (x - u) =
        normalizedPolynomialJet (f.presentation.leftPieceAt x) 1 x := by
    have hdegree := f.presentation.leftPieceAt_natDegree_le x
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdegree]
    simp [normalizedPolynomialJet_eq_iterateDerivative_div]
    field_simp [ne_of_gt (sub_pos.mpr hux)]
  have hlinearRight :
      ((f.presentation.rightPieceAt x).eval v -
          (f.presentation.rightPieceAt x).eval x) / (v - x) =
        normalizedPolynomialJet (f.presentation.rightPieceAt x) 1 x := by
    have hdegree := f.presentation.rightPieceAt_natDegree_le x
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdegree]
    simp [normalizedPolynomialJet_eq_iterateDerivative_div]
    field_simp [ne_of_gt (sub_pos.mpr hxv)]
  rw [hlinearLeft, hlinearRight] at hslope'
  rw [firstMultiplicity_eq_rightJet_sub_leftJet]
  linarith

private theorem convexOn_max_real {f g : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hg : ConvexOn ℝ Set.univ g) :
    ConvexOn ℝ Set.univ (fun x ↦ max (f x) (g x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b ha hb hab
  apply max_le
  · calc
      f (a • x + b • y) ≤ a • f x + b • f y :=
        hf.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
      _ ≤ a • max (f x) (g x) + b • max (f y) (g y) := by
        exact add_le_add
          (smul_le_smul_of_nonneg_left (le_max_left _ _) ha)
          (smul_le_smul_of_nonneg_left (le_max_left _ _) hb)
  · calc
      g (a • x + b • y) ≤ a • g x + b • g y :=
        hg.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
      _ ≤ a • max (f x) (g x) + b • max (f y) (g y) := by
        exact add_le_add
          (smul_le_smul_of_nonneg_left (le_max_right _ _) ha)
          (smul_le_smul_of_nonneg_left (le_max_right _ _) hb)

/-- Pointwise maximum of two first-order entire realizations is entire. -/
theorem maxRealization_isTropicalEntire
    {f g : ℝ → ℝ}
    (R : NthTropicalMeromorphicRealization 1 f)
    (S : NthTropicalMeromorphicRealization 1 g)
    (hR : IsTropicalEntire R.function) (hS : IsTropicalEntire S.function) :
    IsTropicalEntire (R.max S).function := by
  have hRf : ConvexOn ℝ Set.univ f := by
    have h := convexOn_univ_of_order_le_one_entire
      R.function R.order_le hR
    have heq : (R.function : ℝ → ℝ) = f := funext R.eq_fun
    simpa only [heq] using h
  have hSg : ConvexOn ℝ Set.univ g := by
    have h := convexOn_univ_of_order_le_one_entire
      S.function S.order_le hS
    have heq : (S.function : ℝ → ℝ) = g := funext S.eq_fun
    simpa only [heq] using h
  have hmax : ConvexOn ℝ Set.univ (fun x ↦ max (f x) (g x)) := by
    exact convexOn_max_real hRf hSg
  apply isTropicalEntire_of_order_le_one_of_convex
    (R.max S).function (R.max S).order_le
  have heq : ((R.max S).function : ℝ → ℝ) =
      (fun x ↦ max (f x) (g x)) := funext (R.max S).eq_fun
  simpa only [heq] using hmax

/-- Translation preserves entirety for functions of ambient order at most
one. -/
theorem translateRealization_isTropicalEntire
    {q : ℕ} (f : NthTropicalMeromorphicFunction q) (hq : q ≤ 1)
    (hf : IsTropicalEntire f) (c : ℝ) :
    IsTropicalEntire (translateRealization f c).function := by
  have hfconv : ConvexOn ℝ Set.univ f :=
    convexOn_univ_of_order_le_one_entire f hq hf
  have hshift : ConvexOn ℝ Set.univ (fun x ↦ f (x + c)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha hb hab
    have h := hfconv.2 (Set.mem_univ (x + c)) (Set.mem_univ (y + c)) ha hb hab
    have harg :
        a * (x + c) + b * (y + c) = a * x + b * y + c := by
      calc
        a * (x + c) + b * (y + c) = a * x + b * y + (a + b) * c := by ring
        _ = a * x + b * y + c := by rw [hab]; ring
    simpa only [smul_eq_mul, harg] using h
  apply isTropicalEntire_of_order_le_one_of_convex
    (translateRealization f c).function
      ((translateRealization f c).order_le.trans hq)
  have heq : ((translateRealization f c).function : ℝ → ℝ) =
      (fun x ↦ f (x + c)) := funext (translateRealization f c).eq_fun
  simpa only [heq] using hshift

/-- A finite ordinary sum of entire realizations under ambient order one is
entire. -/
theorem finsetSumRealization_isTropicalEntire
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ → ℝ)
    (R : ∀ i, NthTropicalMeromorphicRealization 1 (f i))
    (hR : ∀ i, IsTropicalEntire (R i).function) :
    IsTropicalEntire (finsetSumRealization s f R).function := by
  classical
  have hconv_i : ∀ i, ConvexOn ℝ Set.univ (f i) := by
    intro i
    have h := convexOn_univ_of_order_le_one_entire
      (R i).function (R i).order_le (hR i)
    have heq : ((R i).function : ℝ → ℝ) = f i := funext (R i).eq_fun
    simpa only [heq] using h
  have hsum : ConvexOn ℝ Set.univ (fun x ↦ ∑ i ∈ s, f i x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha hb hab
    simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    exact (hconv_i i).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  apply isTropicalEntire_of_order_le_one_of_convex
    (finsetSumRealization s f R).function
    (finsetSumRealization s f R).order_le
  have heq : ((finsetSumRealization s f R).function : ℝ → ℝ) =
      (fun x ↦ ∑ i ∈ s, f i x) :=
    funext (finsetSumRealization s f R).eq_fun
  simpa only [heq] using hsum

/-- A nonempty finite pointwise maximum of first-order entire realizations is
again entire. -/
theorem finsetSupRealization_isTropicalEntire
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ → ℝ)
    (R : ∀ i, NthTropicalMeromorphicRealization 1 (f i))
    (hR : ∀ i, IsTropicalEntire (R i).function) :
    IsTropicalEntire (finsetSupRealization s hs f R).function := by
  classical
  let property : (ℝ → ℝ) → Prop := fun h ↦ ConvexOn ℝ Set.univ h
  have hconv : property (s.sup' hs f) := by
    apply Finset.sup'_induction (s := s) (f := f)
    · intro u hu v hv
      have hmax := convexOn_max_real hu hv
      change ConvexOn ℝ Set.univ (fun x ↦ max (u x) (v x))
      exact hmax
    · intro i hi
      have h := convexOn_univ_of_order_le_one_entire
        (R i).function (R i).order_le (hR i)
      have heq : ((R i).function : ℝ → ℝ) = f i := funext (R i).eq_fun
      simpa only [heq] using h
  apply isTropicalEntire_of_order_le_one_of_convex
    (finsetSupRealization s hs f R).function
    (finsetSupRealization s hs f R).order_le
  have heq : ((finsetSupRealization s hs f R).function : ℝ → ℝ) =
      s.sup' hs f := funext (finsetSupRealization s hs f R).eq_fun
  simpa only [heq] using hconv

end

end NthTropicalNevanlinna
