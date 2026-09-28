import NthTropicalNevanlinna.Curves.Basic
import NthTropicalNevanlinna.Function.EntireMean
import NthTropicalNevanlinna.Nevanlinna.Jensen

/-!
# Cartan characteristic and Propositions 5.2--5.4

Besides the paper's statements, Proposition 5.4 is proved first in the sharper
form with the explicit constant `F(0) - f_l(0)`.
-/

open Set Filter

namespace NthTropicalNevanlinna

noncomputable section

open scoped BigOperators

private theorem polynomial_eq_of_eqOn_Ioo_curve
    (p q : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (h : ∀ x ∈ Ioo a b, p.eval x = q.eval x) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq p q
  exact (Ioo_infinite hab).mono h

/-- Local left polynomial germs respect a pointwise additive identity, even
when the three functions have different exact orders and different cut grids. -/
theorem leftPieceAt_eq_add_of_eq_add
    {nf ng nh : ℕ}
    (f : NthTropicalMeromorphicFunction nf)
    (g : NthTropicalMeromorphicFunction ng)
    (h : NthTropicalMeromorphicFunction nh)
    (hfun : ∀ x, f x = g x + h x) (x : ℝ) :
    f.presentation.leftPieceAt x =
      g.presentation.leftPieceAt x + h.presentation.leftPieceAt x := by
  obtain ⟨af, haf, hf⟩ := f.presentation.exists_left_germ_interval x
  obtain ⟨ag, hag, hg⟩ := g.presentation.exists_left_germ_interval x
  obtain ⟨ah, hah, hh⟩ := h.presentation.exists_left_germ_interval x
  apply polynomial_eq_of_eqOn_Ioo_curve _ _ (max_lt haf (max_lt hag hah))
  intro y hy
  have hyf : y ∈ Ioo af x :=
    ⟨(le_max_left af (max ag ah)).trans_lt hy.1, hy.2⟩
  have hyg : y ∈ Ioo ag x :=
    ⟨(le_max_left ag ah |>.trans (le_max_right af (max ag ah))).trans_lt hy.1,
      hy.2⟩
  have hyh : y ∈ Ioo ah x :=
    ⟨(le_max_right ag ah |>.trans (le_max_right af (max ag ah))).trans_lt hy.1,
      hy.2⟩
  simp only [Polynomial.eval_add]
  rw [← hf y hyf, ← hg y hyg, ← hh y hyh, hfun y]

/-- Local right polynomial germs respect a pointwise additive identity. -/
theorem rightPieceAt_eq_add_of_eq_add
    {nf ng nh : ℕ}
    (f : NthTropicalMeromorphicFunction nf)
    (g : NthTropicalMeromorphicFunction ng)
    (h : NthTropicalMeromorphicFunction nh)
    (hfun : ∀ x, f x = g x + h x) (x : ℝ) :
    f.presentation.rightPieceAt x =
      g.presentation.rightPieceAt x + h.presentation.rightPieceAt x := by
  obtain ⟨bf, hbf, hf⟩ := f.presentation.exists_right_germ_interval x
  obtain ⟨bg, hbg, hg⟩ := g.presentation.exists_right_germ_interval x
  obtain ⟨bh, hbh, hh⟩ := h.presentation.exists_right_germ_interval x
  apply polynomial_eq_of_eqOn_Ioo_curve _ _ (lt_min hbf (lt_min hbg hbh))
  intro y hy
  have hyf : y ∈ Ioo x bf :=
    ⟨hy.1, hy.2.trans_le (min_le_left bf (min bg bh))⟩
  have hyg : y ∈ Ioo x bg :=
    ⟨hy.1, hy.2.trans_le
      ((min_le_right bf (min bg bh)).trans (min_le_left bg bh))⟩
  have hyh : y ∈ Ioo x bh :=
    ⟨hy.1, hy.2.trans_le
      ((min_le_right bf (min bg bh)).trans (min_le_right bg bh))⟩
  simp only [Polynomial.eval_add]
  rw [← hf y hyf, ← hg y hyg, ← hh y hyh, hfun y]

/-- Intrinsic higher multiplicity is additive under a pointwise additive
identity.  This cross-order form is the calculus lemma needed by projective
rescalings and coordinate quotients. -/
theorem multiplicity_eq_add_of_eq_add
    {nf ng nh : ℕ}
    (f : NthTropicalMeromorphicFunction nf)
    (g : NthTropicalMeromorphicFunction ng)
    (h : NthTropicalMeromorphicFunction nh)
    (hfun : ∀ x, f x = g x + h x) (j : ℕ) (x : ℝ) :
    multiplicity f j x = multiplicity g j x + multiplicity h j x := by
  simp only [multiplicity, multiplicityUsingPresentation]
  rw [leftPieceAt_eq_add_of_eq_add f g h hfun x,
    rightPieceAt_eq_add_of_eq_add f g h hfun x]
  simp only [normalizedPolynomialJet_add]
  ring

/-- Four-function form of additivity, used to compare two pointwise
projectively equivalent representations without first bundling their scalar
difference as a new meromorphic function. -/
theorem multiplicity_add_eq_add_of_fun_add_eq_add
    {na nb nc nd : ℕ}
    (a : NthTropicalMeromorphicFunction na)
    (b : NthTropicalMeromorphicFunction nb)
    (c : NthTropicalMeromorphicFunction nc)
    (d : NthTropicalMeromorphicFunction nd)
    (hfun : ∀ x, a x + b x = c x + d x) (j : ℕ) (x : ℝ) :
    multiplicity a j x + multiplicity b j x =
      multiplicity c j x + multiplicity d j x := by
  have leftGerms :
      a.presentation.leftPieceAt x + b.presentation.leftPieceAt x =
        c.presentation.leftPieceAt x + d.presentation.leftPieceAt x := by
    obtain ⟨aa, haa, ha⟩ := a.presentation.exists_left_germ_interval x
    obtain ⟨ab, hab, hb⟩ := b.presentation.exists_left_germ_interval x
    obtain ⟨ac, hac, hc⟩ := c.presentation.exists_left_germ_interval x
    obtain ⟨ad, had, hd⟩ := d.presentation.exists_left_germ_interval x
    let lower := max aa (max ab (max ac ad))
    apply polynomial_eq_of_eqOn_Ioo_curve _ _
      (show lower < x by exact max_lt haa (max_lt hab (max_lt hac had)))
    intro y hy
    have hya : y ∈ Ioo aa x :=
      ⟨(le_max_left aa _).trans_lt hy.1, hy.2⟩
    have hyb : y ∈ Ioo ab x :=
      ⟨((le_max_left ab _).trans (le_max_right aa _)).trans_lt hy.1, hy.2⟩
    have hyc : y ∈ Ioo ac x :=
      ⟨((le_max_left ac ad).trans (le_max_right ab _)
        |>.trans (le_max_right aa _)).trans_lt hy.1, hy.2⟩
    have hyd : y ∈ Ioo ad x :=
      ⟨((le_max_right ac ad).trans (le_max_right ab _)
        |>.trans (le_max_right aa _)).trans_lt hy.1, hy.2⟩
    simp only [Polynomial.eval_add]
    rw [← ha y hya, ← hb y hyb, ← hc y hyc, ← hd y hyd, hfun y]
  have rightGerms :
      a.presentation.rightPieceAt x + b.presentation.rightPieceAt x =
        c.presentation.rightPieceAt x + d.presentation.rightPieceAt x := by
    obtain ⟨ba, hba, ha⟩ := a.presentation.exists_right_germ_interval x
    obtain ⟨bb, hbb, hb⟩ := b.presentation.exists_right_germ_interval x
    obtain ⟨bc, hbc, hc⟩ := c.presentation.exists_right_germ_interval x
    obtain ⟨bd, hbd, hd⟩ := d.presentation.exists_right_germ_interval x
    let upper := min ba (min bb (min bc bd))
    apply polynomial_eq_of_eqOn_Ioo_curve _ _
      (show x < upper by exact lt_min hba (lt_min hbb (lt_min hbc hbd)))
    intro y hy
    have hya : y ∈ Ioo x ba :=
      ⟨hy.1, hy.2.trans_le (min_le_left ba _)⟩
    have hyb : y ∈ Ioo x bb :=
      ⟨hy.1, hy.2.trans_le ((min_le_right ba _).trans (min_le_left bb _))⟩
    have hyc : y ∈ Ioo x bc :=
      ⟨hy.1, hy.2.trans_le ((min_le_right ba _).trans
        ((min_le_right bb _).trans (min_le_left bc bd)))⟩
    have hyd : y ∈ Ioo x bd :=
      ⟨hy.1, hy.2.trans_le ((min_le_right ba _).trans
        ((min_le_right bb _).trans (min_le_right bc bd)))⟩
    simp only [Polynomial.eval_add]
    rw [← ha y hya, ← hb y hyb, ← hc y hyc, ← hd y hyd, hfun y]
  simp only [multiplicity, multiplicityUsingPresentation]
  have hleftJets := congrArg (fun p ↦ normalizedPolynomialJet p j x) leftGerms
  have hrightJets := congrArg (fun p ↦ normalizedPolynomialJet p j x) rightGerms
  simp only [normalizedPolynomialJet_add] at hleftJets hrightJets
  calc
    rightSign x ^ (j + 1) * normalizedPolynomialJet
          (a.presentation.rightPieceAt x) j x -
        leftSign x ^ (j + 1) * normalizedPolynomialJet
          (a.presentation.leftPieceAt x) j x +
      (rightSign x ^ (j + 1) * normalizedPolynomialJet
          (b.presentation.rightPieceAt x) j x -
        leftSign x ^ (j + 1) * normalizedPolynomialJet
          (b.presentation.leftPieceAt x) j x) =
        rightSign x ^ (j + 1) *
            (normalizedPolynomialJet (a.presentation.rightPieceAt x) j x +
              normalizedPolynomialJet (b.presentation.rightPieceAt x) j x) -
          leftSign x ^ (j + 1) *
            (normalizedPolynomialJet (a.presentation.leftPieceAt x) j x +
              normalizedPolynomialJet (b.presentation.leftPieceAt x) j x) := by ring
    _ = rightSign x ^ (j + 1) *
            (normalizedPolynomialJet (c.presentation.rightPieceAt x) j x +
              normalizedPolynomialJet (d.presentation.rightPieceAt x) j x) -
          leftSign x ^ (j + 1) *
            (normalizedPolynomialJet (c.presentation.leftPieceAt x) j x +
              normalizedPolynomialJet (d.presentation.leftPieceAt x) j x) := by
      rw [hrightJets, hleftJets]
    _ = rightSign x ^ (j + 1) * normalizedPolynomialJet
          (c.presentation.rightPieceAt x) j x -
        leftSign x ^ (j + 1) * normalizedPolynomialJet
          (c.presentation.leftPieceAt x) j x +
      (rightSign x ^ (j + 1) * normalizedPolynomialJet
          (d.presentation.rightPieceAt x) j x -
        leftSign x ^ (j + 1) * normalizedPolynomialJet
          (d.presentation.leftPieceAt x) j x) := by ring

/-- Multiplicity of a tropical quotient `numerator - denominator`. -/
theorem multiplicity_eq_sub_of_eq_sub
    {nq nn nd : ℕ}
    (q : NthTropicalMeromorphicFunction nq)
    (numerator : NthTropicalMeromorphicFunction nn)
    (denominator : NthTropicalMeromorphicFunction nd)
    (hfun : ∀ x, q x = numerator x - denominator x)
    (j : ℕ) (x : ℝ) :
    multiplicity q j x =
      multiplicity numerator j x - multiplicity denominator j x := by
  have h := multiplicity_eq_add_of_eq_add numerator q denominator
    (fun y ↦ by rw [hfun y]; ring) j x
  linarith

/-- The coordinatewise maximum `F(x)=max_i f_i(x)`. -/
def curveCoordinateMaximum {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) (x : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ↦ F.eval i x)

theorem coordinate_le_curveCoordinateMaximum {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (i : Fin (m + 1)) (x : ℝ) :
    F.eval i x ≤ curveCoordinateMaximum F x := by
  exact Finset.le_sup' (fun k ↦ F.eval k x) (Finset.mem_univ i)

/-- The tropical Cartan characteristic attached to a coordinate
representation. -/
def cartanCharacteristic {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) (r : ℝ) : ℝ :=
  (curveCoordinateMaximum F r + curveCoordinateMaximum F (-r)) / 2 -
    curveCoordinateMaximum F 0

theorem curveCoordinateMaximum_eq_add_of_rescaling {n m : ℕ}
    {F G : TropicalHolomorphicCurveRepresentation n m}
    (h : ProjectiveRescaling F G) (x : ℝ) :
    curveCoordinateMaximum F x = curveCoordinateMaximum G x + h.scalar x := by
  unfold curveCoordinateMaximum
  simp_rw [h.eq_coordinate]
  exact (Finset.sup'_add _ _ _ _).symm

/-- The common scalar between two reduced representations has no roots or
poles.  This is the omitted multiplicity calculation in Proposition 5.2. -/
theorem rescaling_scalar_isNowhereVanishingEntire {n m : ℕ}
    {F G : TropicalHolomorphicCurveRepresentation n m}
    (hF : F.IsReduced) (hG : G.IsReduced)
    (h : ProjectiveRescaling F G) :
    IsTropicalNowhereVanishingEntire h.scalar := by
  rw [isTropicalNowhereVanishingEntire_iff_multiplicity_eq_zero]
  intro x j hj hjscalar
  have hjn : j ≤ n := hjscalar.trans h.scalarOrder_le
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · apply hG x j hj hjn
    intro i
    have hFi := F.coordinate_multiplicity_nonneg i x j hj hjn
    have hadd := multiplicity_eq_add_of_eq_add
      (F.coordinate i) (G.coordinate i) h.scalar
      (h.eq_coordinate i) j x
    simp only [IsJthRoot]
    linarith
  · apply hF x j hj hjn
    intro i
    have hGi := G.coordinate_multiplicity_nonneg i x j hj hjn
    have hadd := multiplicity_eq_add_of_eq_add
      (F.coordinate i) (G.coordinate i) h.scalar
      (h.eq_coordinate i) j x
    simp only [IsJthRoot]
    linarith

/-- Proposition 5.2: the Cartan characteristic is independent of the reduced
representation. -/
theorem cartanCharacteristic_eq_of_reduced_rescaling {n m : ℕ}
    {F G : TropicalHolomorphicCurveRepresentation n m}
    (hF : F.IsReduced) (hG : G.IsReduced)
    (h : ProjectiveRescaling F G) {r : ℝ} (hr : 0 < r) :
    cartanCharacteristic F r = cartanCharacteristic G r := by
  have hscalar := rescaling_scalar_isNowhereVanishingEntire hF hG h
  have hmean := nowhereVanishingEntire_endpointMean_eq_allOrder h.scalar hscalar hr
  rw [cartanCharacteristic, cartanCharacteristic,
    curveCoordinateMaximum_eq_add_of_rescaling h r,
    curveCoordinateMaximum_eq_add_of_rescaling h (-r),
    curveCoordinateMaximum_eq_add_of_rescaling h 0]
  linarith

/-- Two entire functions have no common roots through order `n`. -/
def NoCommonRoots {n₁ n₂ : ℕ}
    (f : NthTropicalMeromorphicFunction n₁)
    (g : NthTropicalMeromorphicFunction n₂) (upTo : ℕ) : Prop :=
  ∀ x j, 1 ≤ j → j ≤ upTo →
    ¬ (IsJthRoot f j x ∧ IsJthRoot g j x)

private theorem quotient_pole_iff_denominator_root
    {nq nn nd upTo : ℕ}
    (q : NthTropicalMeromorphicFunction nq)
    (numerator : NthTropicalMeromorphicFunction nn)
    (denominator : NthTropicalMeromorphicFunction nd)
    (hnumerator : ∀ x j, 1 ≤ j → j ≤ upTo →
      0 ≤ multiplicity numerator j x)
    (hdenominator : ∀ x j, 1 ≤ j → j ≤ upTo →
      0 ≤ multiplicity denominator j x)
    (hcommon : NoCommonRoots numerator denominator upTo)
    (hquotient : ∀ x, q x = numerator x - denominator x)
    {x : ℝ} {j : ℕ} (hj : 1 ≤ j) (hju : j ≤ upTo) :
    IsJthPole q j x ↔ IsJthRoot denominator j x := by
  have hmult := multiplicity_eq_sub_of_eq_sub
    q numerator denominator hquotient j x
  have hnum := hnumerator x j hj hju
  have hden := hdenominator x j hj hju
  constructor
  · intro hpole
    simp only [IsJthPole, IsJthRoot] at hpole ⊢
    linarith
  · intro hroot
    have hnum_not_pos : ¬ 0 < multiplicity numerator j x := by
      intro hnumpos
      exact hcommon x j hj hju ⟨hnumpos, hroot⟩
    have hnumzero : multiplicity numerator j x = 0 :=
      le_antisymm (not_lt.mp hnum_not_pos) hnum
    simp only [IsJthRoot, IsJthPole] at hroot ⊢
    rw [hmult, hnumzero]
    linarith

private theorem quotient_multiplicity_abs_eq_denominator_at_root
    {nq nn nd upTo : ℕ}
    (q : NthTropicalMeromorphicFunction nq)
    (numerator : NthTropicalMeromorphicFunction nn)
    (denominator : NthTropicalMeromorphicFunction nd)
    (hnumerator : ∀ x j, 1 ≤ j → j ≤ upTo →
      0 ≤ multiplicity numerator j x)
    (hcommon : NoCommonRoots numerator denominator upTo)
    (hquotient : ∀ x, q x = numerator x - denominator x)
    {x : ℝ} {j : ℕ} (hj : 1 ≤ j) (hju : j ≤ upTo)
    (hroot : IsJthRoot denominator j x) :
    rootOrPoleMultiplicity q j x =
      rootOrPoleMultiplicity denominator j x := by
  have hnum := hnumerator x j hj hju
  have hnum_not_pos : ¬ 0 < multiplicity numerator j x := by
    intro hnumpos
    exact hcommon x j hj hju ⟨hnumpos, hroot⟩
  have hnumzero : multiplicity numerator j x = 0 :=
    le_antisymm (not_lt.mp hnum_not_pos) hnum
  have hmult := multiplicity_eq_sub_of_eq_sub
    q numerator denominator hquotient j x
  simp only [rootOrPoleMultiplicity]
  rw [hmult, hnumzero, zero_sub, abs_neg]

/-- In a reduced entire quotient, poles of the quotient are precisely roots
of its denominator, with the same multiplicities. -/
theorem integratedCounting_quotient_eq_rootCounting
    {nq nn nd upTo : ℕ}
    (q : NthTropicalMeromorphicFunction nq)
    (numerator : NthTropicalMeromorphicFunction nn)
    (denominator : NthTropicalMeromorphicFunction nd)
    (hnumerator : ∀ x j, 1 ≤ j → j ≤ upTo →
      0 ≤ multiplicity numerator j x)
    (hdenominator : ∀ x j, 1 ≤ j → j ≤ upTo →
      0 ≤ multiplicity denominator j x)
    (hcommon : NoCommonRoots numerator denominator upTo)
    (hquotient : ∀ x, q x = numerator x - denominator x)
    {j : ℕ} (hj : 1 ≤ j) (hju : j ≤ upTo) (r : ℝ) :
    integratedCounting j r q = integratedRootCounting j r denominator := by
  classical
  have hpoints : jthPolePoints q j r = jthRootPoints denominator j r := by
    ext x
    simp only [mem_jthPolePoints_iff, mem_jthRootPoints_iff]
    exact and_congr_right fun _ ↦ quotient_pole_iff_denominator_root
      q numerator denominator hnumerator hdenominator hcommon hquotient hj hju
  simp only [integratedCounting, integratedRootCounting, hpoints]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [quotient_multiplicity_abs_eq_denominator_at_root
    q numerator denominator hnumerator hcommon hquotient hj hju
    ((mem_jthRootPoints_iff.mp hx).2)]

theorem integratedCounting_eq_zero_of_entire
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (hf : IsTropicalEntire f) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) (r : ℝ) :
    integratedCounting j r f = 0 := by
  classical
  have hempty : jthPolePoints f j r = ∅ := by
    ext x
    constructor
    · intro hx
      exact (hf x j hj hjn (mem_jthPolePoints_iff.mp hx).2).elim
    · intro hx
      simp at hx
  simp [integratedCounting, hempty]

theorem entire_multiplicity_nonneg_upTo
    {k n : ℕ} (f : NthTropicalMeromorphicFunction k)
    (hf : IsTropicalEntire f) (_hkn : k ≤ n)
    (x : ℝ) (j : ℕ) (hj : 1 ≤ j) (_hjn : j ≤ n) :
    0 ≤ multiplicity f j x := by
  by_cases hjk : j ≤ k
  · exact (isTropicalEntire_iff_multiplicity_nonneg f).mp hf x j hj hjk
  · rw [multiplicity_eq_zero_of_order_lt f (lt_of_not_ge hjk) x]

/-- The heterogeneous-order two-coordinate representation `[g₀:g₁]`. -/
def projectivePairRepresentationOfOrders {n n₀ n₁ : ℕ}
    (g₀ : NthTropicalMeromorphicFunction n₀)
    (g₁ : NthTropicalMeromorphicFunction n₁)
    (hg₀ : IsTropicalEntire g₀) (hg₁ : IsTropicalEntire g₁)
    (hmax : max n₀ n₁ = n) :
    TropicalHolomorphicCurveRepresentation n 1 where
  order := Fin.cases n₀ (fun _ ↦ n₁)
  order_le := by
    intro i
    refine Fin.cases ?_ (fun _ ↦ ?_) i
    · rw [← hmax]
      exact le_max_left _ _
    · rw [← hmax]
      exact le_max_right _ _
  order_attained := by
    rcases le_total n₀ n₁ with hle | hle
    · refine ⟨1, ?_⟩
      change n₁ = n
      simpa [max_eq_right hle] using hmax
    · refine ⟨0, ?_⟩
      change n₀ = n
      simpa [max_eq_left hle] using hmax
  coordinate := Fin.cases g₀ (fun _ ↦ g₁)
  coordinate_multiplicity_nonneg := by
    intro i
    refine Fin.cases ?_ (fun _ ↦ ?_) i
    · intro x j hj hjn
      exact entire_multiplicity_nonneg_upTo g₀ hg₀
        (by rw [← hmax]; exact le_max_left _ _) x j hj hjn
    · intro x j hj hjn
      exact entire_multiplicity_nonneg_upTo g₁ hg₁
        (by rw [← hmax]; exact le_max_right _ _) x j hj hjn

@[simp] theorem projectivePairRepresentationOfOrders_coordinate_zero
    {n n₀ n₁ : ℕ}
    (g₀ : NthTropicalMeromorphicFunction n₀)
    (g₁ : NthTropicalMeromorphicFunction n₁)
    (hg₀ : IsTropicalEntire g₀) (hg₁ : IsTropicalEntire g₁)
    (hmax : max n₀ n₁ = n) :
    (projectivePairRepresentationOfOrders g₀ g₁ hg₀ hg₁ hmax).coordinate 0 = g₀ := by
  rfl

@[simp] theorem projectivePairRepresentationOfOrders_coordinate_one
    {n n₀ n₁ : ℕ}
    (g₀ : NthTropicalMeromorphicFunction n₀)
    (g₁ : NthTropicalMeromorphicFunction n₁)
    (hg₀ : IsTropicalEntire g₀) (hg₁ : IsTropicalEntire g₁)
    (hmax : max n₀ n₁ = n) :
    (projectivePairRepresentationOfOrders g₀ g₁ hg₀ hg₁ hmax).coordinate 1 = g₁ := by
  rfl

theorem curveCoordinateMaximum_projectivePairOfOrders
    {n n₀ n₁ : ℕ}
    (g₀ : NthTropicalMeromorphicFunction n₀)
    (g₁ : NthTropicalMeromorphicFunction n₁)
    (hg₀ : IsTropicalEntire g₀) (hg₁ : IsTropicalEntire g₁)
    (hmax : max n₀ n₁ = n) (x : ℝ) :
    curveCoordinateMaximum
        (projectivePairRepresentationOfOrders g₀ g₁ hg₀ hg₁ hmax) x =
      max (g₀ x) (g₁ x) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _hi
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · apply max_le
    · exact Finset.le_sup'
        (fun i ↦ (projectivePairRepresentationOfOrders
          g₀ g₁ hg₀ hg₁ hmax).eval i x) (Finset.mem_univ 0)
    · exact Finset.le_sup'
        (fun i ↦ (projectivePairRepresentationOfOrders
          g₀ g₁ hg₀ hg₁ hmax).eval i x) (Finset.mem_univ 1)

/-- The two-coordinate representation `[g₀:g₁]`. -/
def projectivePairRepresentation {n : ℕ}
    (g₀ g₁ : NthTropicalMeromorphicFunction n)
    (hg₀ : IsTropicalEntire g₀) (hg₁ : IsTropicalEntire g₁) :
    TropicalHolomorphicCurveRepresentation n 1 where
  order := fun _ ↦ n
  order_le := fun _ ↦ le_rfl
  order_attained := ⟨0, rfl⟩
  coordinate := fun i ↦ if i = 0 then g₀ else g₁
  coordinate_multiplicity_nonneg := by
    intro i x j hj hjn
    split_ifs
    · exact (isTropicalEntire_iff_multiplicity_nonneg g₀).mp hg₀ x j hj hjn
    · exact (isTropicalEntire_iff_multiplicity_nonneg g₁).mp hg₁ x j hj hjn

@[simp] theorem projectivePairRepresentation_coordinate_zero {n : ℕ}
    (g₀ g₁ : NthTropicalMeromorphicFunction n)
    (hg₀ : IsTropicalEntire g₀) (hg₁ : IsTropicalEntire g₁) :
    (projectivePairRepresentation g₀ g₁ hg₀ hg₁).coordinate 0 = g₀ := by
  simp [projectivePairRepresentation]

@[simp] theorem projectivePairRepresentation_coordinate_one {n : ℕ}
    (g₀ g₁ : NthTropicalMeromorphicFunction n)
    (hg₀ : IsTropicalEntire g₀) (hg₁ : IsTropicalEntire g₁) :
    (projectivePairRepresentation g₀ g₁ hg₀ hg₁).coordinate 1 = g₁ := by
  simp [projectivePairRepresentation]

theorem curveCoordinateMaximum_projectivePair {n : ℕ}
    (g₀ g₁ : NthTropicalMeromorphicFunction n)
    (hg₀ : IsTropicalEntire g₀) (hg₁ : IsTropicalEntire g₁) (x : ℝ) :
    curveCoordinateMaximum (projectivePairRepresentation g₀ g₁ hg₀ hg₁) x =
      max (g₀ x) (g₁ x) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _hi
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · apply max_le
    · exact Finset.le_sup'
        (fun i ↦ (projectivePairRepresentation g₀ g₁ hg₀ hg₁).eval i x)
        (Finset.mem_univ 0)
    · exact Finset.le_sup'
        (fun i ↦ (projectivePairRepresentation g₀ g₁ hg₀ hg₁).eval i x)
        (Finset.mem_univ 1)

theorem max_eq_maxPlusPositivePart_sub_add (a b : ℝ) :
    max a b = maxPlusPositivePart (b - a) + a := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    simp [maxPlusPositivePart, sub_nonneg.mpr hab]
  · rw [max_eq_left hba]
    simp [maxPlusPositivePart, sub_nonpos.mpr hba]

/-- Proposition 5.3: the Cartan characteristic of `[g₀:g₁]` agrees with
the characteristic of the reduced quotient, up to `g⁺(0)`. -/
theorem cartanCharacteristic_projectivePair_eq_characteristic_sub_fixedDegree {n : ℕ}
    (g g₀ g₁ : NthTropicalMeromorphicFunction n)
    (hg₀ : IsTropicalEntire g₀) (hg₁ : IsTropicalEntire g₁)
    (hcommon : NoCommonRoots g₁ g₀ n)
    (hquotient : ∀ x, g x = g₁ x - g₀ x)
    {r : ℝ} (hr : 0 < r) :
    cartanCharacteristic (projectivePairRepresentation g₀ g₁ hg₀ hg₁) r =
      characteristic r g - maxPlusPositivePart (g 0) := by
  have hg₀nonneg : ∀ x j, 1 ≤ j → j ≤ n → 0 ≤ multiplicity g₀ j x :=
    (isTropicalEntire_iff_multiplicity_nonneg g₀).mp hg₀
  have hg₁nonneg : ∀ x j, 1 ≤ j → j ≤ n → 0 ≤ multiplicity g₁ j x :=
    (isTropicalEntire_iff_multiplicity_nonneg g₁).mp hg₁
  have hcount :
      (∑ j ∈ Finset.Icc 1 n, integratedCounting j r g) =
        ∑ j ∈ Finset.Icc 1 n, integratedRootCounting j r g₀ := by
    apply Finset.sum_congr rfl
    intro j hj
    exact integratedCounting_quotient_eq_rootCounting
      g g₁ g₀ hg₁nonneg hg₀nonneg hcommon hquotient
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 r
  have hpoleSum :
      (∑ j ∈ Finset.Icc 1 n, integratedCounting j r g₀) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact integratedCounting_eq_zero_of_entire g₀ hg₀
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 r
  have hjensen := jensenFormula g₀ hr
  rw [jensenRootMultiplicitySum_eq g₀ hr,
    jensenPoleMultiplicitySum_eq g₀ hr, hpoleSum] at hjensen
  have hmax (x : ℝ) :
      max (g₀ x) (g₁ x) = maxPlusPositivePart (g x) + g₀ x := by
    rw [hquotient x]
    exact max_eq_maxPlusPositivePart_sub_add _ _
  rw [cartanCharacteristic,
    curveCoordinateMaximum_projectivePair g₀ g₁ hg₀ hg₁ r,
    curveCoordinateMaximum_projectivePair g₀ g₁ hg₀ hg₁ (-r),
    curveCoordinateMaximum_projectivePair g₀ g₁ hg₀ hg₁ 0,
    hmax r, hmax (-r), hmax 0,
    characteristic, proximity]
  linarith

theorem integratedRootCounting_eq_zero_of_order_lt
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {j : ℕ} (hnj : n < j) (r : ℝ) :
    integratedRootCounting j r f = 0 := by
  classical
  have hempty : jthRootPoints f j r = ∅ := by
    ext x
    constructor
    · intro hx
      have hroot := (mem_jthRootPoints_iff.mp hx).2
      simp [IsJthRoot, multiplicity_eq_zero_of_order_lt f hnj x] at hroot
    · intro hx
      simp at hx
  simp [integratedRootCounting, hempty]

theorem integratedRootCounting_eq_of_multiplicity_eq
    {nf ng : ℕ}
    (f : NthTropicalMeromorphicFunction nf)
    (g : NthTropicalMeromorphicFunction ng)
    (j : ℕ)
    (hmult : ∀ x, multiplicity f j x = multiplicity g j x)
    (r : ℝ) :
    integratedRootCounting j r f = integratedRootCounting j r g := by
  classical
  have hpoints : jthRootPoints f j r = jthRootPoints g j r := by
    ext x
    simp only [mem_jthRootPoints_iff, IsJthRoot]
    rw [hmult x]
  simp only [integratedRootCounting, hpoints]
  congr 1
  apply Finset.sum_congr rfl
  intro x _hx
  simp [rootOrPoleMultiplicity, hmult x]

theorem sum_integratedRootCounting_eq_of_order_le
    {n upTo : ℕ} (f : NthTropicalMeromorphicFunction n)
    (hnu : n ≤ upTo) (r : ℝ) :
    (∑ j ∈ Finset.Icc 1 upTo, integratedRootCounting j r f) =
      ∑ j ∈ Finset.Icc 1 n, integratedRootCounting j r f := by
  have hsubset : Finset.Icc 1 n ⊆ Finset.Icc 1 upTo := by
    intro j hj
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hnu⟩
  symm
  apply Finset.sum_subset hsubset
  intro j hjup hjn
  apply integratedRootCounting_eq_zero_of_order_lt f
  have hjn' : ¬ j ≤ n := by
    intro hle
    exact hjn (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hjup).1, hle⟩)
  exact lt_of_not_ge hjn'

/-- Extending the order-indexed root-counting sum beyond the exact degree adds
only zero terms; truncating it gives a smaller nonnegative sum. -/
theorem sum_integratedRootCounting_le_exactOrder
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (upTo : ℕ) (r : ℝ) :
    (∑ j ∈ Finset.Icc 1 upTo, integratedRootCounting j r f) ≤
      ∑ j ∈ Finset.Icc 1 n, integratedRootCounting j r f := by
  rcases le_total upTo n with hun | hnu
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hun⟩
    · intro j hj _hjsmall
      exact integratedRootCounting_nonneg j r f
  · have hsubset : Finset.Icc 1 n ⊆ Finset.Icc 1 upTo := by
      intro j hj
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hnu⟩
    have heq :
        (∑ j ∈ Finset.Icc 1 n, integratedRootCounting j r f) =
          ∑ j ∈ Finset.Icc 1 upTo, integratedRootCounting j r f := by
      apply Finset.sum_subset hsubset
      intro j hjup hjn
      apply integratedRootCounting_eq_zero_of_order_lt f
      have hjn' : ¬ j ≤ n := by
        intro hle
        exact hjn (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hjup).1, hle⟩)
      exact lt_of_not_ge hjn'
    exact heq.ge

/-- Jensen's formula for an entire function, written directly in terms of the
integrated root counts used below. -/
theorem sum_integratedRootCounting_eq_endpointMean_sub
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (hf : IsTropicalEntire f) {r : ℝ} (hr : 0 < r) :
    (∑ j ∈ Finset.Icc 1 n, integratedRootCounting j r f) =
      (f r + f (-r)) / 2 - f 0 := by
  have hpoleSum :
      (∑ j ∈ Finset.Icc 1 n, integratedCounting j r f) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact integratedCounting_eq_zero_of_entire f hf
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 r
  have hjensen := jensenFormula f hr
  rw [jensenRootMultiplicitySum_eq f hr,
    jensenPoleMultiplicitySum_eq f hr, hpoleSum] at hjensen
  linarith

/-- Without a coprimality assumption, every pole of a quotient comes from a
root of its denominator and has no larger multiplicity. -/
theorem integratedCounting_quotient_le_rootCounting
    {nq nn nd upTo : ℕ}
    (q : NthTropicalMeromorphicFunction nq)
    (numerator : NthTropicalMeromorphicFunction nn)
    (denominator : NthTropicalMeromorphicFunction nd)
    (hnumerator : ∀ x j, 1 ≤ j → j ≤ upTo →
      0 ≤ multiplicity numerator j x)
    (hdenominator : ∀ x j, 1 ≤ j → j ≤ upTo →
      0 ≤ multiplicity denominator j x)
    (hquotient : ∀ x, q x = numerator x - denominator x)
    {j : ℕ} (hj : 1 ≤ j) (hju : j ≤ upTo) (r : ℝ) :
    integratedCounting j r q ≤ integratedRootCounting j r denominator := by
  classical
  have hsubset : jthPolePoints q j r ⊆ jthRootPoints denominator j r := by
    intro x hx
    have hpole := (mem_jthPolePoints_iff.mp hx).2
    have hmult := multiplicity_eq_sub_of_eq_sub
      q numerator denominator hquotient j x
    have hnum := hnumerator x j hj hju
    have hden := hdenominator x j hj hju
    apply mem_jthRootPoints_iff.mpr
    refine ⟨(mem_jthPolePoints_iff.mp hx).1, ?_⟩
    simp only [IsJthPole, IsJthRoot] at hpole ⊢
    linarith
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    (∑ x ∈ jthPolePoints q j r,
        rootOrPoleMultiplicity q j x * (r - |x|) ^ j) ≤
        ∑ x ∈ jthPolePoints q j r,
          rootOrPoleMultiplicity denominator j x * (r - |x|) ^ j := by
      apply Finset.sum_le_sum
      intro x hx
      have hpole := (mem_jthPolePoints_iff.mp hx).2
      have hmult := multiplicity_eq_sub_of_eq_sub
        q numerator denominator hquotient j x
      have hnum := hnumerator x j hj hju
      have hden := hdenominator x j hj hju
      have hqneg : multiplicity q j x < 0 := hpole
      have hdenpos : 0 < multiplicity denominator j x := by linarith
      have habs : rootOrPoleMultiplicity q j x ≤
          rootOrPoleMultiplicity denominator j x := by
        simp only [rootOrPoleMultiplicity, abs_of_neg hqneg,
          abs_of_pos hdenpos]
        linarith
      have hxradial := (mem_jthPolePoints_iff.mp hx).1
      have hweight : 0 ≤ (r - |x|) ^ j :=
        pow_nonneg (sub_nonneg.mpr ((abs_lt.mpr hxradial).le)) j
      exact mul_le_mul_of_nonneg_right habs hweight
    _ ≤ ∑ x ∈ jthRootPoints denominator j r,
        rootOrPoleMultiplicity denominator j x * (r - |x|) ^ j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro x hxroot _hxq
      have hxradial := (mem_jthRootPoints_iff.mp hxroot).1
      exact mul_nonneg (abs_nonneg _)
        (pow_nonneg (sub_nonneg.mpr ((abs_lt.mpr hxradial).le)) j)

/-- The exact constant hidden by the `O(1)` in Proposition 5.4. -/
theorem characteristic_coordinateQuotient_le_cartan_add_constant
    {n m nq : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (i l : Fin (m + 1))
    (q : NthTropicalMeromorphicFunction nq) (hnq : nq ≤ n)
    (hquotient : ∀ x, q x = F.eval i x - F.eval l x)
    {r : ℝ} (hr : 0 < r) :
    characteristic r q ≤ cartanCharacteristic F r +
      (curveCoordinateMaximum F 0 - F.eval l 0) := by
  have hcountEach : ∀ j ∈ Finset.Icc 1 nq,
      integratedCounting j r q ≤
        integratedRootCounting j r (F.coordinate l) := by
    intro j hj
    exact integratedCounting_quotient_le_rootCounting
      q (F.coordinate i) (F.coordinate l)
      (F.coordinate_multiplicity_nonneg i)
      (F.coordinate_multiplicity_nonneg l) hquotient
      (Finset.mem_Icc.mp hj).1
      ((Finset.mem_Icc.mp hj).2.trans hnq) r
  have hcount :
      (∑ j ∈ Finset.Icc 1 nq, integratedCounting j r q) ≤
        ∑ j ∈ Finset.Icc 1 (F.order l),
          integratedRootCounting j r (F.coordinate l) := by
    calc
      (∑ j ∈ Finset.Icc 1 nq, integratedCounting j r q) ≤
          ∑ j ∈ Finset.Icc 1 nq,
            integratedRootCounting j r (F.coordinate l) := by
        exact Finset.sum_le_sum hcountEach
      _ ≤ ∑ j ∈ Finset.Icc 1 (F.order l),
          integratedRootCounting j r (F.coordinate l) :=
        sum_integratedRootCounting_le_exactOrder (F.coordinate l) nq r
  have hrootMean := sum_integratedRootCounting_eq_endpointMean_sub
    (F.coordinate l) (F.coordinate_isTropicalEntire l) hr
  change (∑ j ∈ Finset.Icc 1 (F.order l),
      integratedRootCounting j r (F.coordinate l)) =
    (F.eval l r + F.eval l (-r)) / 2 - F.eval l 0 at hrootMean
  have hprox : proximity r q =
      (max (F.eval l r) (F.eval i r) - F.eval l r +
        (max (F.eval l (-r)) (F.eval i (-r)) - F.eval l (-r))) / 2 := by
    rw [proximity]
    have hplus (x : ℝ) : maxPlusPositivePart (q x) =
        max (F.eval l x) (F.eval i x) - F.eval l x := by
      rw [hquotient x, max_eq_maxPlusPositivePart_sub_add]
      ring
    rw [hplus r, hplus (-r)]
  have hmaxr : max (F.eval l r) (F.eval i r) ≤
      curveCoordinateMaximum F r :=
    max_le (coordinate_le_curveCoordinateMaximum F l r)
      (coordinate_le_curveCoordinateMaximum F i r)
  have hmaxnr : max (F.eval l (-r)) (F.eval i (-r)) ≤
      curveCoordinateMaximum F (-r) :=
    max_le (coordinate_le_curveCoordinateMaximum F l (-r))
      (coordinate_le_curveCoordinateMaximum F i (-r))
  rw [characteristic, cartanCharacteristic, hprox]
  linarith

/-- `A(r) ≤ B(r) + O(1)` on positive radii, with the bounded term made
explicit as one uniform constant. -/
def IsLEUpToConstantOnPositiveRadii (A B : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ r, 0 < r → A r ≤ B r + C

/-- Proposition 5.4 in its original `O(1)` form.  The proof uses the stronger
explicit estimate above; reducedness and nonconstancy are retained here to
match the paper's quantifiers, although the estimate does not require them. -/
theorem characteristic_coordinateQuotient_le_upToConstant
    {n m nq : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (_hFReduced : F.IsReduced) (_hFNonconstant : F.IsNonconstant)
    (i l : Fin (m + 1))
    (q : NthTropicalMeromorphicFunction nq) (hnq : nq ≤ n)
    (hquotient : ∀ x, q x = F.eval i x - F.eval l x) :
    IsLEUpToConstantOnPositiveRadii
      (fun r ↦ characteristic r q) (fun r ↦ cartanCharacteristic F r) := by
  refine ⟨curveCoordinateMaximum F 0 - F.eval l 0, fun r hr ↦ ?_⟩
  exact characteristic_coordinateQuotient_le_cartan_add_constant
    F i l q hnq hquotient hr

/-- Proposition 5.3 with the paper's heterogeneous coordinate orders:
`max n₀ n₁ = n`, rather than the fixed-degree specialization. -/
theorem cartanCharacteristic_projectivePair_eq_characteristic_sub
    {n n₀ n₁ : ℕ}
    (g : NthTropicalMeromorphicFunction n)
    (g₀ : NthTropicalMeromorphicFunction n₀)
    (g₁ : NthTropicalMeromorphicFunction n₁)
    (hg₀ : IsTropicalEntire g₀) (hg₁ : IsTropicalEntire g₁)
    (hmax : max n₀ n₁ = n)
    (hcommon : NoCommonRoots g₁ g₀ n)
    (hquotient : ∀ x, g x = g₁ x - g₀ x)
    {r : ℝ} (hr : 0 < r) :
    cartanCharacteristic
        (projectivePairRepresentationOfOrders g₀ g₁ hg₀ hg₁ hmax) r =
      characteristic r g - maxPlusPositivePart (g 0) := by
  have hn₀ : n₀ ≤ n := by
    rw [← hmax]
    exact le_max_left _ _
  have hn₁ : n₁ ≤ n := by
    rw [← hmax]
    exact le_max_right _ _
  have hg₀nonneg : ∀ x j, 1 ≤ j → j ≤ n → 0 ≤ multiplicity g₀ j x :=
    fun x j hj hjn ↦ entire_multiplicity_nonneg_upTo
      g₀ hg₀ hn₀ x j hj hjn
  have hg₁nonneg : ∀ x j, 1 ≤ j → j ≤ n → 0 ≤ multiplicity g₁ j x :=
    fun x j hj hjn ↦ entire_multiplicity_nonneg_upTo
      g₁ hg₁ hn₁ x j hj hjn
  have hcount :
      (∑ j ∈ Finset.Icc 1 n, integratedCounting j r g) =
        ∑ j ∈ Finset.Icc 1 n, integratedRootCounting j r g₀ := by
    apply Finset.sum_congr rfl
    intro j hj
    exact integratedCounting_quotient_eq_rootCounting
      g g₁ g₀ hg₁nonneg hg₀nonneg hcommon hquotient
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 r
  have hrootMean := sum_integratedRootCounting_eq_endpointMean_sub g₀ hg₀ hr
  have hext := sum_integratedRootCounting_eq_of_order_le g₀ hn₀ r
  have hmaxValue (x : ℝ) :
      max (g₀ x) (g₁ x) = maxPlusPositivePart (g x) + g₀ x := by
    rw [hquotient x]
    exact max_eq_maxPlusPositivePart_sub_add _ _
  rw [cartanCharacteristic,
    curveCoordinateMaximum_projectivePairOfOrders g₀ g₁ hg₀ hg₁ hmax r,
    curveCoordinateMaximum_projectivePairOfOrders g₀ g₁ hg₀ hg₁ hmax (-r),
    curveCoordinateMaximum_projectivePairOfOrders g₀ g₁ hg₀ hg₁ hmax 0,
    hmaxValue r, hmaxValue (-r), hmaxValue 0,
    characteristic, proximity]
  linarith

/-- Proposition 5.2 in the paper's original quantifier form: two reduced
representations of the same projective-valued map have the same Cartan
characteristic.  No separately bundled rescaling function is assumed. -/
theorem cartanCharacteristic_eq_of_reduced_projectiveValue_eq {n m : ℕ}
    {F G : TropicalHolomorphicCurveRepresentation n m}
    (hF : F.IsReduced) (hG : G.IsReduced)
    (hprojective : ∀ x, F.projectiveValue x = G.projectiveValue x)
    {r : ℝ} (hr : 0 < r) :
    cartanCharacteristic F r = cartanCharacteristic G r := by
  let ref : Fin (m + 1) := 0
  have hcoordinateDifference (i : Fin (m + 1)) (x : ℝ) :
      F.eval i x + G.eval ref x = G.eval i x + F.eval ref x := by
    obtain ⟨c, hc⟩ := Quotient.exact (hprojective x)
    linarith [hc i, hc ref]
  have hmultiplicityDifference (i : Fin (m + 1)) (x : ℝ) (j : ℕ) :
      multiplicity (F.coordinate i) j x - multiplicity (G.coordinate i) j x =
        multiplicity (F.coordinate ref) j x -
          multiplicity (G.coordinate ref) j x := by
    have hsum := multiplicity_add_eq_add_of_fun_add_eq_add
      (F.coordinate i) (G.coordinate ref) (G.coordinate i) (F.coordinate ref)
      (hcoordinateDifference i) j x
    linarith
  have hrefMultiplicity (x : ℝ) (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
      multiplicity (F.coordinate ref) j x =
        multiplicity (G.coordinate ref) j x := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · apply hG x j hj hjn
      intro i
      have hFi := F.coordinate_multiplicity_nonneg i x j hj hjn
      have hdiff := hmultiplicityDifference i x j
      simp only [IsJthRoot]
      linarith
    · apply hF x j hj hjn
      intro i
      have hGi := G.coordinate_multiplicity_nonneg i x j hj hjn
      have hdiff := hmultiplicityDifference i x j
      simp only [IsJthRoot]
      linarith
  have hrootCounts :
      (∑ j ∈ Finset.Icc 1 n,
          integratedRootCounting j r (F.coordinate ref)) =
        ∑ j ∈ Finset.Icc 1 n,
          integratedRootCounting j r (G.coordinate ref) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact integratedRootCounting_eq_of_multiplicity_eq
      (F.coordinate ref) (G.coordinate ref) j
      (fun x ↦ hrefMultiplicity x j
        (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2) r
  have hmeanF := sum_integratedRootCounting_eq_endpointMean_sub
    (F.coordinate ref) (F.coordinate_isTropicalEntire ref) hr
  have hmeanG := sum_integratedRootCounting_eq_endpointMean_sub
    (G.coordinate ref) (G.coordinate_isTropicalEntire ref) hr
  have hextF := sum_integratedRootCounting_eq_of_order_le
    (F.coordinate ref) (F.order_le ref) r
  have hextG := sum_integratedRootCounting_eq_of_order_le
    (G.coordinate ref) (G.order_le ref) r
  change (∑ j ∈ Finset.Icc 1 (F.order ref),
      integratedRootCounting j r (F.coordinate ref)) =
    (F.eval ref r + F.eval ref (-r)) / 2 - F.eval ref 0 at hmeanF
  change (∑ j ∈ Finset.Icc 1 (G.order ref),
      integratedRootCounting j r (G.coordinate ref)) =
    (G.eval ref r + G.eval ref (-r)) / 2 - G.eval ref 0 at hmeanG
  have hrefMean :
      (F.eval ref r + F.eval ref (-r)) / 2 - F.eval ref 0 =
        (G.eval ref r + G.eval ref (-r)) / 2 - G.eval ref 0 := by
    linarith
  have hmaximum (x : ℝ) :
      curveCoordinateMaximum F x = curveCoordinateMaximum G x +
        (F.eval ref x - G.eval ref x) := by
    obtain ⟨c, hc⟩ := Quotient.exact (hprojective x)
    have hcRef := hc ref
    unfold curveCoordinateMaximum
    calc
      Finset.univ.sup' Finset.univ_nonempty (fun i ↦ F.eval i x) =
          Finset.univ.sup' Finset.univ_nonempty (fun i ↦ G.eval i x + c) := by
        congr 1
        funext i
        exact hc i
      _ = Finset.univ.sup' Finset.univ_nonempty (fun i ↦ G.eval i x) + c :=
        (Finset.sup'_add _ _ _ _).symm
      _ = Finset.univ.sup' Finset.univ_nonempty (fun i ↦ G.eval i x) +
          (F.eval ref x - G.eval ref x) := by linarith
  rw [cartanCharacteristic, cartanCharacteristic,
    hmaximum r, hmaximum (-r), hmaximum 0]
  linarith

theorem cartanCharacteristic_eq_of_reducedCurveRepresentations {n m : ℕ}
    {f : NthTropicalHolomorphicCurve n m}
    (F G : ReducedCurveRepresentation f) {r : ℝ} (hr : 0 < r) :
    cartanCharacteristic F.representation r =
      cartanCharacteristic G.representation r := by
  apply cartanCharacteristic_eq_of_reduced_projectiveValue_eq
    F.reduced G.reduced _ hr
  intro x
  exact (F.represents x).symm.trans (G.represents x)

end

end NthTropicalNevanlinna
