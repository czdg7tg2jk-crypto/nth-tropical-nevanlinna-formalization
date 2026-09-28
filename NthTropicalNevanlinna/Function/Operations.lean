import NthTropicalNevanlinna.Function.PolynomialJet

/-!
# Elementary operations on n-th tropical meromorphic functions

Only the additive inverse is needed for the characteristic identity
`T(r,f)=T(r,-f)+f(0)`.
-/

namespace NthTropicalNevanlinna

noncomputable section

/-- Negating every polynomial piece preserves a global presentation. -/
def PolynomialPresentation.neg
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) :
    PolynomialPresentation n (fun x ↦ -f x) where
  cutPoint := P.cutPoint
  piece := fun i ↦ -P.piece i
  cutPoint_strictMono := P.cutPoint_strictMono
  cutPoint_zero := P.cutPoint_zero
  cutPoint_tendsto_atTop := P.cutPoint_tendsto_atTop
  cutPoint_tendsto_atBot := P.cutPoint_tendsto_atBot
  piece_natDegree_le := by
    intro i
    simpa using P.piece_natDegree_le i
  eq_piece := by
    intro i x hx
    simpa using congrArg Neg.neg (P.eq_piece i hx)
  exists_piece_natDegree_eq := by
    obtain ⟨i, hi⟩ := P.exists_piece_natDegree_eq
    exact ⟨i, by simpa using hi⟩

/-- Additive inverse, corresponding to tropical division `1₀ ⊘ f`. -/
noncomputable def NthTropicalMeromorphicFunction.neg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) :
    NthTropicalMeromorphicFunction n where
  toFun := fun x ↦ -f x
  continuous_toFun := f.continuous.neg
  hasPolynomialPresentation := ⟨f.presentation.neg⟩

instance {n : ℕ} : Neg (NthTropicalMeromorphicFunction n) :=
  ⟨NthTropicalMeromorphicFunction.neg⟩

@[simp]
theorem NthTropicalMeromorphicFunction.neg_apply
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (x : ℝ) :
    (-f) x = -f x := rfl

@[simp]
theorem NthTropicalMeromorphicFunction.neg_neg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : -(-f) = f := by
  ext x
  simp

@[simp]
theorem PolynomialPresentation.presentationIntervalIndex_neg
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) :
    presentationIntervalIndex P.neg x = presentationIntervalIndex P x := by
  apply presentationIntervalIndex_eq_of_mem
  simpa [PolynomialPresentation.neg] using presentationIntervalIndex_mem P x

@[simp]
theorem PolynomialPresentation.neg_leftPieceAt
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) :
    P.neg.leftPieceAt x = -P.leftPieceAt x := by
  simp only [PolynomialPresentation.leftPieceAt,
    PolynomialPresentation.presentationIntervalIndex_neg]
  rfl

@[simp]
theorem PolynomialPresentation.neg_rightPieceAt
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) :
    P.neg.rightPieceAt x = -P.rightPieceAt x := by
  simp only [PolynomialPresentation.rightPieceAt,
    PolynomialPresentation.presentationIntervalIndex_neg]
  change
    (if x = P.cutPoint (presentationIntervalIndex P x) then
        -P.piece (presentationIntervalIndex P x + 1)
      else -P.piece (presentationIntervalIndex P x)) =
      -(if x = P.cutPoint (presentationIntervalIndex P x) then
          P.piece (presentationIntervalIndex P x + 1)
        else P.piece (presentationIntervalIndex P x))
  by_cases h : x = P.cutPoint (presentationIntervalIndex P x)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- Negation reverses every higher tropical multiplicity. -/
@[simp]
theorem multiplicity_neg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (x : ℝ) :
    multiplicity (-f) j x = -multiplicity f j x := by
  rw [multiplicity_eq_usingPresentation (-f) f.presentation.neg,
    multiplicity_eq_usingPresentation f f.presentation]
  change
    rightSign x ^ (j + 1) *
          normalizedPolynomialJet (f.presentation.neg.rightPieceAt x) j x -
        leftSign x ^ (j + 1) *
          normalizedPolynomialJet (f.presentation.neg.leftPieceAt x) j x =
      -(rightSign x ^ (j + 1) *
          normalizedPolynomialJet (f.presentation.rightPieceAt x) j x -
        leftSign x ^ (j + 1) *
          normalizedPolynomialJet (f.presentation.leftPieceAt x) j x)
  rw [PolynomialPresentation.neg_rightPieceAt,
    PolynomialPresentation.neg_leftPieceAt]
  simp
  ring

@[simp]
theorem isJthRoot_neg_iff_isJthPole
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (x : ℝ) :
    IsJthRoot (-f) j x ↔ IsJthPole f j x := by
  simp [IsJthRoot, IsJthPole]

@[simp]
theorem isJthPole_neg_iff_isJthRoot
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (x : ℝ) :
    IsJthPole (-f) j x ↔ IsJthRoot f j x := by
  simp [IsJthRoot, IsJthPole]

@[simp]
theorem rootOrPoleMultiplicity_neg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (x : ℝ) :
    rootOrPoleMultiplicity (-f) j x = rootOrPoleMultiplicity f j x := by
  simp [rootOrPoleMultiplicity]

/-! ## Reflection -/

/-- Reflect a global presentation across the origin.  Because a piece with
index `i` represents `[cutPoint (i-1), cutPoint i]`, the reflected piece with
index `i` is the original piece with index `1-i`, composed with `-X`. -/
def PolynomialPresentation.reflect
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) :
    PolynomialPresentation n (fun x ↦ f (-x)) where
  cutPoint := fun i ↦ -P.cutPoint (-i)
  piece := fun i ↦ (P.piece (1 - i)).comp (-Polynomial.X)
  cutPoint_strictMono := by
    intro i j hij
    have hji : -j < -i := by omega
    have hcut := P.cutPoint_strictMono hji
    dsimp
    linarith
  cutPoint_zero := by simp [P.cutPoint_zero]
  cutPoint_tendsto_atTop := by
    have hindex : Filter.Tendsto (fun i : ℤ ↦ -i) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot
    have hcut := P.cutPoint_tendsto_atBot.comp hindex
    have hneg := Filter.tendsto_neg_atBot_atTop.comp hcut
    simpa [Function.comp_def] using hneg
  cutPoint_tendsto_atBot := by
    have hindex : Filter.Tendsto (fun i : ℤ ↦ -i) Filter.atBot Filter.atTop :=
      Filter.tendsto_neg_atBot_atTop
    have hcut := P.cutPoint_tendsto_atTop.comp hindex
    have hneg := Filter.tendsto_neg_atTop_atBot.comp hcut
    simpa [Function.comp_def] using hneg
  piece_natDegree_le := by
    intro i
    have hdegree :
        ((P.piece (1 - i)).comp (-Polynomial.X)).natDegree =
          (P.piece (1 - i)).natDegree :=
      Polynomial.natDegree_eq_of_degree_eq Polynomial.degree_comp_neg_X
    rw [hdegree]
    exact P.piece_natDegree_le (1 - i)
  eq_piece := by
    intro i x hx
    have hreflected :
        -x ∈ Set.Icc (P.cutPoint ((1 - i) - 1)) (P.cutPoint (1 - i)) := by
      constructor
      · have hindex : (1 - i) - 1 = -i := by omega
        rw [hindex]
        simpa using neg_le_neg hx.2
      · have hindex : -(i - 1) = 1 - i := by omega
        simpa only [neg_neg, hindex] using neg_le_neg hx.1
    rw [P.eq_piece (1 - i) hreflected]
    simp
  exists_piece_natDegree_eq := by
    obtain ⟨i, hi⟩ := P.exists_piece_natDegree_eq
    refine ⟨1 - i, ?_⟩
    have hindex : (1 : ℤ) - (1 - i) = i := by ring
    rw [hindex]
    exact (Polynomial.natDegree_eq_of_degree_eq
      Polynomial.degree_comp_neg_X).trans hi

/-- Reflection `x ↦ f(-x)` preserves the class of n-th tropical meromorphic
functions. -/
noncomputable def NthTropicalMeromorphicFunction.reflect
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) :
    NthTropicalMeromorphicFunction n where
  toFun := fun x ↦ f (-x)
  continuous_toFun := f.continuous.comp continuous_neg
  hasPolynomialPresentation := ⟨f.presentation.reflect⟩

@[simp]
theorem NthTropicalMeromorphicFunction.reflect_apply
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (x : ℝ) :
    f.reflect x = f (-x) := rfl

@[simp]
theorem NthTropicalMeromorphicFunction.reflect_reflect
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) :
    f.reflect.reflect = f := by
  ext x
  simp

@[simp]
theorem NthTropicalMeromorphicFunction.neg_reflect
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) :
    (-f).reflect = -f.reflect := by
  ext x
  simp

private theorem polynomial_eq_of_eqOn_openInterval
    (p q : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (h : ∀ x ∈ Set.Ioo a b, p.eval x = q.eval x) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq p q
  apply (Set.Ioo_infinite hab).mono
  intro x hx
  exact h x hx

/-- Reflection interchanges right and left polynomial germs. -/
theorem PolynomialPresentation.reflect_leftPieceAt
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) :
    P.reflect.leftPieceAt x = (P.rightPieceAt (-x)).comp (-Polynomial.X) := by
  obtain ⟨a, ha, hleft⟩ := P.reflect.exists_left_germ_interval x
  obtain ⟨b, hb, hright⟩ := P.exists_right_germ_interval (-x)
  apply polynomial_eq_of_eqOn_openInterval _ _ (max_lt ha (neg_lt.mpr hb))
  intro y hy
  have hya : y ∈ Set.Ioo a x :=
    ⟨(le_max_left _ _).trans_lt hy.1, hy.2⟩
  have hyb : -y ∈ Set.Ioo (-x) b := by
    constructor
    · linarith [hy.2]
    · have := (le_max_right a (-b)).trans_lt hy.1
      linarith
  calc
    (P.reflect.leftPieceAt x).eval y = f (-y) := (hleft y hya).symm
    _ = (P.rightPieceAt (-x)).eval (-y) := hright (-y) hyb
    _ = ((P.rightPieceAt (-x)).comp (-Polynomial.X)).eval y := by simp

/-- Reflection interchanges left and right polynomial germs. -/
theorem PolynomialPresentation.reflect_rightPieceAt
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) :
    P.reflect.rightPieceAt x = (P.leftPieceAt (-x)).comp (-Polynomial.X) := by
  obtain ⟨b, hb, hright⟩ := P.reflect.exists_right_germ_interval x
  obtain ⟨a, ha, hleft⟩ := P.exists_left_germ_interval (-x)
  apply polynomial_eq_of_eqOn_openInterval _ _ (lt_min hb (lt_neg.mpr ha))
  intro y hy
  have hyb : y ∈ Set.Ioo x b :=
    ⟨hy.1, hy.2.trans_le (min_le_left _ _)⟩
  have hya : -y ∈ Set.Ioo a (-x) := by
    constructor
    · have := hy.2.trans_le (min_le_right b (-a))
      linarith
    · linarith [hy.1]
  calc
    (P.reflect.rightPieceAt x).eval y = f (-y) := (hright y hyb).symm
    _ = (P.leftPieceAt (-x)).eval (-y) := hleft (-y) hya
    _ = ((P.leftPieceAt (-x)).comp (-Polynomial.X)).eval y := by simp

private theorem iterateDerivative_comp_neg_X
    (p : Polynomial ℝ) (j : ℕ) :
    (Polynomial.derivative^[j]) (p.comp (-Polynomial.X)) =
      (-1 : Polynomial ℝ) ^ j *
        ((Polynomial.derivative^[j]) p).comp (-Polynomial.X) := by
  induction j generalizing p with
  | zero => simp
  | succ j ih =>
      simp [Function.iterate_succ_apply, ih (Polynomial.derivative p),
        Polynomial.derivative_comp, pow_succ]

/-- The chain-rule sign for normalized polynomial jets under reflection. -/
theorem normalizedPolynomialJet_comp_neg_X
    (p : Polynomial ℝ) (j : ℕ) (x : ℝ) :
    normalizedPolynomialJet (p.comp (-Polynomial.X)) j x =
      (-1 : ℝ) ^ j * normalizedPolynomialJet p j (-x) := by
  rw [normalizedPolynomialJet_eq_iterateDerivative_div,
    normalizedPolynomialJet_eq_iterateDerivative_div,
    iterateDerivative_comp_neg_X]
  simp
  ring

/-- Reflection preserves every intrinsic tropical multiplicity after
reflecting its point. -/
@[simp]
theorem multiplicity_reflect
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ) (x : ℝ) :
    multiplicity f.reflect j x = multiplicity f j (-x) := by
  rw [multiplicity_eq_usingPresentation f.reflect f.presentation.reflect,
    multiplicity_eq_usingPresentation f f.presentation]
  change multiplicityUsingPresentation f.presentation.reflect j x =
    multiplicityUsingPresentation f.presentation j (-x)
  simp only [multiplicityUsingPresentation]
  rw [PolynomialPresentation.reflect_rightPieceAt f.presentation x,
    PolynomialPresentation.reflect_leftPieceAt f.presentation x,
    normalizedPolynomialJet_comp_neg_X,
    normalizedPolynomialJet_comp_neg_X]
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hnx : 0 < -x := by linarith
    rw [rightSign_of_neg hx, leftSign_of_nonpos hx.le,
      rightSign_of_nonneg hnx.le, leftSign_of_pos hnx]
    rcases neg_one_pow_eq_or ℝ j with hj | hj <;>
      simp [pow_succ, hj] <;> ring
  · subst x
    rcases neg_one_pow_eq_or ℝ j with hj | hj <;>
      simp [rightSign, leftSign, pow_succ, hj] <;> ring
  · have hnx : -x < 0 := by linarith
    rw [rightSign_of_nonneg hx.le, leftSign_of_pos hx,
      rightSign_of_neg hnx, leftSign_of_nonpos hnx.le]
    rcases neg_one_pow_eq_or ℝ j with hj | hj <;>
      simp [pow_succ, hj] <;> ring

end

end NthTropicalNevanlinna
