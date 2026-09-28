import NthTropicalNevanlinna.LogDerivative.WellDefined

/-!
# Characteristic monotonicity and convexity

This file gives the fully explicit proof of Lemma 4.4.  It formalizes the
cases at ordinary sign regions, touching zeros, and sign-changing zeros which
the paper groups under “the other cases are similar”, proves the complete
nonnegative/nondecreasing derivative tower, and derives the stated convexity
as a standard Mathlib `ConvexOn` conclusion.
-/

namespace NthTropicalNevanlinna

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The one-sided derivative used by the paper's notation `g⁽ˡ⁾(r⁻)`. -/
def leftDeriv (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  derivWithin g (Set.Iic r) r

/-- Iterated left derivative.  Order zero is the original function. -/
def iteratedLeftDeriv (l : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  leftDeriv^[l] g

/-! ## Calculus bridge for one-sided polynomial germs -/

/-- On an open interval on which a function is polynomial, its left
derivative is the ordinary derivative of that polynomial. -/
theorem leftDeriv_eq_polynomialDerivative_on_Ioo
    (g : ℝ → ℝ) (p : Polynomial ℝ) {a b x : ℝ}
    (hx : x ∈ Set.Ioo a b)
    (hgp : ∀ y ∈ Set.Ioo a b, g y = p.eval y) :
    leftDeriv g x = p.derivative.eval x := by
  have heq : Filter.EventuallyEq (nhds x) g (fun y ↦ p.eval y) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hgp y hy
  have hdiffp : DifferentiableAt ℝ (fun y ↦ p.eval y) x :=
    p.differentiableAt
  have hdiffg : DifferentiableAt ℝ g x :=
    hdiffp.congr_of_eventuallyEq heq
  rw [leftDeriv, hdiffg.derivWithin (uniqueDiffWithinAt_Iic x)]
  rw [heq.deriv_eq]
  exact (p.hasDerivAt x).deriv

/-- At the right endpoint of a left polynomial germ, `leftDeriv` takes the
derivative of the left polynomial. -/
theorem leftDeriv_eq_polynomialDerivative_on_Ioc
    (g : ℝ → ℝ) (p : Polynomial ℝ) {a x : ℝ}
    (ha : a < x)
    (hgp : ∀ y ∈ Set.Ioc a x, g y = p.eval y) :
    leftDeriv g x = p.derivative.eval x := by
  have heq : Filter.EventuallyEq
      (nhdsWithin x (Set.Iic x)) g (fun y ↦ p.eval y) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ha),
      self_mem_nhdsWithin] with y hya hyx
    exact hgp y ⟨hya, hyx⟩
  have hxEq : g x = p.eval x := hgp x ⟨ha, le_rfl⟩
  have hp : HasDerivWithinAt (fun y ↦ p.eval y) (p.derivative.eval x)
      (Set.Iic x) x := (p.hasDerivAt x).hasDerivWithinAt
  have hg := hp.congr_of_eventuallyEq heq hxEq
  exact hg.derivWithin (uniqueDiffWithinAt_Iic x)

/-- Iterating `leftDeriv` on an open polynomial interval gives the iterated
ordinary polynomial derivative. -/
theorem iteratedLeftDeriv_eq_iterateDerivative_on_Ioo
    (g : ℝ → ℝ) (p : Polynomial ℝ) {a b : ℝ}
    (hgp : ∀ y ∈ Set.Ioo a b, g y = p.eval y) (l : ℕ) :
    Set.EqOn (iteratedLeftDeriv l g)
      (fun y ↦ ((Polynomial.derivative^[l]) p).eval y) (Set.Ioo a b) := by
  induction l with
  | zero =>
      intro y hy
      exact hgp y hy
  | succ l ih =>
      intro y hy
      rw [iteratedLeftDeriv, Function.iterate_succ_apply']
      change leftDeriv (iteratedLeftDeriv l g) y = _
      have hstep := leftDeriv_eq_polynomialDerivative_on_Ioo
        (g := iteratedLeftDeriv l g)
        (p := (Polynomial.derivative^[l]) p) hy ih
      simpa only [Function.iterate_succ_apply'] using hstep

/-- The corresponding iterated statement includes the right endpoint of a
left germ.  This is the formal reason that the paper's notation really is
`T⁽ˡ⁾(r⁻)` at event radii. -/
theorem iteratedLeftDeriv_eq_iterateDerivative_on_Ioc
    (g : ℝ → ℝ) (p : Polynomial ℝ) {a x : ℝ}
    (ha : a < x)
    (hgp : ∀ y ∈ Set.Ioc a x, g y = p.eval y) (l : ℕ) :
    Set.EqOn (iteratedLeftDeriv l g)
      (fun y ↦ ((Polynomial.derivative^[l]) p).eval y) (Set.Ioc a x) := by
  induction l with
  | zero =>
      intro y hy
      exact hgp y hy
  | succ l ih =>
      intro y hy
      rw [iteratedLeftDeriv, Function.iterate_succ_apply']
      change leftDeriv (iteratedLeftDeriv l g) y = _
      have hstep := leftDeriv_eq_polynomialDerivative_on_Ioc
        (g := iteratedLeftDeriv l g)
        (p := (Polynomial.derivative^[l]) p) hy.1
        (fun z hz ↦ ih ⟨hz.1, hz.2.trans hy.2⟩)
      simpa only [Function.iterate_succ_apply'] using hstep

/-- The literal meaning of `T⁽ˡ⁾(r⁻,f)` used in Lemma 4.4. -/
def characteristicLeftDeriv
    {n : ℕ} (l : ℕ) (f : NthTropicalMeromorphicFunction n) (r : ℝ) : ℝ :=
  iteratedLeftDeriv l (fun s ↦ characteristic s f) r

@[simp]
theorem characteristicLeftDeriv_zero
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (r : ℝ) :
    characteristicLeftDeriv 0 f r = characteristic r f := rfl

/-- Local contribution of one endpoint `δa` to the jump of the `l`-th
characteristic derivative. -/
def characteristicJetJump
    (activeLeft activeRight : Bool) (uLeft uRight : ℝ) : ℝ :=
  (if activeRight then uRight else 0) / 2 -
    (if activeLeft then uLeft else 0) / 2 +
    max (uLeft - uRight) 0 / 2

theorem characteristicJetJump_active_active
    (uLeft uRight : ℝ) :
    characteristicJetJump true true uLeft uRight =
      max (uRight - uLeft) 0 / 2 := by
  simp only [characteristicJetJump, Bool.true_eq, if_true]
  rcases le_total uLeft uRight with h | h
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring

theorem characteristicJetJump_inactive_inactive
    (uLeft uRight : ℝ) :
    characteristicJetJump false false uLeft uRight =
      max (uLeft - uRight) 0 / 2 := by
  simp [characteristicJetJump]

theorem characteristicJetJump_active_active_nonneg
    (uLeft uRight : ℝ) :
    0 ≤ characteristicJetJump true true uLeft uRight := by
  rw [characteristicJetJump_active_active]
  positivity

theorem characteristicJetJump_inactive_inactive_nonneg
    (uLeft uRight : ℝ) :
    0 ≤ characteristicJetJump false false uLeft uRight := by
  rw [characteristicJetJump_inactive_inactive]
  positivity

/-- At a zero, positivity on the right forces a nonnegative right jet and
positivity on the left forces a nonpositive left jet.  Under exactly these
conditions all four omitted sign-transition cases have nonnegative jump. -/
theorem characteristicJetJump_at_zero_nonneg
    (activeLeft activeRight : Bool) (uLeft uRight : ℝ)
    (hLeft : activeLeft = true → uLeft ≤ 0)
    (hRight : activeRight = true → 0 ≤ uRight) :
    0 ≤ characteristicJetJump activeLeft activeRight uLeft uRight := by
  cases activeLeft <;> cases activeRight
  · exact characteristicJetJump_inactive_inactive_nonneg uLeft uRight
  · simp only [characteristicJetJump, Bool.false_eq_true, Bool.true_eq,
      if_false, if_true, zero_div, sub_zero]
    have hu : 0 ≤ uRight := hRight rfl
    have hm : 0 ≤ max (uLeft - uRight) 0 := le_max_right _ _
    linarith
  · simp only [characteristicJetJump, Bool.false_eq_true, Bool.true_eq,
      if_true, if_false, zero_div, zero_sub]
    have hu : uLeft ≤ 0 := hLeft rfl
    have hm : 0 ≤ max (uLeft - uRight) 0 := le_max_right _ _
    linarith
  · exact characteristicJetJump_active_active_nonneg uLeft uRight

/-- Coefficient of `r^j` in the initial expansion of the characteristic near
the origin. -/
def characteristicInitialCoefficient
    (activePositive activeNegative : Bool) (a b : ℝ) (jFactorial : ℝ) : ℝ :=
  ((if activePositive then a else 0) +
      (if activeNegative then b else 0) + max (-(a + b)) 0) /
    (2 * jFactorial)

theorem characteristicInitialCoefficient_nonneg
    (activePositive activeNegative : Bool) (a b jFactorial : ℝ)
    (hj : 0 < jFactorial)
    (hPositive : activePositive = true → 0 ≤ a)
    (hNegative : activeNegative = true → 0 ≤ b) :
    0 ≤ characteristicInitialCoefficient
      activePositive activeNegative a b jFactorial := by
  apply div_nonneg
  · apply add_nonneg
    · exact add_nonneg
        (by cases activePositive <;> simp [hPositive])
        (by cases activeNegative <;> simp [hNegative])
    · exact le_max_right _ _
  · positivity

/-- If both endpoint germs have the sign of the common value at zero, the
initial coefficient reduces to the positive or negative part of `a+b`. -/
theorem characteristicInitialCoefficient_sameSign_nonneg
    (positiveAtZero : Bool) (a b jFactorial : ℝ) (hj : 0 < jFactorial) :
    0 ≤ characteristicInitialCoefficient
      positiveAtZero positiveAtZero a b jFactorial := by
  cases positiveAtZero
  · simp only [characteristicInitialCoefficient, Bool.false_eq_true,
      if_false, zero_add]
    apply div_nonneg (le_max_right _ _)
    positivity
  · simp only [characteristicInitialCoefficient, Bool.true_eq, if_true]
    rcases le_total 0 (a + b) with h | h
    · rw [max_eq_right (neg_nonpos.mpr h)]
      positivity
    · rw [max_eq_left (neg_nonneg.mpr h)]
      ring_nf
      positivity

/-- The order-zero nonnegativity part of Lemma 4.4 holds without the
well-defined hypothesis. -/
theorem characteristicLeftDeriv_zero_nonneg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (r : ℝ) :
    0 ≤ characteristicLeftDeriv 0 f r := by
  rw [characteristicLeftDeriv_zero]
  exact characteristic_nonneg r f

/-- Nonnegativity assertion in Lemma 4.4, kept as a named formal target. -/
def CharacteristicLeftDerivativesNonnegative
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Prop :=
  ∀ l : ℕ, l ≤ n → ∀ r : ℝ, 0 < r →
    0 ≤ characteristicLeftDeriv l f r

/-- Monotonicity assertion in Lemma 4.4, kept as a named formal target. -/
def CharacteristicLeftDerivativesMonotone
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Prop :=
  ∀ l : ℕ, l ≤ n →
    MonotoneOn (characteristicLeftDeriv l f) (Set.Ioi 0)

/-- The order-zero monotonicity actually used by the displayed shift lemma. -/
def CharacteristicMonotone
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Prop :=
  MonotoneOn (fun r ↦ characteristic r f) (Set.Ioi 0)

theorem characteristicMonotone_of_leftDerivativesMonotone
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hmono : CharacteristicLeftDerivativesMonotone f) :
    CharacteristicMonotone f := by
  intro x hx y hy hxy
  have h := hmono 0 (Nat.zero_le n) hx hy hxy
  simpa only [characteristicLeftDeriv_zero] using h

theorem CharacteristicMonotone.neg
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hmono : CharacteristicMonotone f) : CharacteristicMonotone (-f) := by
  intro x hx y hy hxy
  have h := hmono hx hy hxy
  have hxJ := characteristic_eq_neg_add_at_zero f hx
  have hyJ := characteristic_eq_neg_add_at_zero f hy
  linarith

theorem CharacteristicMonotone.reflect
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hmono : CharacteristicMonotone f) : CharacteristicMonotone f.reflect := by
  intro x hx y hy hxy
  simpa only [characteristic_reflect] using hmono hx hy hxy

/-- The nonnegativity and monotonicity tower asserted by Lemma 4.4. -/
def CharacteristicAbsoluteMonotonicity
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Prop :=
  CharacteristicLeftDerivativesNonnegative f ∧
    CharacteristicLeftDerivativesMonotone f

/-- The standard Mathlib formulation of convexity of the characteristic on
the positive radius axis. -/
def CharacteristicConvex
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Prop :=
  ConvexOn ℝ (Set.Ioi 0) (fun r ↦ characteristic r f)

/-- The complete conclusion of the paper's Lemma 4.4, including its
"in particular" convexity assertion. -/
structure CharacteristicLemma44Conclusion
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Prop where
  derivativesNonnegative : CharacteristicLeftDerivativesNonnegative f
  derivativesMonotone : CharacteristicLeftDerivativesMonotone f
  convex : CharacteristicConvex f

theorem CharacteristicLemma44Conclusion.absoluteMonotonicity
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (h : CharacteristicLemma44Conclusion f) :
    CharacteristicAbsoluteMonotonicity f :=
  ⟨h.derivativesNonnegative, h.derivativesMonotone⟩

theorem CharacteristicLemma44Conclusion.characteristicMonotone
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (h : CharacteristicLemma44Conclusion f) : CharacteristicMonotone f :=
  characteristicMonotone_of_leftDerivativesMonotone h.derivativesMonotone

/-! ## Local-to-global assembly

The remaining analytic part of the paper is naturally split in two.  On a
small interval containing no new cut or polynomial zero, the jump computation
above supplies monotonicity.  The following theorem performs the independent
topological step: overlapping local monotonicity intervals on the positive
axis glue to global monotonicity.  It does not assume continuity.
-/

/-- Concrete local spline data at every positive event radius.  The function
is represented by a left and a right polynomial of degree at most `n`, and
every ordinary derivative jet has a nonnegative left-to-right jump. -/
def PositivePolynomialSplineEventData (n : ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → ∃ a b : ℝ, ∃ pLeft pRight : Polynomial ℝ,
    a < x ∧ x < b ∧
    pLeft.natDegree ≤ n ∧ pRight.natDegree ≤ n ∧
    (∀ y ∈ Set.Ioc a x, g y = pLeft.eval y) ∧
    (∀ y ∈ Set.Ioo x b, g y = pRight.eval y) ∧
    pLeft.eval x = pRight.eval x ∧
      ∀ l : ℕ, l ≤ n →
        ((Polynomial.derivative^[l]) pLeft).eval x ≤
          ((Polynomial.derivative^[l]) pRight).eval x

/-- The continuity part of the spline data, separated from the higher-order
jump inequalities for the convexity bridge. -/
def ContinuousPolynomialSplineEventData (n : ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → ∃ a b : ℝ, ∃ pLeft pRight : Polynomial ℝ,
    a < x ∧ x < b ∧
    pLeft.natDegree ≤ n ∧ pRight.natDegree ≤ n ∧
    (∀ y ∈ Set.Ioc a x, g y = pLeft.eval y) ∧
    (∀ y ∈ Set.Ioo x b, g y = pRight.eval y) ∧
    pLeft.eval x = pRight.eval x

theorem PositivePolynomialSplineEventData.continuousData
    {n : ℕ} {g : ℝ → ℝ} (h : PositivePolynomialSplineEventData n g) :
    ContinuousPolynomialSplineEventData n g := by
  intro x hx
  obtain ⟨a, b, p, q, hax, hxb, hp, hq, hleft, hright, hmatch, hjump⟩ :=
    h x hx
  exact ⟨a, b, p, q, hax, hxb, hp, hq, hleft, hright, hmatch⟩

/-- Near-origin nonnegativity data for the finite derivative tower. -/
def PositivePolynomialSplineInitialData (n : ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ l : ℕ, l ≤ n → ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ r ∈ Set.Ioo (0 : ℝ) r₀, 0 ≤ iteratedLeftDeriv l g r

/-- Subtract the affine function of slope `m`. -/
def linearTilt (g : ℝ → ℝ) (m : ℝ) : ℝ → ℝ :=
  fun r ↦ g r - m * r

/-- The affine function of slope `m` minus `g`. -/
def linearCotilt (g : ℝ → ℝ) (m : ℝ) : ℝ → ℝ :=
  fun r ↦ m * r - g r

theorem positivePolynomialSplineEventData_linearTilt
    {n : ℕ} {g : ℝ → ℝ} (hn : 1 ≤ n)
    (hevents : PositivePolynomialSplineEventData n g) (m : ℝ) :
    PositivePolynomialSplineEventData n (linearTilt g m) := by
  intro x hx
  obtain ⟨a, b, p, q, hax, hxb, hp, hq, hleft, hright, hmatch, hjump⟩ :=
    hevents x hx
  let affine : Polynomial ℝ := Polynomial.C m * Polynomial.X
  have haffine : affine.natDegree ≤ n := by
    dsimp [affine]
    apply Polynomial.natDegree_mul_le.trans
    calc
      (Polynomial.C m).natDegree + Polynomial.X.natDegree ≤ 0 + 1 := by
        gcongr <;> simp
      _ ≤ n := by simpa using hn
  have hpTilt : (p - affine).natDegree ≤ n :=
    (Polynomial.natDegree_sub_le p affine).trans (max_le hp haffine)
  have hqTilt : (q - affine).natDegree ≤ n :=
    (Polynomial.natDegree_sub_le q affine).trans (max_le hq haffine)
  refine ⟨a, b, p - affine, q - affine, hax, hxb, hpTilt, hqTilt,
    ?_, ?_, ?_, ?_⟩
  · intro y hy
    change g y - m * y = _
    rw [hleft y hy]
    simp [affine]
  · intro y hy
    change g y - m * y = _
    rw [hright y hy]
    simp [affine]
  · simp [hmatch, affine]
  · intro l hl
    have hiterateSub (u v : Polynomial ℝ) (k : ℕ) :
        (Polynomial.derivative^[k]) (u - v) =
          (Polynomial.derivative^[k]) u - (Polynomial.derivative^[k]) v := by
      induction k with
      | zero => rfl
      | succ k ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
            Function.iterate_succ_apply', ih, Polynomial.derivative_sub]
    rw [hiterateSub p affine l, hiterateSub q affine l,
      Polynomial.eval_sub, Polynomial.eval_sub]
    exact sub_le_sub_right (hjump l hl) _

theorem ContinuousPolynomialSplineEventData.linearTilt
    {n : ℕ} {g : ℝ → ℝ} (hn : 1 ≤ n)
    (hdata : ContinuousPolynomialSplineEventData n g) (m : ℝ) :
    ContinuousPolynomialSplineEventData n (linearTilt g m) := by
  intro x hx
  obtain ⟨a, b, p, q, hax, hxb, hp, hq, hleft, hright, hmatch⟩ :=
    hdata x hx
  let affine : Polynomial ℝ := Polynomial.C m * Polynomial.X
  have haffine : affine.natDegree ≤ n := by
    dsimp [affine]
    apply Polynomial.natDegree_mul_le.trans
    calc
      (Polynomial.C m).natDegree + Polynomial.X.natDegree ≤ 0 + 1 := by
        gcongr <;> simp
      _ ≤ n := by simpa using hn
  refine ⟨a, b, p - affine, q - affine, hax, hxb,
    (Polynomial.natDegree_sub_le p affine).trans (max_le hp haffine),
    (Polynomial.natDegree_sub_le q affine).trans (max_le hq haffine),
    ?_, ?_, ?_⟩
  · intro y hy
    change g y - m * y = _
    rw [hleft y hy]
    simp [affine]
  · intro y hy
    change g y - m * y = _
    rw [hright y hy]
    simp [affine]
  · simp [hmatch, affine]

theorem ContinuousPolynomialSplineEventData.linearCotilt
    {n : ℕ} {g : ℝ → ℝ} (hn : 1 ≤ n)
    (hdata : ContinuousPolynomialSplineEventData n g) (m : ℝ) :
    ContinuousPolynomialSplineEventData n (linearCotilt g m) := by
  intro x hx
  obtain ⟨a, b, p, q, hax, hxb, hp, hq, hleft, hright, hmatch⟩ :=
    hdata x hx
  let affine : Polynomial ℝ := Polynomial.C m * Polynomial.X
  have haffine : affine.natDegree ≤ n := by
    dsimp [affine]
    apply Polynomial.natDegree_mul_le.trans
    calc
      (Polynomial.C m).natDegree + Polynomial.X.natDegree ≤ 0 + 1 := by
        gcongr <;> simp
      _ ≤ n := by simpa using hn
  refine ⟨a, b, affine - p, affine - q, hax, hxb,
    (Polynomial.natDegree_sub_le affine p).trans (max_le haffine hp),
    (Polynomial.natDegree_sub_le affine q).trans (max_le haffine hq),
    ?_, ?_, ?_⟩
  · intro y hy
    change m * y - g y = _
    rw [hleft y hy]
    simp [affine]
  · intro y hy
    change m * y - g y = _
    rw [hright y hy]
    simp [affine]
  · simp [hmatch, affine]

theorem iteratedLeftDeriv_one_linearTilt
    {n : ℕ} {g : ℝ → ℝ}
    (hevents : PositivePolynomialSplineEventData n g)
    (m x : ℝ) (hx : 0 < x) :
    iteratedLeftDeriv 1 (linearTilt g m) x =
      iteratedLeftDeriv 1 g x - m := by
  obtain ⟨a, b, p, q, hax, hxb, hp, hq, hleft, hright, hmatch, hjump⟩ :=
    hevents x hx
  let affine : Polynomial ℝ := Polynomial.C m * Polynomial.X
  have htilt : ∀ y ∈ Set.Ioc a x,
      linearTilt g m y = (p - affine).eval y := by
    intro y hy
    rw [linearTilt, hleft y hy]
    simp [affine]
  rw [iteratedLeftDeriv_eq_iterateDerivative_on_Ioc g p hax hleft 1
      ⟨hax, le_rfl⟩,
    iteratedLeftDeriv_eq_iterateDerivative_on_Ioc
      (linearTilt g m) (p - affine) hax htilt 1 ⟨hax, le_rfl⟩]
  simp [affine]

theorem iteratedLeftDeriv_one_linearCotilt
    {n : ℕ} {g : ℝ → ℝ}
    (hevents : PositivePolynomialSplineEventData n g)
    (m x : ℝ) (hx : 0 < x) :
    iteratedLeftDeriv 1 (linearCotilt g m) x =
      m - iteratedLeftDeriv 1 g x := by
  obtain ⟨a, b, p, q, hax, hxb, hp, hq, hleft, hright, hmatch, hjump⟩ :=
    hevents x hx
  let affine : Polynomial ℝ := Polynomial.C m * Polynomial.X
  have hcotilt : ∀ y ∈ Set.Ioc a x,
      linearCotilt g m y = (affine - p).eval y := by
    intro y hy
    rw [linearCotilt, hleft y hy]
    simp [affine]
  rw [iteratedLeftDeriv_eq_iterateDerivative_on_Ioc g p hax hleft 1
      ⟨hax, le_rfl⟩,
    iteratedLeftDeriv_eq_iterateDerivative_on_Ioc
      (linearCotilt g m) (affine - p) hax hcotilt 1 ⟨hax, le_rfl⟩]
  simp [affine]

/-- The `n`-th derivative of a polynomial of degree at most `n` is
constant, including the lower-degree and zero-polynomial cases. -/
theorem iterateDerivative_eval_eq_of_natDegree_le
    (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n) (x y : ℝ) :
    ((Polynomial.derivative^[n]) p).eval x =
      ((Polynomial.derivative^[n]) p).eval y := by
  have hdeg : ((Polynomial.derivative^[n]) p).natDegree ≤ 0 :=
    (Polynomial.natDegree_iterate_derivative p n).trans
      (Nat.sub_eq_zero_of_le hp).le
  rw [Polynomial.eq_C_of_natDegree_le_zero hdeg]
  simp

/-- If the next iterated derivative of a polynomial is nonnegative between
two points, then its current iterated derivative increases between them. -/
theorem iterateDerivative_eval_le_of_next_nonneg
    (p : Polynomial ℝ) (l : ℕ) {u v : ℝ} (huv : u < v)
    (hnonneg : ∀ z ∈ Set.Ioo u v,
      0 ≤ ((Polynomial.derivative^[l + 1]) p).eval z) :
    ((Polynomial.derivative^[l]) p).eval u ≤
      ((Polynomial.derivative^[l]) p).eval v := by
  let q := (Polynomial.derivative^[l]) p
  have hmono : MonotoneOn (fun z ↦ q.eval z) (Set.Icc u v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc u v)
    · exact q.continuous.continuousOn
    · simpa [interior_Icc, huv.ne] using q.differentiable.differentiableOn
    · intro z hz
      rw [(q.hasDerivAt z).deriv]
      simpa [q, Function.iterate_succ_apply'] using hnonneg z (by
        simpa [interior_Icc, huv.ne] using hz)
  exact hmono (Set.left_mem_Icc.mpr huv.le)
    (Set.right_mem_Icc.mpr huv.le) huv.le

/-- The top derivative is locally monotone: it is constant on each side and
the event jet inequality orders the two constants. -/
theorem topIteratedLeftDeriv_locallyMonotone_of_splineEventData
    {n : ℕ} {g : ℝ → ℝ}
    (hevents : PositivePolynomialSplineEventData n g) :
    ∀ x ∈ Set.Ioi (0 : ℝ), ∃ a b : ℝ, a < x ∧ x < b ∧
      MonotoneOn (iteratedLeftDeriv n g) (Set.Ioo a b) := by
  intro x hx
  obtain ⟨a, b, p, q, hax, hxb, hp, hq, hleft, hright, hmatch, hjump⟩ :=
    hevents x hx
  refine ⟨a, b, hax, hxb, ?_⟩
  have hleftJet := iteratedLeftDeriv_eq_iterateDerivative_on_Ioc
    g p hax hleft n
  have hrightJet := iteratedLeftDeriv_eq_iterateDerivative_on_Ioo
    g q hright n
  intro u hu v hv huv
  by_cases hvx : v ≤ x
  · rw [hleftJet ⟨hu.1, huv.trans hvx⟩, hleftJet ⟨hv.1, hvx⟩]
    exact (iterateDerivative_eval_eq_of_natDegree_le p n hp u v).le
  by_cases hxu : x ≤ u
  · by_cases hux : u = x
    · subst u
      rw [hleftJet ⟨hax, le_rfl⟩, hrightJet ⟨lt_of_not_ge hvx, hv.2⟩]
      exact (hjump n le_rfl).trans_eq
        (iterateDerivative_eval_eq_of_natDegree_le q n hq x v)
    · have hxu' : x < u := lt_of_le_of_ne hxu (Ne.symm hux)
      rw [hrightJet ⟨hxu', hu.2⟩,
        hrightJet ⟨hxu'.trans_le huv, hv.2⟩]
      exact (iterateDerivative_eval_eq_of_natDegree_le q n hq u v).le
  · have hux : u < x := lt_of_not_ge hxu
    have hxv : x < v := lt_of_not_ge hvx
    rw [hleftJet ⟨hu.1, hux.le⟩, hrightJet ⟨hxv, hv.2⟩]
    exact (iterateDerivative_eval_eq_of_natDegree_le p n hp u x).le.trans
      ((hjump n le_rfl).trans_eq
        (iterateDerivative_eval_eq_of_natDegree_le q n hq x v))

/-- Descending step: global nonnegativity of derivative `l+1`, together
with nonnegative order-`l` event jumps, makes derivative `l` locally
monotone. -/
theorem iteratedLeftDeriv_locallyMonotone_of_next_nonnegative
    {n l : ℕ} {g : ℝ → ℝ}
    (hevents : PositivePolynomialSplineEventData n g) (hl : l ≤ n)
    (hnext : ∀ r : ℝ, 0 < r → 0 ≤ iteratedLeftDeriv (l + 1) g r) :
    ∀ x ∈ Set.Ioi (0 : ℝ), ∃ a b : ℝ, a < x ∧ x < b ∧
      MonotoneOn (iteratedLeftDeriv l g) (Set.Ioo a b) := by
  intro x hx
  obtain ⟨a, b, p, q, hax, hxb, hp, hq, hleft, hright, hmatch, hjump⟩ :=
    hevents x hx
  let a' := max a 0
  have ha'x : a' < x := max_lt hax hx
  have hleft' : ∀ y ∈ Set.Ioc a' x, g y = p.eval y := by
    intro y hy
    exact hleft y ⟨(le_max_left a 0).trans_lt hy.1, hy.2⟩
  refine ⟨a', b, ha'x, hxb, ?_⟩
  have hleftJet := iteratedLeftDeriv_eq_iterateDerivative_on_Ioc
    g p ha'x hleft' l
  have hleftNext := iteratedLeftDeriv_eq_iterateDerivative_on_Ioo
    g p (fun y hy ↦ hleft' y ⟨hy.1, hy.2.le⟩) (l + 1)
  have hrightJet := iteratedLeftDeriv_eq_iterateDerivative_on_Ioo
    g q hright l
  have hrightNext := iteratedLeftDeriv_eq_iterateDerivative_on_Ioo
    g q hright (l + 1)
  have pmono : ∀ {u v : ℝ}, u ∈ Set.Ioc a' x → v ∈ Set.Ioc a' x →
      u < v → ((Polynomial.derivative^[l]) p).eval u ≤
        ((Polynomial.derivative^[l]) p).eval v := by
    intro u v hu hv huv
    apply iterateDerivative_eval_le_of_next_nonneg p l huv
    intro z hz
    calc
      0 ≤ iteratedLeftDeriv (l + 1) g z :=
        hnext z ((le_max_right a 0).trans_lt (hu.1.trans hz.1))
      _ = ((Polynomial.derivative^[l + 1]) p).eval z :=
        hleftNext ⟨hu.1.trans hz.1, hz.2.trans_le hv.2⟩
  have qmono : ∀ {u v : ℝ}, x ≤ u → u < v → v < b →
      ((Polynomial.derivative^[l]) q).eval u ≤
        ((Polynomial.derivative^[l]) q).eval v := by
    intro u v hxu huv hvb
    apply iterateDerivative_eval_le_of_next_nonneg q l huv
    intro z hz
    have hzEq := hrightNext ⟨hxu.trans_lt hz.1, hz.2.trans hvb⟩
    calc
      0 ≤ iteratedLeftDeriv (l + 1) g z :=
        hnext z (hx.trans_le (hxu.trans hz.1.le))
      _ = ((Polynomial.derivative^[l + 1]) q).eval z := hzEq
  intro u hu v hv huv
  by_cases huvEq : u = v
  · simpa [huvEq]
  have huv' : u < v := lt_of_le_of_ne huv huvEq
  by_cases hvx : v ≤ x
  · rw [hleftJet ⟨hu.1, huv.trans hvx⟩, hleftJet ⟨hv.1, hvx⟩]
    exact pmono ⟨hu.1, huv.trans hvx⟩ ⟨hv.1, hvx⟩ huv'
  by_cases hxu : x ≤ u
  · by_cases hux : u = x
    · subst u
      rw [hleftJet ⟨ha'x, le_rfl⟩, hrightJet ⟨lt_of_not_ge hvx, hv.2⟩]
      exact (hjump l hl).trans (qmono le_rfl huv' hv.2)
    · have hxu' : x < u := lt_of_le_of_ne hxu (Ne.symm hux)
      rw [hrightJet ⟨hxu', hu.2⟩,
        hrightJet ⟨hxu'.trans_le huv, hv.2⟩]
      exact qmono hxu huv' hv.2
  · have hux : u < x := lt_of_not_ge hxu
    have hxv : x < v := lt_of_not_ge hvx
    rw [hleftJet ⟨hu.1, hux.le⟩, hrightJet ⟨hxv, hv.2⟩]
    exact (pmono ⟨hu.1, hux.le⟩ ⟨ha'x, le_rfl⟩ hux).trans
      ((hjump l hl).trans (qmono le_rfl hxv hv.2))

/-- Interval-local version of the descending step. -/
theorem iteratedLeftDeriv_locallyMonotoneOn_Ioo_of_next_nonnegative
    {n l : ℕ} {g : ℝ → ℝ} {c d : ℝ}
    (hevents : PositivePolynomialSplineEventData n g) (hl : l ≤ n)
    (hc : 0 ≤ c)
    (hnext : ∀ r ∈ Set.Ioo c d,
      0 ≤ iteratedLeftDeriv (l + 1) g r) :
    ∀ x ∈ Set.Ioo c d, ∃ a b : ℝ, a < x ∧ x < b ∧
      MonotoneOn (iteratedLeftDeriv l g) (Set.Ioo a b) := by
  intro x hx
  obtain ⟨a, b, p, q, hax, hxb, hp, hq, hleft, hright, hmatch, hjump⟩ :=
    hevents x (hc.trans_lt hx.1)
  let a' := max a c
  let b' := min b d
  have ha'x : a' < x := max_lt hax hx.1
  have hxb' : x < b' := lt_min hxb hx.2
  have hleft' : ∀ y ∈ Set.Ioc a' x, g y = p.eval y := by
    intro y hy
    exact hleft y ⟨(le_max_left a c).trans_lt hy.1, hy.2⟩
  have hright' : ∀ y ∈ Set.Ioo x b', g y = q.eval y := by
    intro y hy
    exact hright y ⟨hy.1, hy.2.trans_le (min_le_left b d)⟩
  refine ⟨a', b', ha'x, hxb', ?_⟩
  have hleftJet := iteratedLeftDeriv_eq_iterateDerivative_on_Ioc
    g p ha'x hleft' l
  have hleftNext := iteratedLeftDeriv_eq_iterateDerivative_on_Ioo
    g p (fun y hy ↦ hleft' y ⟨hy.1, hy.2.le⟩) (l + 1)
  have hrightJet := iteratedLeftDeriv_eq_iterateDerivative_on_Ioo
    g q hright' l
  have hrightNext := iteratedLeftDeriv_eq_iterateDerivative_on_Ioo
    g q hright' (l + 1)
  have pmono : ∀ {u v : ℝ}, u ∈ Set.Ioc a' x → v ∈ Set.Ioc a' x →
      u < v → ((Polynomial.derivative^[l]) p).eval u ≤
        ((Polynomial.derivative^[l]) p).eval v := by
    intro u v hu hv huv
    apply iterateDerivative_eval_le_of_next_nonneg p l huv
    intro z hz
    have hzDomain : z ∈ Set.Ioo c d := by
      constructor
      · exact (le_max_right a c).trans_lt (hu.1.trans hz.1)
      · exact (hz.2.trans_le hv.2).trans hx.2
    calc
      0 ≤ iteratedLeftDeriv (l + 1) g z := hnext z hzDomain
      _ = ((Polynomial.derivative^[l + 1]) p).eval z :=
        hleftNext ⟨hu.1.trans hz.1, hz.2.trans_le hv.2⟩
  have qmono : ∀ {u v : ℝ}, x ≤ u → u < v → v < b' →
      ((Polynomial.derivative^[l]) q).eval u ≤
        ((Polynomial.derivative^[l]) q).eval v := by
    intro u v hxu huv hvb
    apply iterateDerivative_eval_le_of_next_nonneg q l huv
    intro z hz
    have hzDomain : z ∈ Set.Ioo c d := by
      constructor
      · exact hx.1.trans_le (hxu.trans hz.1.le)
      · exact (hz.2.trans hvb).trans_le (min_le_right b d)
    calc
      0 ≤ iteratedLeftDeriv (l + 1) g z := hnext z hzDomain
      _ = ((Polynomial.derivative^[l + 1]) q).eval z :=
        hrightNext ⟨hxu.trans_lt hz.1, hz.2.trans hvb⟩
  intro u hu v hv huv
  by_cases huvEq : u = v
  · simpa [huvEq]
  have huv' : u < v := lt_of_le_of_ne huv huvEq
  by_cases hvx : v ≤ x
  · rw [hleftJet ⟨hu.1, huv.trans hvx⟩, hleftJet ⟨hv.1, hvx⟩]
    exact pmono ⟨hu.1, huv.trans hvx⟩ ⟨hv.1, hvx⟩ huv'
  by_cases hxu : x ≤ u
  · by_cases hux : u = x
    · subst u
      rw [hleftJet ⟨ha'x, le_rfl⟩, hrightJet ⟨lt_of_not_ge hvx, hv.2⟩]
      exact (hjump l hl).trans (qmono le_rfl huv' hv.2)
    · have hxu' : x < u := lt_of_le_of_ne hxu (Ne.symm hux)
      rw [hrightJet ⟨hxu', hu.2⟩,
        hrightJet ⟨hxu'.trans_le huv, hv.2⟩]
      exact qmono hxu huv' hv.2
  · have hux : u < x := lt_of_not_ge hxu
    have hxv : x < v := lt_of_not_ge hvx
    rw [hleftJet ⟨hu.1, hux.le⟩, hrightJet ⟨hxv, hv.2⟩]
    exact (pmono ⟨hu.1, hux.le⟩ ⟨ha'x, le_rfl⟩ hux).trans
      ((hjump l hl).trans (qmono le_rfl hxv hv.2))

/-- A continuous locally polynomial function is locally monotone wherever
its intrinsic left derivative is nonnegative. -/
theorem continuousPolynomialSpline_locallyMonotoneOn_Ioo_of_leftDeriv_nonnegative
    {n : ℕ} {g : ℝ → ℝ} {c d : ℝ}
    (hdata : ContinuousPolynomialSplineEventData n g) (hc : 0 ≤ c)
    (hderiv : ∀ r ∈ Set.Ioo c d, 0 ≤ iteratedLeftDeriv 1 g r) :
    ∀ x ∈ Set.Ioo c d, ∃ a b : ℝ, a < x ∧ x < b ∧
      MonotoneOn g (Set.Ioo a b) := by
  intro x hx
  obtain ⟨a, b, p, q, hax, hxb, hp, hq, hleft, hright, hmatch⟩ :=
    hdata x (hc.trans_lt hx.1)
  let a' := max a c
  let b' := min b d
  have ha'x : a' < x := max_lt hax hx.1
  have hxb' : x < b' := lt_min hxb hx.2
  have hleft' : ∀ y ∈ Set.Ioc a' x, g y = p.eval y := by
    intro y hy
    exact hleft y ⟨(le_max_left a c).trans_lt hy.1, hy.2⟩
  have hright' : ∀ y ∈ Set.Ioo x b', g y = q.eval y := by
    intro y hy
    exact hright y ⟨hy.1, hy.2.trans_le (min_le_left b d)⟩
  refine ⟨a', b', ha'x, hxb', ?_⟩
  have hleftNext := iteratedLeftDeriv_eq_iterateDerivative_on_Ioo
    g p (fun y hy ↦ hleft' y ⟨hy.1, hy.2.le⟩) 1
  have hrightNext := iteratedLeftDeriv_eq_iterateDerivative_on_Ioo
    g q hright' 1
  have pmono : ∀ {u v : ℝ}, u ∈ Set.Ioc a' x → v ∈ Set.Ioc a' x →
      u < v → p.eval u ≤ p.eval v := by
    intro u v hu hv huv
    apply iterateDerivative_eval_le_of_next_nonneg p 0 huv
    intro z hz
    have hzDomain : z ∈ Set.Ioo c d :=
      ⟨(le_max_right a c).trans_lt (hu.1.trans hz.1),
        (hz.2.trans_le hv.2).trans hx.2⟩
    calc
      0 ≤ iteratedLeftDeriv 1 g z := hderiv z hzDomain
      _ = p.derivative.eval z := by
        simpa using hleftNext ⟨hu.1.trans hz.1, hz.2.trans_le hv.2⟩
  have qmono : ∀ {u v : ℝ}, x ≤ u → u < v → v < b' →
      q.eval u ≤ q.eval v := by
    intro u v hxu huv hvb
    apply iterateDerivative_eval_le_of_next_nonneg q 0 huv
    intro z hz
    have hzDomain : z ∈ Set.Ioo c d :=
      ⟨hx.1.trans_le (hxu.trans hz.1.le),
        (hz.2.trans hvb).trans_le (min_le_right b d)⟩
    calc
      0 ≤ iteratedLeftDeriv 1 g z := hderiv z hzDomain
      _ = q.derivative.eval z := by
        simpa using hrightNext ⟨hxu.trans_lt hz.1, hz.2.trans hvb⟩
  intro u hu v hv huv
  by_cases huvEq : u = v
  · simpa [huvEq]
  have huv' : u < v := lt_of_le_of_ne huv huvEq
  by_cases hvx : v ≤ x
  · rw [hleft' u ⟨hu.1, huv.trans hvx⟩,
      hleft' v ⟨hv.1, hvx⟩]
    exact pmono ⟨hu.1, huv.trans hvx⟩ ⟨hv.1, hvx⟩ huv'
  by_cases hxu : x ≤ u
  · by_cases hux : u = x
    · subst u
      rw [hleft' x ⟨ha'x, le_rfl⟩,
        hright' v ⟨lt_of_not_ge hvx, hv.2⟩, hmatch]
      exact qmono le_rfl huv' hv.2
    · have hxu' : x < u := lt_of_le_of_ne hxu (Ne.symm hux)
      rw [hright' u ⟨hxu', hu.2⟩,
        hright' v ⟨hxu'.trans_le huv, hv.2⟩]
      exact qmono hxu huv' hv.2
  · have hux : u < x := lt_of_not_ge hxu
    have hxv : x < v := lt_of_not_ge hvx
    rw [hleft' u ⟨hu.1, hux.le⟩, hright' v ⟨hxv, hv.2⟩]
    exact (pmono ⟨hu.1, hux.le⟩ ⟨ha'x, le_rfl⟩ hux).trans
      (hmatch.le.trans (qmono le_rfl hxv hv.2))

/-- A function which is monotone on some open neighbourhood of every positive
point is monotone on the whole positive axis. -/
theorem monotoneOn_Ioi_of_locally_monotoneOn
    (g : ℝ → ℝ)
    (hlocal : ∀ x ∈ Set.Ioi (0 : ℝ),
      ∃ a b : ℝ, a < x ∧ x < b ∧ MonotoneOn g (Set.Ioo a b)) :
    MonotoneOn g (Set.Ioi 0) := by
  intro x hx y hy hxy
  by_cases hxyEq : x = y
  · simpa [hxyEq]
  have hxyLt : x < y := lt_of_le_of_ne hxy hxyEq
  let A : Set ℝ := {z | x ≤ z ∧ z ≤ y ∧ g x ≤ g z}
  have hA_nonempty : A.Nonempty := by
    refine ⟨x, ?_⟩
    exact ⟨le_rfl, hxy, le_rfl⟩
  have hA_bdd : BddAbove A := by
    refine ⟨y, ?_⟩
    intro z hz
    exact hz.2.1
  let s : ℝ := sSup A
  have hxs : x ≤ s := by
    exact le_csSup hA_bdd (show x ∈ A from ⟨le_rfl, hxy, le_rfl⟩)
  have hsy : s ≤ y := by
    exact csSup_le hA_nonempty (fun z hz ↦ hz.2.1)
  have hs_pos : s ∈ Set.Ioi (0 : ℝ) := hx.trans_le hxs
  obtain ⟨a, b, has, hsb, hmono⟩ := hlocal s hs_pos
  have hxs_value : g x ≤ g s := by
    by_cases hxsEq : x = s
    · simpa [hxsEq]
    · have hxsLt : x < s := lt_of_le_of_ne hxs hxsEq
      have hmax_lt : max a x < s := max_lt has hxsLt
      obtain ⟨z, hzA, hmaxz⟩ := exists_lt_of_lt_csSup hA_nonempty hmax_lt
      have hzs : z ≤ s := le_csSup hA_bdd hzA
      have hz_mem : z ∈ Set.Ioo a b := by
        constructor
        · exact (le_max_left a x).trans_lt hmaxz
        · exact hzs.trans_lt hsb
      have hs_mem : s ∈ Set.Ioo a b := ⟨has, hsb⟩
      exact hzA.2.2.trans (hmono hz_mem hs_mem hzs)
  have hys : y ≤ s := by
    by_cases hys' : y ≤ s
    · exact hys'
    · have hsyLt : s < y := lt_of_not_ge hys'
      let t : ℝ := (s + min b y) / 2
      have hs_min : s < min b y := lt_min hsb hsyLt
      have hst : s < t := by
        dsimp [t]
        linarith
      have ht_min : t < min b y := by
        dsimp [t]
        linarith
      have ht_mem_local : t ∈ Set.Ioo a b := by
        constructor
        · exact has.trans hst
        · exact ht_min.trans_le (min_le_left b y)
      have hs_mem : s ∈ Set.Ioo a b := ⟨has, hsb⟩
      have htA : t ∈ A := by
        refine ⟨hxs.trans hst.le, ?_, ?_⟩
        · exact ht_min.le.trans (min_le_right b y)
        · exact hxs_value.trans (hmono hs_mem ht_mem_local hst.le)
      have hts : t ≤ s := le_csSup hA_bdd htA
      exact (not_le_of_gt hst hts).elim
  have hseq : s = y := le_antisymm hsy hys
  simpa [hseq] using hxs_value

/-- Local monotonicity on open neighbourhoods glues on an arbitrary open
interval.  This interval version is used to turn monotonicity of the left
derivative into the secant-slope inequalities for convexity. -/
theorem monotoneOn_Ioo_of_locally_monotoneOn
    (g : ℝ → ℝ) {c d : ℝ}
    (hlocal : ∀ x ∈ Set.Ioo c d,
      ∃ a b : ℝ, a < x ∧ x < b ∧ MonotoneOn g (Set.Ioo a b)) :
    MonotoneOn g (Set.Ioo c d) := by
  intro x hx y hy hxy
  by_cases hxyEq : x = y
  · simpa [hxyEq]
  have hxyLt : x < y := lt_of_le_of_ne hxy hxyEq
  let A : Set ℝ := {z | x ≤ z ∧ z ≤ y ∧ g x ≤ g z}
  have hA_nonempty : A.Nonempty := ⟨x, le_rfl, hxy, le_rfl⟩
  have hA_bdd : BddAbove A := by
    refine ⟨y, ?_⟩
    intro z hz
    exact hz.2.1
  let s : ℝ := sSup A
  have hxs : x ≤ s :=
    le_csSup hA_bdd (show x ∈ A from ⟨le_rfl, hxy, le_rfl⟩)
  have hsy : s ≤ y := csSup_le hA_nonempty (fun z hz ↦ hz.2.1)
  have hs_mem_domain : s ∈ Set.Ioo c d :=
    ⟨hx.1.trans_le hxs, hsy.trans_lt hy.2⟩
  obtain ⟨a, b, has, hsb, hmono⟩ := hlocal s hs_mem_domain
  have hxs_value : g x ≤ g s := by
    by_cases hxsEq : x = s
    · simpa [hxsEq]
    · have hxsLt : x < s := lt_of_le_of_ne hxs hxsEq
      have hmax_lt : max a x < s := max_lt has hxsLt
      obtain ⟨z, hzA, hmaxz⟩ := exists_lt_of_lt_csSup hA_nonempty hmax_lt
      have hzs : z ≤ s := le_csSup hA_bdd hzA
      have hz_mem : z ∈ Set.Ioo a b :=
        ⟨(le_max_left a x).trans_lt hmaxz, hzs.trans_lt hsb⟩
      have hs_mem : s ∈ Set.Ioo a b := ⟨has, hsb⟩
      exact hzA.2.2.trans (hmono hz_mem hs_mem hzs)
  have hys : y ≤ s := by
    by_cases hys' : y ≤ s
    · exact hys'
    · have hsyLt : s < y := lt_of_not_ge hys'
      let t : ℝ := (s + min b y) / 2
      have hs_min : s < min b y := lt_min hsb hsyLt
      have hst : s < t := by dsimp [t]; linarith
      have ht_min : t < min b y := by dsimp [t]; linarith
      have ht_mem_local : t ∈ Set.Ioo a b :=
        ⟨has.trans hst, ht_min.trans_le (min_le_left b y)⟩
      have hs_mem : s ∈ Set.Ioo a b := ⟨has, hsb⟩
      have htA : t ∈ A := by
        refine ⟨hxs.trans hst.le, ht_min.le.trans (min_le_right b y), ?_⟩
        exact hxs_value.trans (hmono hs_mem ht_mem_local hst.le)
      have hts : t ≤ s := le_csSup hA_bdd htA
      exact (not_le_of_gt hst hts).elim
  have hseq : s = y := le_antisymm hsy hys
  simpa [hseq] using hxs_value

theorem continuousPolynomialSpline_monotoneOn_Ioo_of_leftDeriv_nonnegative
    {n : ℕ} {g : ℝ → ℝ} {c d : ℝ}
    (hdata : ContinuousPolynomialSplineEventData n g) (hc : 0 ≤ c)
    (hderiv : ∀ r ∈ Set.Ioo c d, 0 ≤ iteratedLeftDeriv 1 g r) :
    MonotoneOn g (Set.Ioo c d) :=
  monotoneOn_Ioo_of_locally_monotoneOn g
    (continuousPolynomialSpline_locallyMonotoneOn_Ioo_of_leftDeriv_nonnegative
      hdata hc hderiv)

/-- Endpoint closure of the preceding open-interval monotonicity theorem. -/
theorem continuousPolynomialSpline_endpoints_le_of_leftDeriv_nonnegative
    {n : ℕ} {g : ℝ → ℝ}
    (hdata : ContinuousPolynomialSplineEventData n g)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hderiv : ∀ r ∈ Set.Ioo x y, 0 ≤ iteratedLeftDeriv 1 g r) :
    g x ≤ g y := by
  obtain ⟨ax, bx, px, qx, haxx, hxbx, hpx, hqx,
      hleftx, hrightx, hmatchx⟩ := hdata x hx
  obtain ⟨ay, by_, py, qy, hayy, hyby, hpy, hqy,
      hlefty, hrighty, hmatchy⟩ := hdata y (hx.trans hxy)
  let s := (x + y) / 2
  have hxs : x < s := by dsimp [s]; linarith
  have hsy : s < y := by dsimp [s]; linarith
  let t := (x + min bx s) / 2
  have hxMin : x < min bx s := lt_min hxbx hxs
  have hxt : x < t := by dsimp [t]; linarith
  have htMin : t < min bx s := by dsimp [t]; linarith
  have hts : t < s := htMin.trans_le (min_le_right bx s)
  let u := (max ay s + y) / 2
  have hMaxy : max ay s < y := max_lt hayy hsy
  have hMaxu : max ay s < u := by dsimp [u]; linarith
  have huy : u < y := by dsimp [u]; linarith
  have hsu : s < u := (le_max_right ay s).trans_lt hMaxu
  have htu : t < u := hts.trans hsu
  have htDomain : t ∈ Set.Ioo x y := ⟨hxt, hts.trans hsy⟩
  have huDomain : u ∈ Set.Ioo x y := ⟨hxs.trans hsu, huy⟩
  have hxValue : g x = qx.eval x :=
    (hleftx x ⟨haxx, le_rfl⟩).trans hmatchx
  have htValue : g t = qx.eval t :=
    hrightx t ⟨hxt, htMin.trans_le (min_le_left bx s)⟩
  have huValue : g u = py.eval u :=
    hlefty u ⟨(le_max_left ay s).trans_lt hMaxu, huy.le⟩
  have hyValue : g y = py.eval y := hlefty y ⟨hayy, le_rfl⟩
  have hqxMono : qx.eval x ≤ qx.eval t := by
    apply iterateDerivative_eval_le_of_next_nonneg qx 0 hxt
    intro z hz
    have hzEq := iteratedLeftDeriv_eq_iterateDerivative_on_Ioo
      g qx hrightx 1
        ⟨hz.1, (hz.2.trans htMin).trans_le (min_le_left bx s)⟩
    calc
      0 ≤ iteratedLeftDeriv 1 g z :=
        hderiv z ⟨hz.1, hz.2.trans (hts.trans hsy)⟩
      _ = qx.derivative.eval z := by simpa using hzEq
  have hpyMono : py.eval u ≤ py.eval y := by
    apply iterateDerivative_eval_le_of_next_nonneg py 0 huy
    intro z hz
    have hzEq := iteratedLeftDeriv_eq_iterateDerivative_on_Ioo
      g py (fun w hw ↦ hlefty w ⟨
        (le_max_left ay s).trans_lt (hMaxu.trans hw.1), hw.2.le⟩) 1
        ⟨hz.1, hz.2⟩
    calc
      0 ≤ iteratedLeftDeriv 1 g z :=
        hderiv z ⟨hxs.trans (hsu.trans hz.1), hz.2⟩
      _ = py.derivative.eval z := by simpa using hzEq
  have hopen : g t ≤ g u :=
    continuousPolynomialSpline_monotoneOn_Ioo_of_leftDeriv_nonnegative
      hdata hx.le hderiv htDomain huDomain htu.le
  rw [htValue, huValue] at hopen
  rw [hxValue, hyValue]
  exact hqxMono.trans (hopen.trans hpyMono)

theorem linearTilt_monotoneOn_Ioo_of_leftDeriv_lowerBound
    {n : ℕ} {g : ℝ → ℝ} (hn : 1 ≤ n)
    (hevents : PositivePolynomialSplineEventData n g)
    {c d m : ℝ} (hc : 0 ≤ c)
    (hlower : ∀ r ∈ Set.Ioo c d,
      m ≤ iteratedLeftDeriv 1 g r) :
    MonotoneOn (linearTilt g m) (Set.Ioo c d) := by
  apply continuousPolynomialSpline_monotoneOn_Ioo_of_leftDeriv_nonnegative
    (hevents.continuousData.linearTilt hn m) hc
  intro r hr
  rw [iteratedLeftDeriv_one_linearTilt hevents m r (hc.trans_lt hr.1)]
  exact sub_nonneg.mpr (hlower r hr)

theorem linearCotilt_monotoneOn_Ioo_of_leftDeriv_upperBound
    {n : ℕ} {g : ℝ → ℝ} (hn : 1 ≤ n)
    (hevents : PositivePolynomialSplineEventData n g)
    {c d m : ℝ} (hc : 0 ≤ c)
    (hupper : ∀ r ∈ Set.Ioo c d,
      iteratedLeftDeriv 1 g r ≤ m) :
    MonotoneOn (linearCotilt g m) (Set.Ioo c d) := by
  apply continuousPolynomialSpline_monotoneOn_Ioo_of_leftDeriv_nonnegative
    (hevents.continuousData.linearCotilt hn m) hc
  intro r hr
  rw [iteratedLeftDeriv_one_linearCotilt hevents m r (hc.trans_lt hr.1)]
  exact sub_nonneg.mpr (hupper r hr)

/-- A continuous positive polynomial spline is convex on the positive ray
when its first left derivative is nondecreasing there.  The proof uses the
adjacent-secant-slope characterization of convexity; the endpoint estimates
are supplied by the local polynomial germs in `hevents`. -/
theorem positivePolynomialSpline_convexOn
    {n : ℕ} {g : ℝ → ℝ} (hn : 1 ≤ n)
    (hevents : PositivePolynomialSplineEventData n g)
    (hmono : MonotoneOn (iteratedLeftDeriv 1 g) (Set.Ioi 0)) :
    ConvexOn ℝ (Set.Ioi 0) g := by
  rw [convexOn_iff_slope_mono_adjacent]
  refine ⟨convex_Ioi 0, ?_⟩
  intro x y z hx hz hxy hyz
  let m := iteratedLeftDeriv 1 g y
  have hy : y ∈ Set.Ioi (0 : ℝ) := hx.trans hxy
  have hupper : ∀ r ∈ Set.Ioo x y,
      iteratedLeftDeriv 1 g r ≤ m := by
    intro r hr
    exact hmono (hx.trans hr.1) hy hr.2.le
  have hlower : ∀ r ∈ Set.Ioo y z,
      m ≤ iteratedLeftDeriv 1 g r := by
    intro r hr
    exact hmono hy (hy.trans hr.1) hr.1.le
  have hleftDeriv : ∀ r ∈ Set.Ioo x y,
      0 ≤ iteratedLeftDeriv 1 (linearCotilt g m) r := by
    intro r hr
    rw [iteratedLeftDeriv_one_linearCotilt hevents m r (hx.trans hr.1)]
    exact sub_nonneg.mpr (hupper r hr)
  have hrightDeriv : ∀ r ∈ Set.Ioo y z,
      0 ≤ iteratedLeftDeriv 1 (linearTilt g m) r := by
    intro r hr
    rw [iteratedLeftDeriv_one_linearTilt hevents m r (hy.trans hr.1)]
    exact sub_nonneg.mpr (hlower r hr)
  have hleft :=
    continuousPolynomialSpline_endpoints_le_of_leftDeriv_nonnegative
      (hevents.continuousData.linearCotilt hn m) hx hxy hleftDeriv
  have hright :=
    continuousPolynomialSpline_endpoints_le_of_leftDeriv_nonnegative
      (hevents.continuousData.linearTilt hn m) hy hyz hrightDeriv
  have hleftSlope : (g y - g x) / (y - x) ≤ m := by
    apply (div_le_iff₀ (sub_pos.mpr hxy)).2
    dsimp [linearCotilt, m] at hleft
    linarith
  have hrightSlope : m ≤ (g z - g y) / (z - y) := by
    apply (le_div_iff₀ (sub_pos.mpr hyz)).2
    dsimp [linearTilt, m] at hright
    linarith
  exact hleftSlope.trans hrightSlope

/-- A finite-degree positive polynomial spline with nonnegative event jumps
and nonnegative initial jets has a nonnegative, nondecreasing derivative
tower through its degree.  This is the analytic descending induction in the
proof of Lemma 4.4, isolated from the tropical bookkeeping. -/
theorem positivePolynomialSpline_absoluteMonotonicity
    {n : ℕ} {g : ℝ → ℝ}
    (hinitial : PositivePolynomialSplineInitialData n g)
    (hevents : PositivePolynomialSplineEventData n g) :
    (∀ l : ℕ, l ≤ n → ∀ r : ℝ, 0 < r →
        0 ≤ iteratedLeftDeriv l g r) ∧
      (∀ l : ℕ, l ≤ n →
        MonotoneOn (iteratedLeftDeriv l g) (Set.Ioi 0)) := by
  have nonneg_of_initial_mono : ∀ l : ℕ,
      MonotoneOn (iteratedLeftDeriv l g) (Set.Ioi 0) →
      (∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r ∈ Set.Ioo (0 : ℝ) r₀,
        0 ≤ iteratedLeftDeriv l g r) →
      ∀ r : ℝ, 0 < r → 0 ≤ iteratedLeftDeriv l g r := by
    intro l hmono hinit r hr
    obtain ⟨r₀, hr₀, hnear⟩ := hinit
    let s := min (r / 2) (r₀ / 2)
    have hs : 0 < s := by
      change 0 < min (r / 2) (r₀ / 2)
      exact lt_min (by linarith) (by linarith)
    have hsr : s < r := (min_le_left _ _).trans_lt (by linarith)
    have hsr₀ : s < r₀ := (min_le_right _ _).trans_lt (by linarith)
    exact (hnear s ⟨hs, hsr₀⟩).trans (hmono hs hr hsr.le)
  have htower : ∀ k : ℕ, k ≤ n →
      ((∀ r : ℝ, 0 < r → 0 ≤ iteratedLeftDeriv (n - k) g r) ∧
        MonotoneOn (iteratedLeftDeriv (n - k) g) (Set.Ioi 0)) := by
    intro k
    induction k with
    | zero =>
        intro hk
        have hmono : MonotoneOn (iteratedLeftDeriv n g) (Set.Ioi 0) :=
          monotoneOn_Ioi_of_locally_monotoneOn _
            (topIteratedLeftDeriv_locallyMonotone_of_splineEventData hevents)
        have hnonneg := nonneg_of_initial_mono n hmono (hinitial n le_rfl)
        simpa using And.intro hnonneg hmono
    | succ k ih =>
        intro hk
        have hklt : k < n := by omega
        obtain ⟨hprevNonneg, hprevMono⟩ := ih hklt.le
        let l := n - (k + 1)
        have hl : l ≤ n := Nat.sub_le _ _
        have hnext : ∀ r : ℝ, 0 < r →
            0 ≤ iteratedLeftDeriv (l + 1) g r := by
          intro r hr
          have heq : l + 1 = n - k := by dsimp [l]; omega
          simpa [heq] using hprevNonneg r hr
        have hmono : MonotoneOn (iteratedLeftDeriv l g) (Set.Ioi 0) :=
          monotoneOn_Ioi_of_locally_monotoneOn _
            (iteratedLeftDeriv_locallyMonotone_of_next_nonnegative
              hevents hl hnext)
        have hnonneg := nonneg_of_initial_mono l hmono (hinitial l hl)
        exact ⟨hnonneg, hmono⟩
  constructor
  · intro l hl
    have h := (htower (n - l) (Nat.sub_le n l)).1
    have heq : n - (n - l) = l := by omega
    simpa [heq] using h
  · intro l hl
    have h := (htower (n - l) (Nat.sub_le n l)).2
    have heq : n - (n - l) = l := by omega
    simpa [heq] using h

/-! ## Intrinsic local polynomial and counting bridges -/

theorem PolynomialPresentation.rightPieceAt_eval
    {n : ℕ} {f : ℝ → ℝ} (P : PolynomialPresentation n f) (x : ℝ) :
    (P.rightPieceAt x).eval x = f x := by
  let i := presentationIntervalIndex P x
  have hx := presentationIntervalIndex_mem P x
  change x ∈ Set.Ioc (P.cutPoint (i - 1)) (P.cutPoint i) at hx
  by_cases hcut : x = P.cutPoint i
  · rw [PolynomialPresentation.rightPieceAt, if_pos hcut]
    exact (P.eq_piece (i + 1) ⟨by simpa [hcut], by
      rw [hcut]
      exact (P.cutPoint_strictMono (by omega)).le⟩).symm
  · rw [PolynomialPresentation.rightPieceAt, if_neg hcut]
    exact (P.eq_piece i ⟨hx.1.le, hx.2⟩).symm

/-- If the underlying function agrees with `p` on an open interval, its
intrinsic left germ at every point of that interval is `p`. -/
theorem leftPieceAt_eq_of_eqOn_Ioo
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (P : PolynomialPresentation n f) (p : Polynomial ℝ)
    {a b y : ℝ} (hy : y ∈ Set.Ioo a b)
    (hfp : ∀ z ∈ Set.Ioo a b, f z = p.eval z) :
    P.leftPieceAt y = p := by
  obtain ⟨c, hcy, hleft⟩ := P.exists_left_germ_interval y
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioo_infinite (max_lt hcy hy.1)).mono
  intro z hz
  have hzc : z ∈ Set.Ioo c y :=
    ⟨(le_max_left c a).trans_lt hz.1, hz.2⟩
  have hzab : z ∈ Set.Ioo a b :=
    ⟨(le_max_right c a).trans_lt hz.1, hz.2.trans hy.2⟩
  exact (hleft z hzc).symm.trans (hfp z hzab)

/-- The analogous identification of the intrinsic right germ. -/
theorem rightPieceAt_eq_of_eqOn_Ioo
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (P : PolynomialPresentation n f) (p : Polynomial ℝ)
    {a b y : ℝ} (hy : y ∈ Set.Ioo a b)
    (hfp : ∀ z ∈ Set.Ioo a b, f z = p.eval z) :
    P.rightPieceAt y = p := by
  obtain ⟨c, hyc, hright⟩ := P.exists_right_germ_interval y
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioo_infinite (lt_min hy.2 hyc)).mono
  intro z hz
  have hzc : z ∈ Set.Ioo y c :=
    ⟨hz.1, hz.2.trans_le (min_le_right b c)⟩
  have hzab : z ∈ Set.Ioo a b :=
    ⟨hy.1.trans (hzc.1), hz.2.trans_le (min_le_left b c)⟩
  exact (hright z hzc).symm.trans (hfp z hzab)

/-- There is no intrinsic singularity inside a genuine polynomial interval.
This removes all redundant presentation cuts from the later radial counting
argument. -/
theorem multiplicity_eq_zero_of_eqOn_Ioo
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (P : PolynomialPresentation n f) (p : Polynomial ℝ)
    {a b y : ℝ} (hy : y ∈ Set.Ioo a b) (hy0 : y ≠ 0)
    (hfp : ∀ z ∈ Set.Ioo a b, f z = p.eval z) (j : ℕ) :
    multiplicity f j y = 0 := by
  have hleft := leftPieceAt_eq_of_eqOn_Ioo P p hy hfp
  have hright := rightPieceAt_eq_of_eqOn_Ioo P p hy hfp
  rw [multiplicity_eq_usingPresentation f P]
  rcases lt_or_gt_of_ne hy0 with hyneg | hypos
  · simp [multiplicityUsingPresentation, hleft, hright,
      rightSign_of_neg hyneg, leftSign_of_nonpos hyneg.le]
  · simp [multiplicityUsingPresentation, hleft, hright,
      rightSign_of_nonneg hypos.le, leftSign_of_pos hypos]

/-- Around every positive radius there is a punctured radial annulus with no
intrinsic singularities except possibly at the two boundary points `±x`.
The result uses the four polynomial germs at `x` and `-x`; no assertion is
made that either boundary point is actually singular. -/
theorem exists_radial_punctured_multiplicity_free
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) {x : ℝ} (hx : 0 < x) :
    ∃ a b : ℝ, 0 < a ∧ a < x ∧ x < b ∧
      ∀ j : ℕ, ∀ y : ℝ,
        ((a < |y| ∧ |y| < x) ∨ (x < |y| ∧ |y| < b)) →
          multiplicity f j y = 0 := by
  let P := f.presentation
  obtain ⟨ap, hap, hpl⟩ := P.exists_left_germ_interval x
  obtain ⟨bp, hbp, hpr⟩ := P.exists_right_germ_interval x
  obtain ⟨cn, hcn, hnr⟩ := P.exists_right_germ_interval (-x)
  obtain ⟨dn, hdn, hnl⟩ := P.exists_left_germ_interval (-x)
  let a := max (x / 2) (max ap (-cn))
  let b := min bp (-dn)
  have ha0 : 0 < a := by
    exact (by linarith : 0 < x / 2).trans_le (le_max_left _ _)
  have hax : a < x := by
    apply max_lt
    · linarith
    · apply max_lt hap
      linarith
  have hxb : x < b := by
    apply lt_min hbp
    linarith
  refine ⟨a, b, ha0, hax, hxb, ?_⟩
  intro j y hyann
  have hy0 : y ≠ 0 := by
    intro hyzero
    subst y
    simp only [abs_zero] at hyann
    rcases hyann with hyann | hyann <;> linarith
  rcases lt_or_gt_of_ne hy0 with hyneg | hypos
  · have habs : |y| = -y := abs_of_neg hyneg
    rcases hyann with hinner | houter
    · apply multiplicity_eq_zero_of_eqOn_Ioo P (P.rightPieceAt (-x))
          (a := -x) (b := cn) (y := y) _ hy0 hnr j
      constructor
      · rw [habs] at hinner
        linarith
      · have hacn : -cn ≤ a :=
          (le_max_right ap (-cn)).trans (le_max_right (x / 2) _)
        rw [habs] at hinner
        linarith
    · apply multiplicity_eq_zero_of_eqOn_Ioo P (P.leftPieceAt (-x))
          (a := dn) (b := -x) (y := y) _ hy0 hnl j
      constructor
      · have hbdn : b ≤ -dn := min_le_right bp (-dn)
        rw [habs] at houter
        linarith
      · rw [habs] at houter
        linarith
  · have habs : |y| = y := abs_of_pos hypos
    rcases hyann with hinner | houter
    · apply multiplicity_eq_zero_of_eqOn_Ioo P (P.leftPieceAt x)
          (a := ap) (b := x) (y := y) _ hy0 hpl j
      constructor
      · have hapa : ap ≤ a :=
          (le_max_left ap (-cn)).trans (le_max_right (x / 2) _)
        rw [habs] at hinner
        linarith
      · simpa [habs] using hinner.2
    · apply multiplicity_eq_zero_of_eqOn_Ioo P (P.rightPieceAt x)
          (a := x) (b := bp) (y := y) _ hy0 hpr j
      constructor
      · simpa [habs] using houter.1
      · have hbbp : b ≤ bp := min_le_left bp (-dn)
        rw [habs] at houter
        linarith

/-- On the inner side of a punctured singularity-free radial annulus, every
pole set is the fixed pole set at the event radius. -/
theorem jthPolePoints_eq_at_event_of_mem_Ioc
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ)
    {a x b r : ℝ} (hr : r ∈ Set.Ioc a x)
    (hfree : ∀ j : ℕ, ∀ y : ℝ,
      ((a < |y| ∧ |y| < x) ∨ (x < |y| ∧ |y| < b)) →
        multiplicity f j y = 0) :
    jthPolePoints f j r = jthPolePoints f j x := by
  classical
  ext y
  simp only [mem_jthPolePoints_iff]
  constructor
  · rintro ⟨hyr, hpole⟩
    have hay : |y| < r := (abs_lt).2 hyr
    exact ⟨(abs_lt).1 (hay.trans_le hr.2), hpole⟩
  · rintro ⟨hyx, hpole⟩
    have hyxabs : |y| < x := (abs_lt).2 hyx
    by_cases hyr : |y| < r
    · exact ⟨(abs_lt).1 hyr, hpole⟩
    · have hzero := hfree j y (Or.inl
          ⟨hr.1.trans_le (le_of_not_gt hyr), hyxabs⟩)
      exact (by simp [IsJthPole, hzero] at hpole)

/-- On the outer side, every pole set is the fixed pole set at the outer
radius.  Possible poles at `±x` are automatically included. -/
theorem jthPolePoints_eq_at_outer_of_mem_Ioo
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ)
    {a x b r : ℝ} (hr : r ∈ Set.Ioo x b)
    (hfree : ∀ j : ℕ, ∀ y : ℝ,
      ((a < |y| ∧ |y| < x) ∨ (x < |y| ∧ |y| < b)) →
        multiplicity f j y = 0) :
    jthPolePoints f j r = jthPolePoints f j b := by
  classical
  ext y
  simp only [mem_jthPolePoints_iff]
  constructor
  · rintro ⟨hyr, hpole⟩
    have hyrabs : |y| < r := (abs_lt).2 hyr
    exact ⟨(abs_lt).1 (hyrabs.trans hr.2), hpole⟩
  · rintro ⟨hyb, hpole⟩
    have hybabs : |y| < b := (abs_lt).2 hyb
    by_cases hyr : |y| < r
    · exact ⟨(abs_lt).1 hyr, hpole⟩
    · have hzero := hfree j y (Or.inr
          ⟨hr.1.trans_le (le_of_not_gt hyr), hybabs⟩)
      exact (by simp [IsJthPole, hzero] at hpole)

/-- Polynomial obtained by freezing the finite pole set in an integrated
counting function. -/
def integratedCountingPolynomial
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ)
    (S : Finset ℝ) : Polynomial ℝ :=
  Polynomial.C (1 / 2) * ∑ y ∈ S,
    Polynomial.C (rootOrPoleMultiplicity f j y) *
      (Polynomial.X - Polynomial.C |y|) ^ j

@[simp]
theorem integratedCountingPolynomial_eval
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ)
    (S : Finset ℝ) (r : ℝ) :
    (integratedCountingPolynomial f j S).eval r =
      (1 / 2) * ∑ y ∈ S,
        rootOrPoleMultiplicity f j y * (r - |y|) ^ j := by
  simp [integratedCountingPolynomial, Polynomial.eval_finsetSum]

theorem integratedCounting_eq_polynomial_eval
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ)
    (S : Finset ℝ) {r : ℝ} (hS : jthPolePoints f j r = S) :
    integratedCounting j r f = (integratedCountingPolynomial f j S).eval r := by
  simp [integratedCounting, integratedCountingPolynomial_eval, hS]

theorem integratedCountingPolynomial_natDegree_le
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ)
    (S : Finset ℝ) :
    (integratedCountingPolynomial f j S).natDegree ≤ j := by
  unfold integratedCountingPolynomial
  apply Polynomial.natDegree_mul_le.trans
  calc
    (Polynomial.C (1 / 2 : ℝ)).natDegree +
        (∑ y ∈ S, Polynomial.C (rootOrPoleMultiplicity f j y) *
          (Polynomial.X - Polynomial.C |y|) ^ j).natDegree ≤
        0 + j := by
      gcongr
      · simp
      · apply Polynomial.natDegree_sum_le_of_forall_le
        intro y hy
        exact Polynomial.natDegree_mul_le.trans <| calc
          (Polynomial.C (rootOrPoleMultiplicity f j y)).natDegree +
              ((Polynomial.X - Polynomial.C |y|) ^ j).natDegree ≤
              0 + j := by
            gcongr
            · simp
            · exact Polynomial.natDegree_pow_le.trans (by simp)
          _ = j := by simp
    _ = j := by simp

/-- A well-defined polynomial is monotone or antitone on the nonnegative
axis.  The choice is determined by the common sign of its nonconstant
coefficients. -/
theorem IsWellDefinedPolynomial.monotoneOn_Ici_or_antitoneOn_Ici
    {p : Polynomial ℝ} (hp : IsWellDefinedPolynomial p) :
    MonotoneOn (fun r ↦ p.eval r) (Set.Ici 0) ∨
      AntitoneOn (fun r ↦ p.eval r) (Set.Ici 0) := by
  rcases hp.commonSign with hcoeff | hcoeff
  · left
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact p.continuous.continuousOn
    · simpa using p.differentiable.differentiableOn
    · intro r hr
      have hr0 : 0 ≤ r := interior_subset hr
      rw [(p.hasDerivAt r).deriv, Polynomial.derivative_eval]
      apply Finset.sum_nonneg
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        simp
      · exact mul_nonneg (mul_nonneg (hcoeff k hk0) (by positivity))
          (pow_nonneg hr0 _)
  · right
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact p.continuous.continuousOn
    · simpa using p.differentiable.differentiableOn
    · intro r hr
      have hr0 : 0 ≤ r := interior_subset hr
      rw [(p.hasDerivAt r).deriv, Polynomial.derivative_eval]
      apply Finset.sum_nonpos
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        simp
      · exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (hcoeff k hk0) (by positivity))
          (pow_nonneg hr0 _)

theorem iterateDerivative_eval_nonneg_of_coeff_nonneg
    {p : Polynomial ℝ}
    (hp : ∀ k : ℕ, k ≠ 0 → 0 ≤ p.coeff k)
    {l : ℕ} (hl : 1 ≤ l) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ ((Polynomial.derivative^[l]) p).eval r := by
  rw [Polynomial.eval_eq_sum]
  apply Finset.sum_nonneg
  intro k hk
  apply mul_nonneg
  · rw [Polynomial.coeff_iterate_derivative]
    exact nsmul_nonneg (hp (k + l) (by omega)) _
  · positivity

theorem iterateDerivative_eval_nonpos_of_coeff_nonpos
    {p : Polynomial ℝ}
    (hp : ∀ k : ℕ, k ≠ 0 → p.coeff k ≤ 0)
    {l : ℕ} (hl : 1 ≤ l) {r : ℝ} (hr : 0 ≤ r) :
    ((Polynomial.derivative^[l]) p).eval r ≤ 0 := by
  rw [Polynomial.eval_eq_sum]
  apply Finset.sum_nonpos
  intro k hk
  apply mul_nonpos_of_nonpos_of_nonneg
  · rw [Polynomial.coeff_iterate_derivative]
    exact nsmul_nonpos (hp (k + l) (by omega)) _
  · positivity

theorem polynomial_eval_monotoneOn_Ici_of_coeff_nonneg
    {p : Polynomial ℝ}
    (hp : ∀ k : ℕ, k ≠ 0 → 0 ≤ p.coeff k) :
    MonotoneOn (fun r ↦ p.eval r) (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact p.continuous.continuousOn
  · simpa using p.differentiable.differentiableOn
  · intro r hr
    have hr0 : 0 ≤ r := interior_subset hr
    rw [(p.hasDerivAt r).deriv]
    simpa [Function.iterate_one] using
      (iterateDerivative_eval_nonneg_of_coeff_nonneg hp (l := 1) le_rfl hr0)

theorem polynomial_eval_antitoneOn_Ici_of_coeff_nonpos
    {p : Polynomial ℝ}
    (hp : ∀ k : ℕ, k ≠ 0 → p.coeff k ≤ 0) :
    AntitoneOn (fun r ↦ p.eval r) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact p.continuous.continuousOn
  · simpa using p.differentiable.differentiableOn
  · intro r hr
    have hr0 : 0 ≤ r := interior_subset hr
    rw [(p.hasDerivAt r).deriv]
    simpa [Function.iterate_one] using
      (iterateDerivative_eval_nonpos_of_coeff_nonpos hp (l := 1) le_rfl hr0)

/-- On a left neighbourhood of a positive point, the positive part of a
well-defined polynomial is either that polynomial or zero. -/
theorem exists_positivePart_left_polynomial
    {p : Polynomial ℝ} (hp : IsWellDefinedPolynomial p)
    {x : ℝ} (hx : 0 < x) :
    ∃ a : ℝ, ∃ active : Bool, 0 < a ∧ a < x ∧
      ∀ y ∈ Set.Ioc a x,
        maxPlusPositivePart (p.eval y) =
          (if active then p else 0).eval y := by
  rcases lt_trichotomy (p.eval x) 0 with hneg | hzero | hpos
  · have hnhds : {y : ℝ | p.eval y < 0} ∈ nhds x :=
      p.continuousAt.preimage_mem_nhds (Iio_mem_nhds hneg)
    obtain ⟨l, u, hxu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
    let a := max (x / 2) l
    have ha0 : 0 < a := (by linarith : 0 < x / 2).trans_le
      (le_max_left _ _)
    have hax : a < x := max_lt (by linarith) hxu.1
    refine ⟨a, false, ha0, hax, ?_⟩
    intro y hy
    have hyneg : p.eval y < 0 := hsub ⟨
      (le_max_right (x / 2) l).trans_lt hy.1,
      hy.2.trans_lt hxu.2⟩
    simp [maxPlusPositivePart, max_eq_right hyneg.le]
  · rcases hp.monotoneOn_Ici_or_antitoneOn_Ici with hmono | hanti
    · refine ⟨x / 2, false, by linarith, by linarith, ?_⟩
      intro y hy
      have hy0 : 0 ≤ y :=
        (by linarith : 0 < x / 2).le.trans hy.1.le
      have hnonpos : p.eval y ≤ 0 := by
        rw [← hzero]
        exact hmono hy0 hx.le hy.2
      simp [maxPlusPositivePart, max_eq_right hnonpos]
    · refine ⟨x / 2, true, by linarith, by linarith, ?_⟩
      intro y hy
      have hy0 : 0 ≤ y :=
        (by linarith : 0 < x / 2).le.trans hy.1.le
      have hnonneg : 0 ≤ p.eval y := by
        rw [← hzero]
        exact hanti hy0 hx.le hy.2
      simp [maxPlusPositivePart, max_eq_left hnonneg]
  · have hnhds : {y : ℝ | 0 < p.eval y} ∈ nhds x :=
      p.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hpos)
    obtain ⟨l, u, hxu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
    let a := max (x / 2) l
    have ha0 : 0 < a := (by linarith : 0 < x / 2).trans_le
      (le_max_left _ _)
    have hax : a < x := max_lt (by linarith) hxu.1
    refine ⟨a, true, ha0, hax, ?_⟩
    intro y hy
    have hypos : 0 < p.eval y := hsub ⟨
      (le_max_right (x / 2) l).trans_lt hy.1,
      hy.2.trans_lt hxu.2⟩
    simp [maxPlusPositivePart, max_eq_left hypos.le]

/-- Right-neighbourhood version of `exists_positivePart_left_polynomial`. -/
theorem exists_positivePart_right_polynomial
    {p : Polynomial ℝ} (hp : IsWellDefinedPolynomial p)
    {x : ℝ} (hx : 0 < x) :
    ∃ b : ℝ, ∃ active : Bool, x < b ∧
      ∀ y ∈ Set.Ico x b,
        maxPlusPositivePart (p.eval y) =
          (if active then p else 0).eval y := by
  rcases lt_trichotomy (p.eval x) 0 with hneg | hzero | hpos
  · have hnhds : {y : ℝ | p.eval y < 0} ∈ nhds x :=
      p.continuousAt.preimage_mem_nhds (Iio_mem_nhds hneg)
    obtain ⟨l, u, hxu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
    refine ⟨u, false, hxu.2, ?_⟩
    intro y hy
    have hyneg : p.eval y < 0 := hsub ⟨hxu.1.trans_le hy.1, hy.2⟩
    simp [maxPlusPositivePart, max_eq_right hyneg.le]
  · rcases hp.monotoneOn_Ici_or_antitoneOn_Ici with hmono | hanti
    · refine ⟨2 * x, true, by linarith, ?_⟩
      intro y hy
      have hy0 : 0 ≤ y := hx.le.trans hy.1
      have hnonneg : 0 ≤ p.eval y := by
        rw [← hzero]
        exact hmono hx.le hy0 hy.1
      simp [maxPlusPositivePart, max_eq_left hnonneg]
    · refine ⟨2 * x, false, by linarith, ?_⟩
      intro y hy
      have hy0 : 0 ≤ y := hx.le.trans hy.1
      have hnonpos : p.eval y ≤ 0 := by
        rw [← hzero]
        exact hanti hx.le hy0 hy.1
      simp [maxPlusPositivePart, max_eq_right hnonpos]
  · have hnhds : {y : ℝ | 0 < p.eval y} ∈ nhds x :=
      p.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hpos)
    obtain ⟨l, u, hxu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
    refine ⟨u, true, hxu.2, ?_⟩
    intro y hy
    have hypos : 0 < p.eval y := hsub ⟨hxu.1.trans_le hy.1, hy.2⟩
    simp [maxPlusPositivePart, max_eq_left hypos.le]

/-- If the positive part uses a well-defined polynomial on the left of a
zero, all of its positive-order jets at the endpoint are nonpositive. -/
theorem iterateDerivative_nonpos_of_positivePart_active_left
    {p : Polynomial ℝ} (hp : IsWellDefinedPolynomial p)
    {a x : ℝ} (ha0 : 0 < a) (hax : a < x)
    (hactive : ∀ y ∈ Set.Ioc a x,
      maxPlusPositivePart (p.eval y) = p.eval y)
    (hzero : p.eval x = 0) {l : ℕ} (hl : 1 ≤ l) :
    ((Polynomial.derivative^[l]) p).eval x ≤ 0 := by
  rcases hp.commonSign with hcoeff | hcoeff
  · have hmono := polynomial_eval_monotoneOn_Ici_of_coeff_nonneg hcoeff
    have hpzero : p = 0 := by
      apply Polynomial.eq_of_infinite_eval_eq
      apply (Set.Ioo_infinite hax).mono
      intro y hy
      have hnonneg : 0 ≤ p.eval y := by
        have h := hactive y ⟨hy.1, hy.2.le⟩
        rw [← h]
        exact maxPlusPositivePart_nonneg _
      have hnonpos : p.eval y ≤ 0 := by
        rw [← hzero]
        exact hmono (ha0.le.trans hy.1.le) (ha0.le.trans hax.le) hy.2.le
      simp [le_antisymm hnonpos hnonneg]
    simp [hpzero]
  · exact iterateDerivative_eval_nonpos_of_coeff_nonpos hcoeff hl
      (ha0.trans hax).le

/-- Right-side counterpart: an active positive part at a zero has
nonnegative positive-order jets. -/
theorem iterateDerivative_nonneg_of_positivePart_active_right
    {p : Polynomial ℝ} (hp : IsWellDefinedPolynomial p)
    {x b : ℝ} (hx : 0 < x) (hxb : x < b)
    (hactive : ∀ y ∈ Set.Ico x b,
      maxPlusPositivePart (p.eval y) = p.eval y)
    (hzero : p.eval x = 0) {l : ℕ} (hl : 1 ≤ l) :
    0 ≤ ((Polynomial.derivative^[l]) p).eval x := by
  rcases hp.commonSign with hcoeff | hcoeff
  · exact iterateDerivative_eval_nonneg_of_coeff_nonneg hcoeff hl hx.le
  · have hanti := polynomial_eval_antitoneOn_Ici_of_coeff_nonpos hcoeff
    have hpzero : p = 0 := by
      apply Polynomial.eq_of_infinite_eval_eq
      apply (Set.Ioo_infinite hxb).mono
      intro y hy
      have hnonneg : 0 ≤ p.eval y := by
        have h := hactive y ⟨hy.1.le, hy.2⟩
        rw [← h]
        exact maxPlusPositivePart_nonneg _
      have hnonpos : p.eval y ≤ 0 := by
        rw [← hzero]
        exact hanti hx.le (hx.le.trans hy.1.le) hy.1.le
      simp [le_antisymm hnonpos hnonneg]
    simp [hpzero]

/-- A local polynomial for the characteristic after freezing all pole sets
at the radius `R` and choosing polynomial representatives of the two
positive-part endpoint terms. -/
def characteristicLocalPolynomial
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (pPositive pNegative : Polynomial ℝ) (R : ℝ) : Polynomial ℝ :=
  Polynomial.C (1 / 2) * (pPositive + pNegative) +
    ∑ j ∈ Finset.Icc 1 n,
      integratedCountingPolynomial f j (jthPolePoints f j R)

theorem characteristicLocalPolynomial_natDegree_le
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {pPositive pNegative : Polynomial ℝ} (R : ℝ)
    (hpos : pPositive.natDegree ≤ n)
    (hneg : pNegative.natDegree ≤ n) :
    (characteristicLocalPolynomial f pPositive pNegative R).natDegree ≤ n := by
  unfold characteristicLocalPolynomial
  apply le_trans (Polynomial.natDegree_add_le _ _)
  apply max_le
  · apply Polynomial.natDegree_mul_le.trans
    calc
      (Polynomial.C (1 / 2 : ℝ)).natDegree +
          (pPositive + pNegative).natDegree ≤ 0 + n := by
        gcongr
        · simp
        · exact le_trans (Polynomial.natDegree_add_le pPositive pNegative)
            (max_le hpos hneg)
      _ = n := by simp
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (integratedCountingPolynomial_natDegree_le f j _).trans
      (Finset.mem_Icc.mp hj).2

theorem characteristic_eq_localPolynomial_eval
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (pPositive pNegative : Polynomial ℝ) (R r : ℝ)
    (hPositive : maxPlusPositivePart (f r) = pPositive.eval r)
    (hNegative : maxPlusPositivePart (f (-r)) = pNegative.eval r)
    (hPoleSets : ∀ j ∈ Finset.Icc 1 n,
      jthPolePoints f j r = jthPolePoints f j R) :
    characteristic r f =
      (characteristicLocalPolynomial f pPositive pNegative R).eval r := by
  simp only [characteristic, proximity, characteristicLocalPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_finset_sum, hPositive, hNegative]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    exact integratedCounting_eq_polynomial_eval f j _ (hPoleSets j hj)

theorem normalizedPolynomialJet_integratedCountingPolynomial
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j l : ℕ)
    (S : Finset ℝ) (x : ℝ) :
    normalizedPolynomialJet (integratedCountingPolynomial f j S) l x =
      (1 / 2) * ∑ y ∈ S, rootOrPoleMultiplicity f j y *
        normalizedPolynomialJet
          ((Polynomial.X - Polynomial.C |y|) ^ j) l x := by
  simp [integratedCountingPolynomial, normalizedPolynomialJet,
    ← Polynomial.smul_eq_C_mul, Polynomial.eval_finsetSum, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc]

def totalCountingLocalPolynomial
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (R : ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.Icc 1 n,
    integratedCountingPolynomial f j (jthPolePoints f j R)

theorem polePoints_outer_sdiff_inner_eq_boundary
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j : ℕ)
    {a x b : ℝ} (hx : 0 < x) (hxb : x < b)
    (hfree : ∀ j : ℕ, ∀ y : ℝ,
      ((a < |y| ∧ |y| < x) ∨ (x < |y| ∧ |y| < b)) →
        multiplicity f j y = 0) :
    jthPolePoints f j b \ jthPolePoints f j x =
      ({x, -x} : Finset ℝ).filter (fun y ↦ IsJthPole f j y) := by
  classical
  ext y
  simp only [Finset.mem_sdiff, mem_jthPolePoints_iff, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hyb, hpole⟩, hynot⟩
    have hybabs : |y| < b := (abs_lt).2 hyb
    have hnotinner : ¬ |y| < x := by
      intro hyx
      exact hynot ⟨(abs_lt).1 hyx, hpole⟩
    have hxle : x ≤ |y| := le_of_not_gt hnotinner
    have habseq : |y| = x := by
      apply le_antisymm _ hxle
      by_contra hnotle
      have hxabs : x < |y| := lt_of_not_ge hnotle
      have hzero := hfree j y (Or.inr ⟨hxabs, hybabs⟩)
      exact (by simp [IsJthPole, hzero] at hpole)
    have hycases : y = x ∨ y = -x := by
      rw [abs_eq (le_of_lt hx)] at habseq
      exact habseq
    exact ⟨hycases, hpole⟩
  · rintro ⟨hycases, hpole⟩
    have hyabs : |y| = x := by
      rcases hycases with rfl | rfl <;> simp [abs_of_pos hx]
    refine ⟨⟨(abs_lt).1 (by simpa [hyabs] using hxb), hpole⟩, ?_⟩
    intro hyinner
    have := (abs_lt).2 hyinner.1
    rw [hyabs] at this
    exact (lt_irrefl x this).elim

theorem normalizedPolynomialJet_integratedCountingPolynomial_jump
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (j l : ℕ)
    {a x b : ℝ} (hx : 0 < x) (hxb : x < b)
    (hfree : ∀ j : ℕ, ∀ y : ℝ,
      ((a < |y| ∧ |y| < x) ∨ (x < |y| ∧ |y| < b)) →
        multiplicity f j y = 0) :
    normalizedPolynomialJet
        (integratedCountingPolynomial f j (jthPolePoints f j b)) l x -
      normalizedPolynomialJet
        (integratedCountingPolynomial f j (jthPolePoints f j x)) l x =
      if l = j then
        (max (-multiplicity f j x) 0 +
          max (-multiplicity f j (-x)) 0) / 2
      else 0 := by
  classical
  let Sx := jthPolePoints f j x
  let Sb := jthPolePoints f j b
  have hsub : Sx ⊆ Sb := by
    intro y hy
    rw [mem_jthPolePoints_iff] at hy ⊢
    exact ⟨⟨(neg_lt_neg hxb).trans hy.1.1, hy.1.2.trans hxb⟩, hy.2⟩
  have hsplit : Sb = Sx ∪ (Sb \ Sx) :=
    (Finset.union_sdiff_of_subset hsub).symm
  have hsplit' : jthPolePoints f j b =
      jthPolePoints f j x ∪ (jthPolePoints f j b \ jthPolePoints f j x) := by
    simpa [Sb, Sx] using hsplit
  rw [normalizedPolynomialJet_integratedCountingPolynomial,
    normalizedPolynomialJet_integratedCountingPolynomial, hsplit',
    Finset.sum_union Finset.disjoint_sdiff]
  rw [show Sb \ Sx = ({x, -x} : Finset ℝ).filter
      (fun y ↦ IsJthPole f j y) by
    exact polePoints_outer_sdiff_inner_eq_boundary f j hx hxb hfree]
  simp only [Finset.sum_filter, Finset.sum_insert, Finset.sum_singleton]
  have hxne : x ≠ -x := by linarith
  have habs : |x| = x := abs_of_pos hx
  by_cases hlj : l = j
  · subst l
    by_cases hmx : multiplicity f j x < 0
    · by_cases hmn : multiplicity f j (-x) < 0
      · simp [hxne, habs, normalizedPolynomialJet_shiftedMonomial,
          rootOrPoleMultiplicity, IsJthPole, hmx, hmn,
          abs_of_neg hmx, abs_of_neg hmn,
          max_eq_left (neg_nonneg.mpr hmx.le),
          max_eq_left (neg_nonneg.mpr hmn.le)]
        ring
      · have hmn0 : 0 ≤ multiplicity f j (-x) := le_of_not_gt hmn
        simp [hxne, habs, normalizedPolynomialJet_shiftedMonomial,
          rootOrPoleMultiplicity, IsJthPole, hmx, hmn,
          abs_of_neg hmx, abs_of_nonneg hmn0,
          max_eq_left (neg_nonneg.mpr hmx.le),
          max_eq_right (neg_nonpos.mpr hmn0)]
        ring
    · have hmx0 : 0 ≤ multiplicity f j x := le_of_not_gt hmx
      by_cases hmn : multiplicity f j (-x) < 0
      · simp [hxne, habs, normalizedPolynomialJet_shiftedMonomial,
          rootOrPoleMultiplicity, IsJthPole, hmx, hmn,
          abs_of_nonneg hmx0, abs_of_neg hmn,
          max_eq_right (neg_nonpos.mpr hmx0),
          max_eq_left (neg_nonneg.mpr hmn.le)]
        ring
      · have hmn0 : 0 ≤ multiplicity f j (-x) := le_of_not_gt hmn
        simp [hxne, habs, normalizedPolynomialJet_shiftedMonomial,
          rootOrPoleMultiplicity, IsJthPole, hmx, hmn,
          abs_of_nonneg hmx0, abs_of_nonneg hmn0,
          max_eq_right (neg_nonpos.mpr hmx0),
          max_eq_right (neg_nonpos.mpr hmn0)]
  · simp [hlj, hxne, habs, normalizedPolynomialJet_shiftedMonomial]

theorem normalizedPolynomialJet_totalCountingLocalPolynomial_jump
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (l : ℕ)
    {a x b : ℝ} (hx : 0 < x) (hxb : x < b)
    (hfree : ∀ j : ℕ, ∀ y : ℝ,
      ((a < |y| ∧ |y| < x) ∨ (x < |y| ∧ |y| < b)) →
        multiplicity f j y = 0) :
    normalizedPolynomialJet (totalCountingLocalPolynomial f b) l x -
      normalizedPolynomialJet (totalCountingLocalPolynomial f x) l x =
      if l ∈ Finset.Icc 1 n then
        (max (-multiplicity f l x) 0 +
          max (-multiplicity f l (-x)) 0) / 2
      else 0 := by
  classical
  simp only [totalCountingLocalPolynomial, normalizedPolynomialJet,
    map_sum, Polynomial.eval_finset_sum, ← Finset.sum_sub_distrib]
  by_cases hl : l ∈ Finset.Icc 1 n
  · rw [if_pos hl]
    calc
      (∑ j ∈ Finset.Icc 1 n, (
          ((Polynomial.hasseDeriv l)
            (integratedCountingPolynomial f j (jthPolePoints f j b))).eval x -
          ((Polynomial.hasseDeriv l)
            (integratedCountingPolynomial f j (jthPolePoints f j x))).eval x)) =
          ∑ j ∈ Finset.Icc 1 n, if l = j then
            (max (-multiplicity f j x) 0 +
              max (-multiplicity f j (-x)) 0) / 2 else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            exact normalizedPolynomialJet_integratedCountingPolynomial_jump
              f j l hx hxb hfree
      _ = _ := by simp [hl]
  · rw [if_neg hl]
    apply Finset.sum_eq_zero
    intro j hj
    change normalizedPolynomialJet
        (integratedCountingPolynomial f j (jthPolePoints f j b)) l x -
      normalizedPolynomialJet
        (integratedCountingPolynomial f j (jthPolePoints f j x)) l x = 0
    rw [normalizedPolynomialJet_integratedCountingPolynomial_jump
      f j l hx hxb hfree, if_neg]
    intro hlj
    subst j
    exact hl hj

theorem multiplicity_eq_positive_radialJetJump
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (P : PolynomialPresentation n f) (l : ℕ)
    {x : ℝ} (hx : 0 < x) :
    multiplicity f l x =
      normalizedPolynomialJet (P.rightPieceAt x) l x -
        normalizedPolynomialJet (P.leftPieceAt x) l x := by
  rw [multiplicity_eq_derivativeJump_of_pos f l hx, derivativeJump,
    normalizedRightJet_eq_usingPresentation f P,
    normalizedLeftJet_eq_usingPresentation f P]

theorem normalizedPolynomialJet_radialPolynomial_neg_one
    (p : Polynomial ℝ) (l : ℕ) (x : ℝ) :
    normalizedPolynomialJet (radialPolynomial p (-1)) l x =
      (-1 : ℝ) ^ l * normalizedPolynomialJet p l (-x) := by
  simpa [radialPolynomial] using normalizedPolynomialJet_comp_neg_X p l x

theorem multiplicity_eq_negative_radialJetJump
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (P : PolynomialPresentation n f) (l : ℕ)
    {x : ℝ} (hx : 0 < x) :
    multiplicity f l (-x) =
      normalizedPolynomialJet
          (radialPolynomial (P.leftPieceAt (-x)) (-1)) l x -
        normalizedPolynomialJet
          (radialPolynomial (P.rightPieceAt (-x)) (-1)) l x := by
  rw [multiplicity_eq_pow_mul_derivativeJump_of_neg f l (neg_lt_zero.mpr hx),
    derivativeJump, normalizedRightJet_eq_usingPresentation f P,
    normalizedLeftJet_eq_usingPresentation f P,
    normalizedPolynomialJet_radialPolynomial_neg_one,
    normalizedPolynomialJet_radialPolynomial_neg_one, pow_succ]
  ring

theorem normalizedPolynomialJet_characteristicLocalPolynomial_jump
    {n l : ℕ} (f : NthTropicalMeromorphicFunction n)
    {a x b : ℝ} (hx : 0 < x) (hxb : x < b)
    (hfree : ∀ j : ℕ, ∀ y : ℝ,
      ((a < |y| ∧ |y| < x) ∨ (x < |y| ∧ |y| < b)) →
        multiplicity f j y = 0)
    (pPL pPR pNL pNR : Polynomial ℝ)
    (actPL actPR actNL actNR : Bool)
    (hl : l ∈ Finset.Icc 1 n)
    (hmpos : multiplicity f l x =
      normalizedPolynomialJet pPR l x - normalizedPolynomialJet pPL l x)
    (hmneg : multiplicity f l (-x) =
      normalizedPolynomialJet pNR l x - normalizedPolynomialJet pNL l x) :
    normalizedPolynomialJet
        (characteristicLocalPolynomial f
          (if actPR then pPR else 0) (if actNR then pNR else 0) b) l x -
      normalizedPolynomialJet
        (characteristicLocalPolynomial f
          (if actPL then pPL else 0) (if actNL then pNL else 0) x) l x =
      characteristicJetJump actPL actPR
          (normalizedPolynomialJet pPL l x) (normalizedPolynomialJet pPR l x) +
        characteristicJetJump actNL actNR
          (normalizedPolynomialJet pNL l x) (normalizedPolynomialJet pNR l x) := by
  have hcount := normalizedPolynomialJet_totalCountingLocalPolynomial_jump
    f l hx hxb hfree
  rw [if_pos hl, hmpos, hmneg] at hcount
  simp only [characteristicLocalPolynomial, totalCountingLocalPolynomial,
    normalizedPolynomialJet, map_add, map_sum,
    Polynomial.eval_add, Polynomial.eval_finset_sum,
    ← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul] at ⊢ hcount
  cases actPL <;> cases actPR <;> cases actNL <;> cases actNR <;>
    simp only [if_false, if_true, map_zero, Polynomial.eval_zero,
      characteristicJetJump] at ⊢ <;> norm_num at hcount ⊢ <;> linarith

theorem characteristicJetJump_of_positivePart_germs_nonneg
    {pLeft pRight : Polynomial ℝ}
    (hpLeft : IsWellDefinedPolynomial pLeft)
    (hpRight : IsWellDefinedPolynomial pRight)
    {a x b : ℝ} (ha0 : 0 < a) (hax : a < x) (hxb : x < b)
    (activeLeft activeRight : Bool)
    (hvalue : pLeft.eval x = pRight.eval x)
    (hleft : ∀ y ∈ Set.Ioc a x,
      maxPlusPositivePart (pLeft.eval y) =
        (if activeLeft then pLeft else 0).eval y)
    (hright : ∀ y ∈ Set.Ico x b,
      maxPlusPositivePart (pRight.eval y) =
        (if activeRight then pRight else 0).eval y)
    {l : ℕ} (hl : 1 ≤ l) :
    0 ≤ characteristicJetJump activeLeft activeRight
      (normalizedPolynomialJet pLeft l x)
      (normalizedPolynomialJet pRight l x) := by
  rcases lt_trichotomy (pLeft.eval x) 0 with hneg | hzero | hpos
  · have hactiveLeft : activeLeft = false := by
      cases hact : activeLeft
      · rfl
      · have h := hleft x ⟨hax, le_rfl⟩
        simp only [hact, if_true, Polynomial.eval_zero,
          maxPlusPositivePart, max_eq_right hneg.le] at h
        exact (hneg.ne h.symm).elim
    have hactiveRight : activeRight = false := by
      cases hact : activeRight
      · rfl
      · have h := hright x ⟨le_rfl, hxb⟩
        simp only [hact, if_true, Polynomial.eval_zero, ← hvalue,
          maxPlusPositivePart, max_eq_right hneg.le] at h
        exact (hneg.ne h.symm).elim
    subst activeLeft
    subst activeRight
    exact characteristicJetJump_inactive_inactive_nonneg _ _
  · apply characteristicJetJump_at_zero_nonneg
    · intro hactive
      have hactiveEq : ∀ y ∈ Set.Ioc a x,
          maxPlusPositivePart (pLeft.eval y) = pLeft.eval y := by
        simpa [hactive] using hleft
      rw [normalizedPolynomialJet_eq_iterateDerivative_div]
      exact div_nonpos_of_nonpos_of_nonneg
        (iterateDerivative_nonpos_of_positivePart_active_left hpLeft
          ha0 hax hactiveEq hzero hl) (by positivity)
    · intro hactive
      have hactiveEq : ∀ y ∈ Set.Ico x b,
          maxPlusPositivePart (pRight.eval y) = pRight.eval y := by
        simpa [hactive] using hright
      rw [normalizedPolynomialJet_eq_iterateDerivative_div]
      exact div_nonneg
        (iterateDerivative_nonneg_of_positivePart_active_right hpRight
          (ha0.trans hax) hxb hactiveEq (hvalue.symm.trans hzero) hl)
        (by positivity)
  · have hactiveLeft : activeLeft = true := by
      cases hact : activeLeft
      · have h := hleft x ⟨hax, le_rfl⟩
        simp [hact, maxPlusPositivePart, max_eq_left hpos.le] at h
        linarith
      · rfl
    have hactiveRight : activeRight = true := by
      cases hact : activeRight
      · have h := hright x ⟨le_rfl, hxb⟩
        simp [hact, ← hvalue, maxPlusPositivePart, max_eq_left hpos.le] at h
        linarith
      · rfl
    subst activeLeft
    subst activeRight
    exact characteristicJetJump_active_active_nonneg _ _

/-- The characteristic of a well-defined tropical meromorphic function has
the concrete local polynomial pieces and nonnegative event jets required by
the spline theorem. -/
theorem characteristic_splineEventData_of_wellDefined
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f) :
    PositivePolynomialSplineEventData n (fun r ↦ characteristic r f) := by
  obtain ⟨P, hP⟩ := hf
  intro x hx
  obtain ⟨a₀, b₀, ha₀0, ha₀x, hxb₀, hfree₀⟩ :=
    exists_radial_punctured_multiplicity_free f hx
  let pPL := P.leftPieceAt x
  let pPR := P.rightPieceAt x
  let pNL := radialPolynomial (P.rightPieceAt (-x)) (-1)
  let pNR := radialPolynomial (P.leftPieceAt (-x)) (-1)
  have hpPL : IsWellDefinedPolynomial pPL := hP _
  have hpPR : IsWellDefinedPolynomial pPR := by
    dsimp [pPR]
    simp only [PolynomialPresentation.rightPieceAt]
    split_ifs <;> exact hP _
  have hpNL : IsWellDefinedPolynomial pNL := by
    exact (show IsWellDefinedPolynomial (P.rightPieceAt (-x)) from by
      simp only [PolynomialPresentation.rightPieceAt]
      split_ifs <;> exact hP _).radial (Or.inr rfl)
  have hpNR : IsWellDefinedPolynomial pNR := by
    exact (hP _).radial (Or.inr rfl)
  obtain ⟨ap, hap, hfPL⟩ := P.exists_left_germ_interval x
  obtain ⟨bp, hbp, hfPR⟩ := P.exists_right_germ_interval x
  obtain ⟨cn, hcn, hfNL⟩ := P.exists_right_germ_interval (-x)
  obtain ⟨dn, hdn, hfNR⟩ := P.exists_left_germ_interval (-x)
  obtain ⟨aPL, actPL, haPL0, haPLx, hactPL⟩ :=
    exists_positivePart_left_polynomial hpPL hx
  obtain ⟨aNL, actNL, haNL0, haNLx, hactNL⟩ :=
    exists_positivePart_left_polynomial hpNL hx
  obtain ⟨bPR, actPR, hxbPR, hactPR⟩ :=
    exists_positivePart_right_polynomial hpPR hx
  obtain ⟨bNR, actNR, hxbNR, hactNR⟩ :=
    exists_positivePart_right_polynomial hpNR hx
  let a := max a₀ (max ap (max (-cn) (max aPL aNL)))
  let b := min b₀ (min bp (min (-dn) (min bPR bNR)))
  have ha0 : 0 < a := ha₀0.trans_le (le_max_left _ _)
  have hax : a < x := by
    apply max_lt ha₀x
    apply max_lt hap
    apply max_lt (by linarith)
    exact max_lt haPLx haNLx
  have hxb : x < b := by
    apply lt_min hxb₀
    apply lt_min hbp
    apply lt_min (by linarith)
    exact lt_min hxbPR hxbNR
  have ha₀a : a₀ ≤ a := le_max_left _ _
  have hbb₀ : b ≤ b₀ := min_le_left _ _
  have hap_a : ap ≤ a :=
    calc
      ap ≤ max ap (max (-cn) (max aPL aNL)) := le_max_left _ _
      _ ≤ a := le_max_right _ _
  have hcn_a : -cn ≤ a := by
    calc
      -cn ≤ max (-cn) (max aPL aNL) := le_max_left _ _
      _ ≤ max ap (max (-cn) (max aPL aNL)) := le_max_right _ _
      _ ≤ a := le_max_right _ _
  have haPL_a : aPL ≤ a := by
    calc
      aPL ≤ max aPL aNL := le_max_left _ _
      _ ≤ max (-cn) (max aPL aNL) := le_max_right _ _
      _ ≤ max ap (max (-cn) (max aPL aNL)) := le_max_right _ _
      _ ≤ a := le_max_right _ _
  have haNL_a : aNL ≤ a := by
    calc
      aNL ≤ max aPL aNL := le_max_right _ _
      _ ≤ max (-cn) (max aPL aNL) := le_max_right _ _
      _ ≤ max ap (max (-cn) (max aPL aNL)) := le_max_right _ _
      _ ≤ a := le_max_right _ _
  have hb_bp : b ≤ bp := by
    calc
      b ≤ min bp (min (-dn) (min bPR bNR)) := min_le_right _ _
      _ ≤ bp := min_le_left _ _
  have hb_dn : b ≤ -dn := by
    calc
      b ≤ min bp (min (-dn) (min bPR bNR)) := min_le_right _ _
      _ ≤ min (-dn) (min bPR bNR) := min_le_right _ _
      _ ≤ -dn := min_le_left _ _
  have hb_bPR : b ≤ bPR := by
    calc
      b ≤ min bp (min (-dn) (min bPR bNR)) := min_le_right _ _
      _ ≤ min (-dn) (min bPR bNR) := min_le_right _ _
      _ ≤ min bPR bNR := min_le_right _ _
      _ ≤ bPR := min_le_left _ _
  have hb_bNR : b ≤ bNR := by
    calc
      b ≤ min bp (min (-dn) (min bPR bNR)) := min_le_right _ _
      _ ≤ min (-dn) (min bPR bNR) := min_le_right _ _
      _ ≤ min bPR bNR := min_le_right _ _
      _ ≤ bNR := min_le_right _ _
  have hfree : ∀ j : ℕ, ∀ y : ℝ,
      ((a < |y| ∧ |y| < x) ∨ (x < |y| ∧ |y| < b)) →
        multiplicity f j y = 0 := by
    intro j y hy
    apply hfree₀ j y
    rcases hy with hy | hy
    · exact Or.inl ⟨ha₀a.trans_lt hy.1, hy.2⟩
    · exact Or.inr ⟨hy.1, hy.2.trans_le hbb₀⟩
  let pLeft := characteristicLocalPolynomial f
    (if actPL then pPL else 0) (if actNL then pNL else 0) x
  let pRight := characteristicLocalPolynomial f
    (if actPR then pPR else 0) (if actNR then pNR else 0) b
  have hpPLdeg : pPL.natDegree ≤ n := P.leftPieceAt_natDegree_le x
  have hpPRdeg : pPR.natDegree ≤ n := P.rightPieceAt_natDegree_le x
  have hpNLdeg : pNL.natDegree ≤ n := by
    dsimp [pNL, radialPolynomial]
    exact Polynomial.natDegree_comp_le.trans (by
      simpa using P.rightPieceAt_natDegree_le (-x))
  have hpNRdeg : pNR.natDegree ≤ n := by
    dsimp [pNR, radialPolynomial]
    exact Polynomial.natDegree_comp_le.trans (by
      simpa using P.leftPieceAt_natDegree_le (-x))
  have hselectedPLdeg : (if actPL then pPL else 0).natDegree ≤ n := by
    cases actPL <;> simp [hpPLdeg]
  have hselectedPRdeg : (if actPR then pPR else 0).natDegree ≤ n := by
    cases actPR <;> simp [hpPRdeg]
  have hselectedNLdeg : (if actNL then pNL else 0).natDegree ≤ n := by
    cases actNL <;> simp [hpNLdeg]
  have hselectedNRdeg : (if actNR then pNR else 0).natDegree ≤ n := by
    cases actNR <;> simp [hpNRdeg]
  have hpLeftdeg : pLeft.natDegree ≤ n :=
    characteristicLocalPolynomial_natDegree_le f x
      hselectedPLdeg hselectedNLdeg
  have hpRightdeg : pRight.natDegree ≤ n :=
    characteristicLocalPolynomial_natDegree_le f b
      hselectedPRdeg hselectedNRdeg
  have hleft : ∀ y ∈ Set.Ioc a x, characteristic y f = pLeft.eval y := by
    intro y hy
    have hay_ap : ap < y := hap_a.trans_lt hy.1
    have hay_cn : -cn < y := hcn_a.trans_lt hy.1
    have hay_aPL : aPL < y := haPL_a.trans_lt hy.1
    have hay_aNL : aNL < y := haNL_a.trans_lt hy.1
    have hfpos : f y = pPL.eval y := by
      by_cases hyx : y = x
      · subst y
        simpa [pPL] using (P.leftPieceAt_eval x).symm
      · exact hfPL y ⟨hay_ap, lt_of_le_of_ne hy.2 hyx⟩
    have hfneg : f (-y) = pNL.eval y := by
      by_cases hyx : y = x
      · subst y
        simpa [pNL] using (P.rightPieceAt_eval (-x)).symm
      · have hylt : y < x := lt_of_le_of_ne hy.2 hyx
        change f (-y) = (radialPolynomial (P.rightPieceAt (-x)) (-1)).eval y
        rw [radialPolynomial_eval]
        have hleft : -x < -y := neg_lt_neg hylt
        have hright : -y < cn := by
          have := neg_lt_neg hay_cn
          simpa using this
        simpa only [neg_one_mul] using hfNL (-y) ⟨hleft, hright⟩
    apply characteristic_eq_localPolynomial_eval f _ _ x y
    · rw [hfpos]
      exact hactPL y ⟨hay_aPL, hy.2⟩
    · rw [hfneg]
      exact hactNL y ⟨hay_aNL, hy.2⟩
    · intro j hj
      exact jthPolePoints_eq_at_event_of_mem_Ioc f j hy hfree
  have hright : ∀ y ∈ Set.Ioo x b, characteristic y f = pRight.eval y := by
    intro y hy
    have hy_bp : y < bp := hy.2.trans_le hb_bp
    have hy_dn : y < -dn := hy.2.trans_le hb_dn
    have hy_bPR : y < bPR := hy.2.trans_le hb_bPR
    have hy_bNR : y < bNR := hy.2.trans_le hb_bNR
    have hfpos : f y = pPR.eval y := hfPR y ⟨hy.1, hy_bp⟩
    have hfneg : f (-y) = pNR.eval y := by
      change f (-y) = (radialPolynomial (P.leftPieceAt (-x)) (-1)).eval y
      rw [radialPolynomial_eval]
      have hleft : dn < -y := by
        have := neg_lt_neg hy_dn
        simpa using this
      have hright : -y < -x := neg_lt_neg hy.1
      simpa only [neg_one_mul] using hfNR (-y) ⟨hleft, hright⟩
    apply characteristic_eq_localPolynomial_eval f _ _ b y
    · rw [hfpos]
      exact hactPR y ⟨hy.1.le, hy_bPR⟩
    · rw [hfneg]
      exact hactNR y ⟨hy.1.le, hy_bNR⟩
    · intro j hj
      exact jthPolePoints_eq_at_outer_of_mem_Ioo f j hy hfree
  have hcountJetZero := normalizedPolynomialJet_totalCountingLocalPolynomial_jump
    f 0 hx hxb hfree
  have hcountZero :
      (totalCountingLocalPolynomial f b).eval x =
        (totalCountingLocalPolynomial f x).eval x := by
    simp only [normalizedPolynomialJet, Polynomial.hasseDeriv_zero] at hcountJetZero
    exact sub_eq_zero.mp (by simpa using hcountJetZero)
  have hfPLx : pPL.eval x = f x := P.leftPieceAt_eval x
  have hfPRx : pPR.eval x = f x := P.rightPieceAt_eval x
  have hfNLx : pNL.eval x = f (-x) := by
    simpa [pNL] using P.rightPieceAt_eval (-x)
  have hfNRx : pNR.eval x = f (-x) := by
    simpa [pNR] using P.leftPieceAt_eval (-x)
  have hposZero : (if actPL then pPL else 0).eval x =
      (if actPR then pPR else 0).eval x := by
    calc
      _ = maxPlusPositivePart (pPL.eval x) := (hactPL x ⟨haPLx, le_rfl⟩).symm
      _ = maxPlusPositivePart (f x) := by rw [hfPLx]
      _ = maxPlusPositivePart (pPR.eval x) := by rw [hfPRx]
      _ = _ := hactPR x ⟨le_rfl, hxbPR⟩
  have hnegZero : (if actNL then pNL else 0).eval x =
      (if actNR then pNR else 0).eval x := by
    calc
      _ = maxPlusPositivePart (pNL.eval x) := (hactNL x ⟨haNLx, le_rfl⟩).symm
      _ = maxPlusPositivePart (f (-x)) := by rw [hfNLx]
      _ = maxPlusPositivePart (pNR.eval x) := by rw [hfNRx]
      _ = _ := hactNR x ⟨le_rfl, hxbNR⟩
  have hmatch : pLeft.eval x = pRight.eval x := by
    dsimp [pLeft, pRight]
    simp only [characteristicLocalPolynomial, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C]
    simp only [totalCountingLocalPolynomial] at hcountZero
    rw [hposZero, hnegZero, hcountZero]
  refine ⟨a, b, pLeft, pRight, hax, hxb, hpLeftdeg, hpRightdeg,
    hleft, hright, hmatch, ?_⟩
  intro l hl
  by_cases hl0 : l = 0
  · subst l
    simpa using hmatch.le
  · have hl1 : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr hl0
    have hlmem : l ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hl1, hl⟩
    have hmpos := multiplicity_eq_positive_radialJetJump f P l hx
    have hmneg := multiplicity_eq_negative_radialJetJump f P l hx
    have hjump := normalizedPolynomialJet_characteristicLocalPolynomial_jump
      f hx hxb hfree pPL pPR pNL pNR actPL actPR actNL actNR
        hlmem hmpos hmneg
    have hPLPR : pPL.eval x = pPR.eval x := by
      rw [P.leftPieceAt_eval, P.rightPieceAt_eval]
    have hNLNR : pNL.eval x = pNR.eval x := by
      change (radialPolynomial (P.rightPieceAt (-x)) (-1)).eval x =
        (radialPolynomial (P.leftPieceAt (-x)) (-1)).eval x
      rw [radialPolynomial_eval, radialPolynomial_eval]
      simp only [neg_one_mul]
      rw [
        P.rightPieceAt_eval, P.leftPieceAt_eval]
    have hjetPos := characteristicJetJump_of_positivePart_germs_nonneg
      hpPL hpPR ha0 hax hxb actPL actPR hPLPR
      (fun y hy ↦ hactPL y ⟨haPL_a.trans_lt hy.1, hy.2⟩)
      (fun y hy ↦ hactPR y ⟨hy.1,
        hy.2.trans_le hb_bPR⟩) hl1
    have hjetNeg := characteristicJetJump_of_positivePart_germs_nonneg
      hpNL hpNR ha0 hax hxb actNL actNR hNLNR
      (fun y hy ↦ hactNL y ⟨haNL_a.trans_lt hy.1, hy.2⟩)
      (fun y hy ↦ hactNR y ⟨hy.1,
        hy.2.trans_le hb_bNR⟩) hl1
    have hnorm : normalizedPolynomialJet pLeft l x ≤
        normalizedPolynomialJet pRight l x := by
      linarith
    rw [normalizedPolynomialJet_eq_iterateDerivative_div,
      normalizedPolynomialJet_eq_iterateDerivative_div] at hnorm
    exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < l.factorial)).mp hnorm

/-! ## Initial polynomial at the origin -/

/-- On a sufficiently small positive interval starting at zero, the positive
part of a well-defined polynomial is polynomial.  The extra clauses record
exactly the activity and jet signs needed when its value at zero vanishes. -/
theorem exists_positivePart_from_zero_polynomial
    {p : Polynomial ℝ} (hp : IsWellDefinedPolynomial p) :
    ∃ b : ℝ, ∃ active : Bool, 0 < b ∧
      (∀ y ∈ Set.Ioo (0 : ℝ) b,
        maxPlusPositivePart (p.eval y) =
          (if active then p else 0).eval y) ∧
      (0 < p.eval 0 → active = true) ∧
      (p.eval 0 < 0 → active = false) ∧
      (p.eval 0 = 0 → active = true →
        ∀ l : ℕ, 1 ≤ l → 0 ≤ normalizedPolynomialJet p l 0) := by
  rcases lt_trichotomy (p.eval 0) 0 with hneg | hzero | hpos
  · have hnhds : {y : ℝ | p.eval y < 0} ∈ nhds 0 :=
      p.continuousAt.preimage_mem_nhds (Iio_mem_nhds hneg)
    obtain ⟨l, u, h0, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
    refine ⟨u, false, h0.2, ?_, ?_, ?_, ?_⟩
    · intro y hy
      have := hsub ⟨h0.1.trans hy.1, hy.2⟩
      change p.eval y < 0 at this
      simp [maxPlusPositivePart, max_eq_right this.le]
    · exact fun h ↦ (not_lt_of_ge h.le hneg).elim
    · exact fun _ ↦ rfl
    · exact fun hz ↦ (hneg.ne hz).elim
  · rcases hp.commonSign with hcoeff | hcoeff
    · refine ⟨1, true, by norm_num, ?_, ?_, ?_, ?_⟩
      · intro y hy
        have hmono := polynomial_eval_monotoneOn_Ici_of_coeff_nonneg hcoeff
        have hnonneg : 0 ≤ p.eval y := by
          rw [← hzero]
          exact hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy.1.le) hy.1.le
        simp [maxPlusPositivePart, max_eq_left hnonneg]
      · exact fun h ↦ (h.ne' hzero).elim
      · exact fun h ↦ (h.ne hzero).elim
      · intro hz hactive l hl
        rw [normalizedPolynomialJet, ← Polynomial.coeff_zero_eq_eval_zero,
          Polynomial.hasseDeriv_coeff]
        simpa using hcoeff l (Nat.ne_of_gt hl)
    · refine ⟨1, false, by norm_num, ?_, ?_, ?_, ?_⟩
      · intro y hy
        have hanti := polynomial_eval_antitoneOn_Ici_of_coeff_nonpos hcoeff
        have hnonpos : p.eval y ≤ 0 := by
          rw [← hzero]
          exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy.1.le) hy.1.le
        simp [maxPlusPositivePart, max_eq_right hnonpos]
      · exact fun h ↦ (h.ne' hzero).elim
      · exact fun h ↦ (h.ne hzero).elim
      · intro hz hactive
        contradiction
  · have hnhds : {y : ℝ | 0 < p.eval y} ∈ nhds 0 :=
      p.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hpos)
    obtain ⟨l, u, h0, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
    refine ⟨u, true, h0.2, ?_, ?_, ?_, ?_⟩
    · intro y hy
      have := hsub ⟨h0.1.trans hy.1, hy.2⟩
      change 0 < p.eval y at this
      simp [maxPlusPositivePart, max_eq_left this.le]
    · exact fun _ ↦ rfl
    · exact fun h ↦ (not_lt_of_ge h.le hpos).elim
    · exact fun hz ↦ ((ne_of_gt hpos) hz).elim

theorem normalizedPolynomialJet_characteristicLocalPolynomial_at_zero
    {n k : ℕ} (f : NthTropicalMeromorphicFunction n)
    (pPositive pNegative : Polynomial ℝ)
    (activePositive activeNegative : Bool) (R : ℝ)
    (hk : k ∈ Finset.Icc 1 n)
    (hPole : ∀ j ∈ Finset.Icc 1 n,
      jthPolePoints f j R = ({0} : Finset ℝ).filter
        (fun y ↦ IsJthPole f j y))
    (hmult : multiplicity f k 0 =
      normalizedPolynomialJet pPositive k 0 +
        normalizedPolynomialJet pNegative k 0) :
    normalizedPolynomialJet
        (characteristicLocalPolynomial f
          (if activePositive then pPositive else 0)
          (if activeNegative then pNegative else 0) R) k 0 =
      ((if activePositive then normalizedPolynomialJet pPositive k 0 else 0) +
          (if activeNegative then normalizedPolynomialJet pNegative k 0 else 0) +
          max (-(normalizedPolynomialJet pPositive k 0 +
            normalizedPolynomialJet pNegative k 0)) 0) / 2 := by
  classical
  have hlocal : normalizedPolynomialJet
        (characteristicLocalPolynomial f
          (if activePositive then pPositive else 0)
          (if activeNegative then pNegative else 0) R) k 0 =
      (1 / 2) * (normalizedPolynomialJet
          (if activePositive then pPositive else 0) k 0 +
        normalizedPolynomialJet
          (if activeNegative then pNegative else 0) k 0) +
      ∑ j ∈ Finset.Icc 1 n, normalizedPolynomialJet
        (integratedCountingPolynomial f j (jthPolePoints f j R)) k 0 := by
    cases activePositive <;> cases activeNegative <;>
      simp [characteristicLocalPolynomial, normalizedPolynomialJet,
        ← Polynomial.smul_eq_C_mul, Polynomial.eval_finsetSum] <;> ring
  have hcount :
      (∑ j ∈ Finset.Icc 1 n,
        normalizedPolynomialJet
          (integratedCountingPolynomial f j (jthPolePoints f j R)) k 0) =
        max (-multiplicity f k 0) 0 / 2 := by
    have hmonomial (j : ℕ) :
        normalizedPolynomialJet (Polynomial.X ^ j) k 0 =
          if k = j then 1 else 0 := by
      simpa using normalizedPolynomialJet_shiftedMonomial (0 : ℝ) k j
    calc
      _ = ∑ j ∈ Finset.Icc 1 n, if k = j then
          (if IsJthPole f j 0 then rootOrPoleMultiplicity f j 0 / 2 else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [normalizedPolynomialJet_integratedCountingPolynomial, hPole j hj]
            simp only [Finset.sum_filter, Finset.sum_singleton]
            by_cases hkj : k = j
            · subst j
              by_cases hpole : IsJthPole f k 0
              · simp [hpole, hmonomial]
                ring
              · simp [hpole]
            · simp [hkj, hmonomial]
      _ = (if IsJthPole f k 0 then rootOrPoleMultiplicity f k 0 / 2 else 0) := by
            simp [hk]
      _ = max (-multiplicity f k 0) 0 / 2 := by
            by_cases hpole : multiplicity f k 0 < 0
            · simp only [IsJthPole, hpole, if_true]
              simp [rootOrPoleMultiplicity,
                abs_of_neg hpole, max_eq_left (neg_nonneg.mpr hpole.le)]
            · simp only [IsJthPole, hpole, if_false]
              simp [max_eq_right (neg_nonpos.mpr
                (le_of_not_gt hpole))]
  rw [hlocal, hcount, hmult]
  cases activePositive <;> cases activeNegative <;>
    simp [normalizedPolynomialJet] <;> ring

theorem multiplicity_zero_eq_radialJetSum
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (P : PolynomialPresentation n f) (k : ℕ) :
    multiplicity f k 0 =
      normalizedPolynomialJet (P.piece 1) k 0 +
        normalizedPolynomialJet (radialPolynomial (P.piece 0) (-1)) k 0 := by
  rw [← P.cutPoint_zero, multiplicity_cutPoint_of_presentation,
    presentationMultiplicityAtCutPoint_zero, P.cutPoint_zero,
    normalizedPolynomialJet_radialPolynomial_neg_one]
  simp only [neg_zero, pow_succ]
  ring

/-- Before the first positive and negative presentation cuts, the only
possible pole is the intrinsic point `0`. -/
theorem exists_origin_pole_set_interval
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (P : PolynomialPresentation n f) :
    ∃ R : ℝ, 0 < R ∧ ∀ j : ℕ, ∀ r ∈ Set.Ioo (0 : ℝ) R,
      jthPolePoints f j r = ({0} : Finset ℝ).filter
        (fun y ↦ IsJthPole f j y) := by
  classical
  let R := min (P.cutPoint 1) (-P.cutPoint (-1))
  have hcpos : 0 < P.cutPoint 1 := by
    rw [← P.cutPoint_zero]
    exact P.cutPoint_strictMono (by omega)
  have hcneg : P.cutPoint (-1) < 0 := by
    rw [← P.cutPoint_zero]
    exact P.cutPoint_strictMono (by omega)
  have hR : 0 < R := lt_min hcpos (by linarith)
  refine ⟨R, hR, ?_⟩
  intro j r hr
  ext y
  simp only [mem_jthPolePoints_iff, Finset.mem_filter,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hyr, hpole⟩
    by_cases hy0 : y = 0
    · exact ⟨hy0, hpole⟩
    · have hyabs : |y| < r := (abs_lt).2 hyr
      have hyR : |y| < R := hyabs.trans hr.2
      rcases lt_or_gt_of_ne hy0 with hyneg | hypos
      · have hymem : y ∈ Set.Ioo (P.cutPoint (-1)) 0 := by
          have hRneg : R ≤ -P.cutPoint (-1) := min_le_right _ _
          rw [abs_of_neg hyneg] at hyR
          constructor <;> linarith
        have hzero := multiplicity_eq_zero_of_eqOn_Ioo P (P.piece 0)
          hymem hy0 (fun z hz ↦ P.eq_piece 0 ⟨by simpa using hz.1.le,
            by simpa [P.cutPoint_zero] using hz.2.le⟩) j
        exact (by simp [IsJthPole, hzero] at hpole)
      · have hymem : y ∈ Set.Ioo 0 (P.cutPoint 1) := by
          have hRpos : R ≤ P.cutPoint 1 := min_le_left _ _
          rw [abs_of_pos hypos] at hyR
          exact ⟨hypos, hyR.trans_le hRpos⟩
        have hzero := multiplicity_eq_zero_of_eqOn_Ioo P (P.piece 1)
          hymem hy0 (fun z hz ↦ P.eq_piece 1 ⟨by
            simpa [P.cutPoint_zero] using hz.1.le, hz.2.le⟩) j
        exact (by simp [IsJthPole, hzero] at hpole)
  · rintro ⟨rfl, hpole⟩
    exact ⟨⟨neg_lt_zero.mpr hr.1, hr.1⟩, hpole⟩

theorem characteristic_splineInitialData_of_wellDefined
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f) :
    PositivePolynomialSplineInitialData n (fun r ↦ characteristic r f) := by
  obtain ⟨P, hP⟩ := hf
  let pPositive := P.piece 1
  let pNegative := radialPolynomial (P.piece 0) (-1)
  have hpPositive : IsWellDefinedPolynomial pPositive := hP 1
  have hpNegative : IsWellDefinedPolynomial pNegative :=
    (hP 0).radial (Or.inr rfl)
  have hpPositiveDeg : pPositive.natDegree ≤ n := P.piece_natDegree_le 1
  have hpNegativeDeg : pNegative.natDegree ≤ n := by
    dsimp [pNegative, radialPolynomial]
    exact Polynomial.natDegree_comp_le.trans (by
      simpa using P.piece_natDegree_le 0)
  have hPositive0 : pPositive.eval 0 = f 0 := by
    exact (P.eq_piece 1 ⟨by simp [P.cutPoint_zero], by
      rw [← P.cutPoint_zero]
      exact (P.cutPoint_strictMono (by omega)).le⟩).symm
  have hNegative0 : pNegative.eval 0 = f 0 := by
    change (radialPolynomial (P.piece 0) (-1)).eval 0 = f 0
    rw [radialPolynomial_eval]
    simpa [P.cutPoint_zero] using (P.eq_piece 0 ⟨
      (P.cutPoint_strictMono (by omega)).le, le_rfl⟩).symm
  obtain ⟨bPositive, activePositive, hbPositive,
      hactivePositive, hposPositive, hnegPositive, hzeroPositive⟩ :=
    exists_positivePart_from_zero_polynomial hpPositive
  obtain ⟨bNegative, activeNegative, hbNegative,
      hactiveNegative, hposNegative, hnegNegative, hzeroNegative⟩ :=
    exists_positivePart_from_zero_polynomial hpNegative
  obtain ⟨R, hR, hPole⟩ := exists_origin_pole_set_interval f P
  have hCutPositive : 0 < P.cutPoint 1 := by
    rw [← P.cutPoint_zero]
    exact P.cutPoint_strictMono (by omega)
  have hCutNegative : 0 < -P.cutPoint (-1) := by
    have h := P.cutPoint_strictMono (show (-1 : ℤ) < 0 by omega)
    rw [P.cutPoint_zero] at h
    linarith
  let Rfix := min (R / 2)
    (min (P.cutPoint 1 / 2) ((-P.cutPoint (-1)) / 2))
  have hRfix : Rfix ∈ Set.Ioo (0 : ℝ) R := by
    constructor
    · dsimp [Rfix]
      exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
    · exact (min_le_left _ _).trans_lt (by linarith)
  have hRfixCutPositive : Rfix < P.cutPoint 1 := by
    change min (R / 2)
      (min (P.cutPoint 1 / 2) ((-P.cutPoint (-1)) / 2)) < P.cutPoint 1
    exact (min_le_right _ _).trans_lt
      ((min_le_left _ _).trans_lt (by linarith))
  have hRfixCutNegative : Rfix < -P.cutPoint (-1) := by
    change min (R / 2)
      (min (P.cutPoint 1 / 2) ((-P.cutPoint (-1)) / 2)) < -P.cutPoint (-1)
    exact (min_le_right _ _).trans_lt
      ((min_le_right _ _).trans_lt (by linarith))
  let r₀ := min Rfix (min bPositive bNegative)
  have hr₀ : 0 < r₀ := lt_min hRfix.1 (lt_min hbPositive hbNegative)
  let pInit := characteristicLocalPolynomial f
    (if activePositive then pPositive else 0)
    (if activeNegative then pNegative else 0) Rfix
  have hselPositiveDeg :
      (if activePositive then pPositive else 0).natDegree ≤ n := by
    cases activePositive <;> simp [hpPositiveDeg]
  have hselNegativeDeg :
      (if activeNegative then pNegative else 0).natDegree ≤ n := by
    cases activeNegative <;> simp [hpNegativeDeg]
  have hpInitDeg : pInit.natDegree ≤ n :=
    characteristicLocalPolynomial_natDegree_le f Rfix
      hselPositiveDeg hselNegativeDeg
  have hchar : ∀ r ∈ Set.Ioo (0 : ℝ) r₀,
      characteristic r f = pInit.eval r := by
    intro r hr
    have hrRfix : r < Rfix := hr.2.trans_le (min_le_left _ _)
    have hrbPositive : r < bPositive := hr.2.trans_le <| by
      exact (min_le_right Rfix _).trans (min_le_left _ _)
    have hrbNegative : r < bNegative := hr.2.trans_le <| by
      exact (min_le_right Rfix _).trans (min_le_right _ _)
    have hrR : r < R := hrRfix.trans hRfix.2
    have hcutPos : r ≤ P.cutPoint 1 :=
      (hrRfix.trans hRfixCutPositive).le
    have hcutNeg : P.cutPoint (-1) ≤ -r := by
      linarith [hrRfix.trans hRfixCutNegative]
    have hfpos : f r = pPositive.eval r :=
      P.eq_piece 1 ⟨by simpa [P.cutPoint_zero] using hr.1.le, hcutPos⟩
    have hfneg : f (-r) = pNegative.eval r := by
      change f (-r) = (radialPolynomial (P.piece 0) (-1)).eval r
      rw [radialPolynomial_eval]
      simpa only [neg_one_mul] using
        P.eq_piece 0 ⟨hcutNeg, by simpa [P.cutPoint_zero] using hr.1.le⟩
    apply characteristic_eq_localPolynomial_eval f _ _ Rfix r
    · rw [hfpos]
      exact hactivePositive r ⟨hr.1, hrbPositive⟩
    · rw [hfneg]
      exact hactiveNegative r ⟨hr.1, hrbNegative⟩
    · intro j hj
      rw [hPole j r ⟨hr.1, hrR⟩, hPole j Rfix hRfix]
  have hPoleFix : ∀ j ∈ Finset.Icc 1 n,
      jthPolePoints f j Rfix = ({0} : Finset ℝ).filter
        (fun y ↦ IsJthPole f j y) := by
    intro j hj
    exact hPole j Rfix hRfix
  have hcoeff : ∀ k : ℕ, k ≠ 0 → 0 ≤ pInit.coeff k := by
    intro k hk0
    by_cases hkn : k ≤ n
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hkmem : k ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hk1, hkn⟩
      have hmult := multiplicity_zero_eq_radialJetSum f P k
      have hjet := normalizedPolynomialJet_characteristicLocalPolynomial_at_zero
        f pPositive pNegative activePositive activeNegative Rfix
          hkmem hPoleFix hmult
      have hcoeffJet : pInit.coeff k = normalizedPolynomialJet pInit k 0 := by
        simp [normalizedPolynomialJet, ← Polynomial.coeff_zero_eq_eval_zero,
          Polynomial.hasseDeriv_coeff]
      rw [hcoeffJet, hjet]
      rcases lt_trichotomy (f 0) 0 with hfneg | hfzero | hfpos
      · have haPos : activePositive = false :=
          hnegPositive (by simpa [hPositive0] using hfneg)
        have haNeg : activeNegative = false :=
          hnegNegative (by simpa [hNegative0] using hfneg)
        subst activePositive
        subst activeNegative
        simpa [characteristicInitialCoefficient] using
          characteristicInitialCoefficient_sameSign_nonneg false
            (normalizedPolynomialJet pPositive k 0)
            (normalizedPolynomialJet pNegative k 0) 1 (by norm_num)
      · have hposJet : activePositive = true →
            0 ≤ normalizedPolynomialJet pPositive k 0 := by
          intro hactive
          exact hzeroPositive (by simpa [hPositive0] using hfzero)
            hactive k hk1
        have hnegJet : activeNegative = true →
            0 ≤ normalizedPolynomialJet pNegative k 0 := by
          intro hactive
          exact hzeroNegative (by simpa [hNegative0] using hfzero)
            hactive k hk1
        simpa [characteristicInitialCoefficient] using
          characteristicInitialCoefficient_nonneg activePositive activeNegative
            (normalizedPolynomialJet pPositive k 0)
            (normalizedPolynomialJet pNegative k 0) 1 (by norm_num)
            hposJet hnegJet
      · have haPos : activePositive = true :=
          hposPositive (by simpa [hPositive0] using hfpos)
        have haNeg : activeNegative = true :=
          hposNegative (by simpa [hNegative0] using hfpos)
        subst activePositive
        subst activeNegative
        simpa [characteristicInitialCoefficient] using
          characteristicInitialCoefficient_sameSign_nonneg true
            (normalizedPolynomialJet pPositive k 0)
            (normalizedPolynomialJet pNegative k 0) 1 (by norm_num)
    · rw [pInit.coeff_eq_zero_of_natDegree_lt (hpInitDeg.trans_lt
          (lt_of_not_ge hkn))]
  intro l hl
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr
  by_cases hl0 : l = 0
  · subst l
    change 0 ≤ characteristic r f
    exact characteristic_nonneg r f
  · have hiter := iteratedLeftDeriv_eq_iterateDerivative_on_Ioo
      (fun s ↦ characteristic s f) pInit hchar l hr
    rw [hiter]
    exact iterateDerivative_eval_nonneg_of_coeff_nonneg hcoeff
      (Nat.one_le_iff_ne_zero.mpr hl0) hr.1.le

/-- The derivative-tower part of Lemma 4.4 in its original quantifier form:
well-definedness alone implies nonnegativity and monotonicity of every left
derivative through order `n`. -/
theorem characteristicAbsoluteMonotonicity
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f) :
    CharacteristicAbsoluteMonotonicity f := by
  have h := positivePolynomialSpline_absoluteMonotonicity
    (characteristic_splineInitialData_of_wellDefined hf)
    (characteristic_splineEventData_of_wellDefined hf)
  exact ⟨h.1, h.2⟩

/-- The standard `ConvexOn` form of the convexity clause in Lemma 4.4.
Here `1 ≤ n` records the paper's convention `n ∈ ℕ` (positive natural
numbers), which Lean's `Nat` type does not impose automatically. -/
theorem characteristicConvexOn_of_wellDefined
    {n : ℕ} (hn : 1 ≤ n) {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f) :
    CharacteristicConvex f :=
  positivePolynomialSpline_convexOn hn
    (characteristic_splineEventData_of_wellDefined hf)
    ((characteristicAbsoluteMonotonicity hf).2 1 hn)

/-- Convexity also holds in Lean's extra order-zero case.  In that case all
local characteristic polynomials have degree zero, so the characteristic is
both nondecreasing and nonincreasing on the positive axis and hence constant
there.  This all-order wrapper is useful for automatically constructed
quotients whose exact order may drop to zero. -/
theorem characteristicConvexOn_of_wellDefined_allOrder
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f) :
    CharacteristicConvex f := by
  by_cases hn : 1 ≤ n
  · exact characteristicConvexOn_of_wellDefined hn hf
  · have hn0 : n = 0 := by omega
    subst n
    let g : ℝ → ℝ := fun r ↦ characteristic r f
    have hdata : ContinuousPolynomialSplineEventData 0 g :=
      (characteristic_splineEventData_of_wellDefined hf).continuousData
    have hderiv : ∀ r : ℝ, 0 < r → iteratedLeftDeriv 1 g r = 0 := by
      intro r hr
      obtain ⟨a, b, p, q, har, hrb, hp, hq, hleft, hright, hmatch⟩ :=
        hdata r hr
      rw [iteratedLeftDeriv_eq_iterateDerivative_on_Ioc g p har hleft 1
        ⟨har, le_rfl⟩]
      rw [Polynomial.eq_C_of_natDegree_le_zero hp]
      simp
    have hmono : MonotoneOn g (Set.Ioi 0) := by
      intro x hx y hy hxy
      rcases hxy.eq_or_lt with rfl | hxy
      · exact le_rfl
      · apply continuousPolynomialSpline_endpoints_le_of_leftDeriv_nonnegative
          hdata hx hxy
        intro r hr
        rw [hderiv r (hx.trans hr.1)]
    have hdataNeg : ContinuousPolynomialSplineEventData 0 (fun r ↦ -g r) := by
      intro x hx
      obtain ⟨a, b, p, q, hax, hxb, hp, hq, hleft, hright, hmatch⟩ :=
        hdata x hx
      refine ⟨a, b, -p, -q, hax, hxb, ?_, ?_, ?_, ?_, ?_⟩
      · simpa using hp
      · simpa using hq
      · intro y hy
        change -g y = (-p).eval y
        rw [hleft y hy]
        simp
      · intro y hy
        change -g y = (-q).eval y
        rw [hright y hy]
        simp
      · simp [hmatch]
    have hderivNeg : ∀ r : ℝ, 0 < r →
        iteratedLeftDeriv 1 (fun s ↦ -g s) r = 0 := by
      intro r hr
      obtain ⟨a, b, p, q, har, hrb, hp, hq, hleft, hright, hmatch⟩ :=
        hdataNeg r hr
      rw [iteratedLeftDeriv_eq_iterateDerivative_on_Ioc
        (fun s ↦ -g s) p har hleft 1 ⟨har, le_rfl⟩]
      rw [Polynomial.eq_C_of_natDegree_le_zero hp]
      simp
    have hanti : AntitoneOn g (Set.Ioi 0) := by
      intro x hx y hy hxy
      rcases hxy.eq_or_lt with rfl | hxy
      · exact le_rfl
      · have hneg :=
          continuousPolynomialSpline_endpoints_le_of_leftDeriv_nonnegative
            hdataNeg hx hxy
              (fun r hr ↦ by rw [hderivNeg r (hx.trans hr.1)])
        change -g x ≤ -g y at hneg
        linarith
    change ConvexOn ℝ (Set.Ioi 0) g
    rw [convexOn_iff_slope_mono_adjacent]
    refine ⟨convex_Ioi 0, ?_⟩
    intro x y z hx hz hxy hyz
    have hy : y ∈ Set.Ioi (0 : ℝ) := hx.trans hxy
    have hxyEq : g x = g y :=
      le_antisymm (hmono hx hy hxy.le) (hanti hx hy hxy.le)
    have hyzEq : g y = g z :=
      le_antisymm (hmono hy hz hyz.le) (hanti hy hz hyz.le)
    rw [hxyEq, hyzEq]
    simp

/-- Lemma 4.4 packaged with all three paper conclusions: nonnegativity and
nondecreasingness of `T⁽ˡ⁾(r⁻,f)` for `0 ≤ l ≤ n`, and convexity of
`T(·,f)` on the positive radius axis. -/
theorem characteristicLemma44
    {n : ℕ} (hn : 1 ≤ n) {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f) :
    CharacteristicLemma44Conclusion f := by
  have habs := characteristicAbsoluteMonotonicity hf
  exact ⟨habs.1, habs.2, characteristicConvexOn_of_wellDefined hn hf⟩

theorem characteristicMonotone_of_wellDefined
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f) :
    CharacteristicMonotone f :=
  characteristicMonotone_of_leftDerivativesMonotone
    (characteristicAbsoluteMonotonicity hf).2

/-- The concrete local certificate needed after the finite cut/zero event
construction in the proof of characteristic monotonicity. -/
def CharacteristicLeftDerivativesLocallyMonotone
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Prop :=
  ∀ l : ℕ, l ≤ n → ∀ x ∈ Set.Ioi (0 : ℝ),
    ∃ a b : ℝ, a < x ∧ x < b ∧
      MonotoneOn (characteristicLeftDeriv l f) (Set.Ioo a b)

/-- A near-origin nonnegativity certificate for all derivatives occurring in
the characteristic lemma. -/
def CharacteristicLeftDerivativesInitiallyNonnegative
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Prop :=
  ∀ l : ℕ, l ≤ n → ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ r ∈ Set.Ioo (0 : ℝ) r₀, 0 ≤ characteristicLeftDeriv l f r

theorem characteristicLeftDerivativesMonotone_of_local
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hlocal : CharacteristicLeftDerivativesLocallyMonotone f) :
    CharacteristicLeftDerivativesMonotone f := by
  intro l hl
  exact monotoneOn_Ioi_of_locally_monotoneOn
    (characteristicLeftDeriv l f) (hlocal l hl)

theorem characteristicLeftDerivativesNonnegative_of_initial_of_monotone
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hinitial : CharacteristicLeftDerivativesInitiallyNonnegative f)
    (hmono : CharacteristicLeftDerivativesMonotone f) :
    CharacteristicLeftDerivativesNonnegative f := by
  intro l hl r hr
  obtain ⟨r₀, hr₀, hinitial_l⟩ := hinitial l hl
  let s : ℝ := min (r / 2) (r₀ / 2)
  have hs_pos : 0 < s := by
    dsimp [s]
    exact lt_min (by linarith) (by linarith)
  have hsr : s < r := by
    exact (min_le_left (r / 2) (r₀ / 2)).trans_lt (by linarith)
  have hsr₀ : s < r₀ := by
    exact (min_le_right (r / 2) (r₀ / 2)).trans_lt (by linarith)
  exact (hinitial_l s ⟨hs_pos, hsr₀⟩).trans
    (hmono l hl hs_pos hr hsr.le)

/-- Once the analytic construction supplies the two explicit local
certificates, the full conjunction in the characteristic lemma follows. -/
theorem characteristicAbsoluteMonotonicity_of_localCertificates
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hinitial : CharacteristicLeftDerivativesInitiallyNonnegative f)
    (hlocal : CharacteristicLeftDerivativesLocallyMonotone f) :
    CharacteristicAbsoluteMonotonicity f := by
  have hmono : CharacteristicLeftDerivativesMonotone f :=
    characteristicLeftDerivativesMonotone_of_local hlocal
  exact ⟨characteristicLeftDerivativesNonnegative_of_initial_of_monotone
    hinitial hmono, hmono⟩

end

end NthTropicalNevanlinna
