import NthTropicalNevanlinna.Nevanlinna.Growth

/-!
# Well-defined polynomial pieces

This file formalizes Definition 4.2 and the polynomial common-sign lemma
(Lemma 4.3 in the formalization numbering, labelled `4.3.0` in the source).
-/

namespace NthTropicalNevanlinna

noncomputable section

/-- Apart from its constant term, `p` is supported in the parity of its
highest degree. -/
def HasWellDefinedParity (p : Polynomial ℝ) : Prop :=
  ∀ k : ℕ, k ≠ 0 → k % 2 ≠ p.natDegree % 2 → p.coeff k = 0

/-- All nonconstant coefficients of `p` have one common weak sign. -/
def HasCommonWeakCoefficientSign (p : Polynomial ℝ) : Prop :=
  (∀ k : ℕ, k ≠ 0 → 0 ≤ p.coeff k) ∨
    (∀ k : ℕ, k ≠ 0 → p.coeff k ≤ 0)

/-- Definition 4.2: a well-defined real polynomial. -/
def IsWellDefinedPolynomial (p : Polynomial ℝ) : Prop :=
  HasWellDefinedParity p ∧ HasCommonWeakCoefficientSign p

namespace IsWellDefinedPolynomial

theorem parity
    {p : Polynomial ℝ} (hp : IsWellDefinedPolynomial p) :
    HasWellDefinedParity p := hp.1

theorem commonSign
    {p : Polynomial ℝ} (hp : IsWellDefinedPolynomial p) :
    HasCommonWeakCoefficientSign p := hp.2

theorem constant (a : ℝ) : IsWellDefinedPolynomial (Polynomial.C a) := by
  constructor
  · intro k hk hpar
    simp [Polynomial.coeff_C, hk]
  · left
    intro k hk
    simp [Polynomial.coeff_C, hk]

theorem zero : IsWellDefinedPolynomial (0 : Polynomial ℝ) := by
  simpa using constant 0

/-- The “especially” clause of Definition 4.2: every polynomial of degree at
most one is well defined. -/
theorem of_natDegree_le_one {p : Polynomial ℝ} (hp : p.natDegree ≤ 1) :
    IsWellDefinedPolynomial p := by
  constructor
  · intro k hk hpar
    apply p.coeff_eq_zero_of_natDegree_lt
    omega
  · rcases le_total 0 (p.coeff 1) with hcoeff | hcoeff
    · left
      intro k hk
      by_cases hk1 : k = 1
      · simpa [hk1] using hcoeff
      · rw [p.coeff_eq_zero_of_natDegree_lt (by omega)]
    · right
      intro k hk
      by_cases hk1 : k = 1
      · simpa [hk1] using hcoeff
      · rw [p.coeff_eq_zero_of_natDegree_lt (by omega)]

theorem neg {p : Polynomial ℝ} (hp : IsWellDefinedPolynomial p) :
    IsWellDefinedPolynomial (-p) := by
  constructor
  · intro k hk hpar
    have hdegree : (-p).natDegree = p.natDegree := by simp
    rw [hdegree] at hpar
    simpa using congrArg Neg.neg (hp.parity k hk hpar)
  · rcases hp.commonSign with hnonneg | hnonpos
    · right
      intro k hk
      simpa using neg_nonpos.mpr (hnonneg k hk)
    · left
      intro k hk
      simpa using neg_nonneg.mpr (hnonpos k hk)

end IsWellDefinedPolynomial

/-- A polynomial written in the radial variable `r`, namely `p (δ r)`. -/
def radialPolynomial (p : Polynomial ℝ) (δ : ℝ) : Polynomial ℝ :=
  p.comp (Polynomial.C δ * Polynomial.X)

@[simp]
theorem radialPolynomial_eval (p : Polynomial ℝ) (δ r : ℝ) :
    (radialPolynomial p δ).eval r = p.eval (δ * r) := by
  simp [radialPolynomial]

@[simp]
theorem radialPolynomial_coeff (p : Polynomial ℝ) (δ : ℝ) (k : ℕ) :
    (radialPolynomial p δ).coeff k = p.coeff k * δ ^ k := by
  simp [radialPolynomial]

private theorem iteratedDerivative_eval_nonneg_of_coeff_nonneg
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

private theorem iteratedDerivative_eval_nonpos_of_coeff_nonpos
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

private theorem radialPolynomial_commonSign
    {p : Polynomial ℝ} (hp : IsWellDefinedPolynomial p)
    {δ : ℝ} (hδ : δ = 1 ∨ δ = -1) :
    (∀ k : ℕ, k ≠ 0 → 0 ≤ (radialPolynomial p δ).coeff k) ∨
      (∀ k : ℕ, k ≠ 0 → (radialPolynomial p δ).coeff k ≤ 0) := by
  rcases hδ with rfl | rfl
  · simpa [HasCommonWeakCoefficientSign] using hp.commonSign
  · have hparity : ∀ k : ℕ, k ≠ 0 →
        (-1 : ℝ) ^ k = (-1 : ℝ) ^ p.natDegree ∨ p.coeff k = 0 := by
      intro k hk
      by_cases hmod : k % 2 = p.natDegree % 2
      · left
        calc
          (-1 : ℝ) ^ k = (-1 : ℝ) ^ (k % 2) := neg_one_pow_eq_pow_mod_two k
          _ = (-1 : ℝ) ^ (p.natDegree % 2) := by rw [hmod]
          _ = (-1 : ℝ) ^ p.natDegree := (neg_one_pow_eq_pow_mod_two p.natDegree).symm
      · exact Or.inr (hp.parity k hk hmod)
    rcases hp.commonSign with hnonneg | hnonpos
    · rcases neg_one_pow_eq_or ℝ p.natDegree with hdegree | hdegree
      · left
        intro k hk
        rcases hparity k hk with hpow | hzero
        · simp [radialPolynomial_coeff, hpow, hdegree, hnonneg k hk]
        · simp [radialPolynomial_coeff, hzero]
      · right
        intro k hk
        rcases hparity k hk with hpow | hzero
        · simp [radialPolynomial_coeff, hpow, hdegree, hnonneg k hk]
        · simp [radialPolynomial_coeff, hzero]
    · rcases neg_one_pow_eq_or ℝ p.natDegree with hdegree | hdegree
      · right
        intro k hk
        rcases hparity k hk with hpow | hzero
        · simp [radialPolynomial_coeff, hpow, hdegree, hnonpos k hk]
        · simp [radialPolynomial_coeff, hzero]

      · left
        intro k hk
        rcases hparity k hk with hpow | hzero
        · simp [radialPolynomial_coeff, hpow, hdegree, hnonpos k hk]
        · simp [radialPolynomial_coeff, hzero]

/-- Substitution `x ↦ δx` with `δ=±1` preserves well-defined polynomials. -/
theorem IsWellDefinedPolynomial.radial
    {p : Polynomial ℝ} (hp : IsWellDefinedPolynomial p)
    {δ : ℝ} (hδ : δ = 1 ∨ δ = -1) :
    IsWellDefinedPolynomial (radialPolynomial p δ) := by
  have hdegree : (radialPolynomial p δ).natDegree = p.natDegree := by
    rcases hδ with rfl | rfl
    · have hpoly : radialPolynomial p 1 = p := by
        ext k
        simp [radialPolynomial_coeff]
      rw [hpoly]
    · exact Polynomial.natDegree_eq_of_degree_eq (by
        simp [radialPolynomial])
  constructor
  · intro k hk hparity
    rw [hdegree] at hparity
    simp [radialPolynomial_coeff, hp.parity k hk hparity]
  · exact radialPolynomial_commonSign hp hδ

/-- Lemma 4.3: for a fixed radial direction `δ = ±1`, all positive-order
derivatives of a well-defined polynomial have one common weak sign on `r>0`.
The source only asks for `1 ≤ l ≤ degree p`; the proof gives every `l ≥ 1`.
-/
theorem wellDefinedPolynomial_iteratedDeriv_commonSign
    {p : Polynomial ℝ} (hp : IsWellDefinedPolynomial p)
    {δ : ℝ} (hδ : δ = 1 ∨ δ = -1) {r : ℝ} (hr : 0 < r) :
    (∀ l : ℕ, 1 ≤ l →
      0 ≤ ((Polynomial.derivative^[l]) (radialPolynomial p δ)).eval r) ∨
    (∀ l : ℕ, 1 ≤ l →
      ((Polynomial.derivative^[l]) (radialPolynomial p δ)).eval r ≤ 0) := by
  rcases radialPolynomial_commonSign hp hδ with hnonneg | hnonpos
  · left
    intro l hl
    exact iteratedDerivative_eval_nonneg_of_coeff_nonneg hnonneg hl hr.le
  · right
    intro l hl
    exact iteratedDerivative_eval_nonpos_of_coeff_nonpos hnonpos hl hr.le

/-- Positive-order normalized jets of a well-defined polynomial have one
common weak sign at every positive point. -/
theorem wellDefinedPolynomial_normalizedJet_commonSign
    {p : Polynomial ℝ} (hp : IsWellDefinedPolynomial p)
    {r : ℝ} (hr : 0 < r) :
    (∀ j : ℕ, 1 ≤ j → 0 ≤ normalizedPolynomialJet p j r) ∨
      (∀ j : ℕ, 1 ≤ j → normalizedPolynomialJet p j r ≤ 0) := by
  have hradial : radialPolynomial p 1 = p := by
    ext k
    simp [radialPolynomial_coeff]
  rcases wellDefinedPolynomial_iteratedDeriv_commonSign hp (Or.inl rfl) hr with
      hnonneg | hnonpos
  · left
    intro j hj
    rw [normalizedPolynomialJet_eq_iterateDerivative_div]
    apply div_nonneg
    · simpa [hradial] using hnonneg j hj
    · positivity
  · right
    intro j hj
    rw [normalizedPolynomialJet_eq_iterateDerivative_div]
    apply div_nonpos_of_nonpos_of_nonneg
    · simpa [hradial] using hnonpos j hj
    · positivity

/-- A well-defined n-th tropical meromorphic function admits a global
presentation all of whose polynomial pieces satisfy Definition 4.2. -/
def IsWellDefinedNthTropicalMeromorphicFunction
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) : Prop :=
  ∃ P : PolynomialPresentation n f,
    ∀ i : ℤ, IsWellDefinedPolynomial (P.piece i)

/-- Every piecewise-polynomial function of exact order at most one is
well-defined in the sense of Definition 4.2. -/
theorem isWellDefined_of_order_le_one
    {q : ℕ} (f : NthTropicalMeromorphicFunction q) (hq : q ≤ 1) :
    IsWellDefinedNthTropicalMeromorphicFunction f := by
  refine ⟨f.presentation, fun i ↦ IsWellDefinedPolynomial.of_natDegree_le_one ?_⟩
  exact (f.presentation.piece_natDegree_le i).trans hq

private theorem wellDefined_leftPieceAt
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (P : PolynomialPresentation n f)
    (hP : ∀ i : ℤ, IsWellDefinedPolynomial (P.piece i)) (x : ℝ) :
    IsWellDefinedPolynomial (P.leftPieceAt x) := by
  exact hP (presentationIntervalIndex P x)

private theorem wellDefined_rightPieceAt
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (P : PolynomialPresentation n f)
    (hP : ∀ i : ℤ, IsWellDefinedPolynomial (P.piece i)) (x : ℝ) :
    IsWellDefinedPolynomial (P.rightPieceAt x) := by
  simp only [PolynomialPresentation.rightPieceAt]
  split_ifs
  · exact hP (presentationIntervalIndex P x + 1)
  · exact hP (presentationIntervalIndex P x)

/-- The intrinsic right jets at a positive endpoint have one common sign. -/
theorem IsWellDefinedNthTropicalMeromorphicFunction.normalizedRightJet_commonSign
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f)
    {x : ℝ} (hx : 0 < x) :
    (∀ j : ℕ, 1 ≤ j → 0 ≤ normalizedRightJet f j x) ∨
      (∀ j : ℕ, 1 ≤ j → normalizedRightJet f j x ≤ 0) := by
  obtain ⟨P, hP⟩ := hf
  have hsign := wellDefinedPolynomial_normalizedJet_commonSign
    (wellDefined_rightPieceAt P hP x) hx
  simpa only [normalizedRightJet_eq_usingPresentation f P] using hsign

/-- At a negative endpoint, the coefficients in the reverse radial Taylor
formula, `(-1)^(j+1)` times the intrinsic left jets, have one common sign. -/
theorem IsWellDefinedNthTropicalMeromorphicFunction.signedNormalizedLeftJet_commonSign
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f)
    {x : ℝ} (hx : x < 0) :
    (∀ j : ℕ, 1 ≤ j →
        0 ≤ (-1 : ℝ) ^ (j + 1) * normalizedLeftJet f j x) ∨
      (∀ j : ℕ, 1 ≤ j →
        (-1 : ℝ) ^ (j + 1) * normalizedLeftJet f j x ≤ 0) := by
  obtain ⟨P, hP⟩ := hf
  let p := P.leftPieceAt x
  have hp : IsWellDefinedPolynomial p := wellDefined_leftPieceAt P hP x
  have hq : IsWellDefinedPolynomial (p.comp (-Polynomial.X)) := by
    have := hp.radial (Or.inr rfl)
    simpa [radialPolynomial] using this
  have hr : 0 < -x := neg_pos.mpr hx
  rcases wellDefinedPolynomial_normalizedJet_commonSign hq hr with
      hnonneg | hnonpos
  · right
    intro j hj
    have hjq := hnonneg j hj
    rw [normalizedPolynomialJet_comp_neg_X] at hjq
    have hjq' :
        0 ≤ (-1 : ℝ) ^ j * normalizedPolynomialJet p j x := by
      simpa using hjq
    rw [normalizedLeftJet_eq_usingPresentation f P]
    change (-1 : ℝ) ^ (j + 1) * normalizedPolynomialJet p j x ≤ 0
    rw [pow_succ]
    linarith
  · left
    intro j hj
    have hjq := hnonpos j hj
    rw [normalizedPolynomialJet_comp_neg_X] at hjq
    have hjq' :
        (-1 : ℝ) ^ j * normalizedPolynomialJet p j x ≤ 0 := by
      simpa using hjq
    rw [normalizedLeftJet_eq_usingPresentation f P]
    change 0 ≤ (-1 : ℝ) ^ (j + 1) * normalizedPolynomialJet p j x
    rw [pow_succ]
    linarith

theorem IsWellDefinedNthTropicalMeromorphicFunction.neg
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f) :
    IsWellDefinedNthTropicalMeromorphicFunction (-f) := by
  obtain ⟨P, hP⟩ := hf
  refine ⟨P.neg, ?_⟩
  intro i
  exact (hP i).neg

/-- Reflection across the origin preserves Definition 4.2. -/
theorem IsWellDefinedNthTropicalMeromorphicFunction.reflect
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f) :
    IsWellDefinedNthTropicalMeromorphicFunction f.reflect := by
  obtain ⟨P, hP⟩ := hf
  refine ⟨P.reflect, ?_⟩
  intro i
  change IsWellDefinedPolynomial ((P.piece (1 - i)).comp (-Polynomial.X))
  have hradial := (hP (1 - i)).radial (Or.inr rfl)
  simpa [radialPolynomial] using hradial

end

end NthTropicalNevanlinna
