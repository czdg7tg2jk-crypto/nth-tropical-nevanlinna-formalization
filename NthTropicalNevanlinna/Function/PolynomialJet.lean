import NthTropicalNevanlinna.Function.Multiplicity

/-!
# Polynomial jet algebra

Taylor identities used locally in the proofs of Propositions 2.2 and 2.3.
-/

namespace NthTropicalNevanlinna

open scoped BigOperators

@[simp]
theorem normalizedPolynomialJet_add (p q : Polynomial ℝ) (j : ℕ) (x : ℝ) :
    normalizedPolynomialJet (p + q) j x =
      normalizedPolynomialJet p j x + normalizedPolynomialJet q j x := by
  simp [normalizedPolynomialJet]

@[simp]
theorem normalizedPolynomialJet_neg (p : Polynomial ℝ) (j : ℕ) (x : ℝ) :
    normalizedPolynomialJet (-p) j x = -normalizedPolynomialJet p j x := by
  simp [normalizedPolynomialJet]

/-- Exact Taylor expansion for a polynomial whose degree is at most `n`. -/
theorem polynomial_eval_eq_sum_normalizedJet
    (p : Polynomial ℝ) {n : ℕ} (hp : p.natDegree ≤ n) (x y : ℝ) :
    p.eval y = ∑ j ∈ Finset.range (n + 1), normalizedPolynomialJet p j x * (y - x) ^ j := by
  calc
    p.eval y = (Polynomial.taylor x p).eval (y - x) := by
      symm
      exact Polynomial.taylor_eval_sub x p y
    _ = ∑ j ∈ Finset.range (n + 1),
        (Polynomial.taylor x p).coeff j * (y - x) ^ j := by
      apply Polynomial.eval_eq_sum_range'
      rw [Polynomial.natDegree_taylor]
      omega
    _ = ∑ j ∈ Finset.range (n + 1),
        normalizedPolynomialJet p j x * (y - x) ^ j := by
      simp only [Polynomial.taylor_coeff, normalizedPolynomialJet]

theorem polynomial_eval_sub_eq_sum_jet_sub
    (p q : Polynomial ℝ) {n : ℕ} (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (x y : ℝ) :
    q.eval y - p.eval y =
      ∑ j ∈ Finset.range (n + 1),
        (normalizedPolynomialJet q j x - normalizedPolynomialJet p j x) * (y - x) ^ j := by
  rw [polynomial_eval_eq_sum_normalizedJet q hq x y,
    polynomial_eval_eq_sum_normalizedJet p hp x y, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem polynomial_eval_add_reflection_eq_sum_signedJets
    (p q : Polynomial ℝ) {n : ℕ} (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (r : ℝ) :
    p.eval r + q.eval (-r) =
      ∑ j ∈ Finset.range (n + 1),
        (normalizedPolynomialJet p j 0 -
          (-1 : ℝ) ^ (j + 1) * normalizedPolynomialJet q j 0) * r ^ j := by
  rw [polynomial_eval_eq_sum_normalizedJet p hp 0 r,
    polynomial_eval_eq_sum_normalizedJet q hq 0 (-r), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [sub_zero, neg_pow, pow_succ]
  ring

/-- The normalized jet of the shifted monomial `(X - x)^k` at `x`. -/
@[simp]
theorem normalizedPolynomialJet_shiftedMonomial (x : ℝ) (j k : ℕ) :
    normalizedPolynomialJet ((Polynomial.X - Polynomial.C x) ^ k) j x =
      if j = k then 1 else 0 := by
  rw [normalizedPolynomialJet, ← Polynomial.taylor_coeff]
  simp [Polynomial.taylor_apply]

/-- A polynomial correction with prescribed normalized jets `1, …, n` at `x`. -/
noncomputable def jetCorrection (n : ℕ) (x : ℝ) (c : ℕ → ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.Icc 1 n, Polynomial.C (c j) * (Polynomial.X - Polynomial.C x) ^ j

theorem jetCorrection_natDegree_le (n : ℕ) (x : ℝ) (c : ℕ → ℝ) :
    (jetCorrection n x c).natDegree ≤ n := by
  unfold jetCorrection
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact Polynomial.natDegree_mul_le.trans <| calc
    (Polynomial.C (c j)).natDegree + ((Polynomial.X - Polynomial.C x) ^ j).natDegree
        ≤ 0 + j := by
          gcongr
          · simp
          · exact Polynomial.natDegree_pow_le.trans (by simp)
    _ ≤ n := by simp only [zero_add]; exact (Finset.mem_Icc.mp hj).2

@[simp]
theorem jetCorrection_eval_center (n : ℕ) (x : ℝ) (c : ℕ → ℝ) :
    (jetCorrection n x c).eval x = 0 := by
  unfold jetCorrection
  change (Polynomial.evalRingHom x)
    (∑ j ∈ Finset.Icc 1 n, Polynomial.C (c j) * (Polynomial.X - Polynomial.C x) ^ j) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hj0 : j ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hj).1
  simp [hj0]

theorem normalizedPolynomialJet_C_mul_shiftedMonomial
    (a x : ℝ) (j k : ℕ) :
    normalizedPolynomialJet
        (Polynomial.C a * (Polynomial.X - Polynomial.C x) ^ k) j x =
      a * (if j = k then 1 else 0) := by
  rw [normalizedPolynomialJet, ← Polynomial.taylor_coeff]
  simp [Polynomial.taylor_apply]

theorem normalizedPolynomialJet_jetCorrection
    {n j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) (x : ℝ) (c : ℕ → ℝ) :
    normalizedPolynomialJet (jetCorrection n x c) j x = c j := by
  rw [jetCorrection]
  change (Polynomial.evalRingHom x) ((Polynomial.hasseDeriv j)
    (∑ k ∈ Finset.Icc 1 n,
      Polynomial.C (c k) * (Polynomial.X - Polynomial.C x) ^ k)) = c j
  rw [map_sum, map_sum]
  change (∑ k ∈ Finset.Icc 1 n,
    normalizedPolynomialJet
      (Polynomial.C (c k) * (Polynomial.X - Polynomial.C x) ^ k) j x) = c j
  simp_rw [normalizedPolynomialJet_C_mul_shiftedMonomial]
  simp [hj, hjn]

end NthTropicalNevanlinna
