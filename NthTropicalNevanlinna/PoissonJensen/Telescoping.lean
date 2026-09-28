import NthTropicalNevanlinna.PoissonJensen.DerivativeJump

/-!
# Finite polynomial telescoping — Lemma 3.1

Both endpoint identities are proved.  The paper proves only the right-hand
identity and says that the left-hand identity is similar; here the reverse
Taylor signs and the reverse telescoping sum are checked explicitly.
-/

namespace NthTropicalNevanlinna

open scoped BigOperators

private theorem range_succ_eq_insert_Icc (n : ℕ) :
    Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
  ext j
  simp
  omega

private theorem polynomial_eval_sub_center_eq_sum_jets
    (p q : Polynomial ℝ) {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (x y : ℝ) (hcenter : p.eval x = q.eval x) :
    q.eval y - p.eval y =
      ∑ j ∈ Finset.Icc 1 n,
        (normalizedPolynomialJet q j x - normalizedPolynomialJet p j x) *
          (y - x) ^ j := by
  rw [polynomial_eval_sub_eq_sum_jet_sub p q hp hq x y,
    range_succ_eq_insert_Icc, Finset.sum_insert (by simp)]
  simp [normalizedPolynomialJet, hcenter]

private theorem polynomial_eval_sub_self_eq_sum_jets
    (p : Polynomial ℝ) {n : ℕ} (hp : p.natDegree ≤ n) (x y : ℝ) :
    p.eval y - p.eval x =
      ∑ j ∈ Finset.Icc 1 n,
        normalizedPolynomialJet p j x * (y - x) ^ j := by
  rw [polynomial_eval_eq_sum_normalizedJet p hp x y,
    range_succ_eq_insert_Icc, Finset.sum_insert (by simp)]
  simp [normalizedPolynomialJet]

private theorem polynomial_eval_sub_self_eq_sum_signedJets
    (p : Polynomial ℝ) {n : ℕ} (hp : p.natDegree ≤ n) (a b : ℝ) :
    p.eval b - p.eval a =
      ∑ j ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ (j + 1) * normalizedPolynomialJet p j b * (b - a) ^ j := by
  have h := polynomial_eval_sub_self_eq_sum_jets p hp b a
  calc
    p.eval b - p.eval a = -(p.eval a - p.eval b) := by ring
    _ = -(∑ j ∈ Finset.Icc 1 n,
        normalizedPolynomialJet p j b * (a - b) ^ j) := by rw [h]
    _ = ∑ j ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ (j + 1) * normalizedPolynomialJet p j b * (b - a) ^ j := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show a - b = -(b - a) by ring, neg_pow, pow_succ]
      ring

private theorem polynomial_eval_sub_center_eq_sum_signedJumps
    (p q : Polynomial ℝ) {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (a x : ℝ) (hcenter : p.eval x = q.eval x) :
    q.eval a - p.eval a =
      ∑ j ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ j *
          (normalizedPolynomialJet q j x - normalizedPolynomialJet p j x) *
            (x - a) ^ j := by
  rw [polynomial_eval_sub_center_eq_sum_jets p q hp hq x a hcenter]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show a - x = -(x - a) by ring, neg_pow]
  ring

private theorem sum_adjacent_eval
    {m : ℕ} (p : Fin (m + 1) → Polynomial ℝ) (y : ℝ) :
    Finset.univ.sum (fun i : Fin m ↦
      (p (Fin.succ i)).eval y - (p (Fin.castSucc i)).eval y) =
      (p (Fin.last m)).eval y - (p 0).eval y := by
  rw [Finset.sum_sub_distrib]
  have hsucc := Fin.sum_univ_succ (fun i : Fin (m + 1) ↦ (p i).eval y)
  have hcast := Fin.sum_univ_castSucc (fun i : Fin (m + 1) ↦ (p i).eval y)
  linear_combination hcast - hsucc

/--
Lemma 3.1, right endpoint formula.  The internal cuts may include redundant
cuts; their derivative jumps are zero and hence do not change the sum.
-/
theorem endpoint_sub_eq_jet_sum
    {n m : ℕ} {f : ℝ → ℝ} {a b : ℝ}
    (P : IntervalPolynomialPresentation n m f a b) :
    f b - f a =
      ∑ j ∈ Finset.Icc 1 n,
        (normalizedPolynomialJet P.firstPiece j a * (b - a) ^ j +
          ∑ i : Fin m, P.derivativeJumpAt j i * (b - P.internalCut i) ^ j) := by
  have hfirst := polynomial_eval_sub_self_eq_sum_jets P.firstPiece
    (P.piece_natDegree_le 0) a b
  have htelescope := sum_adjacent_eval P.piece b
  have htelescope' :
      (∑ i : Fin m, ((P.rightPiece i).eval b - (P.leftPiece i).eval b)) =
        P.lastPiece.eval b - P.firstPiece.eval b := by
    simpa [IntervalPolynomialPresentation.rightPiece,
      IntervalPolynomialPresentation.leftPiece,
      IntervalPolynomialPresentation.lastPiece,
      IntervalPolynomialPresentation.firstPiece] using htelescope
  have hjump : ∀ i : Fin m,
      (P.rightPiece i).eval b - (P.leftPiece i).eval b =
        ∑ j ∈ Finset.Icc 1 n,
          P.derivativeJumpAt j i * (b - P.internalCut i) ^ j := by
    intro i
    exact polynomial_eval_sub_center_eq_sum_jets
      (P.leftPiece i) (P.rightPiece i)
      (P.piece_natDegree_le i.castSucc) (P.piece_natDegree_le i.succ)
      (P.internalCut i) b (P.leftPiece_eval_internalCut_eq_rightPiece i)
  rw [P.apply_rightEndpoint, P.apply_leftEndpoint]
  calc
    P.lastPiece.eval b - P.firstPiece.eval a =
        (P.firstPiece.eval b - P.firstPiece.eval a) +
          (P.lastPiece.eval b - P.firstPiece.eval b) := by ring
    _ = (∑ j ∈ Finset.Icc 1 n,
          normalizedPolynomialJet P.firstPiece j a * (b - a) ^ j) +
        ∑ i : Fin m, ((P.rightPiece i).eval b - (P.leftPiece i).eval b) := by
      rw [hfirst, ← htelescope']
    _ = _ := by
      simp_rw [hjump]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]

/--
Lemma 3.1, left endpoint formula omitted from the paper's proof.  This proof
checks the factors `(-1)^(j+1)` and `(-1)^j` by reverse Taylor expansion.
-/
theorem sub_leftEndpoint_eq_jet_sum
    {n m : ℕ} {f : ℝ → ℝ} {a b : ℝ}
    (P : IntervalPolynomialPresentation n m f a b) :
    f b - f a =
      ∑ j ∈ Finset.Icc 1 n,
        ((-1 : ℝ) ^ (j + 1) * normalizedPolynomialJet P.lastPiece j b *
            (b - a) ^ j +
          (-1 : ℝ) ^ j *
            ∑ i : Fin m, P.derivativeJumpAt j i * (P.internalCut i - a) ^ j) := by
  have hlast := polynomial_eval_sub_self_eq_sum_signedJets P.lastPiece
    (P.piece_natDegree_le (Fin.last m)) a b
  have htelescope := sum_adjacent_eval P.piece a
  have htelescope' :
      (∑ i : Fin m, ((P.rightPiece i).eval a - (P.leftPiece i).eval a)) =
        P.lastPiece.eval a - P.firstPiece.eval a := by
    simpa [IntervalPolynomialPresentation.rightPiece,
      IntervalPolynomialPresentation.leftPiece,
      IntervalPolynomialPresentation.lastPiece,
      IntervalPolynomialPresentation.firstPiece] using htelescope
  have hjump : ∀ i : Fin m,
      (P.rightPiece i).eval a - (P.leftPiece i).eval a =
        ∑ j ∈ Finset.Icc 1 n,
          (-1 : ℝ) ^ j * P.derivativeJumpAt j i *
            (P.internalCut i - a) ^ j := by
    intro i
    exact polynomial_eval_sub_center_eq_sum_signedJumps
      (P.leftPiece i) (P.rightPiece i)
      (P.piece_natDegree_le i.castSucc) (P.piece_natDegree_le i.succ)
      a (P.internalCut i) (P.leftPiece_eval_internalCut_eq_rightPiece i)
  rw [P.apply_rightEndpoint, P.apply_leftEndpoint]
  calc
    P.lastPiece.eval b - P.firstPiece.eval a =
        (P.lastPiece.eval b - P.lastPiece.eval a) +
          (P.lastPiece.eval a - P.firstPiece.eval a) := by ring
    _ = (∑ j ∈ Finset.Icc 1 n,
          (-1 : ℝ) ^ (j + 1) * normalizedPolynomialJet P.lastPiece j b *
            (b - a) ^ j) +
        ∑ i : Fin m, ((P.rightPiece i).eval a - (P.leftPiece i).eval a) := by
      rw [hlast, ← htelescope']
    _ = _ := by
      simp_rw [hjump]
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        (∑ i : Fin m, ∑ j ∈ Finset.Icc 1 n,
            (-1 : ℝ) ^ j * P.derivativeJumpAt j i *
              (P.internalCut i - a) ^ j) =
            ∑ j ∈ Finset.Icc 1 n, ∑ i : Fin m,
              ((-1 : ℝ) ^ j * P.derivativeJumpAt j i *
                (P.internalCut i - a) ^ j) := by rw [Finset.sum_comm]
        _ = ∑ j ∈ Finset.Icc 1 n,
            (-1 : ℝ) ^ j *
              ∑ i : Fin m, P.derivativeJumpAt j i *
                (P.internalCut i - a) ^ j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring

end NthTropicalNevanlinna
