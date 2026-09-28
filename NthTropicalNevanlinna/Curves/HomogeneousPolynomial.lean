import NthTropicalNevanlinna.Curves.Characteristic
import NthTropicalNevanlinna.Function.PresentationClosure
import NthTropicalNevanlinna.Function.FirstOrderConvexity

/-!
# Homogeneous tropical polynomials and compositions

An absent monomial represents coefficient `-∞`.  Thus the finite real
coefficients are stored on a nonempty finite support.
-/

namespace NthTropicalNevanlinna

noncomputable section

open scoped BigOperators

/-- An `(m+1)`-variable multi-index of total degree `d`.  Each exponent is
stored in `Fin (d+1)`, which makes the type manifestly finite. -/
def DegreeMultiIndex (m d : ℕ) :=
  {e : Fin (m + 1) → Fin (d + 1) // ∑ i, (e i : ℕ) = d}

instance (m d : ℕ) : Fintype (DegreeMultiIndex m d) := by
  unfold DegreeMultiIndex
  classical
  exact Fintype.ofFinite _
instance (m d : ℕ) : DecidableEq (DegreeMultiIndex m d) := Classical.decEq _

/-- The pure-power multi-index `d e_k`. -/
def pureDegreeMultiIndex {m d : ℕ} (k : Fin (m + 1)) :
    DegreeMultiIndex m d := by
  refine ⟨fun i ↦ if i = k then ⟨d, Nat.lt_succ_self d⟩ else 0, ?_⟩
  classical
  have hterm (i : Fin (m + 1)) :
      (((if i = k then ⟨d, Nat.lt_succ_self d⟩ else 0) : Fin (d + 1)) : ℕ) =
        if i = k then d else 0 := by
    by_cases hi : i = k <;> simp [hi]
  simp_rw [hterm]
  simp

/-- A degree-`d` homogeneous tropical polynomial.  A missing term has
coefficient `-∞`; all terms in `support` have the displayed real
coefficient. -/
structure HomogeneousTropicalPolynomial (m d : ℕ) where
  support : Finset (DegreeMultiIndex m d)
  support_nonempty : support.Nonempty
  coefficient : DegreeMultiIndex m d → ℝ

namespace HomogeneousTropicalPolynomial

/-- Value of one tropical monomial. -/
def monomialValue {m d : ℕ} (P : HomogeneousTropicalPolynomial m d)
    (x : Fin (m + 1) → ℝ) (I : DegreeMultiIndex m d) : ℝ :=
  P.coefficient I + ∑ i, (I.1 i : ℕ) * x i

/-- Evaluation by tropical addition (`max`) over the finite support. -/
def eval {m d : ℕ} (P : HomogeneousTropicalPolynomial m d)
    (x : Fin (m + 1) → ℝ) : ℝ :=
  P.support.sup' P.support_nonempty (P.monomialValue x)

/-- Every pure power `x_k^d` occurs with a finite coefficient.  This is the
extra hypothesis imposed in Theorem 5.6. -/
def HasAllPurePowers {m d : ℕ} (P : HomogeneousTropicalPolynomial m d) : Prop :=
  ∀ k, pureDegreeMultiIndex k ∈ P.support

/-- Largest finite coefficient appearing in `P`. -/
def coefficientMaximum {m d : ℕ} (P : HomogeneousTropicalPolynomial m d) : ℝ :=
  P.support.sup' P.support_nonempty P.coefficient

/-- Smallest coefficient of a pure-power term. -/
def pureCoefficientMinimum {m d : ℕ}
    (P : HomogeneousTropicalPolynomial m d) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun k ↦ P.coefficient (pureDegreeMultiIndex k))

theorem coefficient_le_coefficientMaximum {m d : ℕ}
    (P : HomogeneousTropicalPolynomial m d)
    {I : DegreeMultiIndex m d} (hI : I ∈ P.support) :
    P.coefficient I ≤ P.coefficientMaximum := by
  exact Finset.le_sup' P.coefficient hI

theorem pureCoefficientMinimum_le {m d : ℕ}
    (P : HomogeneousTropicalPolynomial m d) (k : Fin (m + 1)) :
    P.pureCoefficientMinimum ≤ P.coefficient (pureDegreeMultiIndex k) := by
  exact Finset.inf'_le (fun i ↦ P.coefficient (pureDegreeMultiIndex i))
    (Finset.mem_univ k)

theorem pureCoefficientMinimum_le_coefficientMaximum {m d : ℕ}
    (P : HomogeneousTropicalPolynomial m d) (hPure : P.HasAllPurePowers) :
    P.pureCoefficientMinimum ≤ P.coefficientMaximum := by
  let k : Fin (m + 1) := 0
  exact (P.pureCoefficientMinimum_le k).trans
    (P.coefficient_le_coefficientMaximum (hPure k))

theorem weightedSum_le_degree_mul_maximum {m d : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (I : DegreeMultiIndex m d) (x : ℝ) :
    (∑ i, (I.1 i : ℕ) * F.eval i x) ≤ d * curveCoordinateMaximum F x := by
  calc
    (∑ i, (I.1 i : ℕ) * F.eval i x) ≤
        ∑ i, (I.1 i : ℕ) * curveCoordinateMaximum F x := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_left
        (coordinate_le_curveCoordinateMaximum F i x) (Nat.cast_nonneg _)
    _ = d * curveCoordinateMaximum F x := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast I.2

@[simp] theorem pureMonomial_weightedSum {m d : ℕ}
    (k : Fin (m + 1)) (x : Fin (m + 1) → ℝ) :
    (∑ i, ((pureDegreeMultiIndex (d := d) k).1 i : ℕ) * x i) = d * x k := by
  classical
  have hterm (i : Fin (m + 1)) :
      (((pureDegreeMultiIndex (d := d) k).1 i : ℕ) : ℝ) =
        if i = k then d else 0 := by
    by_cases hi : i = k <;> simp [pureDegreeMultiIndex, hi]
  simp_rw [hterm]
  simp

/-- Upper half of the degree-`d` comparison with the coordinate maximum. -/
theorem eval_le_coefficientMaximum_add_degree_mul {n m d : ℕ}
    (P : HomogeneousTropicalPolynomial m d)
    (F : TropicalHolomorphicCurveRepresentation n m) (x : ℝ) :
    P.eval (fun i ↦ F.eval i x) ≤
      P.coefficientMaximum + d * curveCoordinateMaximum F x := by
  apply Finset.sup'_le
  intro I hI
  unfold monomialValue
  exact add_le_add
    (P.coefficient_le_coefficientMaximum hI)
    (weightedSum_le_degree_mul_maximum F I x)

/-- Lower half of the degree-`d` comparison, using the finite pure powers. -/
theorem pureCoefficientMinimum_add_degree_mul_le_eval {n m d : ℕ}
    (P : HomogeneousTropicalPolynomial m d) (hPure : P.HasAllPurePowers)
    (F : TropicalHolomorphicCurveRepresentation n m) (x : ℝ) :
    P.pureCoefficientMinimum + d * curveCoordinateMaximum F x ≤
      P.eval (fun i ↦ F.eval i x) := by
  obtain ⟨k, _hk, hkmax⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty (fun i ↦ F.eval i x)
  calc
    P.pureCoefficientMinimum + d * curveCoordinateMaximum F x ≤
        P.coefficient (pureDegreeMultiIndex k) + d * F.eval k x := by
      exact add_le_add (P.pureCoefficientMinimum_le k)
        (by rw [curveCoordinateMaximum, hkmax])
    _ = P.monomialValue (fun i ↦ F.eval i x) (pureDegreeMultiIndex k) := by
      simp [monomialValue, pureMonomial_weightedSum (d := d)]
    _ ≤ P.eval (fun i ↦ F.eval i x) := by
      exact Finset.le_sup' _ (hPure k)

/-- The raw pointwise composition `P ∘ F`. -/
def composeRaw {n m d : ℕ}
    (P : HomogeneousTropicalPolynomial m d)
    (F : TropicalHolomorphicCurveRepresentation n m) : ℝ → ℝ :=
  fun x ↦ P.eval (fun i ↦ F.eval i x)

/-- A bundled realization of the raw composition as a tropical meromorphic
function.  The exact order is chosen automatically by the closure
construction below and is only required to be at most the ambient order. -/
structure CurveComposition {n m d : ℕ}
    (P : HomogeneousTropicalPolynomial m d)
    (F : TropicalHolomorphicCurveRepresentation n m) where
  order : ℕ
  order_le : order ≤ n
  function : NthTropicalMeromorphicFunction order
  eq_composeRaw : ∀ x, function x = P.composeRaw F x

private def weightedCoordinateRealization {n m d : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (I : DegreeMultiIndex m d) (i : Fin (m + 1)) :
    NthTropicalMeromorphicRealization n
      (fun x ↦ (I.1 i : ℕ) * F.eval i x) := by
  let base : NthTropicalMeromorphicRealization (F.order i)
      (fun x ↦ F.eval i x) :=
    { order := F.order i
      order_le := le_rfl
      function := F.coordinate i
      eq_fun := fun _ ↦ rfl }
  exact (base.promote (F.order_le i)).smul (I.1 i : ℕ)

private def monomialRealization {n m d : ℕ}
    (P : HomogeneousTropicalPolynomial m d)
    (F : TropicalHolomorphicCurveRepresentation n m)
    (I : DegreeMultiIndex m d) :
    NthTropicalMeromorphicRealization n (fun x ↦
      P.monomialValue (fun i ↦ F.eval i x) I) := by
  let weightedSum := finsetSumRealization Finset.univ
    (fun i x ↦ (I.1 i : ℕ) * F.eval i x)
    (weightedCoordinateRealization F I)
  let coefficient := constantRealization n (P.coefficient I)
  simpa [monomialValue] using coefficient.add weightedSum

/-- The raw finite tropical maximum automatically has a globally normalized
polynomial presentation of some exact order at most the curve order. -/
def curveComposition {n m d : ℕ}
    (P : HomogeneousTropicalPolynomial m d)
    (F : TropicalHolomorphicCurveRepresentation n m) : P.CurveComposition F := by
  let R := finsetSupRealization P.support P.support_nonempty
    (fun I x ↦ P.monomialValue (fun i ↦ F.eval i x) I)
    (P.monomialRealization F)
  exact
    { order := R.order
      order_le := R.order_le
      function := R.function
      eq_composeRaw := fun x ↦ by
        rw [R.eq_fun]
        simp only [HomogeneousTropicalPolynomial.composeRaw,
          HomogeneousTropicalPolynomial.eval, Finset.sup'_apply] }

end HomogeneousTropicalPolynomial

/-- A tropical homogeneous Fermat polynomial
`max_i (α_i + d x_i)`. -/
structure TropicalHomogeneousFermatPolynomial (m d : ℕ) where
  coefficient : Fin (m + 1) → ℝ

namespace TropicalHomogeneousFermatPolynomial

def eval {m d : ℕ} (P : TropicalHomogeneousFermatPolynomial m d)
    (x : Fin (m + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i ↦ P.coefficient i + d * x i)

def composeRaw {n m d : ℕ}
    (P : TropicalHomogeneousFermatPolynomial m d)
    (F : TropicalHolomorphicCurveRepresentation n m) : ℝ → ℝ :=
  fun x ↦ P.eval (fun i ↦ F.eval i x)

def coefficientMinimum {m d : ℕ}
    (P : TropicalHomogeneousFermatPolynomial m d) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty P.coefficient

def coefficientMaximum {m d : ℕ}
    (P : TropicalHomogeneousFermatPolynomial m d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty P.coefficient

theorem coefficientMinimum_le_coefficientMaximum {m d : ℕ}
    (P : TropicalHomogeneousFermatPolynomial m d) :
    P.coefficientMinimum ≤ P.coefficientMaximum := by
  let k : Fin (m + 1) := 0
  exact (Finset.inf'_le P.coefficient (Finset.mem_univ k)).trans
    (Finset.le_sup' P.coefficient (Finset.mem_univ k))

theorem coefficientMinimum_add_degree_mul_le_eval {n m d : ℕ}
    (P : TropicalHomogeneousFermatPolynomial m d)
    (F : TropicalHolomorphicCurveRepresentation n m) (x : ℝ) :
    P.coefficientMinimum + d * curveCoordinateMaximum F x ≤
      P.eval (fun i ↦ F.eval i x) := by
  obtain ⟨k, _hk, hkmax⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty (fun i ↦ F.eval i x)
  calc
    P.coefficientMinimum + d * curveCoordinateMaximum F x ≤
        P.coefficient k + d * F.eval k x := by
      exact add_le_add
        (Finset.inf'_le P.coefficient (Finset.mem_univ k))
        (by rw [curveCoordinateMaximum, hkmax])
    _ ≤ P.eval (fun i ↦ F.eval i x) := by
      change P.coefficient k + d * F.eval k x ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun i ↦ P.coefficient i + d * F.eval i x)
      exact Finset.le_sup'
        (fun i : Fin (m + 1) ↦ P.coefficient i + (d : ℝ) * F.eval i x)
        (Finset.mem_univ k)

theorem eval_le_coefficientMaximum_add_degree_mul {n m d : ℕ}
    (P : TropicalHomogeneousFermatPolynomial m d)
    (F : TropicalHolomorphicCurveRepresentation n m) (x : ℝ) :
    P.eval (fun i ↦ F.eval i x) ≤
      P.coefficientMaximum + d * curveCoordinateMaximum F x := by
  apply Finset.sup'_le
  intro i _hi
  exact add_le_add (Finset.le_sup' P.coefficient (Finset.mem_univ i))
    (mul_le_mul_of_nonneg_left
      (coordinate_le_curveCoordinateMaximum F i x) (Nat.cast_nonneg _))

/-- A bundled first-order Fermat composition. -/
structure FirstOrderCurveComposition {m d : ℕ}
    (P : TropicalHomogeneousFermatPolynomial m d)
    (F : TropicalHolomorphicCurveRepresentation 1 m) where
  order : ℕ
  order_le : order ≤ 1
  function : NthTropicalMeromorphicFunction order
  eq_composeRaw : ∀ x, function x = P.composeRaw F x
  function_entire : IsTropicalEntire function

private def coordinateTermRealization {m d : ℕ}
    (P : TropicalHomogeneousFermatPolynomial m d)
    (F : TropicalHolomorphicCurveRepresentation 1 m)
    (i : Fin (m + 1)) :
    NthTropicalMeromorphicRealization 1
      (fun x ↦ P.coefficient i + d * F.eval i x) := by
  let base : NthTropicalMeromorphicRealization (F.order i)
      (fun x ↦ F.eval i x) :=
    { order := F.order i
      order_le := le_rfl
      function := F.coordinate i
      eq_fun := fun _ ↦ rfl }
  let scaled := (base.promote (F.order_le i)).smul (d : ℝ)
  let coefficient := constantRealization 1 (P.coefficient i)
  simpa using coefficient.add scaled

private theorem coordinateTerm_isTropicalEntire {m d : ℕ}
    (P : TropicalHomogeneousFermatPolynomial m d)
    (F : TropicalHolomorphicCurveRepresentation 1 m)
    (i : Fin (m + 1)) :
    IsTropicalEntire (P.coordinateTermRealization F i).function := by
  let R := P.coordinateTermRealization F i
  have hcoordinate : ConvexOn ℝ Set.univ (fun x ↦ F.eval i x) := by
    have h := convexOn_univ_of_order_le_one_entire
      (F.coordinate i) (F.order_le i) (F.coordinate_isTropicalEntire i)
    have heq : ((F.coordinate i : NthTropicalMeromorphicFunction (F.order i)) :
        ℝ → ℝ) = (fun x ↦ F.eval i x) := by
      funext x
      rfl
    simpa only [heq] using h
  have hscaled : ConvexOn ℝ Set.univ (fun x ↦ (d : ℝ) * F.eval i x) :=
    by simpa only [smul_eq_mul] using
      (ConvexOn.smul (Nat.cast_nonneg d) hcoordinate)
  have hterm : ConvexOn ℝ Set.univ
      (fun x ↦ P.coefficient i + (d : ℝ) * F.eval i x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha hb hab
    have h := hscaled.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    calc
      P.coefficient i + (d : ℝ) * F.eval i (a * x + b * y) ≤
          P.coefficient i +
            (a * ((d : ℝ) * F.eval i x) + b * ((d : ℝ) * F.eval i y)) :=
        by linarith
      _ = a * (P.coefficient i + (d : ℝ) * F.eval i x) +
          b * (P.coefficient i + (d : ℝ) * F.eval i y) := by
        calc
          P.coefficient i +
                (a * ((d : ℝ) * F.eval i x) + b * ((d : ℝ) * F.eval i y)) =
              (a + b) * P.coefficient i +
                (a * ((d : ℝ) * F.eval i x) + b * ((d : ℝ) * F.eval i y)) := by
            rw [hab]
            ring
          _ = a * (P.coefficient i + (d : ℝ) * F.eval i x) +
              b * (P.coefficient i + (d : ℝ) * F.eval i y) := by ring
  apply isTropicalEntire_of_order_le_one_of_convex R.function R.order_le
  have heq : (R.function : ℝ → ℝ) =
      (fun x ↦ P.coefficient i + (d : ℝ) * F.eval i x) := funext R.eq_fun
  simpa only [heq] using hterm

/-- The pointwise maximum defining a first-order tropical Fermat composition
is automatically a tropical entire function of exact order at most one. -/
def firstOrderCurveComposition {m d : ℕ}
    (P : TropicalHomogeneousFermatPolynomial m d)
    (F : TropicalHolomorphicCurveRepresentation 1 m) :
    P.FirstOrderCurveComposition F := by
  let R := finsetSupRealization Finset.univ Finset.univ_nonempty
    (fun i x ↦ P.coefficient i + d * F.eval i x)
    (P.coordinateTermRealization F)
  exact
    { order := R.order
      order_le := R.order_le
      function := R.function
      eq_composeRaw := fun x ↦ by
        rw [R.eq_fun]
        simp only [TropicalHomogeneousFermatPolynomial.composeRaw,
          TropicalHomogeneousFermatPolynomial.eval, Finset.sup'_apply]
      function_entire := finsetSupRealization_isTropicalEntire
        Finset.univ Finset.univ_nonempty
        (fun i x ↦ P.coefficient i + d * F.eval i x)
        (P.coordinateTermRealization F)
        (P.coordinateTerm_isTropicalEntire F) }

end TropicalHomogeneousFermatPolynomial

end

end NthTropicalNevanlinna
