import NthTropicalNevanlinna.Truncated.FiniteRoots
import NthTropicalNevanlinna.Curves.SecondMain

/-!
# Shifted counting data for Theorem 6.2

This file contains the realizations and the numerical terms occurring in the
statement.  The analytic comparison of shifted root counts is deliberately
kept separate from the exact Jensen assembly in `Truncated.Main`.
-/

namespace NthTropicalNevanlinna

noncomputable section

open Set
open scoped BigOperators

/-- Simultaneous realizations of the finitely many coordinate shifts used by
the Casoratian.  Translation preserves polynomial order, but the automatic
global-presentation construction is kept visible through this interface. -/
structure CurveShiftRealizations {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) where
  shiftedOrder : Fin (m + 1) → Fin (m + 1) → ℕ
  shiftedOrder_le : ∀ i k, shiftedOrder i k ≤ n
  shifted : ∀ i : Fin (m + 1), ∀ k : Fin (m + 1),
    NthTropicalMeromorphicFunction (shiftedOrder i k)
  eq_forwardShift : ∀ i k x,
    shifted i k x = forwardShift (fun y ↦ F.eval i y) k x

/-- The coordinate shifts required by Theorem 6.2 are constructed from the
translation closure theorem; they are not additional paper hypotheses. -/
def canonicalCurveShiftRealizations {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) :
    CurveShiftRealizations F where
  shiftedOrder i k := (forwardShiftRealization (F.coordinate i) k).order
  shiftedOrder_le i k :=
    (forwardShiftRealization (F.coordinate i) k).order_le.trans (F.order_le i)
  shifted i k := (forwardShiftRealization (F.coordinate i) k).function
  eq_forwardShift i k x := (forwardShiftRealization (F.coordinate i) k).eq_fun x

/-- Odd-order multiplicity transport for the canonical coordinate shifts
used in `(equa1)`. -/
theorem canonicalCurveShift_multiplicity_of_odd {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (i k : Fin (m + 1)) {j : ℕ} (hj : Odd j) (x : ℝ) :
    multiplicity ((canonicalCurveShiftRealizations F).shifted i k) j x =
      multiplicity (F.coordinate i) j (x + k) := by
  simpa [canonicalCurveShiftRealizations] using
    multiplicity_forwardShiftRealization_of_odd (F.coordinate i) k hj x

/-- Same-sign positive multiplicity transport for the canonical coordinate
shifts. -/
theorem canonicalCurveShift_multiplicity_of_pos {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (i k : Fin (m + 1)) (j : ℕ) {x : ℝ}
    (hx : 0 < x) (hxk : 0 < x + k) :
    multiplicity ((canonicalCurveShiftRealizations F).shifted i k) j x =
      multiplicity (F.coordinate i) j (x + k) := by
  simpa [canonicalCurveShiftRealizations] using
    multiplicity_forwardShiftRealization_of_pos (F.coordinate i) k j hx hxk

/-- Same-sign negative multiplicity transport for the canonical coordinate
shifts. -/
theorem canonicalCurveShift_multiplicity_of_neg {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (i k : Fin (m + 1)) (j : ℕ) {x : ℝ}
    (hx : x < 0) (hxk : x + k < 0) :
    multiplicity ((canonicalCurveShiftRealizations F).shifted i k) j x =
      multiplicity (F.coordinate i) j (x + k) := by
  simpa [canonicalCurveShiftRealizations] using
    multiplicity_forwardShiftRealization_of_neg (F.coordinate i) k j hx hxk

/-- A realization of the raw tropical Casoratian as a tropical meromorphic
function of order at most the ambient curve order. -/
structure CurveCasoratianRealization {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) where
  order : ℕ
  order_le : order ≤ n
  function : NthTropicalMeromorphicFunction order
  eq_casoratian : ∀ x,
    function x = tropicalCasoratian (fun i y ↦ F.eval i y) x

/-- One permutation summand in the Casoratian, realized under the curve's
ambient order bound. -/
def curvePermutationSumRealization {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (pi : Equiv.Perm (Fin (m + 1))) :
    NthTropicalMeromorphicRealization n
      (fun x ↦ ∑ i : Fin (m + 1),
        forwardShift (fun y ↦ F.eval i y) (pi i) x) := by
  classical
  exact finsetSumRealization Finset.univ
    (fun i x ↦ forwardShift (fun y ↦ F.eval i y) (pi i) x)
    (fun i ↦
      (forwardShiftRealization (F.coordinate i) (pi i)).promote (F.order_le i))

/-- Every permutation summand is entire for a first-order holomorphic curve. -/
theorem curvePermutationSumRealization_isTropicalEntire {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m)
    (pi : Equiv.Perm (Fin (m + 1))) :
    IsTropicalEntire (curvePermutationSumRealization F pi).function := by
  classical
  apply finsetSumRealization_isTropicalEntire
  intro i
  exact forwardShiftRealization_isTropicalEntire
    (F.coordinate i) (F.order_le i) (F.coordinate_isTropicalEntire i) (pi i)

/-- The raw tropical Casoratian is automatically realizable: it is a finite
maximum of the permutation sums above. -/
def curveCasoratianNthRealization {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) :
    NthTropicalMeromorphicRealization n
      ((Finset.univ : Finset (Equiv.Perm (Fin (m + 1)))).sup'
        Finset.univ_nonempty
        (fun pi x ↦ ∑ i : Fin (m + 1),
          forwardShift (fun y ↦ F.eval i y) (pi i) x)) := by
  classical
  exact finsetSupRealization
    (Finset.univ : Finset (Equiv.Perm (Fin (m + 1))))
    Finset.univ_nonempty
    (fun pi x ↦ ∑ i : Fin (m + 1),
      forwardShift (fun y ↦ F.eval i y) (pi i) x)
    (fun pi ↦ curvePermutationSumRealization F pi)

/-- Canonical realization of the Casoratian appearing in Theorem 6.2. -/
def canonicalCurveCasoratianRealization {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) :
    CurveCasoratianRealization F where
  order := (curveCasoratianNthRealization F).order
  order_le := (curveCasoratianNthRealization F).order_le
  function := (curveCasoratianNthRealization F).function
  eq_casoratian := fun x ↦ by
    rw [(curveCasoratianNthRealization F).eq_fun]
    simpa [tropicalCasoratian] using
      (Finset.sup'_apply Finset.univ_nonempty
        (fun pi x ↦ ∑ i : Fin (m + 1),
          forwardShift (fun y ↦ F.eval i y) (pi i) x) x)

/-- In ambient order one the canonical Casoratian is entire, because its
permutation summands are sums of shifted entire functions and their finite
maximum is convex. -/
theorem canonicalCurveCasoratianRealization_isTropicalEntire {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m) :
    IsTropicalEntire (canonicalCurveCasoratianRealization F).function := by
  classical
  change IsTropicalEntire (curveCasoratianNthRealization F).function
  unfold curveCasoratianNthRealization
  apply finsetSupRealization_isTropicalEntire
  intro pi
  exact curvePermutationSumRealization_isTropicalEntire F pi

/-- Assemble the finite-root data from the coordinate root sets alone.
Affine tails, finite Casoratian roots, and its possibly zero exact order
are constructed internally. Empty coordinate root sets are allowed. -/
def finiteRootCasoratianData {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hfinite : ∀ i, {x : ℝ | IsJthRoot (F.coordinate i) 1 x}.Finite) :
    FiniteRootCasoratianData m := by
  classical
  let D := fun i ↦ FiniteFirstOrderRootData.ofFiniteRoots
    (F.coordinate i) (F.order_le i) (F.coordinate_isTropicalEntire i) (hfinite i)
  let C := canonicalCurveCasoratianRealization F
  have hCfinite : {x : ℝ | IsJthRoot C.function 1 x}.Finite := by
    let R : ℝ := max 1 (Finset.univ.sup' Finset.univ_nonempty (fun i ↦ (D i).cutoff))
    have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
    have hcut (i : Fin (m + 1)) : (D i).cutoff ≤ R :=
      (Finset.le_sup' (fun i ↦ (D i).cutoff) (Finset.mem_univ i)).trans
        (le_max_right _ _)
    obtain ⟨S, _hS, U, V, hleft, hright⟩ := tropicalCasoratian_affine_tails
      (fun i y ↦ F.eval i y) R hR
      (fun i ↦ (D i).leftSlope) (fun i ↦ (D i).rightSlope)
      (fun i ↦ (D i).leftIntercept) (fun i ↦ (D i).rightIntercept)
      (fun i x hx ↦ (D i).left_affine x (by linarith [hcut i]))
      (fun i x hx ↦ (D i).right_affine x (by linarith [hcut i]))
    apply finite_firstOrder_roots_of_affine_tails C.function S
      (∑ i, (D i).leftSlope) (∑ i, (D i).rightSlope) U V
    · intro x hx
      rw [C.eq_casoratian]
      exact hleft x hx
    · intro x hx
      rw [C.eq_casoratian]
      exact hright x hx
  exact {
    coordinateOrder := F.order
    coordinate := F.coordinate
    casoratianOrder := C.order
    casoratian := C.function
    coordinateRoots := D
    casoratianRoots := FiniteFirstOrderRootData.ofFiniteRoots C.function C.order_le
      (canonicalCurveCasoratianRealization_isTropicalEntire F) hCfinite
    casoratian_eq := C.eq_casoratian }

/-- The Section 6 additive `O(1)` relation, using the paper's root-counting
notation explicitly: `N(r,-C₀) - ∑ᵢ N(r,-fᵢ) = O(1)`. -/
theorem finiteRootCasoratian_countingDifference_isBigO_one {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hfinite : ∀ i, {x : ℝ | IsJthRoot (F.coordinate i) 1 x}.Finite) :
    Asymptotics.IsBigO Filter.atTop
      (fun r ↦ integratedCounting 1 r (-(canonicalCurveCasoratianRealization F).function) -
        ∑ i, integratedCounting 1 r (-(F.coordinate i)))
      (fun _ : ℝ ↦ (1 : ℝ)) := by
  simp only [integratedCounting_neg]
  exact (finiteRootCasoratianData F hfinite).countingDifference_isBigO_one

/-- The finite-root first-order conclusion from the coordinate hypotheses,
including the zero-root case. No positive total root mass is assumed. -/
theorem finiteRootCasoratian_firstOrder_identity {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hfinite : ∀ i, {x : ℝ | IsJthRoot (F.coordinate i) 1 x}.Finite) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun r ↦ integratedCounting 1 r (-(canonicalCurveCasoratianRealization F).function))
      (fun r ↦ ∑ i, integratedCounting 1 r (-(F.coordinate i))) := by
  simp only [integratedCounting_neg]
  exact (finiteRootCasoratianData F hfinite).casoratianCounting_isEquivalent_coordinateCountingSum

/-- Literal multiplicative form with an error tending to zero. This form
remains meaningful when both counts vanish, unlike their quotient. -/
theorem finiteRootCasoratian_firstOrder_multiplicative {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m)
    (hfinite : ∀ i, {x : ℝ | IsJthRoot (F.coordinate i) 1 x}.Finite) :
    ∃ ε : ℝ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ᶠ r in Filter.atTop,
        integratedCounting 1 r (-(canonicalCurveCasoratianRealization F).function) =
          (∑ i, integratedCounting 1 r (-(F.coordinate i))) * (1 + ε r) := by
  obtain ⟨φ, hφ, hEq⟩ := (finiteRootCasoratian_firstOrder_identity F hfinite).exists_eq_mul
  refine ⟨fun r ↦ φ r - 1, ?_, ?_⟩
  · simpa using hφ.sub (tendsto_const_nhds (x := (1 : ℝ)))
  · filter_upwards [hEq] with r hr
    change integratedCounting 1 r (-(canonicalCurveCasoratianRealization F).function) =
      φ r * (∑ i, integratedCounting 1 r (-(F.coordinate i))) at hr
    rw [hr]
    ring

/-- Every canonical coordinate shift of a first-order curve is entire. -/
theorem canonicalCurveShiftRealizations_isTropicalEntire {m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation 1 m)
    (i k : Fin (m + 1)) :
    IsTropicalEntire ((canonicalCurveShiftRealizations F).shifted i k) := by
  exact forwardShiftRealization_isTropicalEntire
    (F.coordinate i) (F.order_le i) (F.coordinate_isTropicalEntire i) k

/-- Total root count through order `upTo`.  This is the paper's
`∑ⱼ N⁽ʲ⁾(r,1₀ ⊘ f)`. -/
def rootCountingUpTo {q : ℕ} (upTo : ℕ) (r : ℝ)
    (f : NthTropicalMeromorphicFunction q) : ℝ :=
  ∑ j ∈ Finset.Icc 1 upTo, integratedRootCounting j r f

theorem rootCountingUpTo_nonneg {q : ℕ} (upTo : ℕ) (r : ℝ)
    (f : NthTropicalMeromorphicFunction q) :
    0 ≤ rootCountingUpTo upTo r f := by
  unfold rootCountingUpTo
  exact Finset.sum_nonneg fun j _hj ↦ integratedRootCounting_nonneg j r f

theorem rootCountingUpTo_mono_radius {q : ℕ} (upTo : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (f : NthTropicalMeromorphicFunction q) :
    rootCountingUpTo upTo a f ≤ rootCountingUpTo upTo b f := by
  unfold rootCountingUpTo
  exact Finset.sum_le_sum fun j _hj ↦
    integratedRootCounting_mono_radius j ha hab f

/-- Total pole count through order `upTo`. -/
def poleCountingUpTo {q : ℕ} (upTo : ℕ) (r : ℝ)
    (f : NthTropicalMeromorphicFunction q) : ℝ :=
  ∑ j ∈ Finset.Icc 1 upTo, integratedCounting j r f

/-- Root count restricted to an arbitrary region. -/
def partialRootCounting {q : ℕ} (region : Set ℝ)
    [DecidablePred (fun x : ℝ ↦ x ∈ region)]
    (j : ℕ) (r : ℝ) (f : NthTropicalMeromorphicFunction q) : ℝ :=
  partialIntegratedCounting region j r (-f)

/-- Odd-order root counts of a forward shift are squeezed between the source
counts at radii `r-k` and `r+k`.  This is the exact, correction-free part of
the paper's `(NN2)`. -/
theorem integratedRootCounting_forwardShift_odd_sandwich
    {q : ℕ} (f : NthTropicalMeromorphicFunction q) (k : ℕ)
    {j : ℕ} (hj : Odd j) {r : ℝ} (hr : (k : ℝ) ≤ r) :
    integratedRootCounting j (r - k) f ≤
        integratedRootCounting j r (forwardShiftRealization f k).function ∧
      integratedRootCounting j r (forwardShiftRealization f k).function ≤
        integratedRootCounting j (r + k) f := by
  classical
  let shifted := (forwardShiftRealization f k).function
  let leftPoints := jthRootPoints f j (r - k)
  let shiftedPoints := jthRootPoints shifted j r
  let rightPoints := jthRootPoints f j (r + k)
  let toShift : ℝ → ℝ := fun x ↦ x - k
  let toSource : ℝ → ℝ := fun x ↦ x + k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hleft0 : 0 ≤ r - (k : ℝ) := sub_nonneg.mpr hr
  have htoShift_inj : Function.Injective toShift := by
    intro x y hxy
    dsimp [toShift] at hxy
    linarith
  have htoSource_inj : Function.Injective toSource := by
    intro x y hxy
    dsimp [toSource] at hxy
    linarith
  have hleftMap : leftPoints.image toShift ⊆ shiftedPoints := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rcases mem_jthRootPoints_iff.mp hx with ⟨hxr, hxroot⟩
    apply mem_jthRootPoints_iff.mpr
    refine ⟨?_, ?_⟩
    · constructor <;> linarith [hxr.1, hxr.2]
    · simpa [shifted, toShift] using
        (isJthRoot_forwardShiftRealization_of_odd f k hj (x - k)).2
          (by simpa using hxroot)
  have hrightMap : shiftedPoints.image toSource ⊆ rightPoints := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    rcases mem_jthRootPoints_iff.mp hy with ⟨hyr, hyroot⟩
    apply mem_jthRootPoints_iff.mpr
    refine ⟨?_, ?_⟩
    · constructor <;> linarith [hyr.1, hyr.2]
    · exact (isJthRoot_forwardShiftRealization_of_odd f k hj y).1
        (by simpa [shifted] using hyroot)
  constructor
  · unfold integratedRootCounting
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      (∑ x ∈ leftPoints,
          rootOrPoleMultiplicity f j x * (r - k - |x|) ^ j) ≤
          ∑ x ∈ leftPoints,
            rootOrPoleMultiplicity shifted j (toShift x) *
              (r - |toShift x|) ^ j := by
        apply Finset.sum_le_sum
        intro x hx
        have hxr := (mem_jthRootPoints_iff.mp hx).1
        have hxabs : |x| ≤ r - (k : ℝ) := (abs_lt.mpr hxr).le
        have hbase : 0 ≤ r - (k : ℝ) - |x| := by linarith
        have habs : |x - (k : ℝ)| ≤ |x| + (k : ℝ) := by
          calc
            |x - (k : ℝ)| ≤ |x| + |(k : ℝ)| := abs_sub x (k : ℝ)
            _ = |x| + (k : ℝ) := by rw [abs_of_nonneg hk0]
        have hweight : r - (k : ℝ) - |x| ≤ r - |x - (k : ℝ)| := by
          linarith
        rw [rootOrPoleMultiplicity_forwardShiftRealization_of_odd f k hj]
        simp only [toShift, sub_add_cancel]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact pow_le_pow_left₀ hbase hweight j
      _ = ∑ y ∈ leftPoints.image toShift,
            rootOrPoleMultiplicity shifted j y * (r - |y|) ^ j := by
        rw [Finset.sum_image]
        exact htoShift_inj.injOn
      _ ≤ ∑ y ∈ shiftedPoints,
            rootOrPoleMultiplicity shifted j y * (r - |y|) ^ j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hleftMap
        intro y hy _
        have hyr := (mem_jthRootPoints_iff.mp hy).1
        exact mul_nonneg (abs_nonneg _)
          (pow_nonneg (sub_nonneg.mpr (abs_lt.mpr hyr).le) _)
  · unfold integratedRootCounting
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      (∑ y ∈ shiftedPoints,
          rootOrPoleMultiplicity shifted j y * (r - |y|) ^ j) ≤
          ∑ y ∈ shiftedPoints,
            rootOrPoleMultiplicity f j (toSource y) *
              (r + k - |toSource y|) ^ j := by
        apply Finset.sum_le_sum
        intro y hy
        have hyr := (mem_jthRootPoints_iff.mp hy).1
        have hyabs : |y| ≤ r := (abs_lt.mpr hyr).le
        have hbase : 0 ≤ r - |y| := sub_nonneg.mpr hyabs
        have habs : |y + (k : ℝ)| ≤ |y| + (k : ℝ) := by
          calc
            |y + (k : ℝ)| ≤ |y| + |(k : ℝ)| := abs_add_le y (k : ℝ)
            _ = |y| + (k : ℝ) := by rw [abs_of_nonneg hk0]
        have hweight : r - |y| ≤ r + (k : ℝ) - |y + (k : ℝ)| := by
          linarith
        rw [rootOrPoleMultiplicity_forwardShiftRealization_of_odd f k hj]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact pow_le_pow_left₀ hbase hweight j
      _ = ∑ x ∈ shiftedPoints.image toSource,
            rootOrPoleMultiplicity f j x * (r + k - |x|) ^ j := by
        rw [Finset.sum_image]
        exact htoSource_inj.injOn
      _ ≤ ∑ x ∈ rightPoints,
            rootOrPoleMultiplicity f j x * (r + k - |x|) ^ j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hrightMap
        intro x hx _
        have hxr := (mem_jthRootPoints_iff.mp hx).1
        exact mul_nonneg (abs_nonneg _)
          (pow_nonneg (sub_nonneg.mpr (abs_lt.mpr hxr).le) _)

/-- Away from the central intervals `[-k,k]` and `[-2k,0]`, root counts in
every order satisfy the same exact shift sandwich.  On these complements the
source point and translated point have the same sign, so radial multiplicity
is transported without any parity assumption. -/
theorem exteriorRootCounting_forwardShift_sandwich
    {q : ℕ} (f : NthTropicalMeromorphicFunction q) (k j : ℕ)
    {r : ℝ} (hr : 2 * (k : ℝ) ≤ r) :
    partialIntegratedRootCounting (Set.Icc (-(k : ℝ)) k)ᶜ j (r - k) f ≤
        partialIntegratedRootCounting (Set.Icc (-2 * (k : ℝ)) 0)ᶜ j r
          (forwardShiftRealization f k).function ∧
      partialIntegratedRootCounting (Set.Icc (-2 * (k : ℝ)) 0)ᶜ j r
          (forwardShiftRealization f k).function ≤
        partialIntegratedRootCounting (Set.Icc (-(k : ℝ)) k)ᶜ j (r + k) f := by
  classical
  let shifted := (forwardShiftRealization f k).function
  let sourceCentral : Set ℝ := Set.Icc (-(k : ℝ)) k
  let shiftCentral : Set ℝ := Set.Icc (-2 * (k : ℝ)) 0
  let leftPoints := (jthRootPoints f j (r - k)).filter
    (fun x ↦ x ∈ sourceCentralᶜ)
  let shiftedPoints := (jthRootPoints shifted j r).filter
    (fun x ↦ x ∈ shiftCentralᶜ)
  let rightPoints := (jthRootPoints f j (r + k)).filter
    (fun x ↦ x ∈ sourceCentralᶜ)
  let toShift : ℝ → ℝ := fun x ↦ x - k
  let toSource : ℝ → ℝ := fun x ↦ x + k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr0 : 0 ≤ r := le_trans (mul_nonneg (by norm_num) hk0) hr
  have hleft0 : 0 ≤ r - (k : ℝ) := by linarith
  have htoShift_inj : Function.Injective toShift := by
    intro x y hxy
    dsimp [toShift] at hxy
    linarith
  have htoSource_inj : Function.Injective toSource := by
    intro x y hxy
    dsimp [toSource] at hxy
    linarith
  have hleftMap : leftPoints.image toShift ⊆ shiftedPoints := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rcases Finset.mem_filter.mp hx with ⟨hxrootPoint, hxoutside⟩
    rcases mem_jthRootPoints_iff.mp hxrootPoint with ⟨hxr, hxroot⟩
    have hxoutside' : -(k : ℝ) ≤ x → (k : ℝ) < x := by
      simpa [sourceCentral] using hxoutside
    have hxside : x < -(k : ℝ) ∨ (k : ℝ) < x := by
      by_cases hx : x < -(k : ℝ)
      · exact Or.inl hx
      · exact Or.inr (hxoutside' (le_of_not_gt hx))
    have hsame :
        (0 < x - (k : ℝ) ∧ 0 < x - (k : ℝ) + k) ∨
          (x - (k : ℝ) < 0 ∧ x - (k : ℝ) + k < 0) := by
      rcases hxside with hx | hx
      · exact Or.inr ⟨by linarith, by linarith⟩
      · exact Or.inl ⟨by linarith, by linarith⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_jthRootPoints_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · constructor <;> linarith [hxr.1, hxr.2]
    · simpa [shifted, toShift] using
        (isJthRoot_forwardShiftRealization_of_sameSign f k j hsame).2
          (by simpa using hxroot)
    · change ¬(-2 * (k : ℝ) ≤ x - k ∧ x - k ≤ 0)
      rcases hxside with hx | hx
      · intro hmem
        linarith
      · intro hmem
        linarith
  have hrightMap : shiftedPoints.image toSource ⊆ rightPoints := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    rcases Finset.mem_filter.mp hy with ⟨hyrootPoint, hyoutside⟩
    rcases mem_jthRootPoints_iff.mp hyrootPoint with ⟨hyr, hyroot⟩
    have hyoutside' : -2 * (k : ℝ) ≤ y → 0 < y := by
      simpa [shiftCentral] using hyoutside
    have hyside : y < -2 * (k : ℝ) ∨ 0 < y := by
      by_cases hy : y < -2 * (k : ℝ)
      · exact Or.inl hy
      · exact Or.inr (hyoutside' (le_of_not_gt hy))
    have hsame :
        (0 < y ∧ 0 < y + (k : ℝ)) ∨
          (y < 0 ∧ y + (k : ℝ) < 0) := by
      rcases hyside with hy | hy
      · exact Or.inr ⟨by linarith, by linarith⟩
      · exact Or.inl ⟨hy, by linarith⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_jthRootPoints_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · constructor <;> linarith [hyr.1, hyr.2]
    · exact (isJthRoot_forwardShiftRealization_of_sameSign f k j hsame).1
        (by simpa [shifted] using hyroot)
    · change ¬(-(k : ℝ) ≤ y + k ∧ y + k ≤ k)
      rcases hyside with hy | hy
      · intro hmem
        linarith
      · intro hmem
        linarith
  constructor
  · unfold partialIntegratedRootCounting
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    change (∑ x ∈ leftPoints,
        rootOrPoleMultiplicity f j x * (r - k - |x|) ^ j) ≤ _
    change _ ≤ ∑ y ∈ shiftedPoints,
      rootOrPoleMultiplicity shifted j y * (r - |y|) ^ j
    calc
      (∑ x ∈ leftPoints,
          rootOrPoleMultiplicity f j x * (r - k - |x|) ^ j) ≤
          ∑ x ∈ leftPoints,
            rootOrPoleMultiplicity shifted j (toShift x) *
              (r - |toShift x|) ^ j := by
        apply Finset.sum_le_sum
        intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hxrootPoint, hxoutside⟩
        have hxr := (mem_jthRootPoints_iff.mp hxrootPoint).1
        have hxoutside' : -(k : ℝ) ≤ x → (k : ℝ) < x := by
          simpa [sourceCentral] using hxoutside
        have hxside : x < -(k : ℝ) ∨ (k : ℝ) < x := by
          by_cases hx : x < -(k : ℝ)
          · exact Or.inl hx
          · exact Or.inr (hxoutside' (le_of_not_gt hx))
        have hsame :
            (0 < x - (k : ℝ) ∧ 0 < x - (k : ℝ) + k) ∨
              (x - (k : ℝ) < 0 ∧ x - (k : ℝ) + k < 0) := by
          rcases hxside with hx | hx
          · exact Or.inr ⟨by linarith, by linarith⟩
          · exact Or.inl ⟨by linarith, by linarith⟩
        have hbase : 0 ≤ r - (k : ℝ) - |x| :=
          sub_nonneg.mpr (abs_lt.mpr hxr).le
        have habs : |x - (k : ℝ)| ≤ |x| + (k : ℝ) := by
          calc
            |x - (k : ℝ)| ≤ |x| + |(k : ℝ)| := abs_sub x (k : ℝ)
            _ = |x| + (k : ℝ) := by rw [abs_of_nonneg hk0]
        have hweight : r - (k : ℝ) - |x| ≤ r - |x - (k : ℝ)| := by
          linarith
        rw [rootOrPoleMultiplicity_forwardShiftRealization_of_sameSign f k j hsame]
        simp only [toShift, sub_add_cancel]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact pow_le_pow_left₀ hbase hweight j
      _ = ∑ y ∈ leftPoints.image toShift,
            rootOrPoleMultiplicity shifted j y * (r - |y|) ^ j := by
        rw [Finset.sum_image]
        exact htoShift_inj.injOn
      _ ≤ ∑ y ∈ shiftedPoints,
            rootOrPoleMultiplicity shifted j y * (r - |y|) ^ j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hleftMap
        intro y hy _
        have hyr := (mem_jthRootPoints_iff.mp (Finset.mem_filter.mp hy).1).1
        exact mul_nonneg (abs_nonneg _)
          (pow_nonneg (sub_nonneg.mpr (abs_lt.mpr hyr).le) _)
  · unfold partialIntegratedRootCounting
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    change (∑ y ∈ shiftedPoints,
        rootOrPoleMultiplicity shifted j y * (r - |y|) ^ j) ≤ _
    change _ ≤ ∑ x ∈ rightPoints,
      rootOrPoleMultiplicity f j x * (r + k - |x|) ^ j
    calc
      (∑ y ∈ shiftedPoints,
          rootOrPoleMultiplicity shifted j y * (r - |y|) ^ j) ≤
          ∑ y ∈ shiftedPoints,
            rootOrPoleMultiplicity f j (toSource y) *
              (r + k - |toSource y|) ^ j := by
        apply Finset.sum_le_sum
        intro y hy
        rcases Finset.mem_filter.mp hy with ⟨hyrootPoint, hyoutside⟩
        have hyr := (mem_jthRootPoints_iff.mp hyrootPoint).1
        have hyoutside' : -2 * (k : ℝ) ≤ y → 0 < y := by
          simpa [shiftCentral] using hyoutside
        have hyside : y < -2 * (k : ℝ) ∨ 0 < y := by
          by_cases hy : y < -2 * (k : ℝ)
          · exact Or.inl hy
          · exact Or.inr (hyoutside' (le_of_not_gt hy))
        have hsame :
            (0 < y ∧ 0 < y + (k : ℝ)) ∨
              (y < 0 ∧ y + (k : ℝ) < 0) := by
          rcases hyside with hy | hy
          · exact Or.inr ⟨by linarith, by linarith⟩
          · exact Or.inl ⟨hy, by linarith⟩
        have hbase : 0 ≤ r - |y| := sub_nonneg.mpr (abs_lt.mpr hyr).le
        have habs : |y + (k : ℝ)| ≤ |y| + (k : ℝ) := by
          calc
            |y + (k : ℝ)| ≤ |y| + |(k : ℝ)| := abs_add_le y (k : ℝ)
            _ = |y| + (k : ℝ) := by rw [abs_of_nonneg hk0]
        have hweight : r - |y| ≤ r + (k : ℝ) - |y + (k : ℝ)| := by
          linarith
        rw [rootOrPoleMultiplicity_forwardShiftRealization_of_sameSign f k j hsame]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact pow_le_pow_left₀ hbase hweight j
      _ = ∑ x ∈ shiftedPoints.image toSource,
            rootOrPoleMultiplicity f j x * (r + k - |x|) ^ j := by
        rw [Finset.sum_image]
        exact htoSource_inj.injOn
      _ ≤ ∑ x ∈ rightPoints,
            rootOrPoleMultiplicity f j x * (r + k - |x|) ^ j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hrightMap
        intro x hx _
        have hxr := (mem_jthRootPoints_iff.mp (Finset.mem_filter.mp hx).1).1
        exact mul_nonneg (abs_nonneg _)
          (pow_nonneg (sub_nonneg.mpr (abs_lt.mpr hxr).le) _)

/-- Exact even-order sandwich with the compact corrections evaluated at the
matching radii `r-k` and `r+k`.  Replacing those two compact counts by their
value at `r` is the separate lower-degree remainder in the source proof. -/
theorem integratedRootCounting_forwardShift_even_corrected_sandwich
    {q : ℕ} (f : NthTropicalMeromorphicFunction q) (k j : ℕ)
    {r : ℝ} (hr : 2 * (k : ℝ) ≤ r) :
    integratedRootCounting j (r - k) f ≤
        integratedRootCounting j r (forwardShiftRealization f k).function +
          partialIntegratedRootCounting (Set.Icc (-(k : ℝ)) k) j (r - k) f -
          partialIntegratedRootCounting (Set.Icc (-2 * (k : ℝ)) 0) j r
            (forwardShiftRealization f k).function ∧
      integratedRootCounting j r (forwardShiftRealization f k).function +
          partialIntegratedRootCounting (Set.Icc (-(k : ℝ)) k) j (r + k) f -
          partialIntegratedRootCounting (Set.Icc (-2 * (k : ℝ)) 0) j r
            (forwardShiftRealization f k).function ≤
        integratedRootCounting j (r + k) f := by
  have hext := exteriorRootCounting_forwardShift_sandwich f k j hr
  have hleftPartition := partialIntegratedRootCounting_add_compl
    (Set.Icc (-(k : ℝ)) k) j (r - k) f
  have hshiftPartition := partialIntegratedRootCounting_add_compl
    (Set.Icc (-2 * (k : ℝ)) 0) j r
      (forwardShiftRealization f k).function
  have hrightPartition := partialIntegratedRootCounting_add_compl
    (Set.Icc (-(k : ℝ)) k) j (r + k) f
  constructor <;> linarith

/-- Quantitative consequence of the odd-order sandwich: the shifted
discrepancy is bounded by the two adjacent increments of the source counting
function. -/
theorem integratedRootCounting_forwardShift_odd_discrepancy_le
    {q : ℕ} (f : NthTropicalMeromorphicFunction q) (k : ℕ)
    {j : ℕ} (hj : Odd j) {r : ℝ} (hr : 2 * (k : ℝ) ≤ r) :
    |integratedRootCounting j r (forwardShiftRealization f k).function -
        integratedRootCounting j r f| ≤
      (integratedRootCounting j (r + k) f - integratedRootCounting j r f) +
        (integratedRootCounting j r f - integratedRootCounting j (r - k) f) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hrk0 : 0 ≤ r - (k : ℝ) := by linarith
  have hshift := integratedRootCounting_forwardShift_odd_sandwich
    f k hj (le_trans (by linarith : (k : ℝ) ≤ 2 * k) hr)
  have hminus := integratedRootCounting_mono_radius j hrk0
    (by linarith : r - (k : ℝ) ≤ r) f
  have hplus := integratedRootCounting_mono_radius j
    (by linarith : 0 ≤ r) (by linarith : r ≤ r + (k : ℝ)) f
  rw [abs_le]
  constructor <;> linarith

/-- Quantitative corrected consequence of the exterior sandwich.  The source
central count is taken at the common radius `r`; its monotonicity places the
corrected shifted count between the source counts at `r-k` and `r+k` exactly.
Thus no separate compact-support asymptotic lemma is needed. -/
theorem integratedRootCounting_forwardShift_corrected_discrepancy_le
    {q : ℕ} (f : NthTropicalMeromorphicFunction q) (k j : ℕ)
    {r : ℝ} (hr : 2 * (k : ℝ) ≤ r) :
    |integratedRootCounting j r (forwardShiftRealization f k).function -
        integratedRootCounting j r f| ≤
      |partialIntegratedRootCounting (Set.Icc (-2 * (k : ℝ)) 0) j r
          (forwardShiftRealization f k).function -
        partialIntegratedRootCounting (Set.Icc (-(k : ℝ)) k) j r f| +
      (integratedRootCounting j (r + k) f - integratedRootCounting j r f) +
        (integratedRootCounting j r f - integratedRootCounting j (r - k) f) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hrk0 : 0 ≤ r - (k : ℝ) := by linarith
  have hsandwich := integratedRootCounting_forwardShift_even_corrected_sandwich
    f k j hr
  have hcentralMinus := partialIntegratedRootCounting_mono_radius
    (Set.Icc (-(k : ℝ)) k) j hrk0
      (by linarith : r - (k : ℝ) ≤ r) f
  have hcentralPlus := partialIntegratedRootCounting_mono_radius
    (Set.Icc (-(k : ℝ)) k) j (by linarith : 0 ≤ r)
      (by linarith : r ≤ r + (k : ℝ)) f
  have hminus := integratedRootCounting_mono_radius j hrk0
    (by linarith : r - (k : ℝ) ≤ r) f
  have hplus := integratedRootCounting_mono_radius j
    (by linarith : 0 ≤ r) (by linarith : r ≤ r + (k : ℝ)) f
  let shiftedCount :=
    integratedRootCounting j r (forwardShiftRealization f k).function
  let sourceCount := integratedRootCounting j r f
  let sourceMinus := integratedRootCounting j (r - k) f
  let sourcePlus := integratedRootCounting j (r + k) f
  let shiftCentral := partialIntegratedRootCounting
    (Set.Icc (-2 * (k : ℝ)) 0) j r
      (forwardShiftRealization f k).function
  let sourceCentral := partialIntegratedRootCounting
    (Set.Icc (-(k : ℝ)) k) j r f
  have hlower : sourceMinus ≤ shiftedCount + sourceCentral - shiftCentral := by
    dsimp [sourceMinus, shiftedCount, sourceCentral, shiftCentral]
    linarith [hsandwich.1, hcentralMinus]
  have hupper : shiftedCount + sourceCentral - shiftCentral ≤ sourcePlus := by
    dsimp [sourcePlus, shiftedCount, sourceCentral, shiftCentral]
    linarith [hsandwich.2, hcentralPlus]
  have hcenterBounds :
      |(shiftedCount + sourceCentral - shiftCentral) - sourceCount| ≤
        (sourcePlus - sourceCount) + (sourceCount - sourceMinus) := by
    rw [abs_le]
    constructor <;>
      dsimp [sourcePlus, sourceCount, sourceMinus] at * <;> linarith
  calc
    |shiftedCount - sourceCount| =
        |((shiftedCount + sourceCentral - shiftCentral) - sourceCount) +
          (shiftCentral - sourceCentral)| := by
      congr 1
      ring
    _ ≤ |(shiftedCount + sourceCentral - shiftCentral) - sourceCount| +
          |shiftCentral - sourceCentral| := abs_add_le _ _
    _ ≤ |shiftCentral - sourceCentral| +
          (sourcePlus - sourceCount) + (sourceCount - sourceMinus) := by
      linarith
    _ = |partialIntegratedRootCounting (Set.Icc (-2 * (k : ℝ)) 0) j r
            (forwardShiftRealization f k).function -
          partialIntegratedRootCounting (Set.Icc (-(k : ℝ)) k) j r f| +
        (integratedRootCounting j (r + k) f - integratedRootCounting j r f) +
          (integratedRootCounting j r f - integratedRootCounting j (r - k) f) := by
      rfl

/-- Sum of reciprocal counts of all curve coordinates. -/
def coordinateRootCountingSum {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) (r : ℝ) : ℝ :=
  ∑ i, rootCountingUpTo n r (F.coordinate i)

/-- Sum of reciprocal counts of the diagonal shifts `f̄ᵢ^[i]`. -/
def diagonalShiftRootCountingSum {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (S : CurveShiftRealizations F) (r : ℝ) : ℝ :=
  ∑ i, rootCountingUpTo n r (S.shifted i i)

/-- The sum of the orderwise shifted-root discrepancies.  This is the left
side of `(equa1)`, summed over the diagonal choices `k=i` used in `(equa3)`.
-/
def shiftRootCountingDiscrepancy {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (S : CurveShiftRealizations F) (r : ℝ) : ℝ :=
  ∑ i : Fin (m + 1), ∑ j ∈ Finset.Icc 1 n,
    |integratedRootCounting j r (S.shifted i i) -
      integratedRootCounting j r (F.coordinate i)|

/-- The pole discrepancy in the first line on the right of (6f2). -/
def casoratianPoleDiscrepancy {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (S : CurveShiftRealizations F) (C : CurveCasoratianRealization F)
    (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n,
    |integratedCounting j r C.function -
      ∑ i, integratedCounting j r (S.shifted i i)|

/-- The even-order compact-region correction in the second line of (6f2). -/
def evenShiftCorrection {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (S : CurveShiftRealizations F) (r : ℝ) : ℝ :=
  ∑ i : Fin (m + 1), ∑ j ∈ Finset.Icc 1 (n / 2),
    |partialRootCounting
        (Set.Icc (-2 * (i : ℝ)) 0) (2 * j) r (S.shifted i i) -
      partialRootCounting
        (Set.Icc (-(i : ℝ)) (i : ℝ)) (2 * j) r (F.coordinate i)|

/-- The same even correction indexed directly by the even orders in
`{1,…,n}`.  This form is convenient for the orderwise shift estimate. -/
def evenShiftCorrectionByOrder {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (S : CurveShiftRealizations F) (r : ℝ) : ℝ :=
  ∑ i : Fin (m + 1), ∑ j ∈ (Finset.Icc 1 n).filter Even,
    |partialRootCounting
        (Set.Icc (-2 * (i : ℝ)) 0) j r (S.shifted i i) -
      partialRootCounting
        (Set.Icc (-(i : ℝ)) (i : ℝ)) j r (F.coordinate i)|

/-- Reindexing even orders by `j = 2ℓ` identifies the direct parity form
with the paper's `ℓ = 1,…,⌊n/2⌋` notation. -/
theorem evenShiftCorrectionByOrder_eq_evenShiftCorrection
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (S : CurveShiftRealizations F) (r : ℝ) :
    evenShiftCorrectionByOrder F S r = evenShiftCorrection F S r := by
  classical
  unfold evenShiftCorrectionByOrder evenShiftCorrection
  apply Finset.sum_congr rfl
  intro i _hi
  symm
  apply Finset.sum_bij (fun l _ ↦ 2 * l)
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hlone := (Finset.mem_Icc.mp hl).1
    have hln := (Finset.mem_Icc.mp hl).2
    have htwo : 2 * l ≤ n := by
      simpa [Nat.mul_comm] using
        ((Nat.le_div_iff_mul_le Nat.zero_lt_two).1 hln)
    exact ⟨⟨by omega, htwo⟩, even_two_mul l⟩
  · intro l₁ hl₁ l₂ hl₂ h
    omega
  · intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjn, hjeven⟩
    obtain ⟨l, hl⟩ := hjeven
    have hjeq : j = 2 * l := by omega
    have hlpos : 1 ≤ l := by
      have hjpos := (Finset.mem_Icc.mp hjn).1
      omega
    have hltwo : l * 2 ≤ n := by
      have hjle := (Finset.mem_Icc.mp hjn).2
      omega
    have hldiv : l ≤ n / 2 :=
      (Nat.le_div_iff_mul_le Nat.zero_lt_two).2 hltwo
    exact ⟨l, Finset.mem_Icc.mpr ⟨hlpos, hldiv⟩, hjeq.symm⟩
  · intro l hl
    rfl

/-- Sum of the two source-count increments which control all diagonal shifts
in `(equa1)`. -/
def coordinateRootShiftIncrement {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m) (r : ℝ) : ℝ :=
  ∑ i : Fin (m + 1), ∑ j ∈ Finset.Icc 1 n,
    ((integratedRootCounting j (r + (i : ℝ)) (F.coordinate i) -
        integratedRootCounting j r (F.coordinate i)) +
      (integratedRootCounting j r (F.coordinate i) -
        integratedRootCounting j (r - (i : ℝ)) (F.coordinate i)))

/-- Jensen's formula gives the domination used in the analytic part of
`(equa1)`: each coordinate's total root count is bounded by the curve
characteristic plus the explicit fixed normalization constant. -/
theorem rootCountingUpTo_coordinate_le_cartan_add_constant
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    (i : Fin (m + 1)) {r : ℝ} (hr : 0 < r) :
    rootCountingUpTo n r (F.coordinate i) ≤
      cartanCharacteristic F r +
        (curveCoordinateMaximum F 0 - F.eval i 0) := by
  unfold rootCountingUpTo
  rw [sum_integratedRootCounting_eq_of_order_le
    (F.coordinate i) (F.order_le i) r]
  rw [sum_integratedRootCounting_eq_endpointMean_sub
    (F.coordinate i) (F.coordinate_isTropicalEntire i) hr]
  have hplus := coordinate_le_curveCoordinateMaximum F i r
  have hminus := coordinate_le_curveCoordinateMaximum F i (-r)
  change (F.coordinate i) r ≤ curveCoordinateMaximum F r at hplus
  change (F.coordinate i) (-r) ≤ curveCoordinateMaximum F (-r) at hminus
  change ((F.coordinate i) r + (F.coordinate i) (-r)) / 2 -
      (F.coordinate i) 0 ≤ cartanCharacteristic F r +
        (curveCoordinateMaximum F 0 - (F.coordinate i) 0)
  unfold cartanCharacteristic
  linarith

/-- After summing over the derivative orders, the two adjacent increments
for each coordinate telescope to a single total root-count increment. -/
theorem coordinateRootShiftIncrement_eq_rootCountingUpTo_sub
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m) (r : ℝ) :
    coordinateRootShiftIncrement F r =
      ∑ i : Fin (m + 1),
        (rootCountingUpTo n (r + (i : ℝ)) (F.coordinate i) -
          rootCountingUpTo n (r - (i : ℝ)) (F.coordinate i)) := by
  classical
  unfold coordinateRootShiftIncrement rootCountingUpTo
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- On the radii used in `(equa1)`, every summand of the concrete shift
remainder is nonnegative. -/
theorem coordinateRootShiftIncrement_nonneg
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    {r : ℝ} (hr : 2 * (m : ℝ) ≤ r) :
    0 ≤ coordinateRootShiftIncrement F r := by
  classical
  unfold coordinateRootShiftIncrement
  apply Finset.sum_nonneg
  intro i _hi
  apply Finset.sum_nonneg
  intro j _hj
  have hi : (i : ℕ) ≤ m := Fin.le_last i
  have hir : (i : ℝ) ≤ m := by exact_mod_cast hi
  have hminus0 : 0 ≤ r - (i : ℝ) := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hleft := integratedRootCounting_mono_radius j hminus0
    (by linarith : r - (i : ℝ) ≤ r) (F.coordinate i)
  have hright := integratedRootCounting_mono_radius j
    (by linarith : 0 ≤ r) (by linarith : r ≤ r + (i : ℝ)) (F.coordinate i)
  linarith

/-- Complete pointwise `(equa1)` reduction for the canonical diagonal shifts.
All translation geometry is discharged here; the only remaining analytic
input is that the finite sum of source-count increments is little-o of the
curve scale. -/
theorem shiftRootCountingDiscrepancy_canonical_le
    {n m : ℕ} (F : TropicalHolomorphicCurveRepresentation n m)
    {r : ℝ} (hr : 2 * (m : ℝ) ≤ r) :
    shiftRootCountingDiscrepancy F (canonicalCurveShiftRealizations F) r ≤
      evenShiftCorrection F (canonicalCurveShiftRealizations F) r +
        coordinateRootShiftIncrement F r := by
  classical
  rw [← evenShiftCorrectionByOrder_eq_evenShiftCorrection]
  unfold shiftRootCountingDiscrepancy evenShiftCorrectionByOrder
    coordinateRootShiftIncrement
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _hi
  rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hi : (i : ℕ) ≤ m := Fin.le_last i
  have hir : 2 * (i : ℝ) ≤ r := by
    have : (i : ℝ) ≤ m := by exact_mod_cast hi
    linarith
  by_cases hjeven : Even j
  · have hcorr := integratedRootCounting_forwardShift_corrected_discrepancy_le
      (F.coordinate i) (i : ℕ) j hir
    have hshiftCentral :
        partialRootCounting (Set.Icc (-2 * (i : ℝ)) 0) j r
            (forwardShiftRealization (F.coordinate i) (i : ℕ)).function =
          partialIntegratedRootCounting (Set.Icc (-2 * (i : ℝ)) 0) j r
            (forwardShiftRealization (F.coordinate i) (i : ℕ)).function := by
      simpa [partialRootCounting] using
        (partialIntegratedCounting_neg
          (forwardShiftRealization (F.coordinate i) (i : ℕ)).function
          (Set.Icc (-2 * (i : ℝ)) 0) j r)
    have hsourceCentral :
        partialRootCounting (Set.Icc (-(i : ℝ)) (i : ℝ)) j r
            (F.coordinate i) =
          partialIntegratedRootCounting (Set.Icc (-(i : ℝ)) (i : ℝ)) j r
            (F.coordinate i) := by
      simpa [partialRootCounting] using
        (partialIntegratedCounting_neg (F.coordinate i)
          (Set.Icc (-(i : ℝ)) (i : ℝ)) j r)
    simp only [hjeven, if_pos, canonicalCurveShiftRealizations]
    rw [hshiftCentral, hsourceCentral]
    linarith
  · have hjodd : Odd j := Nat.not_even_iff_odd.mp hjeven
    have hodd := integratedRootCounting_forwardShift_odd_discrepancy_le
      (F.coordinate i) (i : ℕ) hjodd hir
    simpa [canonicalCurveShiftRealizations, hjeven] using hodd

/-- Left side of Theorem 6.2. -/
def truncatedSecondMainDifference {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (C : CurveCasoratianRealization F) (r : ℝ) : ℝ :=
  |coordinateRootCountingSum F r - rootCountingUpTo n r C.function|

/-- The centered endpoint mean from Jensen's formula. -/
def centeredEndpointMean {q : ℕ}
    (f : NthTropicalMeromorphicFunction q) (r : ℝ) : ℝ :=
  (f r + f (-r)) / 2 - f 0

/-- Exact endpoint defect between the Casoratian and the diagonal shifts.
The paper estimates its nonconstant part in (equa2); centering also includes
the fixed `O(1)` term from (equa3). -/
def casoratianCenteredEndpointDefect {n m : ℕ}
    (F : TropicalHolomorphicCurveRepresentation n m)
    (S : CurveShiftRealizations F) (C : CurveCasoratianRealization F)
    (r : ℝ) : ℝ :=
  |centeredEndpointMean C.function r -
    ∑ i, centeredEndpointMean (S.shifted i i) r|

end

end NthTropicalNevanlinna
