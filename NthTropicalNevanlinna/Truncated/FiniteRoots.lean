import NthTropicalNevanlinna.Truncated.Casoratian
import NthTropicalNevanlinna.Curves.SecondMain
import NthTropicalNevanlinna.PoissonJensen.IntrinsicTelescoping
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# The finite-root first-order Casoratian identity

The beginning of Section 6 assumes finitely many first-order roots. We
construct affine tails from that hypothesis, allowing empty root sets and
functions of exact order zero. The exact affine counting formulas imply the
paper's additive `O(1)` estimate. Splitting into positive and zero total root
mass gives the multiplicative `1 + o(1)` conclusion without division by zero.
All counts here are root counts, namely `N(r,-f)` in the paper's notation.
The curve-facing automatic construction is in `Truncated/ShiftCounting.lean`.
-/

namespace NthTropicalNevanlinna

noncomputable section

open Filter Function Set
open scoped BigOperators Topology
open Asymptotics

/-- Finite roots of an entire function of order at most one give affine
tails. The root set may be empty. -/
theorem exists_affine_tails_of_finite_firstOrder_roots
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (hn : n ≤ 1)
    (hf : IsTropicalEntire f) (hfinite : {x : ℝ | IsJthRoot f 1 x}.Finite) :
    ∃ R : ℝ, 0 < R ∧ ∃ a b u v : ℝ,
      (∀ x, IsJthRoot f 1 x → |x| < R) ∧
      (∀ x, x < -R → f x = a * x + u) ∧
      (∀ x, R < x → f x = b * x + v) := by
  classical
  obtain ⟨B, hB⟩ := (hfinite.image (fun x : ℝ ↦ |x|)).bddAbove
  let R : ℝ := max B 0 + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right B 0]
  have hbound (x : ℝ) (hx : IsJthRoot f 1 x) : |x| < R := by
    have hxB := hB (mem_image_of_mem (fun x : ℝ ↦ |x|) hx)
    dsimp [R]
    linarith [le_max_left B 0]
  have hzero (x : ℝ) (hx : R ≤ |x|) : multiplicity f 1 x = 0 := by
    have hnonneg := entire_multiplicity_nonneg_upTo f hf hn x 1 (by omega) (by omega)
    apply le_antisymm _ hnonneg
    apply le_of_not_gt
    intro hpos
    exact (not_lt_of_ge hx) (hbound x hpos)
  let a := ∑ j ∈ Finset.Icc 1 n, normalizedLeftJet f j (-R)
  let b := ∑ j ∈ Finset.Icc 1 n, normalizedRightJet f j R
  refine ⟨R, hR, a, b, f (-R) + a * R, f R - b * R, hbound, ?_, ?_⟩
  · intro x hx
    have hempty : jthSingularPointsIn f 1 x (-R) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have h := mem_jthSingularPointsIn_iff.mp hy
      exact h.2 (hzero y (by linarith [neg_le_abs y, h.1.2]))
    have ht := sub_leftEndpoint_eq_intrinsic_singularity_sum_of_neg f hx (by linarith : -R < 0)
    have heq : f (-R) - f x = a * (-R - x) := by
      rw [ht]
      dsimp [a]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have hj1 : j = 1 := by have h := Finset.mem_Icc.mp hj; omega
      subst j
      simp [hempty]
    linarith
  · intro x hx
    have hempty : jthSingularPointsIn f 1 R x = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have h := mem_jthSingularPointsIn_iff.mp hy
      exact h.2 (hzero y (by linarith [le_abs_self y, h.1.1]))
    have ht := endpoint_sub_eq_intrinsic_singularity_sum_of_pos f hR hx
    have heq : f x - f R = b * (x - R) := by
      rw [ht]
      dsimp [b]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have hj1 : j = 1 := by have h := Finset.mem_Icc.mp hj; omega
      subst j
      simp [hempty]
    linarith

private theorem firstMultiplicity_eq_zero_of_polynomial_on_Ioo
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (p : Polynomial ℝ)
    {a b x : ℝ} (hx : x ∈ Ioo a b)
    (heq : ∀ y ∈ Ioo a b, f y = p.eval y) : multiplicity f 1 x = 0 := by
  obtain ⟨l, hl, hleft⟩ := f.presentation.exists_left_germ_interval x
  obtain ⟨u, hu, hright⟩ := f.presentation.exists_right_germ_interval x
  have hpLeft : f.presentation.leftPieceAt x = p := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Ioo_infinite (max_lt hl hx.1)).mono
    intro y hy
    exact (hleft y ⟨(le_max_left _ _).trans_lt hy.1, hy.2⟩).symm.trans
      (heq y ⟨(le_max_right _ _).trans_lt hy.1, hy.2.trans hx.2⟩)
  have hpRight : f.presentation.rightPieceAt x = p := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Ioo_infinite (lt_min hu hx.2)).mono
    intro y hy
    exact (hright y ⟨hy.1, hy.2.trans_le (min_le_left _ _)⟩).symm.trans
      (heq y ⟨hx.1.trans hy.1, hy.2.trans_le (min_le_right _ _)⟩)
  simp only [multiplicity, multiplicityUsingPresentation, hpLeft, hpRight]
  unfold rightSign leftSign
  split_ifs <;> ring

/-- Affine tails imply that every first-order root lies in a bounded
interval, so local finiteness gives a finite global root set. -/
theorem finite_firstOrder_roots_of_affine_tails
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (R a b u v : ℝ)
    (hleft : ∀ x, x < -R → f x = a * x + u)
    (hright : ∀ x, R < x → f x = b * x + v) :
    {x : ℝ | IsJthRoot f 1 x}.Finite := by
  classical
  apply (jthRootPoints f 1 (R + 1)).finite_toSet.subset
  intro x hx
  have hxroot : 0 < multiplicity f 1 x := hx
  have hlow : -R ≤ x := by
    by_contra h
    have hxR := lt_of_not_ge h
    have hz := firstMultiplicity_eq_zero_of_polynomial_on_Ioo f
      (Polynomial.C a * Polynomial.X + Polynomial.C u)
      (show x ∈ Ioo (x - 1) (-R) by constructor <;> linarith)
      (fun y hy ↦ by simpa using hleft y hy.2)
    linarith
  have hupp : x ≤ R := by
    by_contra h
    have hxR := lt_of_not_ge h
    have hz := firstMultiplicity_eq_zero_of_polynomial_on_Ioo f
      (Polynomial.C b * Polynomial.X + Polynomial.C v)
      (show x ∈ Ioo R (x + 1) by constructor <;> linarith)
      (fun y hy ↦ by simpa using hright y hy.1)
    linarith
  exact mem_jthRootPoints_iff.mpr ⟨⟨by linarith, by linarith⟩, hx⟩


/-- Every permutation has the same slope on each tail. A zero slope is
allowed, so the Casoratian may be constant. -/
theorem tropicalCasoratian_affine_tails {m : ℕ}
    (f : Fin (m + 1) → ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (a b u v : Fin (m + 1) → ℝ)
    (hleft : ∀ i x, x < -R → f i x = a i * x + u i)
    (hright : ∀ i x, R < x → f i x = b i * x + v i) :
    ∃ S : ℝ, 0 < S ∧ ∃ U V : ℝ,
      (∀ x, x < -S → tropicalCasoratian f x = (∑ i, a i) * x + U) ∧
      (∀ x, S < x → tropicalCasoratian f x = (∑ i, b i) * x + V) := by
  let S : ℝ := R + m + 1
  have hS : 0 < S := by dsimp [S]; positivity
  refine ⟨S, hS, tropicalCasoratian f (-S) + (∑ i, a i) * S,
    tropicalCasoratian f S - (∑ i, b i) * S, ?_, ?_⟩
  · intro x hx
    have h := tropicalCasoratian_eq_add_of_coordinateShift f
      (fun i ↦ a i * (x + S)) (-S) x (by
        intro i k
        have hk : ((k : ℕ) : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_lt_succ k.isLt)
        have hbase : -S + (k : ℕ) < -R := by dsimp [S]; linarith
        have hnext : x + (k : ℕ) < -R := by linarith
        rw [hleft i _ hbase, hleft i _ hnext]
        ring)
    rw [h, ← Finset.sum_mul]
    ring
  · intro x hx
    have h := tropicalCasoratian_eq_add_of_coordinateShift f
      (fun i ↦ b i * (x - S)) S x (by
        intro i k
        have hk : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := by positivity
        have hm : (0 : ℝ) ≤ m := by positivity
        have hbase : R < S + (k : ℕ) := by dsimp [S]; linarith
        have hnext : R < x + (k : ℕ) := by linarith
        rw [hright i _ hbase, hright i _ hnext]
        ring)
    rw [h, ← Finset.sum_mul]
    ring


/-- Finite first-order root data for one tropical meromorphic function.

`leftSlope` and `rightSlope` are the two eventual affine slopes in Section 6.
The slope-jump identity is *not* a field: it is proved below from Jensen's
formula, entirety, and the two affine tails. -/
structure FiniteFirstOrderRootData {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) where
  order_le_one : n ≤ 1
  entire : IsTropicalEntire f
  roots : Finset ℝ
  roots_exact : ∀ x, x ∈ roots ↔ IsJthRoot f 1 x
  cutoff : ℝ
  cutoff_pos : 0 < cutoff
  root_abs_lt_cutoff : ∀ x ∈ roots, |x| < cutoff
  leftSlope : ℝ
  rightSlope : ℝ
  leftIntercept : ℝ
  rightIntercept : ℝ
  left_affine : ∀ x, x < -cutoff → f x = leftSlope * x + leftIntercept
  right_affine : ∀ x, cutoff < x → f x = rightSlope * x + rightIntercept

namespace FiniteFirstOrderRootData

/-- Construct the finite-root data directly from the paper's assumptions,
without requiring affine tails or nonempty roots as extra hypotheses. -/
def ofFiniteRoots {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (hn : n ≤ 1) (hf : IsTropicalEntire f)
    (hfinite : {x : ℝ | IsJthRoot f 1 x}.Finite) : FiniteFirstOrderRootData f := by
  classical
  apply Classical.choice
  obtain ⟨R, hR, a, b, u, v, hbound, hleft, hright⟩ :=
    exists_affine_tails_of_finite_firstOrder_roots f hn hf hfinite
  exact ⟨{
    order_le_one := hn
    entire := hf
    roots := hfinite.toFinset
    roots_exact := fun x ↦ hfinite.mem_toFinset
    cutoff := R
    cutoff_pos := hR
    root_abs_lt_cutoff := fun x hx ↦ hbound x (hfinite.mem_toFinset.mp hx)
    leftSlope := a
    rightSlope := b
    leftIntercept := u
    rightIntercept := v
    left_affine := hleft
    right_affine := hright }⟩

/-- Half the total first-order multiplicity, the coefficient of `r`. -/
def linearCoefficient {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (D : FiniteFirstOrderRootData f) : ℝ :=
  (D.rightSlope - D.leftSlope) / 2

/-- The constant weighted absolute first moment of the finite roots. -/
def rootMoment {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (D : FiniteFirstOrderRootData f) : ℝ :=
  (1 / 2) * ∑ x ∈ D.roots, rootOrPoleMultiplicity f 1 x * |x|

theorem jthRootPoints_eq_roots {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (D : FiniteFirstOrderRootData f) {r : ℝ} (hr : D.cutoff < r) :
    jthRootPoints f 1 r = D.roots := by
  classical
  ext x
  simp only [mem_jthRootPoints_iff]
  constructor
  · rintro ⟨_, hxroot⟩
    exact (D.roots_exact x).2 hxroot
  · intro hx
    have habs : |x| < r := (D.root_abs_lt_cutoff x hx).trans hr
    exact ⟨(abs_lt.mp habs), (D.roots_exact x).1 hx⟩

private theorem integratedRootCounting_eq_mass_affine
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (D : FiniteFirstOrderRootData f) {r : ℝ} (hr : D.cutoff < r) :
    integratedRootCounting 1 r f =
      (1 / 2) * (∑ x ∈ D.roots, rootOrPoleMultiplicity f 1 x) * r -
        D.rootMoment := by
  classical
  rw [integratedRootCounting, D.jthRootPoints_eq_roots hr]
  simp only [pow_one, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [rootMoment]
  ring

private theorem integratedCounting_eq_zero
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (D : FiniteFirstOrderRootData f) (r : ℝ) :
    integratedCounting 1 r f = 0 := by
  exact integratedCounting_eq_zero_of_entire_any_order f D.entire (by omega) r

private theorem integratedRootCounting_eq_endpointMean_sub
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (D : FiniteFirstOrderRootData f) {r : ℝ} (hr : 0 < r) :
    integratedRootCounting 1 r f = (f r + f (-r)) / 2 - f 0 := by
  have hmean := sum_integratedRootCounting_eq_endpointMean_sub f D.entire hr
  have hext := sum_integratedRootCounting_eq_of_order_le f D.order_le_one r
  norm_num at hext
  exact hext.trans hmean

/-- The finite jump identity used without proof in the source's calculation:
the total first-order root multiplicity equals the difference of the two tail
slopes. -/
theorem totalMultiplicity_eq_slopeJump
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (D : FiniteFirstOrderRootData f) :
    (∑ x ∈ D.roots, rootOrPoleMultiplicity f 1 x) =
      D.rightSlope - D.leftSlope := by
  let r₀ : ℝ := D.cutoff + 1
  let r₁ : ℝ := D.cutoff + 2
  have hr₀ : D.cutoff < r₀ := by simp [r₀]
  have hr₁ : D.cutoff < r₁ := by simp [r₁]
  have hr₀pos : 0 < r₀ := lt_trans D.cutoff_pos hr₀
  have hr₁pos : 0 < r₁ := lt_trans D.cutoff_pos hr₁
  have hcount₀ := D.integratedRootCounting_eq_mass_affine hr₀
  have hcount₁ := D.integratedRootCounting_eq_mass_affine hr₁
  have hj₀ := D.integratedRootCounting_eq_endpointMean_sub hr₀pos
  have hj₁ := D.integratedRootCounting_eq_endpointMean_sub hr₁pos
  have hright₀ := D.right_affine r₀ hr₀
  have hright₁ := D.right_affine r₁ hr₁
  have hleft₀ := D.left_affine (-r₀) (by linarith)
  have hleft₁ := D.left_affine (-r₁) (by linarith)
  rw [hcount₀, hright₀, hleft₀] at hj₀
  rw [hcount₁, hright₁, hleft₁] at hj₁
  dsimp [r₀, r₁] at hj₀ hj₁
  linarith

/-- Strong form of the finite-root estimate used at the beginning of Section
6: beyond the last root the integrated count is exactly affine, not merely
affine up to `O(1)`. -/
theorem integratedRootCounting_eq_affine
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (D : FiniteFirstOrderRootData f) {r : ℝ} (hr : D.cutoff < r) :
    integratedRootCounting 1 r f = D.linearCoefficient * r - D.rootMoment := by
  classical
  rw [D.integratedRootCounting_eq_mass_affine hr]
  rw [D.totalMultiplicity_eq_slopeJump]
  simp only [linearCoefficient, rootMoment]
  ring

theorem integratedRootCounting_eventually_eq_affine
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (D : FiniteFirstOrderRootData f) :
    (fun r ↦ integratedRootCounting 1 r f) =ᶠ[atTop]
      fun r ↦ D.linearCoefficient * r - D.rootMoment := by
  filter_upwards [eventually_gt_atTop D.cutoff] with r hr
  exact D.integratedRootCounting_eq_affine hr

theorem linearCoefficient_nonneg {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (D : FiniteFirstOrderRootData f) : 0 ≤ D.linearCoefficient := by
  have hsum : 0 ≤ ∑ x ∈ D.roots, rootOrPoleMultiplicity f 1 x :=
    Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  rw [D.totalMultiplicity_eq_slopeJump] at hsum
  exact div_nonneg hsum (by norm_num)

/-- Zero total root mass means that there are no roots, including when the
function itself has exact order zero. -/
theorem roots_eq_empty_of_linearCoefficient_eq_zero
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (D : FiniteFirstOrderRootData f) (hz : D.linearCoefficient = 0) : D.roots = ∅ := by
  classical
  have hsum : (∑ x ∈ D.roots, rootOrPoleMultiplicity f 1 x) = 0 := by
    rw [D.totalMultiplicity_eq_slopeJump]
    dsimp [linearCoefficient] at hz
    linarith
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun y (_ : y ∈ D.roots) ↦ abs_nonneg (multiplicity f 1 y))).mp hsum x hx
  have hroot : 0 < multiplicity f 1 x := (D.roots_exact x).mp hx
  exact (ne_of_gt (abs_pos.mpr (ne_of_gt hroot))) hzero

theorem integratedRootCounting_eq_zero_of_linearCoefficient_eq_zero
    {n : ℕ} {f : NthTropicalMeromorphicFunction n}
    (D : FiniteFirstOrderRootData f) (hz : D.linearCoefficient = 0) (r : ℝ) :
    integratedRootCounting 1 r f = 0 := by
  classical
  have hempty := D.roots_eq_empty_of_linearCoefficient_eq_zero hz
  have hpoints : jthRootPoints f 1 r = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hroot := (mem_jthRootPoints_iff.mp hx).2
    have hm := (D.roots_exact x).mpr hroot
    simpa [hempty] using hm
  simp [integratedRootCounting, hpoints]

end FiniteFirstOrderRootData

/-- The finite-root Section 6 data for all coordinates and their tropical
Casoratian.  Orders may be zero and root sets may be empty. The tail-slope identity is
proved below; no positive total root multiplicity is assumed. -/
structure FiniteRootCasoratianData (m : ℕ) where
  coordinateOrder : Fin (m + 1) → ℕ
  coordinate : ∀ i, NthTropicalMeromorphicFunction (coordinateOrder i)
  casoratianOrder : ℕ
  casoratian : NthTropicalMeromorphicFunction casoratianOrder
  coordinateRoots : ∀ i, FiniteFirstOrderRootData (coordinate i)
  casoratianRoots : FiniteFirstOrderRootData casoratian
  casoratian_eq : ∀ x,
    casoratian x = tropicalCasoratian (fun i y ↦ coordinate i y) x

namespace FiniteRootCasoratianData

def coordinateCutoffMaximum {m : ℕ} (D : FiniteRootCasoratianData m) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i ↦ (D.coordinateRoots i).cutoff

theorem coordinate_cutoff_le_maximum {m : ℕ} (D : FiniteRootCasoratianData m)
    (i : Fin (m + 1)) :
    (D.coordinateRoots i).cutoff ≤ D.coordinateCutoffMaximum := by
  exact Finset.le_sup' (fun k ↦ (D.coordinateRoots k).cutoff)
    (Finset.mem_univ i)

private def tailRadius {m : ℕ} (D : FiniteRootCasoratianData m) : ℝ :=
  max D.casoratianRoots.cutoff D.coordinateCutoffMaximum + (m + 2 : ℕ)

/-- The tail-slope computation suppressed in the source: on either tail all
permutation summands have the same slope, so their finite maximum has the sum
of the coordinate slopes. -/
theorem casoratianSlopeJump {m : ℕ} (D : FiniteRootCasoratianData m) :
    D.casoratianRoots.rightSlope - D.casoratianRoots.leftSlope =
      ∑ i, ((D.coordinateRoots i).rightSlope -
        (D.coordinateRoots i).leftSlope) := by
  classical
  let R : ℝ := D.tailRadius
  have hRcoord (i : Fin (m + 1)) : (D.coordinateRoots i).cutoff < R := by
    have hi := D.coordinate_cutoff_le_maximum i
    have hmax : D.coordinateCutoffMaximum ≤
        max D.casoratianRoots.cutoff D.coordinateCutoffMaximum := le_max_right _ _
    have hpos : (0 : ℝ) < (m + 2 : ℕ) := by positivity
    dsimp [R, tailRadius]
    linarith
  have hRcas : D.casoratianRoots.cutoff < R := by
    have hmax : D.casoratianRoots.cutoff ≤
        max D.casoratianRoots.cutoff D.coordinateCutoffMaximum := le_max_left _ _
    have hpos : (0 : ℝ) < (m + 2 : ℕ) := by positivity
    dsimp [R, tailRadius]
    linarith
  have hright := tropicalCasoratian_eq_add_of_coordinateShift
    (fun i y ↦ D.coordinate i y)
    (fun i ↦ (D.coordinateRoots i).rightSlope) R (R + 1) (by
      intro i k
      have hk : (0 : ℝ) ≤ (k : ℕ) := by positivity
      have h0 := (D.coordinateRoots i).right_affine (R + (k : ℕ)) (by
        linarith [hRcoord i])
      have h1 := (D.coordinateRoots i).right_affine (R + 1 + (k : ℕ)) (by
        linarith [hRcoord i])
      rw [h1, h0]
      ring)
  rw [← D.casoratian_eq (R + 1), ← D.casoratian_eq R] at hright
  have hCright0 := D.casoratianRoots.right_affine R hRcas
  have hCright1 := D.casoratianRoots.right_affine (R + 1) (by linarith)
  rw [hCright1, hCright0] at hright
  have hrightSlope : D.casoratianRoots.rightSlope =
      ∑ i, (D.coordinateRoots i).rightSlope := by
    linarith
  have hleft := tropicalCasoratian_eq_add_of_coordinateShift
    (fun i y ↦ D.coordinate i y)
    (fun i ↦ (D.coordinateRoots i).leftSlope) (-R - 1) (-R) (by
      intro i k
      have hkNat : (k : ℕ) ≤ m := by omega
      have hk : ((k : ℕ) : ℝ) ≤ m := by exact_mod_cast hkNat
      have hi := D.coordinate_cutoff_le_maximum i
      have hmax : D.coordinateCutoffMaximum ≤
          max D.casoratianRoots.cutoff D.coordinateCutoffMaximum := le_max_right _ _
      have hy : -R + (k : ℕ) < -(D.coordinateRoots i).cutoff := by
        dsimp [R, tailRadius]
        norm_num [Nat.cast_add, Nat.cast_ofNat]
        linarith [hi, hmax, hk]
      have hx : -R - 1 + (k : ℕ) < -(D.coordinateRoots i).cutoff := by
        linarith
      have h0 := (D.coordinateRoots i).left_affine (-R - 1 + (k : ℕ)) hx
      have h1 := (D.coordinateRoots i).left_affine (-R + (k : ℕ)) hy
      rw [h1, h0]
      ring)
  rw [← D.casoratian_eq (-R), ← D.casoratian_eq (-R - 1)] at hleft
  have hCleft0 := D.casoratianRoots.left_affine (-R - 1) (by linarith)
  have hCleft1 := D.casoratianRoots.left_affine (-R) (by linarith)
  rw [hCleft1, hCleft0] at hleft
  have hleftSlope : D.casoratianRoots.leftSlope =
      ∑ i, (D.coordinateRoots i).leftSlope := by
    linarith
  rw [hrightSlope, hleftSlope, Finset.sum_sub_distrib]

def coordinateCountingSum {m : ℕ} (D : FiniteRootCasoratianData m) (r : ℝ) : ℝ :=
  ∑ i, integratedRootCounting 1 r (D.coordinate i)

def casoratianCounting {m : ℕ} (D : FiniteRootCasoratianData m) (r : ℝ) : ℝ :=
  integratedRootCounting 1 r D.casoratian

def totalLinearCoefficient {m : ℕ} (D : FiniteRootCasoratianData m) : ℝ :=
  ∑ i, (D.coordinateRoots i).linearCoefficient

def coordinateRootMomentSum {m : ℕ} (D : FiniteRootCasoratianData m) : ℝ :=
  ∑ i, (D.coordinateRoots i).rootMoment

private theorem eventuallyEq_finset_sum
    {I : Type*} [DecidableEq I] {s : Finset I}
    (u v : I → ℝ → ℝ) (h : ∀ i ∈ s, u i =ᶠ[atTop] v i) :
    (fun x ↦ ∑ i ∈ s, u i x) =ᶠ[atTop] fun x ↦ ∑ i ∈ s, v i x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      filter_upwards [h a (Finset.mem_insert_self a s),
        ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi))] with x hax hsx
      simp [ha, hax, hsx]

theorem coordinateCountingSum_eventually_eq_affine
    {m : ℕ} (D : FiniteRootCasoratianData m) :
    D.coordinateCountingSum =ᶠ[atTop]
      fun r ↦ D.totalLinearCoefficient * r - D.coordinateRootMomentSum := by
  classical
  have hsum := eventuallyEq_finset_sum
    (fun i r ↦ integratedRootCounting 1 r (D.coordinate i))
    (fun i r ↦ (D.coordinateRoots i).linearCoefficient * r -
      (D.coordinateRoots i).rootMoment)
    (s := Finset.univ)
    (fun i _ ↦ (D.coordinateRoots i).integratedRootCounting_eventually_eq_affine)
  filter_upwards [hsum] with r hr
  simpa [coordinateCountingSum, totalLinearCoefficient,
    coordinateRootMomentSum, Finset.sum_sub_distrib, Finset.sum_mul] using hr

theorem casoratian_linearCoefficient_eq_total
    {m : ℕ} (D : FiniteRootCasoratianData m) :
    D.casoratianRoots.linearCoefficient = D.totalLinearCoefficient := by
  simp only [FiniteFirstOrderRootData.linearCoefficient, totalLinearCoefficient]
  rw [D.casoratianSlopeJump]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]

theorem casoratianCounting_eventually_eq_affine
    {m : ℕ} (D : FiniteRootCasoratianData m) :
    D.casoratianCounting =ᶠ[atTop]
      fun r ↦ D.totalLinearCoefficient * r - D.casoratianRoots.rootMoment := by
  filter_upwards [D.casoratianRoots.integratedRootCounting_eventually_eq_affine]
    with r hr
  rw [casoratianCounting, hr]
  rw [D.casoratian_linearCoefficient_eq_total]

/-- Strong additive version of the Section 6 conclusion: after all roots have
entered the radial interval, the Casoratian count minus the sum of coordinate
counts is one fixed constant. -/
theorem countingDifference_eventually_constant
    {m : ℕ} (D : FiniteRootCasoratianData m) :
    (fun r ↦ D.casoratianCounting r - D.coordinateCountingSum r) =ᶠ[atTop]
      fun _ ↦ D.coordinateRootMomentSum - D.casoratianRoots.rootMoment := by
  filter_upwards [D.casoratianCounting_eventually_eq_affine,
    D.coordinateCountingSum_eventually_eq_affine] with r hC hF
  rw [hC, hF]
  ring

/-- The paper's additive `O(1)` estimate, valid also when there are no roots. -/
theorem countingDifference_isBigO_one
    {m : ℕ} (D : FiniteRootCasoratianData m) :
    (fun r ↦ D.casoratianCounting r - D.coordinateCountingSum r) =O[atTop]
      (fun _ : ℝ ↦ (1 : ℝ)) := by
  apply IsBigO.of_bound |D.coordinateRootMomentSum - D.casoratianRoots.rootMoment|
  filter_upwards [D.countingDifference_eventually_constant] with r hr
  simp [hr, Real.norm_eq_abs]

/-- The important equality extracted from the beginning of Section 6:
`N(r,-C₀) = (∑ᵢ N(r,-fᵢ))(1+o(1))`, expressed by Mathlib's standard
asymptotic-equivalence relation. -/
theorem casoratianCounting_isEquivalent_coordinateCountingSum
    {m : ℕ} (D : FiniteRootCasoratianData m) :
    D.casoratianCounting ~[atTop] D.coordinateCountingSum := by
  have hnonneg : ∀ i, 0 ≤ (D.coordinateRoots i).linearCoefficient :=
    fun i ↦ (D.coordinateRoots i).linearCoefficient_nonneg
  have ha0 : 0 ≤ D.totalLinearCoefficient := Finset.sum_nonneg (fun i _ ↦ hnonneg i)
  rcases eq_or_lt_of_le ha0 with hz | ha
  · have hi : ∀ i, (D.coordinateRoots i).linearCoefficient = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hnonneg j)).mp
        hz.symm i (Finset.mem_univ i)
    have hC : D.casoratianRoots.linearCoefficient = 0 :=
      D.casoratian_linearCoefficient_eq_total.trans hz.symm
    have hcounts : D.casoratianCounting = D.coordinateCountingSum := by
      funext r
      dsimp [casoratianCounting, coordinateCountingSum]
      rw [D.casoratianRoots.integratedRootCounting_eq_zero_of_linearCoefficient_eq_zero hC]
      symm
      exact Finset.sum_eq_zero (fun i _ ↦
        (D.coordinateRoots i).integratedRootCounting_eq_zero_of_linearCoefficient_eq_zero (hi i) r)
    rw [hcounts]
  · let L : ℝ → ℝ := fun r ↦ D.totalLinearCoefficient * r
    have hLtop : Tendsto L atTop atTop := by
      simpa [L, mul_comm] using tendsto_id.const_mul_atTop ha
    have hLnorm : Tendsto (norm ∘ L) atTop atTop := by
      simpa [Function.comp_def, Real.norm_eq_abs] using
        tendsto_abs_atTop_atTop.comp hLtop
    have hCasLinear :
        (fun r ↦ L r - D.casoratianRoots.rootMoment) ~[atTop] L := by
      simpa [sub_eq_add_neg] using
        (IsEquivalent.refl.add_const_of_norm_tendsto_atTop hLnorm
          (c := -D.casoratianRoots.rootMoment))
    have hCoordLinear :
        (fun r ↦ L r - D.coordinateRootMomentSum) ~[atTop] L := by
      simpa [sub_eq_add_neg] using
        (IsEquivalent.refl.add_const_of_norm_tendsto_atTop hLnorm
          (c := -D.coordinateRootMomentSum))
    have hCas : D.casoratianCounting ~[atTop] L :=
      hCasLinear.congr_left (by
        simpa [L] using D.casoratianCounting_eventually_eq_affine.symm)
    have hCoord : D.coordinateCountingSum ~[atTop] L :=
      hCoordLinear.congr_left (by
        simpa [L] using D.coordinateCountingSum_eventually_eq_affine.symm)
    exact hCas.trans hCoord.symm

end FiniteRootCasoratianData

end

end NthTropicalNevanlinna
