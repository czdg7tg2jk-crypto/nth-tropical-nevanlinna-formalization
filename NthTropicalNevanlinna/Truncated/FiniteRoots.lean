import NthTropicalNevanlinna.Truncated.Casoratian
import NthTropicalNevanlinna.Nevanlinna.Jensen
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# The finite-root first-order Casoratian identity

The beginning of Section 6 assumes that every coordinate has finitely many
first-order roots.  We package exactly that finite data and prove an eventual
affine formula for its integrated root count.  Applied to the coordinates and
their Casoratian, this yields an eventually constant counting difference and
therefore the paper's multiplicative `1 + o(1)` conclusion.
-/

namespace NthTropicalNevanlinna

noncomputable section

open Filter Function Set
open scoped BigOperators Topology
open Asymptotics

/-- Finite first-order root data for one tropical meromorphic function.

`leftSlope` and `rightSlope` are the two eventual affine slopes in Section 6.
The slope-jump identity is *not* a field: it is proved below from Jensen's
formula, entirety, and the two affine tails. -/
structure FiniteFirstOrderRootData
    (f : NthTropicalMeromorphicFunction 1) where
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

/-- Half the total first-order multiplicity, the coefficient of `r`. -/
def linearCoefficient {f : NthTropicalMeromorphicFunction 1}
    (D : FiniteFirstOrderRootData f) : ℝ :=
  (D.rightSlope - D.leftSlope) / 2

/-- The constant weighted absolute first moment of the finite roots. -/
def rootMoment {f : NthTropicalMeromorphicFunction 1}
    (D : FiniteFirstOrderRootData f) : ℝ :=
  (1 / 2) * ∑ x ∈ D.roots, rootOrPoleMultiplicity f 1 x * |x|

theorem jthRootPoints_eq_roots {f : NthTropicalMeromorphicFunction 1}
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
    {f : NthTropicalMeromorphicFunction 1}
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
    {f : NthTropicalMeromorphicFunction 1}
    (D : FiniteFirstOrderRootData f) (r : ℝ) :
    integratedCounting 1 r f = 0 := by
  classical
  have hpoles : jthPolePoints f 1 r = ∅ := by
    ext x
    simp only [mem_jthPolePoints_iff]
    constructor
    · rintro ⟨_, hxPole⟩
      exfalso
      have hxNonneg := (isTropicalEntire_iff_multiplicity_nonneg f).mp
        D.entire x 1 (by simp) (by simp)
      exact (not_lt_of_ge hxNonneg) hxPole
    · intro hx
      simp at hx
  simp [integratedCounting, hpoles]

private theorem integratedRootCounting_eq_endpointMean_sub
    {f : NthTropicalMeromorphicFunction 1}
    (D : FiniteFirstOrderRootData f) {r : ℝ} (hr : 0 < r) :
    integratedRootCounting 1 r f = (f r + f (-r)) / 2 - f 0 := by
  have hj := jensenFormula f hr
  rw [jensenRootMultiplicitySum_eq f hr,
    jensenPoleMultiplicitySum_eq f hr] at hj
  have hpole := D.integratedCounting_eq_zero r
  norm_num [hpole] at hj
  linarith

/-- The finite jump identity used without proof in the source's calculation:
the total first-order root multiplicity equals the difference of the two tail
slopes. -/
theorem totalMultiplicity_eq_slopeJump
    {f : NthTropicalMeromorphicFunction 1}
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
    {f : NthTropicalMeromorphicFunction 1}
    (D : FiniteFirstOrderRootData f) {r : ℝ} (hr : D.cutoff < r) :
    integratedRootCounting 1 r f = D.linearCoefficient * r - D.rootMoment := by
  classical
  rw [D.integratedRootCounting_eq_mass_affine hr]
  rw [D.totalMultiplicity_eq_slopeJump]
  simp only [linearCoefficient, rootMoment]
  ring

theorem integratedRootCounting_eventually_eq_affine
    {f : NthTropicalMeromorphicFunction 1}
    (D : FiniteFirstOrderRootData f) :
    (fun r ↦ integratedRootCounting 1 r f) =ᶠ[atTop]
      fun r ↦ D.linearCoefficient * r - D.rootMoment := by
  filter_upwards [eventually_gt_atTop D.cutoff] with r hr
  exact D.integratedRootCounting_eq_affine hr

end FiniteFirstOrderRootData

/-- The finite-root Section 6 data for all coordinates and their tropical
Casoratian.  `casoratianSlopeJump` records the tail-slope computation made in
the paper; the positivity hypothesis is the nonconstant-curve input. -/
structure FiniteRootCasoratianData (m : ℕ) where
  coordinate : Fin (m + 1) → NthTropicalMeromorphicFunction 1
  casoratian : NthTropicalMeromorphicFunction 1
  coordinateRoots : ∀ i, FiniteFirstOrderRootData (coordinate i)
  casoratianRoots : FiniteFirstOrderRootData casoratian
  casoratian_eq : ∀ x,
    casoratian x = tropicalCasoratian (fun i y ↦ coordinate i y) x
  totalSlopeJump_pos :
    0 < ∑ i, ((coordinateRoots i).rightSlope - (coordinateRoots i).leftSlope)

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

/-- The important equality extracted from the beginning of Section 6:
`N(r,C₀) = (∑ᵢ N(r,fᵢ))(1+o(1))`, expressed by Mathlib's standard
asymptotic-equivalence relation. -/
theorem casoratianCounting_isEquivalent_coordinateCountingSum
    {m : ℕ} (D : FiniteRootCasoratianData m) :
    D.casoratianCounting ~[atTop] D.coordinateCountingSum := by
  have ha : 0 < D.totalLinearCoefficient := by
    have hcoeff : D.totalLinearCoefficient =
        (1 / 2) * ∑ i,
          ((D.coordinateRoots i).rightSlope - (D.coordinateRoots i).leftSlope) := by
      simp only [totalLinearCoefficient,
        FiniteFirstOrderRootData.linearCoefficient, div_eq_mul_inv]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hcoeff]
    nlinarith [D.totalSlopeJump_pos]
  let L : ℝ → ℝ := fun r ↦ D.totalLinearCoefficient * r
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
