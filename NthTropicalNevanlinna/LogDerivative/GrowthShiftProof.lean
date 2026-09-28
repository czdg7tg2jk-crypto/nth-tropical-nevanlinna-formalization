import NthTropicalNevanlinna.LogDerivative.ShiftEstimate
import NthTropicalNevanlinna.Nevanlinna.Growth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Filter MeasureTheory Set
open scoped Topology Interval

/-!
# The growth-shift lemma

This file proves Lemma 4.6 in the refined numbering (Lemma 4.5 in the
source).  The proof uses exponential annuli to make the exceptional-set
argument fully measure-theoretic.
-/

namespace NthTropicalNevanlinna

noncomputable section

/-- The paper's exceptional-set condition
`∫_{E ∩ (1,∞)} dr/r < ∞`. -/
def HasFiniteLogarithmicMeasure (E : Set ℝ) : Prop :=
  IntegrableOn (fun r : ℝ ↦ 1 / r) (E ∩ Set.Ioi 1)

/-- The filter describing `r → ∞` while `r` stays outside `E`. -/
def atTopOutside (E : Set ℝ) : Filter ℝ :=
  Filter.atTop ⊓ Filter.principal Eᶜ

/-- Finite logarithmic measure is stable under finite unions. -/
theorem HasFiniteLogarithmicMeasure.union {E F : Set ℝ}
    (hE : HasFiniteLogarithmicMeasure E)
    (hF : HasFiniteLogarithmicMeasure F) :
    HasFiniteLogarithmicMeasure (E ∪ F) := by
  unfold HasFiniteLogarithmicMeasure at hE hF ⊢
  rw [Set.union_inter_distrib_right]
  exact hE.union hF

/-- A finite union of exceptional sets still has finite logarithmic
measure. -/
theorem hasFiniteLogarithmicMeasure_finset_biUnion
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (E : ι → Set ℝ)
    (hE : ∀ i ∈ s, HasFiniteLogarithmicMeasure (E i)) :
    HasFiniteLogarithmicMeasure (⋃ i ∈ s, E i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [HasFiniteLogarithmicMeasure]
  | @insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact (hE i (Finset.mem_insert_self i s)).union
        (ih fun j hj ↦ hE j (Finset.mem_insert_of_mem hj))

/-- Enlarging the exceptional set makes the outside filter smaller. -/
theorem atTopOutside_mono {E F : Set ℝ} (hEF : E ⊆ F) :
    atTopOutside F ≤ atTopOutside E := by
  unfold atTopOutside
  exact inf_le_inf_left _ (Filter.principal_mono.mpr (compl_subset_compl.mpr hEF))

/-- A little-o estimate remains valid after enlarging its exceptional set. -/
theorem Asymptotics.IsLittleO.mono_atTopOutside
    {E F : Set ℝ} {u v : ℝ → ℝ}
    (h : u =o[atTopOutside E] v) (hEF : E ⊆ F) :
    u =o[atTopOutside F] v :=
  h.mono (atTopOutside_mono hEF)

/-- The quotient whose limsup is the hyper-order of a growth function. -/
def growthFunctionHyperOrderQuotient (T : ℝ → ℝ) (r : ℝ) : EReal :=
  ((Real.log (Real.log (T r)) / Real.log r : ℝ) : EReal)

/-- Hyper-order of an abstract growth function. -/
def growthFunctionHyperOrder (T : ℝ → ℝ) : EReal :=
  Filter.limsup (growthFunctionHyperOrderQuotient T) Filter.atTop

/-- The exact quantified statement of refined Lemma 4.6.  A function on
`[0, ∞)` is represented by an ambient real function whose hypotheses are
restricted to `Set.Ici 0`; values on the negative half-line are irrelevant. -/
def GrowthShiftLemmaStatement : Prop :=
  ∀ (T : ℝ → ℝ) (c rho2 σ : ℝ),
    MonotoneOn T (Set.Ici 0) → ContinuousOn T (Set.Ici 0) →
    (∀ r, 0 ≤ r → 0 ≤ T r) →
    0 < c →
    growthFunctionHyperOrder T = (rho2 : EReal) →
    rho2 < 1 → 0 < σ → σ < 1 - rho2 →
    ∃ E : Set ℝ,
      HasFiniteLogarithmicMeasure E ∧
        (fun r ↦ T (r + c) - T r) =o[atTopOutside E]
          (fun r ↦ T r / r ^ σ)

private lemma exp_nat_cover (R x : ℝ) (hR : 0 < R) (hx : R ≤ x) :
    ∃ n : ℕ, x ∈ Set.Icc (R * Real.exp n) (R * Real.exp (n + 1)) := by
  let P : ℕ → Prop := fun n => x ≤ R * Real.exp (n + 1)
  have hP : ∃ n, P n := by
    obtain ⟨N, hN⟩ := exists_nat_gt (Real.log (x / R))
    refine ⟨N, ?_⟩
    have hratio : 0 < x / R := div_pos (lt_of_lt_of_le hR hx) hR
    have hexp : x / R < Real.exp (N : ℝ) := by
      rw [← Real.exp_log hratio]
      exact Real.exp_lt_exp.mpr hN
    have hNle : (N : ℝ) ≤ N + 1 := by norm_num
    have hexp_le := Real.exp_le_exp.mpr hNle
    dsimp [P]
    rw [mul_comm, ← div_le_iff₀ hR]
    exact le_trans (le_of_lt hexp) hexp_le
  let n := Nat.find hP
  refine ⟨n, ?_, Nat.find_spec hP⟩
  by_cases hn : n = 0
  · simpa [n, hn] using hx
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hnot : ¬ P k := Nat.find_min hP (by simp [n, hk])
    dsimp [P] at hnot
    simp only [not_le] at hnot
    simpa [n, hk] using le_of_lt hnot

open scoped ENNReal

private lemma finite_log_measure_of_exp_blocks
    (F : Set ℝ) (U : ℝ → ℝ) (c k tau alpha A R : ℝ)
    (hc : 0 < c) (hk : 0 < k) (htau : 0 < tau)
    (hp : tau + alpha < 1)
    (hA : 0 ≤ A) (hR1 : 1 ≤ R) (hRc : c ≤ R)
    (hFmeas : MeasurableSet F) (hF : F ⊆ Ici R)
    (hUmono : Monotone U)
    (hUbound : ∀ x, R ≤ x → |U x| ≤ A * x ^ alpha)
    (hbad : ∀ x ∈ F, k / x ^ tau ≤ slope U x (x + c)) :
    IntegrableOn (fun x : ℝ => 1 / x) F := by
  let a : ℕ → ℝ := fun n => R * Real.exp n
  let b : ℕ → ℝ := fun n => R * Real.exp (n + 1)
  let S : ℕ → Set ℝ := fun n => F ∩ Icc (a n) (b n)
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have ha_pos (n : ℕ) : 0 < a n := mul_pos hR (Real.exp_pos _)
  have hab (n : ℕ) : a n ≤ b n := by
    dsimp [a, b]
    gcongr
    exact_mod_cast (Nat.le_add_right n 1)
  have hbRc (n : ℕ) : R ≤ b n + c := by
    have : R ≤ b n := by
      dsimp [b]
      rw [le_mul_iff_one_le_right hR]
      exact Real.one_le_exp (by positivity)
    linarith
  have hcover : F ⊆ ⋃ n, S n := by
    intro x hx
    obtain ⟨n, hn⟩ := exp_nat_cover R x hR (hF hx)
    exact mem_iUnion.2 ⟨n, hx, hn⟩
  have hInt (n : ℕ) : IntegrableOn (fun x : ℝ => 1 / x) (S n) := by
    have hcont : ContinuousOn (fun x : ℝ => 1 / x) (Icc (a n) (b n)) := by
      intro x hx
      exact (continuousAt_const.div continuousAt_id
        (ne_of_gt ((ha_pos n).trans_le hx.1))).continuousWithinAt
    exact (hcont.integrableOn_compact isCompact_Icc).mono_set inter_subset_right
  apply (integrableOn_iUnion_of_summable_integral_norm hInt ?_).mono_set hcover
  let p : ℝ := tau + alpha - 1
  let q : ℝ := Real.exp p
  have hpneg : p < 0 := by dsimp [p]; linarith
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by simpa [q] using Real.exp_lt_one_iff.mpr hpneg
  have hqsum : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  let C : ℝ :=
    (2 * A / k) * (Real.exp 1) ^ tau *
      (Real.exp 1 + 1) ^ |alpha| * R ^ p
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) ?_ (hqsum.mul_left C)
  intro n
  have haR : R ≤ a n := by
    dsimp [a]
    rw [le_mul_iff_one_le_right hR]
    exact Real.one_le_exp (by positivity)
  have hbpos : 0 < b n := lt_of_lt_of_le (ha_pos n) (hab n)
  have hUmonoOn : MonotoneOn U (Icc (a n) (b n + c)) := hUmono.monotoneOn _
  have hSlopeInt : IntervalIntegrable (fun x => slope U x (x + c)) volume (a n) (b n) :=
    hUmonoOn.intervalIntegrable_slope (hab n) hc.le
  have hSlopeNonneg : ∀ x ∈ Icc (a n) (b n), 0 ≤ slope U x (x + c) := by
    intro x hx
    rw [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hc.le)
      (sub_nonneg.mpr (hUmono (le_add_of_nonneg_right hc.le)))
  have hSlopeNonnegAll : ∀ x, 0 ≤ slope U x (x + c) := by
    intro x
    rw [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hc.le)
      (sub_nonneg.mpr (hUmono (le_add_of_nonneg_right hc.le)))
  have hpoint : ∀ x ∈ S n,
      ‖1 / x‖ ≤ (b n ^ tau / (k * a n)) * slope U x (x + c) := by
    intro x hx
    have hax : a n ≤ x := hx.2.1
    have hxb : x ≤ b n := hx.2.2
    have hxpos : 0 < x := (ha_pos n).trans_le hax
    have hxpow : 0 < x ^ tau := Real.rpow_pos_of_pos hxpos _
    have hbpow : x ^ tau ≤ b n ^ tau :=
      Real.rpow_le_rpow hxpos.le hxb htau.le
    have hs := hbad x hx.1
    have hcoeff : 0 ≤ x ^ tau / (k * x) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hs hcoeff
    have hid : (x ^ tau / (k * x)) * (k / x ^ tau) = 1 / x := by
      field_simp
    rw [hid] at hmul
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hxpos)]
    refine hmul.trans ?_
    have hsnonneg : 0 ≤ slope U x (x + c) := le_trans (by positivity) hs
    apply mul_le_mul_of_nonneg_right _ hsnonneg
    rw [div_eq_mul_inv, div_eq_mul_inv]
    gcongr
  have hOneInt : IntegrableOn (fun x : ℝ => ‖1 / x‖) (S n) := (hInt n).norm
  have hSlopeSetInt : IntegrableOn (fun x => slope U x (x + c)) (S n) :=
    ((integrableOn_Icc_iff_integrableOn_Ioc).2 hSlopeInt.1).mono_set inter_subset_right
  have hScaledInt : IntegrableOn
      (fun x => (b n ^ tau / (k * a n)) * slope U x (x + c)) (S n) :=
    hSlopeSetInt.const_mul _
  calc
    (∫ x in S n, ‖1 / x‖) ≤
        ∫ x in S n, (b n ^ tau / (k * a n)) * slope U x (x + c) :=
      setIntegral_mono_on hOneInt hScaledInt
        (hFmeas.inter measurableSet_Icc) hpoint
    _ = (b n ^ tau / (k * a n)) *
          ∫ x in S n, slope U x (x + c) := by rw [← integral_const_mul]
    _ ≤ (b n ^ tau / (k * a n)) *
          ∫ x in Icc (a n) (b n), slope U x (x + c) := by
      exact mul_le_mul_of_nonneg_left
        (setIntegral_mono_set ((integrableOn_Icc_iff_integrableOn_Ioc).2 hSlopeInt.1)
          (Eventually.of_forall hSlopeNonnegAll)
          (Eventually.of_forall fun (x : ℝ) (hx : x ∈ S n) => hx.2)) (by positivity)
    _ = (b n ^ tau / (k * a n)) *
          ∫ x in a n..b n, slope U x (x + c) := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (hab n)]
    _ ≤ (b n ^ tau / (k * a n)) * (U (b n + c) - U (a n)) := by
      gcongr
      exact hUmonoOn.intervalIntegral_slope_le (hab n) hc.le
    _ ≤ (b n ^ tau / (k * a n)) * (|U (b n + c)| + |U (a n)|) := by
      exact mul_le_mul_of_nonneg_left
        (by grind [le_abs_self (U (b n + c)), neg_le_abs (U (a n))]) (by positivity)
    _ ≤ (b n ^ tau / (k * a n)) *
          (A * ((b n + c) ^ alpha + a n ^ alpha)) := by
      gcongr
      nlinarith [hUbound _ (hbRc n), hUbound _ haR]
    _ ≤ C * q ^ n := by
      have hba : b n = a n * Real.exp 1 := by
        dsimp [a, b]
        rw [Real.exp_add]
        ring
      have hac : c ≤ a n := hRc.trans haR
      have hbc : b n + c ≤ a n * (Real.exp 1 + 1) := by
        rw [hba]
        nlinarith
      have hpowSum : (b n + c) ^ alpha + a n ^ alpha ≤
          2 * (Real.exp 1 + 1) ^ |alpha| * a n ^ alpha := by
        have ha_le_bc : a n ≤ b n + c := by
          exact (hab n).trans (le_add_of_nonneg_right hc.le)
        have hfactor : 1 ≤ (Real.exp 1 + 1) ^ |alpha| := by
          exact Real.one_le_rpow (by have := Real.exp_pos 1; linarith) (abs_nonneg alpha)
        by_cases hz : 0 ≤ alpha
        · have hpowbc : (b n + c) ^ alpha ≤
              (a n * (Real.exp 1 + 1)) ^ alpha :=
            Real.rpow_le_rpow (by positivity) hbc hz
          rw [Real.mul_rpow (ha_pos n).le (by positivity)] at hpowbc
          have hfacalpha : (Real.exp 1 + 1) ^ alpha ≤
              (Real.exp 1 + 1) ^ |alpha| := by
            rw [abs_of_nonneg hz]
          have hapos : 0 ≤ a n ^ alpha := Real.rpow_nonneg (ha_pos n).le _
          nlinarith [mul_le_mul_of_nonneg_left hfacalpha hapos]
        · have hz' : alpha ≤ 0 := le_of_lt (lt_of_not_ge hz)
          have hpowbc : (b n + c) ^ alpha ≤ a n ^ alpha :=
            Real.rpow_le_rpow_of_nonpos (ha_pos n) ha_le_bc hz'
          have hapos : 0 ≤ a n ^ alpha := Real.rpow_nonneg (ha_pos n).le _
          nlinarith [mul_le_mul_of_nonneg_right hfactor hapos]
      calc
        (b n ^ tau / (k * a n)) *
            (A * ((b n + c) ^ alpha + a n ^ alpha)) ≤
            (b n ^ tau / (k * a n)) *
              (A * (2 * (Real.exp 1 + 1) ^ |alpha| * a n ^ alpha)) := by
          gcongr
        _ = C * q ^ n := by
          rw [hba, Real.mul_rpow (ha_pos n).le (Real.exp_pos _).le]
          have hpow : a n ^ tau * a n ^ alpha / a n = a n ^ p := by
            dsimp [p]
            rw [Real.rpow_sub (ha_pos n) (tau + alpha) 1,
              Real.rpow_one, Real.rpow_add (ha_pos n) tau alpha]
          calc
            (a n ^ tau * Real.exp 1 ^ tau / (k * a n)) *
                (A * (2 * (Real.exp 1 + 1) ^ |alpha| * a n ^ alpha)) =
                (2 * A / k) * Real.exp 1 ^ tau * (Real.exp 1 + 1) ^ |alpha| *
                  (a n ^ tau * a n ^ alpha / a n) := by ring
            _ = (2 * A / k) * Real.exp 1 ^ tau * (Real.exp 1 + 1) ^ |alpha| *
                  a n ^ p := by rw [hpow]
            _ = C * q ^ n := by
              have haPower : a n ^ p = R ^ p * q ^ n := by
                dsimp [a, q]
                rw [Real.mul_rpow hR.le (Real.exp_pos _).le, ← Real.exp_mul]
                rw [Real.exp_nat_mul]
              rw [haPower]
              dsimp [C]
              ring

lemma eventually_abs_log_le_rpow_of_growthFunctionHyperOrder_lt
    (T : ℝ → ℝ) (rho alpha : ℝ)
    (horder : growthFunctionHyperOrder T = (rho : EReal))
    (hrho : rho < alpha) :
    ∀ᶠ r : ℝ in atTop, |Real.log (T r)| ≤ r ^ alpha := by
  have hlimlt : Filter.limsup (growthFunctionHyperOrderQuotient T) atTop <
      (alpha : EReal) := by
    rw [← growthFunctionHyperOrder, horder]
    exact_mod_cast hrho
  have hq : ∀ᶠ r : ℝ in atTop,
      growthFunctionHyperOrderQuotient T r < (alpha : EReal) :=
    eventually_lt_of_limsup_lt hlimlt
  filter_upwards [hq, eventually_gt_atTop (1 : ℝ)] with r hqr hr
  have hlogr : 0 < Real.log r := Real.log_pos hr
  have hqr' : Real.log (Real.log (T r)) / Real.log r < alpha := by
    simpa only [growthFunctionHyperOrderQuotient, EReal.coe_lt_coe_iff] using hqr
  by_cases hzero : Real.log (T r) = 0
  · simp [hzero, Real.rpow_nonneg (by positivity : 0 ≤ r) alpha]
  · have hlogabs : Real.log |Real.log (T r)| < alpha * Real.log r := by
      rw [Real.log_abs]
      exact (div_lt_iff₀ hlogr).mp hqr'
    have hexp := Real.exp_lt_exp.mpr hlogabs
    rw [Real.exp_log (abs_pos.mpr hzero)] at hexp
    rw [Real.rpow_def_of_pos (by positivity : 0 < r)]
    simpa [mul_comm] using hexp.le

/-- Transfer of an eventual logarithmic growth bound to a nonnegative
monotone function dominated by the original growth function up to a fixed
constant.  This is the precise comparison needed for the counting functions
in Theorem 6.2 and avoids assigning them a separate real-valued hyper-order. -/
theorem eventually_abs_log_le_mul_rpow_of_monotone_le_add
    (A B : ℝ → ℝ) (C rho alpha : ℝ)
    (hAmono : MonotoneOn A (Set.Ici 0))
    (hAnonneg : ∀ r, 0 ≤ r → 0 ≤ A r)
    (hBtop : Tendsto B atTop atTop)
    (hdom : ∀ r, 0 < r → A r ≤ B r + C)
    (hBgrowth : ∀ beta : ℝ, rho < beta →
      ∀ᶠ r : ℝ in atTop, |Real.log (B r)| ≤ r ^ beta)
    (hrhoalpha : rho < alpha) (halpha : 0 < alpha) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ r : ℝ in atTop, |Real.log (A r)| ≤ K * r ^ alpha := by
  by_cases hpositive : ∃ R : ℝ, 0 ≤ R ∧ 0 < A R
  · obtain ⟨R, hR0, hAR⟩ := hpositive
    have hBlarge : ∀ᶠ r : ℝ in atTop, max 1 |C| ≤ B r :=
      hBtop (eventually_ge_atTop (max 1 |C|))
    have hrlarge : ∀ᶠ r : ℝ in atTop, max 1 R ≤ r :=
      eventually_ge_atTop (max 1 R)
    have hgrowth := hBgrowth alpha hrhoalpha
    let K : ℝ := |Real.log (A R)| + |Real.log 2| + 1
    refine ⟨K, by dsimp [K]; positivity, ?_⟩
    filter_upwards [hBlarge, hrlarge, hgrowth] with r hBr hr hlogB
    have hr1 : 1 ≤ r := (le_max_left 1 R).trans hr
    have hrpos : 0 < r := zero_lt_one.trans_le hr1
    have hRr : R ≤ r := (le_max_right 1 R).trans hr
    have hArLower : A R ≤ A r := hAmono hR0 hrpos.le hRr
    have hArpos : 0 < A r := hAR.trans_le hArLower
    have hBr1 : 1 ≤ B r := (le_max_left 1 |C|).trans hBr
    have hBrpos : 0 < B r := zero_lt_one.trans_le hBr1
    have hCBr : C ≤ B r :=
      le_trans (le_abs_self C) ((le_max_right 1 |C|).trans hBr)
    have hAupper : A r ≤ 2 * B r := by linarith [hdom r hrpos]
    have hlogLower : Real.log (A R) ≤ Real.log (A r) :=
      Real.log_le_log hAR hArLower
    have hlogUpper : Real.log (A r) ≤ Real.log 2 + Real.log (B r) := by
      calc
        Real.log (A r) ≤ Real.log (2 * B r) :=
          Real.log_le_log hArpos hAupper
        _ = Real.log 2 + Real.log (B r) := by
          rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hBrpos.ne']
    have hpow : 1 ≤ r ^ alpha := Real.one_le_rpow hr1 halpha.le
    have hlogBUpper : Real.log (B r) ≤ r ^ alpha :=
      (le_abs_self _).trans hlogB
    rw [abs_le]
    constructor
    · dsimp [K]
      have hlogAR : -|Real.log (A R)| ≤ Real.log (A R) := neg_abs_le _
      nlinarith [abs_nonneg (Real.log (A R)), abs_nonneg (Real.log 2)]
    · dsimp [K]
      have hlog2 : Real.log 2 ≤ |Real.log 2| := le_abs_self _
      nlinarith [abs_nonneg (Real.log (A R)), abs_nonneg (Real.log 2)]
  · push Not at hpositive
    refine ⟨0, le_rfl, ?_⟩
    have htop : ∀ᶠ r : ℝ in atTop, 0 ≤ r := eventually_ge_atTop 0
    filter_upwards [htop] with r hr
    have hzero : A r = 0 :=
      le_antisymm (hpositive r hr) (hAnonneg r hr)
    simp [hzero]

/-- The preceding dominated-growth transfer with coefficient one.  A
slightly smaller intermediate exponent absorbs the fixed multiplicative
constant, which is the form consumed by the power-step Borel lemma. -/
theorem eventually_abs_log_le_rpow_of_monotone_le_add
    (A B : ℝ → ℝ) (C rho alpha : ℝ)
    (hAmono : MonotoneOn A (Set.Ici 0))
    (hAnonneg : ∀ r, 0 ≤ r → 0 ≤ A r)
    (hBtop : Tendsto B atTop atTop)
    (hdom : ∀ r, 0 < r → A r ≤ B r + C)
    (hBgrowth : ∀ beta : ℝ, rho < beta →
      ∀ᶠ r : ℝ in atTop, |Real.log (B r)| ≤ r ^ beta)
    (hrho0 : 0 ≤ rho) (hrhoalpha : rho < alpha) :
    ∀ᶠ r : ℝ in atTop, |Real.log (A r)| ≤ r ^ alpha := by
  let beta : ℝ := (rho + alpha) / 2
  have hrhobeta : rho < beta := by dsimp [beta]; linarith
  have hbetaalpha : beta < alpha := by dsimp [beta]; linarith
  have hbeta0 : 0 < beta := hrho0.trans_lt hrhobeta
  obtain ⟨K, hK0, hbound⟩ :=
    eventually_abs_log_le_mul_rpow_of_monotone_le_add
      A B C rho beta hAmono hAnonneg hBtop hdom hBgrowth
        hrhobeta hbeta0
  have hdiff : 0 < alpha - beta := sub_pos.mpr hbetaalpha
  have hlarge : ∀ᶠ r : ℝ in atTop, K ≤ r ^ (alpha - beta) :=
    (tendsto_rpow_atTop hdiff).eventually (eventually_ge_atTop K)
  have hrpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  filter_upwards [hbound, hlarge, hrpos] with r hlog hK hr
  calc
    |Real.log (A r)| ≤ K * r ^ beta := hlog
    _ ≤ r ^ (alpha - beta) * r ^ beta :=
      mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hr.le beta)
    _ = r ^ alpha := by
      rw [← Real.rpow_add hr]
      congr 1
      ring

/-- A power-step version of the Borel growth lemma.  It is the form needed
to turn the finite-radius pointwise shift estimate into Theorem 4.7. -/
theorem powerShiftGrowthBound_of_eventually_abs_log_le_rpow
    (T : ℝ → ℝ) (rho q : ℝ)
    (hTmono : MonotoneOn T (Set.Ici 0))
    (hTnonneg : ∀ r, 0 ≤ r → 0 ≤ T r)
    (hGrowthBound : ∀ alpha : ℝ, rho < alpha →
      ∀ᶠ r : ℝ in atTop, |Real.log (T r)| ≤ r ^ alpha)
    (hq : 0 < q) (hqrho : q < 1 - rho) :
    ∃ E : Set ℝ, HasFiniteLogarithmicMeasure E ∧
      ∀ᶠ r : ℝ in atTopOutside E, T (r + r ^ q) ≤ 2 * T r := by
  by_cases hpositive : ∃ R : ℝ, 0 ≤ R ∧ 0 < T R
  · obtain ⟨R0, hR00, hTR0⟩ := hpositive
    let alpha : ℝ := (rho + (1 - q)) / 2
    have hrhoalpha : rho < alpha := by dsimp [alpha]; linarith
    have hqalpha : q + alpha < 1 := by dsimp [alpha]; linarith
    have hGrowth := hGrowthBound alpha hrhoalpha
    rw [eventually_atTop] at hGrowth
    obtain ⟨R1, hR1⟩ := hGrowth
    let R : ℝ := max 1 (max R0 R1)
    have hRone : 1 ≤ R := le_max_left _ _
    have hRR0 : R0 ≤ R :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hRR1 : R1 ≤ R :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hRpos : 0 < R := zero_lt_one.trans_le hRone
    let U : ℝ → ℝ := fun x => Real.log (T (max R x))
    have hTmaxpos (x : ℝ) : 0 < T (max R x) :=
      hTR0.trans_le (hTmono hR00 (hRpos.le.trans (le_max_left _ _))
        (hRR0.trans (le_max_left _ _)))
    have hUmono : Monotone U := by
      intro x y hxy
      apply Real.log_le_log (hTmaxpos x)
      exact hTmono (hRpos.le.trans (le_max_left _ _))
        (hRpos.le.trans (le_max_left _ _)) (max_le_max (le_refl R) hxy)
    have hUbound : ∀ x, R ≤ x → |U x| ≤ x ^ alpha := by
      intro x hx
      simpa [U, max_eq_right hx] using hR1 x (hRR1.trans hx)
    let k : ℝ := Real.log 2
    have hk : 0 < k := Real.log_pos (by norm_num)
    let F : Set ℝ :=
      {x | R ≤ x ∧ k ≤ U (x + x ^ q) - U x}
    have hFmeas : MeasurableSet F := by
      have hpowcont : Continuous (fun x : ℝ => x ^ q) :=
        continuous_id.rpow_const (fun _ => Or.inr hq.le)
      have hshift : Continuous (fun x : ℝ => x + x ^ q) :=
        continuous_id.add hpowcont
      have hUmeas : Measurable U := hUmono.measurable
      change MeasurableSet (Ici R ∩ {x | k ≤ U (x + x ^ q) - U x})
      exact measurableSet_Ici.inter (measurableSet_le measurable_const
        ((hUmeas.comp hshift.measurable).sub hUmeas))
    have hFsub : F ⊆ Ici R := fun _ hx => hx.1
    let a : ℕ → ℝ := fun n => R * Real.exp n
    let b : ℕ → ℝ := fun n => R * Real.exp (n + 1)
    let H : ℕ → ℝ := fun n => (b n) ^ q
    let S : ℕ → Set ℝ := fun n => F ∩ Icc (a n) (b n)
    have ha_pos (n : ℕ) : 0 < a n := mul_pos hRpos (Real.exp_pos _)
    have hab (n : ℕ) : a n ≤ b n := by
      dsimp [a, b]
      gcongr
      exact_mod_cast (Nat.le_add_right n 1)
    have hb_one (n : ℕ) : 1 ≤ b n := by
      exact hRone.trans (by
        dsimp [b]
        rw [le_mul_iff_one_le_right hRpos]
        exact Real.one_le_exp (by positivity))
    have hHpos (n : ℕ) : 0 < H n := by
      exact Real.rpow_pos_of_pos (lt_of_lt_of_le (ha_pos n) (hab n)) _
    have hcover : F ⊆ ⋃ n, S n := by
      intro x hx
      obtain ⟨n, hn⟩ := exp_nat_cover R x hRpos (hFsub hx)
      exact mem_iUnion.2 ⟨n, hx, hn⟩
    have hInt (n : ℕ) : IntegrableOn (fun x : ℝ => 1 / x) (S n) := by
      have hcont : ContinuousOn (fun x : ℝ => 1 / x) (Icc (a n) (b n)) := by
        intro x hx
        exact (continuousAt_const.div continuousAt_id
          (ne_of_gt ((ha_pos n).trans_le hx.1))).continuousWithinAt
      exact (hcont.integrableOn_compact isCompact_Icc).mono_set inter_subset_right
    have hFfinite : IntegrableOn (fun x : ℝ => 1 / x) F := by
      apply (integrableOn_iUnion_of_summable_integral_norm hInt ?_).mono_set hcover
      let p : ℝ := q + alpha - 1
      let ratio : ℝ := Real.exp p
      have hpneg : p < 0 := by dsimp [p]; linarith
      have hratio0 : 0 ≤ ratio := (Real.exp_pos _).le
      have hratio1 : ratio < 1 := by
        simpa [ratio] using Real.exp_lt_one_iff.mpr hpneg
      have hratiosum : Summable (fun n : ℕ => ratio ^ n) :=
        summable_geometric_of_lt_one hratio0 hratio1
      let C : ℝ :=
        (2 / k) * (Real.exp 1) ^ q *
          (2 * Real.exp 1) ^ |alpha| * R ^ p
      have hC : 0 ≤ C := by dsimp [C]; positivity
      apply Summable.of_nonneg_of_le
        (fun n => integral_nonneg fun _ => norm_nonneg _) ?_ (hratiosum.mul_left C)
      intro n
      have haR : R ≤ a n := by
        dsimp [a]
        rw [le_mul_iff_one_le_right hRpos]
        exact Real.one_le_exp (by positivity)
      have hbpos : 0 < b n := (ha_pos n).trans_le (hab n)
      have hHformula : H n = a n ^ q * Real.exp 1 ^ q := by
        have hba : b n = a n * Real.exp 1 := by
          dsimp [a, b]
          rw [Real.exp_add]
          ring
        change b n ^ q = _
        rw [hba, Real.mul_rpow (ha_pos n).le (Real.exp_pos _).le]
      have hUmonoOn : MonotoneOn U (Icc (a n) (b n + H n)) := hUmono.monotoneOn _
      have hSlopeInt :
          IntervalIntegrable (fun x => slope U x (x + H n)) volume (a n) (b n) :=
        hUmonoOn.intervalIntegrable_slope (hab n) (hHpos n).le
      have hSlopeNonnegAll : ∀ x, 0 ≤ slope U x (x + H n) := by
        intro x
        rw [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.mpr (hHpos n).le)
          (sub_nonneg.mpr (hUmono (le_add_of_nonneg_right (hHpos n).le)))
      have hpoint : ∀ x ∈ S n,
          ‖1 / x‖ ≤ (H n / (k * a n)) * slope U x (x + H n) := by
        intro x hx
        have hax : a n ≤ x := hx.2.1
        have hxb : x ≤ b n := hx.2.2
        have hxpos : 0 < x := (ha_pos n).trans_le hax
        have hxq : x ^ q ≤ H n := by
          dsimp [H]
          exact Real.rpow_le_rpow hxpos.le hxb hq.le
        have hdiff : k ≤ U (x + H n) - U x := by
          have hxshift : x + x ^ q ≤ x + H n := by linarith
          exact hx.1.2.trans (sub_le_sub_right (hUmono hxshift) (U x))
        have hs : k / H n ≤ slope U x (x + H n) := by
          rw [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul]
          rw [div_eq_mul_inv]
          simpa [mul_comm] using
            mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr (hHpos n).le)
        have hcoeff : 0 ≤ H n / (k * x) := by positivity
        have hmul := mul_le_mul_of_nonneg_left hs hcoeff
        have hid : (H n / (k * x)) * (k / H n) = 1 / x := by
          field_simp [ne_of_gt hk, ne_of_gt (hHpos n)]
        rw [hid] at hmul
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hxpos)]
        refine hmul.trans ?_
        apply mul_le_mul_of_nonneg_right _ (le_trans (by positivity) hs)
        rw [div_eq_mul_inv, div_eq_mul_inv]
        gcongr
      have hOneInt : IntegrableOn (fun x : ℝ => ‖1 / x‖) (S n) := (hInt n).norm
      have hSlopeSetInt : IntegrableOn (fun x => slope U x (x + H n)) (S n) :=
        ((integrableOn_Icc_iff_integrableOn_Ioc).2 hSlopeInt.1).mono_set inter_subset_right
      have hScaledInt : IntegrableOn
          (fun x => (H n / (k * a n)) * slope U x (x + H n)) (S n) :=
        hSlopeSetInt.const_mul _
      calc
        (∫ x in S n, ‖1 / x‖) ≤
            ∫ x in S n, (H n / (k * a n)) * slope U x (x + H n) :=
          setIntegral_mono_on hOneInt hScaledInt
            (hFmeas.inter measurableSet_Icc) hpoint
        _ = (H n / (k * a n)) * ∫ x in S n, slope U x (x + H n) := by
          rw [← integral_const_mul]
        _ ≤ (H n / (k * a n)) *
            ∫ x in Icc (a n) (b n), slope U x (x + H n) := by
          exact mul_le_mul_of_nonneg_left
            (setIntegral_mono_set
              ((integrableOn_Icc_iff_integrableOn_Ioc).2 hSlopeInt.1)
              (Eventually.of_forall hSlopeNonnegAll)
              (Eventually.of_forall fun (x : ℝ) (hx : x ∈ S n) => hx.2)) (by positivity)
        _ = (H n / (k * a n)) *
            ∫ x in a n..b n, slope U x (x + H n) := by
          rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (hab n)]
        _ ≤ (H n / (k * a n)) * (U (b n + H n) - U (a n)) := by
          gcongr
          exact hUmonoOn.intervalIntegral_slope_le (hab n) (hHpos n).le
        _ ≤ (H n / (k * a n)) * (|U (b n + H n)| + |U (a n)|) := by
          exact mul_le_mul_of_nonneg_left
            (by grind [le_abs_self (U (b n + H n)), neg_le_abs (U (a n))]) (by positivity)
        _ ≤ (H n / (k * a n)) *
            ((b n + H n) ^ alpha + a n ^ alpha) := by
          have hbaseR : R ≤ b n + H n :=
            haR.trans ((hab n).trans (le_add_of_nonneg_right (hHpos n).le))
          exact mul_le_mul_of_nonneg_left
            (add_le_add (hUbound _ hbaseR) (hUbound _ haR)) (by positivity)
        _ ≤ C * ratio ^ n := by
          have hba : b n = a n * Real.exp 1 := by
            dsimp [a, b]
            rw [Real.exp_add]
            ring
          have hpowSum : (b n + H n) ^ alpha + a n ^ alpha ≤
              2 * (2 * Real.exp 1) ^ |alpha| * a n ^ alpha := by
            have ha_le : a n ≤ b n + H n :=
              (hab n).trans (le_add_of_nonneg_right (hHpos n).le)
            have hfactor : 1 ≤ (2 * Real.exp 1) ^ |alpha| :=
              Real.one_le_rpow (by
                have hexpone : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
                nlinarith) (abs_nonneg alpha)
            by_cases halpha : 0 ≤ alpha
            · have hqle : q ≤ 1 := by linarith
              have hHle : H n ≤ b n := by
                dsimp [H]
                exact Real.rpow_le_self_of_one_le (hb_one n) hqle
              have hbc : b n + H n ≤ a n * (2 * Real.exp 1) := by
                rw [hba]
                nlinarith
              have hpw : (b n + H n) ^ alpha ≤
                  (a n * (2 * Real.exp 1)) ^ alpha :=
                Real.rpow_le_rpow (by positivity) hbc halpha
              rw [Real.mul_rpow (ha_pos n).le (by positivity)] at hpw
              have hfac : (2 * Real.exp 1) ^ alpha ≤
                  (2 * Real.exp 1) ^ |alpha| := by rw [abs_of_nonneg halpha]
              have hapos : 0 ≤ a n ^ alpha := Real.rpow_nonneg (ha_pos n).le _
              nlinarith [mul_le_mul_of_nonneg_left hfac hapos]
            · have halpha' : alpha ≤ 0 := le_of_lt (lt_of_not_ge halpha)
              have hpw : (b n + H n) ^ alpha ≤ a n ^ alpha :=
                Real.rpow_le_rpow_of_nonpos (ha_pos n) ha_le halpha'
              have hapos : 0 ≤ a n ^ alpha := Real.rpow_nonneg (ha_pos n).le _
              nlinarith [mul_le_mul_of_nonneg_right hfactor hapos]
          calc
            (H n / (k * a n)) * ((b n + H n) ^ alpha + a n ^ alpha) ≤
                (H n / (k * a n)) *
                  (2 * (2 * Real.exp 1) ^ |alpha| * a n ^ alpha) := by gcongr
            _ = C * ratio ^ n := by
              rw [hHformula]
              have hpow : a n ^ q * a n ^ alpha / a n = a n ^ p := by
                dsimp [p]
                rw [Real.rpow_sub (ha_pos n) (q + alpha) 1,
                  Real.rpow_one, Real.rpow_add (ha_pos n) q alpha]
              calc
                (a n ^ q * Real.exp 1 ^ q / (k * a n)) *
                    (2 * (2 * Real.exp 1) ^ |alpha| * a n ^ alpha) =
                    (2 / k) * Real.exp 1 ^ q * (2 * Real.exp 1) ^ |alpha| *
                      (a n ^ q * a n ^ alpha / a n) := by ring
                _ = (2 / k) * Real.exp 1 ^ q * (2 * Real.exp 1) ^ |alpha| *
                      a n ^ p := by rw [hpow]
                _ = C * ratio ^ n := by
                  have haPower : a n ^ p = R ^ p * ratio ^ n := by
                    dsimp [a, ratio]
                    rw [Real.mul_rpow hRpos.le (Real.exp_pos _).le, ← Real.exp_mul]
                    rw [Real.exp_nat_mul]
                  rw [haPower]
                  dsimp [C]
                  ring
    refine ⟨F, hFfinite.mono_set inter_subset_left, ?_⟩
    have htop : ∀ᶠ r : ℝ in atTopOutside F, R ≤ r :=
      (eventually_ge_atTop R).filter_mono inf_le_left
    have hout : ∀ᶠ r : ℝ in atTopOutside F, r ∉ F :=
      (show Fᶜ ∈ Filter.principal Fᶜ by simp) |> fun h =>
        Filter.Eventually.filter_mono inf_le_right h
    filter_upwards [htop, hout] with r hr hout
    have hrpos : 0 < r := hRpos.trans_le hr
    have hrqpos : 0 < r ^ q := Real.rpow_pos_of_pos hrpos _
    have hmaxr : max R r = r := max_eq_right hr
    have hmaxshift : max R (r + r ^ q) = r + r ^ q :=
      max_eq_right (hr.trans (le_add_of_nonneg_right hrqpos.le))
    have hnot : U (r + r ^ q) - U r < k := by
      have : ¬(R ≤ r ∧ k ≤ U (r + r ^ q) - U r) := by
        simpa only [F, mem_setOf_eq] using hout
      exact lt_of_not_ge fun h => this ⟨hr, h⟩
    have hlog : Real.log (T (r + r ^ q)) - Real.log (T r) < Real.log 2 := by
      simpa [U, k, hmaxr, hmaxshift] using hnot
    have hTr : 0 < T r := by simpa [hmaxr] using hTmaxpos r
    have hTshift : 0 < T (r + r ^ q) := hTr.trans_le
      (hTmono hrpos.le (add_pos hrpos hrqpos).le (le_add_of_nonneg_right hrqpos.le))
    have hratio : T (r + r ^ q) / T r < 2 := by
      apply (Real.log_lt_log_iff (div_pos hTshift hTr) (by norm_num)).mp
      rw [Real.log_div hTshift.ne' hTr.ne']
      exact hlog
    exact (div_lt_iff₀ hTr).mp hratio |>.le
  · push Not at hpositive
    refine ⟨∅, by simp [HasFiniteLogarithmicMeasure], ?_⟩
    have htop : ∀ᶠ r : ℝ in atTopOutside (∅ : Set ℝ), 0 ≤ r :=
      (eventually_ge_atTop (0 : ℝ)).filter_mono inf_le_left
    filter_upwards [htop] with r hr
    have hrq : 0 ≤ r ^ q := Real.rpow_nonneg hr _
    have hz (x : ℝ) (hx : 0 ≤ x) : T x = 0 :=
      le_antisymm (hpositive x hx) (hTnonneg x hx)
    simp [hz r hr, hz (r + r ^ q) (add_nonneg hr hrq)]

/-- Public hyperorder formulation of the power-step Borel lemma. -/
theorem powerShiftGrowthBound
    (T : ℝ → ℝ) (rho q : ℝ)
    (hTmono : MonotoneOn T (Set.Ici 0))
    (hTnonneg : ∀ r, 0 ≤ r → 0 ≤ T r)
    (horder : growthFunctionHyperOrder T = (rho : EReal))
    (hq : 0 < q) (hqrho : q < 1 - rho) :
    ∃ E : Set ℝ, HasFiniteLogarithmicMeasure E ∧
      ∀ᶠ r : ℝ in atTopOutside E, T (r + r ^ q) ≤ 2 * T r := by
  exact powerShiftGrowthBound_of_eventually_abs_log_le_rpow
    T rho q hTmono hTnonneg
      (fun alpha halpha ↦
        eventually_abs_log_le_rpow_of_growthFunctionHyperOrder_lt
          T rho alpha horder halpha)
      hq hqrho

/-- The analytic core of the growth-shift lemma only needs monotonicity,
nonnegativity, and the eventual logarithmic growth bound extracted from the
hyper-order.  Continuity in the paper statement is stronger than necessary:
the monotone zero-extension is measurable, which is exactly what the bad-set
argument uses. -/
theorem growthShiftLemma_of_eventually_abs_log_le_rpow
    (T : ℝ → ℝ) (c rho sigma : ℝ)
    (hTmono : MonotoneOn T (Set.Ici 0))
    (hTnonneg : ∀ r, 0 ≤ r → 0 ≤ T r)
    (hc : 0 < c)
    (hGrowthBound : ∀ alpha : ℝ, rho < alpha →
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ᶠ r : ℝ in atTop, |Real.log (T r)| ≤ K * r ^ alpha)
    (hrho : rho < 1) (hsigma : 0 < sigma)
    (hsigma' : sigma < 1 - rho) :
    ∃ E : Set ℝ,
      HasFiniteLogarithmicMeasure E ∧
        (fun r ↦ T (r + c) - T r) =o[atTopOutside E]
          (fun r ↦ T r / r ^ sigma) := by
  by_cases hpositive : ∃ R : ℝ, 0 ≤ R ∧ 0 < T R
  · obtain ⟨R0, hR00, hTR0⟩ := hpositive
    let tau : ℝ := (sigma + (1 - rho)) / 2
    let alpha : ℝ := (rho + (1 - tau)) / 2
    have hsigtau : sigma < tau := by dsimp [tau]; linarith
    have htau : 0 < tau := hsigma.trans hsigtau
    have hrhoalpha : rho < alpha := by dsimp [alpha, tau]; linarith
    have hp : tau + alpha < 1 := by dsimp [alpha, tau]; linarith
    obtain ⟨K, hKnonneg, hGrowth⟩ := hGrowthBound alpha hrhoalpha
    rw [eventually_atTop] at hGrowth
    obtain ⟨R1, hR1⟩ := hGrowth
    let R : ℝ := max 1 (max c (max R0 R1))
    have hRone : 1 ≤ R := le_max_left _ _
    have hRc : c ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
    have hRR0 : R0 ≤ R :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    have hRR1 : R1 ≤ R :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    have hRpos : 0 < R := zero_lt_one.trans_le hRone
    let T0 : ℝ → ℝ := fun x => T (max 0 x)
    have hT0mono : Monotone T0 := by
      intro x y hxy
      exact hTmono (mem_Ici.mpr (le_max_left 0 x))
        (mem_Ici.mpr (le_max_left 0 y))
        (max_le_max (le_refl 0) hxy)
    have hT0meas : Measurable T0 := hT0mono.measurable
    let U : ℝ → ℝ := fun x => Real.log (T (max R x))
    have hTmaxpos (x : ℝ) : 0 < T (max R x) := by
      exact hTR0.trans_le (hTmono hR00
        (hRpos.le.trans (le_max_left _ _)) (hRR0.trans (le_max_left _ _)))
    have hUmono : Monotone U := by
      intro x y hxy
      apply Real.log_le_log (hTmaxpos x)
      exact hTmono (hRpos.le.trans (le_max_left _ _))
        (hRpos.le.trans (le_max_left _ _)) (max_le_max (le_refl R) hxy)
    have hUbound : ∀ x, R ≤ x → |U x| ≤ K * x ^ alpha := by
      intro x hx
      simpa [U, max_eq_right hx] using hR1 x (hRR1.trans hx)
    let F : Set ℝ :=
      {r | R ≤ r ∧ T0 r ≤ (T0 (r + c) - T0 r) * r ^ tau}
    have hFmeas : MeasurableSet F := by
      have hpowcont : Continuous (fun r : ℝ => r ^ tau) :=
        continuous_id.rpow_const (fun _ => Or.inr htau.le)
      have hright : Measurable (fun r => (T0 (r + c) - T0 r) * r ^ tau) :=
        ((hT0meas.comp (continuous_id.add continuous_const).measurable).sub
          hT0meas).mul hpowcont.measurable
      change MeasurableSet (Ici R ∩ {r | T0 r ≤ (T0 (r + c) - T0 r) * r ^ tau})
      exact measurableSet_Ici.inter (measurableSet_le hT0meas hright)
    have hFsub : F ⊆ Ici R := fun _ hx => hx.1
    let k : ℝ := 1 / (3 * c)
    have hk : 0 < k := by dsimp [k]; positivity
    have hbad : ∀ x ∈ F, k / x ^ tau ≤ slope U x (x + c) := by
      intro x hx
      have hxR : R ≤ x := hx.1
      have hx1 : 1 ≤ x := hRone.trans hxR
      have hxpos : 0 < x := zero_lt_one.trans_le hx1
      have hxp : 0 < x ^ tau := Real.rpow_pos_of_pos hxpos _
      have hTx : 0 < T x := hTR0.trans_le (hTmono hR00 hxpos.le (hRR0.trans hxR))
      have hxc : x ≤ x + c := le_add_of_nonneg_right hc.le
      have hTxc : 0 < T (x + c) := hTx.trans_le (hTmono hxpos.le
        (hxpos.le.trans hxc) hxc)
      have hdelta : 0 ≤ T (x + c) - T x := sub_nonneg.mpr
        (hTmono hxpos.le (hxpos.le.trans hxc) hxc)
      have hquot : T x / x ^ tau ≤ T (x + c) - T x := by
        have hx0 : max 0 x = x := max_eq_right hxpos.le
        have hxc0 : max 0 (x + c) = x + c := max_eq_right (hxpos.le.trans hxc)
        exact (div_le_iff₀ hxp).2 (by simpa [T0, hx0, hxc0, mul_comm] using hx.2)
      let z : ℝ := 1 / x ^ tau
      have hzpos : 0 < z := by dsimp [z]; positivity
      have hxpone : 1 ≤ x ^ tau := Real.one_le_rpow hx1 htau.le
      have hzle : z ≤ 1 := by
        dsimp [z]
        exact (div_le_one hxp).2 hxpone
      have hmul : T x * (1 + z) ≤ T (x + c) := by
        dsimp [z]
        rw [mul_add, mul_one]
        rw [one_div, ← div_eq_mul_inv]
        simpa [add_comm] using (le_sub_iff_add_le.mp hquot)
      have hlogmul : Real.log (T x) + Real.log (1 + z) ≤ Real.log (T (x + c)) := by
        rw [← Real.log_mul hTx.ne' (by positivity : (1 + z) ≠ 0)]
        exact Real.log_le_log (mul_pos hTx (by positivity)) hmul
      have hzthird : z / 3 ≤ 2 * z / (z + 2) := by
        apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) (by positivity : 0 < z + 2)).2
        nlinarith
      have hloglower : z / 3 ≤ Real.log (1 + z) :=
        hzthird.trans (Real.le_log_one_add_of_nonneg hzpos.le)
      have hUdiff : z / 3 ≤ U (x + c) - U x := by
        have hmaxx : max R x = x := max_eq_right hxR
        have hmaxxc : max R (x + c) = x + c := max_eq_right (hxR.trans hxc)
        dsimp [U]
        rw [hmaxx, hmaxxc]
        linarith
      rw [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul]
      have hUdiff' : (x ^ tau)⁻¹ / 3 ≤ U (x + c) - U x := by
        change (1 / x ^ tau) / 3 ≤ U (x + c) - U x at hUdiff
        simpa only [one_div] using hUdiff
      dsimp [k]
      calc
        1 / (3 * c) / x ^ tau = c⁻¹ * ((x ^ tau)⁻¹ / 3) := by
          field_simp
        _ ≤ c⁻¹ * (U (x + c) - U x) :=
          mul_le_mul_of_nonneg_left hUdiff' (inv_nonneg.mpr hc.le)
    have hFfinite : IntegrableOn (fun x : ℝ => 1 / x) F :=
      finite_log_measure_of_exp_blocks F U c k tau alpha K R hc hk htau hp
        hKnonneg hRone hRc hFmeas hFsub hUmono hUbound hbad
    refine ⟨F, hFfinite.mono_set inter_subset_left, ?_⟩
    apply (Asymptotics.isLittleO_iff).2
    intro eps heps
    have hpowlim : Tendsto (fun r : ℝ => r ^ (-(tau - sigma))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (sub_pos.mpr hsigtau)
    have heventPow : ∀ᶠ r : ℝ in atTop, r ^ (-(tau - sigma)) < eps :=
      hpowlim.eventually (Iio_mem_nhds heps)
    have heventTop : ∀ᶠ r : ℝ in atTopOutside F, R ≤ r ∧
        r ^ (sigma - tau) < eps := by
      have hbase : ∀ᶠ r : ℝ in atTop, R ≤ r ∧ r ^ (sigma - tau) < eps := by
        filter_upwards [eventually_ge_atTop R, heventPow] with r hr hpw
        simpa [neg_sub] using And.intro hr hpw
      exact hbase.filter_mono inf_le_left
    have heventOut : ∀ᶠ r : ℝ in atTopOutside F, r ∉ F := by
      exact (show Fᶜ ∈ Filter.principal Fᶜ by simp) |> fun h =>
        Filter.Eventually.filter_mono inf_le_right h
    filter_upwards [heventTop, heventOut] with r hr hout
    have hrpos : 0 < r := hRpos.trans_le hr.1
    have hrpowtau : 0 < r ^ tau := Real.rpow_pos_of_pos hrpos _
    have hTr : 0 ≤ T r := hTnonneg r (hrpos.le)
    have hdelta : 0 ≤ T (r + c) - T r :=
      sub_nonneg.mpr (hTmono hrpos.le (add_pos hrpos hc).le
        (le_add_of_nonneg_right hc.le))
    have hnotbad : (T (r + c) - T r) * r ^ tau < T r := by
      have hnot : ¬(R ≤ r ∧ T r ≤ (T (r + c) - T r) * r ^ tau) := by
        have hr0 : max 0 r = r := max_eq_right hrpos.le
        have hrc0 : max 0 (r + c) = r + c := max_eq_right (add_pos hrpos hc).le
        simpa only [F, T0, mem_setOf_eq, hr0, hrc0] using hout
      exact lt_of_not_ge fun h => hnot ⟨hr.1, h⟩
    have hdeltaBound : T (r + c) - T r ≤ T r / r ^ tau :=
      (le_of_lt ((lt_div_iff₀ hrpowtau).2 (by simpa [mul_comm] using hnotbad)))
    rw [Real.norm_eq_abs, abs_of_nonneg hdelta, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hTr (Real.rpow_nonneg hrpos.le _))]
    have hpowerId : T r / r ^ tau = r ^ (sigma - tau) * (T r / r ^ sigma) := by
      rw [Real.rpow_sub hrpos sigma tau]
      field_simp
    rw [hpowerId] at hdeltaBound
    exact hdeltaBound.trans (mul_le_mul_of_nonneg_right hr.2.le
      (div_nonneg hTr (Real.rpow_nonneg hrpos.le _)))
  · push Not at hpositive
    have hzero : ∀ r : ℝ, 0 ≤ r → T r = 0 := by
      intro r hr
      exact le_antisymm (hpositive r hr) (hTnonneg r hr)
    refine ⟨∅, by simp [HasFiniteLogarithmicMeasure], ?_⟩
    apply (Asymptotics.isLittleO_iff).2
    intro eps heps
    have hevent : ∀ᶠ r : ℝ in atTopOutside (∅ : Set ℝ), 0 ≤ r :=
      (eventually_ge_atTop (0 : ℝ)).filter_mono inf_le_left
    filter_upwards [hevent] with r hr
    have hrc : 0 ≤ r + c := add_nonneg hr hc.le
    simp [hzero r hr, hzero (r + c) hrc]

/-- Lemma 4.6 in the paper's original quantifiers. -/
theorem growthShiftLemma : GrowthShiftLemmaStatement := by
  intro T c rho sigma hTmono _hTcont hTnonneg hc horder hrho hsigma hsigma'
  exact growthShiftLemma_of_eventually_abs_log_le_rpow T c rho sigma
    hTmono hTnonneg hc
    (fun alpha halpha ↦ ⟨1, by norm_num,
      by simpa using
        (eventually_abs_log_le_rpow_of_growthFunctionHyperOrder_lt
          T rho alpha horder halpha)⟩)
    hrho hsigma hsigma'

end

end NthTropicalNevanlinna
