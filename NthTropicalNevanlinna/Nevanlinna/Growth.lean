import NthTropicalNevanlinna.Nevanlinna.Jensen

/-!
# Order and hyper-order

The codomain is `EReal`, so a limsup is allowed to be infinite.  Mathlib's
real logarithm is total (`Real.log 0 = 0`); this is harmless for the literal
definition, while later asymptotic theorems should state eventual positivity
when they use ordinary logarithmic identities.
-/

namespace NthTropicalNevanlinna

noncomputable section

open Filter
open scoped Topology

/-- The logarithmic quotient whose limsup is the order `ρ(f)`. -/
def orderQuotient {n : ℕ} (f : NthTropicalMeromorphicFunction n) (r : ℝ) : EReal :=
  ((Real.log (characteristic r f) / Real.log r : ℝ) : EReal)

/-- The order `ρ(f)` of an n-th tropical meromorphic function. -/
def growthOrder {n : ℕ} (f : NthTropicalMeromorphicFunction n) : EReal :=
  Filter.limsup (orderQuotient f) Filter.atTop

/-- The iterated logarithmic quotient whose limsup is the hyper-order. -/
def hyperOrderQuotient
    {n : ℕ} (f : NthTropicalMeromorphicFunction n) (r : ℝ) : EReal :=
  ((Real.log (Real.log (characteristic r f)) / Real.log r : ℝ) : EReal)

/-- The hyper-order `ρ₂(f)` of an n-th tropical meromorphic function. -/
def hyperOrder {n : ℕ} (f : NthTropicalMeromorphicFunction n) : EReal :=
  Filter.limsup (hyperOrderQuotient f) Filter.atTop

theorem orderQuotient_congr
    {n : ℕ} {f g : NthTropicalMeromorphicFunction n}
    (hT : ∀ r : ℝ, characteristic r f = characteristic r g) :
    orderQuotient f = orderQuotient g := by
  funext r
  simp [orderQuotient, hT r]

theorem hyperOrderQuotient_congr
    {n : ℕ} {f g : NthTropicalMeromorphicFunction n}
    (hT : ∀ r : ℝ, characteristic r f = characteristic r g) :
    hyperOrderQuotient f = hyperOrderQuotient g := by
  funext r
  simp [hyperOrderQuotient, hT r]

/-- Order depends only on the characteristic function. -/
theorem growthOrder_congr
    {n : ℕ} {f g : NthTropicalMeromorphicFunction n}
    (hT : ∀ r : ℝ, characteristic r f = characteristic r g) :
    growthOrder f = growthOrder g := by
  rw [growthOrder, growthOrder, orderQuotient_congr hT]

/-- Hyper-order depends only on the characteristic function. -/
theorem hyperOrder_congr
    {n : ℕ} {f g : NthTropicalMeromorphicFunction n}
    (hT : ∀ r : ℝ, characteristic r f = characteristic r g) :
    hyperOrder f = hyperOrder g := by
  rw [hyperOrder, hyperOrder, hyperOrderQuotient_congr hT]

/-- Multiplying the argument of the logarithm by a positive constant does
not change its logarithmic scale. -/
theorem tendsto_log_const_mul_div_log_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (fun r : ℝ ↦ Real.log (a * r) / Real.log r)
      atTop (𝓝 1) := by
  have hz : Tendsto (fun r : ℝ ↦ Real.log a / Real.log r)
      atTop (𝓝 0) :=
    Tendsto.div_atTop (a := Real.log a) (by simp) Real.tendsto_log_atTop
  have hmain : Tendsto (fun r : ℝ ↦ Real.log a / Real.log r + 1)
      atTop (𝓝 (0 + 1)) := hz.add tendsto_const_nhds
  simpa only [zero_add] using hmain.congr' (by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    symm
    rw [Real.log_mul (ne_of_gt ha) (ne_of_gt (lt_trans zero_lt_one hr)), add_div]
    field_simp [(Real.log_pos hr).ne'])

/-- A reusable analytic criterion for hyper-order one.  It is deliberately
stated in terms of explicit eventual bounds instead of `O`-notation:
`log T(r)` must be trapped between two positive linear functions. -/
theorem hyperOrder_eq_one_of_eventually_linear_log_characteristic
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hbound : ∀ᶠ r in atTop,
      c * r ≤ Real.log (characteristic r f) ∧
        Real.log (characteristic r f) ≤ C * r) :
    hyperOrder f = (1 : EReal) := by
  have hlower := tendsto_log_const_mul_div_log_atTop c hc
  have hupper := tendsto_log_const_mul_div_log_atTop C hC
  have hreal : Tendsto
      (fun r : ℝ ↦ Real.log (Real.log (characteristic r f)) / Real.log r)
      atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    · filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with r hrange hr
      have hr0 : 0 < r := lt_trans zero_lt_one hr
      have hlogr : 0 < Real.log r := Real.log_pos hr
      have hclog : 0 < c * r := mul_pos hc hr0
      have hTlog : 0 < Real.log (characteristic r f) :=
        lt_of_lt_of_le hclog hrange.1
      exact (div_le_div_iff_of_pos_right hlogr).2
        (Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hclog) (Set.mem_Ioi.mpr hTlog) hrange.1)
    · filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with r hrange hr
      have hr0 : 0 < r := lt_trans zero_lt_one hr
      have hlogr : 0 < Real.log r := Real.log_pos hr
      have hclog : 0 < c * r := mul_pos hc hr0
      have hClog : 0 < C * r := mul_pos hC hr0
      have hTlog : 0 < Real.log (characteristic r f) :=
        lt_of_lt_of_le hclog hrange.1
      exact (div_le_div_iff_of_pos_right hlogr).2
        (Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hTlog) (Set.mem_Ioi.mpr hClog) hrange.2)
  unfold hyperOrder hyperOrderQuotient
  exact (EReal.tendsto_coe.mpr hreal).limsup_eq

end

end NthTropicalNevanlinna
