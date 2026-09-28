import NthTropicalNevanlinna.LogDerivative.GrowthShiftProof

/-!
# The growth lemma and logarithmic-derivative statements

The refined manuscript counts the polynomial sign lemma separately, so the
three declarations below are called Lemma 4.6, Theorem 4.7, and Corollary 4.8
there.  They are Lemma 4.5, Theorem 4.6, and Corollary 4.7 in the original
paper source.

Lemma 4.6 and its complete proof, together with the power-step Borel growth
lemma used below, are in `GrowthShiftProof.lean`.  The already proved
finite-radius shift estimate is in `ShiftEstimate.lean`.
-/

namespace NthTropicalNevanlinna

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- The scale in the pointwise logarithmic-derivative estimate. -/
def logarithmicDerivativeScale {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (σ r : ℝ) : ℝ :=
  characteristic r f / r ^ σ

/-- Theorem 4.7 in the refined numbering (Theorem 4.6 in the source):
the pointwise `n`-th tropical logarithmic-derivative estimate.

The single exceptional set is required to work for both radial signs.  This
is equivalent to the paper's finite conjunction because only two signs are
involved. -/
def PointwiseLogarithmicDerivativeStatement : Prop :=
  ∀ (n : ℕ) (f : NthTropicalMeromorphicFunction n)
      (c rho2 σ : ℝ),
    c ≠ 0 →
    IsWellDefinedNthTropicalMeromorphicFunction f →
    hyperOrder f = (rho2 : EReal) →
    rho2 < 1 → 0 < σ → σ < 1 - rho2 →
    ∃ E : Set ℝ,
      HasFiniteLogarithmicMeasure E ∧
        ∀ δ : ℝ, δ = 1 ∨ δ = -1 →
          (fun r ↦ |f (δ * r + c) - f (δ * r)|) =o[atTopOutside E]
            logarithmicDerivativeScale f σ

/-- Dominated-growth form of Theorem 4.7.  The proof only uses the eventual
logarithmic growth estimate extracted from hyperorder; exposing that estimate
allows a quotient characteristic to be controlled by an ambient curve
characteristic without first assigning the quotient its own real-valued
hyperorder. -/
theorem pointwiseLogarithmicDerivative_of_eventually_abs_log_le_rpow
    (n : ℕ) (f : NthTropicalMeromorphicFunction n)
    (c rho sigma : ℝ)
    (hc : c ≠ 0)
    (hf : IsWellDefinedNthTropicalMeromorphicFunction f)
    (hGrowthBound : ∀ alpha : ℝ, rho < alpha →
      ∀ᶠ r : ℝ in atTop,
        |Real.log (characteristic (max 1 r) f)| ≤ r ^ alpha)
    (hrho : rho < 1) (hsigma : 0 < sigma)
    (hsigma' : sigma < 1 - rho) :
    ∃ E : Set ℝ,
      HasFiniteLogarithmicMeasure E ∧
        ∀ delta : ℝ, delta = 1 ∨ delta = -1 →
          (fun r ↦ |f (delta * r + c) - f (delta * r)|) =o[atTopOutside E]
            logarithmicDerivativeScale f sigma := by
  have hcabs : 0 < |c| := abs_pos.mpr hc
  have hcharMono : CharacteristicMonotone f := characteristicMonotone_of_wellDefined hf
  have hshift : PointwiseShiftEstimate f := pointwiseShiftEstimate_of_wellDefined hf
  by_cases hpositive : ∃ R : ℝ, 0 < R ∧ 0 < characteristic R f
  · obtain ⟨R0, hR0, hTR0⟩ := hpositive
    let q : ℝ := (sigma + (1 - rho)) / 2
    have hsigq : sigma < q := by dsimp [q]; linarith
    have hq : 0 < q := hsigma.trans hsigq
    have hqrho : q < 1 - rho := by dsimp [q]; linarith
    let T : ℝ → ℝ := fun r => characteristic (max 1 r) f
    have hTmono : MonotoneOn T (Ici 0) := by
      intro x hx y hy hxy
      exact hcharMono (by simp) (by simp) (max_le_max (le_refl 1) hxy)
    have hTnonneg : ∀ r, 0 ≤ r → 0 ≤ T r := by
      intro r hr
      exact characteristic_nonneg _ _
    obtain ⟨E, hEfinite, hEbound⟩ :=
      powerShiftGrowthBound_of_eventually_abs_log_le_rpow
        T rho q hTmono hTnonneg hGrowthBound hq hqrho
    refine ⟨E, hEfinite, ?_⟩
    intro delta hdelta
    apply (Asymptotics.isLittleO_iff).2
    intro eps heps
    let K : ℝ :=
      64 * |c| * (2 + |f 0| / (2 * characteristic R0 f))
    have hKpos : 0 < K := by
      dsimp [K]
      have : 0 ≤ |f 0| / (2 * characteristic R0 f) := by positivity
      positivity
    have hpowlim : Tendsto (fun r : ℝ => K * r ^ (sigma - q)) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (sub_pos.mpr hsigq)).const_mul K
    have hsmall : ∀ᶠ r : ℝ in atTop, K * r ^ (sigma - q) < eps :=
      hpowlim.eventually (Iio_mem_nhds heps)
    have hrqLarge : ∀ᶠ r : ℝ in atTop, 8 * |c| < r ^ q :=
      (tendsto_rpow_atTop hq).eventually (eventually_gt_atTop (8 * |c|))
    have hbase : ∀ᶠ r : ℝ in atTop,
        max (max 1 R0) (2 * |c|) < r := eventually_gt_atTop _
    have hEbound' : ∀ᶠ r : ℝ in atTopOutside E,
        characteristic (r + r ^ q) f ≤ 2 * characteristic r f := by
      have hraw := hEbound
      have hlarge : ∀ᶠ r : ℝ in atTopOutside E, 1 ≤ r :=
        (eventually_ge_atTop (1 : ℝ)).filter_mono inf_le_left
      filter_upwards [hraw, hlarge] with r hr hr1
      have hrpos : 0 < r := zero_lt_one.trans_le hr1
      have hshift1 : 1 ≤ r + r ^ q :=
        hr1.trans (le_add_of_nonneg_right (Real.rpow_nonneg hrpos.le _))
      simpa [T, max_eq_right hr1, max_eq_right hshift1] using hr
    have htop : ∀ᶠ r : ℝ in atTopOutside E,
        max (max 1 R0) (2 * |c|) < r ∧
          8 * |c| < r ^ q ∧ K * r ^ (sigma - q) < eps := by
      have hplain : ∀ᶠ r : ℝ in atTop,
          max (max 1 R0) (2 * |c|) < r ∧
            8 * |c| < r ^ q ∧ K * r ^ (sigma - q) < eps := by
        filter_upwards [hbase, hrqLarge, hsmall] with r h1 h2 h3
        exact ⟨h1, h2, h3⟩
      exact hplain.filter_mono inf_le_left
    filter_upwards [hEbound', htop] with r hgrowth hlarge
    have hr1 : 1 < r :=
      (le_max_left (max 1 R0) (2 * |c|)).trans_lt hlarge.1 |>
        (le_max_left 1 R0).trans_lt
    have hrpos : 0 < r := zero_lt_one.trans hr1
    have hrR0 : R0 < r :=
      (le_max_right 1 R0).trans_lt
        ((le_max_left (max 1 R0) (2 * |c|)).trans_lt hlarge.1)
    have hr2c : 2 * |c| < r :=
      (le_max_right (max 1 R0) (2 * |c|)).trans_lt hlarge.1
    have hrq8 : 8 * |c| < r ^ q := hlarge.2.1
    have hrqpos : 0 < r ^ q := Real.rpow_pos_of_pos hrpos _
    let s : ℝ := r + |c|
    have hspos : 0 < s := by dsimp [s]; positivity
    have hcs : |c| < s := by dsimp [s]; linarith
    let A : ℝ := (r + r ^ q) / s
    have hdenShift : (A - 1) * s = r ^ q - |c| := by
      dsimp [A, s]
      field_simp [ne_of_gt hspos]
      ring
    have hdenShiftPos : 0 < (A - 1) * s := by
      rw [hdenShift]
      linarith
    have hA : 1 < A := by
      have hAminus : 0 < A - 1 := by
        rcases (mul_pos_iff.mp hdenShiftPos) with hpos | hneg
        · exact hpos.1
        · exact False.elim (not_lt_of_ge hspos.le hneg.2)
      linarith
    have htarget : A * s = r + r ^ q := by
      dsimp [A]
      exact div_mul_cancel₀ _ (ne_of_gt hspos)
    have hs_lt_two_r : s < 2 * r := by dsimp [s]; linarith
    have hthreshold : ((3 - A) / (A - 1)) * |c| < r := by
      have hAminus : 0 < A - 1 := sub_pos.mpr hA
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ hAminus).2
      have hnum : (3 - A) * |c| ≤ 3 * |c| := by
        have hAnonneg : 0 ≤ A * |c| :=
          mul_nonneg (zero_lt_one.trans hA).le hcabs.le
        nlinarith
      have hthree : 3 * |c| < r * (A - 1) := by
        have hproduct : (3 * |c|) * s < (r * (A - 1)) * s := by
          calc
            (3 * |c|) * s < (3 * |c|) * (2 * r) :=
              mul_lt_mul_of_pos_left hs_lt_two_r (by positivity)
            _ = (6 * |c|) * r := by ring
            _ < (r ^ q - |c|) * r := by
              apply mul_lt_mul_of_pos_right _ hrpos
              nlinarith
            _ = (r * (A - 1)) * s := by
              rw [mul_assoc, hdenShift]
              ring
        exact lt_of_mul_lt_mul_right hproduct hspos.le
      exact hnum.trans_lt hthree
    have hfinite := hshift A c r delta hA hc (max_lt hr2c hthreshold) hdelta
    have hTmonoR : characteristic R0 f ≤ characteristic r f :=
      hcharMono hR0 hrpos hrR0.le
    have hTrpos : 0 < characteristic r f := hTR0.trans_le hTmonoR
    have hinside :
        characteristic (A * s) f + |f 0| / 2 ≤
          (2 + |f 0| / (2 * characteristic R0 f)) * characteristic r f := by
      rw [htarget]
      have hconst : |f 0| / 2 ≤
          (|f 0| / (2 * characteristic R0 f)) * characteristic r f := by
        calc
          |f 0| / 2 = (|f 0| / (2 * characteristic R0 f)) *
              characteristic R0 f := by field_simp [ne_of_gt hTR0]
          _ ≤ (|f 0| / (2 * characteristic R0 f)) * characteristic r f :=
            mul_le_mul_of_nonneg_left hTmonoR (by positivity)
      nlinarith
    have hcoeff :
        (32 * |c|) / ((A - 1) * s) ≤ 64 * |c| / r ^ q := by
      rw [hdenShift]
      have hhalf : r ^ q / 2 < r ^ q - |c| := by linarith
      have hdenpos : 0 < r ^ q - |c| := by linarith
      apply (div_le_div_iff₀ hdenpos hrqpos).2
      nlinarith [mul_nonneg hcabs.le hrqpos.le,
        mul_nonneg hcabs.le hdenpos.le]
    have hbound :
        |f (delta * r + c) - f (delta * r)| ≤
          K * r ^ (sigma - q) * (characteristic r f / r ^ sigma) := by
      calc
        |f (delta * r + c) - f (delta * r)| ≤
            (32 * |c|) / ((A - 1) * s) *
              (characteristic (A * s) f + |f 0| / 2) := by
          simpa [s] using hfinite
        _ ≤ (64 * |c| / r ^ q) *
              ((2 + |f 0| / (2 * characteristic R0 f)) * characteristic r f) :=
          mul_le_mul hcoeff hinside
            (add_nonneg (characteristic_nonneg _ _) (by positivity)) (by positivity)
        _ = K * r ^ (sigma - q) * (characteristic r f / r ^ sigma) := by
          dsimp [K]
          rw [Real.rpow_sub hrpos sigma q]
          field_simp [ne_of_gt hrqpos, ne_of_gt (Real.rpow_pos_of_pos hrpos sigma)]
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _), Real.norm_eq_abs]
    change |f (delta * r + c) - f (delta * r)| ≤
      eps * |characteristic r f / r ^ sigma|
    rw [
      abs_of_nonneg (div_nonneg (characteristic_nonneg _ _)
        (Real.rpow_nonneg hrpos.le _))]
    exact hbound.trans (mul_le_mul_of_nonneg_right hlarge.2.2.le
      (div_nonneg (characteristic_nonneg _ _)
        (Real.rpow_nonneg hrpos.le _)))
  · push Not at hpositive
    refine ⟨∅, by simp [HasFiniteLogarithmicMeasure], ?_⟩
    intro delta hdelta
    have hzero : ∀ r : ℝ, 0 < r → characteristic r f = 0 := by
      intro r hr
      exact le_antisymm (hpositive r hr) (characteristic_nonneg _ _)
    have heq : ∀ r : ℝ, 2 * |c| < r →
        f (delta * r + c) - f (delta * r) = 0 := by
      intro r hr
      have hrpos : 0 < r := by linarith
      by_contra hne
      have hD : 0 < |f (delta * r + c) - f (delta * r)| := abs_pos.mpr hne
      let s : ℝ := r + |c|
      have hspos : 0 < s := by dsimp [s]; positivity
      let B : ℝ := 16 * |c| * |f 0| / s
      have hB : 0 ≤ B := by dsimp [B]; positivity
      let A : ℝ := 3 + B / |f (delta * r + c) - f (delta * r)|
      have hquotnonneg : 0 ≤ B / |f (delta * r + c) - f (delta * r)| :=
        div_nonneg hB hD.le
      have hA : 1 < A := by dsimp [A]; linarith
      have hthreshold : ((3 - A) / (A - 1)) * |c| < r := by
        have hnum : 3 - A ≤ 0 := by dsimp [A]; linarith
        have hden : 0 < A - 1 := sub_pos.mpr hA
        have : ((3 - A) / (A - 1)) * |c| ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hnum hden.le)
            (abs_nonneg c)
        exact this.trans_lt hrpos
      have hb := hshift A c r delta hA hc (max_lt hr hthreshold) hdelta
      have htargetPos : 0 < A * (r + |c|) :=
        mul_pos (zero_lt_one.trans hA) hspos
      rw [hzero _ htargetPos] at hb
      have hstrict :
          (32 * |c|) / ((A - 1) * (r + |c|)) * (|f 0| / 2) <
            |f (delta * r + c) - f (delta * r)| := by
        have hAminus : 0 < A - 1 := sub_pos.mpr hA
        have hrewrite :
            (32 * |c|) / ((A - 1) * (r + |c|)) * (|f 0| / 2) =
              B / (A - 1) := by
          dsimp [B, s]
          field_simp [ne_of_gt hspos, ne_of_gt hAminus]
          ring
        rw [hrewrite]
        apply (div_lt_iff₀ hAminus).2
        dsimp [A]
        have hDne : |f (delta * r + c) - f (delta * r)| ≠ 0 := ne_of_gt hD
        field_simp [hDne]
        nlinarith
      linarith
    apply (Asymptotics.isLittleO_iff).2
    intro eps heps
    have htop : ∀ᶠ r : ℝ in atTopOutside (∅ : Set ℝ), 2 * |c| < r :=
      (eventually_gt_atTop (2 * |c|)).filter_mono inf_le_left
    filter_upwards [htop] with r hr
    simpa [heq r hr] using
      mul_nonneg heps.le (abs_nonneg (logarithmicDerivativeScale f sigma r))

/-- Theorem 4.7 in the refined numbering, with the paper's original public
hypotheses and conclusion. -/
theorem pointwiseLogarithmicDerivative :
    PointwiseLogarithmicDerivativeStatement := by
  intro n f c rho sigma hc hf horder hrho hsigma hsigma'
  let T : ℝ → ℝ := fun r => characteristic (max 1 r) f
  have hquot : ∀ᶠ r : ℝ in atTop,
      growthFunctionHyperOrderQuotient T r = hyperOrderQuotient f r := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    simp [T, growthFunctionHyperOrderQuotient, hyperOrderQuotient, max_eq_right hr]
  have hTorder : growthFunctionHyperOrder T = (rho : EReal) := by
    change Filter.limsup (growthFunctionHyperOrderQuotient T) Filter.atTop = (rho : EReal)
    rw [limsup_congr hquot]
    simpa [hyperOrder] using horder
  have hGrowthBound : ∀ alpha : ℝ, rho < alpha →
      ∀ᶠ r : ℝ in atTop, |Real.log (T r)| ≤ r ^ alpha :=
    fun alpha halpha ↦
      eventually_abs_log_le_rpow_of_growthFunctionHyperOrder_lt
        T rho alpha hTorder halpha
  exact pointwiseLogarithmicDerivative_of_eventually_abs_log_le_rpow
    n f c rho sigma hc hf hGrowthBound hrho hsigma hsigma'

/-- The proximity of the tropical difference quotient `f(x+c) ⊘ f(x)`.
It is written directly from the two endpoints, so no auxiliary realization
of the translated difference is added to the paper statement. -/
def shiftQuotientProximity {n : ℕ}
    (f : NthTropicalMeromorphicFunction n) (c r : ℝ) : ℝ :=
  (maxPlusPositivePart (f (r + c) - f r) +
      maxPlusPositivePart (f (-r + c) - f (-r))) / 2

/-- Corollary 4.8 in the refined numbering (Corollary 4.7 in the source):
the `n`-th tropical logarithmic-derivative lemma. -/
def LogarithmicDerivativeProximityStatement : Prop :=
  ∀ (n : ℕ) (f : NthTropicalMeromorphicFunction n)
      (c rho2 σ : ℝ),
    c ≠ 0 →
    IsWellDefinedNthTropicalMeromorphicFunction f →
    hyperOrder f = (rho2 : EReal) →
    rho2 < 1 → 0 < σ → σ < 1 - rho2 →
    ∃ E : Set ℝ,
      HasFiniteLogarithmicMeasure E ∧
        (fun r ↦ shiftQuotientProximity f c r) =o[atTopOutside E]
          logarithmicDerivativeScale f σ

/-- Corollary 4.8 in the refined numbering, proved from the two radial signs
of Theorem 4.7 and the elementary bound `max x 0 ≤ |x|`. -/
theorem logarithmicDerivativeProximity :
    LogarithmicDerivativeProximityStatement := by
  intro n f c rho sigma hc hf horder hrho hsigma hsigma'
  obtain ⟨E, hEfinite, hpointwise⟩ :=
    pointwiseLogarithmicDerivative n f c rho sigma hc hf horder hrho hsigma hsigma'
  refine ⟨E, hEfinite, ?_⟩
  have hplus := hpointwise 1 (Or.inl rfl)
  have hminus := hpointwise (-1) (Or.inr rfl)
  apply (Asymptotics.isLittleO_iff).2
  intro eps heps
  have hplusEventually :=
    (Asymptotics.isLittleO_iff.mp hplus) (c := eps) heps
  have hminusEventually :=
    (Asymptotics.isLittleO_iff.mp hminus) (c := eps) heps
  filter_upwards [hplusEventually, hminusEventually] with r hplusR hminusR
  have hplusR' :
      |f (r + c) - f r| ≤ eps * ‖logarithmicDerivativeScale f sigma r‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)] using hplusR
  have hminusR' :
      |f (-r + c) - f (-r)| ≤
        eps * ‖logarithmicDerivativeScale f sigma r‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)] using hminusR
  have hpositivePartBound (x : ℝ) : maxPlusPositivePart x ≤ |x| := by
    exact max_le (le_abs_self x) (abs_nonneg x)
  have hproximityNonneg : 0 ≤ shiftQuotientProximity f c r := by
    dsimp [shiftQuotientProximity]
    exact div_nonneg
      (add_nonneg (maxPlusPositivePart_nonneg _) (maxPlusPositivePart_nonneg _)) (by norm_num)
  have hproximityBound :
      shiftQuotientProximity f c r ≤
        (|f (r + c) - f r| + |f (-r + c) - f (-r)|) / 2 := by
    dsimp [shiftQuotientProximity]
    exact div_le_div_of_nonneg_right
      (add_le_add (hpositivePartBound _) (hpositivePartBound _)) (by norm_num)
  rw [Real.norm_eq_abs, abs_of_nonneg hproximityNonneg]
  calc
    shiftQuotientProximity f c r ≤
        (|f (r + c) - f r| + |f (-r + c) - f (-r)|) / 2 := hproximityBound
    _ ≤ ((eps * ‖logarithmicDerivativeScale f sigma r‖) +
          (eps * ‖logarithmicDerivativeScale f sigma r‖)) / 2 :=
      div_le_div_of_nonneg_right (add_le_add hplusR' hminusR') (by norm_num)
    _ = eps * ‖logarithmicDerivativeScale f sigma r‖ := by ring

end

end NthTropicalNevanlinna
