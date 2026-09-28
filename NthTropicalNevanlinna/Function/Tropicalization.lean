import Mathlib

/-!
# The `n`-th tropicalization at the beginning of the paper

The paper works pointwise in the spatial variable `X` and lets the positive
dequantization parameter `ε` tend to zero.  This file records that limit
literally.  In particular, it proves the algebraic step which turns a product
of `n` ordinary logarithms into a product of the `n` first-order tropical
limits; this is the source of the piecewise-polynomial tropical product.
-/

open Filter Set
open scoped Topology

namespace NthTropicalNevanlinna

noncomputable section

/-- Pointwise `n`-th dequantization:
`εⁿ log(f(X,ε)) → F(X)` as `ε → 0⁺`. -/
def NthTropicalizesTo
    (n : ℕ) (f : ℝ → ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ X : ℝ,
    Tendsto (fun ε : ℝ ↦ ε ^ n * Real.log (f X ε))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (F X))

/-- First-order tropicalization used for each rational factor in the
construction at the start of Section 2. -/
abbrev FirstTropicalizesTo := NthTropicalizesTo 1

/-- The max-plus polynomial obtained from coefficient exponents `Aᵢ` after
the substitutions `x = exp(X/ε)` and `aᵢ = exp(Aᵢ/ε)`. -/
def tropicalPolynomial (p : ℕ) (A : Fin (p + 1) → ℝ) (X : ℝ) : ℝ :=
  Finset.univ.sup'
    (show (Finset.univ : Finset (Fin (p + 1))).Nonempty from
      ⟨⟨0, Nat.succ_pos p⟩, Finset.mem_univ _⟩)
    (fun i ↦ (i.1 : ℝ) * X + A i)

/-- The ordinary positive polynomial after exponential reparametrization,
written directly as its finite sum of exponentials. -/
def dequantizedPolynomial
    (p : ℕ) (A : Fin (p + 1) → ℝ) (X ε : ℝ) : ℝ :=
  ∑ i : Fin (p + 1), Real.exp (((i.1 : ℝ) * X + A i) / ε)

/-- Finite log-sum-exp converges to maximum under dequantization.  This is
the full first-order calculation used for every numerator and denominator
at the beginning of Section 2. -/
theorem dequantizedPolynomial_firstTropicalizesTo
    (p : ℕ) (A : Fin (p + 1) → ℝ) :
    FirstTropicalizesTo (dequantizedPolynomial p A)
      (tropicalPolynomial p A) := by
  intro X
  let L : Filter ℝ := nhdsWithin 0 (Ioi 0)
  let H : (Finset.univ : Finset (Fin (p + 1))).Nonempty :=
    ⟨⟨0, Nat.succ_pos p⟩, Finset.mem_univ _⟩
  let M : ℝ := Finset.univ.sup' H (fun i : Fin (p + 1) ↦
    (i.1 : ℝ) * X + A i)
  have heps : Tendsto (fun ε : ℝ ↦ ε) L (𝓝 0) :=
    continuousAt_id.tendsto.mono_left inf_le_left
  have hupperLimit : Tendsto
      (fun ε : ℝ ↦ M + ε * Real.log (p + 1)) L (𝓝 M) := by
    convert tendsto_const_nhds.add (heps.mul_const (Real.log (p + 1))) using 1 <;> ring_nf
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupperLimit
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : 0 < ε := hε
    obtain ⟨i, hi, hMi⟩ := Finset.exists_mem_eq_sup' H
      (fun i : Fin (p + 1) ↦ (i.1 : ℝ) * X + A i)
    have hterm : Real.exp (M / ε) ≤ dequantizedPolynomial p A X ε := by
      dsimp [M]
      rw [hMi]
      unfold dequantizedPolynomial
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun k : Fin (p + 1) ↦
          Real.exp (((k.1 : ℝ) * X + A k) / ε))
        (fun k hk ↦ Real.exp_nonneg _) hi
    have hsumpos : 0 < dequantizedPolynomial p A X ε := by
      exact lt_of_lt_of_le (Real.exp_pos _) hterm
    have hlog := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos (M / ε)))
      (Set.mem_Ioi.mpr hsumpos) hterm
    rw [Real.log_exp] at hlog
    have := mul_le_mul_of_nonneg_left hlog hεpos.le
    change M ≤ ε ^ 1 * Real.log (dequantizedPolynomial p A X ε)
    rw [pow_one]
    calc
      M = ε * (M / ε) := by field_simp
      _ ≤ ε * Real.log (dequantizedPolynomial p A X ε) := this
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : 0 < ε := hε
    have hweight : ∀ i : Fin (p + 1),
        (i.1 : ℝ) * X + A i ≤ M := by
      intro i
      exact Finset.le_sup' (f := fun k : Fin (p + 1) ↦
        (k.1 : ℝ) * X + A k) (Finset.mem_univ i)
    have hsumUpper : dequantizedPolynomial p A X ε ≤
        (p + 1 : ℝ) * Real.exp (M / ε) := by
      unfold dequantizedPolynomial
      calc
        (∑ i : Fin (p + 1), Real.exp (((i.1 : ℝ) * X + A i) / ε)) ≤
            ∑ _i : Fin (p + 1), Real.exp (M / ε) := by
          apply Finset.sum_le_sum
          intro i hi
          exact Real.exp_le_exp.mpr
            (div_le_div_of_nonneg_right (hweight i) hεpos.le)
        _ = (p + 1 : ℝ) * Real.exp (M / ε) := by simp
    have hsumpos : 0 < dequantizedPolynomial p A X ε := by
      unfold dequantizedPolynomial
      exact Finset.sum_pos (fun i hi ↦ Real.exp_pos _) ⟨⟨0, Nat.succ_pos p⟩,
        Finset.mem_univ _⟩
    have hupperpos : 0 < (p + 1 : ℝ) * Real.exp (M / ε) := by positivity
    have hlog := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hsumpos) (Set.mem_Ioi.mpr hupperpos) hsumUpper
    rw [Real.log_mul (by positivity : (p + 1 : ℝ) ≠ 0)
      (Real.exp_pos _).ne', Real.log_exp] at hlog
    have := mul_le_mul_of_nonneg_left hlog hεpos.le
    change ε ^ 1 * Real.log (dequantizedPolynomial p A X ε) ≤
      M + ε * Real.log (p + 1)
    rw [pow_one]
    calc
      ε * Real.log (dequantizedPolynomial p A X ε) ≤
          ε * (Real.log (p + 1) + M / ε) := this
      _ = M + ε * Real.log (p + 1) := by field_simp; ring

theorem dequantizedPolynomial_pos
    (p : ℕ) (A : Fin (p + 1) → ℝ) (X ε : ℝ) :
    0 < dequantizedPolynomial p A X ε := by
  unfold dequantizedPolynomial
  exact Finset.sum_pos (fun i hi ↦ Real.exp_pos _)
    ⟨⟨0, Nat.succ_pos p⟩, Finset.mem_univ _⟩

/-!
The paper also permits zero ordinary coefficients and writes them as
`exp (-∞ / ε) = 0`.  Rather than introduce undefined real arithmetic with
`-∞`, the following equivalent API records exactly the nonzero monomials in
a nonempty finite active set.  Missing indices are precisely the zero
coefficients; gaps between degrees are therefore retained faithfully.
-/

/-- Max-plus polynomial on a nonempty finite set of active (nonzero)
monomials. -/
def activeTropicalPolynomial {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (degree : ι → ℕ)
    (A : ι → ℝ) (X : ℝ) : ℝ :=
  s.sup' hs (fun i ↦ (degree i : ℝ) * X + A i)

/-- Ordinary dequantized polynomial with the zero-coefficient monomials
omitted from its active support. -/
def activeDequantizedPolynomial {ι : Type*}
    (s : Finset ι) (degree : ι → ℕ) (A : ι → ℝ)
    (X ε : ℝ) : ℝ :=
  ∑ i ∈ s, Real.exp (((degree i : ℝ) * X + A i) / ε)

/-- Finite log-sum-exp on an arbitrary nonempty active support.  This is the
version of the opening dequantization formula that includes zero
coefficients exactly. -/
theorem activeDequantizedPolynomial_firstTropicalizesTo
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (degree : ι → ℕ) (A : ι → ℝ) :
    FirstTropicalizesTo (activeDequantizedPolynomial s degree A)
      (activeTropicalPolynomial s hs degree A) := by
  intro X
  let L : Filter ℝ := nhdsWithin 0 (Ioi 0)
  let M : ℝ := s.sup' hs (fun i ↦ (degree i : ℝ) * X + A i)
  have heps : Tendsto (fun ε : ℝ ↦ ε) L (𝓝 0) :=
    continuousAt_id.tendsto.mono_left inf_le_left
  have hcard : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  have hupperLimit : Tendsto
      (fun ε : ℝ ↦ M + ε * Real.log s.card) L (𝓝 M) := by
    convert tendsto_const_nhds.add (heps.mul_const (Real.log s.card)) using 1 <;>
      ring_nf
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupperLimit
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : 0 < ε := hε
    obtain ⟨i, hi, hMi⟩ := Finset.exists_mem_eq_sup' hs
      (fun i ↦ (degree i : ℝ) * X + A i)
    have hterm : Real.exp (M / ε) ≤
        activeDequantizedPolynomial s degree A X ε := by
      dsimp [M]
      rw [hMi]
      unfold activeDequantizedPolynomial
      exact Finset.single_le_sum
        (s := s)
        (f := fun k ↦ Real.exp (((degree k : ℝ) * X + A k) / ε))
        (fun k hk ↦ Real.exp_nonneg _) hi
    have hsumpos : 0 < activeDequantizedPolynomial s degree A X ε :=
      lt_of_lt_of_le (Real.exp_pos _) hterm
    have hlog := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos (M / ε)))
      (Set.mem_Ioi.mpr hsumpos) hterm
    rw [Real.log_exp] at hlog
    have hscaled := mul_le_mul_of_nonneg_left hlog hεpos.le
    change M ≤ ε ^ 1 * Real.log (activeDequantizedPolynomial s degree A X ε)
    rw [pow_one]
    calc
      M = ε * (M / ε) := by field_simp
      _ ≤ ε * Real.log (activeDequantizedPolynomial s degree A X ε) := hscaled
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : 0 < ε := hε
    have hweight : ∀ i ∈ s, (degree i : ℝ) * X + A i ≤ M := by
      intro i hi
      exact Finset.le_sup' (f := fun k ↦ (degree k : ℝ) * X + A k) hi
    have hsumUpper : activeDequantizedPolynomial s degree A X ε ≤
        (s.card : ℝ) * Real.exp (M / ε) := by
      unfold activeDequantizedPolynomial
      calc
        (∑ i ∈ s, Real.exp (((degree i : ℝ) * X + A i) / ε)) ≤
            ∑ _i ∈ s, Real.exp (M / ε) := by
          apply Finset.sum_le_sum
          intro i hi
          exact Real.exp_le_exp.mpr
            (div_le_div_of_nonneg_right (hweight i hi) hεpos.le)
        _ = (s.card : ℝ) * Real.exp (M / ε) := by simp
    have hsumpos : 0 < activeDequantizedPolynomial s degree A X ε := by
      unfold activeDequantizedPolynomial
      exact Finset.sum_pos (fun i hi ↦ Real.exp_pos _) hs
    have hupperpos : 0 < (s.card : ℝ) * Real.exp (M / ε) :=
      mul_pos hcard (Real.exp_pos _)
    have hlog := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hsumpos) (Set.mem_Ioi.mpr hupperpos) hsumUpper
    rw [Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
    have hscaled := mul_le_mul_of_nonneg_left hlog hεpos.le
    change ε ^ 1 * Real.log (activeDequantizedPolynomial s degree A X ε) ≤
      M + ε * Real.log s.card
    rw [pow_one]
    calc
      ε * Real.log (activeDequantizedPolynomial s degree A X ε) ≤
          ε * (Real.log s.card + M / ε) := hscaled
      _ = M + ε * Real.log s.card := by field_simp; ring

theorem activeDequantizedPolynomial_pos
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (degree : ι → ℕ) (A : ι → ℝ) (X ε : ℝ) :
    0 < activeDequantizedPolynomial s degree A X ε := by
  unfold activeDequantizedPolynomial
  exact Finset.sum_pos (fun i hi ↦ Real.exp_pos _) hs

/-- Rational factor with possibly zero coefficients, represented by the
nonempty active supports of its numerator and denominator. -/
def activeDequantizedRationalFactor {ι κ : Type*}
    (num : Finset ι) (den : Finset κ)
    (numDegree : ι → ℕ) (denDegree : κ → ℕ)
    (A : ι → ℝ) (B : κ → ℝ) (X ε : ℝ) : ℝ :=
  activeDequantizedPolynomial num numDegree A X ε /
    activeDequantizedPolynomial den denDegree B X ε

def activeTropicalRationalFactor {ι κ : Type*}
    (num : Finset ι) (hnum : num.Nonempty)
    (den : Finset κ) (hden : den.Nonempty)
    (numDegree : ι → ℕ) (denDegree : κ → ℕ)
    (A : ι → ℝ) (B : κ → ℝ) (X : ℝ) : ℝ :=
  activeTropicalPolynomial num hnum numDegree A X -
    activeTropicalPolynomial den hden denDegree B X

/-- A dequantized rational factor and its max-plus limit. -/
def dequantizedRationalFactor
    (p q : ℕ) (A : Fin (p + 1) → ℝ) (B : Fin (q + 1) → ℝ)
    (X ε : ℝ) : ℝ :=
  dequantizedPolynomial p A X ε / dequantizedPolynomial q B X ε

def tropicalRationalFactor
    (p q : ℕ) (A : Fin (p + 1) → ℝ) (B : Fin (q + 1) → ℝ)
    (X : ℝ) : ℝ :=
  tropicalPolynomial p A X - tropicalPolynomial q B X

/-- The pointwise product of a finite family of tropical limits. -/
def tropicalLimitProduct {n : ℕ} (F : Fin n → ℝ → ℝ) (X : ℝ) : ℝ :=
  ∏ k : Fin n, F k X

/-- The scaled product of logarithms appearing after the paper assumes
`log f = ∏ₖ log fₖ`. -/
def scaledLogProduct {n : ℕ}
    (f : Fin n → ℝ → ℝ → ℝ) (X ε : ℝ) : ℝ :=
  ε ^ n * ∏ k : Fin n, Real.log (f k X ε)

/-- Core `n`-th tropicalization identity from Section 2.  Once every factor
has its ordinary first-order tropical limit, the product of logarithms has
the product of those limits after multiplication by `εⁿ`. -/
theorem tendsto_scaledLogProduct
    {n : ℕ} {f : Fin n → ℝ → ℝ → ℝ} {F : Fin n → ℝ → ℝ}
    (h : ∀ k, FirstTropicalizesTo (f k) (F k)) (X : ℝ) :
    Tendsto (scaledLogProduct f X)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (tropicalLimitProduct F X)) := by
  have hprod : Tendsto
      (fun ε : ℝ ↦ ∏ k : Fin n, (ε * Real.log (f k X ε)))
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (∏ k : Fin n, F k X)) := by
    apply tendsto_finsetProd Finset.univ
    intro k hk
    simpa [FirstTropicalizesTo, NthTropicalizesTo] using h k X
  apply hprod.congr'
  filter_upwards with ε
  simp [scaledLogProduct, Finset.prod_mul_distrib, Finset.prod_const]

/-- Paper-facing formulation: if `log f` is the product of the logarithms of
the `n` factors, then the function `f` has the advertised `n`-th tropical
limit. -/
theorem nthTropicalizesTo_of_log_eq_prod
    {n : ℕ} {f : ℝ → ℝ → ℝ} {factor : Fin n → ℝ → ℝ → ℝ}
    {F : Fin n → ℝ → ℝ}
    (_hn : 1 ≤ n)
    (hfactor : ∀ k, FirstTropicalizesTo (factor k) (F k))
    (hlog : ∀ X ε, Real.log (f X ε) =
      ∏ k : Fin n, Real.log (factor k X ε)) :
    NthTropicalizesTo n f (tropicalLimitProduct F) := by
  intro X
  have h := tendsto_scaledLogProduct hfactor X
  apply h.congr'
  filter_upwards with ε
  simp only [scaledLogProduct, hlog]

/-- Tropical multiplication is ordinary addition of the limiting functions. -/
theorem nthTropicalizesTo_mul
    {n : ℕ} {f g : ℝ → ℝ → ℝ} {F G : ℝ → ℝ}
    (hf : NthTropicalizesTo n f F) (hg : NthTropicalizesTo n g G)
    (hfg : ∀ X, ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
      f X ε ≠ 0 ∧ g X ε ≠ 0) :
    NthTropicalizesTo n (fun X ε ↦ f X ε * g X ε)
      (fun X ↦ F X + G X) := by
  intro X
  have hadd := (hf X).add (hg X)
  apply hadd.congr'
  filter_upwards [hfg X] with ε hε
  rw [Real.log_mul hε.1 hε.2]
  ring

/-- Tropical division is ordinary subtraction of the limiting functions. -/
theorem nthTropicalizesTo_div
    {n : ℕ} {f g : ℝ → ℝ → ℝ} {F G : ℝ → ℝ}
    (hf : NthTropicalizesTo n f F) (hg : NthTropicalizesTo n g G)
    (hfg : ∀ X, ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
      f X ε ≠ 0 ∧ g X ε ≠ 0) :
    NthTropicalizesTo n (fun X ε ↦ f X ε / g X ε)
      (fun X ↦ F X - G X) := by
  intro X
  have hsub := (hf X).sub (hg X)
  apply hsub.congr'
  filter_upwards [hfg X] with ε hε
  rw [Real.log_div hε.1 hε.2]
  ring

theorem activeDequantizedRationalFactor_firstTropicalizesTo
    {ι κ : Type*} (num : Finset ι) (hnum : num.Nonempty)
    (den : Finset κ) (hden : den.Nonempty)
    (numDegree : ι → ℕ) (denDegree : κ → ℕ)
    (A : ι → ℝ) (B : κ → ℝ) :
    FirstTropicalizesTo
      (activeDequantizedRationalFactor num den numDegree denDegree A B)
      (activeTropicalRationalFactor num hnum den hden numDegree denDegree A B) := by
  apply nthTropicalizesTo_div
    (activeDequantizedPolynomial_firstTropicalizesTo num hnum numDegree A)
    (activeDequantizedPolynomial_firstTropicalizesTo den hden denDegree B)
  intro X
  filter_upwards with ε
  exact ⟨(activeDequantizedPolynomial_pos num hnum numDegree A X ε).ne',
    (activeDequantizedPolynomial_pos den hden denDegree B X ε).ne'⟩

/-- Canonical positive ordinary source for `n` rational factors with
possibly zero coefficients.  Each factor may have its own active numerator
and denominator support. -/
def activeDequantizedNthTropicalSource
    {n : ℕ} {ι κ : Type*}
    (num : Fin n → Finset ι) (den : Fin n → Finset κ)
    (numDegree : ι → ℕ) (denDegree : κ → ℕ)
    (A : Fin n → ι → ℝ) (B : Fin n → κ → ℝ)
    (X ε : ℝ) : ℝ :=
  Real.exp (∏ k : Fin n,
    Real.log (activeDequantizedRationalFactor
      (num k) (den k) numDegree denDegree (A k) (B k) X ε))

/-- Complete `n`-factor opening dequantization, including the paper's zero
coefficients through active supports. -/
theorem activeDequantizedNthTropicalSource_tropicalizesTo
    {n : ℕ} (hn : 1 ≤ n) {ι κ : Type*}
    (num : Fin n → Finset ι) (hnum : ∀ k, (num k).Nonempty)
    (den : Fin n → Finset κ) (hden : ∀ k, (den k).Nonempty)
    (numDegree : ι → ℕ) (denDegree : κ → ℕ)
    (A : Fin n → ι → ℝ) (B : Fin n → κ → ℝ) :
    NthTropicalizesTo n
      (activeDequantizedNthTropicalSource num den numDegree denDegree A B)
      (fun X ↦ ∏ k : Fin n,
        activeTropicalRationalFactor
          (num k) (hnum k) (den k) (hden k)
          numDegree denDegree (A k) (B k) X) := by
  apply nthTropicalizesTo_of_log_eq_prod hn
    (factor := fun k ↦ activeDequantizedRationalFactor
      (num k) (den k) numDegree denDegree (A k) (B k))
    (F := fun k ↦ activeTropicalRationalFactor
      (num k) (hnum k) (den k) (hden k)
      numDegree denDegree (A k) (B k))
  · intro k
    exact activeDequantizedRationalFactor_firstTropicalizesTo
      (num k) (hnum k) (den k) (hden k)
      numDegree denDegree (A k) (B k)
  · intro X ε
    simp [activeDequantizedNthTropicalSource]

theorem dequantizedRationalFactor_firstTropicalizesTo
    (p q : ℕ) (A : Fin (p + 1) → ℝ) (B : Fin (q + 1) → ℝ) :
    FirstTropicalizesTo (dequantizedRationalFactor p q A B)
      (tropicalRationalFactor p q A B) := by
  apply nthTropicalizesTo_div
    (dequantizedPolynomial_firstTropicalizesTo p A)
    (dequantizedPolynomial_firstTropicalizesTo q B)
  intro X
  filter_upwards with ε
  exact ⟨(dequantizedPolynomial_pos p A X ε).ne',
    (dequantizedPolynomial_pos q B X ε).ne'⟩

/-- A canonical positive ordinary function whose logarithm is the product of
the logarithms of the rational factors in the paper. -/
def dequantizedNthTropicalSource
    {n : ℕ} (p q : Fin n → ℕ)
    (A : ∀ k, Fin (p k + 1) → ℝ) (B : ∀ k, Fin (q k + 1) → ℝ)
    (X ε : ℝ) : ℝ :=
  Real.exp (∏ k : Fin n,
    Real.log (dequantizedRationalFactor (p k) (q k) (A k) (B k) X ε))

/-- The complete `n`-factor dequantization displayed at the beginning of
Section 2. -/
theorem dequantizedNthTropicalSource_tropicalizesTo
    {n : ℕ} (hn : 1 ≤ n) (p q : Fin n → ℕ)
    (A : ∀ k, Fin (p k + 1) → ℝ) (B : ∀ k, Fin (q k + 1) → ℝ) :
    NthTropicalizesTo n (dequantizedNthTropicalSource p q A B)
      (fun X ↦ ∏ k : Fin n,
        tropicalRationalFactor (p k) (q k) (A k) (B k) X) := by
  apply nthTropicalizesTo_of_log_eq_prod hn
    (factor := fun k ↦ dequantizedRationalFactor (p k) (q k) (A k) (B k))
    (F := fun k ↦ tropicalRationalFactor (p k) (q k) (A k) (B k))
  · intro k
    exact dequantizedRationalFactor_firstTropicalizesTo
      (p k) (q k) (A k) (B k)
  · intro X ε
    simp [dequantizedNthTropicalSource]

/-- Tropical addition is pointwise maximum.  The positive-order hypothesis
is essential: it makes the bounded error `εⁿ log 2` vanish. -/
theorem nthTropicalizesTo_add
    {n : ℕ} (hn : 1 ≤ n)
    {f g : ℝ → ℝ → ℝ} {F G : ℝ → ℝ}
    (hf : NthTropicalizesTo n f F) (hg : NthTropicalizesTo n g G)
    (hpos : ∀ X, ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
      0 < f X ε ∧ 0 < g X ε) :
    NthTropicalizesTo n (fun X ε ↦ f X ε + g X ε)
      (fun X ↦ max (F X) (G X)) := by
  intro X
  let L : Filter ℝ := nhdsWithin 0 (Ioi 0)
  have hmax : Tendsto
      (fun ε : ℝ ↦ max (ε ^ n * Real.log (f X ε))
        (ε ^ n * Real.log (g X ε))) L
      (𝓝 (max (F X) (G X))) := (hf X).max (hg X)
  have heps : Tendsto (fun ε : ℝ ↦ ε ^ n) L (𝓝 0) := by
    have hid : Tendsto (fun ε : ℝ ↦ ε) L (𝓝 0) :=
      continuousAt_id.tendsto.mono_left inf_le_left
    have h := hid.pow n
    simpa [zero_pow (Nat.ne_of_gt hn)] using h
  have hupper : Tendsto
      (fun ε : ℝ ↦ max (ε ^ n * Real.log (f X ε))
          (ε ^ n * Real.log (g X ε)) + ε ^ n * Real.log 2) L
      (𝓝 (max (F X) (G X))) := by
    convert hmax.add (heps.mul_const (Real.log 2)) using 1 <;> ring_nf
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmax hupper
  · filter_upwards [hpos X, self_mem_nhdsWithin] with ε hε hεmem
    have hε0 : 0 ≤ ε ^ n := pow_nonneg hεmem.le n
    have hfadd : f X ε ≤ f X ε + g X ε := le_add_of_nonneg_right hε.2.le
    have hgadd : g X ε ≤ f X ε + g X ε := le_add_of_nonneg_left hε.1.le
    have hlogf := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hε.1) (Set.mem_Ioi.mpr (add_pos hε.1 hε.2)) hfadd
    have hlogg := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hε.2) (Set.mem_Ioi.mpr (add_pos hε.1 hε.2)) hgadd
    exact max_le
      (mul_le_mul_of_nonneg_left hlogf hε0)
      (mul_le_mul_of_nonneg_left hlogg hε0)
  · filter_upwards [hpos X, self_mem_nhdsWithin] with ε hε hεmem
    have hε0 : 0 ≤ ε ^ n := pow_nonneg hεmem.le n
    let M : ℝ := max (f X ε) (g X ε)
    have hMpos : 0 < M := lt_of_lt_of_le hε.1 (le_max_left _ _)
    have hsum : f X ε + g X ε ≤ 2 * M := by
      dsimp [M]
      linarith [le_max_left (f X ε) (g X ε), le_max_right (f X ε) (g X ε)]
    have hlogsum : Real.log (f X ε + g X ε) ≤ Real.log (2 * M) :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (add_pos hε.1 hε.2))
        (Set.mem_Ioi.mpr (mul_pos (by norm_num) hMpos)) hsum
    have hlogM : Real.log M = max (Real.log (f X ε)) (Real.log (g X ε)) := by
      dsimp [M]
      rcases le_total (f X ε) (g X ε) with hfg | hgf
      · rw [max_eq_right hfg, max_eq_right]
        exact Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hε.1) (Set.mem_Ioi.mpr hε.2) hfg
      · rw [max_eq_left hgf, max_eq_left]
        exact Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hε.2) (Set.mem_Ioi.mpr hε.1) hgf
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hMpos.ne', hlogM] at hlogsum
    rw [show max (ε ^ n * Real.log (f X ε))
        (ε ^ n * Real.log (g X ε)) =
        ε ^ n * max (Real.log (f X ε)) (Real.log (g X ε)) by
      exact (mul_max_of_nonneg _ _ hε0).symm]
    nlinarith

end

end NthTropicalNevanlinna
