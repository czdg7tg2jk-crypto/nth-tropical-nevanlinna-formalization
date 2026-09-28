import NthTropicalNevanlinna.PoissonJensen.DerivativeJump
import NthTropicalNevanlinna.PoissonJensen.RegionPartition
import NthTropicalNevanlinna.PoissonJensen.Kernels

/-!
# Auxiliary jumps and Lemma 3.2

The two piecewise formulas are encoded by four coefficient tables on the
nine-element type `RelativeRegion`.  `auxiliaryJump_eq_byRegion` proves both
tables in all nine cases, completing the cases omitted by the paper.
-/

open Set

namespace NthTropicalNevanlinna

noncomputable section

/-- The paper's auxiliary jump `Ω_f^(j)(x,y)`. -/
def auxiliaryOmega {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (x y : ℝ) : ℝ :=
  rightSign (y - x) ^ (j + 1) * normalizedRightJet f j y -
    leftSign (y - x) ^ (j + 1) * normalizedLeftJet f j y

/-- The paper's auxiliary jump `Γ_f^(j)(x,y)`. -/
def auxiliaryGamma {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (x y : ℝ) : ℝ :=
  rightSign (y - x) ^ j * normalizedRightJet f j y -
    leftSign (y - x) ^ j * normalizedLeftJet f j y

private theorem multiplicity_of_pos {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) {y : ℝ} (hy : 0 < y) :
    multiplicity f j y = normalizedRightJet f j y - normalizedLeftJet f j y := by
  rw [multiplicity_eq_derivativeJump_of_pos f j hy]
  rfl

private theorem multiplicity_of_neg {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) {y : ℝ} (hy : y < 0) :
    multiplicity f j y = (-1 : ℝ) ^ (j + 1) *
      (normalizedRightJet f j y - normalizedLeftJet f j y) :=
  multiplicity_eq_pow_mul_derivativeJump_of_neg f j hy

private theorem multiplicity_at_zero {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) : multiplicity f j 0 =
      normalizedRightJet f j 0 - (-1 : ℝ) ^ (j + 1) * normalizedLeftJet f j 0 := by
  simp [multiplicity, multiplicityUsingPresentation, normalizedRightJet,
    normalizedLeftJet, rightSign, leftSign]

theorem auxiliaryOmega_of_lt {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) {x y : ℝ} (hyx : y < x) : auxiliaryOmega f j x y =
      (-1 : ℝ) ^ (j + 1) *
        (normalizedRightJet f j y - normalizedLeftJet f j y) := by
  have h : y - x < 0 := sub_neg.mpr hyx
  simp only [auxiliaryOmega, rightSign_of_neg h, leftSign_of_nonpos h.le]
  ring

theorem auxiliaryGamma_of_lt {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) {x y : ℝ} (hyx : y < x) : auxiliaryGamma f j x y =
      (-1 : ℝ) ^ j * (normalizedRightJet f j y - normalizedLeftJet f j y) := by
  have h : y - x < 0 := sub_neg.mpr hyx
  simp only [auxiliaryGamma, rightSign_of_neg h, leftSign_of_nonpos h.le]
  ring

theorem auxiliaryOmega_of_gt {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) {x y : ℝ} (hxy : x < y) : auxiliaryOmega f j x y =
      normalizedRightJet f j y - normalizedLeftJet f j y := by
  have h : 0 < y - x := sub_pos.mpr hxy
  simp [auxiliaryOmega, rightSign_of_nonneg h.le, leftSign_of_pos h]

theorem auxiliaryGamma_of_gt {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) {x y : ℝ} (hxy : x < y) : auxiliaryGamma f j x y =
      normalizedRightJet f j y - normalizedLeftJet f j y := by
  have h : 0 < y - x := sub_pos.mpr hxy
  simp [auxiliaryGamma, rightSign_of_nonneg h.le, leftSign_of_pos h]

theorem auxiliaryOmega_diag {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (y : ℝ) : auxiliaryOmega f j y y =
      normalizedRightJet f j y - (-1 : ℝ) ^ (j + 1) * normalizedLeftJet f j y := by
  simp [auxiliaryOmega, rightSign, leftSign]

theorem auxiliaryGamma_diag {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (y : ℝ) : auxiliaryGamma f j y y =
      normalizedRightJet f j y - (-1 : ℝ) ^ j * normalizedLeftJet f j y := by
  simp [auxiliaryGamma, rightSign, leftSign]

/-- Coefficient of `ω_f^(j)(y)` in the region formula for `Ω`. -/
def omegaMultiplicityCoefficient (region : RelativeRegion) (j : ℕ) : ℝ :=
  match region with
  | .f1 | .f2 | .f3 | .f6 | .f8 => 1
  | .f4 | .f5 | .f7 | .f9 => (-1 : ℝ) ^ (j + 1)

/-- Coefficient of the normalized left jet in the region formula for `Ω`. -/
def omegaLeftJetCoefficient (region : RelativeRegion) (j : ℕ) : ℝ :=
  match region with
  | .f1 | .f2 | .f3 | .f4 | .f5 => 0
  | .f6 => (-1 : ℝ) ^ (j + 1) - 1
  | .f7 | .f8 | .f9 => 1 - (-1 : ℝ) ^ (j + 1)

/-- Coefficient of `ω_f^(j)(y)` in the region formula for `Γ`. -/
def gammaMultiplicityCoefficient (region : RelativeRegion) (j : ℕ) : ℝ :=
  match region with
  | .f1 => -1
  | .f2 | .f3 | .f6 | .f8 => 1
  | .f4 | .f7 => (-1 : ℝ) ^ j
  | .f5 | .f9 => (-1 : ℝ) ^ (j + 1)

/-- Coefficient of the normalized left jet in the region formula for `Γ`. -/
def gammaLeftJetCoefficient (region : RelativeRegion) (j : ℕ) : ℝ :=
  match region with
  | .f1 | .f2 | .f4 | .f5 => 0
  | .f3 => 2 * (-1 : ℝ) ^ (j + 1)
  | .f6 | .f7 => (-1 : ℝ) ^ (j + 1) - 1
  | .f8 | .f9 => 1 - (-1 : ℝ) ^ j

@[simp]
theorem auxiliaryOmega_zero (f : NthTropicalMeromorphicFunction n)
    (j : ℕ) (y : ℝ) : auxiliaryOmega f j 0 y = multiplicity f j y := by
  simp [auxiliaryOmega, multiplicity, multiplicityUsingPresentation,
    normalizedRightJet, normalizedLeftJet]

/--
Lemma 3.2.  For a point `y` in any of the nine regions, both auxiliary
jumps equal the coefficient-table combinations stated in the paper.
-/
theorem auxiliaryJump_eq_byRegion
    {n j : ℕ} (f : NthTropicalMeromorphicFunction n)
    {r x y : ℝ} (region : RelativeRegion)
    (_hr : 0 < r) (_hx : x ∈ Ioo (-r) r)
    (_hj : 1 ≤ j) (_hjn : j ≤ n)
    (hregion : InRelativeRegion region r x y) :
    auxiliaryOmega f j x y =
        omegaMultiplicityCoefficient region j * multiplicity f j y +
          omegaLeftJetCoefficient region j * normalizedLeftJet f j y ∧
      auxiliaryGamma f j x y =
        gammaMultiplicityCoefficient region j * multiplicity f j y +
          gammaLeftJetCoefficient region j * normalizedLeftJet f j y := by
  rcases hregion with ⟨hyInterval, hregion⟩
  cases region with
  | f1 =>
      have hy0 : y < 0 := hregion.trans_le (min_le_left 0 x)
      have hyx : y < x := hregion.trans_le (min_le_right 0 x)
      rw [auxiliaryOmega_of_lt f j hyx, auxiliaryGamma_of_lt f j hyx,
        multiplicity_of_neg f j hy0]
      rcases Nat.even_or_odd j with hj | hj
      · have hp : (-1 : ℝ) ^ j = 1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
      · have hp : (-1 : ℝ) ^ j = -1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
  | f2 =>
      have hy0 : 0 < y := (le_max_left 0 x).trans_lt hregion
      have hxy : x < y := (le_max_right 0 x).trans_lt hregion
      rw [auxiliaryOmega_of_gt f j hxy, auxiliaryGamma_of_gt f j hxy,
        multiplicity_of_pos f j hy0]
      rcases Nat.even_or_odd j with hj | hj
      · have hp : (-1 : ℝ) ^ j = 1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
      · have hp : (-1 : ℝ) ^ j = -1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
  | f3 =>
      rcases hregion with ⟨rfl, rfl⟩
      rw [auxiliaryOmega_diag f j 0, auxiliaryGamma_diag f j 0,
        multiplicity_at_zero f j]
      rcases Nat.even_or_odd j with hj | hj
      · have hp : (-1 : ℝ) ^ j = 1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
      · have hp : (-1 : ℝ) ^ j = -1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
  | f4 =>
      rcases hregion with ⟨hy0, hyx⟩
      rw [auxiliaryOmega_of_lt f j hyx, auxiliaryGamma_of_lt f j hyx,
        multiplicity_of_pos f j hy0]
      rcases Nat.even_or_odd j with hj | hj
      · have hp : (-1 : ℝ) ^ j = 1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
      · have hp : (-1 : ℝ) ^ j = -1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
  | f5 =>
      rcases hregion with ⟨hxy, hy0⟩
      rw [auxiliaryOmega_of_gt f j hxy, auxiliaryGamma_of_gt f j hxy,
        multiplicity_of_neg f j hy0]
      rcases Nat.even_or_odd j with hj | hj
      · have hp : (-1 : ℝ) ^ j = 1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
      · have hp : (-1 : ℝ) ^ j = -1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
  | f6 =>
      rcases hregion with ⟨hx0, rfl⟩
      rw [auxiliaryOmega_of_gt f j hx0, auxiliaryGamma_of_gt f j hx0,
        multiplicity_at_zero f j]
      rcases Nat.even_or_odd j with hj | hj
      · have hp : (-1 : ℝ) ^ j = 1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
      · have hp : (-1 : ℝ) ^ j = -1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
  | f7 =>
      rcases hregion with ⟨rfl, hx0⟩
      rw [auxiliaryOmega_of_lt f j hx0, auxiliaryGamma_of_lt f j hx0,
        multiplicity_at_zero f j]
      rcases Nat.even_or_odd j with hj | hj
      · have hp : (-1 : ℝ) ^ j = 1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp]
        constructor <;> ring
      · have hp : (-1 : ℝ) ^ j = -1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
  | f8 =>
      rcases hregion with ⟨hy0, rfl⟩
      rw [auxiliaryOmega_diag f j y, auxiliaryGamma_diag f j y,
        multiplicity_of_pos f j hy0]
      rcases Nat.even_or_odd j with hj | hj
      · have hp : (-1 : ℝ) ^ j = 1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
      · have hp : (-1 : ℝ) ^ j = -1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
  | f9 =>
      rcases hregion with ⟨rfl, hx0⟩
      rw [auxiliaryOmega_diag f j y, auxiliaryGamma_diag f j y,
        multiplicity_of_neg f j hx0]
      rcases Nat.even_or_odd j with hj | hj
      · have hp : (-1 : ℝ) ^ j = 1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring
      · have hp : (-1 : ℝ) ^ j = -1 := hj.neg_one_pow
        simp [omegaMultiplicityCoefficient, omegaLeftJetCoefficient,
          gammaMultiplicityCoefficient, gammaLeftJetCoefficient, pow_succ, hp] <;> ring

end

end NthTropicalNevanlinna
