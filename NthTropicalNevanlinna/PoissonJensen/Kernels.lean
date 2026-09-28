import Mathlib

/-!
# Algebraic kernels used in the Poisson--Jensen proof

These definitions are proof infrastructure rather than new primary objects of
the theory.
-/

namespace NthTropicalNevanlinna

noncomputable section

/-- Symmetric endpoint kernel `B_k(r,x)`. -/
def symmetricKernel (k : ℕ) (r x : ℝ) : ℝ :=
  ((r + x) ^ k + (r - x) ^ k) / 2

/-- Antisymmetric endpoint kernel `D_k(r,x)`. -/
def antisymmetricKernel (k : ℕ) (r x : ℝ) : ℝ :=
  ((r + x) ^ k - (r - x) ^ k) / 2

/-- The paper's piecewise-factorizing kernel `E(r,x,y)`. -/
def interactionKernel (r x y : ℝ) : ℝ :=
  r ^ 2 - |x - y| * r - x * y

@[simp] theorem symmetricKernel_zero (r x : ℝ) : symmetricKernel 0 r x = 1 := by
  simp [symmetricKernel]

@[simp] theorem antisymmetricKernel_zero (r x : ℝ) : antisymmetricKernel 0 r x = 0 := by
  simp [antisymmetricKernel]

@[simp] theorem antisymmetricKernel_at_zero (k : ℕ) (r : ℝ) :
    antisymmetricKernel k r 0 = 0 := by
  simp [antisymmetricKernel]

@[simp] theorem symmetricKernel_at_zero (k : ℕ) (r : ℝ) :
    symmetricKernel k r 0 = r ^ k := by
  simp [symmetricKernel]

@[simp] theorem symmetricKernel_one (r x : ℝ) : symmetricKernel 1 r x = r := by
  simp [symmetricKernel]

@[simp] theorem antisymmetricKernel_one (r x : ℝ) : antisymmetricKernel 1 r x = x := by
  simp [antisymmetricKernel]

theorem symmetricKernel_pos {k : ℕ} {r x : ℝ}
    (hr : 0 < r) (hx : x ∈ Set.Ioo (-r) r) : 0 < symmetricKernel k r x := by
  have hplus : 0 < r + x := by linarith [hx.1]
  have hminus : 0 < r - x := by linarith [hx.2]
  simp only [symmetricKernel]
  positivity

theorem symmetricKernel_ne_zero {k : ℕ} {r x : ℝ}
    (hr : 0 < r) (hx : x ∈ Set.Ioo (-r) r) : symmetricKernel k r x ≠ 0 :=
  ne_of_gt (symmetricKernel_pos hr hx)

theorem symmetricKernel_add_antisymmetricKernel (k : ℕ) (r x : ℝ) :
    symmetricKernel k r x + antisymmetricKernel k r x = (r + x) ^ k := by
  simp only [symmetricKernel, antisymmetricKernel]
  ring

theorem symmetricKernel_sub_antisymmetricKernel (k : ℕ) (r x : ℝ) :
    symmetricKernel k r x - antisymmetricKernel k r x = (r - x) ^ k := by
  simp only [symmetricKernel, antisymmetricKernel]
  ring

theorem interactionKernel_of_le {r x y : ℝ} (hxy : x ≤ y) :
    interactionKernel r x y = (r - y) * (r + x) := by
  rw [interactionKernel, abs_of_nonpos (sub_nonpos.mpr hxy)]
  ring

theorem interactionKernel_of_ge {r x y : ℝ} (hyx : y ≤ x) :
    interactionKernel r x y = (r + y) * (r - x) := by
  rw [interactionKernel, abs_of_nonneg (sub_nonneg.mpr hyx)]
  ring

@[simp] theorem interactionKernel_at_zero (r y : ℝ) :
    interactionKernel r 0 y = r * (r - |y|) := by
  simp [interactionKernel]
  ring

@[simp] theorem interactionKernel_diag (r x : ℝ) :
    interactionKernel r x x = r ^ 2 - x ^ 2 := by
  simp [interactionKernel]
  ring

end

end NthTropicalNevanlinna
