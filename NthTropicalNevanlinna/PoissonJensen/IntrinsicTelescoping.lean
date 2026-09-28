import NthTropicalNevanlinna.Function.IntervalRestriction
import NthTropicalNevanlinna.Nevanlinna.Counting
import NthTropicalNevanlinna.PoissonJensen.Telescoping

/-!
# Intrinsic singularity form of Lemma 3.1

The algebraic Lemma 3.1 is naturally proved from every cut of a finite
polynomial presentation.  This file removes redundant cuts from its public
statement.  On a positive interval the ordinary derivative jump `τ` equals
the intrinsic tropical multiplicity `ω`, which is exactly the form needed
in the displayed shift estimate.
-/

open Set

namespace NthTropicalNevanlinna

noncomputable section

open scoped BigOperators

private theorem filtered_internalCuts_eq_jthSingularPointsIn
    {n m : ℕ} {f : NthTropicalMeromorphicFunction n} {a b : ℝ}
    (Q : IntervalPolynomialPresentation n m f a b)
    (hcomplete : ∀ k : ℤ, a < f.presentation.cutPoint k →
      f.presentation.cutPoint k < b →
        ∃ i : Fin m, Q.internalCut i = f.presentation.cutPoint k)
    (j : ℕ) :
    (Finset.univ.image Q.internalCut).filter
        (fun y ↦ multiplicity f j y ≠ 0) =
      jthSingularPointsIn f j a b := by
  classical
  ext y
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hyimage, hyne⟩
    rcases Finset.mem_image.mp hyimage with ⟨i, hi, rfl⟩
    exact mem_jthSingularPointsIn_iff.mpr
      ⟨⟨Q.leftEndpoint_lt_internalCut i,
          Q.internalCut_lt_rightEndpoint i⟩, hyne⟩
  · intro hy
    rcases mem_jthSingularPointsIn_iff.mp hy with ⟨hyab, hyne⟩
    rcases multiplicity_eq_zero_or_cutPoint_of_presentation
        f f.presentation j y with hzero | ⟨k, hyk, hk⟩
    · exact (hyne hzero).elim
    · obtain ⟨i, hi⟩ := hcomplete k (hyk ▸ hyab.1) (hyk ▸ hyab.2)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩, hyne⟩
      exact hi.trans hyk.symm

private theorem sum_internalCut_multiplicities_eq_jthSingularPointsIn
    {n m : ℕ} {f : NthTropicalMeromorphicFunction n} {a b : ℝ}
    (Q : IntervalPolynomialPresentation n m f a b)
    (hcomplete : ∀ k : ℤ, a < f.presentation.cutPoint k →
      f.presentation.cutPoint k < b →
        ∃ i : Fin m, Q.internalCut i = f.presentation.cutPoint k)
    (j : ℕ) (w : ℝ → ℝ) :
    (∑ i : Fin m,
        multiplicity f j (Q.internalCut i) * w (Q.internalCut i)) =
      ∑ y ∈ jthSingularPointsIn f j a b,
        multiplicity f j y * w y := by
  classical
  let cuts : Finset ℝ := Finset.univ.image Q.internalCut
  let weight : ℝ → ℝ := fun y ↦
    multiplicity f j y * w y
  have hsumImage := Finset.sum_image (f := weight)
    (s := Finset.univ) (g := Q.internalCut)
    Q.internalCut_strictMono.injective.injOn
  have hfilter :
      ∑ y ∈ cuts.filter (fun y ↦ multiplicity f j y ≠ 0), weight y =
        ∑ y ∈ cuts, weight y := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro y hycuts hynot
    have hyzero : multiplicity f j y = 0 := by
      simpa only [Finset.mem_filter, hycuts, true_and, not_ne_iff] using hynot
    simp [weight, hyzero]
  change (∑ i ∈ Finset.univ, weight (Q.internalCut i)) = _
  rw [← hsumImage, ← hfilter]
  change (∑ y ∈ (Finset.univ.image Q.internalCut).filter
      (fun y ↦ multiplicity f j y ≠ 0), weight y) = _
  rw [filtered_internalCuts_eq_jthSingularPointsIn Q hcomplete j]

private theorem sum_internalCuts_eq_jthSingularPointsIn_of_pos
    {n m : ℕ} {f : NthTropicalMeromorphicFunction n} {a b : ℝ}
    (Q : IntervalPolynomialPresentation n m f a b)
    (hcomplete : ∀ k : ℤ, a < f.presentation.cutPoint k →
      f.presentation.cutPoint k < b →
        ∃ i : Fin m, Q.internalCut i = f.presentation.cutPoint k)
    (ha : 0 < a) (j : ℕ) :
    (∑ i : Fin m,
        Q.derivativeJumpAt j i * (b - Q.internalCut i) ^ j) =
      ∑ y ∈ jthSingularPointsIn f j a b,
        multiplicity f j y * (b - y) ^ j := by
  have hjump : ∀ i : Fin m,
      Q.derivativeJumpAt j i = multiplicity f j (Q.internalCut i) := by
    intro i
    rw [Q.derivativeJumpAt_eq_intrinsic]
    exact (multiplicity_eq_derivativeJump_of_pos f j
      (ha.trans (Q.leftEndpoint_lt_internalCut i))).symm
  simp_rw [hjump]
  exact sum_internalCut_multiplicities_eq_jthSingularPointsIn
    Q hcomplete j (fun y ↦ (b - y) ^ j)

/--
Lemma 3.1 on a positive interval, with all redundant cuts removed.  The
finite inner sum now ranges over precisely the intrinsic points where the
`j`-th tropical multiplicity is nonzero.
-/
theorem endpoint_sub_eq_intrinsic_singularity_sum_of_pos
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    f b - f a =
      ∑ j ∈ Finset.Icc 1 n,
        (normalizedRightJet f j a * (b - a) ^ j +
          ∑ y ∈ jthSingularPointsIn f j a b,
            multiplicity f j y * (b - y) ^ j) := by
  obtain ⟨m, Q, hcomplete⟩ :=
    f.presentation.exists_intervalPresentation_complete hab
  have hbase := endpoint_sub_eq_jet_sum Q
  rw [hbase]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Q.firstPiece_eq_intrinsicRight,
    ← normalizedRightJet_eq_usingPresentation f f.presentation]
  congr 1
  exact sum_internalCuts_eq_jthSingularPointsIn_of_pos Q hcomplete ha j

/--
The reverse endpoint form of Lemma 3.1 on a negative interval.  Here the
radial sign in the tropical multiplicity converts the signed ordinary jump
sum into the negative of the intrinsic singularity sum.
-/
theorem sub_leftEndpoint_eq_intrinsic_singularity_sum_of_neg
    {n : ℕ} (f : NthTropicalMeromorphicFunction n)
    {a b : ℝ} (hab : a < b) (hb : b < 0) :
    f b - f a =
      ∑ j ∈ Finset.Icc 1 n,
        ((-1 : ℝ) ^ (j + 1) * normalizedLeftJet f j b * (b - a) ^ j -
          ∑ y ∈ jthSingularPointsIn f j a b,
            multiplicity f j y * (y - a) ^ j) := by
  obtain ⟨m, Q, hcomplete⟩ :=
    f.presentation.exists_intervalPresentation_complete hab
  have hbase := sub_leftEndpoint_eq_jet_sum Q
  rw [hbase]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Q.lastPiece_eq_intrinsicLeft,
    ← normalizedLeftJet_eq_usingPresentation f f.presentation]
  congr 1
  have hjump : ∀ i : Fin m,
      (-1 : ℝ) ^ j * Q.derivativeJumpAt j i =
        -multiplicity f j (Q.internalCut i) := by
    intro i
    rw [Q.derivativeJumpAt_eq_intrinsic,
      multiplicity_eq_pow_mul_derivativeJump_of_neg f j
        ((Q.internalCut_lt_rightEndpoint i).trans hb), pow_succ]
    ring
  rw [Finset.mul_sum]
  calc
    (∑ i : Fin m, (-1 : ℝ) ^ j *
        (Q.derivativeJumpAt j i * (Q.internalCut i - a) ^ j)) =
        ∑ i : Fin m,
          ((-1 : ℝ) ^ j * Q.derivativeJumpAt j i) *
            (Q.internalCut i - a) ^ j := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i : Fin m,
          -(multiplicity f j (Q.internalCut i) *
            (Q.internalCut i - a) ^ j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hjump i]
      ring
    _ = -(∑ i : Fin m,
          multiplicity f j (Q.internalCut i) *
            (Q.internalCut i - a) ^ j) := by
      rw [Finset.sum_neg_distrib]
    _ = -(∑ y ∈ jthSingularPointsIn f j a b,
          multiplicity f j y * (y - a) ^ j) := by
      rw [sum_internalCut_multiplicities_eq_jthSingularPointsIn
        Q hcomplete j (fun y ↦ (y - a) ^ j)]

end

end NthTropicalNevanlinna
