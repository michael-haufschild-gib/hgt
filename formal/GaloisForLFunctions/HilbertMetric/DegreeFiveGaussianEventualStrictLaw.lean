import GaloisForLFunctions.HilbertMetric.DegreeFiveGaussianCurvature
import GaloisForLFunctions.HilbertMetric.GaussianJetPositivity

/-!
# Eventual strictness of the degree-five Gaussian collision Gram

The degree-five collision value matrix is exactly an exponential inner-product Fock Gram at
bandwidth `1/2`, so it is positive semidefinite at every collision scale.  The independent
degree-five unisolvent limit theorem makes its determinant nonzero near every sufficiently small
nonzero scale.  Together these force eventual positive definiteness and positive determinant.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Every degree-five Gaussian collision value matrix is an exponential Fock Gram and therefore
positive semidefinite. -/
theorem degreeFiveGaussianValueMatrix_posSemidef {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (e : ℝ) :
    Matrix.PosSemidef (degreeFiveGaussianValueMatrix lam nodes e) := by
  let x : DegreeFiveIndex d → EuclideanSpace ℝ (Fin d ⊕ DegreeFiveTopIndex d) :=
    fun i => WithLp.toLp 2 (degreeFiveCollisionPoint lam nodes e i)
  rw [show degreeFiveGaussianValueMatrix lam nodes e =
      hilbertExponentialInnerMatrix x (1 / 2 : ℝ) by
    ext i j
    simp [degreeFiveGaussianValueMatrix, gaussianCollisionGramEntry,
      hilbertExponentialInnerMatrix, x, PiLp.inner_apply]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      ring
    · apply Finset.sum_congr rfl
      intro k hk
      ring]
  exact hilbertExponentialInnerMatrix_posSemidef x (1 / 2 : ℝ) (by norm_num)

/-- Arbitrary recombination of the degree-five Gaussian collision rows preserves positive
semidefiniteness, without an invertibility assumption on the coefficient matrix. -/
theorem degreeFiveRecombinedValueMatrix_posSemidef {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ) (e : ℝ) :
    Matrix.PosSemidef (degreeFiveRecombinedValueMatrix lam nodes c e) := by
  rw [degreeFiveRecombinedValueMatrix_eq_congr]
  simpa only [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    (degreeFiveGaussianValueMatrix_posSemidef lam nodes e).mul_mul_conjTranspose_same
      (degreeFiveCoefficientMatrix c)

/-- Away from the collision, inverse degree scaling is another congruence, so the normalized
degree-five matrix is positive semidefinite at every nonzero scale. -/
theorem degreeFiveNormalizedValueMatrix_posSemidef_of_ne {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    {e : ℝ} (he : e ≠ 0) :
    Matrix.PosSemidef (degreeFiveNormalizedValueMatrix lam nodes c e) := by
  rw [degreeFiveNormalizedValueMatrix_eq_scale_recombined lam nodes c he]
  have h := (degreeFiveRecombinedValueMatrix_posSemidef lam nodes c e).mul_mul_conjTranspose_same
    (degreeFiveInverseScaleMatrix e)
  have hscaleT : (degreeFiveInverseScaleMatrix (d := d) e).transpose =
      degreeFiveInverseScaleMatrix e := by
    ext i j
    by_cases hij : i = j
    · subst j
      rfl
    · simp [degreeFiveInverseScaleMatrix, Matrix.transpose_apply, hij, Ne.symm hij]
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hscaleT] at h
  exact h

/-- **Degree-five Gaussian collision strictness law.**  Unisolvent degree-five collision packets
are eventually positive definite at every sufficiently small nonzero collision scale. -/
theorem eventually_degreeFiveSixteen_gaussianValueMatrix_posDef
    (nodes : DegreeFiveIndex 16 → (Fin 16 → ℝ))
    (c : DegreeFiveIndex 16 → DegreeFiveIndex 16 → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    ∀ᶠ e in 𝓝[≠] (0 : ℝ),
      Matrix.PosDef (degreeFiveGaussianValueMatrix degreeFiveBalancedAmplitude nodes e) := by
  filter_upwards
    [eventually_ne_degreeFiveSixteen_gaussianValueMatrix_det nodes c hdelta] with e hdet
  exact ((degreeFiveGaussianValueMatrix_posSemidef
    degreeFiveBalancedAmplitude nodes e).posDef_iff_det_ne_zero).2 hdet

/-- The corresponding degree-five collision Gram determinant is eventually strictly positive,
not merely nonzero. -/
theorem eventually_det_degreeFiveSixteen_gaussianValueMatrix_pos
    (nodes : DegreeFiveIndex 16 → (Fin 16 → ℝ))
    (c : DegreeFiveIndex 16 → DegreeFiveIndex 16 → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    ∀ᶠ e in 𝓝[≠] (0 : ℝ),
      0 < (degreeFiveGaussianValueMatrix degreeFiveBalancedAmplitude nodes e).det := by
  filter_upwards
    [eventually_degreeFiveSixteen_gaussianValueMatrix_posDef nodes c hdelta] with e he
  exact he.det_pos

/-- The same unisolvent packet is eventually positive definite in its singularly normalized
degree coordinates, not only in the raw Gaussian coordinates. -/
theorem eventually_degreeFiveSixteen_normalizedValueMatrix_posDef
    (nodes : DegreeFiveIndex 16 → (Fin 16 → ℝ))
    (c : DegreeFiveIndex 16 → DegreeFiveIndex 16 → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    ∀ᶠ e in 𝓝[≠] (0 : ℝ),
      Matrix.PosDef
        (degreeFiveNormalizedValueMatrix degreeFiveBalancedAmplitude nodes c e) := by
  have hdet : ∀ᶠ e in 𝓝[≠] (0 : ℝ),
      (degreeFiveNormalizedValueMatrix degreeFiveBalancedAmplitude nodes c e).det ≠ 0 :=
    (eventually_ne_degreeFiveNormalizedValueMatrix_det nodes c hdelta).filter_mono inf_le_left
  filter_upwards [hdet, self_mem_nhdsWithin] with e hdetE he
  have he0 : e ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using he
  exact ((degreeFiveNormalizedValueMatrix_posSemidef_of_ne
    degreeFiveBalancedAmplitude nodes c he0).posDef_iff_det_ne_zero).2 hdetE

/-- Consequently the normalized degree-five determinant is eventually strictly positive. -/
theorem eventually_det_degreeFiveSixteen_normalizedValueMatrix_pos
    (nodes : DegreeFiveIndex 16 → (Fin 16 → ℝ))
    (c : DegreeFiveIndex 16 → DegreeFiveIndex 16 → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    ∀ᶠ e in 𝓝[≠] (0 : ℝ),
      0 < (degreeFiveNormalizedValueMatrix degreeFiveBalancedAmplitude nodes c e).det := by
  filter_upwards
    [eventually_degreeFiveSixteen_normalizedValueMatrix_posDef nodes c hdelta] with e he
  exact he.det_pos

end


end GaloisForLFunctions.HilbertMetric
