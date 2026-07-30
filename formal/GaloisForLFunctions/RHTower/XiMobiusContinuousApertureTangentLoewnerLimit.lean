import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureDyadicProjection

/-!
# The continuous aperture meshes lie below their Cauchy tangent

One-step dyadic refinement of the normalized continuous Möbius aperture Gram adds a positive
semidefinite innovation.  Iterating this law and passing to the already identified all-prime
Cauchy tangent proves the full source-side Loewner bound at every positive mesh width.

This closes the matrix inequality left by the depth-projection model.  It is an unconditional
source-geometry theorem and does not assert the missing source-to-Xi contraction.
-/

namespace RHTower

noncomputable section

open Filter Matrix

/-- Symmetry of the local continuous Möbius--Szegő aperture kernel. -/
theorem xiMobiusPrimeContinuousApertureSzegoMetric_comm
    (a b : ℝ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureSzegoMetric a b p =
      xiMobiusPrimeContinuousApertureSzegoMetric b a p := by
  simp only [xiMobiusPrimeContinuousApertureSzegoMetric]
  ring

/-- Symmetry survives the all-prime completion. -/
theorem xiMobiusContinuousApertureKernel_comm (a b : ℝ) :
    xiMobiusContinuousApertureKernel a b =
      xiMobiusContinuousApertureKernel b a := by
  apply tsum_congr
  intro p
  exact xiMobiusPrimeContinuousApertureSzegoMetric_comm a b p

/-- The exact all-prime Cauchy tangent Gram selected by the zero-mesh limit. -/
def xiMobiusContinuousApertureSlopeTangentGram
    {N : ℕ} (a : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => xiMobiusContinuousApertureSlopeConstant *
    (a i * a j / (a i + a j))

/-- Every finite dyadic refinement of a normalized aperture mesh lies above the original mesh in
Loewner order. -/
theorem xiMobiusContinuousApertureNormalizedMeshGram_dyadic_iter_sub_posSemidef
    {N : ℕ} {h : ℝ} (hh : 0 < h) (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (n : ℕ) :
    (xiMobiusContinuousApertureNormalizedMeshGram (h * ((1 : ℝ) / 2) ^ n) a -
      xiMobiusContinuousApertureNormalizedMeshGram h a).PosSemidef := by
  induction n with
  | zero =>
      simpa using (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin N) (Fin N) ℝ).PosSemidef)
  | succ n ih =>
      have hscale : 0 < h * ((1 : ℝ) / 2) ^ n :=
        mul_pos hh (pow_pos (by norm_num) n)
      have hstep :=
        xiMobiusContinuousApertureNormalizedMeshGram_dyadic_sub_posSemidef
          hscale a ha
      have hmesh : h * ((1 : ℝ) / 2) ^ (n + 1) =
          (h * ((1 : ℝ) / 2) ^ n) / 2 := by
        rw [pow_succ]
        ring
      rw [hmesh]
      have heq :
          xiMobiusContinuousApertureNormalizedMeshGram
                ((h * ((1 : ℝ) / 2) ^ n) / 2) a -
              xiMobiusContinuousApertureNormalizedMeshGram h a =
            (xiMobiusContinuousApertureNormalizedMeshGram
                ((h * ((1 : ℝ) / 2) ^ n) / 2) a -
              xiMobiusContinuousApertureNormalizedMeshGram
                (h * ((1 : ℝ) / 2) ^ n) a) +
            (xiMobiusContinuousApertureNormalizedMeshGram
                (h * ((1 : ℝ) / 2) ^ n) a -
              xiMobiusContinuousApertureNormalizedMeshGram h a) := by
        abel
      rw [heq]
      exact hstep.add ih

/-- Along every positive dyadic mesh ray, the normalized aperture Gram converges entrywise to the
exact all-prime Cauchy tangent Gram. -/
theorem tendsto_xiMobiusContinuousApertureNormalizedMeshGram_dyadic_apply
    {N : ℕ} {h : ℝ} (hh : 0 < h) (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (i j : Fin N) :
    Tendsto
      (fun n : ℕ =>
        xiMobiusContinuousApertureNormalizedMeshGram
          (h * ((1 : ℝ) / 2) ^ n) a i j)
      atTop
      (nhds (xiMobiusContinuousApertureSlopeTangentGram a i j)) := by
  have hzero : Tendsto (fun n : ℕ => h * ((1 : ℝ) / 2) ^ n) atTop (nhds (0 : ℝ)) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)).const_mul h
  have hpos : ∀ᶠ n : ℕ in atTop, h * ((1 : ℝ) / 2) ^ n ∈ Set.Ioi (0 : ℝ) :=
    Filter.Eventually.of_forall fun n => mul_pos hh (pow_pos (by norm_num) n)
  have hmesh : Tendsto (fun n : ℕ => h * ((1 : ℝ) / 2) ^ n) atTop
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  simpa only [xiMobiusContinuousApertureNormalizedMeshGram,
    xiMobiusContinuousApertureSlopeTangentGram] using!
      (tendsto_xiMobiusContinuousApertureKernel_mul_div_nhdsGT_zero
        (ha i) (ha j)).comp hmesh

/-- **Tangent Loewner closure.** Every positive normalized aperture mesh Gram lies below its exact
all-prime Cauchy tangent Gram.  Equivalently, the complete discarded depth fluctuation is positive
semidefinite on every finite positive aperture packet. -/
theorem xiMobiusContinuousApertureSlopeTangentGram_sub_normalizedMeshGram_posSemidef
    {N : ℕ} {h : ℝ} (hh : 0 < h) (a : Fin N → ℝ) (ha : ∀ i, 0 < a i) :
    (xiMobiusContinuousApertureSlopeTangentGram a -
      xiMobiusContinuousApertureNormalizedMeshGram h a).PosSemidef := by
  have hherm :
      (xiMobiusContinuousApertureSlopeTangentGram a -
        xiMobiusContinuousApertureNormalizedMeshGram h a).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.sub_apply, star_trivial,
      xiMobiusContinuousApertureSlopeTangentGram,
      xiMobiusContinuousApertureNormalizedMeshGram]
    rw [xiMobiusContinuousApertureKernel_comm (h * a j) (h * a i)]
    ring
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
  intro x
  have hrow (i : Fin N) :
      Tendsto
        (fun n : ℕ =>
          (xiMobiusContinuousApertureNormalizedMeshGram
              (h * ((1 : ℝ) / 2) ^ n) a -
            xiMobiusContinuousApertureNormalizedMeshGram h a).mulVec x i)
        atTop
        (nhds ((xiMobiusContinuousApertureSlopeTangentGram a -
          xiMobiusContinuousApertureNormalizedMeshGram h a).mulVec x i)) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply]
    apply tendsto_finsetSum
    intro j hj
    exact ((tendsto_xiMobiusContinuousApertureNormalizedMeshGram_dyadic_apply
      hh a ha i j).sub tendsto_const_nhds).mul_const (x j)
  have hquad :
      Tendsto
        (fun n : ℕ => star x ⬝ᵥ
          (xiMobiusContinuousApertureNormalizedMeshGram
              (h * ((1 : ℝ) / 2) ^ n) a -
            xiMobiusContinuousApertureNormalizedMeshGram h a).mulVec x)
        atTop
        (nhds (star x ⬝ᵥ
          (xiMobiusContinuousApertureSlopeTangentGram a -
            xiMobiusContinuousApertureNormalizedMeshGram h a).mulVec x)) := by
    simp only [dotProduct]
    apply tendsto_finsetSum
    intro i hi
    exact tendsto_const_nhds.mul (hrow i)
  apply ge_of_tendsto hquad
  exact Filter.Eventually.of_forall fun n =>
    (xiMobiusContinuousApertureNormalizedMeshGram_dyadic_iter_sub_posSemidef
      hh a ha n).dotProduct_mulVec_nonneg x

end

end RHTower
