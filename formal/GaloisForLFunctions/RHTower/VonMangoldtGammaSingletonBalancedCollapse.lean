import GaloisForLFunctions.RHTower.VonMangoldtGammaAllDepthCauchy

/-!
# A singleton Euler channel collapses under two-boundary Cauchy balance

For one resolved von Mangoldt rate, every all-depth Cauchy vector is a scalar multiple of the
vector at `w = 1 / 2`: the Cauchy parameter occurs only through the common denominator
`w + log 2`.  Consequently the canonical projection away from the two boundary vectors kills
the complete singleton packet, at every Gamma depth and every Cauchy point.

This is a structural no-go for identifying the balanced Cauchy Gram itself with an additive
one-atom Euler observable.  It does not exclude using the balanced packet as a relative or
transition defect inside a larger unbalanced Euler--polar colligation.
-/

open scoped ComplexOrder

namespace RHTower

noncomputable section

private theorem finiteVonMangoldtAllDepthCauchyVector_apply_singletonAux
    (M N : ℕ) (w : ℂ) (pi : Fin M × Fin N) :
    WithLp.ofLp (finiteVonMangoldtAllDepthCauchyVector M N w) pi =
      star (finiteVonMangoldtAllDepthCauchyFeature
        N pi.2 w ((pi.1 : ℕ) + 2)) := by
  simp only [finiteVonMangoldtAllDepthCauchyVector,
    finiteExponentialAllDepthCauchyVector, WithLp.ofLp_toLp,
    finiteVonMangoldtAllDepthCauchyFeature,
    finiteExponentialAllDepthCauchyFeature, Nat.cast_add, Nat.cast_ofNat]

private theorem finiteVonMangoldtAllDepthCauchyFeature_two_eq_boundary_multiple
    (N : ℕ) (i : Fin N) (w : ℂ) :
    finiteVonMangoldtAllDepthCauchyFeature N i w 2 =
      (((1 / 2 : ℂ) + (Real.log 2 : ℂ)) /
          (w + (Real.log 2 : ℂ))) *
        finiteVonMangoldtAllDepthCauchyFeature N i (1 / 2) 2 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hplusReal : 0 < (1 / 2 : ℝ) + Real.log 2 :=
    add_pos_of_pos_of_nonneg (by norm_num) hlog
  have hplus : (1 / 2 : ℂ) + (Real.log 2 : ℂ) ≠ 0 := by
    intro hzero
    have hre : (1 / 2 : ℝ) + Real.log 2 = 0 := by
      simpa [Complex.log_ofReal_re] using congrArg Complex.re hzero
    linarith
  simp only [finiteVonMangoldtAllDepthCauchyFeature,
    finiteExponentialAllDepthCauchyFeature]
  let A : ℂ :=
    (Real.sqrt (finiteVonMangoldtRealWeight 2) *
      Real.log 2 ^ (i : ℕ) *
      expNegOrientedRemainder (N - (i : ℕ)) (Real.log 2) : ℝ)
  let b : ℂ := (1 / 2 : ℂ) + (Real.log 2 : ℂ)
  let d : ℂ := w + (Real.log 2 : ℂ)
  change A / d = (b / d) * (A / b)
  have hb : b ≠ 0 := by
    simpa only [b] using hplus
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  calc
    A * d⁻¹ = A * d⁻¹ * 1 := by ring
    _ = A * d⁻¹ * (b * b⁻¹) := by rw [mul_inv_cancel₀ hb]
    _ = (b * d⁻¹) * (A * b⁻¹) := by ring

/-- With only the resolved rate `log 2`, every Cauchy vector already lies in the span of the two
boundary vectors.  Analytically the Cauchy pole `w = -log 2` is excluded; Lean's totalized
division assigns zero there, so the theorem is unconditional. -/
theorem finiteVonMangoldtAllDepthCauchyVector_one_mem_boundary
    (N : ℕ) (w : ℂ) :
    finiteVonMangoldtAllDepthCauchyVector 1 N w ∈
      finiteVonMangoldtAllDepthBoundarySubspace 1 N := by
  let c : ℂ :=
    star (((1 / 2 : ℂ) + (Real.log 2 : ℂ)) /
      (w + (Real.log 2 : ℂ)))
  have hv :
      finiteVonMangoldtAllDepthCauchyVector 1 N w =
        c • finiteVonMangoldtAllDepthCauchyVector 1 N (1 / 2) := by
    apply WithLp.ofLp_injective 2
    funext pi
    obtain ⟨p, i⟩ := pi
    have hp : p = (0 : Fin 1) := Subsingleton.elim _ _
    subst p
    rw [WithLp.ofLp_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [finiteVonMangoldtAllDepthCauchyVector_apply_singletonAux,
      finiteVonMangoldtAllDepthCauchyVector_apply_singletonAux]
    simp only [Fin.val_zero, zero_add]
    change star (finiteVonMangoldtAllDepthCauchyFeature N i w 2) =
      c * star (finiteVonMangoldtAllDepthCauchyFeature N i (1 / 2) 2)
    rw [finiteVonMangoldtAllDepthCauchyFeature_two_eq_boundary_multiple N i w,
      star_mul]
    dsimp only [c]
    ring
  rw [hv]
  apply (finiteVonMangoldtAllDepthBoundarySubspace 1 N).smul_mem
  apply Submodule.subset_span
  simp

/-- The canonical two-boundary balanced vector of a singleton von Mangoldt source is zero. -/
@[simp] theorem finiteVonMangoldtAllDepthBalancedCauchyVector_one_eq_zero
    (N : ℕ) (w : ℂ) :
    finiteVonMangoldtAllDepthBalancedCauchyVector 1 N w = 0 := by
  rw [finiteVonMangoldtAllDepthBalancedCauchyVector]
  have hv : finiteVonMangoldtAllDepthCauchyVector 1 N w ∈
      ((finiteVonMangoldtAllDepthBoundarySubspace 1 N)ᗮ)ᗮ := by
    apply (finiteVonMangoldtAllDepthBoundarySubspace 1 N).le_orthogonal_orthogonal
    exact finiteVonMangoldtAllDepthCauchyVector_one_mem_boundary N w
  have hproj :=
    Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hv
  exact congrArg Subtype.val hproj

/-- Every finite Cauchy-point Gram of the balanced singleton source is the zero matrix. -/
@[simp] theorem finiteVonMangoldtAllDepthBalancedCauchyGram_one_eq_zero
    (N : ℕ) {K : ℕ} (w : Fin K → ℂ) :
    finiteVonMangoldtAllDepthBalancedCauchyGram 1 N w = 0 := by
  ext a b
  rw [finiteVonMangoldtAllDepthBalancedCauchyGram, Matrix.gram_apply]
  simp

end

end RHTower
