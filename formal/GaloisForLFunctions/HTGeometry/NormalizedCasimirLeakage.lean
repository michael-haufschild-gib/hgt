import GaloisForLFunctions.HTGeometry.ScaledCasimirCompletion

/-!
# A Casimir gap is a quantitative leakage budget

A Hermitian family with central quadratic Casimir whose nonzero Casimir eigenvalues are all at
least `g` cannot route a source subspace into a smaller target without leaking: the total
Hilbert--Schmidt energy the family deposits outside the target is at least `g` times the dimension
drop.

The proof normalizes the family by the inverse square root of the Casimir of its scaled kernel
completion.  The normalized family is exactly bi-tight, so the bi-stochastic leakage bound applies
to it verbatim; transporting the target along the normalization costs no dimension, and the
normalization itself contracts every vector by the reciprocal of the gap.  Both moves are exact, so
the constant `g` survives undamaged -- which is essential, because it is attained.
-/

open scoped BigOperators Matrix MatrixOrder

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

variable {X J : Type*} [Fintype X] [DecidableEq X] [Fintype J]

/-- The quadratic Casimir of a Hermitian family is Hermitian. -/
theorem matrixFamilyCasimir_isHermitian (A : J → Matrix X X ℂ) (hsymm : ∀ j, (A j)ᴴ = A j) :
    (∑ j, A j * A j).IsHermitian := by
  show (∑ j, A j * A j)ᴴ = ∑ j, A j * A j
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_mul, hsymm j]

/-- A vector the Casimir annihilates lies in the simultaneous kernel, so its projector fixes it. -/
theorem commonKernelProjection_mulVec_eq_self_of_casimir_zero
    (A : J → Matrix X X ℂ) (hsymm : ∀ j, (A j)ᴴ = A j) {w : X → ℂ}
    (hw : (∑ j, A j * A j) *ᵥ w = 0) :
    hermitianMatrixFamilyCommonKernelProjection A *ᵥ w = w := by
  classical
  have hzero : ∑ j, cnormSq (A j *ᵥ w) = 0 := by
    rw [← cinner_casimir_re A hsymm w, hw]
    simp [cinner]
  have hterm : ∀ j : J, A j *ᵥ w = 0 := by
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => cnormSq_nonneg (A j *ᵥ w))).mp hzero j (Finset.mem_univ j)
    exact (cnormSq_eq_zero_iff _).mp this
  have hmem : (WithLp.toLp 2 w : EuclideanSpace ℂ X) ∈ hermitianMatrixFamilyCommonKernel A := by
    refine (Submodule.mem_iInf _).2 fun j => ?_
    show (A j).toEuclideanLin (WithLp.toLp 2 w) = 0
    rw [toEuclideanLin_toLp, hterm j]
    rfl
  have happ := hermitianMatrixFamilyCommonKernelProjection_apply A (WithLp.toLp 2 w)
  rw [Submodule.starProjection_eq_self_iff.mpr hmem, toEuclideanLin_toLp] at happ
  have := congrArg (fun u : EuclideanSpace ℂ X => (WithLp.ofLp u : X → ℂ)) happ
  simpa using this

/-- **A Casimir eigenvalue gap is a form gap off the simultaneous kernel.** -/
theorem commonKernelProjection_form_ge_of_eigenvalue_gap
    (A : J → Matrix X X ℂ) (hsymm : ∀ j, (A j)ᴴ = A j) {g : ℝ}
    (hgap : ∀ (lam : ℝ) (Y : X → ℂ), Y ≠ 0 →
      (∑ j, A j * A j) *ᵥ Y = (lam : ℂ) • Y → lam = 0 ∨ g ≤ lam)
    (z : X → ℂ) (hz : hermitianMatrixFamilyCommonKernelProjection A *ᵥ z = 0) :
    g * cnormSq z ≤ (cinner z ((∑ j, A j * A j) *ᵥ z)).re := by
  refine cnormSq_le_of_eigenvalue_gap _ (matrixFamilyCasimir_isHermitian A hsymm) hgap z ?_
  intro w hw
  have hfix := commonKernelProjection_mulVec_eq_self_of_casimir_zero A hsymm hw
  calc cinner w z
      = cinner (hermitianMatrixFamilyCommonKernelProjection A *ᵥ w) z := by rw [hfix]
    _ = cinner w (hermitianMatrixFamilyCommonKernelProjection A *ᵥ z) := by
        rw [cinner_mulVec, hermitianMatrixFamilyCommonKernelProjection_conjTranspose]
    _ = 0 := by rw [hz]; simp [cinner]

/-- **The source condition is exactly orthogonality to the simultaneous kernel.**  A projector is
annihilated by the kernel projector precisely when its range lies in the orthogonal complement of
the simultaneous kernel. -/
theorem commonKernelProjection_mul_eq_zero_iff (A : J → Matrix X X ℂ) (P : Matrix X X ℂ) :
    hermitianMatrixFamilyCommonKernelProjection A * P = 0 ↔
      ∀ x : EuclideanSpace ℂ X,
        Matrix.toEuclideanLin P x ∈ (hermitianMatrixFamilyCommonKernel A)ᗮ := by
  constructor
  · intro h x
    have hx : Matrix.toEuclideanLin (hermitianMatrixFamilyCommonKernelProjection A * P) x = 0 := by
      rw [h]
      simp
    rw [toEuclideanLin_mul] at hx
    simp only [LinearMap.coe_comp, Function.comp_apply] at hx
    rw [hermitianMatrixFamilyCommonKernelProjection_apply] at hx
    exact (Submodule.starProjection_apply_eq_zero_iff _).mp hx
  · intro h
    have hzero : Matrix.toEuclideanLin (hermitianMatrixFamilyCommonKernelProjection A * P)
        = Matrix.toEuclideanLin (0 : Matrix X X ℂ) := by
      rw [toEuclideanLin_mul, map_zero]
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply]
      rw [hermitianMatrixFamilyCommonKernelProjection_apply]
      exact (Submodule.starProjection_apply_eq_zero_iff _).mpr (h x)
    exact Matrix.toEuclideanLin.injective hzero

/-- **The gap is quantitative leakage.**  For a Hermitian family with central quadratic Casimir
whose form gap off the simultaneous kernel is `g`, the total leakage of a source projector
orthogonal to that kernel past an arbitrary target projector is at least `g` times the dimension
drop. -/
theorem hermitianCentralFamily_leak_ge_gap_mul_dim_sub
    (A : J → Matrix X X ℂ) (hsymm : ∀ j, (A j)ᴴ = A j)
    (hcentral : ∀ j, (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k))
    {g : ℝ} (hg : 0 < g)
    (hgapform : ∀ z : X → ℂ,
      hermitianMatrixFamilyCommonKernelProjection A *ᵥ z = 0 →
        g * cnormSq z ≤ (cinner z ((∑ j, A j * A j) *ᵥ z)).re)
    {PU PV : Matrix X X ℂ}
    (hUherm : PUᴴ = PU) (hUidem : PU * PU = PU)
    (hVidem : PV * PV = PV)
    (hUQ : hermitianMatrixFamilyCommonKernelProjection A * PU = 0) :
    g * ((PU.trace).re - (PV.trace).re) ≤ ∑ j, hsSqRe ((1 - PV) * A j * PU) := by
  classical
  set t : ℝ := Real.sqrt g with htdef
  have ht : t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hg)
  have htg : t ^ 2 = g := Real.sq_sqrt hg.le
  set B : Option J → Matrix X X ℂ := scaledCompletedFamily A t with hBdef
  set Kc : Matrix X X ℂ := ∑ k : Option J, B k * B k with hKc
  obtain ⟨hnonneg, hunit⟩ := scaledCompletedFamily_casimir_nonneg_isUnit A hsymm ht
  set S : Matrix X X ℂ := CFC.sqrt Kc with hS
  have hSunit : IsUnit S := (CFC.isUnit_sqrt_iff Kc hnonneg).mpr hunit
  letI : Invertible S := hSunit.nonempty_invertible.some
  set Rn : Matrix X X ℂ := centralCasimirInvSqrtScaleRCLike B with hRn
  have hRndef : Rn = S⁻¹ := rfl
  have hRS : Rn * S = 1 := by rw [hRndef]; exact Matrix.inv_mul_of_invertible _
  have hSR : S * Rn = 1 := by rw [hRndef]; exact Matrix.mul_inv_of_invertible _
  set PW : Matrix X X ℂ := imageProjection Rn PV with hPW
  obtain ⟨hcol, hrow⟩ := scaledCompletedFamily_biTight A hsymm hcentral ht
  have hleak := leak_ge_dim_sub (fun j : Option J => Rn * B j) hcol hrow hUherm hUidem
    (imageProjection_conjTranspose Rn PV) (imageProjection_mul_self Rn PV)
  have htrace : (PW.trace).re = (PV.trace).re := by
    rw [hPW, imageProjection_trace Rn S PV hRS hSR hVidem]
  rw [htrace] at hleak
  -- the complementary image projector absorbs the target complement
  have hkey : ∀ j : Option J,
      (1 - PW) * ((Rn * B j) * PU) = ((1 - PW) * Rn) * ((1 - PV) * (B j * PU)) := by
    intro j
    have hzero : (1 - PW) * (Rn * PV) = 0 := one_sub_imageProjection_mul Rn PV
    have hsplit : ((1 - PW) * Rn) * ((1 - PV) * (B j * PU))
        = ((1 - PW) * Rn) * (B j * PU) - ((1 - PW) * (Rn * PV)) * (B j * PU) := by
      noncomm_ring
    rw [hsplit, hzero]
    simp only [Matrix.zero_mul, sub_zero]
    noncomm_ring
  -- the normalization is a uniform contraction
  have hcontr : ∀ v : X → ℂ, cnormSq (((1 - PW) * Rn) *ᵥ v) ≤ g⁻¹ * cnormSq v := by
    intro v
    have hstep : ((1 - PW) * Rn) *ᵥ v = (1 - PW) *ᵥ (Rn *ᵥ v) := by
      rw [Matrix.mulVec_mulVec]
    rw [hstep]
    refine le_trans (cnormSq_mulVec_le_of_hermitian_idem
      (conjTranspose_one_sub (imageProjection_conjTranspose Rn PV))
      (one_sub_idem (imageProjection_mul_self Rn PV)) _) ?_
    exact cnormSq_invSqrtScale_mulVec_le A hsymm hg ht htg hgapform v
  have hbound : ∀ j : Option J,
      hsSqRe ((1 - PW) * ((Rn * B j) * PU)) ≤ g⁻¹ * hsSqRe ((1 - PV) * (B j * PU)) := by
    intro j
    rw [hkey j]
    exact hsSqRe_mul_le _ _ hcontr
  have hsum : ∑ j : Option J, hsSqRe ((1 - PW) * ((Rn * B j) * PU))
      ≤ g⁻¹ * ∑ j : Option J, hsSqRe ((1 - PV) * (B j * PU)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hbound j
  -- the adjoined projector contributes nothing
  have hnone : hsSqRe ((1 - PV) * (B none * PU)) = 0 := by
    have hBn : B none * PU = 0 := by
      rw [hBdef]
      show (((t : ℂ)) • hermitianMatrixFamilyCommonKernelProjection A) * PU = 0
      rw [Matrix.smul_mul, hUQ, smul_zero]
    rw [hBn, Matrix.mul_zero, hsSqRe]
    simp
  have hoption : ∑ j : Option J, hsSqRe ((1 - PV) * (B j * PU))
      = ∑ j : J, hsSqRe ((1 - PV) * A j * PU) := by
    rw [Fintype.sum_option, hnone, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_assoc]
    rfl
  rw [hoption] at hsum
  have hfinal : (PU.trace).re - (PV.trace).re
      ≤ g⁻¹ * ∑ j : J, hsSqRe ((1 - PV) * A j * PU) := le_trans hleak hsum
  have hmul := mul_le_mul_of_nonneg_left hfinal (le_of_lt hg)
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hg), one_mul] at hmul

end

end GaloisForLFunctions.HTGeometry
