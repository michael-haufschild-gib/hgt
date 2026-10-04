import GaloisForLFunctions.HTGeometry.MixedSpectralTraceEscape
import GaloisForLFunctions.HTGeometry.PhaseResonanceProjection

/-!
# Closed-range law for unitary transgression on the Hilbert–Schmidt ideal

For a unitary `U` of a complex Hilbert space `H`, let `α(T) = U* T U` act on the Hilbert–Schmidt
ideal, modelled as the column space `ℓ²(ι; H)` of a Hilbert basis.  The transgression `δ = 1 - α`
has closed range exactly when the spectrum of `U` is finite.

* Every spectral value of a unitary is unimodular and an approximate eigenvalue: a shifted unitary
  that is bounded below is invertible, since its adjoint is bounded below by the same constant.
* Closed range is the transverse lower bound `c ‖X‖₂ ≤ ‖δ X‖₂` on the Hilbert–Schmidt operators with
  vanishing atomic pinching, the orthogonal complement of the fixed space.
* A finite spectrum makes `U` diagonal with finitely many eigenvalues (continuous functional
  calculus with the spectral indicators), and on the block `P_λ X P_μ` the transgression is the
  scalar `1 - λ̄ μ`; the minimal gap between distinct eigenvalues is a lower bound.
* An infinite spectrum yields either two distinct eigenvalues closer than any `c`, giving the
  rank-one witness `|x⟩⟨y|`, or a nonzero continuous subspace, whose approximate eigenvectors `u`
  give the almost fixed rank-one projection `|u⟩⟨u|`.  Both witnesses are Hilbert–Schmidt orthogonal
  to the fixed space, so the transgression is not bounded below there.
-/

open Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Approximate eigenvalues of a unitary -/

section ApproxPoint

variable {U : H ≃ₗᵢ[ℂ] H}

omit [CompleteSpace H] in
/-- `‖(z̄ - U*) x‖ = ‖(z - U) x‖`: a shifted unitary is normal. -/
theorem norm_conj_smul_sub_symm (U : H ≃ₗᵢ[ℂ] H) (z : ℂ) (x : H) :
    ‖(starRingEnd ℂ) z • x - U.symm x‖ = ‖z • x - U x‖ := by
  have h1 : ‖(starRingEnd ℂ) z • x - U.symm x‖ = ‖(starRingEnd ℂ) z • U x - x‖ := by
    rw [← U.norm_map, map_sub, map_smul, U.apply_symm_apply]
  rw [h1]
  have hre : RCLike.re ⟪(starRingEnd ℂ) z • U x, x⟫_ℂ = RCLike.re ⟪z • x, U x⟫_ℂ := by
    rw [inner_smul_left, inner_smul_left, Complex.conj_conj, ← inner_conj_symm (U x) x]
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hsq : ‖(starRingEnd ℂ) z • U x - x‖ ^ 2 = ‖z • x - U x‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ), norm_smul, norm_smul, Complex.norm_conj,
      U.norm_map, hre]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- **A shifted unitary bounded below is invertible.**  Its range is closed, and its orthogonal
complement is the kernel of the adjoint `z̄ - U*`, which is bounded below by the same constant. -/
theorem not_mem_spectrum_of_boundedBelow {z : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hbd : ∀ x : H, ε * ‖x‖ ≤ ‖z • x - U x‖) : z ∉ spectrum ℂ (unitaryCLM U) := by
  rw [spectrum.mem_iff, not_not]
  set A : H →L[ℂ] H := algebraMap ℂ (H →L[ℂ] H) z - unitaryCLM U
  have hA : ∀ x, A x = z • x - U x := fun x => by
    simp [A, Algebra.algebraMap_eq_smul_one]
  have hzero : ∀ y : H, ε * ‖y‖ ≤ 0 → y = 0 := fun y hy => by
    by_contra h
    have := mul_pos hε (norm_pos_iff.mpr h)
    linarith
  have hinj : Function.Injective A := by
    intro x y hxy
    have h := hbd (x - y)
    rw [smul_sub, map_sub, sub_sub_sub_comm, ← hA, ← hA, hxy, sub_self, norm_zero] at h
    exact sub_eq_zero.mp (hzero _ h)
  have hanti : AntilipschitzWith (Real.toNNReal ε⁻¹) A := by
    refine AddMonoidHomClass.antilipschitz_of_bound _ fun x => ?_
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hε.le), inv_mul_eq_div, le_div_iff₀ hε, mul_comm,
      hA]
    exact hbd x
  have hcl : IsClosed (LinearMap.range (A : H →ₗ[ℂ] H) : Set H) := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
    exact hanti.isClosed_range A.uniformContinuous
  haveI : CompleteSpace (LinearMap.range (A : H →ₗ[ℂ] H)) := hcl.completeSpace_coe
  have hperp : (LinearMap.range (A : H →ₗ[ℂ] H))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    have hadj : ∀ x, ⟪A x, y⟫_ℂ = ⟪x, (starRingEnd ℂ) z • y - U.symm y⟫_ℂ := by
      intro x
      rw [hA, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        ← U.inner_map_map x (U.symm y), U.apply_symm_apply]
    have h0 := hy _ ⟨(starRingEnd ℂ) z • y - U.symm y, rfl⟩
    rw [ContinuousLinearMap.coe_coe, hadj, inner_self_eq_zero, sub_eq_zero] at h0
    refine hzero y ?_
    have h := hbd y
    rw [← norm_conj_smul_sub_symm, ← h0, sub_self, norm_zero] at h
    exact h
  have hsurj : Function.Surjective A := by
    have htop := Submodule.orthogonal_eq_bot_iff.mp hperp
    exact LinearMap.range_eq_top.mp htop
  exact isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩

/-- The spectrum of a unitary lies on the unit circle. -/
theorem norm_eq_one_of_mem_spectrum {z : ℂ} (hz : z ∈ spectrum ℂ (unitaryCLM U)) : ‖z‖ = 1 := by
  by_contra h
  refine not_mem_spectrum_of_boundedBelow (ε := |‖z‖ - 1|)
    (abs_pos.mpr (sub_ne_zero.mpr h)) (fun x => ?_) hz
  have h1 := abs_norm_sub_norm_le (z • x) (U x)
  rw [norm_smul, U.norm_map, ← sub_one_mul, abs_mul, abs_norm] at h1
  exact h1

/-- **Spectral values of a unitary are approximate eigenvalues.** -/
theorem exists_approxEigen_of_mem_spectrum {z : ℂ} (hz : z ∈ spectrum ℂ (unitaryCLM U))
    {ε : ℝ} (hε : 0 < ε) : ∃ u : H, ‖u‖ = 1 ∧ ‖U u - z • u‖ ≤ ε := by
  by_contra h
  push Not at h
  refine not_mem_spectrum_of_boundedBelow hε (fun x => ?_) hz
  by_cases hx : x = 0
  · simp [hx]
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖(‖x‖ : ℂ)⁻¹ • x‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hx'.ne']
  have h1 := h _ hu
  have heq : U ((‖x‖ : ℂ)⁻¹ • x) - z • (‖x‖ : ℂ)⁻¹ • x = (‖x‖ : ℂ)⁻¹ • (U x - z • x) := by
    rw [map_smul, smul_sub, smul_comm z]
  rw [heq, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_eq_div,
    lt_div_iff₀ hx', norm_sub_rev] at h1
  exact h1.le

/-- A unitary of a nonzero Hilbert space has approximate eigenvectors with unimodular
approximate eigenvalues. -/
theorem hasApproxEigenvectors_of_nontrivial [Nontrivial H] (U : H ≃ₗᵢ[ℂ] H) :
    HasApproxEigenvectors U := by
  obtain ⟨z, hz⟩ := spectrum.nonempty (unitaryCLM U)
  intro ε hε
  obtain ⟨u, hu, hclose⟩ := exists_approxEigen_of_mem_spectrum hz hε
  exact ⟨u, z, hu, norm_eq_one_of_mem_spectrum hz, hclose⟩

/-- An eigenvalue of a unitary is a spectral value. -/
theorem mem_spectrum_of_mem_pointSpectrum {c : ℂ} (hc : c ∈ unitaryPointSpectrum U) :
    c ∈ spectrum ℂ (unitaryCLM U) := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  rw [spectrum.mem_iff, isUnit_iff_bijective]
  rintro ⟨hinj, -⟩
  refine hx0 (hinj ?_)
  simp [Algebra.algebraMap_eq_smul_one, mem_unitaryEigenspace.mp hx]

end ApproxPoint

end GaloisForLFunctions.HTGeometry
