import GaloisForLFunctions.RHTower.RepPointPairSmallEigen

/-!
# The Dirichlet form of a point-pair operator

For a nonnegative profile `φ` with kernel mass `m` and a continuous `ρ`-equivariant field `U`,
square-integrable on the modular cell `𝒟`,

  `∫_𝒟 ∫_ℍ φ(u(z, w)) ‖U(z) − U(w)‖² dμ(w) dμ(z) = 2m ∫_𝒟 ‖U‖² − 2 re ∫_𝒟 ⟪U, L_φ U⟫`

(`integral_dirichlet`).  Expanding the square, the term `∫_𝒟 ∫_ℍ φ(u(z, w)) ‖U(w)‖²` equals
`m ∫_𝒟 ‖U‖²` by the dual tiling of `ℍ` by translates of `𝒟` (`lintegral_fd_kernel_mul_invariant`),
since `‖U‖` is `SL(2, ℤ)`-invariant.  So `m − L_φ` is the Dirichlet form of the kernel `φ(u(z, w))`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology RCLike
open scoped MatrixGroups ENNReal InnerProductSpace

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type} [Fintype ι] {ρ : SL(2, ℤ) →* (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)}

section Kernel

variable {φ : ℝ → ℝ} {R : ℝ} (hφc : Continuous φ) (hφR : KernelSupport φ R)

include hφc hφR in
/-- A continuous function times the kernel at a fixed centre is integrable. -/
theorem integrable_kernel_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (z : ℍ)
    {g : ℍ → E} (hg : Continuous g) : Integrable (fun w => φ (pairU z w) • g w) := by
  refine ((hφc.comp (continuous_pairU_right z)).smul hg).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_pairU_le z R) fun w hw => ?_
  simp only [Set.mem_setOf_eq, not_le] at hw
  simp [hφR _ hw]

include hφc hφR in
/-- **Dual tiling.**  For a continuous `SL(2, ℤ)`-invariant `g`,
`∫⁻_𝒟 ∫⁻_ℍ φ(u(z, w)) g(w) = m ∫⁻_𝒟 g`. -/
theorem lintegral_fd_kernel_mul_invariant (hφ0 : ∀ u, 0 ≤ φ u) {g : ℍ → ℝ} (hg : Continuous g)
    (hginv : ∀ (B : SL(2, ℤ)) w, g (B • w) = g w) :
    ∫⁻ z in fd, ∫⁻ w, ENNReal.ofReal (φ (pairU z w) * g w) =
      ENNReal.ofReal (kernelMassR φ) * ∫⁻ z in fd, ENNReal.ofReal (g z) := by
  have hkm : ppKernelMass φ = ENNReal.ofReal (kernelMassR φ) := by
    have hint : Integrable (fun w : ℍ => φ (pairU UpperHalfPlane.I w)) := by
      simpa using integrable_kernel_mul hφc hφR UpperHalfPlane.I (g := fun _ => (1 : ℝ))
        continuous_const
    unfold ppKernelMass kernelMassR
    simp_rw [abs_of_nonneg (hφ0 _)]
    exact (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w => hφ0 _)).symm
  have hG : Measurable (fun z' : ℍ => ENNReal.ofReal (g z')) :=
    ENNReal.measurable_ofReal.comp hg.measurable
  have key : ∀ z : ℍ, 2 * ∫⁻ w, ENNReal.ofReal (φ (pairU z w) * g w) =
      ∑' B : SL(2, ℤ), ∫⁻ z' in fd, ENNReal.ofReal |φ (pairU z (B • z'))| *
        ENNReal.ofReal (g z') := by
    intro z
    rw [← tsum_lintegral_fd_smul (fun w => ENNReal.ofReal (φ (pairU z w) * g w))]
    refine tsum_congr fun B => lintegral_congr fun z' => ?_
    rw [hginv, abs_of_nonneg (hφ0 _), ENNReal.ofReal_mul (hφ0 _)]
  have h2 : 2 * ∫⁻ z in fd, ∫⁻ w, ENNReal.ofReal (φ (pairU z w) * g w) =
      2 * (ppKernelMass φ * ∫⁻ z' in fd, ENNReal.ofReal (g z')) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    simp_rw [key]
    rw [lintegral_tsum_kernel_mul hφc hG, mul_assoc]
  rw [← hkm]
  exact (ENNReal.mul_right_inj (by norm_num) ENNReal.ofNat_ne_top).1 h2

end Kernel


section Dirichlet

variable {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M) (hR : 0 ≤ R)
  (hφ0 : ∀ u, 0 ≤ φ u) (hφR : KernelSupport φ R)
  {U : ℍ → EuclideanSpace ℂ ι} (hUc : Continuous U) (hUe : IsEquivariant ρ U)

include hφc hφR hUc hUe in
/-- **The inner integral of the Dirichlet form**:
`∫_ℍ φ(u(z,w)) ‖U(z) − U(w)‖² = m ‖U(z)‖² − 2 re⟪U(z), (L_φU)(z)⟫ + ∫_ℍ φ(u(z,w)) ‖U(w)‖²`. -/
theorem integral_kernel_normSq_sub (z : ℍ) :
    ∫ w, φ (pairU z w) * ‖U z - U w‖ ^ 2 =
      kernelMassR φ * ‖U z‖ ^ 2 - 2 * re ⟪U z, ppApply ρ φ U z⟫_ℂ +
        ∫ w, φ (pairU z w) * ‖U w‖ ^ 2 := by
  have h1 : Integrable (fun w => φ (pairU z w) * ‖U z‖ ^ 2) := by
    simpa [smul_eq_mul] using integrable_kernel_mul hφc hφR z (g := fun _ => ‖U z‖ ^ 2)
      continuous_const
  have h2 : Integrable (fun w => φ (pairU z w) * (2 * re ⟪U z, U w⟫_ℂ)) := by
    simpa [smul_eq_mul] using integrable_kernel_mul hφc hφR z
      (g := fun w => 2 * re ⟪U z, U w⟫_ℂ)
      (continuous_const.mul (RCLike.continuous_re.comp (continuous_const.inner hUc)))
  have h3 : Integrable (fun w => φ (pairU z w) * ‖U w‖ ^ 2) := by
    simpa [smul_eq_mul] using integrable_kernel_mul hφc hφR z (hUc.norm.pow 2)
  have e : ∀ w, φ (pairU z w) * ‖U z - U w‖ ^ 2 = φ (pairU z w) * ‖U z‖ ^ 2 -
      φ (pairU z w) * (2 * re ⟪U z, U w⟫_ℂ) + φ (pairU z w) * ‖U w‖ ^ 2 := by
    intro w
    rw [norm_sub_sq (𝕜 := ℂ)]
    ring
  simp_rw [e]
  have h12 : Integrable (fun w => φ (pairU z w) * ‖U z‖ ^ 2 -
      φ (pairU z w) * (2 * re ⟪U z, U w⟫_ℂ)) := h1.sub h2
  rw [integral_add h12 h3, integral_sub h1 h2, integral_mul_const,
    integral_pairU_eq (fun u => φ u) z]
  congr 2
  have hint := integrable_pairKernel_smul hφc hφR hUc z
  rw [ppApply_eq_integral hφc hφR hUc hUe z, ← integral_inner hint, ← integral_re (hint.const_inner _),
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [inner_smul_right]
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
  ring

include hφc hφ0 hφR hUc hUe in
/-- **The averaged energy term**: `∫⁻_𝒟 ∫_ℍ φ(u(z, w)) ‖U(w)‖² = m ∫⁻_𝒟 ‖U‖²`. -/
theorem lintegral_kernel_normSq :
    ∫⁻ z in fd, ENNReal.ofReal (∫ w, φ (pairU z w) * ‖U w‖ ^ 2) =
      ENNReal.ofReal (kernelMassR φ) * ∫⁻ z in fd, ENNReal.ofReal (‖U z‖ ^ 2) := by
  have hg : Continuous (fun w : ℍ => ‖U w‖ ^ 2) := hUc.norm.pow 2
  have hginv : ∀ (B : SL(2, ℤ)) w, ‖U (B • w)‖ ^ 2 = ‖U w‖ ^ 2 := by
    intro B w
    rw [hUe, LinearIsometryEquiv.norm_map]
  rw [← lintegral_fd_kernel_mul_invariant hφc hφR hφ0 hg hginv]
  refine lintegral_congr fun z => ?_
  exact ofReal_integral_eq_lintegral_ofReal
    (by simpa [smul_eq_mul] using integrable_kernel_mul hφc hφR z hg)
    (Eventually.of_forall fun w => mul_nonneg (hφ0 _) (sq_nonneg _))

include hφc hφ0 hφR hUc hUe in
/-- The averaged energy term is integrable over the cell, with integral `m ∫_𝒟 ‖U‖²`. -/
theorem integrable_kernel_normSq (hU2 : MemLp U 2 cellMeasure) :
    Integrable (fun z => ∫ w, φ (pairU z w) * ‖U w‖ ^ 2) cellMeasure ∧
      ∫ z in fd, ∫ w, φ (pairU z w) * ‖U w‖ ^ 2 = kernelMassR φ * ∫ z in fd, ‖U z‖ ^ 2 := by
  have hJ0 : ∀ z, 0 ≤ ∫ w, φ (pairU z w) * ‖U w‖ ^ 2 := fun z =>
    integral_nonneg fun w => mul_nonneg (hφ0 _) (sq_nonneg _)
  have hJc : Continuous (fun q : ℍ × ℍ => φ (pairU q.1 q.2) * ‖U q.2‖ ^ 2) :=
    (hφc.comp continuous_pairU).mul ((hUc.comp continuous_snd).norm.pow 2)
  have hJm : AEStronglyMeasurable (fun z => ∫ w, φ (pairU z w) * ‖U w‖ ^ 2) cellMeasure :=
    hJc.aestronglyMeasurable.integral_prod_right'
  have hU2' : Integrable (fun z => ‖U z‖ ^ 2) cellMeasure :=
    (memLp_two_iff_integrable_sq_norm hU2.1).1 hU2
  have hlinU : ∫⁻ z in fd, ENNReal.ofReal (‖U z‖ ^ 2) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hU2' (Eventually.of_forall fun z => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  have hlinJ := lintegral_kernel_normSq hφc hφ0 hφR hUc hUe
  refine ⟨⟨hJm, ?_⟩, ?_⟩
  · rw [HasFiniteIntegral]
    have : ∫⁻ z, ‖∫ w, φ (pairU z w) * ‖U w‖ ^ 2‖ₑ ∂cellMeasure =
        ∫⁻ z in fd, ENNReal.ofReal (∫ w, φ (pairU z w) * ‖U w‖ ^ 2) := by
      refine lintegral_congr fun z => ?_
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hJ0 z)]
    rw [this, hlinJ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlinU.lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hJ0) hJm, hlinJ,
      ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (show 0 ≤ kernelMassR φ from integral_nonneg fun w => hφ0 _),
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => sq_nonneg _)
        hU2'.aestronglyMeasurable]

include hφc hφM hR hφR hUc in
/-- `re⟪U, L_φ U⟫` is integrable over the cell. -/
theorem integrable_re_inner_ppApply (hU2 : MemLp U 2 cellMeasure) :
    Integrable (fun z => re ⟪U z, ppApply ρ φ U z⟫_ℂ) cellMeasure := by
  have hU2' : Integrable (fun z => ‖U z‖ ^ 2) cellMeasure :=
    (memLp_two_iff_integrable_sq_norm hU2.1).1 hU2
  have hLU : MemLp (ppApply ρ φ U) 2 cellMeasure := memLp_ppApply hφc hφM hR hφR hU2
  have hLU2 : Integrable (fun z => ‖ppApply ρ φ U z‖ ^ 2) cellMeasure :=
    (memLp_two_iff_integrable_sq_norm hLU.1).1 hLU
  refine ((hU2'.add hLU2).div_const 2).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (RCLike.continuous_re.comp (hUc.inner
      (continuous_ppApply (ρ := ρ) hφc hφM hφR hU2))).aestronglyMeasurable
  · show ‖re ⟪U z, ppApply ρ φ U z⟫_ℂ‖ ≤ (‖U z‖ ^ 2 + ‖ppApply ρ φ U z‖ ^ 2) / 2
    rw [Real.norm_eq_abs]
    refine (abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    nlinarith [sq_nonneg (‖U z‖ - ‖ppApply ρ φ U z‖)]

include hφc hφM hR hφ0 hφR hUc hUe in
/-- The inner Dirichlet integral is integrable over the modular cell. -/
theorem integrable_dirichlet_inner (hU2 : MemLp U 2 cellMeasure) :
    Integrable (fun z => ∫ w, φ (pairU z w) * ‖U z - U w‖ ^ 2) cellMeasure := by
  simp_rw [integral_kernel_normSq_sub hφc hφR hUc hUe]
  have hU2' : Integrable (fun z => ‖U z‖ ^ 2) cellMeasure :=
    (memLp_two_iff_integrable_sq_norm hU2.1).1 hU2
  exact ((hU2'.const_mul _).sub ((integrable_re_inner_ppApply (ρ := ρ) hφc hφM hR hφR hUc hU2).const_mul
    _)).add (integrable_kernel_normSq hφc hφ0 hφR hUc hUe hU2).1

include hφc hφM hR hφ0 hφR hUc hUe in
/-- **The Dirichlet form identity**:
`∫_𝒟 ∫_ℍ φ(u(z,w)) ‖U(z) − U(w)‖² = 2m ∫_𝒟 ‖U‖² − 2 ∫_𝒟 re⟪U, L_φ U⟫`. -/
theorem integral_dirichlet (hU2 : MemLp U 2 cellMeasure) :
    ∫ z in fd, ∫ w, φ (pairU z w) * ‖U z - U w‖ ^ 2 =
      2 * kernelMassR φ * (∫ z in fd, ‖U z‖ ^ 2) -
        2 * ∫ z in fd, re ⟪U z, ppApply ρ φ U z⟫_ℂ := by
  simp_rw [integral_kernel_normSq_sub hφc hφR hUc hUe]
  have hU2' : Integrable (fun z => ‖U z‖ ^ 2) cellMeasure :=
    (memLp_two_iff_integrable_sq_norm hU2.1).1 hU2
  have hre := integrable_re_inner_ppApply (ρ := ρ) hφc hφM hR hφR hUc hU2
  obtain ⟨hJi, hJint⟩ := integrable_kernel_normSq hφc hφ0 hφR hUc hUe hU2
  have hA : Integrable (fun z => kernelMassR φ * ‖U z‖ ^ 2 -
      2 * re ⟪U z, ppApply ρ φ U z⟫_ℂ) cellMeasure := (hU2'.const_mul _).sub (hre.const_mul _)
  rw [integral_add hA hJi, integral_sub (hU2'.const_mul _) (hre.const_mul _), integral_const_mul,
    integral_const_mul, hJint]
  ring

end Dirichlet

end

end GaloisForLFunctions.RHTower.RepPointPair
