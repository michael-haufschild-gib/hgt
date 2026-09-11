import GaloisForLFunctions.RHTower.BurnolCoPoissonNormalizedSourceRadialBias
import GaloisForLFunctions.RHTower.BurnolSoninCompletedJetBridge

/-!
# Fourier transport out of the leading co-Poisson jet kernel

A literal combination of the logarithmic window and its Fourier partner
kills the original first nonzero completed Mellin derivative. Its Fourier
image has an exact nonzero derivative on the strict right half of the strip,
with a lower bound retaining both normalization factors. Both vectors lie
in the algebraic co-Poisson source before closure.
-/

open Real Complex Set
namespace RHTower
noncomputable section


/-- The literal window combination that kills its original leading completed jet. -/
def burnolWindowTopJetKernelWitness (L : ℝ) (hL : 0 < L)
    (rho : XiDivisorSupport) : evenSubspace :=
  let f := coPoissonSubWindowEven (Real.exp_pos (-L))
    (Real.exp_le_one_iff.mpr (by linarith : -L ≤ 0))
  burnolWindowFourierCompletedTopJet L hL rho • f -
    burnolWindowCompletedTopJet L hL rho • soninCosineUnitary f

/-- Both evaluations are literal completed derivatives at the unchanged divisor. -/
theorem burnolWindowTopJetKernelWitness_exact_jets
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport)
    (hr : 1 / 2 < (rho : ℂ).re) :
    let V := burnolWindowTopJetKernelWitness L hL rho
    V ∈ soninExtendedSpace (subWindowAperture (Real.exp (-L)) 1) ∧
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (fun w : ℂ => soninMellinEvaluation w (V : SoninL2)) (rho : ℂ) = 0 ∧
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (fun w : ℂ => soninMellinEvaluation w (soninCosineUnitary V : SoninL2))
        (rho : ℂ) =
      burnolWindowFourierCompletedTopJet L hL rho ^ 2 -
        burnolWindowCompletedTopJet L hL rho ^ 2 := by
  let hc := Real.exp_pos (-L)
  have hcd : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  let a := subWindowAperture (Real.exp (-L)) 1
  have ha : 0 < a := subWindowAperture_pos hc hcd
  obtain ⟨ell, hell⟩ := exists_soninExtendedCompletedMellinJetEvaluator ha
    (burnolCoPoissonXiConormalOrder rho) hr (xi_divisor_support_re_mem_open_unit rho).2
  let f : soninExtendedSpace a := coPoissonSubWindowSonin hc hcd
  let g : soninExtendedSpace a :=
    ⟨soninCosineUnitary (f : evenSubspace), soninCosineUnitary_mem_soninExtendedSpace f.property⟩
  let J := burnolWindowCompletedTopJet L hL rho
  let K := burnolWindowFourierCompletedTopJet L hL rho
  let v : soninExtendedSpace a := K • f - J • g
  have hv : (v : evenSubspace) = burnolWindowTopJetKernelWitness L hL rho := rfl
  have hf : ell f = J := hell f
  have hg : ell g = K := hell g
  have hfv : soninCosineUnitary (v : evenSubspace) =
      ((K • g - J • f : soninExtendedSpace a) : evenSubspace) := by
    change soninCosineUnitary (K • (f : evenSubspace) - J • soninCosineUnitary f) =
      K • soninCosineUnitary f - J • (f : evenSubspace)
    rw [map_sub, map_smul, map_smul, soninCosineUnitary_involutive]
  dsimp only
  rw [← hv]
  refine ⟨v.property, ?_, ?_⟩
  · rw [← hell v]
    simp only [v, map_sub, map_smul, hf, hg, smul_eq_mul]
    ring
  · rw [hfv, ← hell (K • g - J • f)]
    simp only [map_sub, map_smul, hf, hg, smul_eq_mul]
    dsimp only [J, K]
    ring

/-- The Fourier image of the actual kernel witness has nonzero leading derivative
on the strict right half, so the actual leading-jet kernel is not Fourier invariant. -/
theorem burnolWindowTopJetKernelWitness_fourier_jet_ne_zero
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport)
    (hr : 1 / 2 < (rho : ℂ).re) :
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (fun w : ℂ => soninMellinEvaluation w
          (soninCosineUnitary (burnolWindowTopJetKernelWitness L hL rho) : SoninL2))
        (rho : ℂ) ≠ 0 := by
  rw [(burnolWindowTopJetKernelWitness_exact_jets hL rho hr).2.2]
  intro hzero
  have heq := congrArg norm (sub_eq_zero.mp hzero)
  simp only [norm_pow] at heq
  have hnorm := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp heq
  have hline := (burnolWindowCompletedTopJets_norm_eq_iff hL rho).mp hnorm.symm
  linarith

/-- The witness and its Fourier image lie in the literal algebraic source,
before taking any source closure. -/
theorem burnolWindowTopJetKernelWitness_mem_algebraicSource
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    burnolWindowTopJetKernelWitness L hL rho ∈
        burnolCoPoissonAlgebraicSourceSpace (subWindowAperture (Real.exp (-L)) 1) ∧
      soninCosineUnitary (burnolWindowTopJetKernelWitness L hL rho) ∈
        burnolCoPoissonAlgebraicSourceSpace (subWindowAperture (Real.exp (-L)) 1) := by
  let hc := Real.exp_pos (-L)
  have hcd : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  let a := subWindowAperture (Real.exp (-L)) 1
  let f := coPoissonSubWindowEven hc hcd
  have hf : f ∈ burnolCoPoissonAlgebraicSourceSpace a :=
    Submodule.subset_span ⟨coPoissonSubWindowSource hc hcd, Or.inl rfl⟩
  have hg := soninCosineUnitary_mem_coPoissonAlgebraicSourceSpace hf
  have hv : burnolWindowTopJetKernelWitness L hL rho ∈
      burnolCoPoissonAlgebraicSourceSpace a :=
    (burnolCoPoissonAlgebraicSourceSpace a).sub_mem
      ((burnolCoPoissonAlgebraicSourceSpace a).smul_mem _ hf)
      ((burnolCoPoissonAlgebraicSourceSpace a).smul_mem _ hg)
  exact ⟨hv, soninCosineUnitary_mem_coPoissonAlgebraicSourceSpace hv⟩

/-- The surviving Fourier derivative exceeds the physical radial gain times
the squared amplitude of the unchanged Fourier normalization factor. -/
theorem burnolWindowTopJetKernelWitness_fourier_jet_lower_bound
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport)
    (hr : 1 / 2 < (rho : ℂ).re) :
    (Real.exp (L * (2 * (rho : ℂ).re - 1)) - 1) *
        ‖burnolWindowFourierCompletedTopJet L hL rho‖ ^ 2 <
      ‖iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (fun w : ℂ => soninMellinEvaluation w
          (soninCosineUnitary (burnolWindowTopJetKernelWitness L hL rho) : SoninL2))
        (rho : ℂ)‖ := by
  rw [(burnolWindowTopJetKernelWitness_exact_jets hL rho hr).2.2]
  have hb := norm_sub_norm_le
    (burnolWindowCompletedTopJet L hL rho ^ 2)
    (burnolWindowFourierCompletedTopJet L hL rho ^ 2)
  rw [norm_pow, norm_pow, norm_sub_rev] at hb
  have hs := burnolWindowCompletedTopJets_strict_radial_bias hL rho hr
  nlinarith

end
end RHTower
