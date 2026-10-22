import GaloisForLFunctions.RHTower.Deninger.DeningerAdiabaticGammaEndpoint

/-!
# Cofinal Green--Stokes transgression

The strict local Green--Stokes derivative is integrated on every finite positive collar.  Local
continuity of the Euler flux follows from the same summable logarithmic majorant used for
differentiation.  Sending the upper wall to infinity and the lower wall to zero then gives an
unconditional, weak Pettis characterization of the full transgression between the Gamma and
Möbius boundaries.
-/

namespace RHTower

open Filter Topology MeasureTheory SchwartzMap FourierTransform ArithmeticFunction

noncomputable section

theorem continuous_deningerAdiabaticMobiusDerivativeScalar (n : ℕ) :
    Continuous (deningerAdiabaticMobiusDerivativeScalar n) := by
  unfold deningerAdiabaticMobiusDerivativeScalar deningerAdiabaticMobiusCoefficient
  fun_prop

theorem continuous_deningerAdiabaticMobiusDerivativeTermLp
    (h : DeningerMeyerSource) (n : ℕ) :
    Continuous (deningerAdiabaticMobiusDerivativeTermLp h n) := by
  by_cases hn : 0 < n
  · have heq : deningerAdiabaticMobiusDerivativeTermLp h n =
        fun a : ℝ => deningerAdiabaticMobiusDerivativeScalar n a •
          deningerAdiabaticEvenLogPullDilationLp h n hn := by
      funext a
      simp only [deningerAdiabaticMobiusDerivativeTermLp, dif_pos hn]
    rw [heq]
    exact (continuous_deningerAdiabaticMobiusDerivativeScalar n).smul
      continuous_const
  · have heq : deningerAdiabaticMobiusDerivativeTermLp h n =
        fun _ : ℝ => (0 : Lp ℂ (1 : ENNReal) (volume : Measure ℝ)) := by
      funext a
      simp only [deningerAdiabaticMobiusDerivativeTermLp, dif_neg hn]
    rw [heq]
    exact continuous_const

/-- The Banach-valued Euler output varies continuously at every positive adiabatic parameter. -/
theorem continuousAt_deningerAdiabaticEulerPositiveLp
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    ContinuousAt (fun b : ℝ => deningerAdiabaticEulerPositiveLp b h) a := by
  let d : ℝ := a / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hda : d < a := by dsimp [d]; linarith
  have hsum : Tendsto
      (fun b : ℝ => ∑' n : ℕ, deningerAdiabaticMobiusDerivativeTermLp h n b)
      (𝓝 a)
      (𝓝 (∑' n : ℕ, deningerAdiabaticMobiusDerivativeTermLp h n a)) :=
    tendsto_tsum_of_dominated_convergence
      (summable_deningerAdiabaticDerivativeMajorant hd h)
      (fun n => (continuous_deningerAdiabaticMobiusDerivativeTermLp h n).continuousAt)
      (by
        filter_upwards [Ioi_mem_nhds hda] with b hb
        exact fun n => norm_deningerAdiabaticMobiusDerivativeTermLp_le hd hb.le h n)
  change Tendsto
    (fun b : ℝ => ∑' n : ℕ, deningerAdiabaticMobiusDerivativeTermLp h n b)
    (𝓝 a) (𝓝 (∑' n : ℕ, deningerAdiabaticMobiusDerivativeTermLp h n a))
  exact hsum

/-- Every Schwartz component of the Green--Stokes flux is continuous on the positive collar. -/
theorem continuousOn_deningerAdiabaticGreenStokesFluxPairing
    (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    ContinuousOn (fun a : ℝ => deningerAdiabaticGreenStokesFluxPairing a h g)
      (Set.Ioi 0) := by
  intro a ha
  have hfirst := (deningerL1SchwartzPairing (𝓕 g)).continuous.continuousAt.tendsto.comp
    (continuousAt_deningerAdiabaticEulerPositiveLp ha h)
  have hsecond := (deningerL1SchwartzPairing g).continuous.continuousAt.tendsto.comp
    (continuousAt_deningerAdiabaticEulerPositiveLp ha
      (deningerMeyerCollarExchange h))
  apply ContinuousAt.continuousWithinAt
  show Tendsto
    (fun b : ℝ => deningerAdiabaticGreenStokesFluxPairing b h g) (𝓝 a)
    (𝓝 (deningerAdiabaticGreenStokesFluxPairing a h g))
  have hsub := hfirst.sub hsecond
  simpa only [deningerAdiabaticGreenStokesFluxPairing, Function.comp_apply] using hsub

/-- Pairing-level form of the strict Green--Stokes derivative. -/
theorem hasDerivAt_deningerAdiabaticMobiusBoundaryPairing_strict
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    HasDerivAt (fun b : ℝ => deningerAdiabaticMobiusBoundaryPairing b h g)
      (deningerAdiabaticGreenStokesFluxPairing a h g) a := by
  simpa only [deningerAdiabaticMobiusBoundaryPairing,
    deningerAdiabaticGreenStokesFluxPairing,
    deningerAdiabaticBoundaryPairingCLM_apply] using
      hasDerivAt_deningerAdiabaticMobiusBoundaryPairing ha h g

/-- **Finite positive-collar Green--Stokes theorem.** -/
theorem integral_deningerAdiabaticGreenStokesFluxPairing
    {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R)
    (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    (∫ a in ε..R, deningerAdiabaticGreenStokesFluxPairing a h g) =
      deningerAdiabaticMobiusBoundaryPairing R h g -
        deningerAdiabaticMobiusBoundaryPairing ε h g := by
  have hsub : Set.uIcc ε R ⊆ Set.Ioi (0 : ℝ) := by
    rw [Set.uIcc_of_le hεR]
    intro a ha
    exact lt_of_lt_of_le hε ha.1
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun a ha => hasDerivAt_deningerAdiabaticMobiusBoundaryPairing_strict
      (hsub ha) h g)
    ((continuousOn_deningerAdiabaticGreenStokesFluxPairing h g).mono hsub).intervalIntegrable

/-- Evaluation of the Gamma boundary is the upper endpoint of every paired strict boundary. -/
theorem tendsto_deningerAdiabaticMobiusBoundaryPairing_atTop
    (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    Tendsto (fun a : ℝ => deningerAdiabaticMobiusBoundaryPairing a h g) atTop
      (𝓝 (deningerAdiabaticGammaBoundary h g)) := by
  have hraw :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ g).continuous.continuousAt.tendsto.comp
      (tendsto_deningerAdiabaticMobiusBoundaryExt_atTop h)
  have hraw' : Tendsto
      (fun a : ℝ => deningerAdiabaticMobiusBoundaryExt a h g) atTop
      (𝓝 (deningerAdiabaticGammaBoundary h g)) := by
    convert hraw using 1
    · funext a
      rfl
    · rfl
  simpa only [deningerAdiabaticMobiusBoundaryExt_apply_eq_pairing] using hraw'

/-- Evaluation of the strict boundary tends to the literal critical Möbius commutator. -/
theorem tendsto_deningerAdiabaticMobiusBoundaryPairing_atBot
    (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    Tendsto
      (fun a : Set.Ioi (0 : ℝ) => deningerAdiabaticMobiusBoundaryPairing a h g)
      atBot (𝓝 (deningerMobiusCommutator (DeningerMeyerSource.toSource h) g)) := by
  have hraw :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ g).continuous.continuousAt.tendsto.comp
      (tendsto_deningerAdiabaticMobiusBoundaryExt_atBot h)
  have hraw' : Tendsto
      (fun a : Set.Ioi (0 : ℝ) => deningerAdiabaticMobiusBoundaryExt a h g) atBot
      (𝓝 (deningerMobiusCommutator (DeningerMeyerSource.toSource h) g)) := by
    convert hraw using 1
    · funext a
      rfl
    · rfl
  simpa only [deningerAdiabaticMobiusBoundaryExt_apply_eq_pairing] using hraw'

/-- Distribution represented by the cofinal weak Green--Stokes integral. -/
def deningerAdiabaticGreenStokesTransgression
    (h : DeningerMeyerSource) : 𝓢'(ℝ, ℂ) :=
  deningerAdiabaticGammaBoundary h -
    deningerMobiusCommutator (DeningerMeyerSource.toSource h)

@[simp]
theorem deningerAdiabaticGreenStokesTransgression_apply
    (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    deningerAdiabaticGreenStokesTransgression h g =
      deningerAdiabaticGammaBoundary h g -
        deningerMobiusCommutator (DeningerMeyerSource.toSource h) g := by
  rfl

/-- For each positive lower wall, finite flux integrals converge to the corresponding upper
Gamma-relative boundary. -/
theorem tendsto_integral_deningerAdiabaticGreenStokesFluxPairing_atTop
    {ε : ℝ} (hε : 0 < ε) (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    Tendsto
      (fun R : ℝ => ∫ a in ε..R, deningerAdiabaticGreenStokesFluxPairing a h g)
      atTop
      (𝓝 (deningerAdiabaticGammaBoundary h g -
        deningerAdiabaticMobiusBoundaryPairing ε h g)) := by
  have hlimit := (tendsto_deningerAdiabaticMobiusBoundaryPairing_atTop h g).sub
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => deningerAdiabaticMobiusBoundaryPairing ε h g) atTop
      (𝓝 (deningerAdiabaticMobiusBoundaryPairing ε h g)))
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop ε] with R hεR
  exact (integral_deningerAdiabaticGreenStokesFluxPairing hε hεR h g).symm

/-- The upper-integrated flux converges at the critical lower wall to the endpoint difference. -/
theorem tendsto_deningerAdiabaticUpperIntegratedFlux_atBot
    (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    Tendsto
      (fun ε : Set.Ioi (0 : ℝ) =>
        deningerAdiabaticGammaBoundary h g -
          deningerAdiabaticMobiusBoundaryPairing ε h g)
      atBot (𝓝 (deningerAdiabaticGreenStokesTransgression h g)) := by
  have hlimit := (tendsto_const_nhds : Tendsto
      (fun _ : Set.Ioi (0 : ℝ) => deningerAdiabaticGammaBoundary h g) atBot
      (𝓝 (deningerAdiabaticGammaBoundary h g))).sub
    (tendsto_deningerAdiabaticMobiusBoundaryPairing_atBot h g)
  simpa only [deningerAdiabaticGreenStokesTransgression_apply] using hlimit

/-- **Cofinal weak Pettis Green--Stokes theorem.**  Every Schwartz component has the same
iterated improper integral, and that component is exactly the canonical distributional endpoint
difference. -/
theorem deningerAdiabaticGreenStokesTransgression_cofinal
    (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    (∀ ε : Set.Ioi (0 : ℝ),
      Tendsto
        (fun R : ℝ => ∫ a in (ε : ℝ)..R,
          deningerAdiabaticGreenStokesFluxPairing a h g)
        atTop
        (𝓝 (deningerAdiabaticGammaBoundary h g -
          deningerAdiabaticMobiusBoundaryPairing ε h g))) ∧
    Tendsto
      (fun ε : Set.Ioi (0 : ℝ) =>
        deningerAdiabaticGammaBoundary h g -
          deningerAdiabaticMobiusBoundaryPairing ε h g)
      atBot (𝓝 (deningerAdiabaticGreenStokesTransgression h g)) := by
  exact ⟨fun ε => tendsto_integral_deningerAdiabaticGreenStokesFluxPairing_atTop
    ε.property h g, tendsto_deningerAdiabaticUpperIntegratedFlux_atBot h g⟩

/-- **Strict source-to-physical chain-map descent.**  The critical Möbius boundary is the Gamma
boundary minus the canonical cofinal Green--Stokes transgression. -/
theorem XI_BV_GREEN_STOKES_STRICT_DESCENT (h : DeningerMeyerSource) :
    deningerMobiusCommutator (DeningerMeyerSource.toSource h) =
      deningerAdiabaticGammaBoundary h -
        deningerAdiabaticGreenStokesTransgression h := by
  rw [deningerAdiabaticGreenStokesTransgression]
  abel

end

end RHTower
