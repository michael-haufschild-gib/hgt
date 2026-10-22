import GaloisForLFunctions.HTGeometry.DuhamelScalarOscillator

/-!
# The evolution frequency by frequency

The Duhamel equation was solved in the space of weighted frequency data, as an identity between
bounded continuous functions. Evaluating it at a single frequency turns it into the scalar Duhamel
formula of the driven oscillator, because evaluation is a continuous linear map and therefore
commutes with the Bochner integral in the time variable.

The consequence is the equation the whole construction was aiming at: at every frequency the
evolution satisfies

`∂ₜ²û(t,ξ) = -⟨ξ⟩² û(t,ξ) + 𝓕(Vu(t))(ξ)`,

with the source term being exactly the convolution the operator produces. Nothing here needs the
potential to be small, and nothing restricts the time interval.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-- The source of the oscillator at a fixed frequency: the potential term of the evolution. -/
noncomputable def kgFlowSource (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E) (s : ℝ) : ℂ :=
  kgConv N (a.density s) (kgPotentialFlow a G₀ s) ξ

theorem continuous_kgFlowSource (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E) :
    Continuous (kgFlowSource a G₀ ξ) := by
  have h1 : Continuous fun s : ℝ => kgConvCLM (a.density s) (kgPotentialFlow a G₀ s) :=
    a.continuous_convCLM.clm_apply (continuous_kgPotentialFlow a G₀)
  exact (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) ξ).continuous.comp h1

/-- **The evolution at a fixed frequency is the Duhamel solution of the driven oscillator.** -/
theorem kgPotentialFlow_apply_eq_duhamel (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E) (t : ℝ) :
    kgPotentialFlow a G₀ t ξ
      = duhamelScalar (kgFreq ξ) (G₀ ξ) (kgFlowSource a G₀ ξ) t := by
  have hsymb : Continuous fun s : ℝ => kgSincBCF (E := E) (t - s) :=
    continuous_kgSincBCF.comp (continuous_const.sub continuous_id)
  have hmul : Continuous fun s : ℝ => kgMulCLM (kgSincBCF (E := E) (t - s)) :=
    (ContinuousLinearMap.mul ℝ (E →ᵇ ℂ)).continuous.comp hsymb
  have hK : Continuous fun s : ℝ => kgDuhamelKernel a t s :=
    ((ContinuousLinearMap.compL ℝ (E →ᵇ ℂ) (E →ᵇ ℂ) (E →ᵇ ℂ)).continuous.comp hmul).clm_apply
      a.continuous_convCLM
  have hcont : Continuous fun s : ℝ => kgDuhamelKernel a t s (kgPotentialFlow a G₀ s) :=
    hK.clm_apply (continuous_kgPotentialFlow a G₀)
  have hint : IntervalIntegrable
      (fun s : ℝ => kgDuhamelKernel a t s (kgPotentialFlow a G₀ s)) volume 0 t :=
    hcont.intervalIntegrable (μ := volume) 0 t
  have heval :
      (∫ s in (0 : ℝ)..t, (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) ξ)
          (kgDuhamelKernel a t s (kgPotentialFlow a G₀ s)))
        = (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) ξ)
            (∫ s in (0 : ℝ)..t, kgDuhamelKernel a t s (kgPotentialFlow a G₀ s)) :=
    ContinuousLinearMap.intervalIntegral_comp_comm _ hint
  simp only [BoundedContinuousFunction.evalCLM_apply] at heval
  rw [kgPotentialFlow_eq a G₀ t, BoundedContinuousFunction.add_apply, kgFreeTerm_apply,
    ← heval, duhamelScalar]
  congr 1

/-- **The evolution solves the driven oscillator equation at every frequency.** -/
theorem hasDerivAt_deriv_kgPotentialFlow_apply (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E)
    (t : ℝ) :
    HasDerivAt (deriv fun r : ℝ => kgPotentialFlow a G₀ r ξ)
      (-(((kgFreq ξ : ℝ) : ℂ) ^ (2 : ℕ) * kgPotentialFlow a G₀ t ξ) + kgFlowSource a G₀ ξ t) t := by
  have hfun : (fun r : ℝ => kgPotentialFlow a G₀ r ξ)
      = duhamelScalar (kgFreq ξ) (G₀ ξ) (kgFlowSource a G₀ ξ) := by
    funext r
    exact kgPotentialFlow_apply_eq_duhamel a G₀ ξ r
  have hmain := hasDerivAt_deriv_duhamelScalar (ω := kgFreq ξ) (c := G₀ ξ)
    (h := kgFlowSource a G₀ ξ) (kgFreq_pos ξ).ne' (continuous_kgFlowSource a G₀ ξ) t
  rw [hfun]
  refine hmain.congr_deriv ?_
  rw [kgPotentialFlow_apply_eq_duhamel a G₀ ξ t]

/-- The first time derivative at a fixed frequency. -/
theorem hasDerivAt_kgPotentialFlow_apply (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => kgPotentialFlow a G₀ r ξ)
      (-(((Real.sin (t * kgFreq ξ) : ℝ) : ℂ) * G₀ ξ)
        + ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ) * duhamelCosPart (kgFreq ξ) (kgFlowSource a G₀ ξ) t
        + ((Real.sin (t * kgFreq ξ) : ℝ) : ℂ)
            * duhamelSinPart (kgFreq ξ) (kgFlowSource a G₀ ξ) t) t := by
  have hfun : (fun r : ℝ => kgPotentialFlow a G₀ r ξ)
      = duhamelScalar (kgFreq ξ) (G₀ ξ) (kgFlowSource a G₀ ξ) := by
    funext r
    exact kgPotentialFlow_apply_eq_duhamel a G₀ ξ r
  rw [hfun]
  exact hasDerivAt_duhamelScalar (kgFreq_pos ξ).ne' (continuous_kgFlowSource a G₀ ξ) t

end GaloisForLFunctions.HTGeometry
