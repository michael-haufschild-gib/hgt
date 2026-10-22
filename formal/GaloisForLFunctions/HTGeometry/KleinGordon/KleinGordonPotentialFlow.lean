import GaloisForLFunctions.HTGeometry.WienerDensityFamily
import GaloisForLFunctions.HTGeometry.WienerSymbolMultiplication
import GaloisForLFunctions.HTGeometry.VolterraLinearIntegralEquation

/-!
# The Klein–Gordon evolution with a potential, on the frequency side

Everything the Volterra theory asks for is now available. The Duhamel kernel of the equation

`∂ₜ²u = (2π)⁻²Δu - u + Vu`

is, on the frequency side, the damped sine propagator composed with convolution by the transform of
the potential:

`K(t,s) = (multiplication by sin((t-s)⟨ξ⟩)/⟨ξ⟩) ∘ (convolution by 𝓕V)`.

Both factors are bounded — the first by `1` for *every* pair of times, the second by Peetre's
inequality — so the kernel is uniformly bounded on the whole time axis, and the Volterra solution
exists globally with no smallness hypothesis and no restriction to a bounded time interval.

The free term is the damped cosine propagator applied to the datum. The damping is what makes the
family continuous in time in the operator norm, and it is the reason the datum is represented with
one extra power of the weight.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-! ## The Duhamel kernel -/

/-- The Duhamel kernel: propagate from `s` to `t` with the damped sine, after multiplying by the
potential — which on the frequency side is convolution by its transform. -/
noncomputable def kgDuhamelKernel (a : WienerFamily E N) (t s : ℝ) :
    (E →ᵇ ℂ) →L[ℝ] (E →ᵇ ℂ) :=
  (kgMulCLM (kgSincBCF (t - s))).comp (kgConvCLM (a.density s))

theorem norm_kgDuhamelKernel_le (a : WienerFamily E N) (t s : ℝ) :
    ‖kgDuhamelKernel a t s‖ ≤ Real.sqrt 2 ^ N * a.bound := by
  have hcomp := ContinuousLinearMap.opNorm_comp_le (kgMulCLM (kgSincBCF (E := E) (t - s)))
    (kgConvCLM (a.density s))
  refine hcomp.trans ?_
  have h1 : ‖kgMulCLM (kgSincBCF (E := E) (t - s))‖ ≤ 1 :=
    (norm_kgMulCLM_le _).trans (norm_kgSincBCF_le _)
  have h2 : ‖kgConvCLM (a.density s)‖ ≤ Real.sqrt 2 ^ N * a.bound := a.norm_convCLM_le s
  have h3 : (0 : ℝ) ≤ ‖kgConvCLM (a.density s)‖ := norm_nonneg _
  nlinarith [norm_nonneg (kgMulCLM (kgSincBCF (E := E) (t - s)))]

theorem continuous_kgDuhamelKernel (a : WienerFamily E N) :
    Continuous fun p : ℝ × ℝ => kgDuhamelKernel a p.1 p.2 := by
  have hsymb : Continuous fun p : ℝ × ℝ => kgSincBCF (E := E) (p.1 - p.2) :=
    continuous_kgSincBCF.comp (continuous_fst.sub continuous_snd)
  have hmul : Continuous fun p : ℝ × ℝ => kgMulCLM (kgSincBCF (E := E) (p.1 - p.2)) :=
    (ContinuousLinearMap.mul ℝ (E →ᵇ ℂ)).continuous.comp hsymb
  have hcompL : Continuous fun p : ℝ × ℝ =>
      (ContinuousLinearMap.compL ℝ (E →ᵇ ℂ) (E →ᵇ ℂ) (E →ᵇ ℂ))
        (kgMulCLM (kgSincBCF (E := E) (p.1 - p.2))) :=
    (ContinuousLinearMap.compL ℝ (E →ᵇ ℂ) (E →ᵇ ℂ) (E →ᵇ ℂ)).continuous.comp hmul
  exact hcompL.clm_apply (a.continuous_convCLM.comp continuous_snd)

/-! ## The free term -/

/-- The free term of the Duhamel equation: the damped cosine propagator applied to the datum. -/
noncomputable def kgFreeTerm (G₀ : E →ᵇ ℂ) (t : ℝ) : E →ᵇ ℂ := kgMulCLM (kgCoscBCF t) G₀

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_kgFreeTerm_le (G₀ : E →ᵇ ℂ) (t : ℝ) : ‖kgFreeTerm G₀ t‖ ≤ ‖G₀‖ := by
  rw [kgFreeTerm]
  have h := (kgMulCLM (kgCoscBCF (E := E) t)).le_opNorm G₀
  have h1 : ‖kgMulCLM (kgCoscBCF (E := E) t)‖ ≤ 1 :=
    (norm_kgMulCLM_le _).trans (norm_kgCoscBCF_le _)
  nlinarith [norm_nonneg G₀, norm_nonneg (kgMulCLM (kgCoscBCF (E := E) t))]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_kgFreeTerm (G₀ : E →ᵇ ℂ) : Continuous (kgFreeTerm G₀) := by
  have hmul : Continuous fun t : ℝ => kgMulCLM (kgCoscBCF (E := E) t) :=
    (ContinuousLinearMap.mul ℝ (E →ᵇ ℂ)).continuous.comp continuous_kgCoscBCF
  exact hmul.clm_apply continuous_const

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kgFreeTerm_apply (G₀ : E →ᵇ ℂ) (t : ℝ) (ξ : E) :
    kgFreeTerm G₀ t ξ = ((Real.cos (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ) * G₀ ξ := rfl

/-! ## The evolution -/

/-- **The Klein–Gordon evolution with a potential**, on the frequency side: the solution of the
Duhamel integral equation. -/
noncomputable def kgPotentialFlow (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) : ℝ → (E →ᵇ ℂ) :=
  volterraSolution (kgFreeTerm G₀) (kgDuhamelKernel a)

theorem continuous_kgPotentialFlow (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) :
    Continuous (kgPotentialFlow a G₀) := by
  refine continuous_volterraSolution (M := Real.sqrt 2 ^ N * a.bound) (F := ‖G₀‖)
    (continuous_kgFreeTerm G₀) (continuous_kgDuhamelKernel a) ?_ (norm_nonneg _)
    (norm_kgDuhamelKernel_le a) (norm_kgFreeTerm_le G₀)
  exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) N) a.bound_nonneg

/-- **The evolution solves the Duhamel equation.** -/
theorem kgPotentialFlow_eq (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) :
    kgPotentialFlow a G₀ t
      = kgFreeTerm G₀ t + ∫ s in (0 : ℝ)..t, kgDuhamelKernel a t s (kgPotentialFlow a G₀ s) := by
  refine volterraSolution_eq (M := Real.sqrt 2 ^ N * a.bound) (F := ‖G₀‖)
    (continuous_kgFreeTerm G₀) (continuous_kgDuhamelKernel a) ?_ (norm_nonneg _)
    (norm_kgDuhamelKernel_le a) (norm_kgFreeTerm_le G₀) t
  exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) N) a.bound_nonneg

/-- **The evolution starts at the datum**, damped by one power of the frequency. -/
theorem kgPotentialFlow_zero (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E) :
    kgPotentialFlow a G₀ 0 ξ = ((kgFreq ξ : ℝ) : ℂ)⁻¹ * G₀ ξ := by
  rw [kgPotentialFlow_eq]
  rw [intervalIntegral.integral_same, add_zero, kgFreeTerm_apply]
  norm_num

/-- **The evolution is the only continuous solution of the Duhamel equation.** -/
theorem kgPotentialFlow_unique (a : WienerFamily E N) (G₀ : E →ᵇ ℂ) {u : ℝ → (E →ᵇ ℂ)}
    (hu : Continuous u)
    (heq : ∀ t : ℝ, u t = kgFreeTerm G₀ t
      + ∫ s in (0 : ℝ)..t, kgDuhamelKernel a t s (u s)) :
    u = kgPotentialFlow a G₀ := by
  refine volterra_eq_of_eq_of_eq (M := Real.sqrt 2 ^ N * a.bound)
    (continuous_kgDuhamelKernel a) ?_ (norm_kgDuhamelKernel_le a) hu
    (continuous_kgPotentialFlow a G₀) heq (kgPotentialFlow_eq a G₀)
  exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) N) a.bound_nonneg

end GaloisForLFunctions.HTGeometry
