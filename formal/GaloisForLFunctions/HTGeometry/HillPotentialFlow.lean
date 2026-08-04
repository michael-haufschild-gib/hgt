import GaloisForLFunctions.HTGeometry.HillPropagatorMultiplier
import GaloisForLFunctions.HTGeometry.VolterraWindowedEquation
import GaloisForLFunctions.HTGeometry.WienerDensityFamily
import GaloisForLFunctions.HTGeometry.DuhamelVariableOscillator

/-!
# The driven evolution of a variable speed, on the frequency side

A potential is multiplication in space, hence convolution in the frequency, so the fibres of the
evolution no longer decouple. The Duhamel equation

`û(t) = C(t)/ω(0) · G₀ + ∫₀ᵗ P(t,s) (a_s * û(s)) ds`

is a Volterra equation in the space of bounded continuous functions of the frequency, whose kernel is
the propagator of the free fibre followed by convolution with the transform of the potential.

Both factors are bounded on every window of times — uniformly in the frequency — and continuous, so
the windowed Volterra theory produces the solution on the whole line, with no smallness hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

section Flow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-- The Duhamel kernel of the driven evolution: propagate from `s` to `t`, after convolving with the
transform of the potential. -/
noncomputable def hillDuhamelKernel (a : HillSpeed) (b : WienerFamily E N) (t s : ℝ) :
    (E →ᵇ ℂ) →L[ℝ] (E →ᵇ ℂ) :=
  (kgMulCLM (a.propBCF t s)).comp (kgConvCLM (b.density s))

/-- The free term: the damped free symbol applied to the datum. -/
noncomputable def hillFreeTerm (a : HillSpeed) (G₀ : E →ᵇ ℂ) (t : ℝ) : E →ᵇ ℂ :=
  kgMulCLM (a.coscBCF t) G₀

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hillFreeTerm_apply (a : HillSpeed) (G₀ : E →ᵇ ℂ) (t : ℝ) (ξ : E) :
    hillFreeTerm a G₀ t ξ = ((a.coscSymbol t ξ : ℝ) : ℂ) * G₀ ξ := rfl

theorem norm_hillDuhamelKernel_le_window (a : HillSpeed) (b : WienerFamily E N) {T t s : ℝ}
    (ht : |t| ≤ T) (hs : |s| ≤ T) :
    ‖hillDuhamelKernel a b t s‖ ≤ a.propSize T * (Real.sqrt 2 ^ N * b.bound) := by
  refine (ContinuousLinearMap.opNorm_comp_le (kgMulCLM (a.propBCF (E := E) t s))
    (kgConvCLM (b.density s))).trans ?_
  have h1 : ‖kgMulCLM (a.propBCF (E := E) t s)‖ ≤ a.propSize T :=
    (norm_kgMulCLM_le _).trans (a.norm_propBCF_le_window ht hs)
  have h2 : ‖kgConvCLM (b.density s)‖ ≤ Real.sqrt 2 ^ N * b.bound := b.norm_convCLM_le s
  exact mul_le_mul h1 h2 (norm_nonneg _) (a.propSize_nonneg T)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_hillFreeTerm_le_window (a : HillSpeed) (G₀ : E →ᵇ ℂ) {T t : ℝ} (ht : |t| ≤ T) :
    ‖hillFreeTerm a G₀ t‖ ≤ a.coscSize T * ‖G₀‖ := by
  refine ((kgMulCLM (a.coscBCF (E := E) t)).le_opNorm G₀).trans ?_
  have h1 : ‖kgMulCLM (a.coscBCF (E := E) t)‖ ≤ a.coscSize T :=
    (norm_kgMulCLM_le _).trans (a.norm_coscBCF_le_window ht)
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

theorem continuous_hillDuhamelKernel (a : HillSpeed) (b : WienerFamily E N) :
    Continuous fun p : ℝ × ℝ => hillDuhamelKernel a b p.1 p.2 := by
  have hmul : Continuous fun p : ℝ × ℝ => kgMulCLM (a.propBCF (E := E) p.1 p.2) :=
    (ContinuousLinearMap.mul ℝ (E →ᵇ ℂ)).continuous.comp a.continuous_propBCF
  have hcompL : Continuous fun p : ℝ × ℝ =>
      (ContinuousLinearMap.compL ℝ (E →ᵇ ℂ) (E →ᵇ ℂ) (E →ᵇ ℂ))
        (kgMulCLM (a.propBCF (E := E) p.1 p.2)) :=
    (ContinuousLinearMap.compL ℝ (E →ᵇ ℂ) (E →ᵇ ℂ) (E →ᵇ ℂ)).continuous.comp hmul
  exact hcompL.clm_apply (b.continuous_convCLM.comp continuous_snd)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_hillFreeTerm (a : HillSpeed) (G₀ : E →ᵇ ℂ) :
    Continuous (hillFreeTerm a G₀ : ℝ → (E →ᵇ ℂ)) := by
  have hmul : Continuous fun t : ℝ => kgMulCLM (a.coscBCF (E := E) t) :=
    (ContinuousLinearMap.mul ℝ (E →ᵇ ℂ)).continuous.comp a.continuous_coscBCF
  exact hmul.clm_apply continuous_const

/-- **The driven evolution on the frequency side**: the solution of the Duhamel equation. -/
noncomputable def hillPotentialFlow (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) :
    ℝ → (E →ᵇ ℂ) :=
  volterraSolution (hillFreeTerm a G₀) (hillDuhamelKernel a b)

theorem locallyBounded_hillDuhamel (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) :
    VolterraLocallyBounded (hillFreeTerm a G₀) (hillDuhamelKernel a b) := by
  intro T _
  refine ⟨a.propSize T * (Real.sqrt 2 ^ N * b.bound), a.coscSize T * ‖G₀‖, ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (a.propSize_nonneg T)
      (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) N) b.bound_nonneg)
  · exact mul_nonneg (a.coscSize_nonneg T) (norm_nonneg _)
  · exact fun t s ht hs => norm_hillDuhamelKernel_le_window a b ht hs
  · exact fun t ht => norm_hillFreeTerm_le_window a G₀ ht

theorem continuous_hillPotentialFlow (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) :
    Continuous (hillPotentialFlow a b G₀) :=
  continuous_volterraSolution_of_locallyBounded (continuous_hillFreeTerm a G₀)
    (continuous_hillDuhamelKernel a b) (locallyBounded_hillDuhamel a b G₀)

/-- **The evolution solves the Duhamel equation.** -/
theorem hillPotentialFlow_eq (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) :
    hillPotentialFlow a b G₀ t
      = hillFreeTerm a G₀ t +
        ∫ s in (0 : ℝ)..t, hillDuhamelKernel a b t s (hillPotentialFlow a b G₀ s) :=
  volterraSolution_eq_of_locallyBounded (continuous_hillFreeTerm a G₀)
    (continuous_hillDuhamelKernel a b) (locallyBounded_hillDuhamel a b G₀) t

/-- **The evolution starts at the datum**, damped by one power of the frequency. -/
theorem hillPotentialFlow_zero (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E) :
    hillPotentialFlow a b G₀ 0 ξ = ((a.freq ξ 0 : ℝ) : ℂ)⁻¹ * G₀ ξ := by
  rw [hillPotentialFlow_eq a b G₀ 0, intervalIntegral.integral_same, add_zero,
    hillFreeTerm_apply, a.coscSymbol_zero ξ, Complex.ofReal_inv]

/-! ## The evolution at a fixed frequency -/

/-- The source of the fibre: the potential term of the evolution. -/
noncomputable def hillFlowSource (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E)
    (s : ℝ) : ℂ :=
  kgConv N (b.density s) (hillPotentialFlow a b G₀ s) ξ

theorem continuous_hillFlowSource (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E) :
    Continuous (hillFlowSource a b G₀ ξ) := by
  have h1 : Continuous fun s : ℝ => kgConvCLM (b.density s) (hillPotentialFlow a b G₀ s) :=
    b.continuous_convCLM.clm_apply (continuous_hillPotentialFlow a b G₀)
  exact (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) ξ).continuous.comp h1

/-- **The evolution at a fixed frequency is the Duhamel solution of the driven Hill oscillator**,
written with the fundamental pair of that fibre. -/
theorem hillPotentialFlow_apply_eq_duhamel (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (ξ : E) (t : ℝ) :
    hillPotentialFlow a b G₀ t ξ
      = duhamelPair (hillCos (a.freq ξ)) (hillSin (a.freq ξ))
          (((a.freq ξ 0 : ℝ) : ℂ)⁻¹ * G₀ ξ) 0 (hillFlowSource a b G₀ ξ) t := by
  have hprop : Continuous fun s : ℝ => a.propBCF (E := E) t s := a.continuous_propBCF_base t
  have hmul : Continuous fun s : ℝ => kgMulCLM (a.propBCF (E := E) t s) :=
    (ContinuousLinearMap.mul ℝ (E →ᵇ ℂ)).continuous.comp hprop
  have hK : Continuous fun s : ℝ => hillDuhamelKernel a b t s :=
    ((ContinuousLinearMap.compL ℝ (E →ᵇ ℂ) (E →ᵇ ℂ) (E →ᵇ ℂ)).continuous.comp hmul).clm_apply
      b.continuous_convCLM
  have hcont : Continuous fun s : ℝ => hillDuhamelKernel a b t s (hillPotentialFlow a b G₀ s) :=
    hK.clm_apply (continuous_hillPotentialFlow a b G₀)
  have hint : IntervalIntegrable
      (fun s : ℝ => hillDuhamelKernel a b t s (hillPotentialFlow a b G₀ s)) volume 0 t :=
    hcont.intervalIntegrable (μ := volume) 0 t
  have heval :
      (∫ s in (0 : ℝ)..t, (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) ξ)
          (hillDuhamelKernel a b t s (hillPotentialFlow a b G₀ s)))
        = (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) ξ)
            (∫ s in (0 : ℝ)..t, hillDuhamelKernel a b t s (hillPotentialFlow a b G₀ s)) :=
    ContinuousLinearMap.intervalIntegral_comp_comm _ hint
  simp only [BoundedContinuousFunction.evalCLM_apply] at heval
  have hpt : ∀ s : ℝ, hillDuhamelKernel a b t s (hillPotentialFlow a b G₀ s) ξ
      = ((hillSin (a.freq ξ) t * hillCos (a.freq ξ) s : ℝ) : ℂ) * hillFlowSource a b G₀ ξ s -
        ((hillCos (a.freq ξ) t * hillSin (a.freq ξ) s : ℝ) : ℂ) * hillFlowSource a b G₀ ξ s := by
    intro s
    show ((a.propSymbol t s ξ : ℝ) : ℂ) * kgConv N (b.density s) (hillPotentialFlow a b G₀ s) ξ = _
    rw [a.propSymbol_eq t s ξ, hillFlowSource, Complex.ofReal_sub]
    ring
  have hsplit : (∫ s in (0 : ℝ)..t, hillDuhamelKernel a b t s (hillPotentialFlow a b G₀ s) ξ)
      = ((hillSin (a.freq ξ) t : ℝ) : ℂ) *
          duhamelPairFirstPart (hillCos (a.freq ξ)) (hillFlowSource a b G₀ ξ) t -
        ((hillCos (a.freq ξ) t : ℝ) : ℂ) *
          duhamelPairSecondPart (hillSin (a.freq ξ)) (hillFlowSource a b G₀ ξ) t := by
    have hcontC : Continuous fun s : ℝ =>
        ((hillCos (a.freq ξ) s : ℝ) : ℂ) * hillFlowSource a b G₀ ξ s :=
      (Complex.continuous_ofReal.comp (a.continuous_hillCos_freq_time ξ)).mul
        (continuous_hillFlowSource a b G₀ ξ)
    have hcontS : Continuous fun s : ℝ =>
        ((hillSin (a.freq ξ) s : ℝ) : ℂ) * hillFlowSource a b G₀ ξ s :=
      (Complex.continuous_ofReal.comp (a.continuous_hillSin_freq_time ξ)).mul
        (continuous_hillFlowSource a b G₀ ξ)
    have hintC := (hcontC.intervalIntegrable (μ := volume) 0 t).const_mul
      ((hillSin (a.freq ξ) t : ℝ) : ℂ)
    have hintS := (hcontS.intervalIntegrable (μ := volume) 0 t).const_mul
      ((hillCos (a.freq ξ) t : ℝ) : ℂ)
    rw [duhamelPairFirstPart, duhamelPairSecondPart, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hintC hintS]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [hpt s, Complex.ofReal_mul, Complex.ofReal_mul]
    ring
  rw [hillPotentialFlow_eq a b G₀ t, BoundedContinuousFunction.add_apply, hillFreeTerm_apply,
    ← heval, hsplit, duhamelPair, a.coscSymbol_eq t ξ]
  have hpos : (a.freq ξ 0 : ℝ) ≠ 0 := ne_of_gt (a.freq_pos ξ 0)
  have hposC : ((a.freq ξ 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos
  rw [Complex.ofReal_div]
  field_simp
  ring


/-! ## The fibre solves the driven equation -/

/-- The velocity of the fibre. -/
noncomputable def hillFlowApplyDeriv (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (ξ : E)
    (t : ℝ) : ℂ :=
  duhamelPairDeriv (hillCos (a.freq ξ)) (hillCosDeriv (a.freq ξ)) (hillSin (a.freq ξ))
    (hillSinDeriv (a.freq ξ)) (((a.freq ξ 0 : ℝ) : ℂ)⁻¹ * G₀ ξ) 0 (hillFlowSource a b G₀ ξ) t

/-- **The fibre is differentiable in time.** -/
theorem hasDerivAt_hillPotentialFlow_apply (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => hillPotentialFlow a b G₀ r ξ) (hillFlowApplyDeriv a b G₀ ξ t) t := by
  have hfun : (fun r : ℝ => hillPotentialFlow a b G₀ r ξ)
      = duhamelPair (hillCos (a.freq ξ)) (hillSin (a.freq ξ))
          (((a.freq ξ 0 : ℝ) : ℂ)⁻¹ * G₀ ξ) 0 (hillFlowSource a b G₀ ξ) := by
    funext r
    exact hillPotentialFlow_apply_eq_duhamel a b G₀ ξ r
  rw [hfun, hillFlowApplyDeriv]
  exact hasDerivAt_duhamelPair (a.hasDerivAt_hillCos_freq ξ) (a.hasDerivAt_hillSin_freq ξ)
    (a.continuous_hillCos_freq_time ξ) (a.continuous_hillSin_freq_time ξ)
    (continuous_hillFlowSource a b G₀ ξ) t

/-- **The fibre solves the driven Hill equation at every frequency and every time.** -/
theorem hasDerivAt_hillFlowApplyDeriv (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (ξ : E) (t : ℝ) :
    HasDerivAt (hillFlowApplyDeriv a b G₀ ξ)
      (-(((a.freq ξ t ^ 2 : ℝ) : ℂ)) * hillPotentialFlow a b G₀ t ξ +
        hillFlowSource a b G₀ ξ t) t := by
  have hmain := hasDerivAt_duhamelPairDeriv
    (C := hillCos (a.freq ξ)) (dC := hillCosDeriv (a.freq ξ))
    (ddC := fun r => -(a.freq ξ r ^ 2) * hillCos (a.freq ξ) r)
    (S := hillSin (a.freq ξ)) (dS := hillSinDeriv (a.freq ξ))
    (ddS := fun r => -(a.freq ξ r ^ 2) * hillSin (a.freq ξ) r)
    (ω := a.freq ξ) (α := ((a.freq ξ 0 : ℝ) : ℂ)⁻¹ * G₀ ξ) (β := 0)
    (h := hillFlowSource a b G₀ ξ)
    (a.hasDerivAt_hillCosDeriv_freq ξ) (a.hasDerivAt_hillSinDeriv_freq ξ)
    (a.continuous_hillCos_freq_time ξ) (a.continuous_hillSin_freq_time ξ)
    (continuous_hillFlowSource a b G₀ ξ) (fun r => by ring) (fun r => by ring)
    (fun r => a.wronskian_freq ξ r) t
  refine hmain.congr_deriv ?_
  rw [hillPotentialFlow_apply_eq_duhamel a b G₀ ξ t]

end Flow

end GaloisForLFunctions.HTGeometry
