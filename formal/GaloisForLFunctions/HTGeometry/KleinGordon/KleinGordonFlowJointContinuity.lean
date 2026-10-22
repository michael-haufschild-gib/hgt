import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonChartPartials

/-!
# Joint continuity of the evolution and its time derivative

The chart interface asks for partial derivatives that are continuous on the whole chart, and those
partials are syntheses of the time derivative of the evolution. So that derivative has to be
continuous jointly in the time and the frequency.

It is, and the reason is the explicit Duhamel formula: the derivative is a combination of the datum
and of the two moments of the source, and the source is the evaluation of a continuous curve of
bounded continuous functions — evaluation being jointly continuous for the supremum norm.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

variable (a : WienerFamily E N) (G₀ : E →ᵇ ℂ)

/-! ## Plumbing -/

theorem continuous_pair_left {X Y W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace W] {F : X → Y → W} (hF : Continuous fun p : X × Y => F p.1 p.2) (x : X) :
    Continuous (F x) :=
  hF.comp (continuous_const.prodMk continuous_id)

theorem continuous_pair_right {X Y W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace W] {F : X → Y → W} (hF : Continuous fun p : X × Y => F p.1 p.2) (y : Y) :
    Continuous fun x : X => F x y :=
  hF.comp (continuous_id.prodMk continuous_const)

theorem continuous_pair_reassoc {X Y W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace W] {F : Y → ℝ → W} (hF : Continuous fun q : Y × ℝ => F q.1 q.2) :
    Continuous fun q : (X × Y) × ℝ => F q.1.2 q.2 :=
  hF.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)

/-! ## The source -/

/-- **The source is jointly continuous** in the frequency and the time. -/
theorem continuous_kgFlowSource_pair :
    Continuous fun q : E × ℝ => kgFlowSource a G₀ q.1 q.2 := by
  have hflow : Continuous fun s : ℝ => kgConvCLM (a.density s) (kgPotentialFlow a G₀ s) :=
    a.continuous_convCLM.clm_apply (continuous_kgPotentialFlow a G₀)
  have heval : Continuous fun q : (E →ᵇ ℂ) × E => q.1 q.2 := ContinuousEval.continuous_eval
  exact heval.comp ((hflow.comp continuous_snd).prodMk continuous_fst)

/-! ## The moments -/

theorem continuous_duhamelCosPart_pair :
    Continuous fun p : ℝ × E => duhamelCosPart (kgFreq p.2) (kgFlowSource a G₀ p.2) p.1 := by
  have hsrc : Continuous fun q : (ℝ × E) × ℝ => kgFlowSource a G₀ q.1.2 q.2 :=
    continuous_pair_reassoc (X := ℝ) (continuous_kgFlowSource_pair a G₀)
  have hcos : Continuous fun q : (ℝ × E) × ℝ =>
      ((Real.cos (q.2 * kgFreq q.1.2) : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp (Real.continuous_cos.comp ?_)
    exact continuous_snd.mul (continuous_kgFreq.comp (continuous_snd.comp continuous_fst))
  have hf : Continuous (Function.uncurry fun (p : ℝ × E) (s : ℝ) =>
      ((Real.cos (s * kgFreq p.2) : ℝ) : ℂ) * kgFlowSource a G₀ p.2 s) := hcos.mul hsrc
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf continuous_fst

theorem continuous_duhamelSinPart_pair :
    Continuous fun p : ℝ × E => duhamelSinPart (kgFreq p.2) (kgFlowSource a G₀ p.2) p.1 := by
  have hsrc : Continuous fun q : (ℝ × E) × ℝ => kgFlowSource a G₀ q.1.2 q.2 :=
    continuous_pair_reassoc (X := ℝ) (continuous_kgFlowSource_pair a G₀)
  have hsin : Continuous fun q : (ℝ × E) × ℝ =>
      ((Real.sin (q.2 * kgFreq q.1.2) : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp (Real.continuous_sin.comp ?_)
    exact continuous_snd.mul (continuous_kgFreq.comp (continuous_snd.comp continuous_fst))
  have hf : Continuous (Function.uncurry fun (p : ℝ × E) (s : ℝ) =>
      ((Real.sin (s * kgFreq p.2) : ℝ) : ℂ) * kgFlowSource a G₀ p.2 s) := hsin.mul hsrc
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf continuous_fst

/-! ## The time derivative -/

/-- **The time derivative of the evolution is jointly continuous.** -/
theorem continuous_deriv_kgPotentialFlow_pair :
    Continuous fun p : ℝ × E => deriv (fun r : ℝ => kgPotentialFlow a G₀ r p.2) p.1 := by
  have hfun : (fun p : ℝ × E => deriv (fun r : ℝ => kgPotentialFlow a G₀ r p.2) p.1)
      = fun p : ℝ × E =>
        -(((Real.sin (p.1 * kgFreq p.2) : ℝ) : ℂ) * G₀ p.2)
          + ((Real.cos (p.1 * kgFreq p.2) : ℝ) : ℂ)
            * duhamelCosPart (kgFreq p.2) (kgFlowSource a G₀ p.2) p.1
          + ((Real.sin (p.1 * kgFreq p.2) : ℝ) : ℂ)
            * duhamelSinPart (kgFreq p.2) (kgFlowSource a G₀ p.2) p.1 := by
    funext p
    exact (hasDerivAt_kgPotentialFlow_apply a G₀ p.2 p.1).deriv
  rw [hfun]
  have hphase : Continuous fun p : ℝ × E => p.1 * kgFreq p.2 :=
    continuous_fst.mul (continuous_kgFreq.comp continuous_snd)
  have hsin : Continuous fun p : ℝ × E => ((Real.sin (p.1 * kgFreq p.2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sin.comp hphase)
  have hcos : Continuous fun p : ℝ × E => ((Real.cos (p.1 * kgFreq p.2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp hphase)
  have hdatum : Continuous fun p : ℝ × E => G₀ p.2 := G₀.continuous.comp continuous_snd
  exact (((hsin.mul hdatum).neg).add (hcos.mul (continuous_duhamelCosPart_pair a G₀))).add
    (hsin.mul (continuous_duhamelSinPart_pair a G₀))

/-- **The density of the time derivative is jointly continuous.** -/
theorem continuous_kgFlowDensityDeriv_pair :
    Continuous fun p : ℝ × E => kgFlowDensityDeriv a G₀ p.1 p.2 := by
  have hinv : Continuous fun p : ℝ × E => ((kgFreq p.2 ^ N : ℝ) : ℂ)⁻¹ := by
    refine Continuous.inv₀ (Complex.continuous_ofReal.comp
      ((continuous_kgFreq.comp continuous_snd).pow N)) fun p => ?_
    exact Complex.ofReal_ne_zero.mpr (pow_pos (kgFreq_pos p.2) N).ne'
  exact hinv.mul (continuous_deriv_kgPotentialFlow_pair a G₀)

theorem continuous_kgFlowDensityDeriv_freq (t : ℝ) :
    Continuous (kgFlowDensityDeriv a G₀ t) :=
  continuous_pair_left (continuous_kgFlowDensityDeriv_pair a G₀) t

theorem continuous_kgFlowDensityDeriv_time (ξ : E) :
    Continuous fun t : ℝ => kgFlowDensityDeriv a G₀ t ξ :=
  continuous_pair_right (continuous_kgFlowDensityDeriv_pair a G₀) ξ

/-! ## The density itself -/

theorem continuous_kgFlowDensity_time (ξ : E) :
    Continuous fun t : ℝ => kgFlowDensity a G₀ t ξ := by
  have hflow : Continuous fun t : ℝ => kgPotentialFlow a G₀ t ξ :=
    ((BoundedContinuousFunction.evalCLM (𝕜 := ℝ) ξ).continuous).comp
      (continuous_kgPotentialFlow a G₀)
  exact continuous_const.mul hflow

end GaloisForLFunctions.HTGeometry
