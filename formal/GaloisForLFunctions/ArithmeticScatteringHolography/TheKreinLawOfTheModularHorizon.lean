import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationRateIsTheDepthOfTheDeepestSeenZero

/-!
# The Krein law of the modular horizon

The ringdown of the modular horizon has one mode per zero, with amplitude `e^{τ(ρ-1)/2}` at modular time `τ`. So a
mode and its functional-equation partner multiply to `e^{-τ/2}`, whatever `ρ` is (`modeFactor_mul_partner`). This
is the Liouville law: partners have rates summing to `½`, and the rate `¼` is the isotropic case.

The modes are read by the zero-side Weil form `W_Z`, and the translation of tests is an isometry of it. In the
energy normalization, where amplitude at modular time `τ` carries `e^{-τ/4}`, this gives the **Krein law**

  `𝒬_f(τ) = e^{-τ/2} W_Z(f, f)`

on every tempered configuration (`physicalKrein_eq`, `hasDerivAt_physicalKrein`). So the **Krein square decays at
exactly the universal rate, unconditionally**, even though the rate of the amplitudes is unknown. The flux is
`½ 𝒬_f`, and it is nonnegative for every test exactly under RH (`kreinFlux_nonneg_iff`). If RH fails there is a
test with `𝒬_f(τ) < 0` at every time, rising to zero (`exists_antiDissipative_of_not_riemannHypothesis`): the
negative-energy state decays because its flux is negative, so Chetaev's principle has no content here until
nonnegativity of the flux is known. A physical proof of RH by energy would have to produce `𝓕 ≥ 0` from something
other than the form itself. The graph model shows that wave dynamics does not supply it.
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

open ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry Zeta23
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)

/-! ### Modes -/

/-- The amplitude of the mode of a zero `ρ` at modular time `τ`. -/
def modeFactor (ρ : ℂ) (τ : ℝ) : ℂ := Complex.exp ((τ : ℂ) * ((ρ - 1) / 2))

/-- **The Liouville law of the horizon.** A mode and its functional-equation partner multiply to `e^{-τ/2}`, for
every position of the zero. -/
theorem modeFactor_mul_partner (ρ : ℂ) (τ : ℝ) :
    modeFactor ρ τ * modeFactor (1 - ρ) τ = ((Real.exp (-τ / 2) : ℝ) : ℂ) := by
  unfold modeFactor
  rw [← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The modulus of a mode: the rate is `(1 - β)/2`. -/
theorem norm_modeFactor (ρ : ℂ) (τ : ℝ) : ‖modeFactor ρ τ‖ = Real.exp (-τ * ((1 - ρ.re) / 2)) := by
  unfold modeFactor
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]
  ring

/-- **The amplitude is the isometric orbit times the universal damping.** -/
theorem modeFactor_eq (ρ : ℂ) (τ : ℝ) :
    modeFactor ρ τ = ((Real.exp (-τ / 4) : ℝ) : ℂ) * Complex.exp (((τ / 2 : ℝ) : ℂ) * (ρ - 1 / 2)) := by
  unfold modeFactor
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ### The Krein square -/

/-- **The physical Krein square** of the probe `f` at modular time `τ`. -/
def physicalKrein (Z : ZeroConfig) (f : ℝ → ℝ) (τ : ℝ) : ℝ :=
  Real.exp (-τ / 2) * configWeil Z (scaleShift (τ / 2) f) (scaleShift (τ / 2) f)

/-- **The Krein law.** The Krein square decays at exactly the universal rate, on every configuration. -/
theorem physicalKrein_eq (Z : ZeroConfig) (f : ℝ → ℝ) (τ : ℝ) :
    physicalKrein Z f τ = Real.exp (-τ / 2) * configWeil Z f f := by
  unfold physicalKrein
  rw [configWeil_scaleShift_same]

/-- The flux law: `d𝒬/dτ = -½ 𝒬`. -/
theorem hasDerivAt_physicalKrein (Z : ZeroConfig) (f : ℝ → ℝ) (τ : ℝ) :
    HasDerivAt (physicalKrein Z f) (-(1 / 2) * physicalKrein Z f τ) τ := by
  have hfun : physicalKrein Z f = fun τ => Real.exp (-τ / 2) * configWeil Z f f :=
    funext (physicalKrein_eq Z f)
  have h1 : HasDerivAt (fun τ : ℝ => -τ / 2) (-1 / 2) τ := by
    simpa using ((hasDerivAt_id τ).neg).div_const 2
  have h2 := (h1.exp).mul_const (configWeil Z f f)
  rw [physicalKrein_eq Z f τ, hfun]
  exact h2.congr_deriv (by ring)

/-- The Krein flux. -/
def kreinFlux (Z : ZeroConfig) (f : ℝ → ℝ) (τ : ℝ) : ℝ := (1 / 2) * physicalKrein Z f τ

theorem kreinFlux_nonneg_iff_weil (Z : ZeroConfig) (f : ℝ → ℝ) (τ : ℝ) :
    0 ≤ kreinFlux Z f τ ↔ 0 ≤ configWeil Z f f := by
  unfold kreinFlux
  rw [physicalKrein_eq, ← mul_assoc]
  have h : 0 < 1 / 2 * Real.exp (-τ / 2) := by positivity
  exact mul_nonneg_iff_of_pos_left h

/-- **The flux is a positive quantity exactly under RH.** -/
theorem kreinFlux_nonneg_iff :
    (∀ f ∈ realTests, ∀ τ : ℝ, 0 ≤ kreinFlux zetaZeroConfig f τ) ↔ RiemannHypothesis := by
  rw [← scalingSurface_hodgeIndex_iff, ← configSurface_zeta_eq,
    configSurface_hodgeIndex_iff zetaZeroConfig temperedConfig_zetaZeroConfig]
  constructor
  · intro h f hf
    exact (kreinFlux_nonneg_iff_weil _ _ 0).mp (h f hf 0)
  · intro h f hf τ
    exact (kreinFlux_nonneg_iff_weil _ _ τ).mpr (h f hf)

/-- **Chetaev's principle has no content here.** If RH fails there is a test whose Krein square is negative at every
time and rises to zero: it decays, with negative flux. -/
theorem exists_antiDissipative_of_not_riemannHypothesis (h : ¬ RiemannHypothesis) :
    ∃ f ∈ realTests, (∀ τ : ℝ, physicalKrein zetaZeroConfig f τ < 0 ∧ kreinFlux zetaZeroConfig f τ < 0) ∧
      Tendsto (physicalKrein zetaZeroConfig f) atTop (𝓝 0) := by
  have hne : ¬ ∀ f ∈ realTests, 0 ≤ configWeil zetaZeroConfig f f := by
    intro hall
    apply h
    rw [← scalingSurface_hodgeIndex_iff, ← configSurface_zeta_eq,
      configSurface_hodgeIndex_iff zetaZeroConfig temperedConfig_zetaZeroConfig]
    exact hall
  obtain ⟨f, hf, hneg⟩ : ∃ f ∈ realTests, configWeil zetaZeroConfig f f < 0 := by
    by_contra hcon
    apply hne
    intro f hf
    by_contra hlt
    exact hcon ⟨f, hf, not_le.mp hlt⟩
  refine ⟨f, hf, fun τ => ?_, ?_⟩
  · have hexp : 0 < Real.exp (-τ / 2) := Real.exp_pos _
    have h1 : physicalKrein zetaZeroConfig f τ < 0 := by
      rw [physicalKrein_eq]
      exact mul_neg_of_pos_of_neg hexp hneg
    refine ⟨h1, ?_⟩
    unfold kreinFlux
    linarith
  · have hfun : physicalKrein zetaZeroConfig f =
        fun τ => Real.exp (-τ / 2) * configWeil zetaZeroConfig f f :=
      funext (physicalKrein_eq _ f)
    rw [hfun]
    have hdiv : Tendsto (fun τ : ℝ => -τ / 2) atTop atBot := by
      have : (fun τ : ℝ => -τ / 2) = fun τ => (-(1 / 2 : ℝ)) * τ := by
        funext τ
        ring
      rw [this]
      exact tendsto_id.const_mul_atTop_of_neg (by norm_num)
    have hexp := Real.tendsto_exp_atBot.comp hdiv
    have := hexp.mul_const (configWeil zetaZeroConfig f f)
    simpa using this

/-- A configuration on the critical line has a dissipative Krein square, with any arrangement of its zeros: the
law sees the position of each zero and no correlation between them. -/
theorem kreinFlux_nonneg_of_onLine (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) {f : ℝ → ℝ} (hf : f ∈ realTests) (τ : ℝ) :
    0 ≤ kreinFlux Z f τ :=
  (kreinFlux_nonneg_iff_weil Z f τ).mpr
    ((configSurface_hodgeIndex_iff Z hZ).mp (configSurface_hodgeIndex_of_onLine Z hZ hon) f hf)

/-! ### The sharp decay of the correlator -/

/-- The two-time correlator of a probe in the energy normalization: the amplitude-level resonant sum, smoothed by the
probe. -/
def physicalCorrelator (Z : ZeroConfig) (hZ : TemperedConfig Z) (x : ScalingCycle) (τ : ℝ) : ℝ :=
  Real.exp (-τ / 4) * (configScalingDatum Z hZ).orbitCorr x (τ / 2)

/-- **The sharp decay of a smoothed resonant sum.** The correlator decays at rate `¼ - σ/2` exactly when the probe does
not see the zeros of depth above `σ`, so the decay rate is the slowest rate that the probe sees. Unlike the Krein square,
the correlator decays at the universal rate only if the probe is blind off the line. -/
theorem physicalCorrelator_rate_iff (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    {σ : ℝ} (hσ : 0 ≤ σ) (x : ScalingCycle) :
    (∃ K : ℝ, ∀ τ : ℝ, 0 ≤ τ → |physicalCorrelator Z hZ x τ| ≤ K * Real.exp (-(1 / 4 - σ / 2) * τ)) ↔
      BlindAbove Z σ x.2.2 := by
  rw [← orbitCorr_rate_iff_blindAbove Z hZ hFE hσ x]
  have hrel (τ : ℝ) (K : ℝ) :
      |physicalCorrelator Z hZ x τ| ≤ K * Real.exp (-(1 / 4 - σ / 2) * τ) ↔
        |(configScalingDatum Z hZ).orbitCorr x (τ / 2)| ≤ K * Real.exp (σ * (τ / 2)) := by
    unfold physicalCorrelator
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hsplit : Real.exp (-(1 / 4 - σ / 2) * τ) = Real.exp (-τ / 4) * Real.exp (σ * (τ / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit, show K * (Real.exp (-τ / 4) * Real.exp (σ * (τ / 2))) =
      Real.exp (-τ / 4) * (K * Real.exp (σ * (τ / 2))) by ring]
    exact mul_le_mul_iff_right₀ (Real.exp_pos _)
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, fun t ht => ?_⟩
    have h := (hrel (2 * t) K).mp (hK (2 * t) (by positivity))
    rwa [show 2 * t / 2 = t by ring] at h
  · rintro ⟨K, hK⟩
    refine ⟨K, fun τ hτ => ?_⟩
    exact (hrel τ K).mpr (hK (τ / 2) (by positivity))

end GaloisForLFunctions.ArithmeticScatteringHolography

end
