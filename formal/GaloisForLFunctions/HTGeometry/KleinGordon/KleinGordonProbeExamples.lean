import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonClockProbe
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# The admissible potentials are plentiful

A hypothesis class asserts nothing until it is inhabited, so this file exhibits the potentials the
construction covers. Two constructions suffice:

* a continuous density of compact support is admissible at *every* weight — no decay estimate is
  needed, the integrand is continuous with compact support;
* multiplying such a density by a bounded Lipschitz function of time produces a family, whose
  potential is genuinely time-dependent.

Concretely, a symmetrised bump function is a real density whose potential is positive at the origin,
so the class contains potentials that are neither zero nor static.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-! ## Compactly supported densities -/

/-- **A continuous density of compact support is admissible at every weight.** -/
noncomputable def WienerDensity.ofCompactSupport {a : E → ℂ} (hcont : Continuous a)
    (hsupp : HasCompactSupport a) (N : ℕ) : WienerDensity E N where
  toFun := a
  aestronglyMeasurable := hcont.aestronglyMeasurable
  integrable_weight := by
    have hcs : HasCompactSupport (fun η : E => kgFreq η ^ N * ‖a η‖) := by
      have h : HasCompactSupport ((fun η : E => kgFreq η ^ N) * fun η : E => ‖a η‖) :=
        HasCompactSupport.mul_left hsupp.norm
      exact h
    exact Continuous.integrable_of_hasCompactSupport (μ := (volume : Measure E))
      ((continuous_kgFreq.pow N).mul hcont.norm) hcs

theorem WienerDensity.ofCompactSupport_apply {a : E → ℂ} (hcont : Continuous a)
    (hsupp : HasCompactSupport a) (N : ℕ) (η : E) :
    WienerDensity.ofCompactSupport hcont hsupp N η = a η := rfl

/-! ## Modulated families -/

/-- A density modulated by a bounded Lipschitz function of time. -/
noncomputable def WienerFamily.ofModulation (a : WienerDensity E N) (g : ℝ → ℝ) {M L : ℝ}
    (hM : ∀ t : ℝ, |g t| ≤ M) (hL0 : 0 ≤ L)
    (hL : ∀ t t' : ℝ, |g t - g t'| ≤ L * |t - t'|) : WienerFamily E N where
  density := fun t =>
    { toFun := fun η => ((g t : ℝ) : ℂ) * a η
      aestronglyMeasurable := (continuous_const.aestronglyMeasurable).mul a.aestronglyMeasurable
      integrable_weight := by
        refine (a.integrable_weight.const_mul |g t|).congr ?_
        filter_upwards with η
        show |g t| * (kgFreq η ^ N * ‖a η‖) = kgFreq η ^ N * ‖((g t : ℝ) : ℂ) * a η‖
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        ring }
  bound := M * a.norm'
  norm_le := by
    intro t
    have hval : (∫ η : E, kgFreq η ^ N * ‖((g t : ℝ) : ℂ) * a η‖)
        = |g t| * a.norm' := by
      rw [WienerDensity.norm', ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
      show kgFreq η ^ N * ‖((g t : ℝ) : ℂ) * a η‖ = |g t| * (kgFreq η ^ N * ‖a η‖)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    show (∫ η : E, kgFreq η ^ N * ‖((g t : ℝ) : ℂ) * a η‖) ≤ M * a.norm'
    rw [hval]
    exact mul_le_mul_of_nonneg_right (hM t) a.norm'_nonneg
  lip := L * a.norm'
  lip_nonneg := mul_nonneg hL0 a.norm'_nonneg
  lip_le := by
    intro t t'
    have hval : (∫ η : E, kgFreq η ^ N * ‖((g t : ℝ) : ℂ) * a η - ((g t' : ℝ) : ℂ) * a η‖)
        = |g t - g t'| * a.norm' := by
      rw [WienerDensity.norm', ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
      show kgFreq η ^ N * ‖((g t : ℝ) : ℂ) * a η - ((g t' : ℝ) : ℂ) * a η‖
        = |g t - g t'| * (kgFreq η ^ N * ‖a η‖)
      have hfac : ((g t : ℝ) : ℂ) * a η - ((g t' : ℝ) : ℂ) * a η
          = ((g t - g t' : ℝ) : ℂ) * a η := by
        push_cast
        ring
      rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    show (∫ η : E, kgFreq η ^ N * ‖((g t : ℝ) : ℂ) * a η - ((g t' : ℝ) : ℂ) * a η‖)
      ≤ L * a.norm' * |t - t'|
    rw [hval]
    have hstep := mul_le_mul_of_nonneg_right (hL t t') a.norm'_nonneg
    refine hstep.trans_eq ?_
    ring

theorem WienerFamily.ofModulation_density_apply (a : WienerDensity E N) (g : ℝ → ℝ) {M L : ℝ}
    (hM : ∀ t : ℝ, |g t| ≤ M) (hL0 : 0 ≤ L)
    (hL : ∀ t t' : ℝ, |g t - g t'| ≤ L * |t - t'|) (t : ℝ) (η : E) :
    (WienerFamily.ofModulation a g hM hL0 hL).density t η = ((g t : ℝ) : ℂ) * a η := rfl

/-- **A modulated real density is a real family.** -/
theorem isRealFamily_ofModulation (a : WienerDensity E N) (ha : IsRealDensity a) (g : ℝ → ℝ)
    {M L : ℝ} (hM : ∀ t : ℝ, |g t| ≤ M) (hL0 : 0 ≤ L)
    (hL : ∀ t t' : ℝ, |g t - g t'| ≤ L * |t - t'|) :
    IsRealFamily (WienerFamily.ofModulation a g hM hL0 hL) := by
  intro t η
  show ((g t : ℝ) : ℂ) * a (-η) = (starRingEnd ℂ) (((g t : ℝ) : ℂ) * a η)
  rw [ha η, map_mul, Complex.conj_ofReal]

/-! ## A concrete potential -/

section Concrete

variable (d : ℕ)

/-- A bump function at the origin. -/
noncomputable def kgBump : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := ⟨1, 2, one_pos, one_lt_two⟩

/-- Its symmetrisation, as a complex density. -/
noncomputable def kgBumpFun (η : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ((kgBump d η + kgBump d (-η) : ℝ) : ℂ)

theorem continuous_kgBumpFun : Continuous (kgBumpFun d) := by
  refine Complex.continuous_ofReal.comp ?_
  exact ((kgBump d).continuous).add ((kgBump d).continuous.comp continuous_neg)

theorem hasCompactSupport_kgBumpFun : HasCompactSupport (kgBumpFun d) := by
  have hneg : HasCompactSupport fun η : EuclideanSpace ℝ (Fin d) => (kgBump d) (-η) :=
    (kgBump d).hasCompactSupport.comp_homeomorph (Homeomorph.neg _)
  have hsum : HasCompactSupport fun η : EuclideanSpace ℝ (Fin d) =>
      (kgBump d) η + (kgBump d) (-η) :=
    (kgBump d).hasCompactSupport.add hneg
  exact hsum.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero

/-- The density of the symmetrised bump. -/
noncomputable def kgBumpDensity (N : ℕ) : WienerDensity (EuclideanSpace ℝ (Fin d)) N :=
  WienerDensity.ofCompactSupport (continuous_kgBumpFun d) (hasCompactSupport_kgBumpFun d) N

theorem kgBumpDensity_apply (N : ℕ) (η : EuclideanSpace ℝ (Fin d)) :
    kgBumpDensity d N η = kgBumpFun d η := rfl

/-- **The bump density is real**: it is real-valued and even. -/
theorem isRealDensity_kgBumpDensity (N : ℕ) : IsRealDensity (kgBumpDensity d N) := by
  intro η
  show kgBumpFun d (-η) = (starRingEnd ℂ) (kgBumpFun d η)
  rw [kgBumpFun, kgBumpFun, Complex.conj_ofReal, neg_neg]
  congr 1
  ring

theorem integral_kgBumpFun_pos :
    0 < ∫ η : EuclideanSpace ℝ (Fin d), ((kgBump d) η + (kgBump d) (-η)) := by
  have hint : Integrable (fun η : EuclideanSpace ℝ (Fin d) => (kgBump d) η)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    (kgBump d).continuous.integrable_of_hasCompactSupport (kgBump d).hasCompactSupport
  have hneg : Integrable (fun η : EuclideanSpace ℝ (Fin d) => (kgBump d) (-η))
      (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    have h := hint.comp_neg
    exact h
  have hsplit : (∫ η : EuclideanSpace ℝ (Fin d), ((kgBump d) η + (kgBump d) (-η)))
      = (∫ η : EuclideanSpace ℝ (Fin d), (kgBump d) η)
        + ∫ η : EuclideanSpace ℝ (Fin d), (kgBump d) (-η) := by
    rw [← integral_add hint hneg]
  have hsame : (∫ η : EuclideanSpace ℝ (Fin d), (kgBump d) (-η))
      = ∫ η : EuclideanSpace ℝ (Fin d), (kgBump d) η :=
    integral_neg_eq_self (fun η : EuclideanSpace ℝ (Fin d) => (kgBump d) η)
      (volume : Measure (EuclideanSpace ℝ (Fin d)))
  rw [hsplit, hsame]
  have hpos : 0 < ∫ η : EuclideanSpace ℝ (Fin d), (kgBump d) η := (kgBump d).integral_pos
  linarith

/-- **The potential of the bump density is positive at the origin** — in particular it is not the
zero potential. -/
theorem kgPotential_kgBumpDensity_zero_pos (N : ℕ) :
    0 < (kgPotential (kgBumpDensity d N) 0).re := by
  have hchar : ∀ η : EuclideanSpace ℝ (Fin d), kgChar 0 η = 1 := by
    intro η
    rw [kgChar, inner_zero_right]
    simp
  have hval : kgPotential (kgBumpDensity d N) 0
      = ((∫ η : EuclideanSpace ℝ (Fin d), ((kgBump d) η + (kgBump d) (-η)) : ℝ) : ℂ) := by
    rw [kgPotential, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show kgChar 0 η * kgBumpFun d η
      = (((kgBump d) η + (kgBump d) (-η) : ℝ) : ℂ)
    rw [hchar η, one_mul, kgBumpFun]
  rw [hval, Complex.ofReal_re]
  exact integral_kgBumpFun_pos d

end Concrete

/-! ## The potential is nonzero and genuinely time-dependent -/

theorem kgPotential_ofModulation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N : ℕ}
    (a : WienerDensity E N) (g : ℝ → ℝ) {M L : ℝ} (hM : ∀ t : ℝ, |g t| ≤ M) (hL0 : 0 ≤ L)
    (hL : ∀ t t' : ℝ, |g t - g t'| ≤ L * |t - t'|) (t : ℝ) (x : E) :
    kgPotential ((WienerFamily.ofModulation a g hM hL0 hL).density t) x
      = ((g t : ℝ) : ℂ) * kgPotential a x := by
  rw [kgPotential, kgPotential, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  show kgChar x η * (((g t : ℝ) : ℂ) * a η) = ((g t : ℝ) : ℂ) * (kgChar x η * a η)
  ring

/-- The chart point on the time axis. -/
noncomputable def kgTimeAxis (d : ℕ) (t : ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons t (fun _ : Fin d => (0 : ℝ))

theorem kgTimeAxis_zero (d : ℕ) (t : ℝ) : kgTimeAxis d t 0 = t := by
  rw [kgTimeAxis, Fin.cons_zero]

theorem kgSpatial_kgTimeAxis (d : ℕ) (t : ℝ) : kgSpatial d (kgTimeAxis d t) = 0 := by
  have hcoord : (fun i : Fin d => kgTimeAxis d t i.succ) = fun _ : Fin d => (0 : ℝ) := by
    funext i
    rw [kgTimeAxis, Fin.cons_succ]
  rw [kgSpatial, hcoord]
  have hzero : (fun _ : Fin d => (0 : ℝ)) = 0 := rfl
  rw [hzero, map_zero, smul_zero]

/-- **The potential of the modulated bump, on the time axis**: an affine function of the modulation
with a positive coefficient. In particular it is not zero, and it varies in time as soon as the
modulation does. -/
theorem kgChartPotential_bump_timeAxis (d N : ℕ) (g : ℝ → ℝ) {M L : ℝ}
    (hM : ∀ t : ℝ, |g t| ≤ M) (hL0 : 0 ≤ L)
    (hL : ∀ t t' : ℝ, |g t - g t'| ≤ L * |t - t'|) (t : ℝ) :
    kgChartPotential (WienerFamily.ofModulation (kgBumpDensity d N) g hM hL0 hL)
        (kgTimeAxis d t)
      = g t * (kgPotential (kgBumpDensity d N) 0).re - 1 := by
  rw [kgChartPotential, kgTimeAxis_zero, kgSpatial_kgTimeAxis,
    kgPotential_ofModulation (kgBumpDensity d N) g hM hL0 hL t 0]
  congr 1
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- **Clock probes for a concrete time-dependent potential.** -/
theorem exists_localProbesOn_bump (d N : ℕ)
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (g : ℝ → ℝ) {M L : ℝ}
    (hM : ∀ t : ℝ, |g t| ≤ M) (hL0 : 0 ≤ L)
    (hL : ∀ t t' : ℝ, |g t - g t'| ≤ L * |t - t'|) (x₀ : EuclideanSpace ℝ (Fin d)) :
    ∃ region : Set (Fin (d + 1) → ℝ), IsOpen region ∧ kgChartEvent d x₀ ∈ region ∧
      LocalProbesOn (kgWaveOp d)
        (kgChartPotential (WienerFamily.ofModulation (kgBumpDensity d N) g hM hL0 hL))
        region :=
  exists_localProbesOn_kgChartPotential _ hN
    (isRealFamily_ofModulation _ (isRealDensity_kgBumpDensity d N) g hM hL0 hL) x₀

/-! ## Schwartz potentials -/

section Schwartz

open SchwartzMap Function

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-- **A Schwartz density is admissible at every weight.** -/
theorem integrable_kgFreq_pow_mul_schwartz (ψ : 𝓢(E, ℂ)) (N : ℕ) :
    Integrable (fun η : E => kgFreq η ^ N * ‖ψ η‖) (volume : Measure E) := by
  have hgrow : Function.HasTemperateGrowth fun η : E => ((kgFreq η ^ N : ℝ) : ℂ) :=
    Complex.hasTemperateGrowth_ofReal.comp ((hasTemperateGrowth_kgFreq E).pow N)
  have hschwartz : Integrable
      (fun η : E => ((kgFreq η ^ N : ℝ) : ℂ) • ψ η) (volume : Measure E) := by
    have h := (smulLeftCLM ℂ (fun η : E => ((kgFreq η ^ N : ℝ) : ℂ)) ψ).integrable
      (μ := (volume : Measure E))
    refine h.congr ?_
    filter_upwards with η
    exact smulLeftCLM_apply_apply hgrow ψ η
  refine (hschwartz.norm).congr ?_
  filter_upwards with η
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (kgFreq_pos η).le N)]

/-- A Schwartz function, as a density. -/
noncomputable def WienerDensity.ofSchwartz (ψ : 𝓢(E, ℂ)) (N : ℕ) : WienerDensity E N where
  toFun := ψ
  aestronglyMeasurable := ψ.continuous.aestronglyMeasurable
  integrable_weight := integrable_kgFreq_pow_mul_schwartz ψ N

theorem WienerDensity.ofSchwartz_apply (ψ : 𝓢(E, ℂ)) (N : ℕ) (η : E) :
    WienerDensity.ofSchwartz ψ N η = ψ η := rfl

/-- **The potential of the transform of a Schwartz function is the function itself** — Fourier
inversion. -/
theorem kgPotential_ofSchwartz_fourier (φ : 𝓢(E, ℂ)) (N : ℕ) (x : E) :
    kgPotential (WienerDensity.ofSchwartz (𝓕 φ) N) x = φ x := by
  have hcont : Continuous (φ : E → ℂ) := φ.continuous
  have hint : Integrable (φ : E → ℂ) (volume : Measure E) := φ.integrable
  have hfour : Integrable (𝓕 (φ : E → ℂ)) (volume : Measure E) := by
    have h := (𝓕 φ).integrable (μ := (volume : Measure E))
    refine h.congr ?_
    filter_upwards with η
    exact (congrFun (SchwartzMap.fourier_coe φ) η).symm
  have hinv := hcont.fourierInv_fourier_eq hint hfour
  have hval : kgPotential (WienerDensity.ofSchwartz (𝓕 φ) N) x
      = 𝓕⁻ (𝓕 (φ : E → ℂ)) x := by
    rw [kgPotential, Real.fourierInv_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show kgChar x η * (𝓕 φ) η = (𝐞 ⟪η, x⟫ : Circle) • 𝓕 (φ : E → ℂ) η
    rw [Circle.smul_def, kgChar]
    congr 1
  rw [hval, hinv]

/-- **The transform of a real Schwartz function satisfies the reality condition.** -/
theorem isRealDensity_ofSchwartz_fourier (φ : 𝓢(E, ℂ))
    (hreal : ∀ x : E, (starRingEnd ℂ) (φ x) = φ x) (N : ℕ) :
    IsRealDensity (WienerDensity.ofSchwartz (𝓕 φ) N) := by
  intro η
  have hcoe : ∀ w : E, (𝓕 φ) w = 𝓕 (φ : E → ℂ) w := fun w =>
    congrFun (SchwartzMap.fourier_coe φ) w
  show (𝓕 φ) (-η) = (starRingEnd ℂ) ((𝓕 φ) η)
  rw [hcoe, hcoe, Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show (𝐞 (-⟪v, -η⟫) : Circle) • φ v = (starRingEnd ℂ) ((𝐞 (-⟪v, η⟫) : Circle) • φ v)
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, map_mul, hreal v,
    inner_neg_right, neg_neg]
  congr 1
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]

theorem isRealFamily_constFamily {a : WienerDensity E N} (ha : IsRealDensity a) :
    IsRealFamily a.constFamily := fun _ => ha

end Schwartz

/-! ## Probes for every real Schwartz potential -/

section SchwartzProbe

open SchwartzMap

variable {d N : ℕ}

theorem kgChartPotential_ofSchwartz (φ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (y : Fin (d + 1) → ℝ) :
    kgChartPotential (WienerDensity.ofSchwartz (𝓕 φ) N).constFamily y
      = (φ (kgSpatial d y)).re - 1 := by
  rw [kgChartPotential]
  congr 2
  exact kgPotential_ofSchwartz_fourier φ N (kgSpatial d y)

/-- **Clock probes for every real Schwartz potential.** The chart potential is literally the given
function, shifted by the mass. -/
theorem exists_localProbesOn_schwartz
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (φ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (hreal : ∀ x : EuclideanSpace ℝ (Fin d), (starRingEnd ℂ) (φ x) = φ x)
    (x₀ : EuclideanSpace ℝ (Fin d)) :
    ∃ region : Set (Fin (d + 1) → ℝ), IsOpen region ∧ kgChartEvent d x₀ ∈ region ∧
      LocalProbesOn (kgWaveOp d)
        (kgChartPotential (WienerDensity.ofSchwartz (𝓕 φ) N).constFamily) region :=
  exists_localProbesOn_kgChartPotential _ hN
    (isRealFamily_constFamily (isRealDensity_ofSchwartz_fourier φ hreal N)) x₀

end SchwartzProbe

/-! ## Families from pointwise weighted bounds -/

section WeightedBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

theorem integrable_weight_of_pointwise {a : E → ℂ} {m : ℕ} {C : ℝ}
    (hdim : (Module.finrank ℝ E : ℝ) < m) (hmeas : AEStronglyMeasurable a (volume : Measure E))
    (hb : ∀ η : E, ‖a η‖ ≤ (kgFreq η ^ (N + m))⁻¹ * C) :
    Integrable (fun η : E => kgFreq η ^ N * ‖a η‖) (volume : Measure E) := by
  refine Integrable.mono' ((integrable_kgFreq_inv_pow (E := E) hdim).const_mul C)
    (((continuous_kgFreq.pow N).aestronglyMeasurable).mul hmeas.norm) ?_
  filter_upwards with η
  have hpos : (0 : ℝ) < kgFreq η ^ N := pow_pos (kgFreq_pos η) N
  have hsplit : (kgFreq η ^ (N + m))⁻¹ = (kgFreq η ^ N)⁻¹ * (kgFreq η ^ m)⁻¹ := by
    rw [pow_add, mul_inv]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpos.le (norm_nonneg _))]
  calc kgFreq η ^ N * ‖a η‖
      ≤ kgFreq η ^ N * ((kgFreq η ^ (N + m))⁻¹ * C) := mul_le_mul_of_nonneg_left (hb η) hpos.le
    _ = C * (kgFreq η ^ m)⁻¹ := by
        rw [hsplit]
        field_simp

theorem integral_weight_le_of_pointwise {a : E → ℂ} {m : ℕ} {C : ℝ}
    (hdim : (Module.finrank ℝ E : ℝ) < m) (hmeas : AEStronglyMeasurable a (volume : Measure E))
    (hb : ∀ η : E, ‖a η‖ ≤ (kgFreq η ^ (N + m))⁻¹ * C) :
    (∫ η : E, kgFreq η ^ N * ‖a η‖) ≤ C * ∫ η : E, (kgFreq η ^ m)⁻¹ := by
  have hint := integrable_weight_of_pointwise (N := N) hdim hmeas hb
  have hdom : Integrable (fun η : E => C * (kgFreq η ^ m)⁻¹) (volume : Measure E) :=
    (integrable_kgFreq_inv_pow (E := E) hdim).const_mul C
  have hle : ∀ η : E, kgFreq η ^ N * ‖a η‖ ≤ C * (kgFreq η ^ m)⁻¹ := by
    intro η
    have hpos : (0 : ℝ) < kgFreq η ^ N := pow_pos (kgFreq_pos η) N
    have hsplit : (kgFreq η ^ (N + m))⁻¹ = (kgFreq η ^ N)⁻¹ * (kgFreq η ^ m)⁻¹ := by
      rw [pow_add, mul_inv]
    calc kgFreq η ^ N * ‖a η‖
        ≤ kgFreq η ^ N * ((kgFreq η ^ (N + m))⁻¹ * C) := mul_le_mul_of_nonneg_left (hb η) hpos.le
      _ = C * (kgFreq η ^ m)⁻¹ := by
          rw [hsplit]
          field_simp
  have hmain := integral_mono hint hdom hle
  rw [integral_const_mul] at hmain
  exact hmain

/-- **A family from pointwise weighted bounds.** A curve of densities decaying like `⟨η⟩⁻ᴺ⁻ᵐ`
uniformly in time, and Lipschitz in time at that rate, is an admissible family. -/
noncomputable def WienerFamily.ofWeightedBounds {a : ℝ → E → ℂ} {m : ℕ} {M L : ℝ}
    (hdim : (Module.finrank ℝ E : ℝ) < m)
    (hmeas : ∀ t : ℝ, AEStronglyMeasurable (a t) (volume : Measure E))
    (hM : ∀ (t : ℝ) (η : E), ‖a t η‖ ≤ (kgFreq η ^ (N + m))⁻¹ * M) (hL0 : 0 ≤ L)
    (hL : ∀ (t t' : ℝ) (η : E),
      ‖a t η - a t' η‖ ≤ (kgFreq η ^ (N + m))⁻¹ * (L * |t - t'|)) :
    WienerFamily E N where
  density := fun t =>
    { toFun := a t
      aestronglyMeasurable := hmeas t
      integrable_weight := integrable_weight_of_pointwise hdim (hmeas t) (hM t) }
  bound := M * ∫ η : E, (kgFreq η ^ m)⁻¹
  norm_le := fun t => integral_weight_le_of_pointwise hdim (hmeas t) (hM t)
  lip := L * ∫ η : E, (kgFreq η ^ m)⁻¹
  lip_nonneg := by
    have hpos : 0 ≤ ∫ η : E, (kgFreq η ^ m)⁻¹ := by
      refine integral_nonneg fun η => ?_
      exact inv_nonneg.mpr (pow_pos (kgFreq_pos η) m).le
    exact mul_nonneg hL0 hpos
  lip_le := by
    intro t t'
    have hmeas' : AEStronglyMeasurable (fun η : E => a t η - a t' η) (volume : Measure E) :=
      (hmeas t).sub (hmeas t')
    have hmain := integral_weight_le_of_pointwise (N := N) hdim hmeas' (hL t t')
    refine hmain.trans_eq ?_
    ring

end WeightedBounds

/-! ## A non-separable time-dependent potential -/

section NonSeparable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kgFreq_neg (η : E) : kgFreq (-η) = kgFreq η := by
  rw [kgFreq, kgFreq, norm_neg]

/-- A density whose time dependence is *frequency dependent*: the potential it defines is not a
product of a function of time and a function of space. -/
noncomputable def kgWaveDensity (m : ℕ) (t : ℝ) (η : E) : ℂ :=
  (((kgFreq η ^ (N + m + 1))⁻¹ * Real.cos (t * kgFreq η) : ℝ) : ℂ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_kgWaveDensity (m : ℕ) (t : ℝ) :
    Continuous (kgWaveDensity (E := E) (N := N) m t) := by
  refine Complex.continuous_ofReal.comp (Continuous.mul ?_ ?_)
  · refine Continuous.inv₀ (continuous_kgFreq.pow (N + m + 1)) fun η => ?_
    exact (pow_pos (kgFreq_pos η) (N + m + 1)).ne'
  · exact Real.continuous_cos.comp (continuous_const.mul continuous_kgFreq)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_kgWaveDensity_le (m : ℕ) (t : ℝ) (η : E) :
    ‖kgWaveDensity (N := N) m t η‖ ≤ (kgFreq η ^ (N + m))⁻¹ * 1 := by
  have hpos : (0 : ℝ) < kgFreq η := kgFreq_pos η
  have hone : (1 : ℝ) ≤ kgFreq η := one_le_kgFreq η
  rw [kgWaveDensity, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_inv,
    abs_of_pos (pow_pos hpos (N + m + 1)), mul_one]
  have hcos : |Real.cos (t * kgFreq η)| ≤ 1 := Real.abs_cos_le_one _
  have hsplit : (kgFreq η ^ (N + m + 1))⁻¹ = (kgFreq η ^ (N + m))⁻¹ * (kgFreq η)⁻¹ := by
    rw [pow_succ, mul_inv]
  have hinv : (kgFreq η)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact hone
  have hbase : (0 : ℝ) < (kgFreq η ^ (N + m))⁻¹ := inv_pos.mpr (pow_pos hpos (N + m))
  rw [hsplit]
  have hnn : (0 : ℝ) ≤ (kgFreq η ^ (N + m))⁻¹ * (kgFreq η)⁻¹ :=
    mul_nonneg hbase.le (inv_nonneg.mpr hpos.le)
  calc (kgFreq η ^ (N + m))⁻¹ * (kgFreq η)⁻¹ * |Real.cos (t * kgFreq η)|
      ≤ (kgFreq η ^ (N + m))⁻¹ * (kgFreq η)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hcos hnn
    _ ≤ (kgFreq η ^ (N + m))⁻¹ * 1 * 1 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hbase.le) zero_le_one
    _ = (kgFreq η ^ (N + m))⁻¹ := by ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_kgWaveDensity_sub_le (m : ℕ) (t t' : ℝ) (η : E) :
    ‖kgWaveDensity (N := N) m t η - kgWaveDensity (N := N) m t' η‖
      ≤ (kgFreq η ^ (N + m))⁻¹ * (1 * |t - t'|) := by
  have hpos : (0 : ℝ) < kgFreq η := kgFreq_pos η
  have hsub : kgWaveDensity (N := N) m t η - kgWaveDensity (N := N) m t' η
      = (((kgFreq η ^ (N + m + 1))⁻¹
        * (Real.cos (t * kgFreq η) - Real.cos (t' * kgFreq η)) : ℝ) : ℂ) := by
    rw [kgWaveDensity, kgWaveDensity, ← Complex.ofReal_sub]
    congr 1
    ring
  have hlip : |Real.cos (t * kgFreq η) - Real.cos (t' * kgFreq η)| ≤ |t - t'| * kgFreq η := by
    have h := Real.lipschitzWith_cos.dist_le_mul (t * kgFreq η) (t' * kgFreq η)
    rw [Real.dist_eq, Real.dist_eq] at h
    have hmul : |t * kgFreq η - t' * kgFreq η| = |t - t'| * kgFreq η := by
      rw [← sub_mul, abs_mul, abs_of_pos hpos]
    simpa [hmul] using h
  rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_inv,
    abs_of_pos (pow_pos hpos (N + m + 1)), one_mul]
  have hsplit : (kgFreq η ^ (N + m + 1))⁻¹ = (kgFreq η ^ (N + m))⁻¹ * (kgFreq η)⁻¹ := by
    rw [pow_succ, mul_inv]
  rw [hsplit, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (pow_pos hpos (N + m)).le)
  rw [inv_mul_eq_div, div_le_iff₀ hpos]
  exact hlip

/-- **A genuinely time-dependent, non-separable admissible family.** -/
noncomputable def kgWaveFamily {m : ℕ} (hdim : (Module.finrank ℝ E : ℝ) < m) :
    WienerFamily E N :=
  WienerFamily.ofWeightedBounds (a := kgWaveDensity (E := E) (N := N) m) hdim
    (fun t => (continuous_kgWaveDensity m t).aestronglyMeasurable)
    (norm_kgWaveDensity_le m) zero_le_one (norm_kgWaveDensity_sub_le m)

theorem isRealFamily_kgWaveFamily {m : ℕ} (hdim : (Module.finrank ℝ E : ℝ) < m) :
    IsRealFamily (kgWaveFamily (E := E) (N := N) hdim) := by
  intro t η
  show kgWaveDensity (N := N) m t (-η) = (starRingEnd ℂ) (kgWaveDensity (N := N) m t η)
  rw [kgWaveDensity, kgWaveDensity, Complex.conj_ofReal, kgFreq_neg]

/-- **Clock probes for a non-separable time-dependent potential.** -/
theorem exists_localProbesOn_wave {d N m : ℕ}
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < m)
    (x₀ : EuclideanSpace ℝ (Fin d)) :
    ∃ region : Set (Fin (d + 1) → ℝ), IsOpen region ∧ kgChartEvent d x₀ ∈ region ∧
      LocalProbesOn (kgWaveOp d)
        (kgChartPotential (kgWaveFamily (E := EuclideanSpace ℝ (Fin d)) (N := N) hdim)) region :=
  exists_localProbesOn_kgChartPotential _ hN (isRealFamily_kgWaveFamily hdim) x₀

end NonSeparable

end GaloisForLFunctions.HTGeometry
