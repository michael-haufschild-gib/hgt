import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheIncompleteEisensteinSeriesReadsTheConstantTerm
import GaloisForLFunctions.MetaplecticMobiusDescent.WeightedCubicResidualFourierTests

/-!
# The square of the cubic theta function unfolds

Let `θ = cubicResidualFunction` be the continuous residue of the cubic Eisenstein series at
`s = 4/3` (MMD): `θ(Mw) = κ(M) θ(w)` and

`θ(z + jv) = c v^{2/3} + Σ_{h ≠ 0} a(v, h) e(ξ_h z)`,   `c = 3π r`,
`a(v, h) = T(h) v K_{1/3}(4π|ξ_h| v)`   (`theta_upperPoint`, `thetaAmplitude_bessel`).

* `thetaSq_automorphy`: `θ²` has multiplier `κ² = κ⁻¹` (`κ³ = 1`), so it unfolds against the
  incomplete Eisenstein series.
* `integral_thetaSq_periodDomain` (**the constant term of `θ²`**): the cross term `c v^{2/3} ∫_P S`
  vanishes and Parseval on `P` gives
  `∫_P θ(z + jv)² dz = |P| (c² v^{4/3} + Σ_h a(v, h) a(v, −h))`.
* `integral_thetaSq_mul_incompleteEisenstein` (**Rankin–Selberg for `θ²`**):
  `∫_{D_Γ} θ² E(·∣ψ) dμ = |P| ∫_0^∞ ψ(v) (c² v^{4/3} + Σ_h a(v, h) a(v, −h)) v^{−3} dv`.

The growth term `c² v^{4/3}` is the square of the constant term of `θ`; the series is
`v² Σ_{h ≠ 0} T(h) T(−h) K_{1/3}(4π|ξ_h| v)²`, whose Mellin transform is the Dirichlet series of the
products `T(h) T(−h)`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein

/-- The cubic theta function: the continuous residue of the cubic Eisenstein series at `4/3`. -/
abbrev theta : HyperbolicSpace → ℂ := cubicResidualFunction

/-- The constant `c = 3π r` of `θ`. -/
abbrev thetaConstant : ℂ := 3 * (Real.pi : ℂ) * constantArithmeticResidue

/-- The Fourier amplitude `a(v, h)` of `θ` at height `v`. -/
abbrev thetaAmplitude (v : ℝ) (h : O) : ℂ := cubicResidualNonzeroAmplitude v h

/-- The area `|P|` of the period parallelogram, as a complex number. -/
abbrev periodArea : ℂ := ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)

/-! ### The multiplier of `θ²` -/

/-- **`θ²` has multiplier `κ⁻¹`.** -/
theorem thetaSq_automorphy (M : levelThree) (w : HyperbolicSpace) :
    theta (complexMatrix M • w) ^ 2 = (complexCharacter M)⁻¹ * theta w ^ 2 := by
  have h3 := complexCharacter_cube M
  have hne : complexCharacter M ≠ 0 := by
    intro h
    rw [h] at h3
    norm_num at h3
  rw [show theta = cubicResidualFunction from rfl, cubicResidualFunction_automorphy, mul_pow]
  field_simp
  linear_combination cubicResidualFunction w ^ 2 * h3

/-! ### The Fourier expansion at a height -/

theorem theta_upperPoint (z : ℂ) (v : ℝ) (hv : 0 < v) :
    theta (upperPoint z v hv) = thetaConstant * (v : ℂ) ^ (2 / 3 : ℂ) +
      cubicResidualNonzeroSeries (v, z) := by
  simp only [theta, cubicResidualFunction, hyperbolicHeight_upperPoint, hyperbolicHorizontal_upperPoint]

theorem nonzeroSeries_eq (v : ℝ) (hv : 0 < v) (z : ℂ) :
    cubicResidualNonzeroSeries (v, z) =
      ∑' h : O, thetaAmplitude v h * tracePhase (cuspFrequency h * z) :=
  tsum_congr fun h => cubicResidualNonzeroTerm_eq_amplitude v hv h z

/-- For `h ≠ 0`, `a(v, h) = T(h) v K_{1/3}(4π|ξ_h| v)`. -/
theorem thetaAmplitude_bessel (v : ℝ) (hv : 0 < v) (h : O) (hh : h ≠ 0) :
    thetaAmplitude v h = cubicResidualFourierCoefficient h * (v : ℂ) *
      schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) := by
  have h1 := cubicResidualNonzeroTerm_eq_amplitude v hv h 0
  rw [cubicResidualNonzeroTerm_bessel h hh v hv 0] at h1
  simp only [mul_zero, AddChar.map_zero_eq_one, mul_one] at h1
  exact h1.symm

/-- The paired amplitudes: `a(v, 0) a(v, 0) = 0` and, for `h ≠ 0`,
`a(v, h) a(v, −h) = T(h) T(−h) v² K_{1/3}(4π|ξ_h| v)²`. -/
theorem thetaAmplitude_mul_neg (v : ℝ) (hv : 0 < v) (h : O) :
    thetaAmplitude v h * thetaAmplitude v (-h) =
      if h = 0 then 0 else cubicResidualFourierCoefficient h * cubicResidualFourierCoefficient (-h) *
        (v : ℂ) ^ 2 * schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) ^ 2 := by
  by_cases hh : h = 0
  · subst hh
    simp [cubicResidualNonzeroAmplitude]
  · rw [if_neg hh, thetaAmplitude_bessel v hv h hh, thetaAmplitude_bessel v hv (-h) (neg_ne_zero.mpr hh),
      cuspFrequency_neg, norm_neg]
    ring

/-- A uniform bound for the amplitudes at a fixed height. -/
theorem thetaAmplitude_summable (v : ℝ) (hv : 0 < v) :
    Summable (fun h : O => ‖thetaAmplitude v h‖) := by
  refine (cubicResidualNonzeroTerm_summable_norm (v, 0) hv).congr fun h => ?_
  rw [cubicResidualNonzeroTerm_eq_amplitude v hv h 0, norm_mul, tracePhase_norm, mul_one]

theorem nonzeroSeries_norm_le (v : ℝ) (hv : 0 < v) (z : ℂ) :
    ‖cubicResidualNonzeroSeries (v, z)‖ ≤ ∑' h : O, ‖thetaAmplitude v h‖ := by
  rw [nonzeroSeries_eq v hv z]
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun h => ?_))
  · exact (thetaAmplitude_summable v hv).congr fun h => by rw [norm_mul, tracePhase_norm, mul_one]
  · rw [norm_mul, tracePhase_norm, mul_one]

theorem nonzeroSeries_continuous (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => cubicResidualNonzeroSeries (v, z)) := by
  refine continuous_iff_continuousAt.mpr fun z => ?_
  have hmem : (v, z) ∈ {p : ℝ × ℂ | 0 < p.1} := hv
  have hopen : IsOpen {p : ℝ × ℂ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  exact ((cubicResidualNonzeroSeries_continuousOn.continuousAt (hopen.mem_nhds hmem)).comp
    (Continuous.continuousAt (by fun_prop)))

/-- Bounded continuous functions are integrable on the period parallelogram. -/
theorem integrableOn_periodDomain_of_continuous (f : ℂ → ℂ) (hf : Continuous f) :
    IntegrableOn f periodDomain := by
  have hc := hf.continuousOn (s := Metric.closedBall (0 : ℂ) (∑ i : Fin 2, ‖periodBasis i‖))
  refine (hc.integrableOn_compact (isCompact_closedBall _ _)).mono_set fun z hz => ?_
  simpa only [Metric.mem_closedBall, dist_zero_right] using norm_mem_periodDomain z hz

/-! ### The constant term of `θ²` -/

/-- `∫_P S(v, z) dz = 0`. -/
theorem integral_nonzeroSeries (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, cubicResidualNonzeroSeries (v, z) = 0 := by
  have h := cubicResidualNonzeroSeries_fourier v hv 0
  have h0 : cuspFrequency 0 = 0 := by simp [cuspFrequency]
  simp only [h0, neg_zero, zero_mul, AddChar.map_zero_eq_one, mul_one] at h
  rw [h, cubicResidualNonzeroAmplitude, if_pos rfl, mul_zero]

/-- `∫_P S(v, z) e(ξ_h z) dz = |P| a(v, −h)`. -/
theorem integral_nonzeroSeries_mul_phase (v : ℝ) (hv : 0 < v) (h : O) :
    ∫ z in periodDomain, cubicResidualNonzeroSeries (v, z) * tracePhase (cuspFrequency h * z) =
      periodArea * thetaAmplitude v (-h) := by
  have hk := cubicResidualNonzeroSeries_fourier v hv (-h)
  simp only [cuspFrequency_neg, neg_neg] at hk
  exact hk

/-- **Parseval on `P`.** `∫_P S(v, z)² dz = |P| Σ_h a(v, h) a(v, −h)`. -/
theorem integral_nonzeroSeries_sq (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, cubicResidualNonzeroSeries (v, z) ^ 2 =
      periodArea * ∑' h : O, thetaAmplitude v h * thetaAmplitude v (-h) := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have hSc := nonzeroSeries_continuous v hv
  have hphase : ∀ h : O, Continuous (fun z : ℂ => tracePhase (cuspFrequency h * z)) := by
    intro h
    change Continuous (fun z : ℂ => Complex.exp (2 * Real.pi * Complex.I *
      ((cuspFrequency h * z) + starRingEnd ℂ (cuspFrequency h * z))))
    fun_prop
  have hfin : volume periodDomain ≠ ⊤ := by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top
  have hFc : ∀ h : O, Continuous (fun z : ℂ => thetaAmplitude v h *
      (cubicResidualNonzeroSeries (v, z) * tracePhase (cuspFrequency h * z))) := fun h =>
    continuous_const.mul (hSc.mul (hphase h))
  have hi : ∀ h : O, Integrable (fun z : ℂ => thetaAmplitude v h *
      (cubicResidualNonzeroSeries (v, z) * tracePhase (cuspFrequency h * z)))
      (volume.restrict periodDomain) := fun h => integrableOn_periodDomain_of_continuous _ (hFc h)
  -- `‖a_h S e_h‖ ≤ ‖a_h‖ B` with `B = Σ ‖a_h‖`
  have hpt : ∀ (h : O) (z : ℂ), ‖thetaAmplitude v h *
      (cubicResidualNonzeroSeries (v, z) * tracePhase (cuspFrequency h * z))‖ ≤
        ‖thetaAmplitude v h‖ * ∑' k : O, ‖thetaAmplitude v k‖ := by
    intro h z
    rw [norm_mul, norm_mul, tracePhase_norm, mul_one]
    exact mul_le_mul_of_nonneg_left (nonzeroSeries_norm_le v hv z) (norm_nonneg _)
  have hint_le : ∀ h : O, ∫ z in periodDomain, ‖thetaAmplitude v h *
      (cubicResidualNonzeroSeries (v, z) * tracePhase (cuspFrequency h * z))‖ ≤
        ‖thetaAmplitude v h‖ * (∑' k : O, ‖thetaAmplitude v k‖) * (volume periodDomain).toReal := by
    intro h
    have hc : IntegrableOn (fun _ : ℂ => ‖thetaAmplitude v h‖ * ∑' k : O, ‖thetaAmplitude v k‖)
        periodDomain := integrableOn_const (μ := volume) hfin
    calc _ ≤ ∫ _ in periodDomain, ‖thetaAmplitude v h‖ * ∑' k : O, ‖thetaAmplitude v k‖ :=
          setIntegral_mono_on (hi h).norm hc periodDomain_measurable (fun z _ => hpt h z)
      _ = _ := by rw [setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
  have hsum : Summable (fun h : O => ∫ z in periodDomain, ‖thetaAmplitude v h *
      (cubicResidualNonzeroSeries (v, z) * tracePhase (cuspFrequency h * z))‖) :=
    Summable.of_nonneg_of_le (fun h => integral_nonneg fun z => norm_nonneg _) hint_le
      (((thetaAmplitude_summable v hv).mul_right _).mul_right _)
  -- `S² = Σ_h a_h S e_h`
  have hsq : ∀ z : ℂ, cubicResidualNonzeroSeries (v, z) ^ 2 = ∑' h : O, thetaAmplitude v h *
      (cubicResidualNonzeroSeries (v, z) * tracePhase (cuspFrequency h * z)) := by
    intro z
    calc cubicResidualNonzeroSeries (v, z) ^ 2 =
          cubicResidualNonzeroSeries (v, z) * cubicResidualNonzeroSeries (v, z) := sq _
      _ = cubicResidualNonzeroSeries (v, z) *
          ∑' h : O, thetaAmplitude v h * tracePhase (cuspFrequency h * z) :=
          congrArg (fun t => cubicResidualNonzeroSeries (v, z) * t) (nonzeroSeries_eq v hv z)
      _ = ∑' h : O, cubicResidualNonzeroSeries (v, z) *
          (thetaAmplitude v h * tracePhase (cuspFrequency h * z)) := tsum_mul_left.symm
      _ = _ := tsum_congr fun h => by ring
  simp_rw [hsq]
  rw [← integral_tsum_of_summable_integral_norm hi hsum]
  calc ∑' h : O, ∫ z in periodDomain, thetaAmplitude v h *
        (cubicResidualNonzeroSeries (v, z) * tracePhase (cuspFrequency h * z))
      = ∑' h : O, periodArea * (thetaAmplitude v h * thetaAmplitude v (-h)) :=
        tsum_congr fun h => by
          rw [integral_const_mul, integral_nonzeroSeries_mul_phase v hv h]
          ring
    _ = _ := tsum_mul_left

/-- **The constant term of `θ²`.** `∫_P θ(z + jv)² dz = |P| (c² v^{4/3} + Σ_h a(v, h) a(v, −h))`. -/
theorem integral_thetaSq_periodDomain (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, theta (upperPoint z v hv) ^ 2 =
      periodArea * (thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ) +
        ∑' h : O, thetaAmplitude v h * thetaAmplitude v (-h)) := by
  have hSc := nonzeroSeries_continuous v hv
  have hexp : ∀ z, theta (upperPoint z v hv) ^ 2 =
      thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ) +
        (2 * thetaConstant * (v : ℂ) ^ (2 / 3 : ℂ)) * cubicResidualNonzeroSeries (v, z) +
          cubicResidualNonzeroSeries (v, z) ^ 2 := by
    intro z
    have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
    have hp : (v : ℂ) ^ (4 / 3 : ℂ) = (v : ℂ) ^ (2 / 3 : ℂ) * (v : ℂ) ^ (2 / 3 : ℂ) := by
      rw [← Complex.cpow_add _ _ hv0]
      norm_num
    rw [theta_upperPoint, hp]
    ring
  simp_rw [hexp]
  have hI1 : IntegrableOn (fun _ : ℂ => thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ)) periodDomain :=
    integrableOn_periodDomain_of_continuous _ continuous_const
  have hI2 : IntegrableOn (fun z : ℂ => (2 * thetaConstant * (v : ℂ) ^ (2 / 3 : ℂ)) *
      cubicResidualNonzeroSeries (v, z)) periodDomain :=
    integrableOn_periodDomain_of_continuous _ (continuous_const.mul hSc)
  have hI3 : IntegrableOn (fun z : ℂ => cubicResidualNonzeroSeries (v, z) ^ 2) periodDomain :=
    integrableOn_periodDomain_of_continuous _ (hSc.pow 2)
  have hI12 : IntegrableOn (fun z : ℂ => thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ) +
      (2 * thetaConstant * (v : ℂ) ^ (2 / 3 : ℂ)) * cubicResidualNonzeroSeries (v, z)) periodDomain :=
    hI1.add hI2
  rw [integral_add hI12 hI3, integral_add hI1 hI2, setIntegral_const, integral_const_mul,
    integral_nonzeroSeries v hv, integral_nonzeroSeries_sq v hv]
  have hvol : (volume periodDomain).toReal = 9 * Real.sqrt 3 / 2 := by
    rw [periodDomain_volume, ENNReal.toReal_ofReal (by positivity)]
  rw [Measure.real, hvol, Complex.real_smul]
  ring

/-! ### Rankin–Selberg for `θ²` -/

/-- **Rankin–Selberg for `θ²`.** If `θ² ψ(v)` is integrable on the period strip, then
`∫_{D_Γ} θ² E(·∣ψ) dμ = |P| ∫_0^∞ ψ(v) (c² v^{4/3} + Σ_h a(v, h) a(v, −h)) v^{−3} dv`. -/
theorem integral_thetaSq_mul_incompleteEisenstein (ψ : ℝ → ℂ)
    (hint : IntegrableOn (unfolded (fun w => theta w ^ 2) ψ) cuspStripSet hyperbolicVolume) :
    ∫ w in levelSet, theta w ^ 2 * incompleteEisenstein ψ w ∂hyperbolicVolume =
      ∫ v in Set.Ioi (0 : ℝ), ψ v * (periodArea * (thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ) +
        ∑' h : O, thetaAmplitude v h * thetaAmplitude v (-h))) / (v : ℂ) ^ 3 := by
  refine (integral_mul_incompleteEisenstein_eq_constantTerm (fun w => theta w ^ 2)
    thetaSq_automorphy ψ hint).trans ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hlift : ∀ z : ℂ, cuspCoordinateLift (v, z) = upperPoint z v hv := fun z =>
    cuspCoordinateLift_positive v z hv
  simp only [hlift]
  rw [integral_thetaSq_periodDomain v hv]

/-- For a continuous profile `ψ` supported in `[a, b] ⊂ (0, ∞)`, `θ² ψ(v)` is integrable on the
period strip: it is continuous, vanishes off heights `[a, b]`, and the compact-height strip has
finite volume. -/
theorem integrableOn_unfolded_thetaSq (ψ : ℝ → ℂ) (hψ : Continuous ψ) (a b : ℝ) (ha : 0 < a)
    (hsupp : ∀ v, v ∉ Set.Icc a b → ψ v = 0) :
    IntegrableOn (unfolded (fun w => theta w ^ 2) ψ) cuspStripSet hyperbolicVolume := by
  have hc : Continuous (unfolded (fun w => theta w ^ 2) ψ) :=
    (cubicResidualFunction_continuous.pow 2).mul (hψ.comp hyperbolicHeight_continuous)
  refine (cuspStrip_integrable_continuous a b ha _ hc).of_forall_sdiff_eq_zero
    cuspStripSet_measurable fun w hw => ?_
  have hv : hyperbolicHeight w ∉ Set.Icc a b := fun hv => hw.2 ⟨hw.1, hv⟩
  simp only [unfolded, hsupp _ hv, mul_zero]

/-- **Rankin–Selberg for `θ²`, compactly supported profiles.** For `ψ` continuous and supported in
`[a, b] ⊂ (0, ∞)`:
`∫_{D_Γ} θ² E(·∣ψ) dμ = |P| ∫_0^∞ ψ(v) (c² v^{4/3} + Σ_h a(v, h) a(v, −h)) v^{−3} dv`. -/
theorem integral_thetaSq_mul_incompleteEisenstein_of_compact (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hsupp : ∀ v, v ∉ Set.Icc a b → ψ v = 0) :
    ∫ w in levelSet, theta w ^ 2 * incompleteEisenstein ψ w ∂hyperbolicVolume =
      ∫ v in Set.Ioi (0 : ℝ), ψ v * (periodArea * (thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ) +
        ∑' h : O, thetaAmplitude v h * thetaAmplitude v (-h))) / (v : ℂ) ^ 3 :=
  integral_thetaSq_mul_incompleteEisenstein ψ (integrableOn_unfolded_thetaSq ψ hψ a b ha hsupp)

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
