import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolApertureDefectColligation
import GaloisForLFunctions.RHTower.Sieve.PrimeLogPowerTail

/-!
# Route P primitive Burnol aperture defect first flux

P-G188's exact aperture colligation has a nonzero first-order defect, but the boundary-interval
channel is first-order flat on every primitive Burnol feature. The entire opening flux is carried
by the distributed tail cocycle. Its primitive family is summable, while every Hilbert-valued
realization of one nonzero defect channel is necessarily nondifferentiable at aperture zero.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- First aperture-time flux of one primitive Burnol defect mass. -/
def routePPrimitiveBurnolApertureDefectFlux
    (pe : Nat.Primes × ℕ) : ℝ :=
  2 * xiGammaEulerPrimitiveLogFrequency pe *
    routePPrimitiveBaseCauchyCubicWeight pe

/-- Boundary-interval energy of one primitive Burnol feature. -/
def routePPrimitiveBurnolApertureBoundaryDefectEnergy
    (c : ℝ) (pe : Nat.Primes × ℕ) (kappa : ℝ) : ℝ :=
  routePBurnolApertureEnergy
    (routePBurnolApertureBoundaryDefect c
      (routePPrimitiveBurnolWindowFeature pe kappa))

/-- Distributed tail-cocycle energy of one primitive Burnol feature. -/
def routePPrimitiveBurnolApertureTailDefectEnergy
    (c : ℝ) (pe : Nat.Primes × ℕ) (kappa : ℝ) : ℝ :=
  routePBurnolApertureEnergy
    (routePBurnolApertureTailDefect c
      (routePPrimitiveBurnolWindowFeature pe kappa))

/-- Primitive defect mass has the exact first aperture derivative `2 lambda w`. -/
theorem hasDerivAt_routePPrimitiveBurnolApertureDefectMass_zero
    (pe : Nat.Primes × ℕ) :
    HasDerivAt (fun c : ℝ => routePPrimitiveBurnolApertureDefectMass c pe)
      (routePPrimitiveBurnolApertureDefectFlux pe) 0 := by
  let lambda := xiGammaEulerPrimitiveLogFrequency pe
  let w := routePPrimitiveBaseCauchyCubicWeight pe
  have hlinear : HasDerivAt (fun c : ℝ => -2 * c * lambda) (-2 * lambda) 0 := by
    simpa only [id_eq, mul_one] using!
      ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul (-2)).mul_const lambda
  have hexp : HasDerivAt (fun c : ℝ => Real.exp (-2 * c * lambda))
      (-2 * lambda) 0 := by
    have hraw := (Real.hasDerivAt_exp (-2 * 0 * lambda)).comp 0 hlinear
    simpa only [Function.comp_apply] using! hraw.congr_deriv (by simp)
  have hsub : HasDerivAt (fun c : ℝ => 1 - Real.exp (-2 * c * lambda))
      (2 * lambda) 0 := by
    have hraw := (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub hexp
    simpa only [Pi.sub_apply] using! hraw.congr_deriv (by ring)
  unfold routePPrimitiveBurnolApertureDefectMass
  change HasDerivAt (fun c : ℝ => (1 - Real.exp (-2 * c * lambda)) * w)
    (routePPrimitiveBurnolApertureDefectFlux pe) 0
  simpa only [routePPrimitiveBurnolApertureDefectFlux, lambda, w] using hsub.mul_const w

theorem routePPrimitiveBurnolWindowFeature_zero
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    routePPrimitiveBurnolWindowFeature pe kappa 0 = 0 := by
  rw [routePPrimitiveBurnolWindowFeature,
    xiWardCubicBurnolWindowConormalFeature_eq,
    routePXiBaseConormalResidueFeature]
  simp

/-- The hard-edge interval carries no first-order primitive defect flux. -/
theorem tendsto_routePPrimitiveBurnolApertureBoundaryDefectEnergy_div_zero
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    Tendsto
      (fun c : ℝ =>
        routePPrimitiveBurnolApertureBoundaryDefectEnergy c pe kappa / c)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let f : ℝ → ℂ := routePPrimitiveBurnolWindowFeature pe kappa
  let g : ℝ → ℝ := fun u => ‖f u‖ ^ 2
  have hfcont : Continuous f := continuous_routePPrimitiveBurnolWindowFeature pe kappa
  have hgcont : Continuous g := by
    dsimp only [g]
    fun_prop
  have hg0 : g 0 = 0 := by
    dsimp only [g, f]
    rw [routePPrimitiveBurnolWindowFeature_zero]
    norm_num
  have hftc : HasDerivAt (fun c : ℝ => ∫ u in (0 : ℝ)..c, g u) 0 0 := by
    have hraw := intervalIntegral.integral_hasDerivAt_right
      (hgcont.intervalIntegrable (0 : ℝ) 0)
      hgcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hgcont.continuousAt
    simpa only [hg0] using hraw
  have hslope := hftc.tendsto_slope_zero_right
  apply hslope.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  change 0 < c at hc
  rw [zero_add]
  have hboundary :
      routePPrimitiveBurnolApertureBoundaryDefectEnergy c pe kappa =
        ∫ u in (0 : ℝ)..c, g u := by
    rw [routePPrimitiveBurnolApertureBoundaryDefectEnergy,
      routePBurnolApertureEnergy_boundaryDefect,
      intervalIntegral.integral_of_le hc.le]
  rw [hboundary]
  simp only [intervalIntegral.integral_same, sub_zero, smul_eq_mul, div_eq_mul_inv]
  ring

/-- **P-G189 tail concentration.** The distributed cocycle carries the entire first-order defect
flux; the deleted boundary interval contributes only higher order. -/
theorem tendsto_routePPrimitiveBurnolApertureTailDefectEnergy_div_zero
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    Tendsto
      (fun c : ℝ =>
        routePPrimitiveBurnolApertureTailDefectEnergy c pe kappa / c)
      (nhdsWithin 0 (Ioi 0))
      (nhds (routePPrimitiveBurnolApertureDefectFlux pe)) := by
  have hmassRaw :=
    (hasDerivAt_routePPrimitiveBurnolApertureDefectMass_zero pe).tendsto_slope_zero_right
  have hmass :
      Tendsto
        (fun c : ℝ => routePPrimitiveBurnolApertureDefectMass c pe / c)
        (nhdsWithin 0 (Ioi 0))
        (nhds (routePPrimitiveBurnolApertureDefectFlux pe)) := by
    convert hmassRaw using 1
    ext c
    rw [zero_add]
    simp [routePPrimitiveBurnolApertureDefectMass]
    ring
  have hboundary :=
    tendsto_routePPrimitiveBurnolApertureBoundaryDefectEnergy_div_zero pe kappa
  have hdiff := hmass.sub hboundary
  have hdiff' :
      Tendsto
        (fun c : ℝ => routePPrimitiveBurnolApertureDefectMass c pe / c -
          routePPrimitiveBurnolApertureBoundaryDefectEnergy c pe kappa / c)
        (nhdsWithin 0 (Ioi 0))
        (nhds (routePPrimitiveBurnolApertureDefectFlux pe)) := by
    simpa only [sub_zero] using hdiff
  apply hdiff'.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  change 0 < c at hc
  have hcoll := routePPrimitiveBurnolApertureDefect_energy_eq_mass hc.le pe kappa
  change routePPrimitiveBurnolApertureBoundaryDefectEnergy c pe kappa +
      routePPrimitiveBurnolApertureTailDefectEnergy c pe kappa =
    routePPrimitiveBurnolApertureDefectMass c pe at hcoll
  rw [← hcoll]
  ring

/-- Every primitive defect flux is strictly positive. -/
theorem routePPrimitiveBurnolApertureDefectFlux_pos
    (pe : Nat.Primes × ℕ) :
    0 < routePPrimitiveBurnolApertureDefectFlux pe := by
  rw [routePPrimitiveBurnolApertureDefectFlux,
    routePPrimitiveBaseCauchyCubicWeight,
    xiGammaEulerPrimitiveCubicLogMomentWeight, invNatLogSq]
  have hp : (0 : ℝ) < (pe.1 : ℝ) := by exact_mod_cast pe.1.property.pos
  have hlog : 0 < Real.log (pe.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast pe.1.property.one_lt)
  have hlambda := xiGammaEulerPrimitiveLogFrequency_pos pe
  positivity

/-- Arithmetic normal form of the primitive aperture flux: one aperture derivative removes one
inverse logarithm and one inverse depth factor from the cubic source mass. -/
theorem routePPrimitiveBurnolApertureDefectFlux_eq
    (pe : Nat.Primes × ℕ) :
    routePPrimitiveBurnolApertureDefectFlux pe =
      (1 / 2 : ℝ) *
        (1 / ((pe.1 : ℝ) * Real.log (pe.1 : ℝ))) *
        ((pe.1 : ℝ)⁻¹) ^ pe.2 *
        (((pe.2 : ℝ) + 1) ^ 2)⁻¹ := by
  have hp : (0 : ℝ) < (pe.1 : ℝ) := by exact_mod_cast pe.1.property.pos
  have hlog : Real.log (pe.1 : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast pe.1.property.one_lt)).ne'
  have hk : ((pe.2 : ℝ) + 1) ≠ 0 := by positivity
  have hfrequency :
      xiGammaEulerPrimitiveLogFrequency pe =
        ((pe.2 : ℝ) + 1) * Real.log (pe.1 : ℝ) := by
    rw [xiGammaEulerPrimitiveLogFrequency, xiGammaEulerValuationNat,
      Nat.cast_pow, Real.log_pow]
    push_cast
    ring
  rw [routePPrimitiveBurnolApertureDefectFlux,
    routePPrimitiveBaseCauchyCubicWeight,
    xiGammaEulerPrimitiveCubicLogMomentWeight, invNatLogSq,
    hfrequency]
  field_simp [hp.ne', hlog, hk]
  ring

theorem routePPrimitiveBurnolApertureDefectFlux_le_geometric
    (pe : Nat.Primes × ℕ) :
    routePPrimitiveBurnolApertureDefectFlux pe ≤
      (1 / 2 : ℝ) *
        (1 / ((pe.1 : ℝ) * Real.log (pe.1 : ℝ))) *
        (1 / 2 : ℝ) ^ pe.2 := by
  have hp : (0 : ℝ) < (pe.1 : ℝ) := by exact_mod_cast pe.1.property.pos
  have hp2 : (2 : ℝ) ≤ (pe.1 : ℝ) := by exact_mod_cast pe.1.property.two_le
  have hlog : 0 < Real.log (pe.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast pe.1.property.one_lt)
  have hpInv : (pe.1 : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using
      (inv_le_inv₀ hp (by norm_num : (0 : ℝ) < 2)).2 hp2
  have hpPow : ((pe.1 : ℝ)⁻¹) ^ pe.2 ≤ (1 / 2 : ℝ) ^ pe.2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hp.le) hpInv pe.2
  have hkOne : (1 : ℝ) ≤ (pe.2 : ℝ) + 1 := by
    exact_mod_cast Nat.le_add_left 1 pe.2
  have hkSq : (1 : ℝ) ≤ ((pe.2 : ℝ) + 1) ^ 2 := one_le_pow₀ hkOne
  have hkInv : (((pe.2 : ℝ) + 1) ^ 2)⁻¹ ≤ (1 : ℝ) := by
    simpa using
      (inv_le_inv₀ (by positivity : 0 < ((pe.2 : ℝ) + 1) ^ 2)
        (by norm_num : (0 : ℝ) < 1)).2 hkSq
  have hcoefficient :
      0 ≤ (1 / 2 : ℝ) *
        (1 / ((pe.1 : ℝ) * Real.log (pe.1 : ℝ))) := by positivity
  rw [routePPrimitiveBurnolApertureDefectFlux_eq]
  calc
    (1 / 2 : ℝ) * (1 / ((pe.1 : ℝ) * Real.log (pe.1 : ℝ))) *
          ((pe.1 : ℝ)⁻¹) ^ pe.2 * (((pe.2 : ℝ) + 1) ^ 2)⁻¹ ≤
        (1 / 2 : ℝ) * (1 / ((pe.1 : ℝ) * Real.log (pe.1 : ℝ))) *
          (1 / 2 : ℝ) ^ pe.2 * (((pe.2 : ℝ) + 1) ^ 2)⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpPow hcoefficient)
        (inv_nonneg.mpr (by positivity))
    _ ≤ (1 / 2 : ℝ) * (1 / ((pe.1 : ℝ) * Real.log (pe.1 : ℝ))) *
          (1 / 2 : ℝ) ^ pe.2 * 1 := by
      exact mul_le_mul_of_nonneg_left hkInv
        (mul_nonneg hcoefficient (by positivity))
    _ = _ := by ring

/-- The complete first-flux family is summable. Thus the square-root singularity is compatible
with one global trace-finite Wold noise channel. -/
theorem summable_routePPrimitiveBurnolApertureDefectFlux :
    Summable routePPrimitiveBurnolApertureDefectFlux := by
  let major : Nat.Primes × ℕ → ℝ := fun pe =>
    (1 / 2 : ℝ) *
      (1 / ((pe.1 : ℝ) * Real.log (pe.1 : ℝ))) *
      (1 / 2 : ℝ) ^ pe.2
  have hmajorNonneg : 0 ≤ major := by
    intro pe
    dsimp only [major]
    have hp : (0 : ℝ) < (pe.1 : ℝ) := by exact_mod_cast pe.1.property.pos
    have hlog : 0 < Real.log (pe.1 : ℝ) :=
      Real.log_pos (by exact_mod_cast pe.1.property.one_lt)
    positivity
  have hmajor : Summable major := by
    rw [summable_prod_of_nonneg hmajorNonneg]
    constructor
    · intro p
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left
        ((1 / 2 : ℝ) * (1 / ((p : ℝ) * Real.log (p : ℝ))))
    · have hprime : Summable
          (fun p : Nat.Primes => 1 / ((p : ℝ) * Real.log (p : ℝ))) := by
        simpa only [Real.rpow_one] using
          (Sieve.summable_primes_one_div_mul_log_rpow
            (s := (1 : ℝ)) (by norm_num))
      apply hprime.congr
      intro p
      dsimp only [major]
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
  exact Summable.of_nonneg_of_le
    (fun pe => (routePPrimitiveBurnolApertureDefectFlux_pos pe).le)
    routePPrimitiveBurnolApertureDefectFlux_le_geometric hmajor

/-- Total primitive defect mass at aperture time `c`. -/
def routePPrimitiveBurnolApertureTotalDefectMass (c : ℝ) : ℝ :=
  ∑' pe : Nat.Primes × ℕ, routePPrimitiveBurnolApertureDefectMass c pe

theorem norm_routePPrimitiveBurnolApertureDefectMass_div_le_flux
    {c : ℝ} (hc : 0 < c) (pe : Nat.Primes × ℕ) :
    ‖routePPrimitiveBurnolApertureDefectMass c pe / c‖ ≤
      routePPrimitiveBurnolApertureDefectFlux pe := by
  let lambda := xiGammaEulerPrimitiveLogFrequency pe
  let w := routePPrimitiveBaseCauchyCubicWeight pe
  have hlambda : 0 < lambda := xiGammaEulerPrimitiveLogFrequency_pos pe
  have hw : 0 ≤ w := routePPrimitiveBaseCauchyCubicWeight_nonneg pe
  have hx : 0 ≤ 2 * c * lambda := by positivity
  have hexp : Real.exp (-(2 * c * lambda)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hmassNonneg : 0 ≤ routePPrimitiveBurnolApertureDefectMass c pe := by
    rw [routePPrimitiveBurnolApertureDefectMass]
    exact mul_nonneg
      (sub_nonneg.mpr (by simpa only [lambda, neg_mul] using hexp)) hw
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hmassNonneg hc.le)]
  apply (div_le_iff₀ hc).2
  rw [routePPrimitiveBurnolApertureDefectMass]
  calc
    (1 - Real.exp (-2 * c * xiGammaEulerPrimitiveLogFrequency pe)) *
          routePPrimitiveBaseCauchyCubicWeight pe ≤
        (2 * c * lambda) * w := by
      have hone : 1 - Real.exp (-(2 * c * lambda)) ≤ 2 * c * lambda := by
        have h := Real.add_one_le_exp (-(2 * c * lambda))
        linarith
      exact mul_le_mul_of_nonneg_right
        (by simpa only [lambda, neg_mul] using hone) hw
    _ = routePPrimitiveBurnolApertureDefectFlux pe * c := by
      simp only [routePPrimitiveBurnolApertureDefectFlux, lambda, w]
      ring

/-- **Global P-G189 flux law.** Differentiation at the aperture wall commutes with the complete
primitive sum. The total defect opens with finite trace equal to the sum of the atomwise tail
fluxes. -/
theorem tendsto_routePPrimitiveBurnolApertureTotalDefectMass_div_zero :
    Tendsto
      (fun c : ℝ => routePPrimitiveBurnolApertureTotalDefectMass c / c)
      (nhdsWithin 0 (Ioi 0))
      (nhds (∑' pe : Nat.Primes × ℕ,
        routePPrimitiveBurnolApertureDefectFlux pe)) := by
  have hpoint : ∀ pe : Nat.Primes × ℕ,
      Tendsto
        (fun c : ℝ => routePPrimitiveBurnolApertureDefectMass c pe / c)
        (nhdsWithin 0 (Ioi 0))
        (nhds (routePPrimitiveBurnolApertureDefectFlux pe)) := by
    intro pe
    have hraw :=
      (hasDerivAt_routePPrimitiveBurnolApertureDefectMass_zero pe).tendsto_slope_zero_right
    convert hraw using 1
    ext c
    rw [zero_add]
    simp [routePPrimitiveBurnolApertureDefectMass]
    ring
  have hbound : ∀ᶠ c : ℝ in nhdsWithin 0 (Ioi 0),
      ∀ pe : Nat.Primes × ℕ,
        ‖routePPrimitiveBurnolApertureDefectMass c pe / c‖ ≤
          routePPrimitiveBurnolApertureDefectFlux pe := by
    filter_upwards [self_mem_nhdsWithin] with c hc pe
    exact norm_routePPrimitiveBurnolApertureDefectMass_div_le_flux hc pe
  have hlim := tendsto_tsum_of_dominated_convergence
    summable_routePPrimitiveBurnolApertureDefectFlux hpoint hbound
  simpa only [routePPrimitiveBurnolApertureTotalDefectMass,
    tsum_div_const] using hlim

/-- A Hilbert defect vector with P-G188's energy has intrinsic square-root boundary scale: no
finite derivative at zero exists, unconditionally. -/
theorem not_hasDerivAt_of_norm_sq_eq_routePPrimitiveBurnolApertureDefectMass
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (pe : Nat.Primes × ℕ) (v : ℝ → F) (hv0 : v 0 = 0)
    (henergy : ∀ c : ℝ, 0 < c →
      ‖v c‖ ^ 2 = routePPrimitiveBurnolApertureDefectMass c pe) :
    ∀ v' : F, ¬ HasDerivAt v v' 0 := by
  intro v' hv
  have hmassRaw :=
    (hasDerivAt_routePPrimitiveBurnolApertureDefectMass_zero pe).tendsto_slope_zero_right
  have hmass :
      Tendsto
        (fun c : ℝ => routePPrimitiveBurnolApertureDefectMass c pe / c)
        (nhdsWithin 0 (Ioi 0))
        (nhds (routePPrimitiveBurnolApertureDefectFlux pe)) := by
    convert hmassRaw using 1
    ext c
    rw [zero_add]
    simp [routePPrimitiveBurnolApertureDefectMass]
    ring
  have hvSlope :
      Tendsto (fun c : ℝ => ‖v c‖ ^ 2 / c)
        (nhdsWithin 0 (Ioi 0))
        (nhds (routePPrimitiveBurnolApertureDefectFlux pe)) := by
    apply hmass.congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    change 0 < c at hc
    rw [henergy c hc]
  have hvNorm : HasDerivAt (fun c : ℝ => ‖v c‖ ^ 2) 0 0 := by
    have h := hv.norm_sq
    rw [hv0, inner_zero_left, mul_zero] at h
    exact h
  have hzeroRaw := hvNorm.tendsto_slope_zero_right
  have hzero :
      Tendsto (fun c : ℝ => ‖v c‖ ^ 2 / c)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    convert hzeroRaw using 1
    ext c
    rw [zero_add, hv0]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  have hfluxZero : routePPrimitiveBurnolApertureDefectFlux pe = 0 :=
    tendsto_nhds_unique hvSlope hzero
  exact (routePPrimitiveBurnolApertureDefectFlux_pos pe).ne' hfluxZero

/-- The stronger channel-local form: any Hilbert realization of the distributed tail cocycle
itself is nondifferentiable at the aperture wall. -/
theorem not_hasDerivAt_of_norm_sq_eq_routePPrimitiveBurnolApertureTailDefectEnergy
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (v : ℝ → F) (hv0 : v 0 = 0)
    (henergy : ∀ c : ℝ, 0 < c →
      ‖v c‖ ^ 2 =
        routePPrimitiveBurnolApertureTailDefectEnergy c pe kappa) :
    ∀ v' : F, ¬ HasDerivAt v v' 0 := by
  intro v' hv
  have htail :=
    tendsto_routePPrimitiveBurnolApertureTailDefectEnergy_div_zero pe kappa
  have hvSlope :
      Tendsto (fun c : ℝ => ‖v c‖ ^ 2 / c)
        (nhdsWithin 0 (Ioi 0))
        (nhds (routePPrimitiveBurnolApertureDefectFlux pe)) := by
    apply htail.congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    change 0 < c at hc
    rw [henergy c hc]
  have hvNorm : HasDerivAt (fun c : ℝ => ‖v c‖ ^ 2) 0 0 := by
    have h := hv.norm_sq
    rw [hv0, inner_zero_left, mul_zero] at h
    exact h
  have hzeroRaw := hvNorm.tendsto_slope_zero_right
  have hzero :
      Tendsto (fun c : ℝ => ‖v c‖ ^ 2 / c)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    convert hzeroRaw using 1
    ext c
    rw [zero_add, hv0]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  have hfluxZero : routePPrimitiveBurnolApertureDefectFlux pe = 0 :=
    tendsto_nhds_unique hvSlope hzero
  exact (routePPrimitiveBurnolApertureDefectFlux_pos pe).ne' hfluxZero

end

end RHTower
