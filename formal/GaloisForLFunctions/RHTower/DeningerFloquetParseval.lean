import GaloisForLFunctions.RHTower.DeningerHalfDensityFloquetEnergy
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Parseval for the prime-circle trace

The periodization over a circle of circumference `L` is the unit-cell periodization of the rescaled
cochain, so its `m`-th Fourier coefficient on `[0,L]` is `L^{-1}` times the Fourier transform of the
cochain at the lattice frequency `m/L`.  Parseval on the interval then turns the circle energy into
the lattice sum

`∫_0^L ‖Per_L h‖² = L^{-1} ∑_{m ∈ ℤ} ‖𝓕h(m/L)‖²`,

and summing over primes gives the arithmetic lattice form of the half-density Floquet energy.

* `deningerPeriodizationSum_eq_l1Periodization` : the two periodizations agree.
* `deningerFourierCoeffOn_periodization` : **the Fourier coefficient is a Fourier-transform
  sample.**
* `deningerPeriodization_intervalIntegral_normSq` : **Parseval on the prime circle.**
* `deningerHalfDensityFloquetEnergy_eq_tsum` : **the arithmetic lattice form of `E_Fl`.**
-/

namespace RHTower

open SchwartzMap MeasureTheory GaloisForLFunctions.HTGeometry
open scoped FourierTransform

noncomputable section

/-- The lattice periodization is the unit-cell periodization of the rescaled cochain. -/
theorem deningerPeriodizationSum_eq_l1Periodization (f : 𝓢(ℝ, ℂ)) {L : ℝ} (hL : 0 < L) (y : ℝ) :
    deningerPeriodizationSum f L (y * L)
      = l1Periodization (fun u : ℝ => (f : ℝ → ℂ) (u / (1 / L))) y := by
  rw [deningerPeriodizationSum, l1Periodization]
  refine tsum_congr fun j => ?_
  congr 1
  field_simp

/-- **The Fourier coefficient of the prime-circle trace is a Fourier-transform sample.** -/
theorem deningerFourierCoeffOn_periodization {f : 𝓢(ℝ, ℂ)} (hf : Integrable f) {L : ℝ}
    (hL : 0 < L) (m : ℤ) :
    fourierCoeffOn hL (deningerPeriodizationSum f L) m
      = (1 / L) • 𝓕 (f : ℝ → ℂ) ((1 / L) * (m : ℝ)) := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hcorpus := integral_unit_scaled_l1Periodization_mul_fourier_eq (f := (f : ℝ → ℂ)) hf
    (a := 1 / L) (by positivity) m
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero]
  congr 1
  -- replace the circle character by the unit-circle character of the rescaled variable
  refine (intervalIntegral.integral_congr (g := fun x : ℝ =>
    fourier (-m) ((x / L : ℝ) : UnitAddCircle) • deningerPeriodizationSum f L x)
    fun x _ => ?_).trans ?_
  · simp only [fourier_coe_apply, smul_eq_mul]
    congr 2
    push_cast
    ring
  -- rescale to the unit cell
  have hcomp := intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => fourier (-m) ((x / L : ℝ) : UnitAddCircle)
      • deningerPeriodizationSum f L x) hLne (a := (0 : ℝ)) (b := 1)
  have hfun : (fun y : ℝ => fourier (-m) (((L * y) / L : ℝ) : UnitAddCircle)
      • deningerPeriodizationSum f L (L * y))
      = fun y : ℝ => fourier (-m) ((y : ℝ) : UnitAddCircle)
        • deningerPeriodizationSum f L (y * L) := by
    funext y
    have hy : L * y / L = y := by field_simp
    rw [hy, mul_comm L y]
  rw [hfun, mul_zero, mul_one] at hcomp
  have hunit : (∫ y in (0 : ℝ)..1, fourier (-m) ((y : ℝ) : UnitAddCircle)
      • deningerPeriodizationSum f L (y * L))
      = ∫ y in Set.Ioc (0 : ℝ) 1, fourier (-m) ((y : ℝ) : UnitAddCircle)
        * l1Periodization (fun u : ℝ => (f : ℝ → ℂ) (u / (1 / L))) y := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
    rw [smul_eq_mul, deningerPeriodizationSum_eq_l1Periodization f hL y]
  rw [hunit, hcorpus] at hcomp
  have hL2 : (∫ x in (0 : ℝ)..L,
      fourier (-m) ((x / L : ℝ) : UnitAddCircle) • deningerPeriodizationSum f L x)
      = L • ((1 / L) • 𝓕 (f : ℝ → ℂ) ((1 / L) * (m : ℝ))) := by
    rw [hcomp, smul_smul, mul_inv_cancel₀ hLne, one_smul]
  rw [hL2, smul_smul, mul_one_div, div_self hLne, one_smul]

/-- **Parseval on the prime circle.** -/
theorem deningerPeriodization_intervalIntegral_normSq {h : DeningerExpSchwartz} {L : ℝ}
    (hL : Real.log 2 ≤ L) :
    (∫ t in (0 : ℝ)..L, ‖deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t‖ ^ 2)
      = L * ∑' m : ℤ, ‖(1 / L) • 𝓕 (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
        ((1 / L) * (m : ℝ))‖ ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le (Real.log_pos one_lt_two) hL
  have hcont := deningerPeriodizationSum_continuous (h := h) hLpos
  have hbdd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) L)),
      ‖deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t‖
        ≤ 5 * deningerMeyerSeminormFun 1 0 h := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    exact deningerPeriodizationSum_norm_le_period hL ht.1.le ht.2
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) L)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top
  have hL2 : MemLp (deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L) 2
      (volume.restrict (Set.Ioc (0 : ℝ) L)) :=
    MemLp.of_bound hcont.aestronglyMeasurable _ hbdd
  have hpars := tsum_sq_fourierCoeffOn hLpos hL2
  have hcoef : ∀ m : ℤ,
      fourierCoeffOn hLpos (deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L) m
        = (1 / L) • 𝓕 (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ((1 / L) * (m : ℝ)) :=
    fun m => deningerFourierCoeffOn_periodization
      (SchwartzMap.integrable ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) hLpos m
  simp only [sub_zero, smul_eq_mul] at hpars
  rw [tsum_congr fun m => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hcoef m)] at hpars
  rw [hpars]
  field_simp

/-- **The arithmetic lattice form of the half-density Floquet energy.** -/
theorem deningerHalfDensityFloquetEnergy_eq_tsum (h : DeningerExpSchwartz) :
    deningerHalfDensityFloquetEnergy h
      = ∑' q : Nat.Primes, ((((q : ℕ) : ℝ) ^ 2)⁻¹ * Real.log (q : ℕ))
        * ∑' m : ℤ, ‖(1 / Real.log (q : ℕ))
          • 𝓕 (((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
            ((1 / Real.log (q : ℕ)) * (m : ℝ))‖ ^ 2 := by
  rw [deningerHalfDensityFloquetEnergy, deningerFloquetEnergy]
  refine tsum_congr fun q => ?_
  have hqR : (2 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast q.2.two_le
  have hL : Real.log 2 ≤ Real.log (q : ℕ) := Real.log_le_log two_pos hqR
  rw [deningerFloquetTerm,
    deningerPeriodization_intervalIntegral_normSq (h := deningerHalfDensityLift h) hL]
  ring

end

end RHTower
