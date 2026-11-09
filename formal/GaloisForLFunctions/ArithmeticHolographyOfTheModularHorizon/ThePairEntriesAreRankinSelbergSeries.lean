import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.OneCavityFunctionSeesEveryResonanceThatAPairSees

/-!
# The pair entries of the cavity are Rankin–Selberg series

The reduction of B109 (`OneCavityFunctionSeesEveryResonanceThatAPairSees`) leaves one question per right zero
`ρ`: is the resonance `ρ/2` seen by some pair of Maass cusp forms, `∫_𝒟 u conj(v) E*(ρ/2 − ½) ≠ 0`? This module
identifies these pair entries with Rankin–Selberg series. For cusp forms `u`, `v` of eigenvalues `λ₁`, `λ₂`, with
Whittaker coefficients `a_n(u)(y) = ρ_u(n) √y K_{ν₁}(2π|n|y)` and `ν_i = i√(λ_i − ¼)`,

  `∫_𝒟 u conj(v) E*(s − ½) = ξ(2s)/(2s(2s − 1)) · (2π)^{−s} G(s; ν₁, ν₂) · Σ_{n ≠ 0} ρ_u(n) conj(ρ_v(n)) |n|^{−s}`

for `Re s > 1`, `Im s ≠ 0` (`pairing_eq_rankinSelberg`), with the Gamma factor
`G(s; ν₁, ν₂) = 2^{s−3}/Γ(s) · Γ((s+ν₁+ν₂)/2) Γ((s+ν₁−ν₂)/2) Γ((s−ν₁+ν₂)/2) Γ((s−ν₁−ν₂)/2)`. So the open core of
B109 is the nonvanishing at `ρ/2` of the continuation of one Rankin–Selberg series of a pair of cavity modes
(`cuspFunction_sees_every_right_zero_iff_rankinSelberg`); for Hecke eigenforms the series is
`ρ_u(1) conj(ρ_v(1)) L(s, u × v)/ζ(2s)`.

**Proof.** The energy `u conj(v)` is a seed, so the unfolding of the completed transform applies. Its horocycle
mean is `Σ_n a_n(u) conj(a_n(v))` by Parseval on the horocycle, polarized:
`4 a conj(b) = |a + b|² − |a − b|² + i|a + ib|² − i|a − ib|²`. Dominated convergence with the majorant
`y^{σ−2}(|a_n(u)|² + |a_n(v)|²)` exchanges the sum and the Mellin integral, and each mode is the two-K Mellin
product `∫_0^∞ y^{s−1} K_{ν₁}(cy) K_{ν₂}(cy) dy = c^{−s} G(s; ν₁, ν₂)`; the Bessel functions are real because the
orders are imaginary.
-/

open Complex MeasureTheory Set Filter Topology BoundedContinuousFunction
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.RHTower
open UpperHalfPlane (ofComplex)

/-- **Polarization** `4 a conj(b) = |a + b|² − |a − b|² + i |a + ib|² − i |a − ib|²`. -/
theorem polarization_normSq (a b : ℂ) :
    a * starRingEnd ℂ b = (1 / 4 : ℂ) * ((Complex.normSq (a + b) : ℂ) - Complex.normSq (a - b) +
      I * Complex.normSq (a + I * b) - I * Complex.normSq (a - I * b)) := by
  apply Complex.ext <;>
  · simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring

theorem continuous_onHorocycle {f : ℍ → ℂ} (hf : Continuous f) {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ => f (ofComplex (SelbergMaassMean.point x y)) := by
  have hp : Continuous fun x : ℝ => SelbergMaassMean.point x y := by
    unfold SelbergMaassMean.point; fun_prop
  have hoc : ContinuousOn (fun w : ℂ => f (ofComplex w)) {w : ℂ | 0 < w.im} :=
    hf.comp_continuousOn (UpperHalfPlane.ofComplex.continuousOn.mono fun w hw => by
      simpa [UpperHalfPlane.ofComplex] using hw)
  exact hoc.comp_continuous hp fun x => HeckeCusp.point_im_pos hy

theorem continuousOn_comp_ofComplex {f : ℍ → ℂ} (hf : Continuous f) :
    ContinuousOn (fun w : ℂ => f (ofComplex w)) {w : ℂ | 0 < w.im} :=
  hf.comp_continuousOn (UpperHalfPlane.ofComplex.continuousOn.mono fun w hw => by
    simpa [UpperHalfPlane.ofComplex] using hw)

/-- The Fourier coefficient of `u + c v` on a horocycle. -/
theorem fourierCoeff_add_mul {u v : ℍ → ℂ} (hu : Continuous u) (hv : Continuous v) (c : ℂ) (n : ℤ)
    {y : ℝ} (hy : 0 < y) :
    SelbergMaassFourier.coefficient 1 n (fun w => u (ofComplex w) + c * v (ofComplex w)) y =
      HeckeCusp.fourierCoeff u n y + c * HeckeCusp.fourierCoeff v n y := by
  have h := HeckeCusp.coefficient_sub (fun w => u (ofComplex w)) (fun w => (-c) * v (ofComplex w)) n
    (continuous_onHorocycle hu hy) (continuous_const.mul (continuous_onHorocycle hv hy))
  have e : (fun w => u (ofComplex w) + c * v (ofComplex w)) =
      fun w => u (ofComplex w) - (-c) * v (ofComplex w) := by funext w; ring
  rw [e, h, HeckeCusp.coefficient_mul]
  unfold HeckeCusp.fourierCoeff
  simp only [Function.comp_def]
  ring

/-- **Polarized Parseval on a horocycle**: `∫_0^1 u conj(v) = Σ_n a_n(u) conj(a_n(v))`. -/
theorem hasSum_response_mul_conj {u v : ℍ → ℂ} (hu : Continuous u) (hv : Continuous v)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => HeckeCusp.fourierCoeff u n y * starRingEnd ℂ (HeckeCusp.fourierCoeff v n y))
      (response (fun z => u z * starRingEnd ℂ (v z)) y) := by
  set U : ℝ → ℂ := fun x => u (ofComplex (SelbergMaassMean.point x y))
  set V : ℝ → ℂ := fun x => v (ofComplex (SelbergMaassMean.point x y))
  have hU : Continuous U := continuous_onHorocycle hu hy
  have hV : Continuous V := continuous_onHorocycle hv hy
  have hP : ∀ c : ℂ, HasSum (fun n : ℤ => ((Complex.normSq (HeckeCusp.fourierCoeff u n y +
      c * HeckeCusp.fourierCoeff v n y) : ℝ) : ℂ)) (((∫ x in (0 : ℝ)..1, Complex.normSq (U x + c * V x)) : ℝ) : ℂ) := by
    intro c
    have hco : ContinuousOn (fun w : ℂ => u (ofComplex w) + c * v (ofComplex w)) {w : ℂ | 0 < w.im} :=
      (continuousOn_comp_ofComplex hu).add (continuousOn_const.mul (continuousOn_comp_ofComplex hv))
    have h := SelbergMaassParseval.coefficient_mass_hasSum 1 one_pos hco hy
    simp only [fourierCoeff_add_mul hu hv c _ hy, inv_one, one_mul] at h
    exact Complex.hasSum_ofReal.2 h
  have hI : ∀ c : ℂ, IntervalIntegrable (fun x : ℝ => ((Complex.normSq (U x + c * V x) : ℝ) : ℂ)) volume 0 1 :=
    fun c => (Complex.continuous_ofReal.comp (Complex.continuous_normSq.comp
      (hU.add (continuous_const.mul hV)))).intervalIntegrable _ _
  have hresp : response (fun z => u z * starRingEnd ℂ (v z)) y = (1 / 4 : ℂ) *
      ((((∫ x in (0 : ℝ)..1, Complex.normSq (U x + 1 * V x)) : ℝ) : ℂ) -
        (((∫ x in (0 : ℝ)..1, Complex.normSq (U x + (-1) * V x)) : ℝ) : ℂ) +
        I * (((∫ x in (0 : ℝ)..1, Complex.normSq (U x + I * V x)) : ℝ) : ℂ) -
        I * (((∫ x in (0 : ℝ)..1, Complex.normSq (U x + (-I) * V x)) : ℝ) : ℂ)) := by
    rw [response_eq_intervalIntegral]
    simp only [← intervalIntegral.integral_ofReal]
    rw [← intervalIntegral.integral_sub (hI 1) (hI (-1)), ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hI 1).sub (hI (-1))) ((hI I).const_mul I),
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (((hI 1).sub (hI (-1))).add ((hI I).const_mul I))
        ((hI (-I)).const_mul I), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [U, V, chart_point]
    rw [polarization_normSq]
    simp only [one_mul, neg_mul, ← sub_eq_add_neg]
  rw [hresp]
  refine ((((hP 1).sub (hP (-1))).add ((hP I).mul_left I)).sub ((hP (-I)).mul_left I) |>.mul_left
    (1 / 4 : ℂ)).congr_fun fun n => ?_
  rw [polarization_normSq]
  simp only [one_mul, neg_mul, ← sub_eq_add_neg]

/-! ### The Mellin transform of a pair energy -/

/-- The two-order Gamma factor `2^{s−3}/Γ(s) · Π Γ((s ± ν₁ ± ν₂)/2)` of `∫ y^{s−1} K_{ν₁} K_{ν₂}`. -/
def pairGamma (ν₁ ν₂ s : ℂ) : ℂ :=
  (2 : ℂ) ^ (s - 3) / Gamma s *
    (Gamma ((s + ν₁ + ν₂) / 2) * Gamma ((s + ν₁ - ν₂) / 2) * Gamma ((s - ν₁ + ν₂) / 2) *
      Gamma ((s - ν₁ - ν₂) / 2))

/-- `∫_0^∞ y^{s−1} K_{ν₁}(cy) K_{ν₂}(cy) dy = c^{−s} ∫_0^∞ x^{s−1} K_{ν₁}(x) K_{ν₂}(x) dx`. -/
theorem integral_scaled_pairKK {s : ℂ} {c : ℝ} (hc : 0 < c) (ν₁ ν₂ : ℂ) :
    ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        (modifiedBesselKOrder (c * y) ν₁ * modifiedBesselKOrder (c * y) ν₂) =
      (c : ℂ) ^ (-s) * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) *
        modifiedBesselKOrder x ν₁ * modifiedBesselKOrder x ν₂ := by
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => (x : ℂ) ^ (s - 1) *
    modifiedBesselKOrder x ν₁ * modifiedBesselKOrder x ν₂) 0 hc
  rw [mul_zero, Complex.real_smul] at h
  have hcC : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
  have hcs : (c : ℂ) ^ (s - 1) ≠ 0 := by rw [cpow_def_of_ne_zero hcC]; exact exp_ne_zero _
  have e : ∀ y ∈ Ioi (0 : ℝ), ((c * y : ℝ) : ℂ) ^ (s - 1) * modifiedBesselKOrder (c * y) ν₁ *
      modifiedBesselKOrder (c * y) ν₂ = (c : ℂ) ^ (s - 1) * ((y : ℂ) ^ (s - 1) *
        (modifiedBesselKOrder (c * y) ν₁ * modifiedBesselKOrder (c * y) ν₂)) := by
    intro y hy
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hc.le (le_of_lt hy)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul] at h
  have hsplit : (c : ℂ) ^ s = (c : ℂ) ^ (s - 1) * c := by
    rw [show s = (s - 1) + 1 by ring, cpow_add _ _ hcC, cpow_one]; ring_nf
  rw [cpow_neg, hsplit]
  calc ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        (modifiedBesselKOrder (c * y) ν₁ * modifiedBesselKOrder (c * y) ν₂)
      = ((c : ℂ) ^ (s - 1))⁻¹ * ((c : ℂ) ^ (s - 1) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        (modifiedBesselKOrder (c * y) ν₁ * modifiedBesselKOrder (c * y) ν₂)) := by
        rw [inv_mul_cancel_left₀ hcs]
    _ = ((c : ℂ) ^ (s - 1))⁻¹ * ((c : ℂ)⁻¹ * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) *
        modifiedBesselKOrder x ν₁ * modifiedBesselKOrder x ν₂) := by rw [h, ofReal_inv]
    _ = _ := by rw [mul_inv]; ring

variable {lam₁ lam₂ : ℝ} {u v : ℍ → ℂ} {ρ₁ ρ₂ : ℤ → ℂ}

/-- **The Mellin transform of a pair energy is a Rankin–Selberg series.** For `Re s > 1`,
`∫_0^∞ y^{s−2} ∫_0^1 u conj(v) dx dy = Σ_n ρ_u(n) conj(ρ_v(n)) (2π|n|)^{−s} G(s; ν₁, ν₂)`. -/
theorem hasSum_mellin_pairResponse (hu : u ∈ HeckeCusp.cuspSpace lam₁) (hv : v ∈ HeckeCusp.cuspSpace lam₂)
    (hρ₁0 : ρ₁ 0 = 0) (hρ₁ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff u n y = ρ₁ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam₁))
    (hρ₂ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff v n y = ρ₂ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam₂)) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ => ρ₁ n * starRingEnd ℂ (ρ₂ n) * ((2 * Real.pi * |(n : ℝ)| : ℝ) : ℂ) ^ (-s) *
      pairGamma (CuspL.nu lam₁) (CuspL.nu lam₂) s)
      (mellin (response (fun z => u z * starRingEnd ℂ (v z))) (s - 1)) := by
  have hcu := HeckeCusp.continuous_of_maass hu.2.1
  have hcv := HeckeCusp.continuous_of_maass hv.2.1
  set a : ℤ → ℝ → ℂ := fun n y => HeckeCusp.fourierCoeff u n y
  set b : ℤ → ℝ → ℂ := fun n y => HeckeCusp.fourierCoeff v n y
  set F : ℤ → ℝ → ℂ := fun n y => (y : ℂ) ^ (s - 2) * (a n y * starRingEnd ℂ (b n y))
  obtain ⟨ρ₂', hρ₂0', hρ₂'⟩ := CuspL.exists_whittaker hv
  have hmain : HasSum (fun n => ∫ y in Ioi (0 : ℝ), F n y)
      (∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 2) * response (fun z => u z * starRingEnd ℂ (v z)) y) := by
    refine hasSum_integral_of_dominated_convergence
      (fun n y => y ^ (s.re - 2) * (‖a n y‖ ^ 2 + ‖b n y‖ ^ 2)) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
    · have hc : ContinuousOn (F n) (Ioi 0) := by
        refine ContinuousOn.mul (fun y hy => ?_) ?_
        · exact (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hy)).comp
            Complex.continuous_ofReal.continuousAt |>.continuousWithinAt
        · exact ((HeckeCusp.modalSol_fourierCoeff hu n).continuousOn.1).mul
            (Complex.continuous_conj.comp_continuousOn (HeckeCusp.modalSol_fourierCoeff hv n).continuousOn.1)
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : (0 : ℝ) < y := hy
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hy0, norm_mul, Complex.norm_conj]
      simp only [sub_re, Complex.re_ofNat]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hy0.le _)
      nlinarith [norm_nonneg (a n y), norm_nonneg (b n y), sq_nonneg (‖a n y‖ - ‖b n y‖)]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact (((WeylUpper.hasSum_slice hu hy).add (WeylUpper.hasSum_slice hv hy)).mul_left _).summable
    · have hI := (CuspRSI.integrableOn_slice_weight hu hρ₁0 hρ₁ hs).add
        (CuspRSI.integrableOn_slice_weight hv hρ₂0' hρ₂' hs)
      refine hI.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [(((WeylUpper.hasSum_slice hu hy).add (WeylUpper.hasSum_slice hv hy)).mul_left _).tsum_eq]
      simp only [Pi.add_apply]
      ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact (hasSum_response_mul_conj hcu hcv hy).mul_left _
  have hmel : mellin (response (fun z => u z * starRingEnd ℂ (v z))) (s - 1) =
      ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 2) * response (fun z => u z * starRingEnd ℂ (v z)) y := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    rw [smul_eq_mul, show s - 1 - 1 = s - 2 by ring]
  rw [hmel]
  refine hmain.congr_fun fun n => ?_
  by_cases hn : n = 0
  · subst hn
    rw [hρ₁0, zero_mul, zero_mul, zero_mul]
    simp only [F, a]
    rw [setIntegral_congr_fun measurableSet_Ioi (show EqOn (fun y : ℝ => (y : ℂ) ^ (s - 2) *
      (HeckeCusp.fourierCoeff u 0 y * starRingEnd ℂ (b 0 y))) (fun _ => (0 : ℂ)) (Ioi 0) from fun y hy => by
        simp [HeckeCusp.fourierCoeff_zero hu hy])]
    simp
  have hc : 0 < 2 * Real.pi * |(n : ℝ)| := by
    have := abs_pos.2 (Int.cast_ne_zero.2 hn : (n : ℝ) ≠ 0); positivity
  have hpt : EqOn (F n) (fun y => ρ₁ n * starRingEnd ℂ (ρ₂ n) * ((y : ℂ) ^ (s - 1) *
      (modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam₁) *
        modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam₂)))) (Ioi 0) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have h0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy0.ne'
    simp only [F, a, b]
    rw [hρ₁ n y hy0, hρ₂ n y hy0, map_mul, map_mul, Complex.conj_ofReal,
      ← CuspRSI.K_real lam₂ (2 * Real.pi * |(n : ℝ)| * y), Complex.conj_ofReal, CuspRSI.K_real]
    have hsub : (y : ℂ) ^ (s - 1) = (y : ℂ) ^ (s - 2) * y := by
      rw [show s - 1 = (s - 2) + 1 by ring, cpow_add _ _ h0, cpow_one]
    have hsq : ((Real.sqrt y : ℝ) : ℂ) * ((Real.sqrt y : ℝ) : ℂ) = (y : ℂ) := by
      rw [← ofReal_mul, Real.mul_self_sqrt hy0.le]
    rw [hsub]
    linear_combination (↑y ^ (s - 2) * ρ₁ n * (starRingEnd ℂ) (ρ₂ n) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam₁) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam₂)) * hsq
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_scaled_pairKK hc,
    GaloisForLFunctions.RHTower.integral_cpow_mul_modifiedBesselKOrder_mul_modifiedBesselKOrder
      (by rw [CuspL.nu_re, CuspL.nu_re, abs_zero, add_zero]; linarith)]
  simp only [pairGamma]
  ring

/-- **The pair entries are Rankin–Selberg series.** For `Re s > 1`, `Im s ≠ 0`,
`∫_𝒟 u conj(v) E*(s − ½) = ξ(2s)/(2s(2s−1)) · (2π)^{−s} G(s; ν₁, ν₂) Σ_n ρ_u(n) conj(ρ_v(n)) |n|^{−s}`. -/
theorem pairing_eq_rankinSelberg (hu : u ∈ HeckeCusp.cuspSpace lam₁) (hv : v ∈ HeckeCusp.cuspSpace lam₂)
    (hρ₁0 : ρ₁ 0 = 0) (hρ₁ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff u n y = ρ₁ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam₁))
    (hρ₂ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff v n y = ρ₂ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam₂)) {s : ℂ} (hs : 1 < s.re)
    (him : s.im ≠ 0) :
    pairing s u v = xi (2 * s) / (2 * s * (2 * s - 1)) * ((2 * Real.pi : ℂ) ^ (-s) *
      pairGamma (CuspL.nu lam₁) (CuspL.nu lam₂) s *
        ∑' n : ℤ, ρ₁ n * starRingEnd ℂ (ρ₂ n) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)) := by
  have hseed : IsSeed (fun z => u z * starRingEnd ℂ (v z)) :=
    (isSeed_of_mem_cuspSpace hu).mul (isSeed_of_mem_cuspSpace hv).star
  have e : pairing s u v = seedTransform (fun z => u z * starRingEnd ℂ (v z)) s := rfl
  rw [e, seedTransform_eq_mellin hseed hs him,
    ← (hasSum_mellin_pairResponse hu hv hρ₁0 hρ₁ hρ₂ hs).tsum_eq]
  congr 1
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [ofReal_mul (2 * Real.pi) |(n : ℝ)|, mul_cpow_ofReal_nonneg (by positivity) (abs_nonneg _)]
  push_cast
  ring

/-- The pair entry is holomorphic on `ℂ ∖ {0, ½, 1}`: it is the continuation of the Rankin–Selberg series. -/
theorem differentiableOn_pairing (hu : u ∈ HeckeCusp.cuspSpace lam₁) (hv : v ∈ HeckeCusp.cuspSpace lam₂) :
    DifferentiableOn ℂ (fun s => pairing s u v) ({0, 1 / 2, 1} : Set ℂ)ᶜ :=
  differentiableOn_seedTransform ((isSeed_of_mem_cuspSpace hu).mul (isSeed_of_mem_cuspSpace hv).star)

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon
