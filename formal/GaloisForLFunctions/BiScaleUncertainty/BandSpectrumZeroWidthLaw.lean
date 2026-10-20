import GaloisForLFunctions.BiScaleUncertainty.BandLimitedLaplaceEnergy
import GaloisForLFunctions.RHTower.CCMCriticalMellinResolventExponentialWidth
import GaloisForLFunctions.RHTower.CCMGeneralizedVonKoch
import GaloisForLFunctions.RHTower.CramerChebyshevMeanSquare
import GaloisForLFunctions.RHTower.VonMangoldtMinusOneAbscissa
import GaloisForLFunctions.RHTower.CCMCriticalMellinGrowingCumulativeBound

/-!
# The band spectrum is the zero width

The square-root barrier has three forms in the field: the mean square `∫_0^L Ẽ²` of the
normalized Chebyshev error, the Laplace energy of `ν_N`, and the spectral energy of `ν_N` on the
band `|ξ| ≤ √(N+2)`. Their exponential growth rates in the cutoff `L` are one number, and that
number is the zero width. For `0 ≤ α < 1/2` the following are equivalent:

* every Xi zero has `Re ρ ≤ 1/2 + α`;
* for every `β > α`, `∫_0^L Ẽ² ≤ C e^{2βL}`;
* for every `β > α`, `laplaceEnergy N ≤ C (N+2)^{2β}`;
* for every `β > α`, the band energy is at most `C (N+2)^{2β}`.

From mean square to width: the resolvent `Q(t) = e^{-t}(∫_0^t e^h Ẽ(h) dh − 2/3)` is bounded by
`(C+1) e^{βt}` through the pointwise inequality `2|ab| ≤ μa² + b²/μ` at the scale
`μ = e^{(β−1)t}`, and an exponentially bounded resolvent continues the critical-Mellin defect
across `Re s > 1/2 + β`. From width to mean square: the generalized von Koch bound
`|Ẽ(t)| ≤ C e^{βt}`.

At the endpoint the band self-improves. RH gives the linear band `∫_0^L Ẽ² ≤ C(1 + L)` through
Cramér's dyadic mean square, and every subexponential band gives RH. So
`∫_0^L Ẽ² = e^{o(L)}` already forces `∫_0^L Ẽ² = O(L)`: no growth rate strictly between linear
and exponential is possible for the mean-square band.
-/

open MeasureTheory Set Filter

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar

noncomputable section
set_option autoImplicit false

/-! ## The three band rates -/

/-- The mean-square band grows at most like `e^{2βL}`. -/
def MeanSquareBandRate (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L →
    ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * Real.exp (2 * β * L)

/-- The Laplace energy grows at most like `(N+2)^{2β} = e^{2β·cutoff N}`. -/
def LaplaceEnergyRate (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, laplaceEnergy N ≤ C * Real.exp (2 * β * cutoff N)

/-- The spectral energy on the band `|ξ| ≤ √(N+2)` grows at most like `(N+2)^{2β}`. -/
def SpectralBandRate (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    (∫ ξ in Icc (-bandFrequency N) (bandFrequency N), spectralDensity N ξ) ≤
      C * Real.exp (2 * β * cutoff N)

/-! ## Elementary facts -/

/-- The corpus critical-Mellin normalized error is the field's `Ẽ`. -/
theorem criticalMellinNormalizedChebyshevError_eq_normalizedLogError (t : ℝ) :
    _root_.RHTower.criticalMellinNormalizedChebyshevError t = normalizedLogError t := by
  rw [_root_.RHTower.criticalMellinNormalizedChebyshevError, _root_.RHTower.criticalMellinError,
    _root_.RHTower.criticalCumulative_vonMangoldt_eq_chebyshevPsi, ← Real.exp_half,
    normalizedLogError, logError, div_eq_mul_inv, ← Real.exp_neg, mul_comm, neg_div]

theorem integral_normalizedLogError_sq_mono {L L' : ℝ} (h : L ≤ L') :
    ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ ∫ t in Icc 0 L', normalizedLogError t ^ 2 :=
  setIntegral_mono_set (integrableOn_normalizedLogError_sq L')
    (Eventually.of_forall fun _ => sq_nonneg _) (Icc_subset_Icc le_rfl h).eventuallyLE

private theorem le_exp_mul_div {c L : ℝ} (hc : 0 < c) : L ≤ Real.exp (c * L) / c := by
  rw [le_div_iff₀ hc]
  linarith [Real.add_one_le_exp (c * L)]

/-- The cutoff `log(N+2)` with `N = ⌈e^L⌉` lies in `[L, L + log 4]`. -/
private theorem exists_cutoff_mem {L : ℝ} (hL : 0 ≤ L) :
    ∃ N : ℕ, L ≤ cutoff N ∧ cutoff N ≤ L + Real.log 4 := by
  refine ⟨⌈Real.exp L⌉₊, ?_, ?_⟩
  · have h1 : Real.exp L ≤ ((⌈Real.exp L⌉₊ + 2 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil (Real.exp L)]
    calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
      _ ≤ cutoff ⌈Real.exp L⌉₊ := Real.log_le_log (Real.exp_pos L) h1
  · have he : 1 ≤ Real.exp L := Real.one_le_exp hL
    have h1 : ((⌈Real.exp L⌉₊ + 2 : ℕ) : ℝ) ≤ 4 * Real.exp L := by
      push_cast; linarith [Nat.ceil_lt_add_one (Real.exp_pos L).le]
    calc cutoff ⌈Real.exp L⌉₊ ≤ Real.log (4 * Real.exp L) :=
          Real.log_le_log (by positivity) h1
      _ = L + Real.log 4 := by
          rw [Real.log_mul (by norm_num) (Real.exp_pos L).ne', Real.log_exp]; ring

/-! ## From the mean-square band to the zero width -/

/-- **Resolvent bound from the band.** A mean-square band of rate `β ≥ 0` bounds the unit
resolvent `Q(t) = e^{-t}(∫_0^t e^h Ẽ − 2/3)` by `(C+1) e^{βt}`. -/
theorem abs_resolventSource_le_of_band {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hband : ∀ L : ℝ, 0 ≤ L →
      ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * Real.exp (2 * β * L))
    {t : ℝ} (ht : 0 ≤ t) :
    |_root_.RHTower.criticalMellinChebyshevResolventSource t| ≤ (C + 1) * Real.exp (β * t) := by
  have hfull := GaloisForLFunctions.RHTower.unitRieszChebyshevRayIntegral_eq_fullResolvent ht
  set Q := _root_.RHTower.criticalMellinChebyshevResolventSource t
  have hEq : (fun h : ℝ => _root_.RHTower.criticalMellinNormalizedChebyshevError h) =
      normalizedLogError := funext criticalMellinNormalizedChebyshevError_eq_normalizedLogError
  have hI : GaloisForLFunctions.RHTower.unitRieszChebyshevRayIntegral t =
      ∫ h in (0 : ℝ)..t, Real.exp h * normalizedLogError h := by
    rw [GaloisForLFunctions.RHTower.unitRieszChebyshevRayIntegral]
    simp only [criticalMellinNormalizedChebyshevError_eq_normalizedLogError]
  rw [hI] at hfull
  set I := ∫ h in (0 : ℝ)..t, Real.exp h * normalizedLogError h
  set μ := Real.exp ((β - 1) * t) with hμ
  have hμpos : 0 < μ := Real.exp_pos _
  have hint1 : IntervalIntegrable (fun h => Real.exp h * normalizedLogError h) volume 0 t := by
    have h := GaloisForLFunctions.RHTower.intervalIntegrable_criticalMellinChebyshevRayDensity 0 t
    unfold GaloisForLFunctions.RHTower.criticalMellinChebyshevRayDensity at h
    simpa only [criticalMellinNormalizedChebyshevError_eq_normalizedLogError] using h
  have hsqI : IntervalIntegrable (fun h => normalizedLogError h ^ 2) volume 0 t := by
    refine IntegrableOn.intervalIntegrable ?_
    rw [uIcc_of_le ht]
    exact integrableOn_normalizedLogError_sq t
  have hexpI : IntervalIntegrable (fun h : ℝ => Real.exp (2 * h)) volume 0 t :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun h => (μ * Real.exp (2 * h) + normalizedLogError h ^ 2 / μ) / 2) volume 0 t :=
    ((hexpI.const_mul μ).add (hsqI.div_const μ)).div_const 2
  have hpt : ∀ h : ℝ, |Real.exp h * normalizedLogError h| ≤
      (μ * Real.exp (2 * h) + normalizedLogError h ^ 2 / μ) / 2 := by
    intro h
    set a := Real.exp h
    set b := normalizedLogError h
    have ha2 : Real.exp (2 * h) = a ^ 2 := by
      rw [show 2 * h = h + h by ring, Real.exp_add]; ring
    rw [ha2, abs_mul,
      show (μ * a ^ 2 + b ^ 2 / μ) / 2 = (μ ^ 2 * a ^ 2 + b ^ 2) / (2 * μ) by
        field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (μ * |a| - |b|), sq_abs a, sq_abs b]
  have hIle : |I| ≤ ∫ h in (0 : ℝ)..t, (μ * Real.exp (2 * h) + normalizedLogError h ^ 2 / μ) / 2 :=
    (intervalIntegral.abs_integral_le_integral_abs ht).trans
      (intervalIntegral.integral_mono_on ht hint1.abs hint2 fun h _ => hpt h)
  have hexp : ∫ h in (0 : ℝ)..t, Real.exp (2 * h) = (Real.exp (2 * t) - 1) / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun h => Real.exp (2 * h) / 2)
      (fun x _ => by
        have h := (((hasDerivAt_id' x).const_mul (2 : ℝ)).exp).div_const 2
        rw [mul_one, mul_div_assoc, div_self two_ne_zero, mul_one] at h
        exact h) hexpI]
    simp only [mul_zero, Real.exp_zero]; ring
  have hsq : ∫ h in (0 : ℝ)..t, normalizedLogError h ^ 2 =
      ∫ h in Icc 0 t, normalizedLogError h ^ 2 := by
    rw [intervalIntegral.integral_of_le ht, integral_Icc_eq_integral_Ioc]
  have hsplit : ∫ h in (0 : ℝ)..t, (μ * Real.exp (2 * h) + normalizedLogError h ^ 2 / μ) / 2 =
      μ / 2 * ((Real.exp (2 * t) - 1) / 2) +
        (∫ h in Icc 0 t, normalizedLogError h ^ 2) / (2 * μ) := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hexpI.const_mul μ)
      (hsqI.div_const μ), intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      hexp, hsq]
    field_simp
  have hband' := hband t ht
  have hE1 : μ * Real.exp (2 * t) = Real.exp ((β + 1) * t) := by
    rw [hμ, ← Real.exp_add]; ring_nf
  have hE2 : Real.exp (2 * β * t) = μ * Real.exp ((β + 1) * t) := by
    rw [hμ, ← Real.exp_add]; ring_nf
  have hE3 : Real.exp ((β + 1) * t) * Real.exp (-t) = Real.exp (β * t) := by
    rw [← Real.exp_add]; ring_nf
  have hE4 : Real.exp (-t) ≤ Real.exp (β * t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hIbound : |I| ≤ (1 / 4 + C / 2) * Real.exp ((β + 1) * t) := by
    rw [hsplit] at hIle
    have h1 : μ / 2 * ((Real.exp (2 * t) - 1) / 2) ≤ Real.exp ((β + 1) * t) / 4 := by
      rw [← hE1]; nlinarith
    have h2 : (∫ h in Icc 0 t, normalizedLogError h ^ 2) / (2 * μ) ≤
        C / 2 * Real.exp ((β + 1) * t) := by
      rw [div_le_iff₀ (by positivity)]
      rw [hE2] at hband'
      nlinarith
    linarith
  have hQ : Q = (I - 2 / 3) * Real.exp (-t) := by
    calc Q = Q * (Real.exp t * Real.exp (-t)) := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ = (I - 2 / 3) * Real.exp (-t) := by rw [hfull]; ring
  rw [hQ, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hIt : |I - 2 / 3| ≤ |I| + 2 / 3 := by
    have := abs_sub I (2 / 3); rw [abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)] at this; exact this
  have hpos := Real.exp_pos (-t)
  calc |I - 2 / 3| * Real.exp (-t) ≤ (|I| + 2 / 3) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right hIt hpos.le
    _ ≤ ((1 / 4 + C / 2) * Real.exp ((β + 1) * t) + 2 / 3) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ = (1 / 4 + C / 2) * Real.exp (β * t) + 2 / 3 * Real.exp (-t) := by rw [← hE3]; ring
    _ ≤ (C + 1) * Real.exp (β * t) := by nlinarith [Real.exp_pos (β * t)]

/-- **Mean-square band ⟹ zero width.** A mean-square band of rate `β ∈ [0, 1/2)` excludes every
Xi zero with `Re ρ > 1/2 + β`. -/
theorem xiZeroHalfPlaneBound_of_meanSquareBandRate {β : ℝ} (hβ : 0 ≤ β) (hβ' : β < 1 / 2)
    (h : MeanSquareBandRate β) : _root_.RHTower.XiZeroHalfPlaneBound β := by
  obtain ⟨C, hC, hband⟩ := h
  exact GaloisForLFunctions.RHTower.xiZeroHalfPlaneBound_of_criticalMellinChebyshevResolventSource_exponentialBound
    hβ hβ' (by linarith) fun t ht => abs_resolventSource_le_of_band hβ hC hband ht

/-! ## From the zero width to the bands -/

/-- **Generalized von Koch in the gauge.** A zero width `α` gives `|Ẽ(t)| ≤ C e^{βt}` for every
`β > α`. -/
theorem exists_abs_normalizedLogError_le_of_xiZeroHalfPlaneBound {α β : ℝ} (hα : 0 ≤ α)
    (hαβ : α < β) (hXi : _root_.RHTower.XiZeroHalfPlaneBound α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → |normalizedLogError t| ≤ C * Real.exp (β * t) := by
  obtain ⟨C, hC0, hC⟩ :=
    _root_.RHTower.chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound hα hXi (β - α)
      (by linarith)
  refine ⟨C, hC0, fun t ht => ?_⟩
  have h := hC (Real.exp t) (Real.one_le_exp ht)
  rw [_root_.RHTower.criticalMellinError,
    _root_.RHTower.criticalCumulative_vonMangoldt_eq_chebyshevPsi, ← Real.exp_mul] at h
  rw [normalizedLogError, logError, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-t / 2) * |Chebyshev.psi (Real.exp t) - Real.exp t|
      ≤ Real.exp (-t / 2) * (C * Real.exp (t * (1 / 2 + α + (β - α)))) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = C * Real.exp (β * t) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf

/-- **Zero width ⟹ mean-square band.** -/
theorem meanSquareBandRate_of_xiZeroHalfPlaneBound {α β : ℝ} (hα : 0 ≤ α) (hαβ : α < β)
    (hXi : _root_.RHTower.XiZeroHalfPlaneBound α) : MeanSquareBandRate β := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_normalizedLogError_le_of_xiZeroHalfPlaneBound hα
    (show α < (α + β) / 2 by linarith) hXi
  have hc : 0 < β - α := by linarith
  refine ⟨C ^ 2 / (β - α), by positivity, fun L hL => ?_⟩
  have hpt : ∀ t ∈ Icc 0 L, ‖normalizedLogError t ^ 2‖ ≤ C ^ 2 * Real.exp ((α + β) * L) := by
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc |normalizedLogError t| ^ 2 ≤ (C * Real.exp ((α + β) / 2 * t)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (hC t ht.1) 2
      _ = C ^ 2 * Real.exp ((α + β) * t) := by
          rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
      _ ≤ C ^ 2 * Real.exp ((α + β) * L) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left ht.2 (by linarith))) (sq_nonneg _)
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Icc_lt_top hpt
  rw [Real.volume_real_Icc_of_le hL, sub_zero] at hint
  have hL' := le_exp_mul_div (L := L) hc
  calc ∫ t in Icc 0 L, normalizedLogError t ^ 2
      ≤ ‖∫ t in Icc 0 L, normalizedLogError t ^ 2‖ := le_abs_self _
    _ ≤ C ^ 2 * Real.exp ((α + β) * L) * L := hint
    _ ≤ C ^ 2 * Real.exp ((α + β) * L) * (Real.exp ((β - α) * L) / (β - α)) :=
        mul_le_mul_of_nonneg_left hL' (by positivity)
    _ = C ^ 2 / (β - α) * Real.exp (2 * β * L) := by
        rw [mul_div_assoc', mul_assoc, ← Real.exp_add]; ring_nf

/-! ## The mean-square law -/

/-- A width bound below every larger width below `1/2` is a width bound. -/
private theorem xiZeroHalfPlaneBound_of_forall_gt {α : ℝ} (hα' : α < 1 / 2)
    (h : ∀ β : ℝ, α < β → β < 1 / 2 → _root_.RHTower.XiZeroHalfPlaneBound β) :
    _root_.RHTower.XiZeroHalfPlaneBound α := by
  intro ρ hρ
  by_contra hlt
  rw [not_le] at hlt
  set β := α + min ((ρ.re - 1 / 2 - α) / 2) ((1 / 2 - α) / 2)
  have hm1 := min_le_left ((ρ.re - 1 / 2 - α) / 2) ((1 / 2 - α) / 2)
  have hm2 := min_le_right ((ρ.re - 1 / 2 - α) / 2) ((1 / 2 - α) / 2)
  have hm0 : 0 < min ((ρ.re - 1 / 2 - α) / 2) ((1 / 2 - α) / 2) :=
    lt_min (by linarith) (by linarith)
  have := h β (by simp only [β]; linarith) (by simp only [β]; linarith) ρ hρ
  simp only [β] at this
  linarith

/-- **The mean-square band spectrum is the zero width.** For `0 ≤ α < 1/2`, every Xi zero has
`Re ρ ≤ 1/2 + α` exactly when `∫_0^L Ẽ² = O(e^{2βL})` for every `β > α`. -/
theorem xiZeroHalfPlaneBound_iff_meanSquareBandRate {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1 / 2) :
    _root_.RHTower.XiZeroHalfPlaneBound α ↔ ∀ β : ℝ, α < β → MeanSquareBandRate β :=
  ⟨fun hXi _ hβ => meanSquareBandRate_of_xiZeroHalfPlaneBound hα hβ hXi,
    fun h => xiZeroHalfPlaneBound_of_forall_gt hα' fun β hβ hβ' =>
      xiZeroHalfPlaneBound_of_meanSquareBandRate (by linarith) hβ' (h β hβ)⟩

/-! ## The Laplace energy and the spectral band carry the same spectrum -/

/-- A Laplace-energy rate `β ≥ 0` is a mean-square band rate. -/
theorem meanSquareBandRate_of_laplaceEnergyRate {β : ℝ} (hβ : 0 ≤ β) (h : LaplaceEnergyRate β) :
    MeanSquareBandRate β := by
  obtain ⟨C, hC, hE⟩ := h
  refine ⟨2 * C * Real.exp (2 * β * Real.log 4) + 2, by positivity, fun L hL => ?_⟩
  obtain ⟨N, hN1, hN2⟩ := exists_cutoff_mem hL
  have hexp : Real.exp (2 * β * cutoff N) ≤
      Real.exp (2 * β * Real.log 4) * Real.exp (2 * β * L) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h1 : 1 ≤ Real.exp (2 * β * L) := Real.one_le_exp (by positivity)
  calc ∫ t in Icc 0 L, normalizedLogError t ^ 2
      ≤ ∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2 := integral_normalizedLogError_sq_mono hN1
    _ ≤ 2 * laplaceEnergy N + 2 := chebyshev_mean_square_le_laplaceEnergy N
    _ ≤ 2 * (C * (Real.exp (2 * β * Real.log 4) * Real.exp (2 * β * L))) + 2 * Real.exp (2 * β * L) := by
        have := hE N
        nlinarith [mul_le_mul_of_nonneg_left hexp hC]
    _ = (2 * C * Real.exp (2 * β * Real.log 4) + 2) * Real.exp (2 * β * L) := by ring

private theorem transient_sq_le {L : ℝ} (hL : 0 ≤ L) : ((1 - L) * Real.exp (-L / 2)) ^ 2 ≤ 4 := by
  have h1 : 1 + L / 2 ≤ Real.exp (L / 2) := by linarith [Real.add_one_le_exp (L / 2)]
  have h2 : Real.exp (-L / 2) * Real.exp (L / 2) = 1 := by rw [← Real.exp_add]; ring_nf; simp
  have hpos := Real.exp_pos (-L / 2)
  have h3 : |1 - L| * Real.exp (-L / 2) ≤ 2 := by
    have : |1 - L| ≤ 2 * (1 + L / 2) := by rw [abs_le]; constructor <;> linarith
    calc |1 - L| * Real.exp (-L / 2) ≤ 2 * (1 + L / 2) * Real.exp (-L / 2) :=
          mul_le_mul_of_nonneg_right this hpos.le
      _ ≤ 2 * Real.exp (L / 2) * Real.exp (-L / 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos.le
      _ = 2 := by rw [mul_assoc, mul_comm (Real.exp _), h2, mul_one]
  rw [← sq_abs, abs_mul, abs_of_pos hpos]
  calc (|1 - L| * Real.exp (-L / 2)) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
    _ = 4 := by norm_num

/-- **Zero width ⟹ Laplace-energy rate.** -/
theorem laplaceEnergyRate_of_xiZeroHalfPlaneBound {α β : ℝ} (hα : 0 ≤ α) (hαβ : α < β)
    (hXi : _root_.RHTower.XiZeroHalfPlaneBound α) : LaplaceEnergyRate β := by
  obtain ⟨C₁, hC₁, hM⟩ := meanSquareBandRate_of_xiZeroHalfPlaneBound hα hαβ hXi
  obtain ⟨C₀, hC₀, hP⟩ := exists_abs_normalizedLogError_le_of_xiZeroHalfPlaneBound hα hαβ hXi
  refine ⟨2 * C₁ + 2 * C₀ ^ 2 + 10, by positivity, fun N => ?_⟩
  set L := cutoff N
  have hL : 0 ≤ L := cutoff_nonneg N
  have h1 : 1 ≤ Real.exp (2 * β * L) := Real.one_le_exp (by nlinarith)
  have hE := hP L hL
  have hE2 : normalizedLogError L ^ 2 ≤ C₀ ^ 2 * Real.exp (2 * β * L) := by
    rw [← sq_abs]
    calc |normalizedLogError L| ^ 2 ≤ (C₀ * Real.exp (β * L)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hE 2
      _ = C₀ ^ 2 * Real.exp (2 * β * L) := by rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  have hT := transient_sq_le hL
  have hsq : (normalizedLogError L + (1 - L) * Real.exp (-L / 2)) ^ 2 ≤
      2 * normalizedLogError L ^ 2 + 2 * ((1 - L) * Real.exp (-L / 2)) ^ 2 := by
    nlinarith [sq_nonneg (normalizedLogError L - (1 - L) * Real.exp (-L / 2))]
  have := laplaceEnergy_le_chebyshev_mean_square N
  have hM' := hM L hL
  nlinarith

/-- **The Laplace-energy spectrum is the zero width.** -/
theorem xiZeroHalfPlaneBound_iff_laplaceEnergyRate {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1 / 2) :
    _root_.RHTower.XiZeroHalfPlaneBound α ↔ ∀ β : ℝ, α < β → LaplaceEnergyRate β :=
  ⟨fun hXi _ hβ => laplaceEnergyRate_of_xiZeroHalfPlaneBound hα hβ hXi,
    fun h => (xiZeroHalfPlaneBound_iff_meanSquareBandRate hα hα').2 fun β hβ =>
      meanSquareBandRate_of_laplaceEnergyRate (by linarith) (h β hβ)⟩

/-- For a positive rate the spectral band and the Laplace energy grow alike: the band theorem's
linear remainder is absorbed by `e^{2βL}`. -/
theorem spectralBandRate_iff_laplaceEnergyRate {β : ℝ} (hβ : 0 < β) :
    SpectralBandRate β ↔ LaplaceEnergyRate β := by
  constructor
  · rintro ⟨C, hC, hB⟩
    obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 52 * (Real.log 4 + 4) / Real.pi ^ 3 := ⟨_, rfl⟩
    obtain ⟨b, hb_def⟩ : ∃ b : ℝ,
        b = (32 + 8 * (Real.log 4 + 4)) / Real.pi ^ 2 + 4 / (3 * Real.pi ^ 4) := ⟨_, rfl⟩
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    have ha : 0 ≤ a := by rw [ha_def]; positivity
    have hb : 0 ≤ b := by rw [hb_def]; positivity
    refine ⟨C + a / (2 * β) + b, by positivity, fun N => ?_⟩
    have hL := le_exp_mul_div (L := cutoff N) (show 0 < 2 * β by linarith)
    have h1 : 1 ≤ Real.exp (2 * β * cutoff N) := Real.one_le_exp (by nlinarith [cutoff_nonneg N])
    have hLE := laplaceEnergy_le_band_add_linear N
    rw [← ha_def] at hLE
    have hBN := hB N
    have haL : a * cutoff N ≤ a / (2 * β) * Real.exp (2 * β * cutoff N) :=
      calc a * cutoff N ≤ a * (Real.exp (2 * β * cutoff N) / (2 * β)) :=
            mul_le_mul_of_nonneg_left hL ha
        _ = a / (2 * β) * Real.exp (2 * β * cutoff N) := by ring
    have hbE : b ≤ b * Real.exp (2 * β * cutoff N) := le_mul_of_one_le_right hb h1
    have hexpand : (C + a / (2 * β) + b) * Real.exp (2 * β * cutoff N) =
        C * Real.exp (2 * β * cutoff N) + a / (2 * β) * Real.exp (2 * β * cutoff N) +
          b * Real.exp (2 * β * cutoff N) := by ring
    rw [hexpand]
    linarith
  · rintro ⟨C, hC, hE⟩
    exact ⟨C, hC, fun N => (band_le_laplaceEnergy N).trans (hE N)⟩

/-- **The spectral band spectrum is the zero width.** -/
theorem xiZeroHalfPlaneBound_iff_spectralBandRate {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1 / 2) :
    _root_.RHTower.XiZeroHalfPlaneBound α ↔ ∀ β : ℝ, α < β → SpectralBandRate β := by
  rw [xiZeroHalfPlaneBound_iff_laplaceEnergyRate hα hα']
  exact forall_congr' fun β => imp_congr_right fun hβ =>
    (spectralBandRate_iff_laplaceEnergyRate (by linarith)).symm

/-! ## The endpoint: RH and the linear band -/

private theorem integrableOn_chebyshevError_sq (b : ℝ) :
    IntegrableOn (fun x => (Chebyshev.psi x - x) ^ 2) (Icc 1 b) := by
  refine Measure.integrableOn_of_bounded (M := (Chebyshev.psi b + b) ^ 2) measure_Icc_lt_top.ne
    ((Chebyshev.psi_mono.measurable.sub measurable_id).pow_const 2).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Eventually.of_forall fun x hx => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  have hψ := Chebyshev.psi_nonneg x
  have hψb := Chebyshev.psi_mono hx.2
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2]

private theorem integrableOn_chebyshevError_sq_div (b : ℝ) :
    IntegrableOn (fun x => (Chebyshev.psi x - x) ^ 2 / x ^ 2) (Icc 1 b) := by
  refine (integrableOn_chebyshevError_sq b).mono' (((Chebyshev.psi_mono.measurable.sub
    measurable_id).pow_const 2).div (measurable_id.pow_const 2)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Eventually.of_forall fun x hx => ?_
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx.1
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact div_le_self (sq_nonneg _) hx2

/-- **Cramér's band.** Under RH the mean-square band is linear: `∫_0^L Ẽ² ≤ C(1 + L)`. -/
theorem exists_meanSquare_band_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L) := by
  obtain ⟨C, hC0, hC⟩ := _root_.RHTower.dyadic_chebyshev_mean_square_of_riemannHypothesis hRH
  set g : ℝ → ℝ := fun x => (Chebyshev.psi x - x) ^ 2 / x ^ 2
  have hgI : ∀ {a b : ℝ}, 1 ≤ a → a ≤ b → IntervalIntegrable g volume a b := fun {a b} ha hab =>
    ((integrableOn_chebyshevError_sq_div b).mono_set (by
      rw [uIcc_of_le hab]; exact Icc_subset_Icc ha le_rfl)).intervalIntegrable
  have hdy : ∀ K : ℕ, ∫ x in (1 : ℝ)..2 ^ K, g x ≤ C * K := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      have hX : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
      have hXX : (2 : ℝ) ^ K ≤ 2 ^ (K + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ K)
      rw [← intervalIntegral.integral_add_adjacent_intervals (hgI le_rfl hX) (hgI hX hXX)]
      have hblock : ∫ x in (2 : ℝ) ^ K..2 ^ (K + 1), g x ≤ C := by
        have h2 : (2 : ℝ) ^ (K + 1) = 2 * 2 ^ K := by ring
        have hX0 : 0 < (2 : ℝ) ^ K := by positivity
        rw [h2]
        have hsqI : IntervalIntegrable (fun x => (Chebyshev.psi x - x) ^ 2) volume
            (2 ^ K) (2 * 2 ^ K) :=
          ((integrableOn_chebyshevError_sq (2 * 2 ^ K)).mono_set (by
            rw [uIcc_of_le (by linarith)]; exact Icc_subset_Icc hX le_rfl)).intervalIntegrable
        calc ∫ x in (2 : ℝ) ^ K..2 * 2 ^ K, g x
            ≤ ∫ x in (2 : ℝ) ^ K..2 * 2 ^ K, (Chebyshev.psi x - x) ^ 2 / (2 ^ K) ^ 2 := by
              refine intervalIntegral.integral_mono_on (by linarith) (hgI hX (by linarith))
                (hsqI.div_const _) fun x hx => ?_
              exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
                (pow_le_pow_left₀ hX0.le hx.1 2)
          _ = (∫ x in (2 : ℝ) ^ K..2 * 2 ^ K, (Chebyshev.psi x - x) ^ 2) / (2 ^ K) ^ 2 :=
              intervalIntegral.integral_div _ _
          _ ≤ C * (2 ^ K) ^ 2 / (2 ^ K) ^ 2 :=
              div_le_div_of_nonneg_right (hC _ hX) (by positivity)
          _ = C := by field_simp
      push_cast
      linarith
  refine ⟨2 * C, by positivity, fun L hL => ?_⟩
  have hlog2 : 1 / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  set K := ⌈L / Real.log 2⌉₊
  have hK1 : L ≤ K * Real.log 2 := by
    have := Nat.le_ceil (L / Real.log 2)
    rwa [div_le_iff₀ (by linarith)] at this
  have hK2 : (K : ℝ) ≤ 2 * L + 1 := by
    have h := Nat.ceil_lt_add_one (div_nonneg hL (by linarith : (0 : ℝ) ≤ Real.log 2))
    have : L / Real.log 2 ≤ 2 * L := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hexpK : Real.exp L ≤ 2 ^ K := by
    calc Real.exp L ≤ Real.exp (K * Real.log 2) := Real.exp_le_exp.mpr hK1
      _ = 2 ^ K := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hK2pos : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  rw [integral_normalizedLogError_sq_eq]
  calc ∫ x in Icc 1 (Real.exp L), g x
      ≤ ∫ x in Icc 1 (2 ^ K), g x :=
        setIntegral_mono_set (integrableOn_chebyshevError_sq_div _)
          (Eventually.of_forall fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
          (Icc_subset_Icc le_rfl hexpK).eventuallyLE
    _ = ∫ x in (1 : ℝ)..2 ^ K, g x := by
        rw [intervalIntegral.integral_of_le hK2pos, integral_Icc_eq_integral_Ioc]
    _ ≤ C * K := hdy K
    _ ≤ C * (2 * L + 1) := mul_le_mul_of_nonneg_left hK2 hC0
    _ ≤ 2 * C * (1 + L) := by nlinarith

/-- **RH is the linear mean-square band.** -/
theorem riemannHypothesis_iff_meanSquare_band :
    RiemannHypothesis ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L →
        ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L) := by
  refine ⟨exists_meanSquare_band_of_riemannHypothesis, fun ⟨C, hC, hband⟩ => ?_⟩
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    xiZeroHalfPlaneBound_iff_meanSquareBandRate le_rfl (by norm_num)]
  intro β hβ
  refine ⟨C * (1 + 1 / (2 * β)), by positivity, fun L hL => ?_⟩
  have hL' := le_exp_mul_div (L := L) (show 0 < 2 * β by linarith)
  have h1 : 1 ≤ Real.exp (2 * β * L) := Real.one_le_exp (by positivity)
  calc ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L) := hband L hL
    _ ≤ C * (Real.exp (2 * β * L) + Real.exp (2 * β * L) / (2 * β)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 hL') hC
    _ = C * (1 + 1 / (2 * β)) * Real.exp (2 * β * L) := by ring

/-- **RH is every subexponential mean-square band.** -/
theorem riemannHypothesis_iff_forall_meanSquareBandRate :
    RiemannHypothesis ↔ ∀ β : ℝ, 0 < β → MeanSquareBandRate β := by
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero]
  exact xiZeroHalfPlaneBound_iff_meanSquareBandRate le_rfl (by norm_num)

/-- **RH is every subexponential Laplace energy.** -/
theorem riemannHypothesis_iff_forall_laplaceEnergyRate :
    RiemannHypothesis ↔ ∀ β : ℝ, 0 < β → LaplaceEnergyRate β := by
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero]
  exact xiZeroHalfPlaneBound_iff_laplaceEnergyRate le_rfl (by norm_num)

/-- **RH is every subexponential band energy.** -/
theorem riemannHypothesis_iff_forall_spectralBandRate :
    RiemannHypothesis ↔ ∀ β : ℝ, 0 < β → SpectralBandRate β := by
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero]
  exact xiZeroHalfPlaneBound_iff_spectralBandRate le_rfl (by norm_num)

/-- **Self-improvement of the band.** A mean-square band below every exponential rate is linear. -/
theorem exists_meanSquare_band_of_forall_meanSquareBandRate
    (h : ∀ β : ℝ, 0 < β → MeanSquareBandRate β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L) :=
  riemannHypothesis_iff_meanSquare_band.1 (riemannHypothesis_iff_forall_meanSquareBandRate.2 h)

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
