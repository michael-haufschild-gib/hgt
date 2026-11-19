import GaloisForLFunctions.BlackHoleRingdown.CuspEscapeAndMixedPulseInterference
import GaloisForLFunctions.BlackHoleRingdown.ThePositiveEulerTwinsArePassive

/-!
# Passive-Twin Retarded Echo Dynamics and Finite-Time Distinguishing Inequalities

This module develops the exact time-domain wave dynamics of `PositiveEulerHorizon` (`q > 1`,
`1 < u < r`, `r * u = q`) and establishes two unconditional finite-time inequalities distinguishing
the undeformed modular horizon (`ζ`, where `b_ζ(p²) = +1/2`) from its passive reciprocal Euler twin
(`b_{p,A}(p²) < 0`) below the Riemann Hypothesis:

1. **Retarded Echo Kernel and Reflected Wavepacket of `PositiveEulerHorizon`**:
   - Partial-fraction expansion of `PositiveEulerHorizon.gate q (r + u) w` in powers of `q^{-2w}`
     gives an explicit real retarded echo kernel `twinEchoKernel q r u τ` satisfying strict
     causality (`twinEchoKernel q r u τ = 0` for `τ ≤ 0`), exact early attenuation
     (`twinEchoKernel q r u τ = (1 / q) * echoKernel τ` for `τ ≤ 2 log q`), exact Laplace transform
     `gate q (r + u) w * (Λ(2w)/Λ(2w + 1))` on `Re w > 1/2`, and the contour-shift decomposition
     `twinEcho q r u h T = twinReflected q (r + u) h T + gate q (r + u) (1/2) * μ(h) * e^{T/2}`.
   - Exact ringdown dichotomy: for `r = q^σ, u = q^{1-σ}` (`1/2 < σ < 1`), every compact pulse
     decays as `O(e^{-η τ})` for `0 < η < min(3001/48000, (1 - σ)/2)`, whereas `excitingPulse` at
     the off-line zero `p₀ = (factorZero q r - 1)/2` violates `O(e^{-δ τ})` for every
     `δ > (1 - σ)/2`.

2. **Finite-Time Inequality 1 (Predeclared-Window Cusp Escape Separation)**:
   On the predeclared window `(-S₀, 2 log q - S₀]` (`0 < S₀ < log q`), every mean-zero compact
   pulse `h` (`meanCoefficient h = 0`) supported in `[-S₀, S₀]` obeys
   `twinReflected q (r + u) h T = (1 / q) * pulseReflected h T` (`T ≤ 2 log q - S₀`) and
   `∫_{T₂}^∞ ‖twinReflected q (r + u) h T‖² dT - ∫_{T₂}^∞ ‖pulseReflected h T‖² dT
     = (1 - 1 / q²) ∫_{-S₀}^{T₂} ‖pulseReflected h T‖² dT > 0`
   at `T₂ = 2 log q - S₀`, realized unconditionally by an explicit balanced two-lobe pulse.

3. **Finite-Time Inequality 2 (Prime-Square `p²` and Mixed-Prime `p q` Group-Delay Interference)**:
   Global Schur passivity + imaginary-axis unitarity imply universal nonnegativity of the boundary
   group-delay density `-Re(S_red'(iξ)/S_red(iξ)) ≥ 0` and finite-band group delay. On the
   three-component mixed pulse `c₀ h₀(S) + c_{p²} h₀(S - 4 log p) + c_{pq} h₀(S - 2 log(p q))`
   (`p ≠ q` primes), retaining all diagonal, `p²`, `p q`, and beat cross-terms, all mixed-prime and
   beat interferences cancel identically by unique factorization, while flipping `c_{p²} ↦ -c_{p²}`
   isolates the exact `p²` logarithmic discrepancy
   `-(8 log p / (π p²)) (b_{p,A}(p²) - 1/2) ∫ ‖h₀‖² > 0` vs. `0` on `ζ` (both on the full line and
   on finite frequency windows `[-Ω, Ω]`).
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff FourierTransform Classical

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography (schurNum schurDen schur_bound_iff)
open GaloisForLFunctions.SelbergClass.PositiveFiniteEuler
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
  (riemannZeta_zero_mem_sub_quasiRH_strip)

private theorem integrable_tsum_of_summable_integral_norm
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [CompleteSpace E]
    {μ : Measure α} {F : ℕ → α → E}
    (hF : ∀ n, Integrable (F n) μ) (hsum : Summable fun n => ∫ x, ‖F n x‖ ∂μ) :
    Integrable (fun x => ∑' n, F n x) μ := by
  refine ⟨AEStronglyMeasurable.tsum fun n => (hF n).1, ?_⟩
  rw [HasFiniteIntegral]
  calc (∫⁻ x, ‖∑' n, F n x‖ₑ ∂μ)
      ≤ ∫⁻ x, ∑' n, ‖F n x‖ₑ ∂μ := lintegral_mono fun _ => enorm_tsum_le_tsum_enorm
    _ = ∑' n, ∫⁻ x, ‖F n x‖ₑ ∂μ := lintegral_tsum fun n => (hF n).1.enorm
    _ = ∑' n, ENNReal.ofReal (∫ x, ‖F n x‖ ∂μ) := by
        congr 1; funext n; rw [ofReal_integral_norm_eq_lintegral_enorm (hF n)]
    _ = ENNReal.ofReal (∑' n, ∫ x, ‖F n x‖ ∂μ) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun _ => norm_nonneg _) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-! ## 1. Retarded Echo Kernel and Reflected Packet of `PositiveEulerHorizon` -/

/-- Expansion coefficients of `PositiveEulerHorizon.gate q (r + u)` in powers of `q^{-2w}`. -/
def twinEchoCoeff (q : ℕ) (r u : ℝ) (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ m *
    ((((q : ℝ) - 1) * (r ^ 2 - 1)) / (r * (r - u)) * (r⁻¹) ^ (m + 1) -
     (((q : ℝ) - 1) * (u ^ 2 - 1)) / (u * (r - u)) * (u⁻¹) ^ (m + 1))

/-- Retarded echo kernel of `PositiveEulerHorizon` (`1 < q`, `1 < u < r`, `r * u = q`). -/
def twinEchoKernel (q : ℕ) (r u : ℝ) (τ : ℝ) : ℝ :=
  (1 / (q : ℝ)) * echoKernel τ +
    ∑' m : ℕ, twinEchoCoeff q r u m * echoKernel (τ - 2 * ((m : ℝ) + 1) * Real.log q)

/-- Time-domain echo response of `twinEchoKernel q r u` to a pulse `h`. -/
def twinEcho (q : ℕ) (r u : ℝ) (h : ℝ → ℂ) (T : ℝ) : ℂ :=
  ∫ τ : ℝ, h (T - τ) * ((twinEchoKernel q r u τ : ℝ) : ℂ)

/-- Reflected cusp wavepacket of `PositiveEulerHorizon`. -/
def twinReflected (q : ℕ) (A : ℝ) (h : ℝ → ℂ) (T : ℝ) : ℂ :=
  unitaryReflected (fun ξ => PositiveEulerHorizon.scatteringPhase q A ((ξ : ℂ) * I)) h T

/-- **Strict Retarded Causality of `twinEchoKernel`.** -/
theorem twinEchoKernel_eq_zero_of_nonpos (q : ℕ) (r u : ℝ) {τ : ℝ} (hτ : τ ≤ 0) :
    twinEchoKernel q r u τ = 0 := by
  have hlog : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hz : ∀ m : ℕ,
      twinEchoCoeff q r u m * echoKernel (τ - 2 * ((m : ℝ) + 1) * Real.log q) = 0 := by
    intro m
    have hm : τ - 2 * ((m : ℝ) + 1) * Real.log q ≤ 0 := by
      have : 0 ≤ 2 * ((m : ℝ) + 1) * Real.log q := by positivity
      linarith
    rw [echoKernel_eq_zero_of_nonpos hm, mul_zero]
  rw [twinEchoKernel, echoKernel_eq_zero_of_nonpos hτ, mul_zero, zero_add]
  simp [hz]

/-- **Exact Early-Window Attenuation.** Up to `2 log q`, only the prompt `1 / q` copy of
`echoKernel` has arrived. -/
theorem twinEchoKernel_eq_early {q : ℕ} (hq : 1 < q) (r u : ℝ) {τ : ℝ}
    (hτ : τ ≤ 2 * Real.log q) :
    twinEchoKernel q r u τ = (1 / (q : ℝ)) * echoKernel τ := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hz : ∀ m : ℕ,
      twinEchoCoeff q r u m * echoKernel (τ - 2 * ((m : ℝ) + 1) * Real.log q) = 0 := by
    intro m
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hm : τ - 2 * ((m : ℝ) + 1) * Real.log q ≤ 0 := by nlinarith
    rw [echoKernel_eq_zero_of_nonpos hm, mul_zero]
  rw [twinEchoKernel]
  simp [hz]

theorem measurable_twinEchoKernel (q : ℕ) (r u : ℝ) : Measurable (twinEchoKernel q r u) := by
  unfold twinEchoKernel
  refine (measurable_echoKernel.const_mul _).add (Measurable.tsum fun m => ?_)
  exact (measurable_echoKernel.comp (measurable_id.sub_const _)).const_mul _

theorem summable_abs_twinEchoCoeff (q : ℕ) {r u : ℝ} (hr : 1 < r) (hu : 1 < u) :
    Summable fun m : ℕ => |twinEchoCoeff q r u m| := by
  have hr_inv0 : 0 ≤ r⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hr).le
  have hu_inv0 : 0 ≤ u⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hu).le
  have hr_inv1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have hu_inv1 : u⁻¹ < 1 := inv_lt_one_of_one_lt₀ hu
  set Cr : ℝ := |(((q : ℝ) - 1) * (r ^ 2 - 1)) / (r * (r - u))| * r⁻¹
  set Cu : ℝ := |(((q : ℝ) - 1) * (u ^ 2 - 1)) / (u * (r - u))| * u⁻¹
  have hdom : Summable fun m : ℕ => Cr * (r⁻¹) ^ m + Cu * (u⁻¹) ^ m :=
    ((summable_geometric_of_lt_one hr_inv0 hr_inv1).mul_left Cr).add
      ((summable_geometric_of_lt_one hu_inv0 hu_inv1).mul_left Cu)
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun m => ?_) hdom
  unfold twinEchoCoeff
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hr_inv0, abs_of_nonneg hu_inv0,
    pow_succ, pow_succ]
  exact le_of_eq (by simp only [Cr, Cu]; ring)

private theorem gate_partial_fractions {q : ℕ} (hq : 1 < q) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = q) (hur : u < r) {v : ℂ} (hv : ‖v‖ ≤ 1) :
    schurNum q (-(r + u)) v / schurDen q (-(r + u)) v =
      (1 / (q : ℂ)) +
        ((((q : ℝ) - 1) * (r ^ 2 - 1) / (r * (r - u)) : ℝ) : ℂ) *
          (((r⁻¹ : ℝ) : ℂ) * v * (1 + ((r⁻¹ : ℝ) : ℂ) * v)⁻¹) -
        ((((q : ℝ) - 1) * (u ^ 2 - 1) / (u * (r - u)) : ℝ) : ℂ) *
          (((u⁻¹ : ℝ) : ℂ) * v * (1 + ((u⁻¹ : ℝ) : ℂ) * v)⁻¹) := by
  have _ := hq
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hr).ne'
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hu).ne'
  have hsub0 : (r : ℂ) - (u : ℂ) ≠ 0 :=
    sub_ne_zero.mpr fun h => hur.ne' (Complex.ofReal_inj.mp h)
  have hne_a : ∀ {a : ℝ}, 1 < a → (a : ℂ) + v ≠ 0 ∧ (1 : ℂ) + ((a⁻¹ : ℝ) : ℂ) * v ≠ 0 := by
    intro a ha
    have ha0 : 0 < a := zero_lt_one.trans ha
    have h1 : (a : ℂ) + v ≠ 0 := fun h => by
      have hv_eq : v = -(a : ℂ) := by linear_combination h
      rw [hv_eq, norm_neg, Complex.norm_real, Real.norm_of_nonneg ha0.le] at hv
      linarith
    have h2 : (1 : ℂ) + ((a⁻¹ : ℝ) : ℂ) * v ≠ 0 := fun h => h1 (by
      have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0.ne'
      have hm := congrArg ((a : ℂ) * ·) h
      push_cast at hm
      field_simp [haC] at hm
      linear_combination hm)
    exact ⟨h1, h2⟩
  obtain ⟨hrv, hrv1⟩ := hne_a hr
  obtain ⟨huv, huv1⟩ := hne_a hu
  have hruR : ((q : ℝ) : ℂ) = (r : ℂ) * (u : ℂ) := by rw [← hru, Complex.ofReal_mul]
  have hruC : (q : ℂ) = (r : ℂ) * (u : ℂ) := by rw [← Complex.ofReal_natCast, hruR]
  have hden : schurDen q (-(r + u)) v = ((r : ℂ) + v) * ((u : ℂ) + v) := by
    simp only [schurDen, Complex.ofReal_neg, Complex.ofReal_add]
    rw [hruR]; ring
  have hnum : schurNum q (-(r + u)) v = (1 + (r : ℂ) * v) * (1 + (u : ℂ) * v) := by
    simp only [schurNum, Complex.ofReal_neg, Complex.ofReal_add]
    rw [hruR]; ring
  have hinv_r : ((r⁻¹ : ℝ) : ℂ) * v * (1 + ((r⁻¹ : ℝ) : ℂ) * v)⁻¹ = v / ((r : ℂ) + v) := by
    push_cast
    rw [eq_div_iff hrv]
    field_simp [hr0, hrv1]
  have hinv_u : ((u⁻¹ : ℝ) : ℂ) * v * (1 + ((u⁻¹ : ℝ) : ℂ) * v)⁻¹ = v / ((u : ℂ) + v) := by
    push_cast
    rw [eq_div_iff huv]
    field_simp [hu0, huv1]
  rw [hnum, hden, hinv_r, hinv_u]
  push_cast
  rw [hruC]
  have hprod0 : (r : ℂ) * (u : ℂ) ≠ 0 := mul_ne_zero hr0 hu0
  field_simp [hr0, hu0, hsub0, hrv, huv, hprod0]
  ring

/-- Power-series representation of `PositiveEulerHorizon.gate q (r + u) w` across `Re w ≥ 0`. -/
theorem hasSum_twinEchoCoeff_gate {q : ℕ} (hq : 1 < q) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = q) (hur : u < r) {w : ℂ} (hw : 0 ≤ w.re) :
    HasSum (fun m : ℕ =>
        ((twinEchoCoeff q r u m : ℝ) : ℂ) *
          Complex.exp (-w * ((2 * ((m : ℝ) + 1) * Real.log q : ℝ) : ℂ)))
      (PositiveEulerHorizon.gate q (r + u) w - 1 / (q : ℂ)) := by
  set v : ℂ := (q : ℂ) ^ (-2 * w) with hv_def
  have hv_le : ‖v‖ ≤ 1 := by
    rw [hv_def, Complex.norm_natCast_cpow_of_pos (by omega),
      show (-2 * w).re = -2 * w.re by simp]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hq.le) (by linarith)
  have hvm : ∀ m : ℕ,
      Complex.exp (-w * ((2 * ((m : ℝ) + 1) * Real.log q : ℝ) : ℂ)) = v ^ (m + 1) := by
    intro m
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    rw [hv_def, Complex.cpow_def_of_ne_zero hq0, ← Complex.natCast_log, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hr_lt : ‖-((r⁻¹ : ℝ) : ℂ) * v‖ < 1 := by
    rw [norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (zero_lt_one.trans hr).le)]
    calc r⁻¹ * ‖v‖ ≤ r⁻¹ * 1 := mul_le_mul_of_nonneg_left hv_le (by positivity)
      _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hr
  have hu_lt : ‖-((u⁻¹ : ℝ) : ℂ) * v‖ < 1 := by
    rw [norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (zero_lt_one.trans hu).le)]
    calc u⁻¹ * ‖v‖ ≤ u⁻¹ * 1 := mul_le_mul_of_nonneg_left hv_le (by positivity)
      _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hu
  set Cr : ℂ := ((((q : ℝ) - 1) * (r ^ 2 - 1) / (r * (r - u)) : ℝ) : ℂ)
  set Cu : ℂ := ((((q : ℝ) - 1) * (u ^ 2 - 1) / (u * (r - u)) : ℝ) : ℂ)
  have hgeo_r := (hasSum_geometric_of_norm_lt_one hr_lt).mul_left (Cr * (((r⁻¹ : ℝ) : ℂ) * v))
  have hgeo_u := (hasSum_geometric_of_norm_lt_one hu_lt).mul_left (Cu * (((u⁻¹ : ℝ) : ℂ) * v))
  have hsub := hgeo_r.sub hgeo_u
  have hr_den : (1 - -((r⁻¹ : ℝ) : ℂ) * v) = 1 + ((r⁻¹ : ℝ) : ℂ) * v := by ring
  have hu_den : (1 - -((u⁻¹ : ℝ) : ℂ) * v) = 1 + ((u⁻¹ : ℝ) : ℂ) * v := by ring
  rw [hr_den, hu_den] at hsub
  have hpf := gate_partial_fractions hq hr hu hru hur hv_le
  have hval : Cr * (((r⁻¹ : ℝ) : ℂ) * v) * (1 + ((r⁻¹ : ℝ) : ℂ) * v)⁻¹ -
      Cu * (((u⁻¹ : ℝ) : ℂ) * v) * (1 + ((u⁻¹ : ℝ) : ℂ) * v)⁻¹ =
      PositiveEulerHorizon.gate q (r + u) w - 1 / (q : ℂ) := by
    rw [PositiveEulerHorizon.gate, ← hv_def, hpf]
    simp only [Cr, Cu]
    ring
  have hsub' : HasSum (fun m : ℕ =>
      Cr * (((r⁻¹ : ℝ) : ℂ) * v) * (-((r⁻¹ : ℝ) : ℂ) * v) ^ m -
        Cu * (((u⁻¹ : ℝ) : ℂ) * v) * (-((u⁻¹ : ℝ) : ℂ) * v) ^ m)
      (PositiveEulerHorizon.gate q (r + u) w - 1 / (q : ℂ)) := by
    rw [← hval]
    exact hsub
  refine hsub'.congr_fun fun m => ?_
  rw [hvm m]
  simp only [twinEchoCoeff, Cr, Cu]
  push_cast
  have hr_pow : (((r⁻¹ : ℝ) : ℂ) * v) * (-((r⁻¹ : ℝ) : ℂ) * v) ^ m =
      (-1 : ℂ) ^ m * ((r⁻¹ : ℝ) : ℂ) ^ (m + 1) * v ^ (m + 1) := by
    rw [show -((r⁻¹ : ℝ) : ℂ) * v = (-1 : ℂ) * ((r⁻¹ : ℝ) : ℂ) * v by ring,
      mul_pow, mul_pow, pow_succ, pow_succ]
    ring
  have hu_pow : (((u⁻¹ : ℝ) : ℂ) * v) * (-((u⁻¹ : ℝ) : ℂ) * v) ^ m =
      (-1 : ℂ) ^ m * ((u⁻¹ : ℝ) : ℂ) ^ (m + 1) * v ^ (m + 1) := by
    rw [show -((u⁻¹ : ℝ) : ℂ) * v = (-1 : ℂ) * ((u⁻¹ : ℝ) : ℂ) * v by ring,
      mul_pow, mul_pow, pow_succ, pow_succ]
    ring
  linear_combination Cr * hr_pow - Cu * hu_pow

/-- **Laplace Transform of `twinEchoKernel`.** On `Re w > 1/2`, `twinEchoKernel q r u` is
exponentially integrable and transforms to `gate q (r + u) w * (Λ(2w)/Λ(2w+1))`. -/
theorem integrable_and_laplace_twinEchoKernel {q : ℕ} (hq : 1 < q) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = q) (hur : u < r) {w : ℂ} (hw : 1 / 2 < w.re) :
    Integrable (fun τ : ℝ => Complex.exp (-w * (τ : ℂ)) * ((twinEchoKernel q r u τ : ℝ) : ℂ)) ∧
      (∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * ((twinEchoKernel q r u τ : ℝ) : ℂ)) =
        PositiveEulerHorizon.gate q (r + u) w *
          (completedRiemannZeta (2 * w) / completedRiemannZeta (2 * w + 1)) := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hint0 := integrable_cexp_mul_echoKernel hw
  have hval0 := integral_cexp_mul_echoKernel_eq_completed hw
  set G : ℕ → ℝ → ℂ := fun m τ =>
    ((twinEchoCoeff q r u m : ℝ) : ℂ) *
      (Complex.exp (-w * (τ : ℂ)) *
        ((echoKernel (τ - 2 * ((m : ℝ) + 1) * Real.log q) : ℝ) : ℂ)) with hG
  have hG_shift : ∀ m τ, G m τ =
      ((twinEchoCoeff q r u m : ℝ) : ℂ) *
        Complex.exp (-w * ((2 * ((m : ℝ) + 1) * Real.log q : ℝ) : ℂ)) *
        (Complex.exp (-w * ((τ - 2 * ((m : ℝ) + 1) * Real.log q : ℝ) : ℂ)) *
          ((echoKernel (τ - 2 * ((m : ℝ) + 1) * Real.log q) : ℝ) : ℂ)) := by
    intro m τ
    simp only [hG]
    have he : Complex.exp (-w * (τ : ℂ)) =
        Complex.exp (-w * ((2 * ((m : ℝ) + 1) * Real.log q : ℝ) : ℂ)) *
          Complex.exp (-w * ((τ - 2 * ((m : ℝ) + 1) * Real.log q : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1; push_cast; ring
    rw [he]; ring
  have hG_int : ∀ m : ℕ, Integrable (G m) := by
    intro m
    have h1 := (hint0.comp_sub_right (2 * ((m : ℝ) + 1) * Real.log q)).const_mul
      (((twinEchoCoeff q r u m : ℝ) : ℂ) *
        Complex.exp (-w * ((2 * ((m : ℝ) + 1) * Real.log q : ℝ) : ℂ)))
    exact h1.congr (Eventually.of_forall fun τ => (hG_shift m τ).symm)
  have hG_norm_sum : Summable fun m : ℕ => ∫ τ : ℝ, ‖G m τ‖ := by
    have hdom := (summable_abs_twinEchoCoeff q hr hu).mul_right
      (∫ v : ℝ, ‖Complex.exp (-w * (v : ℂ)) * ((echoKernel v : ℝ) : ℂ)‖)
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun m => ?_) hdom
    have hpt : ∀ τ : ℝ, ‖G m τ‖ ≤ |twinEchoCoeff q r u m| *
        ‖Complex.exp (-w * ((τ - 2 * ((m : ℝ) + 1) * Real.log q : ℝ) : ℂ)) *
          ((echoKernel (τ - 2 * ((m : ℝ) + 1) * Real.log q) : ℝ) : ℂ)‖ := by
      intro τ
      rw [hG_shift m τ, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      have hexp_le : Real.exp ((-w * ((2 * ((m : ℝ) + 1) * Real.log q : ℝ) : ℂ)).re) ≤ 1 := by
        rw [Complex.re_mul_ofReal, Complex.neg_re, Real.exp_le_one_iff]
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      calc |twinEchoCoeff q r u m| *
              Real.exp ((-w * ((2 * ((m : ℝ) + 1) * Real.log q : ℝ) : ℂ)).re) * _
          ≤ |twinEchoCoeff q r u m| * 1 * _ := by gcongr
        _ = _ := by ring
    calc ∫ τ : ℝ, ‖G m τ‖
        ≤ ∫ τ : ℝ, |twinEchoCoeff q r u m| *
            ‖Complex.exp (-w * ((τ - 2 * ((m : ℝ) + 1) * Real.log q : ℝ) : ℂ)) *
              ((echoKernel (τ - 2 * ((m : ℝ) + 1) * Real.log q) : ℝ) : ℂ)‖ :=
          integral_mono (hG_int m).norm
            ((hint0.norm.comp_sub_right _).const_mul _) hpt
      _ = |twinEchoCoeff q r u m| *
            ∫ v : ℝ, ‖Complex.exp (-w * (v : ℂ)) * ((echoKernel v : ℝ) : ℂ)‖ := by
          rw [integral_const_mul, integral_sub_right_eq_self (μ := volume)
            (fun v : ℝ => ‖Complex.exp (-w * (v : ℂ)) * ((echoKernel v : ℝ) : ℂ)‖)
            (2 * ((m : ℝ) + 1) * Real.log q)]
  have hHS := hasSum_integral_of_summable_integral_norm hG_int hG_norm_sum
  have hint_tsum : Integrable fun τ : ℝ => ∑' m : ℕ, G m τ :=
    integrable_tsum_of_summable_integral_norm hG_int hG_norm_sum
  have hpoint : ∀ τ : ℝ,
      Complex.exp (-w * (τ : ℂ)) * ((twinEchoKernel q r u τ : ℝ) : ℂ) =
        ((1 / (q : ℂ)) * (Complex.exp (-w * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ))) +
          ∑' m : ℕ, G m τ := by
    intro τ
    rw [twinEchoKernel, Complex.ofReal_add, mul_add, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_natCast, Complex.ofReal_tsum, ← tsum_mul_left]
    congr 1
    · ring
    · exact tsum_congr fun m => by simp only [hG, Complex.ofReal_mul]; ring
  have hint_full : Integrable fun τ : ℝ =>
      Complex.exp (-w * (τ : ℂ)) * ((twinEchoKernel q r u τ : ℝ) : ℂ) :=
    ((hint0.const_mul (1 / (q : ℂ))).add hint_tsum).congr
      (Eventually.of_forall fun τ => (hpoint τ).symm)
  refine ⟨hint_full, ?_⟩
  simp_rw [hpoint]
  rw [integral_add (hint0.const_mul _) hint_tsum, integral_const_mul, hval0, ← hHS.tsum_eq]
  have hG_int_val : ∀ m : ℕ, ∫ τ : ℝ, G m τ =
      (((twinEchoCoeff q r u m : ℝ) : ℂ) *
        Complex.exp (-w * ((2 * ((m : ℝ) + 1) * Real.log q : ℝ) : ℂ))) *
        (completedRiemannZeta (2 * w) / completedRiemannZeta (2 * w + 1)) := by
    intro m
    simp_rw [hG_shift m]
    rw [integral_const_mul, integral_sub_right_eq_self (μ := volume)
      (fun v : ℝ => Complex.exp (-w * (v : ℂ)) * ((echoKernel v : ℝ) : ℂ))
      (2 * ((m : ℝ) + 1) * Real.log q), hval0]
  simp_rw [hG_int_val]
  rw [tsum_mul_right, (hasSum_twinEchoCoeff_gate hq hr hu hru hur (by linarith)).tsum_eq]
  ring

/-- **Contour-Shift Decomposition of `twinEcho`.** Shifting across `w = 1/2` splits the causal echo
convolution `twinEcho q r u h` into `twinReflected q (r + u) h` plus the attenuated zero-mode
`gate q (r + u) (1/2) * meanCoefficient h * e^{T/2}`. -/
theorem twinEcho_eq_reflected_add_mean {q : ℕ} (hq : 1 < q) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = q) (hur : u < r)
    (h : CompactPulse) (T : ℝ) :
    twinEcho q r u h T =
      twinReflected q (r + u) h T +
        PositiveEulerHorizon.gate q (r + u) (1 / 2) * meanCoefficient h *
          Complex.exp ((T : ℂ) / 2) := by
  have hw1 : (1 / 2 : ℝ) < ((1 : ℝ) : ℂ).re := by norm_num
  obtain ⟨hK1_int, _⟩ := integrable_and_laplace_twinEchoKernel hq hr hu hru hur hw1
  set D : ℝ → ℝ → ℂ := fun τ y =>
    pulseAmplitude h (-I * linePoint 1 y) * Complex.exp (linePoint 1 y * ((T - τ : ℝ) : ℂ)) *
      ((twinEchoKernel q r u τ : ℝ) : ℂ) with hD
  have hA : Integrable fun y : ℝ => pulseAmplitude h (-I * linePoint 1 y) := by
    refine (h.integrable_amplitude_line 1).congr (Eventually.of_forall fun y => ?_)
    simp only [linePoint]
    congr 1; linear_combination (y : ℂ) * I_sq
  have hD_int : Integrable (Function.uncurry D) (volume.prod volume) := by
    have hG := hK1_int.norm.mul_prod (hA.norm.const_mul (Real.exp (1 * T)))
    have hmeas : Measurable (Function.uncurry D) :=
      (((h.differentiable_amplitude.continuous.comp (by unfold linePoint; fun_prop)).measurable.mul
        (by unfold linePoint; fun_prop : Continuous fun p : ℝ × ℝ =>
          Complex.exp (linePoint 1 p.2 * ((T - p.1 : ℝ) : ℂ))).measurable).mul
        (Complex.measurable_ofReal.comp ((measurable_twinEchoKernel q r u).comp measurable_fst)))
    refine hG.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun p => le_of_eq ?_)
    have hE1 : ‖Complex.exp (linePoint 1 p.2 * ((T - p.1 : ℝ) : ℂ))‖ =
        Real.exp (1 * T) * Real.exp (-1 * p.1) := by
      rw [Complex.norm_exp, ← Real.exp_add]
      congr 1
      have : (linePoint 1 p.2 * ((T - p.1 : ℝ) : ℂ)).re = 1 * (T - p.1) := by simp [linePoint]
      rw [this]; ring
    have hE2 : ‖Complex.exp (-((1 : ℝ) : ℂ) * (p.1 : ℂ))‖ = Real.exp (-1 * p.1) := by
      rw [Complex.norm_exp]; congr 1; simp
    show ‖D p.1 p.2‖ = _
    simp only [hD, norm_mul]
    rw [hE1, hE2]; ring
  have hDy : ∀ τ : ℝ, ∫ y : ℝ, D τ y = h (T - τ) * ((twinEchoKernel q r u τ : ℝ) : ℂ) := by
    intro τ
    simp only [hD, linePoint]
    rw [integral_mul_const, h.eq_integral_amplitude_line 1 (T - τ)]
  have hDτ : ∀ y : ℝ, ∫ τ : ℝ, D τ y =
      pulseAmplitude h (-I * linePoint 1 y) * Complex.exp (linePoint 1 y * (T : ℂ)) *
        PositiveEulerHorizon.scatteringPhase q (r + u) (linePoint 1 y) := by
    intro y
    have hre : 1 / 2 < (linePoint 1 y).re := by rw [linePoint_re]; norm_num
    have hpt : ∀ τ : ℝ, D τ y = pulseAmplitude h (-I * linePoint 1 y) *
        Complex.exp (linePoint 1 y * (T : ℂ)) *
          (Complex.exp (-linePoint 1 y * (τ : ℂ)) * ((twinEchoKernel q r u τ : ℝ) : ℂ)) := by
      intro τ
      have he : Complex.exp (linePoint 1 y * ((T - τ : ℝ) : ℂ)) =
          Complex.exp (linePoint 1 y * (T : ℂ)) * Complex.exp (-linePoint 1 y * (τ : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      simp only [hD]; rw [he]; ring
    simp_rw [hpt]
    rw [integral_const_mul, (integrable_and_laplace_twinEchoKernel hq hr hu hru hur hre).2,
      completed_div_eq_scatteringPhase hre,
      PositiveEulerHorizon.scatteringPhase_eq_gate_mul (by omega)]
    rfl
  have hline1 : twinEcho q r u h T = ∫ y : ℝ, pulseAmplitude h (-I * linePoint 1 y) *
      Complex.exp (linePoint 1 y * (T : ℂ)) *
        PositiveEulerHorizon.scatteringPhase q (r + u) (linePoint 1 y) := by
    have hswap := integral_integral_swap (f := D) hD_int
    simp_rw [hDy, hDτ] at hswap
    exact hswap
  set F : ℂ → ℂ := fun w => PositiveEulerHorizon.gate q (r + u) w * h.echoIntegrand T w with hF
  have hgate_an : ∀ w : ℂ, 0 ≤ w.re → AnalyticAt ℂ (PositiveEulerHorizon.gate q (r + u)) w := by
    intro w hw
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have heq : PositiveEulerHorizon.gate q (r + u) =
        fun z : ℂ => completedFactor q (r + u) (2 * z) / completedFactor q (r + u) (1 + 2 * z) :=
      funext fun z => (PositiveEulerHorizon.factor_ratio_eq_gate (by omega) (r + u) z).symm
    rw [heq]
    have hdf : Differentiable ℂ (completedFactor q (r + u)) := by
      have hc : completedFactor q (r + u) = fun s : ℂ => (q : ℂ) ^ s * localFactor q (r + u) s :=
        funext fun s => (cpow_mul_localFactor (by omega) (r + u) s).symm
      rw [hc]
      exact (differentiable_id.const_cpow (.inl hqC)).mul
        (differentiable_localFactor (by omega) (r + u))
    have hden_ne : completedFactor q (r + u) (1 + 2 * w) ≠ 0 := fun hz =>
      PositiveEulerHorizon.completedXi_den_ne_zero hq hr hu hru hw
        (by rw [PositiveEulerHorizon.completedXi, hz, zero_mul])
    exact ((hdf.comp (by fun_prop)).analyticAt w).div
      ((hdf.comp (by fun_prop)).analyticAt w) hden_ne
  obtain ⟨K, _, hK⟩ := h.exists_norm_echoIntegrand_le T (c := 1) (by norm_num)
  have hF_bound : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → 1 / 2 ≤ |w.im| →
      ‖F w‖ ≤ K * ((1 + |w.im|) ^ 2)⁻¹ := by
    intro w h0 h1 him
    simp only [hF]
    rw [norm_mul]
    calc ‖PositiveEulerHorizon.gate q (r + u) w‖ * ‖h.echoIntegrand T w‖
        ≤ 1 * (K * ((1 + |w.im|) ^ 2)⁻¹) :=
          mul_le_mul (PositiveEulerHorizon.norm_gate_le_one hq hr hu hru h0)
            (hK w h0 h1 him) (norm_nonneg _) zero_le_one
      _ = K * ((1 + |w.im|) ^ 2)⁻¹ := one_mul _
  have hF_line_int : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → c ≠ 1 / 2 →
      Integrable fun y : ℝ => F ((c : ℂ) + (y : ℂ) * I) := by
    intro c hc0 hc1 hcne
    have hcont : Continuous fun y : ℝ => F ((c : ℂ) + (y : ℂ) * I) := by
      refine continuous_iff_continuousAt.mpr fun y => ?_
      set z : ℂ := (c : ℂ) + (y : ℂ) * I
      have hz0 : 0 ≤ z.re := by simp [z, hc0]
      have hd : 2 * z - 1 ≠ 0 := fun h0 => hcne (by
        have := congrArg Complex.re h0; simp [z] at this; linarith)
      have han : AnalyticAt ℂ F z :=
        (hgate_an z hz0).mul ((h.analyticAt_echoRegular T hz0).div (by fun_prop) hd)
      exact ContinuousAt.comp (f := fun y : ℝ => (c : ℂ) + (y : ℂ) * I) han.continuousAt (by fun_prop)
    refine integrable_of_continuous_of_inv_sq_tail hcont (R := 1 / 2) (C := K) fun y hy => ?_
    simpa using hF_bound ((c : ℂ) + (y : ℂ) * I) (by simp [hc0]) (by simp [hc1]) (by simpa using hy)
  have hLat : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun k : ℕ => K * ((1 + ((k : ℝ) + 1)) ^ 2)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 + ((k : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_left _ _ hLat
    have h2 : Tendsto (fun k : ℕ => (1 + ((k : ℝ) + 1)) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp h1
    simpa using (tendsto_inv_atTop_zero.comp h2).const_mul K
  have hshift := integral_line_shift (f := F) (c := 1) (by norm_num)
    (fun s hs _ hne => (hgate_an s hs).mul
      ((h.analyticAt_echoRegular T hs).div (by fun_prop) (fun h0 => hne (by linear_combination h0 / 2))))
    ((hgate_an (1 / 2) (by norm_num)).meromorphicAt.mul
      ((h.analyticAt_echoRegular T (by norm_num)).meromorphicAt.div
        (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 2 * w - 1) (1 / 2)).meromorphicAt))
    (hF_line_int 1 (by norm_num) le_rfl (by norm_num))
    (hF_line_int 0 le_rfl (by norm_num) (by norm_num)) hLat hB
    (Eventually.of_forall fun k x hx s hs => by
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      simpa [hs] using hF_bound ((x : ℂ) + (s : ℂ) * I) (by simp [hx.1]) (by simp [hx.2])
        (by simp [hs]; linarith))
  have hres : laurentCoeff F (1 / 2) (-1) =
      PositiveEulerHorizon.gate q (r + u) (1 / 2) *
        pulseAmplitude h (-I * (1 / 2)) * Complex.exp ((T : ℂ) / 2) * (3 / (Real.pi : ℂ)) := by
    have hD2 : Differentiable ℂ fun w : ℂ => 2 * w - 1 := by fun_prop
    have hder : deriv (fun w : ℂ => 2 * w - 1) (1 / 2) = 2 := by
      exact (((hasDerivAt_id (1 / 2 : ℂ)).const_mul 2).sub_const 1 |>.congr_deriv (by ring)).deriv
    have hP : AnalyticAt ℂ (fun v : ℂ => PositiveEulerHorizon.gate q (r + u) v *
        (pulseAmplitude h (-I * v) * Complex.exp (v * (T : ℂ)) *
          ((1 + 2 * v) * (xi (2 * v) / xi (1 + 2 * v))))) (1 / 2) :=
      (hgate_an (1 / 2) (by norm_num)).mul (h.analyticAt_echoRegular T (by norm_num))
    have hFeq : F = fun z : ℂ => (PositiveEulerHorizon.gate q (r + u) z *
        (pulseAmplitude h (-I * z) * Complex.exp (z * (T : ℂ)) *
          ((1 + 2 * z) * (xi (2 * z) / xi (1 + 2 * z))))) / (2 * z - 1) := by
      funext z; simp only [hF, CompactPulse.echoIntegrand]; ring
    rw [hFeq, laurentCoeff_div_of_simple_zero hP hD2 (by norm_num) (by rw [hder]; norm_num), hder]
    have e1 : (2 : ℂ) * (1 / 2) = 1 := by norm_num
    have e2 : (1 : ℂ) + 1 = 2 := by norm_num
    rw [e1, e2, xi_one_div_xi_two, show (1 / 2 : ℂ) * (T : ℂ) = (T : ℂ) / 2 by ring]
    ring
  rw [hres] at hshift
  have hright : (∫ y : ℝ, F (((1 : ℝ) : ℂ) + (y : ℂ) * I)) = twinEcho q r u h T := by
    rw [hline1]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hF, linePoint]
    rw [h.echoIntegrand_eq T, PositiveEulerHorizon.scatteringPhase_eq_gate_mul (by omega)]
    unfold scatteringPhase modularScatteringPhase
    ring
  have hleft : (∫ y : ℝ, F (((0 : ℝ) : ℂ) + (y : ℂ) * I)) = twinReflected q (r + u) h T := by
    rw [twinReflected, unitaryReflected]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hF]
    rw [h.echoIntegrand_eq T]
    have e : ((0 : ℝ) : ℂ) + (t : ℂ) * I = (t : ℂ) * I := by simp
    have harg : -I * ((t : ℂ) * I) = (t : ℂ) := by linear_combination (-(t : ℂ)) * I_sq
    have he : Complex.exp ((t : ℂ) * I * (T : ℂ)) = Complex.exp (I * (t : ℂ) * (T : ℂ)) := by
      congr 1; ring
    rw [e, harg, he, PositiveEulerHorizon.scatteringPhase_eq_gate_mul (by omega)]
    unfold scatteringPhase modularScatteringPhase
    ring
  rw [hright, hleft, sub_eq_iff_eq_add] at hshift
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hshift, meanCoefficient]
  field_simp
  ring

theorem twinEcho_eq_zero_before_wavefront {q : ℕ} {r u S₀ T : ℝ} (h : CompactPulse)
    (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) (hT : T < -S₀) :
    twinEcho q r u h T = 0 := by
  rw [twinEcho]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun τ => ?_)
  rcases le_or_gt τ 0 with hτ | hτ
  · simp [twinEchoKernel_eq_zero_of_nonpos q r u hτ]
  · have hs : S₀ < |T - τ| := by
      have := neg_abs_le (T - τ); linarith
    simp [hS₀ (T - τ) hs]

theorem twinReflected_before_wavefront {q : ℕ} (hq : 1 < q) {r u S₀ T : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = q) (hur : u < r)
    (h : CompactPulse) (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) (hT : T < -S₀) :
    twinReflected q (r + u) h T =
      -(PositiveEulerHorizon.gate q (r + u) (1 / 2) * meanCoefficient h *
        Complex.exp ((T : ℂ) / 2)) := by
  have he := twinEcho_eq_reflected_add_mean hq hr hu hru hur h T
  rw [twinEcho_eq_zero_before_wavefront h hS₀ hT] at he
  linear_combination -he

/-- **Exact Early-Window Proportionality for Mean-Zero Pulses.** For any mean-zero compact pulse
supported in `[-S₀, S₀]`, up to `T ≤ 2 log q - S₀` the twin reflected signal is identically
`(1 / q)` times the undeformed modular reflected signal. -/
theorem twinReflected_eq_div_early_of_meanZero {q : ℕ} (hq : 1 < q) {r u S₀ T : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = q) (hur : u < r)
    (h : CompactPulse) (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) (hmean : meanCoefficient h = 0)
    (hT : T ≤ 2 * Real.log q - S₀) :
    twinReflected q (r + u) h T = (1 / (q : ℂ)) * pulseReflected h T := by
  have he1 := twinEcho_eq_reflected_add_mean hq hr hu hru hur h T
  have he2 := h.pulseEcho_eq T
  rw [hmean, mul_zero, zero_mul, add_zero] at he1
  rw [hmean, zero_mul, add_zero] at he2
  rw [← he1, ← he2, twinEcho, pulseEcho, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  dsimp only
  rcases le_or_gt τ (2 * Real.log q) with hτ | hτ
  · rw [twinEchoKernel_eq_early hq r u hτ]
    push_cast; ring
  · have hs : S₀ < |T - τ| := by
      have := neg_abs_le (T - τ); linarith
    simp [hS₀ (T - τ) hs]

/-! ## 2. Exact Ringdown Dichotomy of `PositiveEulerHorizon` -/

private theorem continuous_scatteringPhase_twin_line {q : ℕ} (hq : 1 < q) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = q) :
    Continuous fun ξ : ℝ => PositiveEulerHorizon.scatteringPhase q (r + u) ((ξ : ℂ) * I) := by
  refine continuous_iff_continuousAt.mpr fun ξ => ?_
  have hne : ((ξ : ℂ) * I) ≠ 1 / 2 := fun he => by
    have := congrArg Complex.re he; simp at this
  have hd : 2 * ((ξ : ℂ) * I) - 1 ≠ 0 := fun h0 => hne (by linear_combination h0 / 2)
  have hdiff : DifferentiableAt ℂ (PositiveEulerHorizon.scatteringPhase q (r + u)) ((ξ : ℂ) * I) :=
    ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) ((ξ : ℂ) * I)).div
      (by fun_prop) hd).mul
      (PositiveEulerHorizon.differentiableAt_reducedScattering hq hr hu hru (by simp))
  exact ContinuousAt.comp (f := fun ξ : ℝ => (ξ : ℂ) * I) hdiff.continuousAt (by fun_prop)

theorem integrable_and_integral_norm_sq_twinReflected {q : ℕ} (hq : 1 < q) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = q) (h : CompactPulse) :
    Integrable (fun T : ℝ => ‖twinReflected q (r + u) h T‖ ^ 2) ∧
      (∫ T : ℝ, ‖twinReflected q (r + u) h T‖ ^ 2) = ∫ S : ℝ, ‖h S‖ ^ 2 :=
  integrable_and_integral_norm_sq_unitaryReflected
    (continuous_scatteringPhase_twin_line hq hr hu hru).measurable
    (PositiveEulerHorizon.norm_scatteringPhase_axis hq hr hu hru) h

private theorem differentiableAt_twinScatteringPhase {q : ℕ} (hq : q ≠ 0) {A : ℝ} {w : ℂ}
    (hne : w ≠ 1 / 2) (hxi : PositiveEulerHorizon.completedXi q A (1 + 2 * w) ≠ 0) :
    DifferentiableAt ℂ (PositiveEulerHorizon.scatteringPhase q A) w := by
  have hd : 2 * w - 1 ≠ 0 := fun h0 => hne (by linear_combination h0 / 2)
  have hcx := PositiveEulerHorizon.differentiable_completedXi hq A
  unfold PositiveEulerHorizon.scatteringPhase PositiveEulerHorizon.reducedScattering
  exact ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) w).div (by fun_prop) hd).mul
    (((hcx _).comp w (by fun_prop)).div ((hcx _).comp w (by fun_prop)) hxi)

private theorem exists_amplitude_twin_right_le {q : ℕ} (hq : 1 < q) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = q) (h : CompactPulse) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 3 / 8 →
      ‖pulseAmplitude h (-I * w) * PositiveEulerHorizon.scatteringPhase q (r + u) w‖ ≤
        B / (1 + w.im ^ 2) := by
  obtain ⟨C₁, hC₁, hζ_log⟩ := exists_norm_inv_LFunction_le_log_pow (1 : DirichletCharacter ℂ 1)
  set boxR : Set ℂ := {z : ℂ | (1 ≤ z.re ∧ z.re ≤ 2) ∧ 2 ≤ |z.im| ∧ |z.im| ≤ 10}
  have hboxR_c : IsCompact boxR := by
    have heq : boxR = ((Icc (1 : ℝ) 2) ×ℂ (Icc (-10 : ℝ) 10)) ∩ {z : ℂ | 2 ≤ |z.im|} := by
      ext z
      simp only [boxR, mem_inter_iff, Complex.mem_reProdIm, mem_Icc, mem_setOf_eq, abs_le]
      tauto
    rw [heq]
    exact (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im))
  have hcont_ζ : ContinuousOn (fun z : ℂ => (riemannZeta z)⁻¹) boxR := by
    intro z hz
    have hne1 : z ≠ 1 := fun he => by have := hz.2.1; rw [he] at this; simp at this; linarith
    exact ((differentiableAt_riemannZeta hne1).continuousAt.inv₀
      (riemannZeta_ne_zero_of_one_le_re hz.1.1)).continuousWithinAt
  obtain ⟨M₁, hM₁⟩ := hboxR_c.exists_bound_of_continuousOn hcont_ζ
  have hζ_shift : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 8 → 1 ≤ |s.im| →
      ‖(riemannZeta (2 * s))⁻¹‖ ≤ (max (max M₁ 0) (C₁ * 2 ^ 7)) * |s.im| ^ 7 := by
    intro s hs1 hs2 hsim
    set z : ℂ := 2 * s with hzdef
    have hzre1 : 1 ≤ z.re := by simp [hzdef]; linarith
    have hzre2 : z.re ≤ 2 := by simp [hzdef]; linarith
    have hzim : |z.im| = 2 * |s.im| := by
      have : z.im = 2 * s.im := by simp [hzdef]
      rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hpow1 : (1 : ℝ) ≤ |s.im| ^ 7 := one_le_pow₀ hsim
    rcases le_or_gt |z.im| 10 with hsmall | hbig
    · calc ‖(riemannZeta z)⁻¹‖ ≤ M₁ := hM₁ z ⟨⟨hzre1, hzre2⟩, by linarith, hsmall⟩
        _ ≤ max (max M₁ 0) (C₁ * 2 ^ 7) * 1 := by
            rw [mul_one]; exact (le_max_left M₁ 0).trans (le_max_left _ _)
        _ ≤ max (max M₁ 0) (C₁ * 2 ^ 7) * |s.im| ^ 7 :=
            mul_le_mul_of_nonneg_left hpow1 (by positivity)
    · have hz_eq : z = (z.re : ℂ) + (z.im : ℂ) * I := by apply Complex.ext <;> simp
      have hb := hζ_log z.re z.im hzre1 hzre2 (by linarith)
      rw [DirichletCharacter.LFunction_modOne_eq, ← hz_eq] at hb
      have hlog_id : Real.log |z.im| ≤ 2 * |s.im| := by
        rw [← hzim]
        exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      have hlog : Real.log |z.im| ^ 7 ≤ (2 * |s.im|) ^ 7 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog_id 7
      calc ‖(riemannZeta z)⁻¹‖ ≤ C₁ * Real.log |z.im| ^ 7 := hb
        _ ≤ C₁ * (2 * |s.im|) ^ 7 := mul_le_mul_of_nonneg_left hlog hC₁.le
        _ = (C₁ * 2 ^ 7) * |s.im| ^ 7 := by ring
        _ ≤ max (max M₁ 0) (C₁ * 2 ^ 7) * |s.im| ^ 7 :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  obtain ⟨CQ, NQ, hCQ, hQ⟩ := exists_norm_scatterQ_le (by positivity) hζ_shift
  obtain ⟨Ca, _, hrap⟩ := h.rapidAmplitude.decay (3 / 8) (NQ + 2)
  set Kbox : Set ℂ := Icc (0 : ℝ) (3 / 8) ×ℂ Icc (-1 : ℝ) 1
  have hKbox : IsCompact Kbox := isCompact_Icc.reProdIm isCompact_Icc
  have hcontK : ContinuousOn (fun w =>
      pulseAmplitude h (-I * w) * PositiveEulerHorizon.scatteringPhase q (r + u) w) Kbox := by
    intro w hw
    have hw' := Complex.mem_reProdIm.1 hw
    have hne : w ≠ 1 / 2 := fun he => by have := hw'.1.2; rw [he] at this; norm_num at this
    exact (((h.differentiable_amplitude _).comp w (by fun_prop)).mul
      (differentiableAt_twinScatteringPhase (by omega) hne
        (PositiveEulerHorizon.completedXi_den_ne_zero hq hr hu hru hw'.1.1))).continuousAt.continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := hKbox.exists_bound_of_continuousOn hcontK
  refine ⟨max (2 * max B₀ 0) (CQ * Ca), by positivity, fun w hw1 hw2 => ?_⟩
  by_cases hut : 1 ≤ |w.im|
  · have hφw : ‖PositiveEulerHorizon.scatteringPhase q (r + u) w‖ ≤ CQ * |w.im| ^ NQ := by
      rw [PositiveEulerHorizon.scatteringPhase_eq_gate_mul (by omega), norm_mul]
      have hmod : modularScatteringPhase w = ((2 : ℂ) / (2 * w - 1)) * scatterQ (w + 1 / 2) := by
        unfold modularScatteringPhase scatterQ
        rw [show 2 * (w + 1 / 2) - 1 = 2 * w by ring, show 2 * (w + 1 / 2) = 1 + 2 * w by ring]
        ring
      rw [hmod, norm_mul]
      have h2le : ‖(2 : ℂ) / (2 * w - 1)‖ ≤ 1 := by
        have him2 : (2 : ℝ) ≤ |(2 * w - 1).im| := by simp; linarith
        have hn2 : (2 : ℝ) ≤ ‖2 * w - 1‖ := him2.trans (Complex.abs_im_le_norm _)
        rw [norm_div, Complex.norm_ofNat, div_le_one (by linarith)]
        exact hn2
      have hQb : ‖scatterQ (w + 1 / 2)‖ ≤ CQ * |w.im| ^ NQ := by
        simpa using hQ (w + 1 / 2) (by simp; linarith) (by simp; linarith) (by simpa using hut)
      calc ‖PositiveEulerHorizon.gate q (r + u) w‖ * (‖(2 : ℂ) / (2 * w - 1)‖ * ‖scatterQ (w + 1 / 2)‖)
          ≤ 1 * (1 * (CQ * |w.im| ^ NQ)) :=
            mul_le_mul (PositiveEulerHorizon.norm_gate_le_one hq hr hu hru hw1)
              (mul_le_mul h2le hQb (norm_nonneg _) (by positivity)) (by positivity) zero_le_one
        _ = CQ * |w.im| ^ NQ := by ring
    have hw_re : (-I * w).re = w.im := by simp
    have hw_im : (-I * w).im = -w.re := by simp
    have ha := hrap (-I * w) (by rw [hw_im, abs_neg, abs_le]; exact ⟨by linarith, hw2⟩)
    rw [hw_re] at ha
    have ht1 : |w.im| ^ NQ ≤ (1 + |w.im|) ^ NQ := pow_le_pow_left₀ (abs_nonneg _) (by linarith) NQ
    have ht2 : 1 + w.im ^ 2 ≤ (1 + |w.im|) ^ 2 := by nlinarith [abs_nonneg w.im, sq_abs w.im]
    rw [le_div_iff₀ (by positivity), norm_mul]
    calc ‖pulseAmplitude h (-I * w)‖ * ‖PositiveEulerHorizon.scatteringPhase q (r + u) w‖ * (1 + w.im ^ 2)
        ≤ ‖pulseAmplitude h (-I * w)‖ * (CQ * (1 + |w.im|) ^ NQ) * (1 + |w.im|) ^ 2 := by
          gcongr; exact hφw.trans (mul_le_mul_of_nonneg_left ht1 hCQ)
      _ = CQ * (‖pulseAmplitude h (-I * w)‖ * (1 + |w.im|) ^ (NQ + 2)) := by ring
      _ ≤ CQ * Ca := mul_le_mul_of_nonneg_left ha hCQ
      _ ≤ max (2 * max B₀ 0) (CQ * Ca) := le_max_right _ _
  · have hut' := abs_le.1 (not_le.1 hut).le
    have hb := hB₀ w (Complex.mem_reProdIm.2 ⟨⟨hw1, hw2⟩, hut'⟩)
    have hsq : w.im ^ 2 ≤ 1 := by nlinarith
    rw [le_div_iff₀ (by positivity)]
    calc ‖pulseAmplitude h (-I * w) * PositiveEulerHorizon.scatteringPhase q (r + u) w‖ * (1 + w.im ^ 2)
        ≤ max B₀ 0 * 2 := mul_le_mul (hb.trans (le_max_left _ _)) (by linarith) (by positivity)
          (le_max_right _ _)
      _ ≤ max (2 * max B₀ 0) (CQ * Ca) := by linarith [le_max_left (2 * max B₀ 0) (CQ * Ca)]

private theorem twin_bilateral_laplace_eq {q : ℕ} (hq : 1 < q) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = q)
    (h : CompactPulse) {w : ℂ} (hw1 : 1 / 8 < w.re) (hw2 : w.re < 5 / 16) :
    (∫ τ in Ioi (0 : ℝ), Complex.exp (-w * (τ : ℂ)) * twinReflected q (r + u) h τ) +
      (∫ σ in Ioi (0 : ℝ), Complex.exp (w * (σ : ℂ)) * twinReflected q (r + u) h (-σ)) =
      2 * Real.pi * pulseAmplitude h (-I * w) *
        PositiveEulerHorizon.scatteringPhase q (r + u) w := by
  set c : ℝ := w.re
  set η : ℝ := w.im
  have hc0 : 0 ≤ c := by linarith
  have hc1 : c ≤ 3 / 8 := by linarith
  have hw_eq : w = (c : ℂ) + (η : ℂ) * I := by apply Complex.ext <;> simp [c, η]
  obtain ⟨B, _, hB⟩ := exists_amplitude_twin_right_le hq hr hu hru h
  have hGc : Continuous (twinReflected q (r + u) h) :=
    continuous_unitaryReflected (continuous_scatteringPhase_twin_line hq hr hu hru).measurable
      (fun ξ => (PositiveEulerHorizon.norm_scatteringPhase_axis hq hr hu hru ξ).le) h
  have hint_a : Integrable fun ξ : ℝ => ‖pulseAmplitude h (ξ : ℂ)‖ :=
    ((h.integrable_amplitude_line 0).norm).congr (Eventually.of_forall fun _ => by simp)
  set M₀ : ℝ := ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖
  have hGb : ∀ τ : ℝ, ‖twinReflected q (r + u) h τ‖ ≤ M₀ := by
    intro τ
    rw [twinReflected, unitaryReflected]
    refine norm_integral_le_of_norm_le hint_a (Eventually.of_forall fun ξ => le_of_eq ?_)
    rw [norm_mul, norm_mul, PositiveEulerHorizon.norm_scatteringPhase_axis hq hr hu hru ξ,
      mul_one, norm_exp_I_mul, mul_one]
  have hshift_line : ∀ d : ℝ, 0 ≤ d → d ≤ 3 / 8 → ∀ τ : ℝ,
      twinReflected q (r + u) h τ = ∫ t : ℝ,
        pulseAmplitude h (-I * ((d : ℂ) + (t : ℂ) * I)) *
          PositiveEulerHorizon.scatteringPhase q (r + u) ((d : ℂ) + (t : ℂ) * I) *
          Complex.exp (((d : ℂ) + (t : ℂ) * I) * (τ : ℂ)) := by
    intro d hd0 hd1 τ
    set Φ : ℂ → ℂ := fun z => pulseAmplitude h (-I * z) *
      PositiveEulerHorizon.scatteringPhase q (r + u) z * Complex.exp (z * (τ : ℂ)) with hΦ
    have hstrip : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) d → 0 ≤ s.re ∧ s.re ≤ 3 / 8 := by
      intro s hs; rw [uIcc_of_le hd0] at hs; exact ⟨hs.1, hs.2.trans hd1⟩
    have hdΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) d → DifferentiableAt ℂ Φ s := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := hstrip s hs
      have hne : s ≠ 1 / 2 := fun he => by rw [he] at hs2; norm_num at hs2
      exact ((((h.differentiable_amplitude _).comp s (by fun_prop)).mul
        (differentiableAt_twinScatteringPhase (by omega) hne
          (PositiveEulerHorizon.completedXi_den_ne_zero hq hr hu hru hs1))).mul (by fun_prop))
    have hbΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) d →
        ‖Φ s‖ ≤ (B * Real.exp ((3 / 8) * |τ|)) / (1 + s.im ^ 2) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := hstrip s hs
      have hexp : ‖Complex.exp (s * (τ : ℂ))‖ ≤ Real.exp ((3 / 8) * |τ|) := by
        rw [Complex.norm_exp]
        have hre : (s * (τ : ℂ)).re = s.re * τ := by simp
        rw [hre]
        refine Real.exp_le_exp.mpr ?_
        calc s.re * τ ≤ |s.re * τ| := le_abs_self _
          _ = |s.re| * |τ| := abs_mul _ _
          _ ≤ (3 / 8) * |τ| := mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg hs1]; exact hs2)
              (abs_nonneg _)
      simp only [hΦ]; rw [norm_mul]
      calc ‖pulseAmplitude h (-I * s) * PositiveEulerHorizon.scatteringPhase q (r + u) s‖ *
              ‖Complex.exp (s * (τ : ℂ))‖
          ≤ (B / (1 + s.im ^ 2)) * Real.exp ((3 / 8) * |τ|) :=
            mul_le_mul (hB s hs1 hs2) hexp (norm_nonneg _) (by positivity)
        _ = (B * Real.exp ((3 / 8) * |τ|)) / (1 + s.im ^ 2) := by ring
    have h0_eq : twinReflected q (r + u) h τ = ∫ t : ℝ, Φ (((0 : ℝ) : ℂ) + (t : ℂ) * I) := by
      rw [twinReflected, unitaryReflected]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hΦ]
      have e : ((0 : ℝ) : ℂ) + (t : ℂ) * I = (t : ℂ) * I := by simp
      rw [e, show -I * ((t : ℂ) * I) = (t : ℂ) by linear_combination (-(t : ℂ)) * I_sq]
      congr 2; ring
    rw [h0_eq]
    exact integral_vertical_line_shift_of_decay hdΦ hbΦ
  have hGe : ∀ τ : ℝ, τ ≤ 0 → ‖twinReflected q (r + u) h τ‖ ≤ B * Real.pi * Real.exp ((3 / 8) * τ) := by
    intro τ _
    rw [hshift_line (3 / 8) (by norm_num) le_rfl τ]
    have hpt : ∀ t : ℝ,
        ‖pulseAmplitude h (-I * (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I)) *
          PositiveEulerHorizon.scatteringPhase q (r + u) (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) *
          Complex.exp ((((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) * (τ : ℂ))‖ ≤
        B * (1 + t ^ 2)⁻¹ * Real.exp ((3 / 8) * τ) := by
      intro t
      rw [norm_mul, Complex.norm_exp]
      have hre_exp : ((((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) * (τ : ℂ)).re = (3 / 8) * τ := by simp
      rw [hre_exp]
      have hb := hB (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) (by simp; norm_num) (by simp)
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    calc ‖∫ t : ℝ, _‖ ≤ ∫ t : ℝ, B * (1 + t ^ 2)⁻¹ * Real.exp ((3 / 8) * τ) :=
          norm_integral_le_of_norm_le ((integrable_inv_one_add_sq.const_mul B).mul_const _)
            (Eventually.of_forall hpt)
      _ = B * Real.pi * Real.exp ((3 / 8) * τ) := by
          rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]
  set f : ℝ → ℂ := fun t => pulseAmplitude h (-I * ((c : ℂ) + (t : ℂ) * I)) *
    PositiveEulerHorizon.scatteringPhase q (r + u) ((c : ℂ) + (t : ℂ) * I) with hf_def
  have hf_cont : Continuous f := by
    refine (h.differentiable_amplitude.continuous.comp (by fun_prop)).mul ?_
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hne : ((c : ℂ) + (t : ℂ) * I) ≠ 1 / 2 := fun he => by
      have := congrArg Complex.re he; simp at this; linarith
    exact ContinuousAt.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * I)
      (differentiableAt_twinScatteringPhase (by omega) hne
        (PositiveEulerHorizon.completedXi_den_ne_zero hq hr hu hru (by simp [hc0]))).continuousAt
      (by fun_prop)
  have hf_int : Integrable f := by
    refine (integrable_inv_one_add_sq.const_mul B).mono' hf_cont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    simpa [hf_def, div_eq_mul_inv] using hB ((c : ℂ) + (t : ℂ) * I) (by simp [hc0]) (by simp [hc1])
  set g : ℝ → ℂ := fun τ => Complex.exp (-(c : ℂ) * (τ : ℂ)) * twinReflected q (r + u) h τ with hg_def
  have hg_cont : Continuous g := (by fun_prop : Continuous fun τ : ℝ =>
    Complex.exp (-(c : ℂ) * (τ : ℂ))).mul hGc
  have hg_pos : IntegrableOn g (Ioi (0 : ℝ)) := by
    refine ((integrableOn_exp_mul_Ioi (by linarith : -c < 0) 0).const_mul M₀).mono'
      hg_cont.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun τ _ => ?_))
    simp only [hg_def]
    rw [norm_mul, Complex.norm_exp, show (-(c : ℂ) * (τ : ℂ)).re = -c * τ by simp, mul_comm]
    exact mul_le_mul_of_nonneg_right (hGb τ) (Real.exp_pos _).le
  have hg_neg : IntegrableOn g (Iic (0 : ℝ)) := by
    have hdom_i : IntegrableOn (fun σ : ℝ => B * Real.pi * Real.exp (-(3 / 8 - c) * σ)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul (B * Real.pi)
    have hdom : IntegrableOn (fun τ : ℝ => B * Real.pi * Real.exp ((3 / 8 - c) * τ)) (Iic 0) := by
      rw [← integrable_indicator_iff measurableSet_Iic]
      have h1' := (integrable_indicator_iff measurableSet_Ioi).mpr hdom_i
      refine (h1'.comp_neg).congr ?_
      have hae : ∀ᵐ τ : ℝ, τ ≠ 0 := by
        rw [ae_iff]
        have hset : {τ : ℝ | ¬ τ ≠ 0} = ({0} : Set ℝ) := by ext τ; simp
        rw [hset]; exact measure_singleton 0
      refine hae.mono fun τ hτ => ?_
      dsimp only
      rcases lt_or_gt_of_ne hτ with hlt | hgt
      · rw [indicator_of_mem (show -τ ∈ Ioi (0 : ℝ) by simp; linarith),
          indicator_of_mem (show τ ∈ Iic (0 : ℝ) from hlt.le)]
        ring_nf
      · rw [indicator_of_notMem (show -τ ∉ Ioi (0 : ℝ) by simp; linarith),
          indicator_of_notMem (show τ ∉ Iic (0 : ℝ) by simp; linarith)]
    refine hdom.mono' hg_cont.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun τ hτ => ?_))
    simp only [hg_def]
    rw [norm_mul, Complex.norm_exp, show (-(c : ℂ) * (τ : ℂ)).re = -c * τ by simp]
    calc Real.exp (-c * τ) * ‖twinReflected q (r + u) h τ‖
        ≤ Real.exp (-c * τ) * (B * Real.pi * Real.exp ((3 / 8) * τ)) :=
          mul_le_mul_of_nonneg_left (hGe τ hτ) (Real.exp_pos _).le
      _ = B * Real.pi * Real.exp ((3 / 8 - c) * τ) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hg_int : Integrable g := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact hg_neg.union hg_pos
  have hpi0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi0
  set F : ℝ → ℂ := fun v => (2 * Real.pi : ℂ) * f (2 * Real.pi * v) with hF_def
  have hF_cont : Continuous F := continuous_const.mul (hf_cont.comp (by fun_prop))
  have hF_int : Integrable F := (hf_int.comp_mul_left' hpi0).const_mul (2 * Real.pi : ℂ)
  have hFinv_eq : 𝓕⁻ F = g := by
    funext τ
    rw [fourierInv_eq_integral_exp]
    have hg_sub := Measure.integral_comp_mul_left
      (fun y : ℝ => f y * Complex.exp (I * (y : ℂ) * (τ : ℂ))) (2 * Real.pi)
    have habs : |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := abs_of_pos (by positivity)
    rw [habs, Complex.real_smul] at hg_sub
    have hrw : ∀ v : ℝ, Complex.exp (((2 * Real.pi * v * τ : ℝ)) * I) • F v =
        (2 * Real.pi : ℂ) * (f (2 * Real.pi * v) *
          Complex.exp (I * ((2 * Real.pi * v : ℝ) : ℂ) * (τ : ℂ))) := by
      intro v
      simp only [hF_def, smul_eq_mul]
      have he : Complex.exp (((2 * Real.pi * v * τ : ℝ)) * I) =
          Complex.exp (I * ((2 * Real.pi * v : ℝ) : ℂ) * (τ : ℂ)) := by
        congr 1; push_cast; ring
      rw [he]; ring
    simp_rw [hrw]
    rw [integral_const_mul, hg_sub]
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
    simp only [hg_def]
    rw [hshift_line c hc0 hc1 τ, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hf_def]
    have he : Complex.exp (((c : ℂ) + (y : ℂ) * I) * (τ : ℂ)) =
        Complex.exp ((c : ℂ) * (τ : ℂ)) * Complex.exp (I * (y : ℂ) * (τ : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    have hc_cancel : Complex.exp (-(c : ℂ) * (τ : ℂ)) * Complex.exp ((c : ℂ) * (τ : ℂ)) = 1 := by
      rw [← Complex.exp_add]
      have : -(c : ℂ) * (τ : ℂ) + (c : ℂ) * (τ : ℂ) = 0 := by ring
      rw [this, Complex.exp_zero]
    rw [he]
    linear_combination (f y * Complex.exp (I * (y : ℂ) * (τ : ℂ))) * (-hc_cancel)
  have hFF_int : Integrable (𝓕 F) := by
    have hFF_eq : 𝓕 F = fun x => g (-x) := funext fun x => by
      have h1' := Real.fourierInv_eq_fourier_neg F (-x)
      rw [neg_neg, hFinv_eq] at h1'
      exact h1'.symm
    rw [hFF_eq]; exact hg_int.comp_neg
  have hinv := hF_cont.fourier_fourierInv_eq hF_int hFF_int
  rw [hFinv_eq] at hinv
  have hval := congrFun hinv (η / (2 * Real.pi))
  rw [Real.fourier_real_eq_integral_exp_smul] at hval
  have hF_eval : F (η / (2 * Real.pi)) =
      2 * Real.pi * pulseAmplitude h (-I * w) *
        PositiveEulerHorizon.scatteringPhase q (r + u) w := by
    simp only [hF_def, hf_def]
    rw [mul_div_cancel₀ _ hpi0, ← hw_eq]; ring
  set H : ℝ → ℂ := fun τ => Complex.exp (-w * (τ : ℂ)) * twinReflected q (r + u) h τ with hH_def
  have hH_eq : ∀ τ : ℝ,
      Complex.exp ((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) * I) • g τ = H τ := by
    intro τ
    simp only [smul_eq_mul, hg_def, hH_def]
    have hexp : Complex.exp ((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) * I) *
        Complex.exp (-(c : ℂ) * (τ : ℂ)) = Complex.exp (-w * (τ : ℂ)) := by
      rw [← Complex.exp_add]; congr 1
      have hdiv : -2 * Real.pi * τ * (η / (2 * Real.pi)) = -η * τ := by field_simp
      rw [hdiv, hw_eq]; push_cast; ring
    rw [← mul_assoc, hexp]
  have hH_int : Integrable H := by
    refine (hg_int.norm).mono' ((by fun_prop : Continuous fun τ : ℝ =>
      Complex.exp (-w * (τ : ℂ))).mul hGc).aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [← hH_eq τ, smul_eq_mul, norm_mul, Complex.norm_exp]
    have hre : (((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) : ℂ) * I).re = 0 := by
      generalize -2 * Real.pi * τ * (η / (2 * Real.pi)) = t; simp
    rw [hre, Real.exp_zero, one_mul]
  have hsplit : (∫ τ in Ioi (0 : ℝ), H τ) + (∫ τ in Iic (0 : ℝ), H τ) = ∫ τ : ℝ, H τ := by
    have h1' := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hH_int
    rwa [compl_Ioi] at h1'
  have hneg_eq : (∫ τ in Iic (0 : ℝ), H τ) =
      ∫ σ in Ioi (0 : ℝ), Complex.exp (w * (σ : ℂ)) * twinReflected q (r + u) h (-σ) := by
    rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Ioi,
      ← integral_neg_eq_self]
    have hae : ∀ᵐ σ : ℝ, σ ≠ 0 := by
      rw [ae_iff]
      have hset : {σ : ℝ | ¬ σ ≠ 0} = ({0} : Set ℝ) := by ext σ; simp
      rw [hset]; exact measure_singleton 0
    refine integral_congr_ae (hae.mono fun σ hσ => ?_)
    dsimp only
    rcases lt_or_gt_of_ne hσ with hlt | hgt
    · rw [indicator_of_notMem (show -σ ∉ Iic (0 : ℝ) by simp; linarith),
        indicator_of_notMem (show σ ∉ Ioi (0 : ℝ) by simp; linarith)]
    · rw [indicator_of_mem (show -σ ∈ Iic (0 : ℝ) by simp; linarith),
        indicator_of_mem (show σ ∈ Ioi (0 : ℝ) from hgt)]
      simp only [hH_def]; push_cast; ring_nf
  rw [← hneg_eq, hsplit]
  calc ∫ τ : ℝ, H τ
      = ∫ τ : ℝ, Complex.exp ((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) * I) • g τ :=
        integral_congr_ae (Eventually.of_forall fun τ => (hH_eq τ).symm)
    _ = F (η / (2 * Real.pi)) := hval
    _ = 2 * Real.pi * pulseAmplitude h (-I * w) *
          PositiveEulerHorizon.scatteringPhase q (r + u) w := hF_eval

/-- **Sub-Threshold Ringdown of `PositiveEulerHorizon`.** Below `min(3001/48000, (1 - σ)/2)`, every
compact pulse `h` decays as `O(e^{-η τ})` on `twinReflected q (q^σ + q^{1-σ}) h`. -/
theorem twinReflected_decay_lt {q : ℕ} (hq : 1 < q) {σ η : ℝ}
    (h0 : 1 / 2 < σ) (h1 : σ < 1) (hη0 : 0 < η)
    (hη_ζ : η < 3001 / 48000) (hη_σ : η < (1 - σ) / 2) (h : CompactPulse) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
      ‖twinReflected q ((q : ℝ) ^ σ + (q : ℝ) ^ (1 - σ)) h τ‖ ≤ C * Real.exp (-η * τ) := by
  have _ := h1
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hqR
  set r : ℝ := (q : ℝ) ^ σ
  set u : ℝ := (q : ℝ) ^ (1 - σ)
  have hr : 1 < r := Real.one_lt_rpow hqR (by linarith)
  have hu : 1 < u := Real.one_lt_rpow hqR (by linarith [h1])
  have hur : u < r := Real.rpow_lt_rpow_of_exponent_lt hqR (by linarith)
  have hru : r * u = q := by
    dsimp only [r, u]
    rw [← Real.rpow_add hq0, show σ + (1 - σ) = 1 by ring, Real.rpow_one]
  set gap : ℝ := u - (q : ℝ) ^ (2 * η)
  have hgap : 0 < gap := by
    have hlt : (q : ℝ) ^ (2 * η) < u :=
      Real.rpow_lt_rpow_of_exponent_lt hqR (by linarith)
    linarith
  set KG : ℝ := ((1 + r * u) * (1 + u * u)) / (gap * gap)
  have hKG0 : 0 ≤ KG := by positivity
  have hgate_left : ∀ w : ℂ, -η ≤ w.re → w.re ≤ 0 →
      ‖PositiveEulerHorizon.gate q (r + u) w‖ ≤ KG ∧
        completedFactor q (r + u) (1 + 2 * w) ≠ 0 := by
    intro w hw1 _
    set v : ℂ := (q : ℂ) ^ (-2 * w)
    have hv_le : ‖v‖ ≤ (q : ℝ) ^ (2 * η) := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega), show (-2 * w).re = -2 * w.re by simp]
      exact Real.rpow_le_rpow_of_exponent_le hqR.le (by linarith)
    have hv_u : ‖v‖ ≤ u := hv_le.trans (by linarith)
    have hruR : ((q : ℝ) : ℂ) = (r : ℂ) * (u : ℂ) := by rw [← hru, Complex.ofReal_mul]
    have hnum_eq : schurNum q (-(r + u)) v = (1 + (r : ℂ) * v) * (1 + (u : ℂ) * v) := by
      simp only [schurNum, Complex.ofReal_neg, Complex.ofReal_add]; rw [hruR]; ring
    have hden_eq : schurDen q (-(r + u)) v = ((r : ℂ) + v) * ((u : ℂ) + v) := by
      simp only [schurDen, Complex.ofReal_neg, Complex.ofReal_add]; rw [hruR]; ring
    have hnum_ub : ‖schurNum q (-(r + u)) v‖ ≤ (1 + r * u) * (1 + u * u) := by
      rw [hnum_eq, norm_mul]
      have hb1 : ‖1 + (r : ℂ) * v‖ ≤ 1 + r * u := by
        calc ‖1 + (r : ℂ) * v‖ ≤ ‖(1 : ℂ)‖ + ‖(r : ℂ) * v‖ := norm_add_le _ _
          _ = 1 + r * ‖v‖ := by
              rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg (zero_lt_one.trans hr).le]
          _ ≤ 1 + r * u := by gcongr
      have hb2 : ‖1 + (u : ℂ) * v‖ ≤ 1 + u * u := by
        calc ‖1 + (u : ℂ) * v‖ ≤ ‖(1 : ℂ)‖ + ‖(u : ℂ) * v‖ := norm_add_le _ _
          _ = 1 + u * ‖v‖ := by
              rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg (zero_lt_one.trans hu).le]
          _ ≤ 1 + u * u := by gcongr
      exact mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
    have hden_lb : gap * gap ≤ ‖schurDen q (-(r + u)) v‖ := by
      rw [hden_eq, norm_mul]
      have hd1 : gap ≤ ‖(r : ℂ) + v‖ := by
        have hs := norm_sub_norm_le (r : ℂ) (-v)
        rw [sub_neg_eq_add, norm_neg, Complex.norm_real,
          Real.norm_of_nonneg (zero_lt_one.trans hr).le] at hs
        linarith
      have hd2 : gap ≤ ‖(u : ℂ) + v‖ := by
        have hs := norm_sub_norm_le (u : ℂ) (-v)
        rw [sub_neg_eq_add, norm_neg, Complex.norm_real,
          Real.norm_of_nonneg (zero_lt_one.trans hu).le] at hs
        linarith
      exact mul_le_mul hd1 hd2 hgap.le (by linarith)
    refine ⟨?_, ?_⟩
    · rw [PositiveEulerHorizon.gate, norm_div]
      exact div_le_div₀ (by positivity) hnum_ub (mul_pos hgap hgap) hden_lb
    · have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
      have hz : (q : ℂ) ^ (2 * w) ≠ 0 := cpow_ne_zero_iff.mpr (.inl hqC)
      have hd : completedFactor q (r + u) (1 + 2 * w) =
          (q : ℂ) ^ (2 * w) * schurDen q (-(r + u)) v := by
        rw [completedFactor, cpow_add _ _ hqC, cpow_one,
          show (1 : ℂ) - (1 + 2 * w) = -(2 * w) by ring,
          show v = (q : ℂ) ^ (-(2 * w)) by dsimp only [v]; ring_nf, cpow_neg, schurDen]
        push_cast; field_simp [hz]; ring
      rw [hd]
      exact mul_ne_zero hz (norm_ne_zero_iff.mp (by linarith [mul_pos hgap hgap]))
  have hz_ζ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re ≤ 1 - 2 * (3001 / 48000 : ℝ) := by
    intro ρ h0' hpos
    have hmem := riemannZeta_zero_mem_sub_quasiRH_strip hpos h0'
    linarith [hmem.2]
  set Θ : ℝ := 1 - 2 * (3001 / 48000 : ℝ)
  have hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0 := fun z hz' h0' => by
    have := hz_ζ z h0' (by dsimp only [Θ] at hz'; linarith); linarith
  obtain ⟨κ, hκ, hζ⟩ := exists_zeta_lower_bound_subpolynomial_of_zeroFree (Θ := Θ) (by norm_num)
    (by norm_num) hzf (δ := 2 * (3001 / 48000 - η)) (by linarith)
    (by linarith) (ε := 1) one_pos
  set boxU : Set ℂ := {w : ℂ | (-η ≤ w.re ∧ w.re ≤ 0) ∧ 1 ≤ |w.im| ∧ |w.im| ≤ 3}
  have hboxU_c : IsCompact boxU := by
    have heq : boxU = ((Icc (-η) 0) ×ℂ (Icc (-3 : ℝ) 3)) ∩ {w : ℂ | 1 ≤ |w.im|} := by
      ext w
      simp only [boxU, mem_inter_iff, Complex.mem_reProdIm, mem_Icc, mem_setOf_eq, abs_le]
      tauto
    rw [heq]
    exact (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im))
  have hcont_ζU : ContinuousOn (fun w : ℂ => (riemannZeta (1 + 2 * w))⁻¹) boxU := by
    intro w hw
    have hne1 : 1 + 2 * w ≠ 1 := fun he => by
      have him0 := congrArg Complex.im he; simp at him0
      have := hw.2.1; rw [him0, abs_zero] at this; linarith
    have hz0 : riemannZeta (1 + 2 * w) ≠ 0 := hzf _ (by simp [Θ]; linarith [hw.1.1])
    exact ((ContinuousAt.comp (f := fun v : ℂ => 1 + 2 * v)
      (differentiableAt_riemannZeta hne1).continuousAt (by fun_prop)).inv₀ hz0).continuousWithinAt
  obtain ⟨Mζ, hMζ⟩ := hboxU_c.exists_bound_of_continuousOn hcont_ζU
  have hζ_shift : ∀ s : ℂ, -η + 1 / 2 ≤ s.re → s.re ≤ 1 / 2 → 1 ≤ |s.im| →
      ‖(riemannZeta (2 * s))⁻¹‖ ≤ (max (max Mζ 0) (4 / κ)) * |s.im| ^ 1 := by
    intro s hs1 hs2 hsim
    set w : ℂ := s - 1 / 2
    have hw_eq : 1 + 2 * w = 2 * s := by simp [w]; ring
    have hw1 : -η ≤ w.re := by simp [w]; linarith
    have hw2 : w.re ≤ 0 := by simp [w]; linarith
    have hwim : |w.im| = |s.im| := by simp [w]
    rw [← hw_eq, ← hwim]
    have hpow1 : (1 : ℝ) ≤ |w.im| ^ 1 := by simpa [hwim] using hsim
    rcases le_or_gt |w.im| 3 with hsmall | hbig
    · calc ‖(riemannZeta (1 + 2 * w))⁻¹‖
          ≤ Mζ := hMζ w ⟨⟨hw1, hw2⟩, by rwa [hwim], hsmall⟩
        _ ≤ max (max Mζ 0) (4 / κ) * 1 := by
            rw [mul_one]; exact (le_max_left Mζ 0).trans (le_max_left _ _)
        _ ≤ max (max Mζ 0) (4 / κ) * |w.im| ^ 1 :=
            mul_le_mul_of_nonneg_left hpow1 (by positivity)
    · have him : |(1 + 2 * w).im| = 2 * |w.im| := by
        have : (1 + 2 * w).im = 2 * w.im := by simp
        rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hb := hζ (1 + 2 * w) (by simp [Θ]; linarith) (by rw [him]; linarith)
      rw [Real.rpow_neg_one, him] at hb
      have hpos : 0 < ‖riemannZeta (1 + 2 * w)‖ := lt_of_lt_of_le (by positivity) hb
      rw [norm_inv, inv_le_comm₀ hpos (by positivity)]
      have h2t : 2 + 2 * |w.im| ≤ 4 * |w.im| := by linarith
      calc (max (max Mζ 0) (4 / κ) * |w.im| ^ 1)⁻¹
          ≤ ((4 / κ) * |w.im|)⁻¹ := by
            rw [pow_one]
            exact inv_anti₀ (by positivity)
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
        _ = κ * (4 * |w.im|)⁻¹ := by field_simp
        _ ≤ κ * (2 + 2 * |w.im|)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h2t) hκ.le
        _ ≤ ‖riemannZeta (1 + 2 * w)‖ := hb
  obtain ⟨CQ, NQ, hCQ, hQ⟩ := exists_norm_scatterQ_le (by positivity) hζ_shift
  obtain ⟨Ca, _, hrap⟩ := h.rapidAmplitude.decay η (NQ + 2)
  have hxi_left : ∀ w : ℂ, -η ≤ w.re → w.re ≤ 0 →
      PositiveEulerHorizon.completedXi q (r + u) (1 + 2 * w) ≠ 0 := by
    intro w hw1 hw2
    exact mul_ne_zero (hgate_left w hw1 hw2).2
      (RingdownRate.xi_ne_zero_of_zeroFree (δ := 3001 / 48000) (by norm_num) hη_ζ hz_ζ hw1)
  set Kbox : Set ℂ := Icc (-η) 0 ×ℂ Icc (-1 : ℝ) 1
  have hKbox : IsCompact Kbox := isCompact_Icc.reProdIm isCompact_Icc
  have hcontK : ContinuousOn (fun w =>
      pulseAmplitude h (-I * w) * PositiveEulerHorizon.scatteringPhase q (r + u) w) Kbox := by
    intro w hw
    have hw12 := Complex.mem_reProdIm.1 hw
    have hne : w ≠ 1 / 2 := fun he => by have := hw12.1.2; rw [he] at this; norm_num at this
    exact (((h.differentiable_amplitude _).comp w (by fun_prop)).mul
      (differentiableAt_twinScatteringPhase (by omega) hne
        (hxi_left w hw12.1.1 hw12.1.2))).continuousAt.continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := hKbox.exists_bound_of_continuousOn hcontK
  set B : ℝ := max (2 * max B₀ 0) ((KG * CQ) * Ca)
  have hB_left : ∀ w : ℂ, -η ≤ w.re → w.re ≤ 0 →
      ‖pulseAmplitude h (-I * w) * PositiveEulerHorizon.scatteringPhase q (r + u) w‖ ≤
        B / (1 + w.im ^ 2) := by
    intro w hw1 hw2
    by_cases hut : 1 ≤ |w.im|
    · have hφw : ‖PositiveEulerHorizon.scatteringPhase q (r + u) w‖ ≤ (KG * CQ) * |w.im| ^ NQ := by
        rw [PositiveEulerHorizon.scatteringPhase_eq_gate_mul (by omega), norm_mul]
        have hmod : modularScatteringPhase w = ((2 : ℂ) / (2 * w - 1)) * scatterQ (w + 1 / 2) := by
          unfold modularScatteringPhase scatterQ
          rw [show 2 * (w + 1 / 2) - 1 = 2 * w by ring, show 2 * (w + 1 / 2) = 1 + 2 * w by ring]
          ring
        rw [hmod, norm_mul]
        have h2le : ‖(2 : ℂ) / (2 * w - 1)‖ ≤ 1 := by
          have him2 : (2 : ℝ) ≤ |(2 * w - 1).im| := by simp; linarith
          have hn2 : (2 : ℝ) ≤ ‖2 * w - 1‖ := him2.trans (Complex.abs_im_le_norm _)
          rw [norm_div, Complex.norm_ofNat, div_le_one (by linarith)]
          exact hn2
        have hQb : ‖scatterQ (w + 1 / 2)‖ ≤ CQ * |w.im| ^ NQ := by
          simpa using hQ (w + 1 / 2) (by simp; linarith) (by simp; linarith) (by simpa using hut)
        calc ‖PositiveEulerHorizon.gate q (r + u) w‖ * (‖(2 : ℂ) / (2 * w - 1)‖ * ‖scatterQ (w + 1 / 2)‖)
            ≤ KG * (1 * (CQ * |w.im| ^ NQ)) :=
              mul_le_mul (hgate_left w hw1 hw2).1
                (mul_le_mul h2le hQb (norm_nonneg _) (by positivity)) (by positivity) hKG0
          _ = (KG * CQ) * |w.im| ^ NQ := by ring
      have hw_re : (-I * w).re = w.im := by simp
      have hw_im : (-I * w).im = -w.re := by simp
      have ha := hrap (-I * w) (by rw [hw_im, abs_neg, abs_le]; constructor <;> linarith)
      rw [hw_re] at ha
      have ht1 : |w.im| ^ NQ ≤ (1 + |w.im|) ^ NQ := pow_le_pow_left₀ (abs_nonneg _) (by linarith) NQ
      have ht2 : 1 + w.im ^ 2 ≤ (1 + |w.im|) ^ 2 := by nlinarith [abs_nonneg w.im, sq_abs w.im]
      rw [le_div_iff₀ (by positivity), norm_mul]
      calc ‖pulseAmplitude h (-I * w)‖ * ‖PositiveEulerHorizon.scatteringPhase q (r + u) w‖ * (1 + w.im ^ 2)
          ≤ ‖pulseAmplitude h (-I * w)‖ * ((KG * CQ) * (1 + |w.im|) ^ NQ) * (1 + |w.im|) ^ 2 := by
            gcongr; exact hφw.trans (mul_le_mul_of_nonneg_left ht1 (by positivity))
        _ = (KG * CQ) * (‖pulseAmplitude h (-I * w)‖ * (1 + |w.im|) ^ (NQ + 2)) := by ring
        _ ≤ (KG * CQ) * Ca := mul_le_mul_of_nonneg_left ha (by positivity)
        _ ≤ B := le_max_right _ _
    · have hut' := abs_le.1 (not_le.1 hut).le
      have hb := hB₀ w (Complex.mem_reProdIm.2 ⟨⟨hw1, hw2⟩, hut'⟩)
      have hsq : w.im ^ 2 ≤ 1 := by nlinarith
      rw [le_div_iff₀ (by positivity)]
      calc ‖pulseAmplitude h (-I * w) * PositiveEulerHorizon.scatteringPhase q (r + u) w‖ * (1 + w.im ^ 2)
          ≤ max B₀ 0 * 2 := mul_le_mul (hb.trans (le_max_left _ _)) (by linarith) (by positivity)
            (le_max_right _ _)
        _ ≤ B := by linarith [le_max_left (2 * max B₀ 0) ((KG * CQ) * Ca)]
  refine ⟨B * Real.pi, by positivity, fun τ hτ => ?_⟩
  set Φ : ℂ → ℂ := fun w => pulseAmplitude h (-I * w) *
    PositiveEulerHorizon.scatteringPhase q (r + u) w * Complex.exp (w * (τ : ℂ)) with hΦ
  have hstrip : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-η) → -η ≤ s.re ∧ s.re ≤ 0 := by
    intro s hs; rw [uIcc_of_ge (by linarith)] at hs; exact hs
  have hd : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-η) → DifferentiableAt ℂ Φ s := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hstrip s hs
    have hne : s ≠ 1 / 2 := fun he => by rw [he] at hs2; norm_num at hs2
    exact ((((h.differentiable_amplitude _).comp s (by fun_prop)).mul
      (differentiableAt_twinScatteringPhase (by omega) hne (hxi_left s hs1 hs2))).mul (by fun_prop))
  have hbΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-η) → ‖Φ s‖ ≤ B / (1 + s.im ^ 2) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hstrip s hs
    have he : ‖Complex.exp (s * (τ : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp, show (s * (τ : ℂ)).re = s.re * τ by simp]
      exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hs2 hτ)
    simp only [hΦ]; rw [norm_mul]
    calc ‖pulseAmplitude h (-I * s) * PositiveEulerHorizon.scatteringPhase q (r + u) s‖ *
            ‖Complex.exp (s * (τ : ℂ))‖
        ≤ B / (1 + s.im ^ 2) * 1 := mul_le_mul (hB_left s hs1 hs2) he (norm_nonneg _) (by positivity)
      _ = B / (1 + s.im ^ 2) := mul_one _
  have hshift := integral_vertical_line_shift_of_decay hd hbΦ
  have hpk : twinReflected q (r + u) h τ = ∫ t : ℝ, Φ (((0 : ℝ) : ℂ) + (t : ℂ) * I) := by
    rw [twinReflected, unitaryReflected]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hΦ]
    have e : ((0 : ℝ) : ℂ) + (t : ℂ) * I = (t : ℂ) * I := by simp
    rw [e, show -I * ((t : ℂ) * I) = (t : ℂ) by linear_combination (-(t : ℂ)) * I_sq]
    congr 2; ring
  rw [hpk, hshift]
  have hpt : ∀ t : ℝ,
      ‖Φ (((-η : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ B * (1 + t ^ 2)⁻¹ * Real.exp (-η * τ) := by
    intro t
    simp only [hΦ]; rw [norm_mul, Complex.norm_exp]
    have : ((((-η : ℝ) : ℂ) + (t : ℂ) * I) * (τ : ℂ)).re = -η * τ := by simp
    rw [this]
    have hb := hB_left (((-η : ℝ) : ℂ) + (t : ℂ) * I) (by simp) (by simp; linarith)
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  calc ‖∫ t : ℝ, Φ (((-η : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ ∫ t : ℝ, B * (1 + t ^ 2)⁻¹ * Real.exp (-η * τ) :=
        norm_integral_le_of_norm_le ((integrable_inv_one_add_sq.const_mul B).mul_const _)
          (Eventually.of_forall hpt)
    _ = B * Real.pi * Real.exp (-η * τ) := by
        rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]

/-- **Strict Failure of Decay Above `(1 - σ) / 2` on `PositiveEulerHorizon`.** For any `q > 1`,
`1/2 < σ < 1` (`r = q^σ, u = q^{1-σ}`), and any `δ > (1 - σ) / 2`, the compactly supported smooth
pulse `excitingPulse ((factorZero q r - 1) / 2)` violates `O(e^{-δ τ})`. -/
theorem not_twinReflected_decay_gt {q : ℕ} (hq : 1 < q) {σ δ : ℝ}
    (h0 : 1 / 2 < σ) (h1 : σ < 1) (hδ : (1 - σ) / 2 < δ) :
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
      ‖twinReflected q ((q : ℝ) ^ σ + (q : ℝ) ^ (1 - σ))
        (excitingPulse ((factorZero q ((q : ℝ) ^ σ) - 1) / 2)) τ‖ ≤
        C * Real.exp (-δ * τ) := by
  rintro ⟨C₀, hC₀⟩
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hqR
  set r : ℝ := (q : ℝ) ^ σ
  set u : ℝ := (q : ℝ) ^ (1 - σ)
  have hr : 1 < r := Real.one_lt_rpow hqR (by linarith)
  have hu : 1 < u := Real.one_lt_rpow hqR (by linarith [h1])
  have hru : r * u = q := by
    dsimp only [r, u]
    rw [← Real.rpow_add hq0, show σ + (1 - σ) = 1 by ring, Real.rpow_one]
  set s₀ : ℂ := factorZero q r
  have hs₀_re : s₀.re = σ := by
    rw [factorZero_re, show Real.log r = σ * Real.log q from Real.log_rpow hq0 σ]
    exact mul_div_cancel_right₀ _ (Real.log_pos hqR).ne'
  set p : ℂ := (s₀ - 1) / 2 with hpdef
  set h := excitingPulse p
  have hp1 : 1 + 2 * p = s₀ := by rw [hpdef]; ring
  have hparam : reciprocalParameter q r = r + u := by
    rw [reciprocalParameter, (div_eq_iff (zero_lt_one.trans hr).ne').mpr (by rw [mul_comm, hru])]
  have hpxi : PositiveEulerHorizon.completedXi q (r + u) (1 + 2 * p) = 0 := by
    rw [hp1, PositiveEulerHorizon.completedXi, ← cpow_mul_localFactor (by omega),
      ← hparam, localFactor_factorZero hq (zero_lt_one.trans hr), mul_zero, zero_mul]
  have hpre : p.re = (σ - 1) / 2 := by rw [hpdef]; simp [hs₀_re]
  have hp_gt : -δ < p.re := by rw [hpre]; linarith
  have hGc : Continuous (twinReflected q (r + u) h) :=
    continuous_unitaryReflected (continuous_scatteringPhase_twin_line hq hr hu hru).measurable
      (fun ξ => (PositiveEulerHorizon.norm_scatteringPhase_axis hq hr hu hru ξ).le) h
  obtain ⟨B, _, hB⟩ := exists_amplitude_twin_right_le hq hr hu hru h
  have hGe : ∀ τ : ℝ, τ ≤ 0 → ‖twinReflected q (r + u) h τ‖ ≤ B * Real.pi * Real.exp ((3 / 8) * τ) := by
    intro τ _
    set Φ : ℂ → ℂ := fun z => pulseAmplitude h (-I * z) *
      PositiveEulerHorizon.scatteringPhase q (r + u) z * Complex.exp (z * (τ : ℂ)) with hΦ
    have hstrip : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (3 / 8) → 0 ≤ s.re ∧ s.re ≤ 3 / 8 := by
      intro s hs; rwa [uIcc_of_le (by norm_num)] at hs
    have hdΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (3 / 8) → DifferentiableAt ℂ Φ s := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := hstrip s hs
      have hne : s ≠ 1 / 2 := fun he => by rw [he] at hs2; norm_num at hs2
      exact ((((h.differentiable_amplitude _).comp s (by fun_prop)).mul
        (differentiableAt_twinScatteringPhase (by omega) hne
          (PositiveEulerHorizon.completedXi_den_ne_zero hq hr hu hru hs1))).mul (by fun_prop))
    have hbΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (3 / 8) →
        ‖Φ s‖ ≤ (B * Real.exp ((3 / 8) * |τ|)) / (1 + s.im ^ 2) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := hstrip s hs
      have hexp : ‖Complex.exp (s * (τ : ℂ))‖ ≤ Real.exp ((3 / 8) * |τ|) := by
        rw [Complex.norm_exp]
        have hre : (s * (τ : ℂ)).re = s.re * τ := by simp
        rw [hre]
        refine Real.exp_le_exp.mpr ?_
        calc s.re * τ ≤ |s.re * τ| := le_abs_self _
          _ = |s.re| * |τ| := abs_mul _ _
          _ ≤ (3 / 8) * |τ| := mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg hs1]; exact hs2)
              (abs_nonneg _)
      simp only [hΦ]; rw [norm_mul]
      calc ‖pulseAmplitude h (-I * s) * PositiveEulerHorizon.scatteringPhase q (r + u) s‖ *
              ‖Complex.exp (s * (τ : ℂ))‖
          ≤ (B / (1 + s.im ^ 2)) * Real.exp ((3 / 8) * |τ|) :=
            mul_le_mul (hB s hs1 hs2) hexp (norm_nonneg _) (by positivity)
        _ = (B * Real.exp ((3 / 8) * |τ|)) / (1 + s.im ^ 2) := by ring
    have h0_eq : twinReflected q (r + u) h τ = ∫ t : ℝ, Φ (((0 : ℝ) : ℂ) + (t : ℂ) * I) := by
      rw [twinReflected, unitaryReflected]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hΦ]
      have e : ((0 : ℝ) : ℂ) + (t : ℂ) * I = (t : ℂ) * I := by simp
      rw [e, show -I * ((t : ℂ) * I) = (t : ℂ) by linear_combination (-(t : ℂ)) * I_sq]
      congr 2; ring
    rw [h0_eq, integral_vertical_line_shift_of_decay hdΦ hbΦ]
    have hpt : ∀ t : ℝ, ‖Φ (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        B * (1 + t ^ 2)⁻¹ * Real.exp ((3 / 8) * τ) := by
      intro t
      simp only [hΦ]; rw [norm_mul, Complex.norm_exp]
      have hre_exp : ((((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) * (τ : ℂ)).re = (3 / 8) * τ := by simp
      rw [hre_exp]
      have hb := hB (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) (by simp; norm_num) (by simp)
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    calc ‖∫ t : ℝ, Φ (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ ∫ t : ℝ, B * (1 + t ^ 2)⁻¹ * Real.exp ((3 / 8) * τ) :=
          norm_integral_le_of_norm_le ((integrable_inv_one_add_sq.const_mul B).mul_const _)
            (Eventually.of_forall hpt)
      _ = B * Real.pi * Real.exp ((3 / 8) * τ) := by
          rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]
  set Lpos : ℂ → ℂ := fun w => ∫ τ in Ioi (0 : ℝ),
    Complex.exp (-w * (τ : ℂ)) * twinReflected q (r + u) h τ with hLpos
  have hC₀' : ∀ τ : ℝ, -(0 : ℝ) < τ →
      ‖twinReflected q (r + u) h τ‖ ≤ max C₀ 0 * Real.exp (-δ * τ) :=
    fun τ hτ => (hC₀ τ (by linarith)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hLpos_d : DifferentiableOn ℂ Lpos {w : ℂ | -δ < w.re} := by
    simpa [hLpos] using RingdownRate.differentiableOn_laplace hGc (le_max_right C₀ 0) hC₀'
  set Lneg₀ : ℂ → ℂ := fun z => ∫ σ' in Ioi (0 : ℝ),
    Complex.exp (-z * (σ' : ℂ)) * twinReflected q (r + u) h (-σ') with hLneg₀
  have hGe' : ∀ σ' : ℝ, -(0 : ℝ) < σ' →
      ‖twinReflected q (r + u) h (-σ')‖ ≤ B * Real.pi * Real.exp (-(3 / 8) * σ') := by
    intro σ' hσ'; simpa [mul_neg, neg_mul] using hGe (-σ') (by linarith)
  have hLneg₀_d : DifferentiableOn ℂ Lneg₀ {z : ℂ | -(3 / 8 : ℝ) < z.re} := by
    simpa [hLneg₀] using RingdownRate.differentiableOn_laplace (hGc.comp continuous_neg)
      (by positivity) hGe'
  set Lneg : ℂ → ℂ := fun w => Lneg₀ (-w) with hLneg
  have hLneg_d : DifferentiableOn ℂ Lneg {w : ℂ | w.re < 3 / 8} := by
    intro w hw
    have hw' : -w ∈ {z : ℂ | -(3 / 8 : ℝ) < z.re} := by show -(3 / 8 : ℝ) < (-w).re; simp; exact hw
    have hopen : IsOpen {z : ℂ | -(3 / 8 : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact ((hLneg₀_d (-w) hw').differentiableAt (hopen.mem_nhds hw')).comp w differentiableAt_id.neg
      |>.differentiableWithinAt
  set S : Set ℂ := {w : ℂ | -δ < w.re ∧ w.re < 3 / 8}
  have hSo : IsOpen S := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hSconn : IsPreconnected S :=
    ((convex_halfSpace_re_gt (-δ)).inter (convex_halfSpace_re_lt (3 / 8))).isPreconnected
  set Φ₁ : ℂ → ℂ := fun w =>
    (2 * w - 1) * PositiveEulerHorizon.completedXi q (r + u) (1 + 2 * w) * (Lpos w + Lneg w) with hΦ₁
  set Φ₂ : ℂ → ℂ := fun w =>
    2 * Real.pi * pulseAmplitude h (-I * w) * (1 + 2 * w) *
      PositiveEulerHorizon.completedXi q (r + u) (2 * w) with hΦ₂
  have hUpos : IsOpen {w : ℂ | -δ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUneg : IsOpen {w : ℂ | w.re < 3 / 8} := isOpen_lt Complex.continuous_re continuous_const
  have hcx := PositiveEulerHorizon.differentiable_completedXi (p := q) (by omega) (r + u)
  have hΦ₁a : AnalyticOnNhd ℂ Φ₁ S := by
    refine DifferentiableOn.analyticOnNhd ?_ hSo
    intro w hw
    have h1' := (hLpos_d w hw.1).differentiableAt (hUpos.mem_nhds hw.1)
    have h2' := (hLneg_d w hw.2).differentiableAt (hUneg.mem_nhds hw.2)
    exact (((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 2 * v - 1) w).mul
      ((hcx _).comp w (by fun_prop))).mul (h1'.add h2')).differentiableWithinAt
  have hΦ₂a : AnalyticOnNhd ℂ Φ₂ S := by
    refine DifferentiableOn.analyticOnNhd ?_ hSo
    intro w _
    exact ((((differentiableAt_const _).mul
      ((h.differentiable_amplitude _).comp w (by fun_prop))).mul (by fun_prop)).mul
      ((hcx _).comp w (by fun_prop))).differentiableWithinAt
  have hagree : ∀ w : ℂ, 1 / 8 < w.re → w.re < 5 / 16 → Φ₁ w = Φ₂ w := by
    intro w hw1 hw2
    have hlap : Lpos w + Lneg w = 2 * Real.pi * pulseAmplitude h (-I * w) *
        PositiveEulerHorizon.scatteringPhase q (r + u) w := by
      have hneg_rw : Lneg w = ∫ σ' in Ioi (0 : ℝ),
          Complex.exp (w * (σ' : ℂ)) * twinReflected q (r + u) h (-σ') := by
        simp only [hLneg, hLneg₀, neg_neg]
      rw [hneg_rw]
      exact twin_bilateral_laplace_eq hq hr hu hru h hw1 hw2
    have h2w : 2 * w - 1 ≠ 0 := fun h0' => by
      have := congrArg Complex.re h0'; simp at this; linarith
    have hxi : PositiveEulerHorizon.completedXi q (r + u) (1 + 2 * w) ≠ 0 :=
      PositiveEulerHorizon.completedXi_den_ne_zero hq hr hu hru (by linarith)
    simp only [hΦ₁, hΦ₂, hlap, PositiveEulerHorizon.scatteringPhase,
      PositiveEulerHorizon.reducedScattering]
    field_simp
  have hEq : EqOn Φ₁ Φ₂ S := by
    refine hΦ₁a.eqOn_of_preconnected_of_eventuallyEq hΦ₂a hSconn
      (show (1 / 4 : ℂ) ∈ S from ⟨by simp; linarith, by norm_num⟩) ?_
    have hV : IsOpen {w : ℂ | 1 / 8 < w.re ∧ w.re < 5 / 16} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hV.mem_nhds (show (1 / 4 : ℂ) ∈ {w : ℂ | 1 / 8 < w.re ∧ w.re < 5 / 16} by
      norm_num)] with w hw
    exact hagree w hw.1 hw.2
  have hpS : p ∈ S := ⟨hp_gt, by rw [hpre]; linarith⟩
  have hp_eq := hEq hpS
  simp only [hΦ₁, hΦ₂, hpxi, mul_zero, zero_mul] at hp_eq
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have ha_ne : pulseAmplitude h (-I * p) ≠ 0 := pulseAmplitude_excitingPulse_ne_zero p
  have h12p : 1 + 2 * p ≠ 0 := by
    intro h0'; rw [hp1] at h0'
    have := congrArg Complex.re h0'; rw [hs₀_re, Complex.zero_re] at this; linarith
  have hxi2p : PositiveEulerHorizon.completedXi q (r + u) (2 * p) ≠ 0 := by
    rw [← PositiveEulerHorizon.completedXi_one_sub q (r + u) (2 * p),
      show (1 : ℂ) - 2 * p = 1 + 2 * (-p) by ring]
    exact PositiveEulerHorizon.completedXi_den_ne_zero hq hr hu hru (by simp [hpre]; linarith)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hpi ha_ne) h12p) hxi2p hp_eq.symm

/-! ## 3. Finite-Time Distinguishing Inequality 1: Predeclared-Window Cusp Escape Separation -/

/-- Smooth nonnegative bump supported in `(-R, R)` and equal to `1` on `[-R/2, R/2]`. -/
def scaledBumpData (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : ℝ) :=
  ⟨R / 2, R, by positivity, by linarith⟩

/-- Compactly supported smooth pulse associated to `scaledBumpData R hR`. -/
def scaledBumpPulse (R : ℝ) (hR : 0 < R) : CompactPulse where
  toFun S := ((scaledBumpData R hR S : ℝ) : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp (scaledBumpData R hR).contDiff
  compact := (scaledBumpData R hR).hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)

theorem scaledBumpPulse_eq_zero_of_le {R : ℝ} (hR : 0 < R) {S : ℝ} (hS : R ≤ |S|) :
    scaledBumpPulse R hR S = 0 := by
  have hnot : S ∉ Function.support (scaledBumpData R hR : ℝ → ℝ) := by
    rw [(scaledBumpData R hR).support_eq, Metric.mem_ball, Real.dist_0_eq_abs]
    have hr : (scaledBumpData R hR).rOut = R := rfl
    rw [hr]; linarith
  rw [scaledBumpPulse]
  simp [Function.notMem_support.mp hnot]

theorem integral_norm_sq_scaledBumpPulse_pos {R : ℝ} (hR : 0 < R) :
    0 < ∫ S : ℝ, ‖scaledBumpPulse R hR S‖ ^ 2 := by
  have hint : Integrable fun S : ℝ => ‖scaledBumpPulse R hR S‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm (scaledBumpPulse R hR).continuous_toFun.aestronglyMeasurable).mp
      (memLp_two_pulse (scaledBumpPulse R hR))
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg (fun _ => sq_nonneg _) hint]
  have hsupp : Function.support (fun S : ℝ => ‖scaledBumpPulse R hR S‖ ^ 2) = Metric.ball (0 : ℝ) R := by
    have hb := (scaledBumpData R hR).support_eq
    have hr : (scaledBumpData R hR).rOut = R := rfl
    rw [hr] at hb
    ext S
    simp only [Function.mem_support, ne_eq, sq_eq_zero_iff, norm_eq_zero, scaledBumpPulse,
      Complex.ofReal_eq_zero]
    exact Iff.rfl.trans (Function.mem_support.symm.trans (by rw [hb]))
  rw [hsupp]
  exact Metric.measure_ball_pos _ _ hR

/-- **Finite-Time Distinguishing Inequality 1 (Exact Cusp Escape Separation on Predeclared Window).**
For any `q > 1`, `1/2 < σ < 1` (`r = q^σ, u = q^{1-σ}`), `0 < S₀ < log q`, and any mean-zero
`h : CompactPulse` supported in `[-S₀, S₀]`, at the predeclared cutoff `T₂ = 2 log q - S₀`:
`∫_{T₂}^∞ ‖twinReflected q (r + u) h T‖² dT - ∫_{T₂}^∞ ‖pulseReflected h T‖² dT
  = (1 - 1/q²) ∫_{-S₀}^{T₂} ‖pulseReflected h T‖² dT`.
Moreover, an explicit balanced mean-zero compact pulse makes this gap strictly positive (`> 0`). -/
theorem finite_time_cusp_escape_separation {q : ℕ} (hq : 1 < q) {σ S₀ : ℝ}
    (h0 : 1 / 2 < σ) (h1 : σ < 1) (hS₀_pos : 0 < S₀) (hS₀_lt : S₀ < Real.log q) :
    let r : ℝ := (q : ℝ) ^ σ
    let u : ℝ := (q : ℝ) ^ (1 - σ)
    let T₂ : ℝ := 2 * Real.log q - S₀
    (∀ h : CompactPulse, (∀ s : ℝ, S₀ < |s| → h s = 0) → meanCoefficient h = 0 →
      (∫ T in Ioi T₂, ‖twinReflected q (r + u) h T‖ ^ 2) -
        (∫ T in Ioi T₂, ‖pulseReflected h T‖ ^ 2) =
        (1 - 1 / (q : ℝ) ^ 2) * ∫ T in Ioc (-S₀) T₂, ‖pulseReflected h T‖ ^ 2) ∧
    (∃ h : CompactPulse, (∀ s : ℝ, S₀ < |s| → h s = 0) ∧ meanCoefficient h = 0 ∧
      0 < (∫ T in Ioi T₂, ‖twinReflected q (r + u) h T‖ ^ 2) -
        (∫ T in Ioi T₂, ‖pulseReflected h T‖ ^ 2)) := by
  dsimp only
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hqR
  set r : ℝ := (q : ℝ) ^ σ
  set u : ℝ := (q : ℝ) ^ (1 - σ)
  set T₂ : ℝ := 2 * Real.log q - S₀
  have hr : 1 < r := Real.one_lt_rpow hqR (by linarith)
  have hu : 1 < u := Real.one_lt_rpow hqR (by linarith [h1])
  have hur : u < r := Real.rpow_lt_rpow_of_exponent_lt hqR (by linarith)
  have hru : r * u = q := by
    dsimp only [r, u]
    rw [← Real.rpow_add hq0, show σ + (1 - σ) = 1 by ring, Real.rpow_one]
  have hT₂_ge : -S₀ ≤ T₂ := by dsimp only [T₂]; linarith
  have hid : ∀ h : CompactPulse, (∀ s : ℝ, S₀ < |s| → h s = 0) → meanCoefficient h = 0 →
      (∫ T in Ioi T₂, ‖twinReflected q (r + u) h T‖ ^ 2) -
        (∫ T in Ioi T₂, ‖pulseReflected h T‖ ^ 2) =
        (1 - 1 / (q : ℝ) ^ 2) * ∫ T in Ioc (-S₀) T₂, ‖pulseReflected h T‖ ^ 2 := by
    intro h hS₀ hmean
    obtain ⟨hE_twin_int, hE_twin_tot⟩ := integrable_and_integral_norm_sq_twinReflected hq hr hu hru h
    have hall_twin : (∫ T in Iic T₂, ‖twinReflected q (r + u) h T‖ ^ 2) +
        (∫ T in Ioi T₂, ‖twinReflected q (r + u) h T‖ ^ 2) = ∫ S : ℝ, ‖h S‖ ^ 2 := by
      have h1' := integral_add_compl (s := Iic T₂) measurableSet_Iic hE_twin_int
      rwa [compl_Iic, hE_twin_tot] at h1'
    have hdisj : Disjoint (Iic (-S₀)) (Ioc (-S₀) T₂) :=
      Set.disjoint_left.mpr fun _ hx1 hx2 => hx2.1.not_ge hx1
    have hunion : Iic (-S₀) ∪ Ioc (-S₀) T₂ = Iic T₂ := Iic_union_Ioc_eq_Iic hT₂_ge
    have hsplit_twin : (∫ T in Iic T₂, ‖twinReflected q (r + u) h T‖ ^ 2) =
        (∫ T in Iic (-S₀), ‖twinReflected q (r + u) h T‖ ^ 2) +
          ∫ T in Ioc (-S₀) T₂, ‖twinReflected q (r + u) h T‖ ^ 2 := by
      rw [← hunion, setIntegral_union hdisj measurableSet_Ioc hE_twin_int.integrableOn
        hE_twin_int.integrableOn]
    have hpre_twin : (∫ T in Iic (-S₀), ‖twinReflected q (r + u) h T‖ ^ 2) = 0 := by
      have hae : ∀ᵐ T : ℝ, T ≠ -S₀ := by
        rw [ae_iff]
        have hset : {T : ℝ | ¬ T ≠ -S₀} = ({-S₀} : Set ℝ) := by ext T; simp
        rw [hset]; exact measure_singleton (-S₀)
      refine setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
        hE_twin_int.integrableOn |>.mpr ?_
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic]
      refine hae.mono fun T hne hle => ?_
      rw [twinReflected_before_wavefront hq hr hu hru hur h hS₀ (lt_of_le_of_ne hle hne), hmean]
      simp
    have hwin_twin : (∫ T in Ioc (-S₀) T₂, ‖twinReflected q (r + u) h T‖ ^ 2) =
        (1 / (q : ℝ) ^ 2) * ∫ T in Ioc (-S₀) T₂, ‖pulseReflected h T‖ ^ 2 := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc fun T hT => ?_
      rw [twinReflected_eq_div_early_of_meanZero hq hr hu hru hur h hS₀ hmean hT.2,
        norm_mul, norm_div, norm_one, Complex.norm_natCast, mul_pow, div_pow, one_pow]
    have hmod_esc := integral_Ioi_norm_sq_pulseReflected h hS₀ hT₂_ge
    rw [hmean, norm_zero, zero_pow (by decide), zero_mul, sub_zero] at hmod_esc
    linarith
  refine ⟨hid, ?_⟩
  set δ : ℝ := min (S₀ / 2) (Real.log 2 / 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : 0 < δ := lt_min (by linarith) (by positivity)
  set b := scaledBumpPulse δ hδ
  set h := balancedMeanZeroPulse δ b
  have hb_supp : ∀ s : ℝ, δ < |s| → b s = 0 := fun s hs => scaledBumpPulse_eq_zero_of_le hδ hs.le
  have hh_supp : ∀ s : ℝ, S₀ < |s| → h s = 0 := by
    intro s hs
    have h2δ : δ + δ ≤ S₀ := by linarith [min_le_left (S₀ / 2) (Real.log 2 / 2)]
    exact balancedMeanZeroPulse_eq_zero_of_support_bound hδ.le b hb_supp (by linarith)
  have hh_mean : meanCoefficient h = 0 := meanCoefficient_balancedMeanZeroPulse δ b
  refine ⟨h, hh_supp, hh_mean, ?_⟩
  rw [hid h hh_supp hh_mean]
  have h1q : 0 < 1 - 1 / (q : ℝ) ^ 2 := by
    have hq2 : (1 : ℝ) < (q : ℝ) ^ 2 := one_lt_pow₀ hqR (by decide)
    rw [sub_pos, div_lt_one (by positivity)]
    exact hq2
  refine mul_pos h1q ?_
  have hS0_ne : pulseReflected h 0 ≠ 0 := by
    have he := h.pulseEcho_eq 0
    rw [hh_mean, zero_mul, add_zero] at he
    rw [← he, pulseEcho]
    have hpt_c1 : ∀ τ : ℝ, h (0 - τ) * ((echoKernel τ : ℝ) : ℂ) =
        (Ioi (0 : ℝ)).indicator
          (fun v : ℝ => ((scaledBumpData δ hδ (δ - v) * bounceKernel v : ℝ) : ℂ)) τ := by
      intro τ
      rcases le_or_gt τ 0 with hτ | hτ
      · rw [echoKernel_eq_zero_of_nonpos hτ, indicator_of_notMem (by simp; linarith)]
        simp
      · rw [indicator_of_mem (mem_Ioi.mpr hτ)]
        have hker : echoKernel τ = bounceKernel τ ∨ 2 * Real.log 2 < τ := by
          rcases le_or_gt τ (2 * Real.log 2) with hle2 | hgt2
          · left
            rw [echoKernel, tsum_eq_single 1]
            · rw [echoTerm, if_pos (by simp [echoDelay]; exact hτ)]
              simp [echoWeight, echoDelay]
            · intro c hc1
              rcases eq_or_ne c 0 with rfl | hc0
              · exact echoTerm_zero τ
              · have hc2 : (2 : ℝ) ≤ c := by exact_mod_cast (show 2 ≤ c by omega)
                have hdl : 2 * Real.log 2 ≤ echoDelay c := by
                  rw [echoDelay]; linarith [Real.log_le_log (by norm_num) hc2]
                rw [echoTerm, if_neg (by linarith)]
          · exact Or.inr hgt2
        rcases hker with hker1 | hgt2
        · rw [hker1, balancedMeanZeroPulse_apply]
          have hb_neg : b (0 - τ - δ) = 0 :=
            scaledBumpPulse_eq_zero_of_le hδ (by rw [abs_of_neg (by linarith)]; linarith)
          rw [hb_neg, mul_zero, sub_zero, show (0 : ℝ) - τ + δ = δ - τ by ring]
          simp [b, scaledBumpPulse, Complex.ofReal_mul]
        · have h2δ_le : 2 * δ ≤ Real.log 2 := by linarith [min_le_right (S₀ / 2) (Real.log 2 / 2)]
          have hh0 : h (0 - τ) = 0 :=
            balancedMeanZeroPulse_eq_zero_of_support_bound hδ.le b hb_supp
              (by rw [zero_sub, abs_neg, abs_of_pos hτ]; linarith)
          have hb0 : scaledBumpData δ hδ (δ - τ) = 0 := by
            have hnot : δ - τ ∉ Function.support (scaledBumpData δ hδ : ℝ → ℝ) := by
              rw [(scaledBumpData δ hδ).support_eq, Metric.mem_ball, Real.dist_0_eq_abs]
              have hr' : (scaledBumpData δ hδ).rOut = δ := rfl
              rw [hr', abs_of_neg (by linarith)]; linarith
            exact Function.notMem_support.mp hnot
          rw [hh0, hb0]; simp
    simp_rw [hpt_c1]
    rw [integral_indicator measurableSet_Ioi, integral_complex_ofReal]
    intro hzero
    have hreal0 : (∫ v in Ioi (0 : ℝ), scaledBumpData δ hδ (δ - v) * bounceKernel v) = 0 :=
      Complex.ofReal_eq_zero.mp hzero
    have h_int_rhs : IntegrableOn
        (fun v : ℝ => scaledBumpData δ hδ (δ - v) * bounceKernel v) (Ioi 0) := by
      have hi_c := (h.integrable_pulse_mul_echoKernel 0).congr (Eventually.of_forall hpt_c1)
      rw [integrable_indicator_iff measurableSet_Ioi] at hi_c
      exact (integrableOn_congr_fun (fun v _ => by simp) measurableSet_Ioi).mp
        (Complex.reCLM.integrable_comp hi_c)
    have h_int_lhs : IntegrableOn (fun v : ℝ => scaledBumpData δ hδ (δ - v)) (Ioi 0) := by
      have hc_b : Continuous fun v : ℝ => scaledBumpData δ hδ (δ - v) :=
        (scaledBumpData δ hδ).continuous.comp (continuous_const.sub continuous_id)
      have hcs_b : HasCompactSupport fun v : ℝ => scaledBumpData δ hδ (δ - v) := by
        refine HasCompactSupport.of_support_subset_isCompact
          (isCompact_Icc (a := (0 : ℝ)) (b := 2 * δ)) fun v hv => ?_
        rw [Function.mem_support] at hv
        have hmem : δ - v ∈ Function.support (scaledBumpData δ hδ : ℝ → ℝ) := hv
        rw [(scaledBumpData δ hδ).support_eq, Metric.mem_ball, Real.dist_0_eq_abs] at hmem
        have hr' : (scaledBumpData δ hδ).rOut = δ := rfl
        rw [hr', abs_lt] at hmem
        exact ⟨by linarith, by linarith⟩
      exact (hc_b.integrable_of_hasCompactSupport hcs_b).integrableOn
    have hbounce_ge : ∀ v ∈ Ioi (0 : ℝ),
        scaledBumpData δ hδ (δ - v) ≤ scaledBumpData δ hδ (δ - v) * bounceKernel v := by
      intro v hv
      have hv0 : 0 < v := hv
      have hexp1 : Real.exp (-v) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have hexp0 : 0 < Real.exp (-v) := Real.exp_pos _
      have hb1 : 1 ≤ bounceKernel v := by
        unfold bounceKernel
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) (by norm_num)
      exact le_mul_of_one_le_right (scaledBumpData δ hδ).nonneg hb1
    have hle_int := setIntegral_mono_on h_int_lhs h_int_rhs measurableSet_Ioi hbounce_ge
    have hpos_lhs : 0 < ∫ v in Ioi (0 : ℝ), scaledBumpData δ hδ (δ - v) := by
      have hall : (∫ v in Ioi (0 : ℝ), scaledBumpData δ hδ (δ - v)) =
          ∫ v : ℝ, scaledBumpData δ hδ (δ - v) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_
        have hv0 : v ≤ 0 := not_lt.mp hv
        have hnot : δ - v ∉ Function.support (scaledBumpData δ hδ : ℝ → ℝ) := by
          rw [(scaledBumpData δ hδ).support_eq, Metric.mem_ball, Real.dist_0_eq_abs]
          have hr' : (scaledBumpData δ hδ).rOut = δ := rfl
          rw [hr', abs_of_nonneg (by linarith)]; linarith
        exact Function.notMem_support.mp hnot
      rw [hall, integral_sub_left_eq_self (scaledBumpData δ hδ : ℝ → ℝ) volume δ]
      exact (scaledBumpData δ hδ).integral_pos
    linarith
  have h0_mem : (0 : ℝ) ∈ Ioo (-S₀) T₂ := ⟨by linarith, by dsimp only [T₂]; linarith⟩
  have hopen : IsOpen (Ioo (-S₀) T₂ ∩ {T : ℝ | pulseReflected h T ≠ 0}) :=
    isOpen_Ioo.inter (isOpen_ne.preimage (continuous_pulseReflected h))
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp hopen 0 ⟨h0_mem, hS0_ne⟩
  have hcont_norm : Continuous fun T : ℝ => ‖pulseReflected h T‖ ^ 2 :=
    (continuous_pulseReflected h).norm.pow 2
  obtain ⟨r₁, hr₁, hr₁_le⟩ := Metric.isOpen_iff.mp
    (isOpen_lt continuous_const hcont_norm) 0 (by
      show ‖pulseReflected h 0‖ ^ 2 / 2 < ‖pulseReflected h 0‖ ^ 2
      have : 0 < ‖pulseReflected h 0‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hS0_ne)
      linarith)
  set η : ℝ := min (ε₀ / 2) (r₁ / 2)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hsub_Ioc : Ioc (0 : ℝ) η ⊆ Ioc (-S₀) T₂ := by
    intro T hT
    have hmem : T ∈ Metric.ball (0 : ℝ) ε₀ := by
      rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_of_pos hT.1]
      linarith [hT.2, min_le_left (ε₀ / 2) (r₁ / 2)]
    exact Ioo_subset_Ioc_self (hball hmem).1
  have hfloor : (‖pulseReflected h 0‖ ^ 2 / 2) * η ≤
      ∫ T in Ioc (0 : ℝ) η, ‖pulseReflected h T‖ ^ 2 := by
    have hconst : (‖pulseReflected h 0‖ ^ 2 / 2) * η =
        ∫ _T in Ioc (0 : ℝ) η, (‖pulseReflected h 0‖ ^ 2 / 2) := by
      rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
        ENNReal.toReal_ofReal hη.le, smul_eq_mul]
      ring
    rw [hconst]
    have hfin : volume (Ioc (0 : ℝ) η) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    refine setIntegral_mono_on (integrableOn_const hfin)
      (integrable_norm_sq_pulseReflected h).integrableOn measurableSet_Ioc fun T hT => ?_
    have hmem : T ∈ Metric.ball (0 : ℝ) r₁ := by
      rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_of_pos hT.1]
      linarith [hT.2, min_le_right (ε₀ / 2) (r₁ / 2)]
    exact (hr₁_le hmem).le
  have hpos_floor : 0 < (‖pulseReflected h 0‖ ^ 2 / 2) * η :=
    mul_pos (half_pos (sq_pos_of_pos (norm_pos_iff.mpr hS0_ne))) hη
  exact hpos_floor.trans_le (hfloor.trans (setIntegral_mono_set
    (integrable_norm_sq_pulseReflected h).integrableOn
    (Eventually.of_forall fun _ => sq_nonneg _) hsub_Ioc.eventuallyLE))

/-! ## 4. Finite-Time Distinguishing Inequality 2: `p²` and `p q` Group-Delay Interference -/

/-- Boundary reduced group-delay density `-Re(S_red'(iξ) / S_red(iξ))`. -/
def boundaryGroupDelayDensity (S_red : ℂ → ℂ) (ξ : ℝ) : ℝ :=
  -(deriv S_red ((ξ : ℂ) * I) / S_red ((ξ : ℂ) * I)).re

/-- Band-limited boundary group-delay functional on `[-Ω, Ω]`. -/
def bandGroupDelay (S_red : ℂ → ℂ) (Ω : ℝ) (h : CompactPulse) : ℝ :=
  ∫ ξ in Icc (-Ω) Ω, ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 * boundaryGroupDelayDensity S_red ξ

/-- Full-line excess boundary group-delay functional of `PositiveEulerHorizon` over `ζ`. -/
def excessPulseGroupDelay (p : ℕ) (r u : ℝ) (h : CompactPulse) : ℝ :=
  ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 *
    (boundaryGroupDelayDensity (PositiveEulerHorizon.reducedScattering p (r + u)) ξ -
      boundaryGroupDelayDensity modularReducedScattering ξ)

/-- **Universal Dynamical Nonnegativity of Boundary Group Delay.** Any Schur contraction on
`Re w ≥ 0` that is differentiable and unitary at `iξ` has `boundaryGroupDelayDensity S_red ξ ≥ 0`. -/
theorem boundaryGroupDelayDensity_nonneg_of_schur {S_red : ℂ → ℂ} {ξ : ℝ}
    (hdiff : DifferentiableAt ℂ S_red ((ξ : ℂ) * I))
    (hunit : ‖S_red ((ξ : ℂ) * I)‖ = 1)
    (hschur : ∀ x : ℝ, 0 ≤ x → ‖S_red ((x : ℂ) + (ξ : ℂ) * I)‖ ≤ 1) :
    0 ≤ boundaryGroupDelayDensity S_red ξ := by
  set z₀ : ℂ := (ξ : ℂ) * I
  set z' : ℂ := deriv S_red z₀
  let t_seq : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have ht_pos : ∀ n : ℕ, 0 < t_seq n := fun n => by dsimp only [t_seq]; positivity
  have hseq : Tendsto (fun n : ℕ => (t_seq n : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have ht : Tendsto t_seq atTop (𝓝 (0 : ℝ)) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
      have hc := (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto.comp ht
      rw [Complex.ofReal_zero] at hc
      exact hc
    · exact Set.mem_compl_singleton_iff.mpr (Complex.ofReal_ne_zero.mpr (ht_pos n).ne')
  have hlim_c : Tendsto (fun n : ℕ =>
      (t_seq n : ℂ)⁻¹ • (S_red (z₀ + (t_seq n : ℂ)) - S_red z₀))
      atTop (𝓝 z') :=
    (hasDerivAt_iff_tendsto_slope_zero.mp hdiff.hasDerivAt).comp hseq
  have hlim_re : Tendsto (fun n : ℕ =>
      (((t_seq n : ℂ)⁻¹ • (S_red (z₀ + (t_seq n : ℂ)) - S_red z₀)) *
        (starRingEnd ℂ) (S_red z₀)).re)
      atTop (𝓝 (z' * (starRingEnd ℂ) (S_red z₀)).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp (hlim_c.mul_const ((starRingEnd ℂ) (S_red z₀)))
  have hnonpos : (z' * (starRingEnd ℂ) (S_red z₀)).re ≤ 0 := by
    refine le_of_tendsto hlim_re (Eventually.of_forall fun n => ?_)
    dsimp only [Function.comp_def, smul_eq_mul]
    have ht0 : 0 < t_seq n := ht_pos n
    have hcast : (((t_seq n : ℂ)⁻¹ * (S_red (z₀ + (t_seq n : ℂ)) - S_red z₀) *
          (starRingEnd ℂ) (S_red z₀)).re) =
        (t_seq n)⁻¹ * ((S_red ((t_seq n : ℂ) + z₀) * (starRingEnd ℂ) (S_red z₀)).re - 1) := by
      have hns : (S_red z₀ * (starRingEnd ℂ) (S_red z₀)).re = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re, hunit, one_pow]
      rw [add_comm z₀ (t_seq n : ℂ), mul_assoc, ← Complex.ofReal_inv, Complex.re_ofReal_mul,
        sub_mul, Complex.sub_re, hns]
    rw [hcast]
    refine mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht0.le) ?_
    have hle1 : (S_red ((t_seq n : ℂ) + z₀) * (starRingEnd ℂ) (S_red z₀)).re ≤ 1 := by
      refine ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans ?_
      rw [norm_mul, RCLike.norm_conj, hunit, mul_one]
      exact hschur (t_seq n) ht0.le
    linarith
  have hdiv : z' / S_red z₀ = z' * (starRingEnd ℂ) (S_red z₀) := by
    have hns : Complex.normSq (S_red z₀) = 1 := by rw [Complex.normSq_eq_norm_sq, hunit, one_pow]
    rw [div_eq_mul_inv, Complex.inv_def, hns]
    simp
  rw [boundaryGroupDelayDensity, show ((ξ : ℂ) * I) = z₀ from rfl,
    show deriv S_red z₀ = z' from rfl, hdiv]
  linarith

/-- Nonnegativity of boundary group delay on both the undeformed modular surface and
`PositiveEulerHorizon`, both pointwise and on every finite frequency band `[-Ω, Ω]`. -/
theorem modular_and_twin_groupDelay_nonneg {q : ℕ} (hq : 1 < q) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = q) (Ω : ℝ) (h : CompactPulse) :
    (∀ ξ : ℝ, 0 ≤ boundaryGroupDelayDensity modularReducedScattering ξ ∧
      0 ≤ boundaryGroupDelayDensity (PositiveEulerHorizon.reducedScattering q (r + u)) ξ) ∧
    0 ≤ bandGroupDelay modularReducedScattering Ω h ∧
    0 ≤ bandGroupDelay (PositiveEulerHorizon.reducedScattering q (r + u)) Ω h := by
  have hpt : ∀ ξ : ℝ, 0 ≤ boundaryGroupDelayDensity modularReducedScattering ξ ∧
      0 ≤ boundaryGroupDelayDensity (PositiveEulerHorizon.reducedScattering q (r + u)) ξ := by
    intro ξ
    have hmod_diff : DifferentiableAt ℂ modularReducedScattering ((ξ : ℂ) * I) :=
      ((xi_differentiable _).comp ((ξ : ℂ) * I) (by fun_prop)).div
        ((xi_differentiable _).comp ((ξ : ℂ) * I) (by fun_prop))
        (xi_ne_zero_of_one_le_re (by simp))
    have hmod_unit : ‖modularReducedScattering ((ξ : ℂ) * I)‖ = 1 := by
      have hn := norm_scatteringPhase_line ξ
      have hlin : ‖(1 + 2 * ((ξ : ℂ) * I)) / (2 * ((ξ : ℂ) * I) - 1)‖ = 1 := by
        rw [norm_div]
        have hsq : ‖1 + 2 * ((ξ : ℂ) * I)‖ ^ 2 = ‖2 * ((ξ : ℂ) * I) - 1‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
          simp [Complex.normSq_apply]
        have hne : 2 * ((ξ : ℂ) * I) - 1 ≠ 0 := fun h0 => by
          have := congrArg Complex.re h0; simp at this
        rw [(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq,
          div_self (norm_ne_zero_iff.mpr hne)]
      unfold scatteringPhase at hn
      rw [norm_mul, hlin, one_mul] at hn
      exact hn
    exact ⟨boundaryGroupDelayDensity_nonneg_of_schur hmod_diff hmod_unit
        (fun x hx => norm_modularReducedScattering_le_one (by simp [hx])),
      boundaryGroupDelayDensity_nonneg_of_schur
        (PositiveEulerHorizon.differentiableAt_reducedScattering hq hr hu hru (by simp))
        (by rw [PositiveEulerHorizon.reducedScattering_eq_gate_mul (by omega), norm_mul,
          PositiveEulerHorizon.norm_gate_axis hq hr hu hru ξ, hmod_unit, one_mul])
        (fun x hx => PositiveEulerHorizon.norm_reducedScattering_le_one hq hr hu hru (by simp [hx]))⟩
  refine ⟨hpt, setIntegral_nonneg measurableSet_Icc (fun ξ _ => mul_nonneg (sq_nonneg _) (hpt ξ).1),
    setIntegral_nonneg measurableSet_Icc (fun ξ _ => mul_nonneg (sq_nonneg _) (hpt ξ).2)⟩

private def singleFactorGate (p : ℕ) (a : ℝ) (w : ℂ) : ℂ :=
  (1 + (a : ℂ) * (p : ℂ) ^ (-2 * w)) / ((a : ℂ) + (p : ℂ) ^ (-2 * w))

private theorem hasDerivAt_singleFactorGate {p : ℕ} (hp : 1 < p) {a : ℝ} (ha : 1 < a)
    {w : ℂ} (hw : 0 ≤ w.re) :
    HasDerivAt (singleFactorGate p a)
      (-2 * (Real.log p : ℂ) * ((a ^ 2 - 1 : ℝ) : ℂ) * (p : ℂ) ^ (-2 * w) /
        ((a : ℂ) + (p : ℂ) ^ (-2 * w)) ^ 2) w := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hpow_eq : (fun z : ℂ => (p : ℂ) ^ (-2 * z)) =
      fun z : ℂ => Complex.exp (-2 * (Real.log p : ℂ) * z) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.natCast_log]
    congr 1; ring
  have hv_der : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-2 * z))
      (-2 * (Real.log p : ℂ) * (p : ℂ) ^ (-2 * w)) w := by
    rw [hpow_eq]
    refine (((hasDerivAt_id w).const_mul (-2 * (Real.log p : ℂ))).cexp).congr_deriv ?_
    have hw_eq := congrFun hpow_eq w
    dsimp only [id]
    rw [← hw_eq]
    ring
  have hv_le : ‖(p : ℂ) ^ (-2 * w)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), show (-2 * w).re = -2 * w.re by simp]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.le) (by linarith)
  have hden_ne : (a : ℂ) + (p : ℂ) ^ (-2 * w) ≠ 0 := fun h0 => by
    have hv_eq : (p : ℂ) ^ (-2 * w) = -(a : ℂ) := by linear_combination h0
    rw [hv_eq, norm_neg, Complex.norm_real, Real.norm_of_nonneg (zero_lt_one.trans ha).le] at hv_le
    linarith
  have hnum_der : HasDerivAt (fun z : ℂ => 1 + (a : ℂ) * (p : ℂ) ^ (-2 * z))
      ((a : ℂ) * (-2 * (Real.log p : ℂ) * (p : ℂ) ^ (-2 * w))) w := by
    simpa using (hv_der.const_mul (a : ℂ)).const_add 1
  have hden_der : HasDerivAt (fun z : ℂ => (a : ℂ) + (p : ℂ) ^ (-2 * z))
      (-2 * (Real.log p : ℂ) * (p : ℂ) ^ (-2 * w)) w := by
    simpa using hv_der.const_add (a : ℂ)
  refine (hnum_der.div hden_der hden_ne).congr_deriv ?_
  push_cast
  congr 1
  ring

/-- **Exact Closed-Form Excess Group-Delay Density of `PositiveEulerHorizon`.** -/
theorem twin_excess_groupDelayDensity_eq {p : ℕ} (hp : 1 < p) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = p) (ξ : ℝ) :
    boundaryGroupDelayDensity (PositiveEulerHorizon.reducedScattering p (r + u)) ξ -
        boundaryGroupDelayDensity modularReducedScattering ξ =
      2 * Real.log p *
        ((r ^ 2 - 1) / ‖(r : ℂ) + (p : ℂ) ^ (-2 * ((ξ : ℂ) * I))‖ ^ 2 +
         (u ^ 2 - 1) / ‖(u : ℂ) + (p : ℂ) ^ (-2 * ((ξ : ℂ) * I))‖ ^ 2) := by
  set z₀ : ℂ := (ξ : ℂ) * I
  set v : ℂ := (p : ℂ) ^ (-2 * z₀)
  have hv_norm : ‖v‖ = 1 := by
    dsimp only [v, z₀]
    rw [Complex.norm_natCast_cpow_of_pos (by omega),
      show (-2 * ((ξ : ℂ) * I)).re = 0 by simp, Real.rpow_zero]
  have hv_ne : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv_norm]; exact one_ne_zero)
  have hgate_fac : PositiveEulerHorizon.gate p (r + u) =
      fun w => singleFactorGate p r w * singleFactorGate p u w := by
    funext w
    have hruR : ((p : ℝ) : ℂ) = (r : ℂ) * (u : ℂ) := by rw [← hru, Complex.ofReal_mul]
    rw [PositiveEulerHorizon.gate, singleFactorGate, singleFactorGate, ← mul_div_mul_comm]
    congr 1 <;> { simp only [schurNum, schurDen, Complex.ofReal_neg, Complex.ofReal_add]
                  rw [hruR]; ring }
  have hsingle_ne : ∀ {a : ℝ}, 1 < a → singleFactorGate p a z₀ ≠ 0 := by
    intro a ha
    rw [singleFactorGate]
    have h1 : 1 + (a : ℂ) * v ≠ 0 := fun h0 => by
      have hv' : ‖(a : ℂ) * v‖ = 1 := by
        have he : (a : ℂ) * v = -1 := by linear_combination h0
        rw [he, norm_neg, norm_one]
      rw [norm_mul, hv_norm, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (zero_lt_one.trans ha).le] at hv'
      linarith
    have h2 : (a : ℂ) + v ≠ 0 := fun h0 => by
      have hv' : v = -(a : ℂ) := by linear_combination h0
      rw [hv', norm_neg, Complex.norm_real,
        Real.norm_of_nonneg (zero_lt_one.trans ha).le] at hv_norm
      linarith
    exact div_ne_zero h1 h2
  have hlog_single : ∀ {a : ℝ} (ha : 1 < a),
      deriv (singleFactorGate p a) z₀ / singleFactorGate p a z₀ =
        -(((2 * Real.log p * (a ^ 2 - 1) / ‖(a : ℂ) + v‖ ^ 2 : ℝ)) : ℂ) := by
    intro a ha
    rw [(hasDerivAt_singleFactorGate hp ha (w := z₀) (by simp [z₀])).deriv, singleFactorGate]
    have h1 : 1 + (a : ℂ) * v = v * (starRingEnd ℂ) ((a : ℂ) + v) := by
      have hvv : v * (starRingEnd ℂ) v = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv_norm, one_pow, Complex.ofReal_one]
      rw [map_add, Complex.conj_ofReal]
      linear_combination -hvv
    have hn2 : ((a : ℂ) + v) * (starRingEnd ℂ) ((a : ℂ) + v) = ((‖(a : ℂ) + v‖ : ℂ) ^ 2) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    have hden_ne : (a : ℂ) + v ≠ 0 := fun h0 => by
      have hv' : v = -(a : ℂ) := by linear_combination h0
      rw [hv', norm_neg, Complex.norm_real,
        Real.norm_of_nonneg (zero_lt_one.trans ha).le] at hv_norm
      linarith
    have hn_pos : (‖(a : ℂ) + v‖ : ℂ) ^ 2 ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hden_ne)
    change (-2 * (Real.log p : ℂ) * ((a ^ 2 - 1 : ℝ) : ℂ) * v / ((a : ℂ) + v) ^ 2) /
      ((1 + (a : ℂ) * v) / ((a : ℂ) + v)) = _
    rw [h1]
    have hconj_ne : (starRingEnd ℂ) ((a : ℂ) + v) ≠ 0 :=
      map_ne_zero_iff _ (RingHom.injective _) |>.mpr hden_ne
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat]
    field_simp [hv_ne, hden_ne, hconj_ne, hn_pos]
    rw [← hn2]
    ring
  have hd_gate := (hasDerivAt_singleFactorGate hp hr (w := z₀) (by simp [z₀])).mul
    (hasDerivAt_singleFactorGate hp hu (w := z₀) (by simp [z₀]))
  have hmod_diff : DifferentiableAt ℂ modularReducedScattering z₀ :=
    ((xi_differentiable _).comp z₀ (by fun_prop)).div
      ((xi_differentiable _).comp z₀ (by fun_prop)) (xi_ne_zero_of_one_le_re (by simp [z₀]))
  have hmod_ne : modularReducedScattering z₀ ≠ 0 := by
    intro h0
    have hn := norm_scatteringPhase_line ξ
    change ‖(1 + 2 * z₀) / (2 * z₀ - 1) * modularReducedScattering z₀‖ = 1 at hn
    rw [h0, mul_zero, norm_zero] at hn
    exact zero_ne_one hn
  have hgate_diff : DifferentiableAt ℂ (PositiveEulerHorizon.gate p (r + u)) z₀ := by
    rw [hgate_fac]; exact hd_gate.differentiableAt
  have hgate_ne : PositiveEulerHorizon.gate p (r + u) z₀ ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [PositiveEulerHorizon.norm_gate_axis hp hr hu hru ξ]; exact one_ne_zero)
  have hred_eq : PositiveEulerHorizon.reducedScattering p (r + u) =
      PositiveEulerHorizon.gate p (r + u) * modularReducedScattering :=
    funext fun w => PositiveEulerHorizon.reducedScattering_eq_gate_mul (by omega) (r + u) w
  have hlog_red : deriv (PositiveEulerHorizon.reducedScattering p (r + u)) z₀ /
      PositiveEulerHorizon.reducedScattering p (r + u) z₀ =
      deriv (PositiveEulerHorizon.gate p (r + u)) z₀ / PositiveEulerHorizon.gate p (r + u) z₀ +
        deriv modularReducedScattering z₀ / modularReducedScattering z₀ := by
    rw [hred_eq, (hgate_diff.hasDerivAt.mul hmod_diff.hasDerivAt).deriv, Pi.mul_apply]
    field_simp [hgate_ne, hmod_ne]
  have hlog_gate : deriv (PositiveEulerHorizon.gate p (r + u)) z₀ /
      PositiveEulerHorizon.gate p (r + u) z₀ =
      deriv (singleFactorGate p r) z₀ / singleFactorGate p r z₀ +
        deriv (singleFactorGate p u) z₀ / singleFactorGate p u z₀ := by
    have hgate_mul : PositiveEulerHorizon.gate p (r + u) =
        singleFactorGate p r * singleFactorGate p u := hgate_fac
    rw [hgate_mul, hd_gate.deriv, Pi.mul_apply]
    have hr_ne := hsingle_ne hr
    have hu_ne := hsingle_ne hu
    rw [← (hasDerivAt_singleFactorGate hp hr (w := z₀) (by simp [z₀])).deriv,
      ← (hasDerivAt_singleFactorGate hp hu (w := z₀) (by simp [z₀])).deriv]
    field_simp [hr_ne, hu_ne]
  rw [boundaryGroupDelayDensity, boundaryGroupDelayDensity, show (ξ : ℂ) * I = z₀ from rfl,
    hlog_red, hlog_gate, hlog_single hr, hlog_single hu]
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  ring

private theorem poisson_harmonic_hasSum {a : ℝ} (ha : 1 < a) {v : ℂ} (hv : ‖v‖ = 1) :
    HasSum (fun k : ℕ =>
        ((-1 : ℝ) ^ (k + 1) * (a⁻¹) ^ (k + 1)) * (v ^ (k + 1) + ((starRingEnd ℂ) v) ^ (k + 1)).re)
      ((a ^ 2 - 1) / ‖(a : ℂ) + v‖ ^ 2 - 1) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hlt1 : ‖-((a⁻¹ : ℝ) : ℂ) * v‖ < 1 := by
    rw [norm_mul, norm_neg, hv, mul_one, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr ha0.le)]
    exact inv_lt_one_of_one_lt₀ ha
  have hlt2 : ‖-((a⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) v‖ < 1 := by
    rw [norm_mul, norm_neg, RCLike.norm_conj, hv, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr ha0.le)]
    exact inv_lt_one_of_one_lt₀ ha
  have hg1 := (hasSum_geometric_of_norm_lt_one hlt1).mul_left (-((a⁻¹ : ℝ) : ℂ) * v)
  have hg2 := (hasSum_geometric_of_norm_lt_one hlt2).mul_left (-((a⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) v)
  have hsum_c := hg1.add hg2
  have hd1 : (1 - -((a⁻¹ : ℝ) : ℂ) * v) = 1 + ((a⁻¹ : ℝ) : ℂ) * v := by ring
  have hd2 : (1 - -((a⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) v) = 1 + ((a⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) v := by ring
  rw [hd1, hd2] at hsum_c
  have hval_eq : ((-((a⁻¹ : ℝ) : ℂ) * v) * (1 + ((a⁻¹ : ℝ) : ℂ) * v)⁻¹ +
      (-((a⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) v) * (1 + ((a⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) v)⁻¹) =
      (((a ^ 2 - 1) / ‖(a : ℂ) + v‖ ^ 2 - 1 : ℝ) : ℂ) := by
    have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0.ne'
    have hden1 : (a : ℂ) + v ≠ 0 := fun h0 => by
      have hv' : v = -(a : ℂ) := by linear_combination h0
      rw [hv', norm_neg, Complex.norm_real, Real.norm_of_nonneg ha0.le] at hv; linarith
    have hden2 : (a : ℂ) + (starRingEnd ℂ) v ≠ 0 := by
      have hc : (a : ℂ) + (starRingEnd ℂ) v = (starRingEnd ℂ) ((a : ℂ) + v) := by
        simp [map_add, Complex.conj_ofReal]
      rw [hc]; exact map_ne_zero_iff _ (RingHom.injective _) |>.mpr hden1
    have hd1_ne : 1 + ((a⁻¹ : ℝ) : ℂ) * v ≠ 0 := fun h0 => hden1 (by
      have hm := congrArg ((a : ℂ) * ·) h0; push_cast at hm; field_simp [haC] at hm
      linear_combination hm)
    have hd2_ne : 1 + ((a⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) v ≠ 0 := fun h0 => hden2 (by
      have hm := congrArg ((a : ℂ) * ·) h0; push_cast at hm; field_simp [haC] at hm
      linear_combination hm)
    have hr1 : (-((a⁻¹ : ℝ) : ℂ) * v) * (1 + ((a⁻¹ : ℝ) : ℂ) * v)⁻¹ = -v / ((a : ℂ) + v) := by
      push_cast; rw [eq_div_iff hden1]; field_simp [haC, hd1_ne]
    have hr2 : (-((a⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) v) *
        (1 + ((a⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) v)⁻¹ = -(starRingEnd ℂ) v / ((a : ℂ) + (starRingEnd ℂ) v) := by
      push_cast; rw [eq_div_iff hden2]; field_simp [haC, hd2_ne]
    have hvv : v * (starRingEnd ℂ) v = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv, one_pow, Complex.ofReal_one]
    have hnorm_sq : (‖(a : ℂ) + v‖ : ℂ) ^ 2 = ((a : ℂ) + v) * ((a : ℂ) + (starRingEnd ℂ) v) := by
      have hc : (a : ℂ) + (starRingEnd ℂ) v = (starRingEnd ℂ) ((a : ℂ) + v) := by
        simp [map_add, Complex.conj_ofReal]
      rw [hc, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    rw [hr1, hr2]
    push_cast
    rw [hnorm_sq]
    field_simp [hden1, hden2]
    linear_combination -hvv
  rw [hval_eq] at hsum_c
  have hsum_re := Complex.reCLM.hasSum hsum_c
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hsum_re
  refine hsum_re.congr_fun fun k => ?_
  have hp1 : (-((a⁻¹ : ℝ) : ℂ) * v) * (-((a⁻¹ : ℝ) : ℂ) * v) ^ k =
      (((-1 : ℝ) ^ (k + 1) * (a⁻¹) ^ (k + 1) : ℝ) : ℂ) * v ^ (k + 1) := by
    push_cast
    rw [show -(a : ℂ)⁻¹ * v = (-1 : ℂ) * (a : ℂ)⁻¹ * v by ring,
      mul_pow, mul_pow, pow_succ, pow_succ, pow_succ]
    ring
  have hp2 : (-((a⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) v) * (-((a⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) v) ^ k =
      (((-1 : ℝ) ^ (k + 1) * (a⁻¹) ^ (k + 1) : ℝ) : ℂ) * ((starRingEnd ℂ) v) ^ (k + 1) := by
    push_cast
    rw [show -(a : ℂ)⁻¹ * (starRingEnd ℂ) v = (-1 : ℂ) * (a : ℂ)⁻¹ * (starRingEnd ℂ) v by ring,
      mul_pow, mul_pow, pow_succ, pow_succ, pow_succ]
    ring
  rw [hp1, hp2, ← mul_add, Complex.re_ofReal_mul]

/-- Explicit positive minimum delay separation between `{0, 4 log p, 2 log(p q)}` and all multiples
`2 (k + 1) log p` (aside from the resonant prime-square hit `4 log p = 2 · 2 log p`). -/
def mixedPrimeGap (p q : ℕ) : ℝ :=
  2 * min (Real.log p)
    (min (Real.log (((p * q : ℕ) + 1 : ℝ) / (p * q : ℕ)))
         (Real.log (((q : ℕ) + 1 : ℝ) / q)))

theorem mixedPrimeGap_pos {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    0 < mixedPrimeGap p q := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpq0 : (0 : ℝ) < (p * q : ℕ) := by exact_mod_cast mul_pos hp.pos hq.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hl1 : 0 < Real.log p := Real.log_pos hp1
  have hl2 : 0 < Real.log (((p * q : ℕ) + 1 : ℝ) / (p * q : ℕ)) :=
    Real.log_pos ((one_lt_div hpq0).mpr (by linarith))
  have hl3 : 0 < Real.log (((q : ℕ) + 1 : ℝ) / q) :=
    Real.log_pos ((one_lt_div hq0).mpr (by linarith))
  unfold mixedPrimeGap
  exact mul_pos (by norm_num) (lt_min hl1 (lt_min hl2 hl3))

private theorem nat_log_sep {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hne : m ≠ n) :
    Real.log (((m : ℕ) + 1 : ℝ) / m) ≤ |Real.log m - Real.log n| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmn : (m : ℝ) < n := by exact_mod_cast hlt
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr (Real.log_lt_log hm0 hmn)),
      ← Real.log_div hn0.ne' hm0.ne']
    exact Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_right (by exact_mod_cast hlt) hm0.le)
  · have hnm : (n : ℝ) < m := by exact_mod_cast hgt
    rw [abs_of_pos (sub_pos.mpr (Real.log_lt_log hn0 hnm)), ← Real.log_div hm0.ne' hn0.ne']
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ hm0 hn0]
    have hn_le : (n : ℝ) ≤ (m : ℝ) - 1 := by
      have h1 : n + 1 ≤ m := hgt
      have h2 : (n : ℝ) + 1 ≤ m := by exact_mod_cast h1
      linarith
    nlinarith

/-- Predeclared three-channel delays `(0, 4 log p, 2 log(p q))` for prompt, prime-square, and mixed
two-prime paths. -/
def threeChannelDelays (p q : ℕ) (i : Fin 3) : ℝ :=
  if i.val = 0 then 0 else if i.val = 1 then 4 * Real.log p else 2 * Real.log ((p * q : ℕ))

/-- Predeclared three-channel complex weights `(c₀, c_{p²}, c_{pq})`. -/
def threeChannelWeights (c₀ c_sq c_pq : ℂ) (i : Fin 3) : ℂ :=
  if i.val = 0 then c₀ else if i.val = 1 then c_sq else c_pq

/-- Predeclared three-component mixed pulse
`c₀ h₀(S) + c_{p²} h₀(S - 4 log p) + c_{pq} h₀(S - 2 log(p q))`. -/
def threeChannelMixedPulse (p q : ℕ) (c₀ c_sq c_pq : ℂ) (h₀ : CompactPulse) : CompactPulse :=
  mixedPulse Finset.univ (threeChannelWeights c₀ c_sq c_pq)
    (fun i : Fin 3 => h₀.delay (threeChannelDelays p q i))

private theorem delay_overlap_eq_zero (h₀ : CompactPulse) {S₀ A B : ℝ}
    (hS₀ : ∀ s : ℝ, S₀ < |s| → h₀ s = 0) (hsep : 2 * S₀ < |A - B|) :
    (∫ S : ℝ, h₀ (S - A) * (starRingEnd ℂ) (h₀ (S - B))) = 0 := by
  refine integral_eq_zero_of_ae (Eventually.of_forall fun S => ?_)
  by_cases hA : S₀ < |S - A|
  · simp [hS₀ (S - A) hA]
  · have hB : S₀ < |S - B| := by
      have hle : |A - B| ≤ |S - B| + |S - A| := by
        calc |A - B| = |(S - B) - (S - A)| := by ring_nf
          _ ≤ |S - B| + |S - A| := abs_sub _ _
      linarith [not_lt.mp hA]
    simp [hS₀ (S - B) hB]

private theorem delay_overlap_self (h₀ : CompactPulse) (A : ℝ) :
    (∫ S : ℝ, h₀ (S - A) * (starRingEnd ℂ) (h₀ (S - A))) =
      ((∫ u : ℝ, ‖h₀ u‖ ^ 2 : ℝ) : ℂ) := by
  rw [integral_sub_right_eq_self (μ := volume) (fun u : ℝ => h₀ u * (starRingEnd ℂ) (h₀ u)) A,
    ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem threeChannel_autocorr_expand (p q : ℕ) (c₀ c_sq c_pq : ℂ)
    (h₀ : CompactPulse) (d : ℝ) :
    (∫ S : ℝ, threeChannelMixedPulse p q c₀ c_sq c_pq h₀ (S - d) *
        (starRingEnd ℂ) (threeChannelMixedPulse p q c₀ c_sq c_pq h₀ S)) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (threeChannelWeights c₀ c_sq c_pq i *
          (starRingEnd ℂ) (threeChannelWeights c₀ c_sq c_pq j)) *
        ∫ S : ℝ, h₀ (S - (threeChannelDelays p q i + d)) *
          (starRingEnd ℂ) (h₀ (S - threeChannelDelays p q j)) := by
  set w : Fin 3 → ℂ := threeChannelWeights c₀ c_sq c_pq
  set L : Fin 3 → ℝ := threeChannelDelays p q
  have hpt : ∀ S : ℝ, threeChannelMixedPulse p q c₀ c_sq c_pq h₀ (S - d) *
      (starRingEnd ℂ) (threeChannelMixedPulse p q c₀ c_sq c_pq h₀ S) =
      ∑ i : Fin 3, ∑ j : Fin 3, (w i * (starRingEnd ℂ) (w j)) *
        (h₀ (S - (L i + d)) * (starRingEnd ℂ) (h₀ (S - L j))) := by
    intro S
    simp only [threeChannelMixedPulse, mixedPulse_apply, CompactPulse.delay_apply, map_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, show S - d - L i = S - (L i + d) by ring]
    ring
  have hint_ij : ∀ i j : Fin 3, Integrable fun S : ℝ =>
      (w i * (starRingEnd ℂ) (w j)) * (h₀ (S - (L i + d)) * (starRingEnd ℂ) (h₀ (S - L j))) := by
    intro i j
    have hc : Continuous fun S : ℝ =>
        h₀ (S - (L i + d)) * (starRingEnd ℂ) (h₀ (S - L j)) :=
      (h₀.continuous_toFun.comp (continuous_id.sub continuous_const)).mul
        (continuous_conj.comp (h₀.continuous_toFun.comp (continuous_id.sub continuous_const)))
    have hcs : HasCompactSupport fun S : ℝ =>
        h₀ (S - (L i + d)) * (starRingEnd ℂ) (h₀ (S - L j)) :=
      ((h₀.delay (L i + d)).compact).mul_right
    exact (hc.integrable_of_hasCompactSupport hcs).const_mul _
  simp_rw [hpt]
  rw [integral_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => hint_ij i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum Finset.univ fun j _ => hint_ij i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]

private theorem sep_nonresonant_pairs {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (k : ℕ) {d : ℝ} (hd : |d| = 2 * ((k + 1 : ℕ) : ℝ) * Real.log p)
    {i j : Fin 3} (hnot : ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))) :
    mixedPrimeGap p q ≤ |(threeChannelDelays p q i + d) - threeChannelDelays p q j| := by
  have htri : |(|threeChannelDelays p q i - threeChannelDelays p q j| -
      2 * ((k + 1 : ℕ) : ℝ) * Real.log p)| ≤
      |(threeChannelDelays p q i + d) - threeChannelDelays p q j| := by
    calc |(|threeChannelDelays p q i - threeChannelDelays p q j| -
            2 * ((k + 1 : ℕ) : ℝ) * Real.log p)|
        = |(|threeChannelDelays p q i - threeChannelDelays p q j| - |-d|)| := by rw [abs_neg, hd]
      _ ≤ |(threeChannelDelays p q i - threeChannelDelays p q j) - (-d)| :=
          abs_abs_sub_abs_le_abs_sub _ _
      _ = |(threeChannelDelays p q i + d) - threeChannelDelays p q j| := by ring_nf
  refine le_trans ?_ htri
  have hp_log : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hg1 : mixedPrimeGap p q ≤ 2 * Real.log p := by
    unfold mixedPrimeGap; linarith [min_le_left (Real.log p)
      (min (Real.log (((p * q : ℕ) + 1 : ℝ) / (p * q : ℕ))) (Real.log (((q : ℕ) + 1 : ℝ) / q)))]
  have hg2 : mixedPrimeGap p q ≤ 2 * Real.log (((p * q : ℕ) + 1 : ℝ) / (p * q : ℕ)) := by
    unfold mixedPrimeGap
    linarith [min_le_right (Real.log p)
      (min (Real.log (((p * q : ℕ) + 1 : ℝ) / (p * q : ℕ))) (Real.log (((q : ℕ) + 1 : ℝ) / q))),
      min_le_left (Real.log (((p * q : ℕ) + 1 : ℝ) / (p * q : ℕ)))
        (Real.log (((q : ℕ) + 1 : ℝ) / q))]
  have hg3 : mixedPrimeGap p q ≤ 2 * Real.log (((q : ℕ) + 1 : ℝ) / q) := by
    unfold mixedPrimeGap
    linarith [min_le_right (Real.log p)
      (min (Real.log (((p * q : ℕ) + 1 : ℝ) / (p * q : ℕ))) (Real.log (((q : ℕ) + 1 : ℝ) / q))),
      min_le_right (Real.log (((p * q : ℕ) + 1 : ℝ) / (p * q : ℕ)))
        (Real.log (((q : ℕ) + 1 : ℝ) / q))]
  have h02 : mixedPrimeGap p q ≤
      |2 * Real.log ((p * q : ℕ)) - 2 * ((k + 1 : ℕ) : ℝ) * Real.log p| := by
    have hne_pq : p * q ≠ p ^ (k + 1) := fun heq => by
      have hdvd : q ∣ p ^ (k + 1) := ⟨p, by rw [← heq, mul_comm]⟩
      exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd)).symm
    have hl_pow : ((k + 1 : ℕ) : ℝ) * Real.log p = Real.log ((p ^ (k + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]
    have hsep := nat_log_sep (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne_zero hq.ne_zero))
      (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)) hne_pq
    rw [mul_assoc 2 ((k + 1 : ℕ) : ℝ), hl_pow,
      show |2 * Real.log ((p * q : ℕ)) - 2 * Real.log ((p ^ (k + 1) : ℕ) : ℝ)| =
        2 * |Real.log ((p * q : ℕ)) - Real.log ((p ^ (k + 1) : ℕ) : ℝ)| by
        rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]]
    linarith
  have h12 : mixedPrimeGap p q ≤
      |(|4 * Real.log p - 2 * Real.log ((p * q : ℕ))| - 2 * ((k + 1 : ℕ) : ℝ) * Real.log p)| := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hq_log : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
    have hl_mul : Real.log ((p * q : ℕ) : ℝ) = Real.log p + Real.log q := by
      rw [Nat.cast_mul, Real.log_mul hp0.ne' hq0.ne']
    rw [hl_mul, show 4 * Real.log p - 2 * (Real.log p + Real.log q) =
      2 * (Real.log p - Real.log q) by ring, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · have hpqR : (p : ℝ) < q := by exact_mod_cast hlt
      rw [abs_sub_comm (Real.log p) (Real.log q),
        abs_of_pos (sub_pos.mpr (Real.log_lt_log hp0 hpqR)),
        show 2 * (Real.log q - Real.log p) - 2 * ((k + 1 : ℕ) : ℝ) * Real.log p =
          2 * (Real.log q - ((k + 2 : ℕ) : ℝ) * Real.log p) by push_cast; ring,
        abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hl_pow : ((k + 2 : ℕ) : ℝ) * Real.log p = Real.log ((p ^ (k + 2) : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
      have hne_q : q ≠ p ^ (k + 2) := fun heq => by
        have hcomp : ¬ (p ^ (k + 2)).Prime := by
          rw [pow_succ]
          exact Nat.not_prime_mul (pow_ne_zero (k + 1) hp.ne_zero |> fun _ =>
            ne_of_gt (one_lt_pow₀ hp.one_lt (by omega))) hp.ne_one
        exact hcomp (heq ▸ hq)
      have hsep := nat_log_sep hq.one_le
        (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)) hne_q
      rw [hl_pow]
      linarith
    · have hqpR : (q : ℝ) < p := by exact_mod_cast hgt
      rw [abs_of_pos (sub_pos.mpr (Real.log_lt_log hq0 hqpR))]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hneg : 2 * (Real.log p - Real.log q) - 2 * ((k + 1 : ℕ) : ℝ) * Real.log p =
          -(2 * Real.log q + 2 * (k : ℝ) * Real.log p) := by push_cast; ring
      have hq_ge : Real.log (((q : ℕ) + 1 : ℝ) / q) ≤ Real.log q := by
        refine Real.log_le_log (by positivity) ?_
        rw [div_le_iff₀ hq0]
        have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
        nlinarith
      rw [hneg, abs_neg, abs_of_pos (by positivity)]
      linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 * k) hp_log.le]
  have hk_pos : 0 < 2 * ((k + 1 : ℕ) : ℝ) * Real.log p := by positivity
  have hpq_pos : 0 < 2 * Real.log ((p * q : ℕ)) := by
    have h1pq : 1 < p * q := one_lt_mul_of_lt_of_le hp.one_lt hq.one_le
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast h1pq))
  fin_cases i <;> fin_cases j
  · simp only [threeChannelDelays, ↓reduceIte, sub_self, abs_zero, zero_sub, abs_neg,
      abs_of_pos hk_pos]
    have hk1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    nlinarith
  · exact absurd (Or.inl ⟨rfl, rfl⟩) hnot
  · simp only [threeChannelDelays, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
      ↓reduceIte, zero_sub, abs_neg, abs_of_pos hpq_pos]
    exact h02
  · exact absurd (Or.inr ⟨rfl, rfl⟩) hnot
  · simp only [threeChannelDelays, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte,
      sub_self, abs_zero, zero_sub, abs_neg, abs_of_pos hk_pos]
    have hk1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    nlinarith
  · simp only [threeChannelDelays, show (1 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 0 by decide,
      show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
    exact h12
  · simp only [threeChannelDelays, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
      ↓reduceIte, sub_zero, abs_of_pos hpq_pos]
    exact h02
  · simp only [threeChannelDelays, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
      show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
    rw [abs_sub_comm (2 * Real.log ((p * q : ℕ))) (4 * Real.log p)]
    exact h12
  · simp only [threeChannelDelays, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
      ↓reduceIte, sub_self, abs_zero, zero_sub, abs_neg, abs_of_pos hk_pos]
    have hk1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    nlinarith

/-- **Exact Mixed-Pulse Excess Group-Delay Formula (Retaining All Interference Terms).**
For distinct primes `p ≠ q`, `1 < r`, `1 < u`, `r * u = p`, and any compact pulse `h₀` supported in
`[-S₀, S₀]` with `2 * S₀ < mixedPrimeGap p q`, the three-component mixed pulse
`h_mix = c₀ h₀(S) + c_{p²} h₀(S - 4 log p) + c_{pq} h₀(S - 2 log(p q))` satisfies
`excessPulseGroupDelay p r u h_mix = (2 log p / π) (‖c₀‖² + ‖c_{p²}‖² + ‖c_{pq}‖² + (r⁻² + u⁻²) Re(c₀ conj c_{p²})) ∫ ‖h₀‖²`. -/
theorem excessPulseGroupDelay_threeChannelMixedPulse {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {r u S₀ : ℝ} (hr : 1 < r) (hu : 1 < u) (hru : r * u = p)
    (c₀ c_sq c_pq : ℂ) (h₀ : CompactPulse) (hS₀ : ∀ s : ℝ, S₀ < |s| → h₀ s = 0)
    (hgap : 2 * S₀ < mixedPrimeGap p q) :
    excessPulseGroupDelay p r u (threeChannelMixedPulse p q c₀ c_sq c_pq h₀) =
      (2 * Real.log p / Real.pi) *
        (‖c₀‖ ^ 2 + ‖c_sq‖ ^ 2 + ‖c_pq‖ ^ 2 +
          ((r⁻¹) ^ 2 + (u⁻¹) ^ 2) * (c₀ * (starRingEnd ℂ) c_sq).re) *
        ∫ S : ℝ, ‖h₀ S‖ ^ 2 := by
  set h := threeChannelMixedPulse p q c₀ c_sq c_pq h₀
  set I₀ : ℝ := ∫ S : ℝ, ‖h₀ S‖ ^ 2
  have hp_log : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hg1 : mixedPrimeGap p q ≤ 2 * Real.log p := by
    unfold mixedPrimeGap; linarith [min_le_left (Real.log p)
      (min (Real.log (((p * q : ℕ) + 1 : ℝ) / (p * q : ℕ))) (Real.log (((q : ℕ) + 1 : ℝ) / q)))]
  -- 1. `d = 0` norm-square evaluation of `h`
  have hnorm_h : (∫ S : ℝ, ‖h S‖ ^ 2) = (‖c₀‖ ^ 2 + ‖c_sq‖ ^ 2 + ‖c_pq‖ ^ 2) * I₀ := by
    have hc_eq : ((∫ S : ℝ, ‖h S‖ ^ 2 : ℝ) : ℂ) = ∫ S : ℝ, h (S - 0) * (starRingEnd ℂ) (h S) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun S => ?_)
      dsimp only
      rw [sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [threeChannel_autocorr_expand] at hc_eq
    have h4p_pos : 0 < 4 * Real.log p := by positivity
    have hoff : ∀ i j : Fin 3, i ≠ j →
        (∫ S : ℝ, h₀ (S - threeChannelDelays p q i) *
          (starRingEnd ℂ) (h₀ (S - threeChannelDelays p q j))) = 0 := by
      intro i j hij
      have h0_add : ∀ S : ℝ, h₀ (S - threeChannelDelays p q i) =
          h₀ (S - (threeChannelDelays p q i + 0)) := fun S => by rw [add_zero]
      simp_rw [h0_add]
      refine delay_overlap_eq_zero h₀ hS₀ (hgap.trans_le ?_)
      rw [add_zero]
      fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
      · simp only [threeChannelDelays, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, zero_sub,
          abs_neg, abs_of_pos h4p_pos]; linarith
      · have hpq1 : (p : ℝ) ≤ (p * q : ℕ) := by
          exact_mod_cast Nat.le_mul_of_pos_right p hq.pos
        have hl := Real.log_le_log (by exact_mod_cast hp.pos) hpq1
        simp only [threeChannelDelays, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
          ↓reduceIte, zero_sub, abs_neg]
        rw [abs_of_pos (mul_pos (by norm_num) (lt_of_lt_of_le hp_log hl))]; linarith
      · simp only [threeChannelDelays, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, sub_zero,
          abs_of_pos h4p_pos]; linarith
      · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
        have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
        have hg3 : mixedPrimeGap p q ≤ 2 * Real.log (((q : ℕ) + 1 : ℝ) / q) := by
          unfold mixedPrimeGap
          linarith [min_le_right (Real.log p)
            (min (Real.log (((p * q : ℕ) + 1 : ℝ) / (p * q : ℕ))) (Real.log (((q : ℕ) + 1 : ℝ) / q))),
            min_le_right (Real.log (((p * q : ℕ) + 1 : ℝ) / (p * q : ℕ)))
              (Real.log (((q : ℕ) + 1 : ℝ) / q))]
        have hsep := nat_log_sep hq.one_le hp.one_le hpq.symm
        simp only [threeChannelDelays, show (1 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 0 by decide,
          show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
        rw [Nat.cast_mul, Real.log_mul hp0.ne' hq0.ne',
          show 4 * Real.log p - 2 * (Real.log p + Real.log q) =
            -2 * (Real.log q - Real.log p) by ring,
          abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      · have hpq1 : (p : ℝ) ≤ (p * q : ℕ) := by
          exact_mod_cast Nat.le_mul_of_pos_right p hq.pos
        have hl := Real.log_le_log (by exact_mod_cast hp.pos) hpq1
        simp only [threeChannelDelays, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
          ↓reduceIte, sub_zero]
        rw [abs_of_pos (mul_pos (by norm_num) (lt_of_lt_of_le hp_log hl))]; linarith
      · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
        have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
        have hg3 : mixedPrimeGap p q ≤ 2 * Real.log (((q : ℕ) + 1 : ℝ) / q) := by
          unfold mixedPrimeGap
          linarith [min_le_right (Real.log p)
            (min (Real.log (((p * q : ℕ) + 1 : ℝ) / (p * q : ℕ))) (Real.log (((q : ℕ) + 1 : ℝ) / q))),
            min_le_right (Real.log (((p * q : ℕ) + 1 : ℝ) / (p * q : ℕ)))
              (Real.log (((q : ℕ) + 1 : ℝ) / q))]
        have hsep := nat_log_sep hq.one_le hp.one_le hpq.symm
        simp only [threeChannelDelays, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
          show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
        rw [Nat.cast_mul, Real.log_mul hp0.ne' hq0.ne',
          show 2 * (Real.log p + Real.log q) - 4 * Real.log p =
            2 * (Real.log q - Real.log p) by ring,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
    simp only [add_zero] at hc_eq
    rw [Fin.sum_univ_three] at hc_eq
    simp only [Fin.sum_univ_three, hoff 0 1 (by decide), hoff 0 2 (by decide),
      hoff 1 0 (by decide), hoff 1 2 (by decide), hoff 2 0 (by decide), hoff 2 1 (by decide),
      mul_zero, add_zero, zero_add, delay_overlap_self h₀, threeChannelWeights,
      Fin.val_zero, Fin.val_one, Fin.val_two, show (1 : ℕ) ≠ 0 by decide,
      show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte] at hc_eq
    have h1 := congrArg Complex.re hc_eq
    simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_mul] at h1
    change ∫ S : ℝ, ‖h S‖ ^ 2 = (‖c₀‖ ^ 2 * I₀ + ‖c_sq‖ ^ 2 * I₀) + ‖c_pq‖ ^ 2 * I₀ at h1
    rw [h1]; ring
  -- 2. Harmonic integral evaluation at `k : ℕ`
  have hharm_val : ∀ k : ℕ,
      (∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 *
        (((p : ℂ) ^ (-2 * ((ξ : ℂ) * I))) ^ (k + 1) +
          ((starRingEnd ℂ) ((p : ℂ) ^ (-2 * ((ξ : ℂ) * I)))) ^ (k + 1)).re) =
      if k = 1 then (1 / Real.pi) * (c₀ * (starRingEnd ℂ) c_sq).re * I₀ else 0 := by
    intro k
    set d_k : ℝ := 2 * ((k + 1 : ℕ) : ℝ) * Real.log p
    have hd_abs : |d_k| = 2 * ((k + 1 : ℕ) : ℝ) * Real.log p :=
      abs_of_pos (by positivity)
    have hv_pow : ∀ ξ : ℝ,
        ((p : ℂ) ^ (-2 * ((ξ : ℂ) * I))) ^ (k + 1) =
          Complex.exp (-(I * (ξ : ℂ) * (d_k : ℂ))) ∧
        ((starRingEnd ℂ) ((p : ℂ) ^ (-2 * ((ξ : ℂ) * I)))) ^ (k + 1) =
          Complex.exp (-(I * (ξ : ℂ) * ((-d_k : ℝ) : ℂ))) := by
      intro ξ
      have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hb : (p : ℂ) ^ (-2 * ((ξ : ℂ) * I)) =
          Complex.exp (-(I * (ξ : ℂ) * (2 * Real.log p : ℂ))) := by
        rw [Complex.cpow_def_of_ne_zero hpC, ← Complex.natCast_log]
        congr 1; ring
      constructor
      · rw [hb, ← Complex.exp_nat_mul]; congr 1; simp only [d_k]; push_cast; ring
      · rw [hb, ← Complex.exp_conj, ← Complex.exp_nat_mul]
        congr 1
        simp only [d_k, map_neg, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
        push_cast; ring
    have hint_cexp : ∀ d : ℝ, Integrable fun ξ : ℝ =>
        ((‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 : ℝ) : ℂ) * Complex.exp (-(I * (ξ : ℂ) * (d : ℂ))) := by
      intro d
      have hcont : Continuous fun ξ : ℝ =>
          ((‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 : ℝ) : ℂ) * Complex.exp (-(I * (ξ : ℂ) * (d : ℂ))) :=
        (Complex.continuous_ofReal.comp ((h.differentiable_amplitude.continuous.comp
          Complex.continuous_ofReal).norm.pow 2)).mul (by fun_prop)
      refine (integrable_norm_sq_pulseAmplitude h).mono' hcont.aestronglyMeasurable
        (Eventually.of_forall fun ξ => le_of_eq ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), Complex.norm_exp]
      have hre : (-(I * (ξ : ℂ) * (d : ℂ))).re = 0 := by simp
      rw [hre, Real.exp_zero, mul_one]
    have hlhs_eq : (∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 *
        (((p : ℂ) ^ (-2 * ((ξ : ℂ) * I))) ^ (k + 1) +
          ((starRingEnd ℂ) ((p : ℂ) ^ (-2 * ((ξ : ℂ) * I)))) ^ (k + 1)).re) =
        (1 / (2 * Real.pi)) *
          ((∫ S : ℝ, h (S - d_k) * (starRingEnd ℂ) (h S)) +
            ∫ S : ℝ, h (S - (-d_k)) * (starRingEnd ℂ) (h S)).re := by
      have h1 := integral_norm_sq_pulseAmplitude_mul_cexp h d_k
      have h2 := integral_norm_sq_pulseAmplitude_mul_cexp h (-d_k)
      have hsum_c : (2 * (Real.pi : ℂ)) * (∫ ξ : ℝ,
          ((‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 : ℝ) : ℂ) * Complex.exp (-(I * (ξ : ℂ) * (d_k : ℂ))) +
          ((‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 : ℝ) : ℂ) * Complex.exp (-(I * (ξ : ℂ) * ((-d_k : ℝ) : ℂ)))) =
          (∫ S : ℝ, h (S - d_k) * (starRingEnd ℂ) (h S)) +
            ∫ S : ℝ, h (S - (-d_k)) * (starRingEnd ℂ) (h S) := by
        rw [integral_add (hint_cexp d_k) (hint_cexp (-d_k)), mul_add, h1, h2]
      have hre_comm := Complex.reCLM.integral_comp_comm ((hint_cexp d_k).add (hint_cexp (-d_k)))
      simp only [Complex.reCLM_apply, Pi.add_apply] at hre_comm
      have hre_sum := congrArg Complex.re hsum_c
      rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.re_ofReal_mul] at hre_sum
      have hint_eq : (∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 *
          (((p : ℂ) ^ (-2 * ((ξ : ℂ) * I))) ^ (k + 1) +
            ((starRingEnd ℂ) ((p : ℂ) ^ (-2 * ((ξ : ℂ) * I)))) ^ (k + 1)).re) =
          (∫ x : ℝ, (((‖pulseAmplitude h (x : ℂ)‖ ^ 2 : ℝ) : ℂ) *
              Complex.exp (-(I * (x : ℂ) * (d_k : ℂ))) +
            ((‖pulseAmplitude h (x : ℂ)‖ ^ 2 : ℝ) : ℂ) *
              Complex.exp (-(I * (x : ℂ) * ((-d_k : ℝ) : ℂ)))).re) := by
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        dsimp only
        rw [(hv_pow ξ).1, (hv_pow ξ).2, ← mul_add, Complex.re_ofReal_mul]
      rw [hint_eq, hre_comm, ← hre_sum, one_div,
        inv_mul_cancel_left₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
    rw [hlhs_eq]
    by_cases hk1 : k = 1
    · subst hk1
      rw [if_pos rfl]
      have hd1 : d_k = 4 * Real.log p := by dsimp only [d_k]; push_cast; ring
      have h_plus : (∫ S : ℝ, h (S - d_k) * (starRingEnd ℂ) (h S)) =
          c₀ * (starRingEnd ℂ) c_sq * (I₀ : ℂ) := by
        rw [threeChannel_autocorr_expand]
        have hz_ij : ∀ i j : Fin 3, ¬ (i = 0 ∧ j = 1) →
            (∫ S : ℝ, h₀ (S - (threeChannelDelays p q i + d_k)) *
              (starRingEnd ℂ) (h₀ (S - threeChannelDelays p q j))) = 0 := by
          intro i j hij
          refine delay_overlap_eq_zero h₀ hS₀ (hgap.trans_le ?_)
          by_cases h10 : i = 1 ∧ j = 0
          · rcases h10 with ⟨rfl, rfl⟩
            simp only [threeChannelDelays, Fin.val_zero, Fin.val_one, show (1 : ℕ) ≠ 0 by decide,
              ↓reduceIte, hd1, sub_zero]
            rw [show 4 * Real.log p + 4 * Real.log p = 8 * Real.log p by ring,
              abs_of_pos (mul_pos (by norm_num) hp_log)]
            linarith
          · exact sep_nonresonant_pairs hp hq hpq 1 hd_abs (not_or.mpr ⟨hij, h10⟩)
        rw [Fin.sum_univ_three]
        simp only [Fin.sum_univ_three, hz_ij 0 0 (by decide), hz_ij 0 2 (by decide),
          hz_ij 1 0 (by decide), hz_ij 1 1 (by decide), hz_ij 1 2 (by decide),
          hz_ij 2 0 (by decide), hz_ij 2 1 (by decide), hz_ij 2 2 (by decide),
          mul_zero, add_zero, zero_add]
        simp only [threeChannelDelays, threeChannelWeights, Fin.val_zero, Fin.val_one,
          show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, hd1, zero_add, delay_overlap_self h₀]
        rfl
      have h_minus : (∫ S : ℝ, h (S - (-d_k)) * (starRingEnd ℂ) (h S)) =
          c_sq * (starRingEnd ℂ) c₀ * (I₀ : ℂ) := by
        rw [threeChannel_autocorr_expand]
        have hd_neg_abs : |-d_k| = 2 * ((1 + 1 : ℕ) : ℝ) * Real.log p := by rw [abs_neg]; exact hd_abs
        have hz_ij : ∀ i j : Fin 3, ¬ (i = 1 ∧ j = 0) →
            (∫ S : ℝ, h₀ (S - (threeChannelDelays p q i + (-d_k))) *
              (starRingEnd ℂ) (h₀ (S - threeChannelDelays p q j))) = 0 := by
          intro i j hij
          refine delay_overlap_eq_zero h₀ hS₀ (hgap.trans_le ?_)
          by_cases h01 : i = 0 ∧ j = 1
          · rcases h01 with ⟨rfl, rfl⟩
            simp only [threeChannelDelays, Fin.val_zero, Fin.val_one, show (1 : ℕ) ≠ 0 by decide,
              ↓reduceIte, hd1]
            rw [show 0 + -(4 * Real.log p) - 4 * Real.log p = -(8 * Real.log p) by ring,
              abs_neg, abs_of_pos (mul_pos (by norm_num) hp_log)]
            linarith
          · exact sep_nonresonant_pairs hp hq hpq 1 hd_neg_abs (not_or.mpr ⟨h01, hij⟩)
        rw [Fin.sum_univ_three]
        simp only [Fin.sum_univ_three, hz_ij 0 0 (by decide), hz_ij 0 1 (by decide),
          hz_ij 0 2 (by decide), hz_ij 1 1 (by decide), hz_ij 1 2 (by decide),
          hz_ij 2 0 (by decide), hz_ij 2 1 (by decide), hz_ij 2 2 (by decide),
          mul_zero, add_zero, zero_add]
        simp only [threeChannelDelays, threeChannelWeights, Fin.val_zero, Fin.val_one,
          show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, hd1, add_neg_cancel, delay_overlap_self h₀]
        rfl
      rw [h_plus, h_minus]
      have hconj_pair : c_sq * (starRingEnd ℂ) c₀ = (starRingEnd ℂ) (c₀ * (starRingEnd ℂ) c_sq) := by
        simp [map_mul, mul_comm]
      rw [hconj_pair, ← add_mul, Complex.re_mul_ofReal, Complex.add_re, Complex.conj_re]
      have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      ring
    · rw [if_neg hk1]
      have hzero_shift : ∀ d : ℝ, |d| = 2 * ((k + 1 : ℕ) : ℝ) * Real.log p →
          (∫ S : ℝ, h (S - d) * (starRingEnd ℂ) (h S)) = 0 := by
        intro d hd'
        rw [threeChannel_autocorr_expand]
        have hz_all : ∀ i j : Fin 3,
            (∫ S : ℝ, h₀ (S - (threeChannelDelays p q i + d)) *
              (starRingEnd ℂ) (h₀ (S - threeChannelDelays p q j))) = 0 := by
          intro i j
          refine delay_overlap_eq_zero h₀ hS₀ (hgap.trans_le ?_)
          by_cases h01 : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
          · have htri : |(|threeChannelDelays p q i - threeChannelDelays p q j| -
                2 * ((k + 1 : ℕ) : ℝ) * Real.log p)| ≤
                |(threeChannelDelays p q i + d) - threeChannelDelays p q j| := by
              calc |(|threeChannelDelays p q i - threeChannelDelays p q j| -
                      2 * ((k + 1 : ℕ) : ℝ) * Real.log p)|
                  = |(|threeChannelDelays p q i - threeChannelDelays p q j| - |-d|)| := by
                      rw [abs_neg, hd']
                _ ≤ |(threeChannelDelays p q i - threeChannelDelays p q j) - (-d)| :=
                    abs_abs_sub_abs_le_abs_sub _ _
                _ = |(threeChannelDelays p q i + d) - threeChannelDelays p q j| := by ring_nf
            refine le_trans ?_ htri
            have h4p_pos : 0 < 4 * Real.log p := by positivity
            have hdiff4 : |threeChannelDelays p q i - threeChannelDelays p q j| = 4 * Real.log p := by
              rcases h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · simp only [threeChannelDelays, Fin.val_zero, Fin.val_one, show (1 : ℕ) ≠ 0 by decide,
                  ↓reduceIte, zero_sub, abs_neg, abs_of_pos h4p_pos]
              · simp only [threeChannelDelays, Fin.val_zero, Fin.val_one, show (1 : ℕ) ≠ 0 by decide,
                  ↓reduceIte, sub_zero, abs_of_pos h4p_pos]
            rw [hdiff4, show 4 * Real.log p - 2 * ((k + 1 : ℕ) : ℝ) * Real.log p =
              2 * ((2 : ℝ) - ((k + 1 : ℕ) : ℝ)) * Real.log p by ring,
              abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hp_log]
            have hk_gap : (1 : ℝ) ≤ |(2 : ℝ) - ((k + 1 : ℕ) : ℝ)| := by
              rcases eq_or_ne k 0 with rfl | hk0
              · norm_num
              · have hk2 : 2 ≤ k := by omega
                have hk2R : (3 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hk2
                rw [abs_of_neg (by linarith)]; linarith
            nlinarith
          · exact sep_nonresonant_pairs hp hq hpq k hd' h01
        simp only [hz_all, mul_zero, Finset.sum_const_zero]
      rw [hzero_shift d_k hd_abs, hzero_shift (-d_k) (by rw [abs_neg]; exact hd_abs)]
      simp
  -- 3. Sum over `k : ℕ` via `hasSum_integral_of_summable_integral_norm`
  set FK : ℕ → ℝ → ℝ := fun k ξ =>
    ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 *
      (((-1 : ℝ) ^ (k + 1) * ((r⁻¹) ^ (k + 1) + (u⁻¹) ^ (k + 1))) *
        (((p : ℂ) ^ (-2 * ((ξ : ℂ) * I))) ^ (k + 1) +
          ((starRingEnd ℂ) ((p : ℂ) ^ (-2 * ((ξ : ℂ) * I)))) ^ (k + 1)).re) with hFK
  have hFK_int : ∀ k : ℕ, Integrable (FK k) := by
    intro k
    have hcont : Continuous (FK k) := by
      unfold FK
      have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hpow_c : Continuous fun ξ : ℝ => (p : ℂ) ^ (-2 * ((ξ : ℂ) * I)) := by
        have heq : (fun ξ : ℝ => (p : ℂ) ^ (-2 * ((ξ : ℂ) * I))) =
            fun ξ : ℝ => Complex.exp ((-2 * ((ξ : ℂ) * I)) * (Real.log p : ℂ)) := by
          funext ξ; rw [Complex.cpow_def_of_ne_zero hpC, ← Complex.natCast_log, mul_comm]
        rw [heq]; fun_prop
      exact ((h.differentiable_amplitude.continuous.comp Complex.continuous_ofReal).norm.pow 2).mul
        (continuous_const.mul (Complex.continuous_re.comp
          ((hpow_c.pow (k + 1)).add ((continuous_conj.comp hpow_c).pow (k + 1)))))
    refine ((integrable_norm_sq_pulseAmplitude h).const_mul
      (2 * ((r⁻¹) ^ (k + 1) + (u⁻¹) ^ (k + 1)))).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    simp only [hFK]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_pow,
      abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (add_nonneg (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans hr).le) _)
        (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans hu).le) _))]
    have hv1 : ‖(p : ℂ) ^ (-2 * ((ξ : ℂ) * I))‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp.pos,
        show (-2 * ((ξ : ℂ) * I)).re = 0 by simp, Real.rpow_zero]
    have hcos_le : |(((p : ℂ) ^ (-2 * ((ξ : ℂ) * I))) ^ (k + 1) +
        ((starRingEnd ℂ) ((p : ℂ) ^ (-2 * ((ξ : ℂ) * I)))) ^ (k + 1)).re| ≤ 2 := by
      refine (Complex.abs_re_le_norm _).trans ?_
      refine (norm_add_le _ _).trans ?_
      rw [norm_pow, norm_pow, RCLike.norm_conj, hv1, one_pow]; norm_num
    calc ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 *
            ((r⁻¹ ^ (k + 1) + u⁻¹ ^ (k + 1)) *
              |(((p : ℂ) ^ (-2 * ((ξ : ℂ) * I))) ^ (k + 1) +
                ((starRingEnd ℂ) ((p : ℂ) ^ (-2 * ((ξ : ℂ) * I)))) ^ (k + 1)).re|)
        ≤ ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 * ((r⁻¹ ^ (k + 1) + u⁻¹ ^ (k + 1)) * 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcos_le (by positivity)) (sq_nonneg _)
      _ = 2 * (r⁻¹ ^ (k + 1) + u⁻¹ ^ (k + 1)) * ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 := by ring
  have hFK_sum : Summable fun k : ℕ => ∫ ξ : ℝ, ‖FK k ξ‖ := by
    have hr0 : 0 ≤ r⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hr).le
    have hu0 : 0 ≤ u⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hu).le
    have hdom := (((summable_geometric_of_lt_one hr0 (inv_lt_one_of_one_lt₀ hr)).mul_left r⁻¹).add
      ((summable_geometric_of_lt_one hu0 (inv_lt_one_of_one_lt₀ hu)).mul_left u⁻¹)).mul_left
      (2 * ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2)
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun k => ?_) hdom
    have hpt_le : ∀ ξ : ℝ, ‖FK k ξ‖ ≤
        (2 * (r⁻¹ * (r⁻¹) ^ k + u⁻¹ * (u⁻¹) ^ k)) * ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 := by
      intro ξ
      simp only [hFK]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_pow,
        abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (add_nonneg (pow_nonneg hr0 _) (pow_nonneg hu0 _))]
      have hv1 : ‖(p : ℂ) ^ (-2 * ((ξ : ℂ) * I))‖ = 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hp.pos,
          show (-2 * ((ξ : ℂ) * I)).re = 0 by simp, Real.rpow_zero]
      have hcos_le : |(((p : ℂ) ^ (-2 * ((ξ : ℂ) * I))) ^ (k + 1) +
          ((starRingEnd ℂ) ((p : ℂ) ^ (-2 * ((ξ : ℂ) * I)))) ^ (k + 1)).re| ≤ 2 := by
        refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
        rw [norm_pow, norm_pow, RCLike.norm_conj, hv1, one_pow]; norm_num
      calc ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 *
              ((r⁻¹ ^ (k + 1) + u⁻¹ ^ (k + 1)) *
                |(((p : ℂ) ^ (-2 * ((ξ : ℂ) * I))) ^ (k + 1) +
                  ((starRingEnd ℂ) ((p : ℂ) ^ (-2 * ((ξ : ℂ) * I)))) ^ (k + 1)).re|)
          ≤ ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 * ((r⁻¹ ^ (k + 1) + u⁻¹ ^ (k + 1)) * 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcos_le (by positivity)) (sq_nonneg _)
        _ = (2 * (r⁻¹ * (r⁻¹) ^ k + u⁻¹ * (u⁻¹) ^ k)) * ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 := by
            rw [pow_succ' r⁻¹ k, pow_succ' u⁻¹ k]; ring
    calc ∫ ξ : ℝ, ‖FK k ξ‖
        ≤ ∫ ξ : ℝ, (2 * (r⁻¹ * (r⁻¹) ^ k + u⁻¹ * (u⁻¹) ^ k)) * ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 :=
          integral_mono (hFK_int k).norm ((integrable_norm_sq_pulseAmplitude h).const_mul _) hpt_le
      _ = (2 * ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2) * (r⁻¹ * (r⁻¹) ^ k + u⁻¹ * (u⁻¹) ^ k) := by
          rw [integral_const_mul]; ring
  have hHS_FK := hasSum_integral_of_summable_integral_norm hFK_int hFK_sum
  have hint_tsum_FK := integrable_tsum_of_summable_integral_norm hFK_int hFK_sum
  have hpt_density : ∀ ξ : ℝ,
      ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 *
        (boundaryGroupDelayDensity (PositiveEulerHorizon.reducedScattering p (r + u)) ξ -
          boundaryGroupDelayDensity modularReducedScattering ξ) =
      2 * Real.log p * (2 * ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 + ∑' k : ℕ, FK k ξ) := by
    intro ξ
    rw [twin_excess_groupDelayDensity_eq hp.one_lt hr hu hru ξ]
    have hv1 : ‖(p : ℂ) ^ (-2 * ((ξ : ℂ) * I))‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp.pos,
        show (-2 * ((ξ : ℂ) * I)).re = 0 by simp, Real.rpow_zero]
    have hpr := poisson_harmonic_hasSum hr hv1
    have hpu := poisson_harmonic_hasSum hu hv1
    have hpru := (hpr.add hpu).mul_left (‖pulseAmplitude h (ξ : ℂ)‖ ^ 2)
    have htsum_eq : (∑' k : ℕ, FK k ξ) =
        ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 *
          (((r ^ 2 - 1) / ‖(r : ℂ) + (p : ℂ) ^ (-2 * ((ξ : ℂ) * I))‖ ^ 2 - 1) +
            ((u ^ 2 - 1) / ‖(u : ℂ) + (p : ℂ) ^ (-2 * ((ξ : ℂ) * I))‖ ^ 2 - 1)) := by
      rw [← hpru.tsum_eq]
      exact tsum_congr fun k => by simp only [hFK]; ring
    rw [htsum_eq]
    ring
  rw [excessPulseGroupDelay, integral_congr_ae (Eventually.of_forall hpt_density),
    integral_const_mul, integral_add ((integrable_norm_sq_pulseAmplitude h).const_mul 2)
      hint_tsum_FK, integral_const_mul, ← hHS_FK.tsum_eq]
  have hFK_eval : ∀ k : ℕ, ∫ ξ : ℝ, FK k ξ =
      ((-1 : ℝ) ^ (k + 1) * ((r⁻¹) ^ (k + 1) + (u⁻¹) ^ (k + 1))) *
        if k = 1 then (1 / Real.pi) * (c₀ * (starRingEnd ℂ) c_sq).re * I₀ else 0 := by
    intro k
    have hrw : FK k = fun ξ : ℝ => ((-1 : ℝ) ^ (k + 1) * ((r⁻¹) ^ (k + 1) + (u⁻¹) ^ (k + 1))) *
        (‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 *
          (((p : ℂ) ^ (-2 * ((ξ : ℂ) * I))) ^ (k + 1) +
            ((starRingEnd ℂ) ((p : ℂ) ^ (-2 * ((ξ : ℂ) * I)))) ^ (k + 1)).re) := by
      funext ξ; simp only [hFK]; ring
    rw [hrw, integral_const_mul, hharm_val k]
  simp_rw [hFK_eval]
  rw [tsum_eq_single 1 (fun k hk => by simp [hk])]
  simp only [↓reduceIte]
  have hamp_h : ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ ^ 2 =
      (1 / (2 * Real.pi)) * ((‖c₀‖ ^ 2 + ‖c_sq‖ ^ 2 + ‖c_pq‖ ^ 2) * I₀) := by
    have hpl := integral_norm_sq_pulseAmplitude h
    rw [hnorm_h] at hpl
    have hpi2 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp at hpl ⊢
    linarith
  have hpi_half : (1 : ℝ) / (2 * Real.pi) = (1 / 2) * (1 / Real.pi) := by field_simp
  have hdiv_pi : 2 * Real.log p / Real.pi = 2 * Real.log p * (1 / Real.pi) := by ring
  rw [hamp_h, hpi_half, hdiv_pi, show (-1 : ℝ) ^ (1 + 1) = 1 by norm_num,
    show (1 + 1 : ℕ) = 2 from rfl]
  dsimp only [I₀]
  ring

/-- **Finite-Time Distinguishing Inequality 2 (Prime-Square `p²` and Mixed-Prime `p q` Interference
Separation).** For distinct primes `p ≠ q`, `1/2 < σ < 1` (`r = p^σ, u = p^{1-σ}, A = r + u`), and
any nonzero `h₀ : CompactPulse` supported in `[-S₀, S₀]` (`2 * S₀ < mixedPrimeGap p q`), retaining
all interference terms:
1. Rotating the mixed-prime phase `c_{pq} ↦ e^{iθ} c_{pq}` leaves `excessPulseGroupDelay`
   identically invariant;
2. Flipping the prime-square phase `c_{p²} = +1` vs. `c_{p²} = -1` (at `c₀ = 1` and any `c_{pq}`)
   produces the exact positive excess
   `-(8 log p / (π p²)) ((eulerLogCoeff p (-r) (-u) (p²)).re - 1/2) ∫ ‖h₀‖² > 0`
   on the passive twin (vs. `0` on `ζ`), and hence strictly separates finite-band group delays
   `bandGroupDelay` at every sufficiently large finite bandwidth `Ω`. -/
theorem finite_time_mixed_pulse_prime_square_distinction {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {σ S₀ : ℝ} (h0 : 1 / 2 < σ) (h1 : σ < 1) (h₀ : CompactPulse)
    (hS₀ : ∀ s : ℝ, S₀ < |s| → h₀ s = 0) (hgap : 2 * S₀ < mixedPrimeGap p q)
    (hne : 0 < ∫ S : ℝ, ‖h₀ S‖ ^ 2) (c_pq : ℂ) :
    let r : ℝ := (p : ℝ) ^ σ
    let u : ℝ := (p : ℝ) ^ (1 - σ)
    let h_plus := threeChannelMixedPulse p q 1 1 c_pq h₀
    let h_minus := threeChannelMixedPulse p q 1 (-1) c_pq h₀
    (∀ c₀ c_sq : ℂ, ∀ θ : ℝ,
      excessPulseGroupDelay p r u
          (threeChannelMixedPulse p q c₀ c_sq (Complex.exp (I * (θ : ℂ)) * c_pq) h₀) =
        excessPulseGroupDelay p r u (threeChannelMixedPulse p q c₀ c_sq c_pq h₀)) ∧
    excessPulseGroupDelay p r u h_plus - excessPulseGroupDelay p r u h_minus =
      -(8 * Real.log p / (Real.pi * (p : ℝ) ^ 2)) *
        ((eulerLogCoeff p (-(r : ℂ)) (-(u : ℂ)) (p ^ 2)).re - 1 / 2) *
        (∫ S : ℝ, ‖h₀ S‖ ^ 2) ∧
    0 < excessPulseGroupDelay p r u h_plus - excessPulseGroupDelay p r u h_minus ∧
    (∃ Ω₀ : ℝ, 0 < Ω₀ ∧ ∀ Ω : ℝ, Ω₀ ≤ Ω →
      (bandGroupDelay modularReducedScattering Ω h_plus -
        bandGroupDelay modularReducedScattering Ω h_minus) <
      (bandGroupDelay (PositiveEulerHorizon.reducedScattering p (r + u)) Ω h_plus -
        bandGroupDelay (PositiveEulerHorizon.reducedScattering p (r + u)) Ω h_minus)) := by
  dsimp only
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hpR
  set r : ℝ := (p : ℝ) ^ σ
  set u : ℝ := (p : ℝ) ^ (1 - σ)
  have hr : 1 < r := Real.one_lt_rpow hpR (by linarith)
  have hu : 1 < u := Real.one_lt_rpow hpR (by linarith)
  have hru : r * u = p := by
    dsimp only [r, u]
    rw [← Real.rpow_add hp0, show σ + (1 - σ) = 1 by ring, Real.rpow_one]
  set h_plus := threeChannelMixedPulse p q 1 1 c_pq h₀
  set h_minus := threeChannelMixedPulse p q 1 (-1) c_pq h₀
  have hinv : ∀ c₀ c_sq : ℂ, ∀ θ : ℝ,
      excessPulseGroupDelay p r u
          (threeChannelMixedPulse p q c₀ c_sq (Complex.exp (I * (θ : ℂ)) * c_pq) h₀) =
        excessPulseGroupDelay p r u (threeChannelMixedPulse p q c₀ c_sq c_pq h₀) := by
    intro c₀ c_sq θ
    have he1 : ‖Complex.exp (I * (θ : ℂ))‖ = 1 := by
      rw [Complex.norm_exp, show (I * (θ : ℂ)).re = 0 by simp, Real.exp_zero]
    rw [excessPulseGroupDelay_threeChannelMixedPulse hp hq hpq hr hu hru _ _ _ h₀ hS₀ hgap,
      excessPulseGroupDelay_threeChannelMixedPulse hp hq hpq hr hu hru _ _ _ h₀ hS₀ hgap,
      norm_mul, he1, one_mul]
  have hdiff_eq : excessPulseGroupDelay p r u h_plus - excessPulseGroupDelay p r u h_minus =
      -(8 * Real.log p / (Real.pi * (p : ℝ) ^ 2)) *
        ((eulerLogCoeff p (-(r : ℂ)) (-(u : ℂ)) (p ^ 2)).re - 1 / 2) *
        (∫ S : ℝ, ‖h₀ S‖ ^ 2) := by
    rw [excessPulseGroupDelay_threeChannelMixedPulse hp hq hpq hr hu hru 1 1 c_pq h₀ hS₀ hgap,
      excessPulseGroupDelay_threeChannelMixedPulse hp hq hpq hr hu hru 1 (-1) c_pq h₀ hS₀ hgap]
    simp only [norm_one, norm_neg, one_pow, map_one, map_neg, one_mul, Complex.one_re, Complex.neg_re]
    rw [eulerLogCoeff_prime_pow hp _ _ (by decide : (2 : ℕ) ≠ 0)]
    have hb_re : ((1 - (-(r : ℂ)) ^ 2 - (-(u : ℂ)) ^ 2) / ((2 : ℕ) : ℂ)).re =
        (1 - r ^ 2 - u ^ 2) / 2 := by
      have he : (1 - (-(r : ℂ)) ^ 2 - (-(u : ℂ)) ^ 2) / ((2 : ℕ) : ℂ) =
          (((1 - r ^ 2 - u ^ 2) / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [he, Complex.ofReal_re]
    rw [hb_re]
    have hr0 : r ≠ 0 := (zero_lt_one.trans hr).ne'
    have hu0 : u ≠ 0 := (zero_lt_one.trans hu).ne'
    have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
    have hp2 : (p : ℝ) ^ 2 = r ^ 2 * u ^ 2 := by rw [← hru]; ring
    rw [hp2]
    field_simp [hr0, hu0, hpi_ne]
    ring
  have hdiff_pos : 0 < excessPulseGroupDelay p r u h_plus - excessPulseGroupDelay p r u h_minus := by
    rw [hdiff_eq]
    have hb_neg := PositiveEulerHorizon.eulerLogCoeff_prime_sq_neg hp hr hu
    have hlog_p : 0 < Real.log p := Real.log_pos hpR
    have h1' : 0 < -(8 * Real.log p / (Real.pi * (p : ℝ) ^ 2)) *
        ((eulerLogCoeff p (-(r : ℂ)) (-(u : ℂ)) (p ^ 2)).re - 1 / 2) := by
      have hfac : 0 < 8 * Real.log p / (Real.pi * (p : ℝ) ^ 2) := by positivity
      nlinarith
    exact mul_pos h1' hne
  refine ⟨hinv, hdiff_eq, hdiff_pos, ?_⟩
  -- Continuity and finite-band convergence as `Ω → ∞`
  have hcont_mod : Continuous (boundaryGroupDelayDensity modularReducedScattering) := by
    unfold boundaryGroupDelayDensity
    refine Continuous.neg (Complex.continuous_re.comp (Continuous.div ?_ ?_ ?_))
    · refine continuous_iff_continuousAt.mpr fun ξ => ?_
      have han : AnalyticAt ℂ modularReducedScattering ((ξ : ℂ) * I) :=
        ((xi_differentiable.comp (by fun_prop : Differentiable ℂ fun z : ℂ => 2 * z)).analyticAt _).div
          ((xi_differentiable.comp (by fun_prop : Differentiable ℂ fun z : ℂ => 1 + 2 * z)).analyticAt _)
          (xi_ne_zero_of_one_le_re (by simp))
      exact ContinuousAt.comp (f := fun ξ : ℝ => (ξ : ℂ) * I) han.deriv.continuousAt (by fun_prop)
    · refine continuous_iff_continuousAt.mpr fun ξ => ?_
      have hdiff : DifferentiableAt ℂ modularReducedScattering ((ξ : ℂ) * I) :=
        ((xi_differentiable _).comp ((ξ : ℂ) * I) (by fun_prop)).div
          ((xi_differentiable _).comp ((ξ : ℂ) * I) (by fun_prop))
          (xi_ne_zero_of_one_le_re (by simp))
      exact ContinuousAt.comp (f := fun ξ : ℝ => (ξ : ℂ) * I) hdiff.continuousAt (by fun_prop)
    · intro ξ h0
      have hn := norm_scatteringPhase_line ξ
      change ‖(1 + 2 * ((ξ : ℂ) * I)) / (2 * ((ξ : ℂ) * I) - 1) *
        modularReducedScattering ((ξ : ℂ) * I)‖ = 1 at hn
      rw [h0, mul_zero, norm_zero] at hn
      exact zero_ne_one hn
  have hcont_twin : Continuous
      (boundaryGroupDelayDensity (PositiveEulerHorizon.reducedScattering p (r + u))) := by
    unfold boundaryGroupDelayDensity
    refine Continuous.neg (Complex.continuous_re.comp (Continuous.div ?_ ?_ ?_))
    · refine continuous_iff_continuousAt.mpr fun ξ => ?_
      have hcx := PositiveEulerHorizon.differentiable_completedXi hp.ne_zero (r + u)
      have han : AnalyticAt ℂ (PositiveEulerHorizon.reducedScattering p (r + u)) ((ξ : ℂ) * I) :=
        ((hcx.comp (by fun_prop : Differentiable ℂ fun z : ℂ => 2 * z)).analyticAt _).div
          ((hcx.comp (by fun_prop : Differentiable ℂ fun z : ℂ => 1 + 2 * z)).analyticAt _)
          (PositiveEulerHorizon.completedXi_den_ne_zero hp.one_lt hr hu hru (by simp))
      exact ContinuousAt.comp (f := fun ξ : ℝ => (ξ : ℂ) * I) han.deriv.continuousAt (by fun_prop)
    · refine continuous_iff_continuousAt.mpr fun ξ => ?_
      exact ContinuousAt.comp (f := fun ξ : ℝ => (ξ : ℂ) * I)
        (PositiveEulerHorizon.differentiableAt_reducedScattering hp.one_lt hr hu hru (by simp)).continuousAt
        (by fun_prop)
    · intro ξ h0
      have hmod_ne : modularReducedScattering ((ξ : ℂ) * I) ≠ 0 := by
        intro hm0
        have hn := norm_scatteringPhase_line ξ
        change ‖(1 + 2 * ((ξ : ℂ) * I)) / (2 * ((ξ : ℂ) * I) - 1) *
          modularReducedScattering ((ξ : ℂ) * I)‖ = 1 at hn
        rw [hm0, mul_zero, norm_zero] at hn
        exact zero_ne_one hn
      rw [PositiveEulerHorizon.reducedScattering_eq_gate_mul hp.ne_zero] at h0
      rcases mul_eq_zero.mp h0 with hg0 | hm0
      · have := PositiveEulerHorizon.norm_gate_axis hp.one_lt hr hu hru ξ
        rw [hg0, norm_zero] at this; exact zero_ne_one this
      · exact hmod_ne hm0
  have hint_excess : ∀ g : CompactPulse, Integrable fun ξ : ℝ =>
      ‖pulseAmplitude g (ξ : ℂ)‖ ^ 2 *
        (boundaryGroupDelayDensity (PositiveEulerHorizon.reducedScattering p (r + u)) ξ -
          boundaryGroupDelayDensity modularReducedScattering ξ) := by
    intro g
    set K_ub : ℝ := 2 * Real.log p * ((r ^ 2 - 1) / (r - 1) ^ 2 + (u ^ 2 - 1) / (u - 1) ^ 2)
    have hcont_g : Continuous fun ξ : ℝ => ‖pulseAmplitude g (ξ : ℂ)‖ ^ 2 *
        (boundaryGroupDelayDensity (PositiveEulerHorizon.reducedScattering p (r + u)) ξ -
          boundaryGroupDelayDensity modularReducedScattering ξ) :=
      ((g.differentiable_amplitude.continuous.comp Complex.continuous_ofReal).norm.pow 2).mul
        (hcont_twin.sub hcont_mod)
    refine ((integrable_norm_sq_pulseAmplitude g).const_mul K_ub).mono' hcont_g.aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    have hpt := twin_excess_groupDelayDensity_eq hp.one_lt hr hu hru ξ
    have hr2 : 0 ≤ r ^ 2 - 1 := by nlinarith
    have hu2 : 0 ≤ u ^ 2 - 1 := by nlinarith
    have hlp : 0 ≤ Real.log p := (Real.log_pos hpR).le
    have hnonneg : 0 ≤ boundaryGroupDelayDensity (PositiveEulerHorizon.reducedScattering p (r + u)) ξ -
        boundaryGroupDelayDensity modularReducedScattering ξ := by
      rw [hpt]; positivity
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hnonneg), hpt, mul_comm K_ub]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    simp only [K_ub]
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
    · refine div_le_div_of_nonneg_left (by nlinarith) (sq_pos_of_pos (sub_pos.mpr hr)) ?_
      have hv1 : ‖(p : ℂ) ^ (-2 * ((ξ : ℂ) * I))‖ = 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hp.pos,
          show (-2 * ((ξ : ℂ) * I)).re = 0 by simp, Real.rpow_zero]
      have hs := norm_sub_norm_le (r : ℂ) (-(p : ℂ) ^ (-2 * ((ξ : ℂ) * I)))
      rw [sub_neg_eq_add, norm_neg, hv1, Complex.norm_real,
        Real.norm_of_nonneg (zero_lt_one.trans hr).le] at hs
      exact pow_le_pow_left₀ (by linarith) hs 2
    · refine div_le_div_of_nonneg_left (by nlinarith) (sq_pos_of_pos (sub_pos.mpr hu)) ?_
      have hv1 : ‖(p : ℂ) ^ (-2 * ((ξ : ℂ) * I))‖ = 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hp.pos,
          show (-2 * ((ξ : ℂ) * I)).re = 0 by simp, Real.rpow_zero]
      have hs := norm_sub_norm_le (u : ℂ) (-(p : ℂ) ^ (-2 * ((ξ : ℂ) * I)))
      rw [sub_neg_eq_add, norm_neg, hv1, Complex.norm_real,
        Real.norm_of_nonneg (zero_lt_one.trans hu).le] at hs
      exact pow_le_pow_left₀ (by linarith) hs 2
  have htend_band : ∀ g : CompactPulse, Tendsto (fun Ω : ℝ =>
      bandGroupDelay (PositiveEulerHorizon.reducedScattering p (r + u)) Ω g -
        bandGroupDelay modularReducedScattering Ω g) atTop (𝓝 (excessPulseGroupDelay p r u g)) := by
    intro g
    have hband_eq : ∀ Ω : ℝ,
        bandGroupDelay (PositiveEulerHorizon.reducedScattering p (r + u)) Ω g -
          bandGroupDelay modularReducedScattering Ω g =
        ∫ ξ in Icc (-Ω) Ω, ‖pulseAmplitude g (ξ : ℂ)‖ ^ 2 *
          (boundaryGroupDelayDensity (PositiveEulerHorizon.reducedScattering p (r + u)) ξ -
            boundaryGroupDelayDensity modularReducedScattering ξ) := by
      intro Ω
      have hi1 : IntegrableOn (fun ξ : ℝ => ‖pulseAmplitude g (ξ : ℂ)‖ ^ 2 *
          boundaryGroupDelayDensity (PositiveEulerHorizon.reducedScattering p (r + u)) ξ)
          (Icc (-Ω) Ω) :=
        (((g.differentiable_amplitude.continuous.comp Complex.continuous_ofReal).norm.pow 2).mul
          hcont_twin).continuousOn.integrableOn_compact isCompact_Icc
      have hi2 : IntegrableOn (fun ξ : ℝ => ‖pulseAmplitude g (ξ : ℂ)‖ ^ 2 *
          boundaryGroupDelayDensity modularReducedScattering ξ) (Icc (-Ω) Ω) :=
        (((g.differentiable_amplitude.continuous.comp Complex.continuous_ofReal).norm.pow 2).mul
          hcont_mod).continuousOn.integrableOn_compact isCompact_Icc
      rw [bandGroupDelay, bandGroupDelay, ← integral_sub hi1 hi2]
      exact setIntegral_congr_fun measurableSet_Icc fun ξ _ => by ring
    simp_rw [hband_eq, ← integral_indicator measurableSet_Icc]
    unfold excessPulseGroupDelay
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ξ : ℝ => ‖‖pulseAmplitude g (ξ : ℂ)‖ ^ 2 *
        (boundaryGroupDelayDensity (PositiveEulerHorizon.reducedScattering p (r + u)) ξ -
          boundaryGroupDelayDensity modularReducedScattering ξ)‖)
      (Eventually.of_forall fun Ω => ((hint_excess g).integrableOn (s := Icc (-Ω) Ω) |>
        (integrable_indicator_iff measurableSet_Icc).mpr).aestronglyMeasurable)
      (Eventually.of_forall fun Ω => Eventually.of_forall fun ξ => norm_indicator_le_norm_self _ _)
      (hint_excess g).norm
      (Eventually.of_forall fun ξ => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop |ξ|] with Ω hΩ
    rw [indicator_of_mem (mem_Icc.mpr (abs_le.mp hΩ))]
  have htend_diff := (htend_band h_plus).sub (htend_band h_minus)
  have hev := (tendsto_order.mp htend_diff).1 0 hdiff_pos
  obtain ⟨Ω₁, hΩ₁⟩ := eventually_atTop.mp hev
  refine ⟨max Ω₁ 1, by positivity, fun Ω hΩ => ?_⟩
  have hgt := hΩ₁ Ω ((le_max_left Ω₁ 1).trans hΩ)
  linarith

end GaloisForLFunctions.BlackHoleRingdown

end
