import GaloisForLFunctions.RHTower.EulerPrimitiveJointDepthKreinXiLanding
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldPrimeZetaLaplaceSymbol
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldRelativeOrbitLeakage
import GaloisForLFunctions.RHTower.PrimeBoundaryMonodromyEscape
import GaloisForLFunctions.RHTower.GammaDampedVerticalBound
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Joint-depth Möbius transport of the Route-T Wold current

The literal joint prime/depth source supplies the full von Mangoldt channel as one off-diagonal
Krein coefficient.  Möbius inversion extracts its valuation-one prime channel; the Route-T Wold
current is then the cubic four-shift difference of that channel.  This module puts those exact
operations together before any divisor is selected.

The exact source-to-Wold identity is deliberately restricted to the common Euler chamber.  The
properly reindexed `r ≥ 2` continuation tail is proved below to converge uniformly on every closed
half-plane `Re z ≥ a > 1/2`; transporting that source continuation through the safe-chamber
identity to the meromorphic Wold current remains a separate producer problem.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every positive Möbius dilation of a positive four-shift source argument remains in the
literal joint-depth Hilbert chamber. -/
theorem xiHeatCassiniWold_jointDepthMöbiusArg_re_pos
    {s : ℂ} (hs : 0 < s.re) {r : ℕ+} {k : ℕ} (hk : 1 ≤ k) :
    0 < (((r : ℂ) * (s + k) - 1).re) := by
  have hr : (1 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (one_le : (1 : ℕ+) ≤ r)
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk
  have hsk : 1 < s.re + (k : ℝ) := by linarith
  have hprod : 1 < (r : ℝ) * (s.re + (k : ℝ)) := by
    calc
      (1 : ℝ) < s.re + (k : ℝ) := hsk
      _ = 1 * (s.re + (k : ℝ)) := by ring
      _ ≤ (r : ℝ) * (s.re + (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hr (by linarith)
  simpa only [Complex.sub_re, Complex.mul_re, Complex.add_re,
    Complex.natCast_re, Complex.one_re, Complex.natCast_im, zero_mul, sub_zero] using
    sub_pos.mpr hprod

/-- The valuation-one prime channel at `s + k` as a Möbius superposition of literal
joint-depth Krein source coefficients. -/
def xiHeatCassiniWoldJointDepthMöbiusSourceChannel
    (s : ℂ) (k : ℕ) (hs : 0 < s.re) (hk : 1 ≤ k) : ℂ :=
  ∑' r : ℕ+, (ArithmeticFunction.moebius (r : ℕ) : ℂ) *
    xiGammaEulerPrimitiveJointDepthKreinPair
      (xiGammaEulerPrimitiveJointDepthKreinSplitCoSource
        ((r : ℂ) * (s + k) - 1)
        (xiHeatCassiniWold_jointDepthMöbiusArg_re_pos hs hk))
      (xiGammaEulerPrimitiveJointDepthKreinSplitSource
        ((r : ℂ) * (s + k) - 1)
        (xiHeatCassiniWold_jointDepthMöbiusArg_re_pos hs hk))

/-- Exact source-level Möbius inversion.  No zero coordinate or divisor condition occurs: the
right side is the valuation-one prime-zeta derivative, obtained from literal prime-power source
coefficients. -/
theorem xiHeatCassiniWoldJointDepthMöbiusSourceChannel_eq_neg_deriv_coronaPrimeZeta
    {s : ℂ} (hs : 0 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    xiHeatCassiniWoldJointDepthMöbiusSourceChannel s k hs hk =
      -deriv coronaPrimeZeta (s + k) := by
  rw [xiHeatCassiniWoldJointDepthMöbiusSourceChannel]
  rw [primeBoundary_moebius_inversion]
  · apply tsum_congr
    intro r
    rw [xiGammaEulerPrimitiveJointDepthKreinSplitPair_eq]
    congr 1
    unfold vonMangoldtPrimeLaplaceChannelComplex
    congr 2
    ring
  · simp only [Complex.add_re, Complex.natCast_re]
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith

/-- The literal source-side four-shift combination matching the cubic Wold Euler depletion. -/
def xiHeatCassiniWoldJointDepthMöbiusTransport (s : ℂ) (hs : 0 < s.re) : ℂ :=
  xiHeatCassiniWoldJointDepthMöbiusSourceChannel s 1 hs (by omega) -
    3 * xiHeatCassiniWoldJointDepthMöbiusSourceChannel s 2 hs (by omega) +
      3 * xiHeatCassiniWoldJointDepthMöbiusSourceChannel s 3 hs (by omega) -
        xiHeatCassiniWoldJointDepthMöbiusSourceChannel s 4 hs (by omega)

/-- **Route-T source-to-Wold transport.**  In the Euler chamber, the complete Wold current is
the four-shift Möbius transform of the actual off-diagonal joint-depth source. -/
theorem xiHeatCassiniWoldJointDepthMöbiusTransport_eq_woldLaplaceCurrent
    {s : ℂ} (hs : 0 < s.re) :
    xiHeatCassiniWoldJointDepthMöbiusTransport s hs =
      xiHeatCassiniWoldLaplaceCurrent s := by
  rw [xiHeatCassiniWoldJointDepthMöbiusTransport,
    xiHeatCassiniWoldJointDepthMöbiusSourceChannel_eq_neg_deriv_coronaPrimeZeta
      hs 1 (by omega),
    xiHeatCassiniWoldJointDepthMöbiusSourceChannel_eq_neg_deriv_coronaPrimeZeta
      hs 2 (by omega),
    xiHeatCassiniWoldJointDepthMöbiusSourceChannel_eq_neg_deriv_coronaPrimeZeta
      hs 3 (by omega),
    xiHeatCassiniWoldJointDepthMöbiusSourceChannel_eq_neg_deriv_coronaPrimeZeta
      hs 4 (by omega),
    xiHeatCassiniWoldLaplaceCurrent_eq_primeZetaDerivFourShift hs]
  ring

/-- Canonical meromorphic continuation of one Möbius-dilated joint-depth source channel.  On the
Euler chamber this is the continuation of the corresponding literal Krein coefficient; the
definition exposes the continuation needed to study a Wold pole. -/
def xiHeatCassiniWoldJointDepthMöbiusSourceContinuationTerm
    (r : ℕ+) (k : ℕ) (s : ℂ) : ℂ :=
  (ArithmeticFunction.moebius (r : ℕ) : ℂ) *
    infinitePrimeFlux ((r : ℂ) * (s + k))

/-- At an off-critical right-half zero, every shifted/dilated source argument except the
undilated first one is strictly inside the Euler half-plane. -/
theorem xiHeatCassiniWold_jointDepthMöbiusTailArgument_re_gt_one
    {rho : ℂ} (hrho : 1 / 2 < rho.re) {r : ℕ+} {k : ℕ}
    (hk : 1 ≤ k) (hprincipal : ¬ (r = 1 ∧ k = 1)) :
    1 < (((r : ℂ) * ((rho - 1) + k)).re) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hr : (1 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (one_le : (1 : ℕ+) ≤ r)
  simp only [Complex.mul_re, Complex.sub_re, Complex.add_re,
    Complex.natCast_re, Complex.one_re, Complex.natCast_im, Complex.sub_im,
    Complex.add_im, zero_mul, sub_zero, add_zero]
  by_cases hr1 : r = 1
  · subst r
    have hk1 : k ≠ 1 := fun hk1 => hprincipal ⟨rfl, hk1⟩
    have hk2 : 2 ≤ k := by omega
    have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    norm_num
    linarith
  · have hr2 : (2 : ℝ) ≤ (r : ℝ) := by
      have h1r : (1 : ℕ+) < r :=
        lt_of_le_of_ne (one_le : (1 : ℕ+) ≤ r) (Ne.symm hr1)
      have h1rNat : 1 < (r : ℕ) := by exact_mod_cast h1r
      have hr2Nat : 2 ≤ (r : ℕ) := by omega
      exact_mod_cast hr2Nat
    have ht : 1 / 2 < rho.re - 1 + (k : ℝ) := by linarith
    calc
      (1 : ℝ) < 2 * (rho.re - 1 + (k : ℝ)) := by nlinarith
      _ ≤ (r : ℝ) * (rho.re - 1 + (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hr2 (by linarith)

/-- **Termwise pole isolation.**  Near a hypothetical off-critical right-half zero, every
Möbius source term except `(r,k) = (1,1)` is holomorphic.  Thus any cancellation of the Wold
residue by the Möbius tail would have to violate normal convergence; it cannot arise from a
second termwise divisor pole. -/
theorem differentiableAt_xiHeatCassiniWoldJointDepthMöbiusSourceContinuationTerm_nonprincipal
    {rho : ℂ} (hrho : 1 / 2 < rho.re) {r : ℕ+} {k : ℕ}
    (hk : 1 ≤ k) (hprincipal : ¬ (r = 1 ∧ k = 1)) :
    DifferentiableAt ℂ (xiHeatCassiniWoldJointDepthMöbiusSourceContinuationTerm r k)
      (rho - 1) := by
  have harg := xiHeatCassiniWold_jointDepthMöbiusTailArgument_re_gt_one
    hrho hk hprincipal
  have hflux : DifferentiableAt ℂ (fun z : ℂ =>
      -deriv riemannZeta z / riemannZeta z)
      ((r : ℂ) * ((rho - 1) + k)) := by
    exact differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re harg
  have hcomp := hflux.comp (rho - 1) (by fun_prop : DifferentiableAt ℂ
    (fun s : ℂ => (r : ℂ) * (s + k)) (rho - 1))
  have hresult := hcomp.const_mul (ArithmeticFunction.moebius (r : ℕ) : ℂ)
  have hfun : xiHeatCassiniWoldJointDepthMöbiusSourceContinuationTerm r k = fun s : ℂ =>
      (ArithmeticFunction.moebius (r : ℕ) : ℂ) *
        (-deriv riemannZeta ((r : ℂ) * (s + k)) /
          riemannZeta ((r : ℂ) * (s + k))) := by
    funext s
    simp only [xiHeatCassiniWoldJointDepthMöbiusSourceContinuationTerm, infinitePrimeFlux,
      logDeriv_apply]
    rw [← neg_div]
  rw [hfun]
  exact hresult

/-! ### Normal Möbius tail beyond the principal source channel -/

/-- The geometric majorant for the dilated continuation tail is summable at every positive
horizontal margin. -/
theorem xiHeatCassiniWold_summable_geometric_rpow_neg_mul {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => (2 : ℝ) ^ (-((n : ℝ) * a))) := by
  let q : ℝ := (2 : ℝ) ^ (-a)
  have hqpos : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hqlt : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr ha)
  have hsum : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_iff_norm_lt_one.mpr (by
      rw [Real.norm_eq_abs, abs_of_pos hqpos]
      exact hqlt)
  convert hsum using 1
  funext n
  dsimp [q]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- Each von Mangoldt Dirichlet term at an `r ≥ 2` dilation is bounded by a fixed Euler-series
term times an exponentially summable factor. -/
theorem xiHeatCassiniWold_term_vonMangoldt_dilate_le_geometric
    {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : a ≤ z.re)
    (r : ℕ) (hr : 2 ≤ r) (n : ℕ) :
    ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ((r : ℂ) * z) n‖ ≤
      (2 : ℝ) ^ (-(((r : ℝ) - 2) * a)) *
        ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ((2 * a : ℝ) : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rcases eq_or_ne n 1 with rfl | hn1
  · simp [ArithmeticFunction.vonMangoldt_apply_one]
  simp only [if_neg hn0, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Complex.ofReal_re]
  have hn2 : 2 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnr : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hgap : (0 : ℝ) ≤ (r : ℝ) - 2 := by linarith
  have hgapA : (0 : ℝ) ≤ ((r : ℝ) - 2) * a := mul_nonneg hgap ha
  have hpowTwo : (2 : ℝ) ^ (((r : ℝ) - 2) * a) ≤
      (n : ℝ) ^ (((r : ℝ) - 2) * a) :=
    Real.rpow_le_rpow (by norm_num) hnR hgapA
  have hpowSplit : (n : ℝ) ^ (2 * a) * (n : ℝ) ^ (((r : ℝ) - 2) * a) =
      (n : ℝ) ^ ((r : ℝ) * a) := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < (n : ℝ))]
    congr 1
    ring
  have hpowScale : (n : ℝ) ^ ((r : ℝ) * a) ≤
      (n : ℝ) ^ ((r : ℝ) * z.re) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · exact le_trans (by norm_num) hnR
    · exact mul_le_mul_of_nonneg_left hz hnr
  have hdenom : (n : ℝ) ^ (2 * a) * (2 : ℝ) ^ (((r : ℝ) - 2) * a) ≤
      (n : ℝ) ^ ((r : ℝ) * z.re) := by
    calc
      (n : ℝ) ^ (2 * a) * (2 : ℝ) ^ (((r : ℝ) - 2) * a) ≤
          (n : ℝ) ^ (2 * a) * (n : ℝ) ^ (((r : ℝ) - 2) * a) := by
        gcongr
      _ = (n : ℝ) ^ ((r : ℝ) * a) := hpowSplit
      _ ≤ (n : ℝ) ^ ((r : ℝ) * z.re) := hpowScale
  have hbase : (0 : ℝ) < (n : ℝ) ^ (2 * a) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hgeo : (0 : ℝ) < (2 : ℝ) ^ (((r : ℝ) - 2) * a) :=
    Real.rpow_pos_of_pos (by norm_num) _
  set q : ℝ := (2 : ℝ) ^ (((r : ℝ) - 2) * a) with hq_def
  have hq : 0 < q := by simpa [hq_def] using hgeo
  have hdenomQ : (n : ℝ) ^ (2 * a) * q ≤ (n : ℝ) ^ ((r : ℝ) * z.re) := by
    simpa [hq_def] using hdenom
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  change ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ / (n : ℝ) ^ ((r : ℝ) * z.re) ≤
    q⁻¹ * (‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ / (n : ℝ) ^ (2 * a))
  have hrewrite : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ /
      ((n : ℝ) ^ (2 * a) * q) =
      q⁻¹ * (‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ / (n : ℝ) ^ (2 * a)) := by
    field_simp [ne_of_gt hbase, ne_of_gt hq]
  calc
    ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ / (n : ℝ) ^ ((r : ℝ) * z.re) ≤
        ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ /
          ((n : ℝ) ^ (2 * a) * q) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hbase hq) hdenomQ
    _ = q⁻¹ * (‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ / (n : ℝ) ^ (2 * a)) := hrewrite

/-- Uniform geometric bound for every nonprincipal dilation of the prime-flux continuation. -/
theorem xiHeatCassiniWold_norm_infinitePrimeFlux_dilate_le_geometric
    {a : ℝ} (ha : 1 / 2 < a) {z : ℂ} (hz : a ≤ z.re)
    (r : ℕ) (hr : 2 ≤ r) :
    ‖infinitePrimeFlux ((r : ℂ) * z)‖ ≤
      (2 : ℝ) ^ (-(((r : ℝ) - 2) * a)) *
        ∑' n : ℕ, ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((2 * a : ℝ) : ℂ) n‖ := by
  have ha0 : 0 ≤ a := by linarith
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hargR : 1 < (r : ℝ) * z.re := by
    calc
      (1 : ℝ) < 2 * a := by linarith
      _ = (2 : ℝ) * a := by ring
      _ ≤ (r : ℝ) * a := mul_le_mul_of_nonneg_right hrR ha0
      _ ≤ (r : ℝ) * z.re := mul_le_mul_of_nonneg_left hz (by positivity)
  have harg : 1 < (((r : ℂ) * z).re) := by
    simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
      using hargR
  have hbase : 1 < ((2 * a : ℝ) : ℂ).re := by
    simp only [Complex.ofReal_re]
    linarith
  rw [infinitePrimeFlux_eq_vonMangoldtLSeries harg]
  calc
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((r : ℂ) * z)‖ ≤
        ∑' n : ℕ, (2 : ℝ) ^ (-(((r : ℝ) - 2) * a)) *
          ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
            ((2 * a : ℝ) : ℂ) n‖ := by
      apply norm_lSeries_le_of_term_bound
      · exact (summable_norm_iff.mpr
          (ArithmeticFunction.LSeriesSummable_vonMangoldt hbase)).mul_left _
      · intro n
        exact xiHeatCassiniWold_term_vonMangoldt_dilate_le_geometric ha0 hz r hr n
    _ = (2 : ℝ) ^ (-(((r : ℝ) - 2) * a)) *
        ∑' n : ℕ, ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((2 * a : ℝ) : ℂ) n‖ := tsum_mul_left

/-- Absolute summability of the unweighted `r ≥ 2` continuation family. -/
theorem xiHeatCassiniWold_summable_norm_infinitePrimeFlux_dilationTail
    {a : ℝ} (ha : 1 / 2 < a) {z : ℂ} (hz : a ≤ z.re) :
    Summable (fun n : ℕ => ‖infinitePrimeFlux (((n + 2 : ℕ) : ℂ) * z)‖) := by
  let C : ℝ := ∑' n : ℕ, ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
    ((2 * a : ℝ) : ℂ) n‖
  have hmajorant : Summable (fun n : ℕ => C * (2 : ℝ) ^ (-((n : ℝ) * a))) :=
    (xiHeatCassiniWold_summable_geometric_rpow_neg_mul (by linarith : 0 < a)).mul_left C
  refine hmajorant.of_nonneg_of_le (fun n => norm_nonneg _) ?_
  intro n
  have h := xiHeatCassiniWold_norm_infinitePrimeFlux_dilate_le_geometric
    ha hz (n + 2) (by omega)
  have hrewrite : (2 : ℝ) ^ (-((((n + 2 : ℕ) : ℝ) - 2) * a)) =
      (2 : ℝ) ^ (-((n : ℝ) * a)) := by
    congr 1
    push_cast
    ring
  rw [hrewrite] at h
  calc
    ‖infinitePrimeFlux (((n + 2 : ℕ) : ℂ) * z)‖ ≤
        (2 : ℝ) ^ (-((n : ℝ) * a)) * C := by simpa only [C] using h
    _ = C * (2 : ℝ) ^ (-((n : ℝ) * a)) := by ring

/-- The actual nonprincipal source terms, reindexed by `r = n + 2`. -/
def xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm (n : ℕ) (z : ℂ) : ℂ :=
  (ArithmeticFunction.moebius (n + 2) : ℂ) *
    infinitePrimeFlux (((n + 2 : ℕ) : ℂ) * z)

/-- This reindexing is literally the `k = 1`, `r ≥ 2` portion of the canonical source
continuation, so no new surrogate carrier is introduced. -/
theorem xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm_eq_continuationTerm
    (n : ℕ) (z : ℂ) :
    xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm n z =
      xiHeatCassiniWoldJointDepthMöbiusSourceContinuationTerm ⟨n + 2, by omega⟩ 1 (z - 1) := by
  simp [xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm,
    xiHeatCassiniWoldJointDepthMöbiusSourceContinuationTerm]

theorem norm_xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm_le (n : ℕ) (z : ℂ) :
    ‖xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm n z‖ ≤
      ‖infinitePrimeFlux (((n + 2 : ℕ) : ℂ) * z)‖ := by
  have hmu : ‖(ArithmeticFunction.moebius (n + 2) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 2)
  rw [xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm, norm_mul]
  calc
    ‖(ArithmeticFunction.moebius (n + 2) : ℂ)‖ *
        ‖infinitePrimeFlux (((n + 2 : ℕ) : ℂ) * z)‖ ≤
        1 * ‖infinitePrimeFlux (((n + 2 : ℕ) : ℂ) * z)‖ :=
      mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
    _ = ‖infinitePrimeFlux (((n + 2 : ℕ) : ℂ) * z)‖ := one_mul _

/-- The nonprincipal `k = 1` source continuation tail is absolutely summable at every point of
every half-plane `Re z ≥ a > 1/2`. -/
theorem summable_xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm
    {a : ℝ} (ha : 1 / 2 < a) {z : ℂ} (hz : a ≤ z.re) :
    Summable (fun n : ℕ => xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm n z) := by
  exact Summable.of_norm_bounded
    (xiHeatCassiniWold_summable_norm_infinitePrimeFlux_dilationTail ha hz)
    (fun n => norm_xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm_le n z)

/-- Reindexed normal continuation of the `r ≥ 2`, `k = 1` source tail. -/
def xiHeatCassiniWoldJointDepthMöbiusDilationTail (z : ℂ) : ℂ :=
  ∑' n : ℕ, xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm n z

/-- **Normal-tail theorem.**  The actual nonprincipal Möbius source continuation converges
uniformly on every closed half-plane strictly to the right of `1/2`.  Thus it cannot produce or
cancel a Wold pole there through a failure of normal convergence. -/
theorem tendstoUniformlyOn_xiHeatCassiniWoldJointDepthMöbiusDilationTail
    {a : ℝ} (ha : 1 / 2 < a) :
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm n z)
      xiHeatCassiniWoldJointDepthMöbiusDilationTail Filter.atTop {z : ℂ | a ≤ z.re} := by
  let C : ℝ := ∑' n : ℕ, ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
    ((2 * a : ℝ) : ℂ) n‖
  let u : ℕ → ℝ := fun n => C * (2 : ℝ) ^ (-((n : ℝ) * a))
  have hu : Summable u := by
    dsimp only [u]
    exact (xiHeatCassiniWold_summable_geometric_rpow_neg_mul (by linarith : 0 < a)).mul_left C
  apply tendstoUniformlyOn_tsum_nat hu
  intro n z hz
  change a ≤ z.re at hz
  calc
    ‖xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm n z‖ ≤
        ‖infinitePrimeFlux (((n + 2 : ℕ) : ℂ) * z)‖ :=
      norm_xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm_le n z
    _ ≤ (2 : ℝ) ^ (-((((n + 2 : ℕ) : ℝ) - 2) * a)) * C := by
      simpa only [C] using
        xiHeatCassiniWold_norm_infinitePrimeFlux_dilate_le_geometric ha hz (n + 2) (by omega)
    _ = (2 : ℝ) ^ (-((n : ℝ) * a)) * C := by
      congr 1
      push_cast
      ring
    _ = C * (2 : ℝ) ^ (-((n : ℝ) * a)) := by ring

/-- The normal continuation tail is holomorphic on every open half-plane strictly to the right
of the critical boundary.  This upgrades its uniform convergence to a genuine pole-free source
germ, rather than merely a bounded correction. -/
theorem differentiableOn_xiHeatCassiniWoldJointDepthMöbiusDilationTail
    {a : ℝ} (ha : 1 / 2 < a) :
    DifferentiableOn ℂ xiHeatCassiniWoldJointDepthMöbiusDilationTail {z : ℂ | a < z.re} := by
  let C : ℝ := ∑' n : ℕ, ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
    ((2 * a : ℝ) : ℂ) n‖
  let u : ℕ → ℝ := fun n => C * (2 : ℝ) ^ (-((n : ℝ) * a))
  have hu : Summable u := by
    dsimp only [u]
    exact (xiHeatCassiniWold_summable_geometric_rpow_neg_mul (by linarith : 0 < a)).mul_left C
  change DifferentiableOn ℂ (fun z => ∑' n : ℕ,
    xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm n z) {z : ℂ | a < z.re}
  apply differentiableOn_tsum_of_summable_norm hu
  · intro n z hz
    change a < z.re at hz
    have hr : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ≤ n + 2)
    have hargR : 1 < ((n + 2 : ℕ) : ℝ) * z.re := by
      calc
        (1 : ℝ) < 2 * z.re := by linarith
        _ = (2 : ℝ) * z.re := by ring
        _ ≤ ((n + 2 : ℕ) : ℝ) * z.re := mul_le_mul_of_nonneg_right hr (by linarith)
    have harg : 1 < ((((n + 2 : ℕ) : ℂ) * z).re) := by
      simpa [Complex.mul_re] using hargR
    have hflux : DifferentiableAt ℂ (fun w : ℂ =>
        (-deriv riemannZeta w) / riemannZeta w) (((n + 2 : ℕ) : ℂ) * z) :=
      differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re harg
    have hcomp := hflux.comp z (by fun_prop : DifferentiableAt ℂ
      (fun w : ℂ => ((n + 2 : ℕ) : ℂ) * w) z)
    have hfun : xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm n = fun w : ℂ =>
        (ArithmeticFunction.moebius (n + 2) : ℂ) *
          ((-deriv riemannZeta (((n + 2 : ℕ) : ℂ) * w) /
            riemannZeta (((n + 2 : ℕ) : ℂ) * w))) := by
      funext w
      simp only [xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm, infinitePrimeFlux,
        logDeriv_apply]
      rw [← neg_div]
    rw [hfun]
    exact (hcomp.const_mul (ArithmeticFunction.moebius (n + 2) : ℂ)).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro n z hz
    change a < z.re at hz
    calc
      ‖xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm n z‖ ≤
          ‖infinitePrimeFlux (((n + 2 : ℕ) : ℂ) * z)‖ :=
        norm_xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm_le n z
      _ ≤ (2 : ℝ) ^ (-((((n + 2 : ℕ) : ℝ) - 2) * a)) * C := by
        simpa only [C] using
          xiHeatCassiniWold_norm_infinitePrimeFlux_dilate_le_geometric ha hz.le (n + 2) (by omega)
      _ = (2 : ℝ) ^ (-((n : ℝ) * a)) * C := by
        congr 1
        push_cast
        ring
      _ = C * (2 : ℝ) ^ (-((n : ℝ) * a)) := by ring

/-- **Safe-chamber source decomposition.**  The literal Möbius prime-boundary current is the
undilated logarithmic-derivative flux plus exactly the reindexed normal continuation tail.  Thus
the only source term that can carry a pole in `Re z > 1/2` is the undilated channel. -/
theorem xiHeatCassiniWoldJointDepthMöbiusSource_decomposition
    {z : ℂ} (hz : 1 < z.re) :
    -deriv coronaPrimeZeta z = infinitePrimeFlux z +
      xiHeatCassiniWoldJointDepthMöbiusDilationTail z := by
  let f : ℕ+ → ℂ := fun r => (ArithmeticFunction.moebius (r : ℕ) : ℂ) *
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (((r : ℕ) : ℂ) * z)
  have htailTerm (n : ℕ) :
      f (Nat.succPNat (n + 1)) =
        xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm n z := by
    have hn : 1 < ((n + 2 : ℕ) : ℝ) * z.re := by
      have hn2 : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 ≤ n + 2)
      nlinarith
    have harg : 1 < ((((n + 2 : ℕ) : ℂ) * z).re) := by
      simpa [Complex.mul_re] using hn
    have hindex : ((Nat.succPNat (n + 1) : ℕ+) : ℕ) = n + 2 := by
      simp [Nat.succPNat]
    rw [xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm]
    change (ArithmeticFunction.moebius ((Nat.succPNat (n + 1) : ℕ+) : ℕ) : ℂ) *
        LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((((Nat.succPNat (n + 1) : ℕ+) : ℕ) : ℂ) * z) =
      (ArithmeticFunction.moebius (n + 2) : ℂ) *
        infinitePrimeFlux (((n + 2 : ℕ) : ℂ) * z)
    rw [hindex, infinitePrimeFlux_eq_vonMangoldtLSeries harg]
  have htail : Summable (fun n : ℕ => f (Nat.succPNat (n + 1))) := by
    refine (summable_xiHeatCassiniWoldJointDepthMöbiusDilationTailTerm
      (a := (3 / 4 : ℝ)) (z := z) (by norm_num) (by linarith [hz])).congr ?_
    intro n
    exact (htailTerm n).symm
  have hsucc : Summable (f ∘ Nat.succPNat) := by
    exact (summable_nat_add_iff (f := fun n : ℕ => f (Nat.succPNat n)) 1).mp htail
  have hhead : f 1 = infinitePrimeFlux z := by
    simpa [f] using (infinitePrimeFlux_eq_vonMangoldtLSeries hz).symm
  rw [primeBoundary_moebius_inversion hz]
  change (∑' r : ℕ+, f r) = _
  rw [← tsum_succPNat]
  change (∑' n : ℕ, (f ∘ Nat.succPNat) n) = _
  rw [hsucc.tsum_eq_zero_add]
  simp only [Function.comp_apply]
  have hzero : Nat.succPNat 0 = (1 : ℕ+) := by
    apply PNat.coe_injective
    simp [Nat.succPNat]
  rw [hzero, hhead]
  unfold xiHeatCassiniWoldJointDepthMöbiusDilationTail
  congr 1
  apply tsum_congr
  intro n
  exact htailTerm n

/-- **Möbius--valuation duality.**  On the full half-plane beyond the critical boundary, the
normal `r ≥ 2` Möbius-dilation correction is exactly the negative of the usual higher-prime-power
tail.  Thus it is not a second singular carrier: Möbius inversion reorganizes the known valuation
tail rather than producing an independent Route-T residue. -/
theorem xiHeatCassiniWoldJointDepthMöbiusDilationTail_eq_neg_higherValuation
    {z : ℂ} (hz : 1 / 2 < z.re) :
    xiHeatCassiniWoldJointDepthMöbiusDilationTail z =
      -xiPrimeLogHigherValuation z := by
  let U : Set ℂ := {w : ℂ | 1 / 2 < w.re}
  have hUopen : IsOpen U := by
    dsimp only [U]
    exact isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U := by
    dsimp only [U]
    exact (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have htailDiff : DifferentiableOn ℂ xiHeatCassiniWoldJointDepthMöbiusDilationTail U := by
    intro w hw
    change 1 / 2 < w.re at hw
    let a : ℝ := (1 / 2 + w.re) / 2
    have ha : 1 / 2 < a := by
      dsimp only [a]
      linarith
    have haw : a < w.re := by
      dsimp only [a]
      linarith
    have hlocalOpen : IsOpen {v : ℂ | a < v.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact (differentiableOn_xiHeatCassiniWoldJointDepthMöbiusDilationTail ha w haw).differentiableAt
      (hlocalOpen.mem_nhds haw) |>.differentiableWithinAt
  have htailAnalytic : AnalyticOnNhd ℂ xiHeatCassiniWoldJointDepthMöbiusDilationTail U :=
    htailDiff.analyticOnNhd hUopen
  have hhighAnalytic : AnalyticOnNhd ℂ xiPrimeLogHigherValuation U := by
    exact differentiableOn_xiPrimeLogHigherValuation_halfPlane.analyticOnNhd hUopen
  have hsumAnalytic : AnalyticOnNhd ℂ (fun w : ℂ =>
      xiHeatCassiniWoldJointDepthMöbiusDilationTail w + xiPrimeLogHigherValuation w) U :=
    htailAnalytic.add hhighAnalytic
  have hsafe : ∀ w : ℂ, 1 < w.re →
      xiHeatCassiniWoldJointDepthMöbiusDilationTail w + xiPrimeLogHigherValuation w = 0 := by
    intro w hw
    have hmobius := xiHeatCassiniWoldJointDepthMöbiusSource_decomposition hw
    have hprime := neg_deriv_coronaPrimeZeta_eq_xiPrimeLogDirichlet hw
    have hcontinuation := xiPrimeLogDirichletContinuation_eq hw
    rw [xiPrimeLogDirichletContinuation] at hcontinuation
    linear_combination -hmobius + hprime - hcontinuation
  let z₀ : ℂ := 2
  have hz₀U : z₀ ∈ U := by
    dsimp only [z₀, U]
    norm_num
  have hsafeOpen : IsOpen {w : ℂ | 1 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hevent : (fun w : ℂ =>
      xiHeatCassiniWoldJointDepthMöbiusDilationTail w + xiPrimeLogHigherValuation w) =ᶠ[𝓝 z₀]
        (0 : ℂ → ℂ) := by
    filter_upwards [hsafeOpen.mem_nhds (by dsimp only [z₀]; norm_num)] with w hw
    exact hsafe w hw
  have hglobal := hsumAnalytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    hUpre hz₀U hevent
  have hzU : z ∈ U := by
    change 1 / 2 < z.re
    exact hz
  have hzero := hglobal hzU
  change xiHeatCassiniWoldJointDepthMöbiusDilationTail z +
      xiPrimeLogHigherValuation z = 0 at hzero
  linear_combination hzero

/-- The canonical normal model of the literal Möbius source: retain the undilated source flux
and add the normal `r ≥ 2` correction before any four-shift is taken. -/
def xiHeatCassiniWoldJointDepthMöbiusSourceNormalContinuation (z : ℂ) : ℂ :=
  infinitePrimeFlux z + xiHeatCassiniWoldJointDepthMöbiusDilationTail z

/-- **Source-germ conservation.**  Beyond the critical boundary, the canonical normal
continuation of the literal Möbius source model is exactly the established valuation-one prime-log
continuation.  The Möbius correction contributes no new carrier: it is the higher-valuation
subtraction already present in that continuation. -/
theorem xiHeatCassiniWoldJointDepthMöbiusSourceNormalContinuation_eq_primeLogContinuation
    {z : ℂ} (hz : 1 / 2 < z.re) :
    xiHeatCassiniWoldJointDepthMöbiusSourceNormalContinuation z =
      xiPrimeLogDirichletContinuation z := by
  rw [xiHeatCassiniWoldJointDepthMöbiusSourceNormalContinuation,
    xiHeatCassiniWoldJointDepthMöbiusDilationTail_eq_neg_higherValuation hz,
    xiPrimeLogDirichletContinuation]
  ring

/-- The four-shift Route-T transport of the canonical normal Möbius source model. -/
def xiHeatCassiniWoldJointDepthMöbiusNormalTransport (s : ℂ) : ℂ :=
  xiHeatCassiniWoldJointDepthMöbiusSourceNormalContinuation (s + 1) -
    3 * xiHeatCassiniWoldJointDepthMöbiusSourceNormalContinuation (s + 2) +
      3 * xiHeatCassiniWoldJointDepthMöbiusSourceNormalContinuation (s + 3) -
        xiHeatCassiniWoldJointDepthMöbiusSourceNormalContinuation (s + 4)

/-- **Normal source-to-Wold transport.**  The normal continuation selected by the literal
joint-depth source agrees with the meromorphic Wold continuation on the whole half-plane
containing every strict-right divisor pole. -/
theorem xiHeatCassiniWoldJointDepthMöbiusNormalTransport_eq_woldLaplaceContinuation
    {s : ℂ} (hs : -(1 / 2 : ℝ) < s.re) :
    xiHeatCassiniWoldJointDepthMöbiusNormalTransport s =
      xiHeatCassiniWoldLaplaceContinuation s := by
  have hs1 : 1 / 2 < (s + 1).re := by simp; linarith
  have hs2 : 1 / 2 < (s + 2).re := by simp; linarith
  have hs3 : 1 / 2 < (s + 3).re := by simp; linarith
  have hs4 : 1 / 2 < (s + 4).re := by simp; linarith
  rw [xiHeatCassiniWoldJointDepthMöbiusNormalTransport,
    xiHeatCassiniWoldJointDepthMöbiusSourceNormalContinuation_eq_primeLogContinuation hs1,
    xiHeatCassiniWoldJointDepthMöbiusSourceNormalContinuation_eq_primeLogContinuation hs2,
    xiHeatCassiniWoldJointDepthMöbiusSourceNormalContinuation_eq_primeLogContinuation hs3,
    xiHeatCassiniWoldJointDepthMöbiusSourceNormalContinuation_eq_primeLogContinuation hs4,
    xiHeatCassiniWoldLaplaceContinuation]

/-- **Source-level strict-right divisor transport.**  Every strict-right zeta zero occurs with
its exact negative multiplicity residue already in the canonical normal transport of the literal
joint-depth Möbius source.  Thus this source family is a faithful realization of the known Wold
carrier, not a second Route-T comparison. -/
theorem xiHeatCassiniWoldJointDepthMöbiusNormalTransport_zero_residue
    {rho : ℂ} (hrho : 1 / 2 < rho.re) (hzeta : riemannZeta rho = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun s : ℂ =>
        (s - (rho - 1)) * xiHeatCassiniWoldJointDepthMöbiusNormalTransport s)
        (𝓝[≠] (rho - 1)) (𝓝 (-(m : ℂ))) := by
  obtain ⟨m, hm, hres⟩ :=
    xiHeatCassiniWoldLaplaceContinuation_zero_residue hrho hzeta
  refine ⟨m, hm, ?_⟩
  apply hres.congr'
  have hdomain : ∀ᶠ s : ℂ in 𝓝[≠] (rho - 1), -(1 / 2 : ℝ) < s.re :=
    (show ∀ᶠ s : ℂ in 𝓝 (rho - 1), s ∈ {w : ℂ | -(1 / 2 : ℝ) < w.re} from
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
        change -(1 / 2 : ℝ) < (rho - 1).re
        norm_num [Complex.sub_re]
        linarith)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hdomain] with s hs
  rw [xiHeatCassiniWoldJointDepthMöbiusNormalTransport_eq_woldLaplaceContinuation hs]

/-- **Unconditional source-to-orbit obstruction.**  A strict-right zero forces the same positive
multiplicity both in the literal normal source residue and in every reflected shift-two
completion: the latter must retain a nonzero compensator.  This removes the critical-energy
premise from the source-level obstruction, but does not construct the noncompact relative
selector needed to exclude that compensator. -/
theorem xiHeatCassiniWoldJointDepthMöbiusNormalTransport_cofinalCompensator
    {rho : ℂ} (hrho : 1 / 2 < rho.re) (hzeta : riemannZeta rho = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun s : ℂ =>
        (s - (rho - 1)) * xiHeatCassiniWoldJointDepthMöbiusNormalTransport s)
        (𝓝[≠] (rho - 1)) (𝓝 (-(m : ℂ))) ∧
      ∀ R E : ℂ →₀ (ℕ →₀ ℂ),
        xiHeatCassiniReflectedWoldPhysicalPoleHead rho m + R =
            GaloisForLFunctions.finiteOrbitCoboundary (2 : ℂ) E →
          R ≠ 0 := by
  obtain ⟨m, hm, hres⟩ :=
    xiHeatCassiniWoldJointDepthMöbiusNormalTransport_zero_residue hrho hzeta
  refine ⟨m, hm, hres, ?_⟩
  intro R E hcompletion
  apply xiHeatCassiniReflectedWoldPhysicalPoleHead_compensator_ne_zero
    (rho := rho) ⟨by linarith, riemannZeta_zero_re_lt_one hzeta⟩
    (by linarith) hm R E hcompletion

end

end RHTower
