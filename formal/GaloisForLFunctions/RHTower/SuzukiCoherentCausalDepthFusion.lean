import GaloisForLFunctions.RHTower.SuzukiCausalDepthFrostmanTransfer
import GaloisForLFunctions.RHTower.SuzukiApertureDressedWallLightCompletion
import GaloisForLFunctions.RHTower.EulerFisherCurvature

/-!
# Suzuki coherent causal-depth fusion

The causal depth resolvent was previously fused separately on each prime ray.  Cubic aperture
innovation supplies enough additional damping to do more: the fused prime rays are absolutely
summable over all primes.  They may therefore be coherently summed before taking a Gram square.

This file proves unconditionally that the resulting scalar field:

* has a uniform logarithmic `p^(-5/4)` majorant;
* is an absolutely convergent all-prime sum;
* obeys functional-equation reflection;
* has an exact absolutely convergent cross-prime Gram expansion; and
* has a faithful global height deficit, vanishing exactly at equal heights.

The new field is a concrete cross-prime source carrier.  Identifying its Gamma-projected covariance
with the actual rectangular Robin--Gamma--holonomy trace and proving the Ward residual lower bound
remain open.  No RH premise, Xi zero, numerical computation, or fitted covariance is used.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Exact endpoint and summable majorant -/

/-- Source endpoint written so that its extra inverse-prime damping is explicit. -/
theorem suzukiCriticalEntryWallEndpointAmplitude_zero_eq_coherentWeight
    (h a : ℝ) (p : Nat.Primes) :
    suzukiCriticalEntryWallEndpointAmplitude h a p 0 =
      Real.sqrt (Real.log (p : ℝ) *
          Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ))) *
        (h * Real.sqrt h)⁻¹ *
        ((p : ℝ) + 1)⁻¹ *
        (1 - xiMobiusContinuousApertureDiskNode ((h / 2) * a) p) ^ 2 := by
  rw [suzukiCriticalEntryWallEndpointAmplitude,
    xiMobiusCubicNormalizedInnovationFeature,
    xiMobiusContinuousApertureDyadicInnovationFeature,
    xiMobiusPrimeContinuousApertureDyadicInnovationFeature,
    xiGammaEulerValuationNat]
  simp only [Nat.cast_pow, pow_zero]
  norm_num
  rw [xiTransversePrimeApertureDiskNode_one_eq_inv]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hden : (p : ℝ) + 1 ≠ 0 := by positivity
  have hdensity :
      Real.log (p : ℝ) / (p : ℝ) *
          Real.exp ((1 / 2 : ℝ) * Real.log (p : ℝ)) =
        Real.log (p : ℝ) * Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) := by
    have hinv : (p : ℝ)⁻¹ = Real.exp (-Real.log (p : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log hp0]
    rw [div_eq_mul_inv, hinv]
    calc
      Real.log (p : ℝ) * Real.exp (-Real.log (p : ℝ)) *
          Real.exp ((1 / 2 : ℝ) * Real.log (p : ℝ)) =
        Real.log (p : ℝ) *
          Real.exp (-Real.log (p : ℝ) +
            (1 / 2 : ℝ) * Real.log (p : ℝ)) := by rw [Real.exp_add]; ring
      _ = _ := by
        congr 2
        ring
  simp only [hdensity]
  have hq : (p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹) = ((p : ℝ) + 1)⁻¹ := by
    have hpne : (p : ℝ) ≠ 0 := hp0.ne'
    simp only [← one_div]
    have hdenform : 1 + 1 / (p : ℝ) = ((p : ℝ) + 1) / (p : ℝ) := by
      calc
        1 + 1 / (p : ℝ) = (p : ℝ) / (p : ℝ) + 1 / (p : ℝ) := by
          rw [div_self hpne]
        _ = ((p : ℝ) + 1) / (p : ℝ) := by rw [add_div]
    rw [hdenform]
    exact div_div_div_cancel_right₀ hpne 1 ((p : ℝ) + 1)
  rw [hq]
  ring_nf

/-- Explicit logarithmic `p^(-5/4)` majorant for one undivided prime endpoint. -/
def suzukiCriticalEntryWallCoherentMajorant (h : ℝ) (p : Nat.Primes) : ℝ :=
  (h * Real.sqrt h)⁻¹ * ((1 + Real.log (p : ℝ)) / 2) *
    Real.exp (-(5 / 4 : ℝ) * Real.log (p : ℝ))

theorem suzukiCriticalEntryWallEndpointAmplitude_zero_le_coherentMajorant
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    suzukiCriticalEntryWallEndpointAmplitude h a p 0 ≤
      suzukiCriticalEntryWallCoherentMajorant h p := by
  rw [suzukiCriticalEntryWallEndpointAmplitude_zero_eq_coherentWeight]
  let l := Real.log (p : ℝ)
  let d := xiMobiusContinuousApertureDiskNode ((h / 2) * a) p
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hl0 : 0 ≤ l := (Real.log_pos (by exact_mod_cast p.property.one_lt)).le
  have hd0 : 0 < d := xiMobiusContinuousApertureDiskNode_pos _ p
  have hd1 : d < 1 := xiMobiusContinuousApertureDiskNode_lt_one
    (mul_pos (half_pos hh) ha) p
  have hC0 : 0 ≤ (h * Real.sqrt h)⁻¹ := by positivity
  have hsqrtExp : Real.sqrt (Real.exp (-(1 / 2 : ℝ) * l)) =
      Real.exp (-(1 / 4 : ℝ) * l) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_nonneg _) (Real.exp_nonneg _)]
    rw [← Real.exp_add]
    congr 1
    ring
  have hsqrt : Real.sqrt (l * Real.exp (-(1 / 2 : ℝ) * l)) =
      Real.sqrt l * Real.exp (-(1 / 4 : ℝ) * l) := by
    rw [Real.sqrt_mul hl0, hsqrtExp]
  have hsqrtLog : Real.sqrt l ≤ (1 + l) / 2 := by
    have hs := sq_nonneg (Real.sqrt l - 1)
    have hsq := Real.sq_sqrt hl0
    nlinarith
  have hinv : ((p : ℝ) + 1)⁻¹ ≤ Real.exp (-l) := by
    have hraw : ((p : ℝ) + 1)⁻¹ ≤ (p : ℝ)⁻¹ := by
      exact (inv_le_inv₀ (by positivity) hp0).2 (by linarith)
    rw [Real.exp_neg, Real.exp_log hp0]
    exact hraw
  have hdSq : (1 - d) ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
  have hnonneg1 : 0 ≤ (1 + l) / 2 := by linarith
  rw [hsqrt]
  change Real.sqrt l * Real.exp (-(1 / 4 : ℝ) * l) *
      (h * Real.sqrt h)⁻¹ * ((p : ℝ) + 1)⁻¹ * (1 - d) ^ 2 ≤ _
  dsimp only [suzukiCriticalEntryWallCoherentMajorant]
  change _ ≤ (h * Real.sqrt h)⁻¹ * ((1 + l) / 2) *
    Real.exp (-(5 / 4 : ℝ) * l)
  calc
    Real.sqrt l * Real.exp (-(1 / 4 : ℝ) * l) *
        (h * Real.sqrt h)⁻¹ * ((p : ℝ) + 1)⁻¹ * (1 - d) ^ 2
      ≤ ((1 + l) / 2) * Real.exp (-(1 / 4 : ℝ) * l) *
        (h * Real.sqrt h)⁻¹ * Real.exp (-l) * 1 := by gcongr
    _ = (h * Real.sqrt h)⁻¹ * ((1 + l) / 2) *
        Real.exp (-(5 / 4 : ℝ) * l) := by
      have hExp : Real.exp (-(1 / 4 : ℝ) * l) * Real.exp (-l) =
          Real.exp (-(5 / 4 : ℝ) * l) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hExp]
      ring

theorem summable_suzukiCriticalEntryWallCoherentMajorant (h : ℝ) :
    Summable (suzukiCriticalEntryWallCoherentMajorant h) := by
  have hbeta : (1 : ℝ) < 5 / 4 := by norm_num
  have h0 : Summable (fun p : Nat.Primes =>
      (p : ℝ) ^ (-(5 / 4 : ℝ))) := by
    have hn : Summable (fun n : ℕ =>
        |Real.log n| ^ 0 * (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
      summable_abs_log_natCast_pow_mul_rpow_neg 0 (5 / 4) hbeta
    simpa [Function.comp_def] using
      hn.comp_injective (i := fun p : Nat.Primes => (p : ℕ))
        Subtype.val_injective
  have h1 : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) * (p : ℝ) ^ (-(5 / 4 : ℝ))) := by
    have hn : Summable (fun n : ℕ =>
        |Real.log n| ^ 1 * (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
      summable_abs_log_natCast_pow_mul_rpow_neg 1 (5 / 4) hbeta
    have hp := hn.comp_injective (i := fun p : Nat.Primes => (p : ℕ))
      Subtype.val_injective
    refine hp.congr (fun p => ?_)
    have hl : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.property.one_lt)
    simp [abs_of_pos hl]
  have hsum : Summable (fun p : Nat.Primes =>
      (1 + Real.log (p : ℝ)) * (p : ℝ) ^ (-(5 / 4 : ℝ))) := by
    convert h0.add h1 using 1
    funext p
    ring
  refine (hsum.mul_left ((h * Real.sqrt h)⁻¹ / 2)).congr (fun p => ?_)
  rw [suzukiCriticalEntryWallCoherentMajorant, Real.rpow_def_of_pos
    (by exact_mod_cast p.property.pos : (0 : ℝ) < (p : ℝ))]
  ring_nf

/-! ## Absolute all-prime coherent fusion -/

/-- Uniform cap for every causal depth radius over the prime set. -/
def suzukiCoherentCausalDepthRadiusCap : ℝ :=
  Real.exp (-(1 / 4 : ℝ) * Real.log 2)

/-- Majorant after the valuation-depth resolvent is summed. -/
def suzukiCriticalApertureDepthFusedCoherentMajorant
    (h : ℝ) (p : Nat.Primes) : ℝ :=
  (1 - suzukiCoherentCausalDepthRadiusCap)⁻¹ *
    suzukiCriticalEntryWallCoherentMajorant h p

theorem suzukiCoherentCausalDepthRadiusCap_lt_one :
    suzukiCoherentCausalDepthRadiusCap < 1 := by
  rw [suzukiCoherentCausalDepthRadiusCap, Real.exp_lt_one_iff]
  have : 0 < Real.log 2 := Real.log_pos one_lt_two
  nlinarith

theorem suzukiCriticalApertureDepthFusionRadius_le_coherentCap
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    suzukiCriticalApertureDepthFusionRadius h a p ≤
      suzukiCoherentCausalDepthRadiusCap := by
  rw [suzukiCriticalApertureDepthFusionRadius, suzukiCoherentCausalDepthRadiusCap]
  let d := xiMobiusContinuousApertureDiskNode ((h / 2) * a) p
  have hd0 : 0 ≤ d := (xiMobiusContinuousApertureDiskNode_pos _ p).le
  have hd1 : d < 1 := xiMobiusContinuousApertureDiskNode_lt_one
    (mul_pos (half_pos hh) ha) p
  have hdSq : d ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
  have hlog : Real.log 2 ≤ Real.log (p : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast p.property.two_le
  have hexp : Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ)) ≤
      Real.exp (-(1 / 4 : ℝ) * Real.log 2) := by
    rw [Real.exp_le_exp]
    nlinarith
  exact (mul_le_of_le_one_right (Real.exp_nonneg _) hdSq).trans hexp

theorem norm_suzukiCriticalApertureDepthFusionPhase
    (t : ℝ) (p : Nat.Primes) :
    ‖suzukiCriticalApertureDepthFusionPhase t p‖ = 1 := by
  rw [suzukiCriticalApertureDepthFusionPhase, HTGeometry.phaseClockValue,
    Complex.norm_exp_ofReal_mul_I]

theorem norm_suzukiCriticalApertureDepthFusedAtom_le_coherentMajorant
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    ‖suzukiCriticalApertureDepthFusedAtom h a t p‖ ≤
      suzukiCriticalApertureDepthFusedCoherentMajorant h p := by
  rw [suzukiCriticalApertureDepthFusedAtom_eq_mobius hh ha]
  let r := suzukiCriticalApertureDepthFusionRadius h a p
  let z := suzukiCriticalApertureDepthFusionPhase t p
  have hr0 : 0 < r := suzukiCriticalApertureDepthFusionRadius_pos h a p
  have hrCap : r ≤ suzukiCoherentCausalDepthRadiusCap :=
    suzukiCriticalApertureDepthFusionRadius_le_coherentCap hh ha p
  have hcap1 : suzukiCoherentCausalDepthRadiusCap < 1 :=
    suzukiCoherentCausalDepthRadiusCap_lt_one
  have hbase : 0 < 1 - suzukiCoherentCausalDepthRadiusCap := sub_pos.mpr hcap1
  have hz : ‖z‖ = 1 := norm_suzukiCriticalApertureDepthFusionPhase t p
  have hrz : ‖(r : ℂ) * z‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hz, mul_one]
  have hdenLower :
      1 - suzukiCoherentCausalDepthRadiusCap ≤ ‖1 - (r : ℂ) * z‖ := by
    calc
      1 - suzukiCoherentCausalDepthRadiusCap ≤ 1 - r := by linarith
      _ ≤ ‖(1 : ℂ) - (r : ℂ) * z‖ := by
        have hnorm := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * z)
        rw [norm_one, hrz] at hnorm
        exact hnorm
  have hdenPos : 0 < ‖1 - (r : ℂ) * z‖ := hbase.trans_le hdenLower
  have hinv : ‖(1 - (r : ℂ) * z)⁻¹‖ ≤
      (1 - suzukiCoherentCausalDepthRadiusCap)⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ hdenPos hbase).2 hdenLower
  have hA0 := suzukiCriticalEntryWallEndpointAmplitude_zero_pos hh ha p |>.le
  have hAle :=
    suzukiCriticalEntryWallEndpointAmplitude_zero_le_coherentMajorant hh ha p
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hA0, hz, mul_one]
  rw [suzukiCriticalApertureDepthFusedCoherentMajorant]
  have hM0 : 0 ≤ suzukiCriticalEntryWallCoherentMajorant h p := by
    rw [suzukiCriticalEntryWallCoherentMajorant]
    positivity
  have hmul := mul_le_mul hAle hinv (norm_nonneg _) hM0
  simpa [mul_comm] using hmul

theorem summable_suzukiCriticalApertureDepthFusedCoherentMajorant (h : ℝ) :
    Summable (suzukiCriticalApertureDepthFusedCoherentMajorant h) := by
  exact (summable_suzukiCriticalEntryWallCoherentMajorant h).mul_left
    (1 - suzukiCoherentCausalDepthRadiusCap)⁻¹

/-- The valuation-fused rays are `ell^(1 : ℕ)` over all primes, uniformly in height. -/
theorem summable_norm_suzukiCriticalApertureDepthFusedAtom_allPrime
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) :
    Summable (fun p : Nat.Primes =>
      ‖suzukiCriticalApertureDepthFusedAtom h a t p‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_suzukiCriticalApertureDepthFusedAtom_le_coherentMajorant hh ha t)
    (summable_suzukiCriticalApertureDepthFusedCoherentMajorant h)

theorem summable_suzukiCriticalApertureDepthFusedAtom_allPrime
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) :
    Summable (fun p : Nat.Primes =>
      suzukiCriticalApertureDepthFusedAtom h a t p) :=
  summable_norm_iff.mp
    (summable_norm_suzukiCriticalApertureDepthFusedAtom_allPrime hh ha t)

/-- Coherent fusion of all prime rays before taking the Gram square. -/
def suzukiCriticalApertureCoherentlyFusedAtom (h a t : ℝ) : ℂ :=
  ∑' p : Nat.Primes, suzukiCriticalApertureDepthFusedAtom h a t p

/-! ## Reflection and cross-prime Gram -/

theorem suzukiCriticalApertureDepthFusedAtom_neg_eq_star
    (h a t : ℝ) (p : Nat.Primes) :
    suzukiCriticalApertureDepthFusedAtom h a (-t) p =
      star (suzukiCriticalApertureDepthFusedAtom h a t p) := by
  rw [suzukiCriticalApertureDepthFusedAtom]
  calc
    (∑' e : ℕ, suzukiCriticalApertureBoundaryAtom h a (-t) p e) =
        ∑' e : ℕ, star (suzukiCriticalApertureBoundaryAtom h a t p e) := by
          apply tsum_congr
          intro e
          exact suzukiCriticalApertureBoundaryAtom_neg_eq_star h a t p e
    _ = star (∑' e : ℕ, suzukiCriticalApertureBoundaryAtom h a t p e) :=
      tsum_star.symm

theorem suzukiCriticalApertureCoherentlyFusedAtom_neg_eq_star
    (h a t : ℝ) :
    suzukiCriticalApertureCoherentlyFusedAtom h a (-t) =
      star (suzukiCriticalApertureCoherentlyFusedAtom h a t) := by
  rw [suzukiCriticalApertureCoherentlyFusedAtom,
    suzukiCriticalApertureCoherentlyFusedAtom]
  calc
    (∑' p : Nat.Primes, suzukiCriticalApertureDepthFusedAtom h a (-t) p) =
        ∑' p : Nat.Primes,
          star (suzukiCriticalApertureDepthFusedAtom h a t p) := by
            apply tsum_congr
            exact suzukiCriticalApertureDepthFusedAtom_neg_eq_star h a t
    _ = star (∑' p : Nat.Primes,
        suzukiCriticalApertureDepthFusedAtom h a t p) := tsum_star.symm

/-- Every finite coherent packet has the literal full cross-prime Gram expansion. -/
theorem normSq_suzukiCriticalApertureCoherentFiniteSum_eq_crossPrimeGram
    (h a t : ℝ) (F : Finset Nat.Primes) :
    ((Complex.normSq
        (∑ p ∈ F, suzukiCriticalApertureDepthFusedAtom h a t p) : ℝ) : ℂ) =
      ∑ p ∈ F, ∑ q ∈ F,
        star (suzukiCriticalApertureDepthFusedAtom h a t p) *
          suzukiCriticalApertureDepthFusedAtom h a t q := by
  rw [Complex.normSq_eq_conj_mul_self]
  rw [map_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro q _hq
  rfl

/-- The cofinal coherent energy is an absolutely convergent double-prime Gram, including all
off-diagonal cross-prime terms. -/
theorem normSq_suzukiCriticalApertureCoherentlyFusedAtom_eq_crossPrimeGram
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) :
    ((Complex.normSq (suzukiCriticalApertureCoherentlyFusedAtom h a t) : ℝ) : ℂ) =
      ∑' pq : Nat.Primes × Nat.Primes,
        star (suzukiCriticalApertureDepthFusedAtom h a t pq.1) *
          suzukiCriticalApertureDepthFusedAtom h a t pq.2 := by
  let f : Nat.Primes → ℂ := fun p =>
    suzukiCriticalApertureDepthFusedAtom h a t p
  have hfnorm : Summable (fun p => ‖f p‖) :=
    summable_norm_suzukiCriticalApertureDepthFusedAtom_allPrime hh ha t
  have hf : Summable f := summable_norm_iff.mp hfnorm
  have hprodNorm : Summable (fun pq : Nat.Primes × Nat.Primes =>
      ‖f pq.1‖ * ‖f pq.2‖) :=
    hfnorm.mul_of_nonneg hfnorm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hprod : Summable (fun pq : Nat.Primes × Nat.Primes =>
      star (f pq.1) * f pq.2) := by
    rw [← summable_norm_iff]
    convert hprodNorm using 1
    funext pq
    rw [norm_mul, norm_star]
  rw [suzukiCriticalApertureCoherentlyFusedAtom,
    Complex.normSq_eq_conj_mul_self]
  change star (∑' p : Nat.Primes,
      suzukiCriticalApertureDepthFusedAtom h a t p) *
    (∑' p : Nat.Primes, suzukiCriticalApertureDepthFusedAtom h a t p) = _
  rw [tsum_star]
  exact hf.star.tsum_mul_tsum hf hprod

/-! ## Faithful global height separator -/

theorem suzukiCriticalApertureDepthFusedAtom_zero_eq_ofReal
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    suzukiCriticalApertureDepthFusedAtom h a 0 p =
      ((suzukiCriticalEntryWallEndpointAmplitude h a p 0 /
        (1 - suzukiCriticalApertureDepthFusionRadius h a p) : ℝ) : ℂ) := by
  rw [suzukiCriticalApertureDepthFusedAtom_eq_mobius hh ha]
  simp [suzukiCriticalApertureDepthFusionPhase, HTGeometry.phaseClockValue]
  rw [div_eq_mul_inv]

theorem suzukiCriticalApertureDepthFusedAtom_zero_eq_norm
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    suzukiCriticalApertureDepthFusedAtom h a 0 p =
      (‖suzukiCriticalApertureDepthFusedAtom h a 0 p‖ : ℂ) := by
  rw [suzukiCriticalApertureDepthFusedAtom_zero_eq_ofReal hh ha]
  have hA := suzukiCriticalEntryWallEndpointAmplitude_zero_pos hh ha p
  have hr := suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hA (sub_pos.mpr hr))]

/-- Sum of the positive central ray amplitudes. -/
def suzukiCriticalApertureCoherentCap (h a : ℝ) : ℝ :=
  ∑' p : Nat.Primes, ‖suzukiCriticalApertureDepthFusedAtom h a 0 p‖

theorem suzukiCriticalApertureCoherentlyFusedAtom_zero_eq_cap
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    suzukiCriticalApertureCoherentlyFusedAtom h a 0 =
      (suzukiCriticalApertureCoherentCap h a : ℂ) := by
  rw [suzukiCriticalApertureCoherentlyFusedAtom,
    suzukiCriticalApertureCoherentCap, ofReal_tsum]
  apply tsum_congr
  exact suzukiCriticalApertureDepthFusedAtom_zero_eq_norm hh ha

theorem norm_suzukiCriticalApertureDepthFusedAtom_le_zero
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    ‖suzukiCriticalApertureDepthFusedAtom h a t p‖ ≤
      ‖suzukiCriticalApertureDepthFusedAtom h a 0 p‖ := by
  have heq :=
    normSq_suzukiCriticalApertureDepthFusedAtom_eq_zero_mul_frostmanProfile
      hh ha t p
  have hprofile := suzukiCriticalApertureDepthFrostmanProfile_le_one hh ha t p
  have hsq : Complex.normSq (suzukiCriticalApertureDepthFusedAtom h a t p) ≤
      Complex.normSq (suzukiCriticalApertureDepthFusedAtom h a 0 p) := by
    rw [heq]
    exact mul_le_of_le_one_right (Complex.normSq_nonneg _) hprofile
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem suzukiCriticalApertureCoherentCap_nonneg (h a : ℝ) :
    0 ≤ suzukiCriticalApertureCoherentCap h a := by
  rw [suzukiCriticalApertureCoherentCap]
  exact tsum_nonneg fun _ => norm_nonneg _

theorem norm_suzukiCriticalApertureCoherentlyFusedAtom_le_cap
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) :
    ‖suzukiCriticalApertureCoherentlyFusedAtom h a t‖ ≤
      suzukiCriticalApertureCoherentCap h a := by
  have ht := summable_norm_suzukiCriticalApertureDepthFusedAtom_allPrime hh ha t
  have h0 := summable_norm_suzukiCriticalApertureDepthFusedAtom_allPrime hh ha 0
  calc
    ‖suzukiCriticalApertureCoherentlyFusedAtom h a t‖ ≤
        ∑' p : Nat.Primes,
          ‖suzukiCriticalApertureDepthFusedAtom h a t p‖ := by
      rw [suzukiCriticalApertureCoherentlyFusedAtom]
      exact norm_tsum_le_tsum_norm ht
    _ ≤ ∑' p : Nat.Primes,
          ‖suzukiCriticalApertureDepthFusedAtom h a 0 p‖ :=
      ht.tsum_mono h0 (norm_suzukiCriticalApertureDepthFusedAtom_le_zero hh ha t)
    _ = suzukiCriticalApertureCoherentCap h a := rfl

/-- Translation-invariant deficit from the coherent all-prime cap. -/
def suzukiCriticalApertureCoherentSeparation
    (h a t u : ℝ) : ℝ :=
  suzukiCriticalApertureCoherentCap h a ^ 2 -
    Complex.normSq (suzukiCriticalApertureCoherentlyFusedAtom h a (t - u))

theorem suzukiCriticalApertureCoherentSeparation_nonneg
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t u : ℝ) :
    0 ≤ suzukiCriticalApertureCoherentSeparation h a t u := by
  have hnorm := norm_suzukiCriticalApertureCoherentlyFusedAtom_le_cap hh ha (t - u)
  have hcap := suzukiCriticalApertureCoherentCap_nonneg h a
  rw [suzukiCriticalApertureCoherentSeparation, Complex.normSq_eq_norm_sq]
  exact sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) hcap).mpr hnorm)

private def coherentPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩
private def coherentPrimeThree : Nat.Primes := ⟨3, Nat.prime_three⟩

private theorem coherentPrimeTwo_ne_coherentPrimeThree :
    coherentPrimeTwo ≠ coherentPrimeThree := by
  intro h
  have := congrArg Subtype.val h
  norm_num [coherentPrimeTwo, coherentPrimeThree] at this

/-- **Faithful coherent height separation.**  The global cross-prime energy reaches its cap
exactly at equal real heights. -/
theorem suzukiCriticalApertureCoherentSeparation_eq_zero_iff
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t u : ℝ) :
    suzukiCriticalApertureCoherentSeparation h a t u = 0 ↔ t = u := by
  let s := t - u
  let f0 : Nat.Primes → ℝ := fun p =>
    ‖suzukiCriticalApertureDepthFusedAtom h a 0 p‖
  let fs : Nat.Primes → ℝ := fun p =>
    ‖suzukiCriticalApertureDepthFusedAtom h a s p‖
  have hf0 : Summable f0 :=
    summable_norm_suzukiCriticalApertureDepthFusedAtom_allPrime hh ha 0
  have hfs : Summable fs :=
    summable_norm_suzukiCriticalApertureDepthFusedAtom_allPrime hh ha s
  have hpoint : ∀ p, fs p ≤ f0 p :=
    norm_suzukiCriticalApertureDepthFusedAtom_le_zero hh ha s
  have hcap : 0 ≤ suzukiCriticalApertureCoherentCap h a :=
    suzukiCriticalApertureCoherentCap_nonneg h a
  constructor
  · intro hsep
    have hglobal : ‖suzukiCriticalApertureCoherentlyFusedAtom h a s‖ =
        suzukiCriticalApertureCoherentCap h a := by
      have hsq : suzukiCriticalApertureCoherentCap h a ^ 2 =
          ‖suzukiCriticalApertureCoherentlyFusedAtom h a s‖ ^ 2 := by
        rw [suzukiCriticalApertureCoherentSeparation,
          Complex.normSq_eq_norm_sq] at hsep
        linarith
      exact (sq_eq_sq₀ (norm_nonneg _) hcap).mp hsq.symm
    have hnormTsum : ‖suzukiCriticalApertureCoherentlyFusedAtom h a s‖ ≤
        ∑' p, fs p := by
      rw [suzukiCriticalApertureCoherentlyFusedAtom]
      exact norm_tsum_le_tsum_norm hfs
    have hsumLe : (∑' p, fs p) ≤ suzukiCriticalApertureCoherentCap h a := by
      change (∑' p, fs p) ≤ ∑' p, f0 p
      exact hfs.tsum_mono hf0 hpoint
    have hsumEq : (∑' p, fs p) = suzukiCriticalApertureCoherentCap h a := by
      linarith
    let d : Nat.Primes → ℝ := fun p => f0 p - fs p
    have hd : Summable d := hf0.sub hfs
    have hd0 : ∀ p, 0 ≤ d p := fun p => sub_nonneg.mpr (hpoint p)
    have hdSum : (∑' p, d p) = 0 := by
      rw [show (∑' p, d p) = (∑' p, f0 p) - ∑' p, fs p by
        exact hf0.tsum_sub hfs]
      change suzukiCriticalApertureCoherentCap h a - ∑' p, fs p = 0
      rw [hsumEq]
      ring
    have hdPoint : ∀ p, d p = 0 := by
      intro p
      have hsplit := hd.tsum_eq_add_tsum_ite p
      rw [hdSum] at hsplit
      have hrest : 0 ≤ ∑' q, if q = p then 0 else d q :=
        tsum_nonneg fun q => by
          by_cases hqp : q = p
          · simp [hqp]
          · simpa [hqp] using hd0 q
      have hdp := hd0 p
      linarith
    have hprof (p : Nat.Primes) :
        suzukiCriticalApertureDepthFrostmanProfile h a s p = 1 := by
      have hnorm : fs p = f0 p := by
        have hp := hdPoint p
        dsimp only [d] at hp
        linarith
      have hsq : Complex.normSq
          (suzukiCriticalApertureDepthFusedAtom h a s p) =
          Complex.normSq (suzukiCriticalApertureDepthFusedAtom h a 0 p) := by
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
        exact congrArg (fun x : ℝ => x ^ 2) hnorm
      rw [← normSq_suzukiCriticalApertureDepthFusedAtom_div_zero_eq_frostmanProfile
        hh ha s p, hsq]
      exact div_self
        (normSq_suzukiCriticalApertureDepthFusedAtom_zero_pos hh ha p).ne'
    have hpair :
        suzukiCriticalApertureDepthFrostmanPairProfile h a s
          coherentPrimeTwo coherentPrimeThree = 2 := by
      rw [suzukiCriticalApertureDepthFrostmanPairProfile,
        hprof coherentPrimeTwo, hprof coherentPrimeThree]
      norm_num
    have hs0 := (suzukiCriticalApertureDepthFrostmanPairProfile_eq_two_iff
      hh ha coherentPrimeTwo_ne_coherentPrimeThree s).mp hpair
    exact sub_eq_zero.mp hs0
  · rintro rfl
    rw [suzukiCriticalApertureCoherentSeparation]
    have hzero := suzukiCriticalApertureCoherentlyFusedAtom_zero_eq_cap hh ha
    rw [sub_self, hzero, Complex.normSq_ofReal]
    ring

end

end RHTower
