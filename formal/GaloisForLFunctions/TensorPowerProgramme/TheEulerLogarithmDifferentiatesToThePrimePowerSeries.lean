import GaloisForLFunctions.RHTower.NumberFieldFinitePlaceNormSummability
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Euler logarithm differentiates to the prime-power series

For a number field `K` and coefficients `c_v` of size at most one at the nonzero primes `v` of
`𝓞 K`, the Euler logarithm `S(w) = Σ_v −log(1 − c_v N(v)^{−w})` (`eulerLog`) is holomorphic on
`Re w > 1`, and

`−S'(w) = Σ_{v, m ≥ 0} log N(v) · (c_v N(v)^{−w})^{m+1}`   (`deriv_eulerLog`).

So every `L`-function that is the exponential of its Euler logarithm on `Re w > 1` has
`−L'/L` equal to the prime-power series (`neg_deriv_div_eq_primePowerSeries`): the logarithmic
derivative runs over the powers of the prime ideals, weighted by `log N(v)`. This is the analytic
package of the abelian base of a number field.
-/

open Complex Filter Topology
open NumberField IsDedekindDomain

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

variable {K : Type*} [Field K] [NumberField K]

theorem two_le_absNorm_prime (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ v.asIdeal.absNorm := by
  have h0 : v.asIdeal.absNorm ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : v.asIdeal.absNorm ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

/-- The Euler-factor ratio `c_v N(v)^{−w}`. -/
def eulerRatio (c : HeightOneSpectrum (𝓞 K) → ℂ) (w : ℂ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  c v * (v.asIdeal.absNorm : ℂ) ^ (-w)

/-- The Euler logarithm `Σ_v −log(1 − c_v N(v)^{−w})`. -/
def eulerLog (c : HeightOneSpectrum (𝓞 K) → ℂ) (w : ℂ) : ℂ :=
  ∑' v, -Complex.log (1 - eulerRatio c w v)

/-- The prime-power series `Σ_{v, m} log N(v) (c_v N(v)^{−w})^{m+1}`. -/
def primePowerSeries (c : HeightOneSpectrum (𝓞 K) → ℂ) (w : ℂ) : ℂ :=
  ∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
    (Real.log p.1.asIdeal.absNorm : ℂ) * eulerRatio c w p.1 ^ (p.2 + 1)

variable {c : HeightOneSpectrum (𝓞 K) → ℂ}

theorem norm_eulerRatio_le (hc : ∀ v, ‖c v‖ ≤ 1) (w : ℂ) (v : HeightOneSpectrum (𝓞 K)) :
    ‖eulerRatio c w v‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-w.re) := by
  have hv0 : 0 < v.asIdeal.absNorm := lt_of_lt_of_le two_pos (two_le_absNorm_prime v)
  rw [eulerRatio, norm_mul, Complex.norm_natCast_cpow_of_pos hv0, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hc v)

/-- On `Re w ≥ σ > 1` the ratio is at most `N(v)^{−σ} ≤ 2^{−σ} < 1/2`. -/
theorem norm_eulerRatio_le_half (hc : ∀ v, ‖c v‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {w : ℂ}
    (hw : σ ≤ w.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖eulerRatio c w v‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-σ) ∧
      (v.asIdeal.absNorm : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have hv2 : (2 : ℝ) ≤ v.asIdeal.absNorm := by exact_mod_cast two_le_absNorm_prime v
  refine ⟨(norm_eulerRatio_le hc w v).trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)), ?_⟩
  calc (v.asIdeal.absNorm : ℝ) ^ (-σ) ≤ (v.asIdeal.absNorm : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = ((v.asIdeal.absNorm : ℝ))⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith

/-- The derivative of one Euler logarithm: `d/dw [−log(1 − r)] = −log N(v) · r/(1 − r)`. -/
theorem hasDerivAt_neg_log_one_sub_eulerRatio (hc : ∀ v, ‖c v‖ ≤ 1) {w : ℂ} (hw : 1 < w.re)
    (v : HeightOneSpectrum (𝓞 K)) :
    HasDerivAt (fun w => -Complex.log (1 - eulerRatio c w v))
      (-((Real.log v.asIdeal.absNorm : ℂ) * eulerRatio c w v / (1 - eulerRatio c w v))) w := by
  have hv0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le two_pos (two_le_absNorm_prime v)).ne'
  -- derivative of the ratio
  have hr : HasDerivAt (fun w => eulerRatio c w v)
      (-(Real.log v.asIdeal.absNorm : ℂ) * eulerRatio c w v) w := by
    show HasDerivAt (fun w => c v * (v.asIdeal.absNorm : ℂ) ^ (-w)) _ w
    have h1 : HasDerivAt (fun w : ℂ => -w) (-1) w := (hasDerivAt_id w).neg
    have h3 := (h1.const_cpow (c := (v.asIdeal.absNorm : ℂ)) (Or.inl hv0)).const_mul (c v)
    refine h3.congr_deriv ?_
    simp only [eulerRatio, ← Complex.natCast_log]
    ring
  have hlt : ‖eulerRatio c w v‖ < 1 :=
    lt_of_le_of_lt (norm_eulerRatio_le_half hc hw le_rfl v).1
      (lt_of_le_of_lt (norm_eulerRatio_le_half hc hw le_rfl v).2 (by norm_num))
  have hslit : 1 - eulerRatio c w v ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have := Complex.re_le_norm (eulerRatio c w v)
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hlog := ((hasDerivAt_const w (1 : ℂ)).sub hr).clog hslit
  refine hlog.neg.congr_deriv ?_
  simp only [Pi.sub_apply]
  ring

/-- The open half-plane `Re z > σ`. -/
theorem isOpen_re_gt (σ : ℝ) : IsOpen {z : ℂ | σ < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem norm_neg_log_one_sub_le (hc : ∀ v, ‖c v‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {w : ℂ}
    (hw : σ ≤ w.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖-Complex.log (1 - eulerRatio c w v)‖ ≤ 3 / 2 * (v.asIdeal.absNorm : ℝ) ^ (-σ) := by
  obtain ⟨h1, h2⟩ := norm_eulerRatio_le_half hc hσ hw v
  have hhalf : ‖-eulerRatio c w v‖ ≤ 1 / 2 := by rw [norm_neg]; linarith
  have hlog := Complex.norm_log_one_add_half_le_self hhalf
  rw [← sub_eq_add_neg, norm_neg] at hlog
  rw [norm_neg]
  exact hlog.trans (mul_le_mul_of_nonneg_left h1 (by norm_num))

/-- The Euler logarithm is holomorphic on `Re w > 1`. -/
theorem differentiableAt_eulerLog (hc : ∀ v, ‖c v‖ ≤ 1) {w : ℂ} (hw : 1 < w.re) :
    DifferentiableAt ℂ (eulerLog c) w := by
  set σ := (1 + w.re) / 2 with hσdef
  have hσ : 1 < σ := by rw [hσdef]; linarith
  have hwσ : σ < w.re := by rw [hσdef]; linarith
  have hu := (numberField_summable_finitePlace_absNorm_rpow (K := K) hσ).mul_left (3 / 2 : ℝ)
  have hd := Complex.differentiableOn_tsum_of_summable_norm hu
    (fun v z hz => (hasDerivAt_neg_log_one_sub_eulerRatio hc (lt_trans hσ hz) v).differentiableAt
      |>.differentiableWithinAt) (isOpen_re_gt σ)
    (fun v z hz => norm_neg_log_one_sub_le hc hσ (le_of_lt hz) v)
  exact hd.differentiableAt ((isOpen_re_gt σ).mem_nhds hwσ)

/-- The derivative of the Euler logarithm is the sum of the derivatives of its terms. -/
theorem hasSum_deriv_eulerLog (hc : ∀ v, ‖c v‖ ≤ 1) {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun v => -((Real.log v.asIdeal.absNorm : ℂ) * eulerRatio c w v /
      (1 - eulerRatio c w v))) (deriv (eulerLog c) w) := by
  set σ := (1 + w.re) / 2 with hσdef
  have hσ : 1 < σ := by rw [hσdef]; linarith
  have hwσ : σ < w.re := by rw [hσdef]; linarith
  have hu := (numberField_summable_finitePlace_absNorm_rpow (K := K) hσ).mul_left (3 / 2 : ℝ)
  have h := Complex.hasSum_deriv_of_summable_norm hu
    (fun v z hz => (hasDerivAt_neg_log_one_sub_eulerRatio hc (lt_trans hσ hz) v).differentiableAt
      |>.differentiableWithinAt) (isOpen_re_gt σ)
    (fun v z hz => norm_neg_log_one_sub_le hc hσ (le_of_lt hz) v) (show w ∈ {z : ℂ | σ < z.re} from hwσ)
  have hfun : (fun v => deriv (fun w => -Complex.log (1 - eulerRatio c w v)) w) =
      fun v => -((Real.log v.asIdeal.absNorm : ℂ) * eulerRatio c w v / (1 - eulerRatio c w v)) :=
    funext fun v => (hasDerivAt_neg_log_one_sub_eulerRatio hc hw v).deriv
  rw [hfun] at h
  exact h

/-- The real majorant `Σ_{v,m} log N(v) · (N(v)^{−σ})^{m+1}` converges for `σ > 1`: the level sums
are `log N(v) · q/(1 − q) ≤ 2 log N(v) N(v)^{−σ}`, and `log N(v) ≤ N(v)^δ/δ` leaves the prime sum at
exponent `σ − δ > 1`. -/
theorem summable_log_mul_rpow_pow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : HeightOneSpectrum (𝓞 K) × ℕ =>
      Real.log p.1.asIdeal.absNorm * ((p.1.asIdeal.absNorm : ℝ) ^ (-σ)) ^ (p.2 + 1) := by
  set δ := (σ - 1) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hσδ : 1 < σ - δ := by rw [hδ]; linarith
  set q : HeightOneSpectrum (𝓞 K) → ℝ := fun v => (v.asIdeal.absNorm : ℝ) ^ (-σ)
  have hq0 : ∀ v, 0 ≤ q v := fun v => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hqh : ∀ v, q v ≤ 1 / 2 := fun v =>
    (norm_eulerRatio_le_half (c := fun _ => 1) (fun _ => by simp) hσ (w := (σ : ℂ)) (by simp) v).2
  have hlog0 : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ Real.log v.asIdeal.absNorm := fun v =>
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ v.asIdeal.absNorm by
      linarith [two_le_absNorm_prime v]))
  set M : HeightOneSpectrum (𝓞 K) × ℕ → ℝ := fun p => Real.log p.1.asIdeal.absNorm * q p.1 ^ (p.2 + 1)
  have hM0 : 0 ≤ M := fun p => mul_nonneg (hlog0 _) (pow_nonneg (hq0 _) _)
  have hfib : ∀ v, HasSum (fun m : ℕ => M (v, m)) (Real.log v.asIdeal.absNorm * (q v * (1 - q v)⁻¹)) := by
    intro v
    have hg := hasSum_geometric_of_lt_one (hq0 v) (by linarith [hqh v])
    have h2 := (hg.mul_left (q v)).mul_left (Real.log v.asIdeal.absNorm)
    have hfun : (fun i : ℕ => Real.log v.asIdeal.absNorm * (q v * q v ^ i)) =
        fun m : ℕ => M (v, m) := funext fun m => by
      show _ = Real.log v.asIdeal.absNorm * q v ^ (m + 1)
      rw [pow_succ']
    rw [hfun] at h2
    exact h2
  show Summable M
  refine (summable_prod_of_nonneg hM0).mpr ⟨fun v => (hfib v).summable, ?_⟩
  have hmaj := (numberField_summable_finitePlace_absNorm_rpow (K := K) hσδ).mul_left (2 / δ)
  refine Summable.of_nonneg_of_le (fun v => tsum_nonneg fun m => hM0 (v, m)) (fun v => ?_) hmaj
  rw [(hfib v).tsum_eq]
  have hv1 : (1 : ℝ) ≤ v.asIdeal.absNorm := by
    exact_mod_cast (show 1 ≤ v.asIdeal.absNorm by linarith [two_le_absNorm_prime v])
  have hv0 : (0 : ℝ) < v.asIdeal.absNorm := by linarith
  have hlogle : Real.log v.asIdeal.absNorm ≤ (v.asIdeal.absNorm : ℝ) ^ δ / δ :=
    Real.log_le_rpow_div hv0.le hδ0
  have hgeo : q v * (1 - q v)⁻¹ ≤ 2 * q v := by
    have h1 : (1 / 2 : ℝ) ≤ 1 - q v := by linarith [hqh v]
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
    nlinarith [hq0 v]
  calc Real.log v.asIdeal.absNorm * (q v * (1 - q v)⁻¹)
      ≤ ((v.asIdeal.absNorm : ℝ) ^ δ / δ) * (2 * q v) :=
        mul_le_mul hlogle hgeo (mul_nonneg (hq0 v) (inv_nonneg.mpr (by linarith [hqh v])))
          (by positivity)
    _ = 2 / δ * (v.asIdeal.absNorm : ℝ) ^ (-(σ - δ)) := by
        simp only [q]
        rw [show -(σ - δ) = δ + -σ by ring, Real.rpow_add hv0]
        ring

/-- The prime-power series converges and regroups by primes:
`Σ_m log N(v) r^{m+1} = log N(v) · r/(1 − r)`. -/
theorem hasSum_primePowerSeries (hc : ∀ v, ‖c v‖ ≤ 1) {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun v => (Real.log v.asIdeal.absNorm : ℂ) * eulerRatio c w v / (1 - eulerRatio c w v))
      (primePowerSeries c w) := by
  have hq : ∀ v, ‖eulerRatio c w v‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-w.re) ∧
      (v.asIdeal.absNorm : ℝ) ^ (-w.re) ≤ 1 / 2 := fun v =>
    norm_eulerRatio_le_half hc hw le_rfl v
  have hlog0 : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ Real.log v.asIdeal.absNorm := fun v =>
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ v.asIdeal.absNorm by
      linarith [two_le_absNorm_prime v]))
  -- the complex series is dominated by the real majorant
  have hfsum : Summable fun p : HeightOneSpectrum (𝓞 K) × ℕ =>
      (Real.log p.1.asIdeal.absNorm : ℂ) * eulerRatio c w p.1 ^ (p.2 + 1) := by
    refine Summable.of_norm ((summable_log_mul_rpow_pow (K := K) hw).of_nonneg_of_le
      (fun p => norm_nonneg _) fun p => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hlog0 _), norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hq p.1).1 _) (hlog0 _)
  refine hfsum.hasSum.prod_fiberwise fun v => ?_
  have hr1 : ‖eulerRatio c w v‖ < 1 := lt_of_le_of_lt (hq v).1 (by linarith [(hq v).2])
  have hg := (hasSum_geometric_of_norm_lt_one hr1).mul_left
    ((Real.log v.asIdeal.absNorm : ℂ) * eulerRatio c w v)
  have hfun : (fun i : ℕ => (Real.log v.asIdeal.absNorm : ℂ) * eulerRatio c w v *
      eulerRatio c w v ^ i) =
      fun m : ℕ => (Real.log v.asIdeal.absNorm : ℂ) * eulerRatio c w v ^ (m + 1) :=
    funext fun m => by ring
  rw [hfun, ← div_eq_mul_inv] at hg
  exact hg

/-- **The Euler logarithm differentiates to minus the prime-power series.** -/
theorem deriv_eulerLog (hc : ∀ v, ‖c v‖ ≤ 1) {w : ℂ} (hw : 1 < w.re) :
    deriv (eulerLog c) w = -primePowerSeries c w :=
  (hasSum_deriv_eulerLog hc hw).unique (hasSum_primePowerSeries hc hw).neg

/-- **The logarithmic derivative of an Euler product is the prime-power series.** If `L = exp ∘ S`
on `Re w > 1`, then `−L'(w)/L(w) = Σ_{v,m} log N(v) (c_v N(v)^{−w})^{m+1}` there. -/
theorem neg_deriv_div_eq_primePowerSeries (hc : ∀ v, ‖c v‖ ≤ 1) {L : ℂ → ℂ}
    (hL : ∀ z : ℂ, 1 < z.re → L z = Complex.exp (eulerLog c z)) {w : ℂ} (hw : 1 < w.re) :
    -deriv L w / L w = primePowerSeries c w := by
  have hev : L =ᶠ[𝓝 w] fun z => Complex.exp (eulerLog c z) := by
    filter_upwards [(isOpen_re_gt 1).mem_nhds hw] with z hz
    exact hL z hz
  have hd : HasDerivAt (fun z => Complex.exp (eulerLog c z))
      (Complex.exp (eulerLog c w) * deriv (eulerLog c) w) w :=
    (differentiableAt_eulerLog hc hw).hasDerivAt.cexp
  rw [hev.deriv_eq, hd.deriv, hL w hw, deriv_eulerLog hc hw]
  field_simp [Complex.exp_ne_zero]

end GaloisForLFunctions.TensorPowerProgramme
