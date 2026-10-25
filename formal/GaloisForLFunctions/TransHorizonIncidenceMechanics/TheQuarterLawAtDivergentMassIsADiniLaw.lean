import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheDiniThresholdOfTheLogLogAmplitudeIsOne
import GaloisForLFunctions.RHTower.ZetaGateProductAFEMainTermInputs

/-!
# The quarter law at divergent mass is a Dini law

At height zero the boundary amplitude is `1/2`: the constant pattern `f(p) = a` has a paid
half-damped receiver iff `a < 1/2` (the quarter law). Lower the amplitude by a completely monotone
defect, `f(p) = (1 − c g(p))/2` with `g(p) = Σ_k w_k p^{-s_k}` (`halfDefectPattern`). The Euler
product gives `log|F(v)| = ½(log|ζ(v)| − c Σ_k w_k log|ζ(v + s_k)|) + O(1)`
(`abs_log_norm_halfDefectSeries_sub_le`), which is the Dini box at the height `t₀ = 0`
(`exists_diniBox_halfDefectPattern`). Since `ζ(1/2) < 0`:

* `f(d) d^{-1/2}` is paid iff `∫_0^1 e^{−cΛ(ρ)} dρ/ρ < ∞` (`receiverBounded_halfDefectWeight_iff`);
* the harmonic defect is paid iff `c > 1` (`receiverBounded_halfHarmonicDefect_iff`), and so is
  the log-log amplitude `(1 − c/ℓ(p))/2`, `ℓ = max(1, log log)`
  (`receiverBounded_halfLogLogPattern_iff`);
* the mass `Σ_p |f(p) − 1/2|/p` is infinite for every `c > 0` (`not_summable_halfHarmonicMass`).

The oscillating boundary `cos(t₀ log p)`, `t₀ ≠ 0`, and the constant boundary `1/2` at `t₀ = 0`
share one Dini threshold: in both the amplitude reaching the boundary is `1/2` per height.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

variable {w s : ℕ → ℝ}

/-! ### The half-amplitude defect pattern -/

/-- The half-amplitude defect pattern at height zero: `f(p) = (1 − c g(p))/2`. -/
def halfDefectPattern (c : ℝ) (w s : ℕ → ℝ) : ℕ →*₀ ℝ :=
  primeValueHom fun p => (1 - c * cmDefect w s p) / 2

theorem halfDefectPattern_prime (c : ℝ) {p : ℕ} (hp : p.Prime) :
    halfDefectPattern c w s p = (1 - c * cmDefect w s p) / 2 :=
  primeValueHom_prime _ hp

theorem abs_halfDefectPattern_le (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) (n : ℕ) : |halfDefectPattern c w s n| ≤ 1 :=
  abs_patternHom_le_one _ (fun p hp => by
    rw [halfDefectPattern_prime c hp, abs_div, abs_two]
    have := abs_one_sub_mul_cmDefect_le hd hc hcW (show (1 : ℝ) ≤ p by
      exact_mod_cast hp.one_lt.le)
    linarith) n

/-- **The Euler comparison at height zero.** On `Re v > 1`,
`|log|F(v)| − ½ D_{c,0}(v)| ≤ (2 + cW) S`. -/
theorem abs_log_norm_halfDefectSeries_sub_le (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) {v : ℂ} (hv : 1 < v.re) :
    |Real.log ‖∑' n : ℕ, (halfDefectPattern c w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-v)‖ -
      defectLogModel c 0 w s v / 2| ≤ (2 + c * ∑' k, w k) * primeSquareMass := by
  have hF := abs_log_norm_tsum_sub_re_le (cweightedPatternHom (halfDefectPattern c w s) v) hv
    fun n => by
      simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_natCast]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_halfDefectPattern_le hd hc hcW n)
  have hFn : ∑' n, cweightedPatternHom (halfDefectPattern c w s) v n =
      ∑' n : ℕ, (halfDefectPattern c w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-v) := tsum_congr fun n => rfl
  have hP : ∑' p : Nat.Primes, cweightedPatternHom (halfDefectPattern c w s) v p =
      (∑' p : Nat.Primes, cweightedPatternHom (defectPattern c 0 w s) v p) / 2 := by
    rw [← tsum_div_const]
    refine tsum_congr fun p => ?_
    simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      halfDefectPattern_prime c p.2, defectPattern_prime c 0 p.2, zero_mul, Real.cos_zero,
      mul_one]
    push_cast; ring
  rw [hFn, hP, Complex.div_ofNat_re, ← primeSquareMass] at hF
  have hR := abs_re_primeSum_defectPattern_sub_le hd hc 0 hv
  have hS : 0 ≤ primeSquareMass := tsum_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hW : 0 ≤ c * ∑' k, w k := mul_nonneg hc (tsum_nonneg hd.nonneg)
  have hWS := mul_nonneg hW hS
  rw [abs_le] at hF hR ⊢
  constructor <;> nlinarith [hF.1, hF.2, hR.1, hR.2]

/-- **The Dini box at height zero.** -/
theorem exists_diniBox_halfDefectPattern (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) : ∃ B : ℝ, DiniBox (halfDefectPattern c w s) c 0 w s B := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_log_norm_zeta_add_log_le 11
  set W := ∑' k, w k
  have hW : 0 ≤ W := tsum_nonneg hd.nonneg
  refine ⟨(L + Real.log 2) / 2 + c / 4 * (W * (2 * (L + Real.log 2))) +
    (2 + c * W) * primeSquareMass, fun v hv hv2 hv0 hvT => ?_⟩
  have hE := abs_log_norm_halfDefectSeries_sub_le hd hc hcW hv
  simp only [sub_zero, zero_add] at hvT ⊢
  set u := v.re - 1
  set ρ := u + |v.im|
  have hu : 0 < u := by simp only [u]; linarith
  have hρ : 0 < ρ := by simp only [ρ]; positivity
  have hvH : |v.im| ≤ 11 := by rw [abs_of_nonneg hv0]; exact hvT
  have hZ : |Real.log ‖riemannZeta v‖ - Real.log ρ⁻¹| ≤ L + Real.log 2 := by
    have hn := norm_bounds_abs_add_abs (v - 1)
    have hre : (v - 1).re = u := by simp [u]
    have him : (v - 1).im = v.im := by simp
    rw [hre, him, abs_of_pos hu] at hn
    exact abs_log_norm_zeta_sub_log_inv_le hL hv (by linarith) hvH hn.1 hn.2
  have hZk : ∀ k, |Real.log ‖riemannZeta (v + s k)‖ - Real.log (s k + ρ)⁻¹| ≤ L + Real.log 2 :=
    fun k => by
      have hk := hd.pos k
      have hk2 := hd.le_half k
      have hre : (v + s k - 1).re = u + s k := by simp [u]; ring
      have him : (v + s k - 1).im = v.im := by simp
      have hn := norm_bounds_abs_add_abs (v + s k - 1)
      rw [hre, him, abs_of_pos (by linarith)] at hn
      refine abs_log_norm_zeta_sub_log_inv_le hL (by simp; linarith) (by simp; linarith)
        (by simpa using hvH) ?_ ?_
      · simp only [ρ]; linarith [hn.1]
      · simp only [ρ]; linarith [hn.2]
  -- the model at height zero
  have hmodel : defectLogModel c 0 w s v / 2 = Real.log ‖riemannZeta v‖ / 2 -
      c / 4 * ∑' k, w k * (Real.log ‖riemannZeta (v + s k)‖ +
        Real.log ‖riemannZeta (v + s k)‖) := by
    simp only [defectLogModel, Complex.ofReal_zero, zero_mul, sub_zero, add_zero]
    ring
  have hsum := abs_tsum_mul_sub_tsum_mul_le hd
    (a := fun k => Real.log ‖riemannZeta (v + s k)‖ + Real.log ‖riemannZeta (v + s k)‖)
    (b := fun k => 2 * Real.log (s k + ρ)⁻¹)
    (B := 2 * (|Real.log ρ| + |Real.log (1 + ρ)|))
    (fun k => by rw [abs_mul, abs_two]; linarith [abs_log_inv_shift_le hd hρ k])
    (C := 2 * (L + Real.log 2)) fun k => by
      have h1 := hZk k
      rw [abs_le] at h1 ⊢; constructor <;> linarith [h1.1, h1.2]
  have h2Λ : ∑' k, w k * (2 * Real.log (s k + ρ)⁻¹) = 2 * defectProfile w s ρ := by
    rw [defectProfile, ← tsum_mul_left]; exact tsum_congr fun k => by ring
  rw [h2Λ] at hsum
  have hcs := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ c / 4)
  rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ c / 4), ← abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ c / 4)] at hcs
  rw [hmodel] at hE
  set Lf := Real.log ‖∑' n : ℕ, (halfDefectPattern c w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-v)‖
  rw [abs_le] at hE hcs hZ ⊢
  constructor <;> nlinarith [hE.1, hE.2, hcs.1, hcs.2, hZ.1, hZ.2]

/-- **The large-height bound at height zero.** -/
theorem exists_diniLarge_halfDefectPattern (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) : ∃ Cl : ℝ, 0 ≤ Cl ∧ DiniLarge (halfDefectPattern c w s) 0 Cl := by
  obtain ⟨C₁, hC₁, hD⟩ := exists_abs_defectLogModel_le_large hd hc hcW le_rfl
  have hS : 0 ≤ primeSquareMass := tsum_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set E : ℝ := C₁ + 4 * primeSquareMass
  refine ⟨Real.exp E * (2 * 108 ^ 27), by positivity, fun v hv hv2 hvy => ?_⟩
  have hE := abs_log_norm_halfDefectSeries_sub_le hd hc hcW hv
  have hcS : c * (∑' k, w k) * primeSquareMass ≤ 2 * primeSquareMass :=
    mul_le_mul_of_nonneg_right hcW hS
  have hDv := hD v hv hv2 hvy
  have hy : 9 ≤ v.im := by linarith
  have hll : 0 ≤ Real.log (Real.log (2 * v.im)) := by
    refine Real.log_nonneg ?_
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  refine le_mul_rpow_quarter_of_log_le (norm_pos_iff.mpr (patternSeries_ne_zero
    (fun p _ => abs_halfDefectPattern_le hd hc hcW p) hv)) hy ?_
  rw [abs_le] at hE hDv
  simp only [E]
  nlinarith [hE.2, hDv.2, hDv.1]

/-! ### The quarter law at divergent mass -/

theorem riemannZeta_half_ne_zero' : riemannZeta (1 / 2 + ((0 : ℝ) : ℂ) * I) ≠ 0 := by
  rw [Complex.ofReal_zero, zero_mul, add_zero]
  intro h
  have := RHTower.re_riemannZeta_ofReal_neg (σ := 1 / 2) (by norm_num) (by norm_num)
  rw [show (((1 / 2 : ℝ)) : ℂ) = 1 / 2 by norm_num, h, Complex.zero_re] at this
  exact lt_irrefl _ this

/-- **The quarter law at divergent mass is a Dini law.** For admissible defect data and `c ≥ 0`
with `cW ≤ 2`, the half-damped weight of `f(p) = (1 − c Σ_k w_k p^{-s_k})/2` has bounded receiver iff
the Dini density `e^{−cΛ(ρ)}/ρ` is integrable on `(0, 1]`. -/
theorem receiverBounded_halfDefectWeight_iff (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) :
    ReceiverBounded (dampedSignWeight ⇑(halfDefectPattern c w s) (1 / 2)) ↔
      IntegrableOn (diniDensity c w s) (Ioc 0 1) := by
  obtain ⟨B, hB⟩ := exists_diniBox_halfDefectPattern hd hc hcW
  obtain ⟨Cl, -, hCl⟩ := exists_diniLarge_halfDefectPattern hd hc hcW
  rw [receiverBounded_half_iff_of_diniBox hd hc hcW le_rfl
    (fun p _ => abs_halfDefectPattern_le hd hc hcW p) hB hCl]
  exact or_iff_left riemannZeta_half_ne_zero'

/-- **The harmonic defect at height zero**: `(1 − c g(p))/2` is paid iff `c > 1`. -/
theorem receiverBounded_halfHarmonicDefect_iff {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 2) :
    ReceiverBounded (dampedSignWeight ⇑(halfDefectPattern c harmonicWeight harmonicShift) (1 / 2)) ↔
      1 < c := by
  have hcW : c * ∑' k, harmonicWeight k ≤ 2 := by
    have := mul_le_mul_of_nonneg_left tsum_harmonicWeight_le hc; linarith
  rw [receiverBounded_halfDefectWeight_iff admissibleDefect_harmonic hc hcW,
    integrableOn_diniDensity_harmonic_iff hc hc2]

/-- The log-log amplitude at height zero, `f(p) = (1 − c/ℓ(p))/2`. -/
def halfLogLogPattern (c : ℝ) : ℕ →*₀ ℝ :=
  primeValueHom fun p => (1 - c / logLogFloor p) / 2

/-- **The log-log amplitude at height zero** is paid iff `c > 1`. -/
theorem receiverBounded_halfLogLogPattern_iff {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 2) :
    ReceiverBounded (dampedSignWeight ⇑(halfLogLogPattern c) (1 / 2)) ↔ 1 < c := by
  have hd := admissibleDefect_harmonic
  have hcW : c * ∑' k, harmonicWeight k ≤ 2 := by
    have := mul_le_mul_of_nonneg_left tsum_harmonicWeight_le hc; linarith
  have hf : ∀ p : ℕ, p.Prime → |halfDefectPattern c harmonicWeight harmonicShift p| ≤ 1 :=
    fun p _ => abs_halfDefectPattern_le hd hc hcW p
  have hf' : ∀ p : ℕ, p.Prime → |halfLogLogPattern c p| ≤ 1 := fun p hp => by
    rw [halfLogLogPattern, primeValueHom_prime _ hp, abs_div, abs_two]
    have hl := one_le_logLogFloor p
    have h0 : 0 ≤ c / logLogFloor p := div_nonneg hc (by linarith)
    have h1 : c / logLogFloor p ≤ c := div_le_self hc hl
    rw [div_le_one (by norm_num), abs_le]; constructor <;> linarith
  have hdiff : Summable (fun p : ℕ => if p.Prime then
      |halfLogLogPattern c p - halfDefectPattern c harmonicWeight harmonicShift p| *
        (p : ℝ) ^ (-(1 / 2 + 1 / 2 : ℝ)) else 0) := by
    refine (summable_inv_mul_logLogFloor_sq.mul_left (3600 * c)).of_nonneg_of_le
      (fun p => by split_ifs <;> positivity) fun p => ?_
    split_ifs with hp
    · have hp1 : 1 ≤ p := hp.one_lt.le
      rw [halfLogLogPattern, primeValueHom_prime _ hp, halfDefectPattern_prime c hp,
        show (1 - c / logLogFloor p) / 2 - (1 - c * cmDefect harmonicWeight harmonicShift p) / 2 =
          c * (cmDefect harmonicWeight harmonicShift p - 1 / logLogFloor p) / 2 by ring,
        abs_div, abs_two, abs_mul, abs_of_nonneg hc,
        show (-(1 / 2 + 1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
      have hA := abs_cmDefect_harmonic_sub_inv_logLogFloor_le hp1
      simp only [primeRecipTerm, if_pos hp]
      calc c * |cmDefect harmonicWeight harmonicShift p - 1 / logLogFloor p| / 2 * (p : ℝ)⁻¹
          ≤ c * (3600 / logLogFloor p ^ 2) / 2 * (p : ℝ)⁻¹ := by gcongr
        _ ≤ 3600 * c * (1 / (p : ℝ) / logLogFloor p ^ 2) := by
            have : 0 ≤ c * (3600 / logLogFloor p ^ 2) * (p : ℝ)⁻¹ := by
              have := one_le_logLogFloor p; positivity
            rw [show 3600 * c * (1 / (p : ℝ) / logLogFloor p ^ 2) =
              c * (3600 / logLogFloor p ^ 2) * (p : ℝ)⁻¹ by ring]
            linarith
    · simp only [primeRecipTerm, if_neg hp, zero_div, mul_zero, le_refl]
  rw [receiverBounded_iff_of_summable_prime_diff hf hf' (by norm_num) hdiff]
  exact receiverBounded_halfHarmonicDefect_iff hc hc2

/-- **The mass at height zero diverges**: `Σ_p |f(p) − 1/2|/p = ∞` for the harmonic defect at every
`c > 0` (it dominates half the oscillating mass at the height `1`). -/
theorem not_summable_halfHarmonicMass {c : ℝ} (hc : 0 < c) :
    ¬ Summable fun p : Nat.Primes =>
      |halfDefectPattern c harmonicWeight harmonicShift p - 1 / 2| / ((p : ℕ) : ℝ) := by
  intro hsum
  refine not_summable_criticalLineMass_harmonic hc one_pos ((hsum.mul_left 2).of_nonneg_of_le
    (fun p => by positivity) fun p => ?_)
  have hp := p.2
  rw [defectPattern_prime c 1 hp, oscPattern_prime 1 1 hp, halfDefectPattern_prime c hp,
    show (1 - c * cmDefect harmonicWeight harmonicShift p) * Real.cos (1 * Real.log p) -
        1 * Real.cos (1 * Real.log p) =
      -(c * cmDefect harmonicWeight harmonicShift p * Real.cos (1 * Real.log p)) by ring,
    show (1 - c * cmDefect harmonicWeight harmonicShift p) / 2 - 1 / 2 =
      -(c * cmDefect harmonicWeight harmonicShift p / 2) by ring,
    abs_neg, abs_neg, abs_mul]
  have hg := cmDefect_nonneg admissibleDefect_harmonic (show (1 : ℝ) ≤ (p : ℕ) by
    exact_mod_cast hp.one_lt.le)
  rw [abs_of_nonneg (mul_nonneg hc.le hg), abs_of_nonneg (div_nonneg (mul_nonneg hc.le hg) zero_le_two)]
  have hcos := Real.abs_cos_le_one (1 * Real.log p)
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast hp.pos
  rw [div_le_iff₀ hp0, mul_div_assoc', div_mul_cancel₀ _ hp0.ne']
  nlinarith [mul_nonneg hc.le hg]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
