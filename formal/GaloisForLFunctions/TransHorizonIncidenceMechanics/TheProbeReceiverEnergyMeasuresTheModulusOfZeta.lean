import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheLogTwistedOscillatingSmoothPowerIsPaidExactlyAtTheDoubleZerosOfZeta

/-!
# The probe receiver energy measures the modulus of ζ

For `0 < ε ≤ 1/2`, `t ∈ ℝ` and `ρ = 1 − ε + it`, the receiver energy `E_T` of the probe
`d^{-ε} cos(t log d)` is computed to leading order by `ζ(ρ)`:

* below half damping (`0 < ε < 1/2`), `E_T/T^{1−2ε} − Φ(T) → 0` with
  `Φ(T) = |a|²/(2(1−2ε)) + ½ Re(a² T^{2it}/(1 − 2ε + 2it))`, `a = ζ(ρ)/ρ`
  (`tendsto_probeEnergy_div_sub_profile`);
* at half damping (`ε = 1/2`, `t ≠ 0`), `E_T/log T → |ζ(½ + it)|²/(2|½ + it|²)`
  (`tendsto_probeEnergy_half_div_log`).

The receiver is therefore a calibrated instrument: its growth constant is `|ζ|²` on every vertical
line of `1/2 ≤ Re s < 1`, it vanishes exactly at the zeros, and on the critical line
`|ζ(½ + it)|² = 2|½ + it|² lim E_T/log T` evaluates `ζ` from finite divisor-sum energies
(`norm_sq_riemannZeta_half_eq_limit`). Below half damping `Φ` stays between
`|a|²/2 (1/(1−2ε) ∓ 1/|1−2ε+2it|)`, so `E_T ≍ |ζ(ρ)|² T^{1−2ε}` for `t ≠ 0`
(`probeEnergy_le_and_ge`).

* **Main term.** `|A(n) − Re(a n^ρ)| ≤ K (√n)^{1−ε}` gives `|√E_T − ‖M‖_T| ≤ K√(1 + 1/ε)` for
  `M(n) = Re(a n^ρ)` (`abs_sqrt_probeEnergy_sub_le`).
* **Energy of the main term.** `M(n)²/(n(n+1)) = |a|²/2 · n^{1−2ε}/(n+1) + ½ Re(a² n^{1−2ε+2it}/(n+1))`
  (`probeMain_sq_div`), and `Σ_{n≤T} n^β/(n+1) = T^β/β + O(1)` for `0 < Re β < 1`
  (`norm_sum_cpow_div_succ_sub_le`); at `β = 0` the sum is `log T + O(1)` and at `β = 2it ≠ 0` it is
  bounded.
-/

open Finset Filter Topology Complex
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Comparison with the main term -/

/-- The reverse triangle inequality for the pronic norm. -/
theorem abs_pronicNorm_sub_le (f g : ℕ → ℝ) (T : ℕ) :
    |pronicNorm f T - pronicNorm g T| ≤ pronicNorm (fun n => f n - g n) T := by
  have h1 := pronicNorm_add_le g (fun n => f n - g n) T
  have h2 := pronicNorm_add_le f (fun n => (-1) * (f n - g n)) T
  rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at h2
  have e1 : pronicNorm (fun n => g n + (f n - g n)) T = pronicNorm f T :=
    pronicNorm_congr fun n _ => by ring
  have e2 : pronicNorm (fun n => f n + (-1) * (f n - g n)) T = pronicNorm g T :=
    pronicNorm_congr fun n _ => by ring
  rw [e1] at h1
  rw [e2] at h2
  rw [abs_le]
  constructor <;> linarith

/-- The probe amplitude `a = ζ(ρ)/ρ`. -/
def probeAmp (ε t : ℝ) : ℂ := riemannZeta (oscillationExponent ε t) / oscillationExponent ε t

/-- The main term `M(n) = Re(a n^ρ)` of the probe prefix. -/
def probeMain (ε t : ℝ) (n : ℕ) : ℝ :=
  (probeAmp ε t * ((n : ℝ) : ℂ) ^ oscillationExponent ε t).re

/-- **The probe receiver is its main term up to a bounded norm.** -/
theorem abs_sqrt_probeEnergy_sub_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (t : ℝ) (T : ℕ) :
    |Real.sqrt (weightPronicEnergy (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T) - pronicNorm (probeMain ε t) T| ≤
      |floorSumRate (oscillationExponent ε t)| * Real.sqrt (1 + 1 / ε) := by
  rw [weightPronicEnergy_eq_sq_pronicNorm, Real.sqrt_sq (pronicNorm_nonneg _ _)]
  refine (abs_pronicNorm_sub_le _ _ T).trans ?_
  have hrem : ∀ n, 1 ≤ n → |weightCenteredPrefix (oscillatingSmoothPower ε t)
      (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n - probeMain ε t n| ≤
        floorSumRate (oscillationExponent ε t) * Real.sqrt n ^ (1 - ε) := by
    intro n hn
    have h := abs_weightCenteredPrefix_oscillatingSmoothPower_sub_le hε hε1 t hn
    have e : probeMain ε t n = (riemannZeta (oscillationExponent ε t) *
        ((n : ℝ) : ℂ) ^ oscillationExponent ε t / oscillationExponent ε t).re := by
      unfold probeMain probeAmp; congr 1; ring
    rw [e]
    exact h
  have h := sum_sq_le_of_abs_le_sqrt_rpow hε (f := fun n => weightCenteredPrefix
    (oscillatingSmoothPower ε t) (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n -
      probeMain ε t n) hrem T
  rw [pronicNorm]
  calc Real.sqrt _ ≤ Real.sqrt (floorSumRate (oscillationExponent ε t) ^ 2 * (1 + 1 / ε)) :=
        Real.sqrt_le_sqrt h
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-! ### The energy of the main term -/

/-- The exponent `β = 1 − 2ε + 2it` of the cross term. -/
def probeCrossExponent (ε t : ℝ) : ℂ := ((1 - 2 * ε : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I

theorem probeCrossExponent_re (ε t : ℝ) : (probeCrossExponent ε t).re = 1 - 2 * ε := by
  simp [probeCrossExponent]

/-- `M(n)²/(n(n+1)) = |a|²/2 · n^{1−2ε}/(n+1) + ½ Re(a² n^β/(n+1))`. -/
theorem probeMain_sq_div (ε t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    probeMain ε t n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
      ‖probeAmp ε t‖ ^ 2 / 2 * ((n : ℝ) ^ (1 - 2 * ε) / ((n : ℝ) + 1)) +
        (probeAmp ε t ^ 2 * (((n : ℝ) : ℂ) ^ probeCrossExponent ε t /
          (((n : ℝ) + 1 : ℝ) : ℂ))).re / 2 := by
  set a := probeAmp ε t with ha
  set x : ℝ := (n : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; exact_mod_cast hn
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hsplit : (x : ℂ) ^ oscillationExponent ε t =
      ((x ^ (1 - ε) : ℝ) : ℂ) * (x : ℂ) ^ ((t : ℂ) * I) := by
    rw [oscillationExponent, Complex.cpow_add _ _ hxC, Complex.ofReal_cpow hx0.le]
  have hM : probeMain ε t n = x ^ (1 - ε) * (a * (x : ℂ) ^ ((t : ℂ) * I)).re := by
    simp only [probeMain, ← ha, ← hx]
    rw [hsplit, mul_left_comm, Complex.re_ofReal_mul]
  have hw : ‖(x : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp
  have hz2 : (a * (x : ℂ) ^ ((t : ℂ) * I)) ^ 2 = a ^ 2 * (x : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) := by
    rw [mul_pow, sq ((x : ℂ) ^ ((t : ℂ) * I)), ← Complex.cpow_add _ _ hxC]
    push_cast; ring_nf
  have hu2 : (a * (x : ℂ) ^ ((t : ℂ) * I)).re ^ 2 =
      (‖a‖ ^ 2 + (a ^ 2 * (x : ℂ) ^ (((2 * t : ℝ) : ℂ) * I)).re) / 2 := by
    rw [re_sq_eq_half, norm_mul, hw, mul_one, hz2]
  have hpow : (x ^ (1 - ε)) ^ 2 = x * x ^ (1 - 2 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
      show (1 - ε) * ((2 : ℕ) : ℝ) = 1 + (1 - 2 * ε) by push_cast; ring, Real.rpow_add hx0,
      Real.rpow_one]
  have hcross : (x : ℂ) ^ probeCrossExponent ε t =
      ((x ^ (1 - 2 * ε) : ℝ) : ℂ) * (x : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) := by
    rw [probeCrossExponent, Complex.cpow_add _ _ hxC, Complex.ofReal_cpow hx0.le]
  have hre : (a ^ 2 * ((x : ℂ) ^ probeCrossExponent ε t / ((x + 1 : ℝ) : ℂ))).re =
      x ^ (1 - 2 * ε) / (x + 1) * (a ^ 2 * (x : ℂ) ^ (((2 * t : ℝ) : ℂ) * I)).re := by
    rw [hcross, ← Complex.re_ofReal_mul]
    congr 1
    push_cast
    ring
  rw [hM, mul_pow, hu2, hpow, hre]
  field_simp
  ring

/-- The energy of the main term. -/
theorem sq_pronicNorm_probeMain (ε t : ℝ) (T : ℕ) :
    pronicNorm (probeMain ε t) T ^ 2 =
      ‖probeAmp ε t‖ ^ 2 / 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (1 - 2 * ε) / ((n : ℝ) + 1) +
        (probeAmp ε t ^ 2 * ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ probeCrossExponent ε t /
          (((n : ℝ) + 1 : ℝ) : ℂ)).re / 2 := by
  rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity), mul_sum, mul_sum,
    Complex.re_sum, sum_div, ← sum_add_distrib]
  exact sum_congr rfl fun n hn => probeMain_sq_div ε t (mem_Icc.mp hn).1

/-! ### Shifted harmonic sums -/

/-- **`Σ_{n ≤ T} n^β/(n+1) = T^β/β + O(1)`** for `0 < Re β < 1`. -/
theorem norm_sum_cpow_div_succ_sub_le {β : ℂ} (hβ0 : 0 < β.re) (hβ1 : β.re < 1) {T : ℕ}
    (hT : 1 ≤ T) :
    ‖∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ β / (((n : ℝ) + 1 : ℝ) : ℂ) - ((T : ℝ) : ℂ) ^ β / β‖ ≤
      ‖riemannZeta (1 - β)‖ + partialSumRate (1 - β) + (1 + 1 / (1 - β.re)) := by
  set w : ℂ := 1 - β with hw
  have hwre : w.re = 1 - β.re := by rw [hw, sub_re, one_re]
  have hw0 : 0 < w.re := by rw [hwre]; linarith
  have hw1 : w ≠ 1 := fun h => by
    have := congrArg Complex.re h
    rw [hwre, one_re] at this
    linarith
  have hβ : β = 1 - w := by rw [hw]; ring
  -- `n^β/(n+1) = n^{-w} − n^{-w}/(n+1)`
  have hterm : ∀ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ β / (((n : ℝ) + 1 : ℝ) : ℂ) =
      ((n : ℝ) : ℂ) ^ (-w) - ((n : ℝ) : ℂ) ^ (-w) / (((n : ℝ) + 1 : ℝ) : ℂ) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnC : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    have hn1C : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (n : ℝ) + 1 ≠ 0)
    rw [hβ, sub_eq_add_neg (1 : ℂ) w, Complex.cpow_add _ _ hnC, Complex.cpow_one]
    field_simp
    push_cast
    ring
  have htail : ‖∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ (-w) / (((n : ℝ) + 1 : ℝ) : ℂ)‖ ≤
      1 + 1 / w.re := by
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ n ∈ Icc 1 T, ‖((n : ℝ) : ℂ) ^ (-w) / (((n : ℝ) + 1 : ℝ) : ℂ)‖ ≤
        (n : ℝ) ^ (-(1 + w.re)) := by
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by linarith
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith), neg_re, div_le_iff₀ (by linarith),
        show -(1 + w.re) = -w.re + (-1 : ℝ) by ring, Real.rpow_add hn0, Real.rpow_neg_one]
      have h1 : 0 ≤ (n : ℝ) ^ (-w.re) := Real.rpow_nonneg hn0.le _
      have h2 : (n : ℝ) ^ (-w.re) * (n : ℝ)⁻¹ * ((n : ℝ) + 1) =
          (n : ℝ) ^ (-w.re) * (1 + (n : ℝ)⁻¹) := by field_simp
      rw [h2]
      have h3 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn0.le
      nlinarith
    calc _ ≤ ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(1 + w.re)) := sum_le_sum hle
      _ ≤ (1 + 1 / w.re) * ((1 : ℕ) : ℝ) ^ (-w.re) := sum_Icc_rpow_neg_one_sub_le hw0 le_rfl T
      _ = 1 + 1 / w.re := by rw [Nat.cast_one, Real.one_rpow, mul_one]
  have hP := norm_cpowPartialSum_sub_le hw0 hw1 hT (x := T) le_rfl (by linarith)
  have hTpow : (T : ℝ) ^ (-w.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT) (by linarith)
  have hrate0 := partialSumRate_nonneg hw0
  have hsum : ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ (-w) = cpowPartialSum w T := rfl
  rw [sum_congr rfl hterm, sum_sub_distrib, hsum, ← hwre, hβ]
  calc ‖cpowPartialSum w T - ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ (-w) / (((n : ℝ) + 1 : ℝ) : ℂ) -
        ((T : ℝ) : ℂ) ^ (1 - w) / (1 - w)‖
      = ‖(cpowPartialSum w T - ((T : ℝ) : ℂ) ^ (1 - w) / (1 - w) - riemannZeta w) +
          riemannZeta w - ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ (-w) / (((n : ℝ) + 1 : ℝ) : ℂ)‖ := by
        congr 1; ring
    _ ≤ ‖cpowPartialSum w T - ((T : ℝ) : ℂ) ^ (1 - w) / (1 - w) - riemannZeta w‖ +
          ‖riemannZeta w‖ + ‖∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ (-w) / (((n : ℝ) + 1 : ℝ) : ℂ)‖ :=
        (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ partialSumRate w * 1 + ‖riemannZeta w‖ + (1 + 1 / w.re) := by
        gcongr
        exact hP.trans (mul_le_mul_of_nonneg_left hTpow hrate0)
    _ = ‖riemannZeta w‖ + partialSumRate w + (1 + 1 / w.re) := by ring

/-- `Σ_{n ≤ T} 1/(n(n+1)) ≤ 2`. -/
theorem sum_Icc_one_div_mul_succ_le_two (T : ℕ) :
    ∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ 2 := by
  have hle : ∀ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ (n : ℝ) ^ (-(1 + 1 : ℝ)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [show -(1 + 1 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg, zpow_two,
      one_div]
    exact inv_anti₀ (by positivity) (by nlinarith)
  calc _ ≤ ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(1 + 1 : ℝ)) := sum_le_sum hle
    _ ≤ (1 + 1 / 1) * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ)) := sum_Icc_rpow_neg_one_sub_le one_pos le_rfl T
    _ = 2 := by norm_num

/-- `|Σ_{n ≤ T} 1/(n+1) − log T| ≤ 2` for `T ≥ 1`. -/
theorem abs_sum_one_div_succ_sub_log_le {T : ℕ} (hT : 1 ≤ T) :
    |∑ n ∈ Icc 1 T, 1 / ((n : ℝ) + 1) - Real.log T| ≤ 2 := by
  have hsplit : ∑ n ∈ Icc 1 T, 1 / ((n : ℝ) + 1) =
      ∑ n ∈ Icc 1 T, 1 / (n : ℝ) - ∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    field_simp
    ring
  have h1 := log_succ_le_sum_Icc_one_div T
  have h2 := RHTower.Sieve.sum_Icc_one_div_le_one_add_log T
  have h3 := sum_Icc_one_div_mul_succ_le_two T
  have h4 : 0 ≤ ∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) := sum_nonneg fun n _ => by positivity
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have h5 : Real.log T ≤ Real.log ((T : ℝ) + 1) := Real.log_le_log hT0 (by linarith)
  rw [hsplit, abs_le]
  constructor <;> linarith

/-- `‖Σ_{n ≤ T} n^{iτ}/(n+1)‖ ≤ B_τ + 2` for `τ ≠ 0`. -/
theorem norm_sum_cpow_I_div_succ_le {τ : ℝ} (hτ : τ ≠ 0) (T : ℕ) :
    ‖∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((τ : ℂ) * I) / (((n : ℝ) + 1 : ℝ) : ℂ)‖ ≤
      oscHarmonicBound τ + 2 := by
  have hsplit : ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((τ : ℂ) * I) / (((n : ℝ) + 1 : ℝ) : ℂ) =
      ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((τ : ℂ) * I) / ((n : ℝ) : ℂ) -
        ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((τ : ℂ) * I) * ((1 / ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnC : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    have hn1C : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (n : ℝ) + 1 ≠ 0)
    have hnC' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    have hn1C' : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : (n : ℝ) + 1 ≠ 0)
    push_cast
    field_simp
    ring
  have h2 : ‖∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((τ : ℂ) * I) *
      ((1 / ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ)‖ ≤ 2 := by
    refine (norm_sum_le _ _).trans ((sum_le_sum fun n hn => ?_).trans
      (sum_Icc_one_div_mul_succ_le_two T))
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    simp
  rw [hsplit]
  exact (norm_sub_le _ _).trans (add_le_add (norm_sum_Icc_cpow_div_le hτ T) h2)

/-! ### The energy laws -/

/-- `|y² − X| ≤ C + B(2x + B)` from `|y − x| ≤ B` and `|x² − X| ≤ C`. -/
theorem abs_sq_sub_le_of_abs_sub_le {y x X B C : ℝ} (hx : 0 ≤ x) (h1 : |y - x| ≤ B)
    (h2 : |x ^ 2 - X| ≤ C) : |y ^ 2 - X| ≤ C + B * (2 * x + B) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans h1
  have h3 : |y + x| ≤ 2 * x + B := by
    have : |y + x| = |(y - x) + 2 * x| := by ring_nf
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * x)]
    linarith
  have h4 : |y ^ 2 - x ^ 2| ≤ B * (2 * x + B) := by
    rw [show y ^ 2 - x ^ 2 = (y - x) * (y + x) by ring, abs_mul]
    exact mul_le_mul h1 h3 (abs_nonneg _) hB
  calc |y ^ 2 - X| = |(y ^ 2 - x ^ 2) + (x ^ 2 - X)| := by ring_nf
    _ ≤ |y ^ 2 - x ^ 2| + |x ^ 2 - X| := abs_add_le _ _
    _ ≤ C + B * (2 * x + B) := by linarith

/-- The energy profile `Φ(T) = |a|²/(2(1−2ε)) + ½ Re(a² T^{2it}/β)`. -/
def probeEnergyProfile (ε t : ℝ) (T : ℕ) : ℝ :=
  ‖probeAmp ε t‖ ^ 2 / (2 * (1 - 2 * ε)) +
    (probeAmp ε t ^ 2 * ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) / probeCrossExponent ε t).re / 2

/-- The rate of the main-term energy law below half damping. -/
def probeProfileRate (ε t : ℝ) : ℝ :=
  ‖probeAmp ε t‖ ^ 2 / 2 *
    ((‖riemannZeta (1 - ((1 - 2 * ε : ℝ) : ℂ))‖ + partialSumRate (1 - ((1 - 2 * ε : ℝ) : ℂ)) +
        (1 + 1 / (1 - (1 - 2 * ε)))) +
      (‖riemannZeta (1 - probeCrossExponent ε t)‖ + partialSumRate (1 - probeCrossExponent ε t) +
        (1 + 1 / (1 - (1 - 2 * ε)))))

/-- **The main-term energy below half damping**: `|‖M‖_T² − T^{1−2ε} Φ(T)| ≤ C`. -/
theorem abs_sq_pronicNorm_probeMain_sub_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (t : ℝ)
    {T : ℕ} (hT : 1 ≤ T) :
    |pronicNorm (probeMain ε t) T ^ 2 - (T : ℝ) ^ (1 - 2 * ε) * probeEnergyProfile ε t T| ≤
      probeProfileRate ε t := by
  set a := probeAmp ε t with ha
  set β := probeCrossExponent ε t with hβ
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hβre : β.re = 1 - 2 * ε := probeCrossExponent_re ε t
  have hβ0 : β ≠ 0 := fun h => by rw [h, zero_re] at hβre; linarith
  -- the real sum as the real part of a complex one
  have hS0 : ∑ n ∈ Icc 1 T, (n : ℝ) ^ (1 - 2 * ε) / ((n : ℝ) + 1) =
      (∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ (((1 - 2 * ε : ℝ) : ℂ)) / (((n : ℝ) + 1 : ℝ) : ℂ)).re := by
    rw [Complex.re_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.div_ofReal_re, Complex.ofReal_re]
  have h0 := norm_sum_cpow_div_succ_sub_le (β := ((1 - 2 * ε : ℝ) : ℂ))
    (by simp; linarith) (by simp; linarith) hT
  have h1 := norm_sum_cpow_div_succ_sub_le (β := β) (by rw [hβre]; linarith)
    (by rw [hβre]; linarith) hT
  simp only [Complex.ofReal_re] at h0
  rw [hβre] at h1
  set E0 := ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ (((1 - 2 * ε : ℝ) : ℂ)) / (((n : ℝ) + 1 : ℝ) : ℂ) -
    ((T : ℝ) : ℂ) ^ (((1 - 2 * ε : ℝ) : ℂ)) / (((1 - 2 * ε : ℝ) : ℂ)) with hE0
  set E1 := ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ β / (((n : ℝ) + 1 : ℝ) : ℂ) -
    ((T : ℝ) : ℂ) ^ β / β with hE1
  -- the main growth
  have hmain0 : (((T : ℝ) : ℂ) ^ (((1 - 2 * ε : ℝ) : ℂ)) / (((1 - 2 * ε : ℝ) : ℂ))).re =
      (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) := by
    rw [← Complex.ofReal_cpow hT0.le, ← Complex.ofReal_div, Complex.ofReal_re]
  have hTβ : ((T : ℝ) : ℂ) ^ β = (((T : ℝ) ^ (1 - 2 * ε) : ℝ) : ℂ) *
      ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) := by
    rw [hβ, probeCrossExponent, Complex.cpow_add _ _ (by exact_mod_cast hT0.ne'),
      Complex.ofReal_cpow hT0.le]
  have hmain1 : (a ^ 2 * (((T : ℝ) : ℂ) ^ β / β)).re =
      (T : ℝ) ^ (1 - 2 * ε) * (a ^ 2 * ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) / β).re := by
    rw [hTβ, ← Complex.re_ofReal_mul]
    congr 1
    ring
  have hid : pronicNorm (probeMain ε t) T ^ 2 - (T : ℝ) ^ (1 - 2 * ε) * probeEnergyProfile ε t T =
      ‖a‖ ^ 2 / 2 * E0.re + (a ^ 2 * E1).re / 2 := by
    rw [sq_pronicNorm_probeMain, hS0, probeEnergyProfile, ← ha, ← hβ]
    have e0 : (∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ (((1 - 2 * ε : ℝ) : ℂ)) /
        (((n : ℝ) + 1 : ℝ) : ℂ)).re = E0.re + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) := by
      rw [hE0, sub_re, hmain0]; ring
    have e1 : (a ^ 2 * ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ β / (((n : ℝ) + 1 : ℝ) : ℂ)).re =
        (a ^ 2 * E1).re + (T : ℝ) ^ (1 - 2 * ε) *
          (a ^ 2 * ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) / β).re := by
      rw [← hmain1, ← add_re, hE1]
      congr 1
      ring
    rw [e0, e1]
    have h12 : (1 - 2 * ε) ≠ 0 := by linarith
    field_simp
    ring
  rw [hid]
  have hb0 : |E0.re| ≤ ‖riemannZeta (1 - ((1 - 2 * ε : ℝ) : ℂ))‖ +
      partialSumRate (1 - ((1 - 2 * ε : ℝ) : ℂ)) + (1 + 1 / (1 - (1 - 2 * ε))) :=
    (Complex.abs_re_le_norm _).trans h0
  have hb1 : |(a ^ 2 * E1).re| ≤ ‖a‖ ^ 2 * (‖riemannZeta (1 - β)‖ + partialSumRate (1 - β) +
      (1 + 1 / (1 - (1 - 2 * ε)))) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have ha2 : 0 ≤ ‖a‖ ^ 2 / 2 := by positivity
  calc |‖a‖ ^ 2 / 2 * E0.re + (a ^ 2 * E1).re / 2|
      ≤ ‖a‖ ^ 2 / 2 * |E0.re| + |(a ^ 2 * E1).re| / 2 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg ha2, abs_div, abs_two]
    _ ≤ probeProfileRate ε t := by
        rw [probeProfileRate, ← ha, ← hβ]
        linarith [mul_le_mul_of_nonneg_left hb0 ha2]

/-- **The probe energy law below half damping.** For `0 < ε < 1/2` and every `t ∈ ℝ`,
`E_T / T^{1−2ε} − Φ(T) → 0`, where `Φ(T) = |a|²/(2(1−2ε)) + ½ Re(a² T^{2it}/(1 − 2ε + 2it))` and
`a = ζ(1 − ε + it)/(1 − ε + it)`. -/
theorem tendsto_probeEnergy_div_sub_profile {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (t : ℝ) :
    Tendsto (fun T : ℕ => weightPronicEnergy (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T / (T : ℝ) ^ (1 - 2 * ε) -
          probeEnergyProfile ε t T) atTop (𝓝 0) := by
  set a := probeAmp ε t with ha
  set γ := 1 - 2 * ε with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  set B := |floorSumRate (oscillationExponent ε t)| * Real.sqrt (1 + 1 / ε) with hB
  set C := probeProfileRate ε t with hC
  set Φm := ‖a‖ ^ 2 / γ with hΦm
  have hB0 : 0 ≤ B := by positivity
  have hC0 : 0 ≤ C := by
    have h := abs_sq_pronicNorm_probeMain_sub_le hε hε2 t (T := 1) le_rfl
    exact (abs_nonneg _).trans h
  -- the profile is bounded by `|a|²/γ`
  have hΦ : ∀ T : ℕ, 1 ≤ T → |probeEnergyProfile ε t T| ≤ Φm := by
    intro T hT
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
    have hnβ : γ ≤ ‖probeCrossExponent ε t‖ := by
      have := Complex.re_le_norm (probeCrossExponent ε t)
      rwa [probeCrossExponent_re] at this
    have hnT : ‖((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hT0]; simp
    have h2 : |(a ^ 2 * ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
        probeCrossExponent ε t).re| ≤ ‖a‖ ^ 2 / γ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_div, norm_mul, norm_pow, hnT, mul_one]
      exact div_le_div_of_nonneg_left (by positivity) hγ0 hnβ
    unfold probeEnergyProfile
    rw [← ha, ← hγ]
    have h1 : 0 ≤ ‖a‖ ^ 2 / (2 * γ) := by positivity
    calc |‖a‖ ^ 2 / (2 * γ) + (a ^ 2 * ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
          probeCrossExponent ε t).re / 2|
        ≤ ‖a‖ ^ 2 / (2 * γ) + ‖a‖ ^ 2 / γ / 2 := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_of_nonneg h1, abs_div, abs_two]
          linarith
      _ = Φm := by rw [hΦm]; field_simp; ring
  -- the bound on the deviation
  have hbound : ∀ T : ℕ, 1 ≤ T →
      |weightPronicEnergy (oscillatingSmoothPower ε t)
          (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T / (T : ℝ) ^ γ -
        probeEnergyProfile ε t T| ≤
        (C + B * (2 * Real.sqrt C + B)) * (T : ℝ) ^ (-γ) +
          2 * B * Real.sqrt Φm * (T : ℝ) ^ (-(γ / 2)) := by
    intro T hT
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
    have hTγ : 0 < (T : ℝ) ^ γ := Real.rpow_pos_of_pos hT0 _
    have h1 := abs_sqrt_probeEnergy_sub_le hε (by linarith) t T
    have h2 := abs_sq_pronicNorm_probeMain_sub_le hε hε2 t hT
    rw [← hγ, ← hC] at h2
    rw [← hB] at h1
    set x := pronicNorm (probeMain ε t) T with hx
    have hx0 : 0 ≤ x := pronicNorm_nonneg _ _
    have h3 := abs_sq_sub_le_of_abs_sub_le hx0 h1 h2
    have hE0 : 0 ≤ weightPronicEnergy (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T :=
      sum_nonneg fun n _ => by positivity
    rw [Real.sq_sqrt hE0] at h3
    -- `x ≤ √Φm T^{γ/2} + √C`
    have hxle : x ≤ Real.sqrt Φm * (T : ℝ) ^ (γ / 2) + Real.sqrt C := by
      have hp : (Real.sqrt Φm * (T : ℝ) ^ (γ / 2)) ^ 2 = (T : ℝ) ^ γ * Φm := by
        rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hT0.le,
          show γ / 2 * ((2 : ℕ) : ℝ) = γ by push_cast; ring]
        ring
      have hq : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC0
      have hpq : 0 ≤ Real.sqrt Φm * (T : ℝ) ^ (γ / 2) := by positivity
      have hx2 : x ^ 2 ≤ (Real.sqrt Φm * (T : ℝ) ^ (γ / 2) + Real.sqrt C) ^ 2 := by
        have h2' := (abs_le.mp h2).2
        have hΦT := (abs_le.mp (hΦ T hT)).2
        nlinarith [mul_le_mul_of_nonneg_left hΦT hTγ.le, mul_nonneg hpq (Real.sqrt_nonneg C)]
      calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx0).symm
        _ ≤ Real.sqrt ((Real.sqrt Φm * (T : ℝ) ^ (γ / 2) + Real.sqrt C) ^ 2) :=
          Real.sqrt_le_sqrt hx2
        _ = _ := Real.sqrt_sq (by positivity)
    rw [show weightPronicEnergy (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T / (T : ℝ) ^ γ - probeEnergyProfile ε t T =
        (weightPronicEnergy (oscillatingSmoothPower ε t)
          (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T -
            (T : ℝ) ^ γ * probeEnergyProfile ε t T) / (T : ℝ) ^ γ by field_simp,
      abs_div, abs_of_pos hTγ, div_le_iff₀ hTγ]
    have hTm : (T : ℝ) ^ (-γ) * (T : ℝ) ^ γ = 1 := by
      rw [← Real.rpow_add hT0]; simp
    have hTm2 : (T : ℝ) ^ (-(γ / 2)) * (T : ℝ) ^ γ = (T : ℝ) ^ (γ / 2) := by
      rw [← Real.rpow_add hT0]; ring_nf
    have hrhs : ((C + B * (2 * Real.sqrt C + B)) * (T : ℝ) ^ (-γ) +
        2 * B * Real.sqrt Φm * (T : ℝ) ^ (-(γ / 2))) * (T : ℝ) ^ γ =
        C + B * (2 * Real.sqrt C + B) + 2 * B * Real.sqrt Φm * (T : ℝ) ^ (γ / 2) := by
      rw [add_mul, mul_assoc, hTm, mul_assoc (2 * B * Real.sqrt Φm), hTm2, mul_one]
    rw [hrhs]
    calc _ ≤ C + B * (2 * x + B) := h3
      _ ≤ C + B * (2 * (Real.sqrt Φm * (T : ℝ) ^ (γ / 2) + Real.sqrt C) + B) := by
          gcongr
      _ = C + B * (2 * Real.sqrt C + B) + 2 * B * Real.sqrt Φm * (T : ℝ) ^ (γ / 2) := by ring
  -- the bound tends to zero
  have hlim : Tendsto (fun T : ℕ => (C + B * (2 * Real.sqrt C + B)) * (T : ℝ) ^ (-γ) +
      2 * B * Real.sqrt Φm * (T : ℝ) ^ (-(γ / 2))) atTop (𝓝 0) := by
    have t1 := (tendsto_rpow_neg_atTop hγ0).comp tendsto_natCast_atTop_atTop
    have t2 := (tendsto_rpow_neg_atTop (by linarith : 0 < γ / 2)).comp tendsto_natCast_atTop_atTop
    simpa using (t1.const_mul (C + B * (2 * Real.sqrt C + B))).add
      (t2.const_mul (2 * B * Real.sqrt Φm))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [Real.norm_eq_abs]
  exact hbound T hT

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
