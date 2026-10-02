import GaloisForLFunctions.RHTower.Sieve.NearDiagonalOffsetBookkeeping
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

/-!
# Complete prime work for factor-count interpolation

At real part `3/4`, the parameter derivative of the corrected factor-count Euler
product contains the real kernel `Re(w / (1 + w) - w)`. On a height interval of
width comparable to `1 / log D`, its complete prime sum is at least
`a^(4/3) / (256 log a)` for `D^(9/10) ≤ a ≤ D` and every truncation covering the
central interval.

Primes between `a^(13/10)` and `a^(7/5)` have nonnegative work. The central
interval contributes a fixed positive amount per prime; PNT counts those primes.
All omitted sectors are retained in two integer-sum loss bounds, with exponents
`53/40` and `13/10`, both strictly below `4/3`.

This theorem controls the actual complete parameter kernel. It does not yet
identify the logarithmic derivative of the Euler product, bound the signed
Mellin inversion, or prove the route-MC subpower Möbius-energy estimate.
-/

noncomputable section
namespace RHTower
open Filter Topology

/-- The real parameter derivative kernel after removing its linear Euler term. -/
def mobiusFactorCountParameterKernel (w : ℂ) : ℝ := (w / (1 + w) - w).re

private lemma parameterKernel_eq {w : ℂ} (hw : 1 + w ≠ 0) :
    mobiusFactorCountParameterKernel w =
      (‖w‖ ^ 2 - 2 * w.re ^ 2 - w.re * ‖w‖ ^ 2) / ‖1 + w‖ ^ 2 := by
  have hd : Complex.normSq (1 + w) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hw)
  simp only [mobiusFactorCountParameterKernel, Complex.sub_re, Complex.div_re,
    ← Complex.normSq_eq_norm_sq, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im, zero_add]
  field_simp
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im, zero_add] at *
  ring

private lemma parameterKernel_sector {w : ℂ}
    (hlo : -‖w‖ / 2 ≤ w.re) (hhi : w.re ≤ 0) :
    ‖w‖ ^ 2 / (2 * (1 + ‖w‖) ^ 2) ≤ mobiusFactorCountParameterKernel w := by
  have hn : 0 ≤ ‖w‖ := norm_nonneg _
  have hw : 1 + w ≠ 0 := by
    intro hz
    have he : w = -1 := by linear_combination hz
    rw [he] at hlo
    norm_num at hlo
  have hsq : 4 * w.re ^ 2 ≤ ‖w‖ ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ ‖w‖ + 2 * w.re)
      (by linarith : 0 ≤ ‖w‖ - 2 * w.re)]
  have hprod : w.re * ‖w‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hhi (sq_nonneg _)
  have hnum : ‖w‖ ^ 2 / 2 ≤
      ‖w‖ ^ 2 - 2 * w.re ^ 2 - w.re * ‖w‖ ^ 2 := by nlinarith
  have hd : 0 < ‖1 + w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  have hu : ‖1 + w‖ ^ 2 ≤ (1 + ‖w‖) ^ 2 := by
    have h := norm_add_le (1 : ℂ) w
    norm_num at h
    nlinarith [norm_nonneg (1 + w)]
  rw [parameterKernel_eq hw]
  calc
    ‖w‖ ^ 2 / (2 * (1 + ‖w‖) ^ 2) =
        (‖w‖ ^ 2 / 2) / (1 + ‖w‖) ^ 2 := by rw [div_div]
    _ ≤ (‖w‖ ^ 2 / 2) / ‖1 + w‖ ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) hd hu
    _ ≤ _ := div_le_div_of_nonneg_right hnum hd.le

private lemma parameterKernel_central {w : ℂ}
    (hlo : -‖w‖ / 2 ≤ w.re) (hhi : w.re ≤ 0)
    (hrlo : 1 / 2 ≤ ‖w‖) :
    1 / 32 ≤ mobiusFactorCountParameterKernel w := by
  apply le_trans _ (parameterKernel_sector hlo hhi)
  have hd : 0 < 2 * (1 + ‖w‖) ^ 2 := by positivity
  apply (le_div_iff₀ hd).mpr
  nlinarith [sq_nonneg (‖w‖ - 1 / 2), sq_nonneg (1 - ‖w‖)]

private lemma parameterKernel_abs_le {w : ℂ} (hw : 1 + w ≠ 0) :
    |mobiusFactorCountParameterKernel w| ≤ ‖w‖ ^ 2 / ‖1 + w‖ := by
  have he : w / (1 + w) - w = -(w ^ 2) / (1 + w) := by
    field_simp
    ring
  dsimp [mobiusFactorCountParameterKernel]
  calc
    |(w / (1 + w) - w).re| ≤ ‖w / (1 + w) - w‖ := Complex.abs_re_le_norm _
    _ = _ := by rw [he, norm_div, norm_neg, norm_pow]

private lemma parameterKernel_abs_small {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    |mobiusFactorCountParameterKernel w| ≤ 2 * ‖w‖ ^ 2 := by
  have hl : 1 - ‖w‖ ≤ ‖1 + w‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) (-w)
  have hd : 0 < ‖1 + w‖ := by linarith
  apply (parameterKernel_abs_le (norm_pos_iff.mp hd)).trans
  apply (div_le_iff₀ hd).mpr
  nlinarith [sq_nonneg ‖w‖]

private lemma parameterKernel_abs_large {w : ℂ} (hw : 2 ≤ ‖w‖) :
    |mobiusFactorCountParameterKernel w| ≤ 2 * ‖w‖ := by
  have hl : ‖w‖ - 1 ≤ ‖1 + w‖ := by
    simpa [add_comm] using norm_sub_norm_le w (-1 : ℂ)
  have hd : 0 < ‖1 + w‖ := by linarith
  apply (parameterKernel_abs_le (norm_pos_iff.mp hd)).trans
  apply (div_le_iff₀ hd).mpr
  nlinarith

/-- The prime argument at real part three quarters. -/
def mobiusFactorCountPrimeArgument (a t : ℝ) (p : ℕ) : ℂ :=
  ((a * (p : ℝ) ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) *
    Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I)

private lemma norm_primeArgument {a : ℝ} (ha : 0 ≤ a) (t : ℝ) (p : ℕ) :
    ‖mobiusFactorCountPrimeArgument a t p‖ = a * (p : ℝ) ^ (-(3 / 4 : ℝ)) := by
  rw [mobiusFactorCountPrimeArgument, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]

private lemma re_primeArgument (a t : ℝ) (p : ℕ) :
    (mobiusFactorCountPrimeArgument a t p).re =
      a * (p : ℝ) ^ (-(3 / 4 : ℝ)) * Real.cos (t * Real.log p) := by
  simp only [mobiusFactorCountPrimeArgument, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    sub_zero, add_zero, Real.exp_zero, mul_one, one_mul, Real.cos_neg]

private lemma cos_sector {x : ℝ} (hxlo : Real.pi / 2 ≤ x)
    (hxhi : x ≤ 2 * Real.pi / 3) : -1 / 2 ≤ Real.cos x ∧ Real.cos x ≤ 0 := by
  have hpi := Real.pi_pos
  have hc : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  constructor
  · rw [← hc]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hxhi
  · exact Real.cos_nonpos_of_pi_div_two_le_of_le hxlo (by linarith)

private lemma primeArgument_sector {a t : ℝ} (ha : 0 ≤ a) {p : ℕ}
    (hlo : Real.pi / 2 ≤ t * Real.log p)
    (hhi : t * Real.log p ≤ 2 * Real.pi / 3) :
    0 ≤ mobiusFactorCountParameterKernel (mobiusFactorCountPrimeArgument a t p) := by
  obtain ⟨hc0, hc1⟩ := cos_sector hlo hhi
  have hr : 0 ≤ a * (p : ℝ) ^ (-(3 / 4 : ℝ)) := by positivity
  have hl : -‖mobiusFactorCountPrimeArgument a t p‖ / 2 ≤ (mobiusFactorCountPrimeArgument a t p).re := by
    rw [norm_primeArgument ha, re_primeArgument]
    nlinarith [mul_le_mul_of_nonneg_left hc0 hr]
  have hu : (mobiusFactorCountPrimeArgument a t p).re ≤ 0 := by
    rw [re_primeArgument]
    exact mul_nonpos_of_nonneg_of_nonpos hr hc1
  exact (by positivity : 0 ≤ ‖mobiusFactorCountPrimeArgument a t p‖ ^ 2 /
    (2 * (1 + ‖mobiusFactorCountPrimeArgument a t p‖) ^ 2)).trans (parameterKernel_sector hl hu)

private lemma primeArgument_middle_phase {D a t : ℝ} (hD : 1 < D)
    (ha0 : 0 < a) (haLo : D ^ (9 / 10 : ℝ) ≤ a) (haHi : a ≤ D)
    (htLo : 7 * Real.pi / (16 * Real.log D) ≤ t)
    (htHi : t ≤ 15 * Real.pi / (32 * Real.log D))
    {p : ℕ} (hp : 0 < p) (hpLo : a ^ (13 / 10 : ℝ) ≤ p)
    (hpHi : (p : ℝ) ≤ a ^ (7 / 5 : ℝ)) :
    Real.pi / 2 ≤ t * Real.log p ∧ t * Real.log p ≤ 2 * Real.pi / 3 := by
  have hD0 : 0 < D := by linarith
  have hLD : 0 < Real.log D := Real.log_pos hD
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hALo := Real.log_le_log (Real.rpow_pos_of_pos hD0 _) haLo
  rw [Real.log_rpow hD0] at hALo
  have hAHi := Real.log_le_log ha0 haHi
  have hPLo := Real.log_le_log (Real.rpow_pos_of_pos ha0 _) hpLo
  rw [Real.log_rpow ha0] at hPLo
  have hPHi := Real.log_le_log hp0 hpHi
  rw [Real.log_rpow ha0] at hPHi
  have ht0 : 0 ≤ t := (by positivity : 0 ≤ 7 * Real.pi / (16 * Real.log D)).trans htLo
  have hLP : 0 ≤ Real.log p := by linarith
  have hlo := mul_le_mul htLo (show (117 / 100 : ℝ) * Real.log D ≤ Real.log p by linarith)
    (by positivity : 0 ≤ (117 / 100 : ℝ) * Real.log D) ht0
  have hhi := mul_le_mul htHi (show Real.log p ≤ (7 / 5 : ℝ) * Real.log D by linarith)
    hLP (by positivity : 0 ≤ 15 * Real.pi / (32 * Real.log D))
  have hel : (7 * Real.pi / (16 * Real.log D)) * ((117 / 100 : ℝ) * Real.log D) =
      819 * Real.pi / 1600 := by field_simp; ring
  have heh : (15 * Real.pi / (32 * Real.log D)) * ((7 / 5 : ℝ) * Real.log D) =
      21 * Real.pi / 32 := by field_simp; ring
  rw [hel] at hlo
  rw [heh] at hhi
  constructor <;> nlinarith [Real.pi_pos]

private lemma mul_rpow_rpow {a : ℝ} (ha : 0 < a) (u v : ℝ) :
    a * (a ^ u) ^ v = a ^ (1 + u * v) := by
  rw [Real.rpow_add ha, Real.rpow_one, Real.rpow_mul ha.le]

private lemma primeArgument_low_radius {a : ℝ} (ha : 0 < a) (t : ℝ)
    {p : ℕ} (hp : 0 < p) (hpLo : (p : ℝ) ≤ a ^ (13 / 10 : ℝ)) :
    a ^ (1 / 40 : ℝ) ≤ ‖mobiusFactorCountPrimeArgument a t p‖ := by
  rw [norm_primeArgument ha.le]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hp0 hpLo (by norm_num : (-(3 / 4) : ℝ) ≤ 0)) ha.le
  rw [mul_rpow_rpow ha] at h
  norm_num at h
  exact h

private lemma primeArgument_high_radius {a : ℝ} (ha : 0 < a) (t : ℝ)
    {p : ℕ} (hpHi : a ^ (7 / 5 : ℝ) ≤ p) :
    ‖mobiusFactorCountPrimeArgument a t p‖ ≤ a ^ (-(1 / 20) : ℝ) := by
  rw [norm_primeArgument ha.le]
  have h := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos ha _) hpHi
      (by norm_num : (-(3 / 4) : ℝ) ≤ 0)) ha.le
  rw [mul_rpow_rpow ha] at h
  norm_num at h
  exact h

private lemma primeArgument_central_radius {a : ℝ} (ha : 0 < a) (t : ℝ)
    {p : ℕ} (hp : 0 < p) (hpHi : (p : ℝ) ≤ 2 * a ^ (4 / 3 : ℝ)) :
    1 / 2 ≤ ‖mobiusFactorCountPrimeArgument a t p‖ := by
  rw [norm_primeArgument ha.le]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hp0 hpHi
      (by norm_num : (-(3 / 4) : ℝ) ≤ 0)) ha.le
  have he : a * (2 * a ^ (4 / 3 : ℝ)) ^ (-(3 / 4) : ℝ) =
      (2 : ℝ) ^ (-(3 / 4) : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
    calc
      a * ((2 : ℝ) ^ (-(3 / 4) : ℝ) * (a ^ (4 / 3 : ℝ)) ^ (-(3 / 4) : ℝ)) =
          (2 : ℝ) ^ (-(3 / 4) : ℝ) *
            (a * (a ^ (4 / 3 : ℝ)) ^ (-(3 / 4) : ℝ)) := by ring
      _ = _ := by rw [mul_rpow_rpow ha]; norm_num
  rw [he] at h
  apply le_trans _ h
  calc
    (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

private def centralPrimes (a : ℝ) : Finset ℕ :=
  GaloisForLFunctions.HTGeometry.primesInIoc
    ⌊a ^ (4 / 3 : ℝ)⌋₊ ⌊2 * a ^ (4 / 3 : ℝ)⌋₊

private lemma centralPrimes_bounds {a : ℝ} (ha : 0 < a) {p : ℕ}
    (hp : p ∈ centralPrimes a) :
    p.Prime ∧ a ^ (4 / 3 : ℝ) < p ∧ (p : ℝ) ≤ 2 * a ^ (4 / 3 : ℝ) := by
  obtain ⟨hpPrime, hpLo, hpHi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  exact ⟨hpPrime, (Nat.floor_lt (by positivity)).mp hpLo,
    (Nat.cast_le.mpr hpHi).trans (Nat.floor_le (by positivity))⟩

private lemma centralPrimes_middle {a : ℝ} (ha : 1 ≤ a)
    (haGap : 2 ≤ a ^ (1 / 15 : ℝ)) {p : ℕ} (hp : p ∈ centralPrimes a) :
    a ^ (13 / 10 : ℝ) ≤ p ∧ (p : ℝ) ≤ a ^ (7 / 5 : ℝ) := by
  have ha0 : 0 < a := by linarith
  obtain ⟨_, hpLo, hpHi⟩ := centralPrimes_bounds ha0 hp
  refine ⟨(Real.rpow_le_rpow_of_exponent_le ha (by norm_num :
    (13 / 10 : ℝ) ≤ 4 / 3)).trans hpLo.le, hpHi.trans ?_⟩
  have h := mul_le_mul_of_nonneg_right haGap
    (Real.rpow_nonneg ha0.le (4 / 3 : ℝ))
  rw [← Real.rpow_add ha0] at h
  norm_num at h
  exact h

private lemma primeArgument_central_work {D a t : ℝ} (hD : 1 < D)
    (ha : 1 ≤ a) (haLo : D ^ (9 / 10 : ℝ) ≤ a) (haHi : a ≤ D)
    (haGap : 2 ≤ a ^ (1 / 15 : ℝ))
    (htLo : 7 * Real.pi / (16 * Real.log D) ≤ t)
    (htHi : t ≤ 15 * Real.pi / (32 * Real.log D))
    {p : ℕ} (hp : p ∈ centralPrimes a) :
    1 / 32 ≤ mobiusFactorCountParameterKernel (mobiusFactorCountPrimeArgument a t p) := by
  have ha0 : 0 < a := by linarith
  obtain ⟨hpPrime, _, hpUpper⟩ := centralPrimes_bounds ha0 hp
  obtain ⟨hpLo, hpHi⟩ := centralPrimes_middle ha haGap hp
  obtain ⟨hphaseLo, hphaseHi⟩ := primeArgument_middle_phase hD ha0 haLo haHi
    htLo htHi hpPrime.pos hpLo hpHi
  obtain ⟨hcLo, hcHi⟩ := cos_sector hphaseLo hphaseHi
  have hr : 0 ≤ a * (p : ℝ) ^ (-(3 / 4) : ℝ) := by positivity
  apply parameterKernel_central
  · rw [norm_primeArgument ha0.le, re_primeArgument]
    nlinarith [mul_le_mul_of_nonneg_left hcLo hr]
  · rw [re_primeArgument]
    exact mul_nonpos_of_nonneg_of_nonpos hr hcHi
  · exact primeArgument_central_radius ha0 t hpPrime.pos hpUpper

private lemma integer_head_work_le {a : ℝ} (ha : 1 ≤ a) :
    2 * a * (∑ n ∈ Finset.Icc 1 ⌊a ^ (13 / 10 : ℝ)⌋₊,
      (n : ℝ) ^ (-(3 / 4) : ℝ)) ≤ 10 * a ^ (53 / 40 : ℝ) := by
  have hfloor : (⌊a ^ (13 / 10 : ℝ)⌋₊ : ℝ) ≤ 1 * a ^ (13 / 10 : ℝ) := by
    simpa using (Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ a) (13 / 10 : ℝ)))
  have h := Sieve.head_contribution_le (T := a) (a := 13 / 10)
    (c := 3 / 4) (θ := 1) (K := 1) ha (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (M := ⌊a ^ (13 / 10 : ℝ)⌋₊) hfloor
  norm_num at h
  linarith

private lemma integer_tail_work_le {a : ℝ} (ha : 1 ≤ a) (N : ℕ) :
    2 * a ^ 2 * (∑ n ∈ Finset.Icc ⌈a ^ (7 / 5 : ℝ)⌉₊ N,
      (n : ℝ) ^ (-(3 / 2) : ℝ)) ≤ 6 * a ^ (13 / 10 : ℝ) := by
  have hceil := Nat.le_ceil (a ^ (7 / 5 : ℝ))
  have hpow : 1 ≤ a ^ (7 / 5 : ℝ) := Real.one_le_rpow ha (by norm_num)
  have hR : 1 ≤ ⌈a ^ (7 / 5 : ℝ)⌉₊ := by exact_mod_cast hpow.trans hceil
  have h := Sieve.tail_contribution_le (T := a) (a := 7 / 5)
    (c := 3 / 2) (θ := 2) ha (by norm_num) (N := N) hR hceil
  norm_num at h
  linarith

private def lowBudget (a : ℝ) (p : ℕ) : ℝ :=
  if p ≤ ⌊a ^ (13 / 10 : ℝ)⌋₊ then 2 * a * (p : ℝ) ^ (-(3 / 4) : ℝ) else 0

private def highBudget (a : ℝ) (p : ℕ) : ℝ :=
  if ⌈a ^ (7 / 5 : ℝ)⌉₊ ≤ p then 2 * a ^ 2 * (p : ℝ) ^ (-(3 / 2) : ℝ) else 0

private lemma lowBudget_nonneg {a : ℝ} (ha : 0 ≤ a) (p : ℕ) : 0 ≤ lowBudget a p := by
  unfold lowBudget
  split_ifs <;> positivity

private lemma highBudget_nonneg (a : ℝ) (p : ℕ) : 0 ≤ highBudget a p := by
  unfold highBudget
  split_ifs <;> positivity

private lemma primeArgument_norm_sq {a : ℝ} (ha : 0 ≤ a) (t : ℝ) (p : ℕ) :
    ‖mobiusFactorCountPrimeArgument a t p‖ ^ 2 = a ^ 2 * (p : ℝ) ^ (-(3 / 2) : ℝ) := by
  rw [norm_primeArgument ha, mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
  norm_num

private lemma compensated_prime_work_nonneg {D a t : ℝ} (hD : 1 < D)
    (ha : 1 ≤ a) (haLo : D ^ (9 / 10 : ℝ) ≤ a) (haHi : a ≤ D)
    (haSmall : 2 ≤ a ^ (1 / 40 : ℝ)) (haLarge : a ^ (-(1 / 20) : ℝ) ≤ 1 / 2)
    (htLo : 7 * Real.pi / (16 * Real.log D) ≤ t)
    (htHi : t ≤ 15 * Real.pi / (32 * Real.log D))
    {p : ℕ} (hp : p.Prime) :
    0 ≤ mobiusFactorCountParameterKernel (mobiusFactorCountPrimeArgument a t p) + lowBudget a p + highBudget a p := by
  have ha0 : 0 < a := by linarith
  have hlow := lowBudget_nonneg ha0.le p
  have hhigh := highBudget_nonneg a p
  by_cases hpl : p ≤ ⌊a ^ (13 / 10 : ℝ)⌋₊
  · have hpr : (p : ℝ) ≤ a ^ (13 / 10 : ℝ) :=
      (Nat.cast_le.mpr hpl).trans (Nat.floor_le (by positivity))
    have hb := parameterKernel_abs_large
      (haSmall.trans (primeArgument_low_radius ha0 t hp.pos hpr))
    have hb' := (abs_le.mp hb).1
    rw [norm_primeArgument ha0.le] at hb'
    rw [lowBudget, if_pos hpl]
    linarith
  · by_cases hph : ⌈a ^ (7 / 5 : ℝ)⌉₊ ≤ p
    · have hpr : a ^ (7 / 5 : ℝ) ≤ (p : ℝ) :=
        (Nat.le_ceil _).trans (Nat.cast_le.mpr hph)
      have hb := parameterKernel_abs_small
        ((primeArgument_high_radius ha0 t hpr).trans haLarge)
      have hb' := (abs_le.mp hb).1
      rw [primeArgument_norm_sq ha0.le] at hb'
      rw [highBudget, if_pos hph]
      linarith
    · have hpl' : a ^ (13 / 10 : ℝ) ≤ (p : ℝ) :=
        ((Nat.floor_lt (by positivity)).mp (lt_of_not_ge hpl)).le
      have hph' : (p : ℝ) ≤ a ^ (7 / 5 : ℝ) :=
        (Nat.lt_ceil.mp (lt_of_not_ge hph)).le
      obtain ⟨hl, hh⟩ := primeArgument_middle_phase hD ha0 haLo haHi
        htLo htHi hp.pos hpl' hph'
      have hk := primeArgument_sector ha0.le hl hh
      linarith

private lemma sum_lowBudget_le {a : ℝ} (ha : 1 ≤ a) (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, lowBudget a p) ≤ 10 * a ^ (53 / 40 : ℝ) := by
  classical
  let P := (Nat.primesLE N).filter (fun p => p ≤ ⌊a ^ (13 / 10 : ℝ)⌋₊)
  have hP : P ⊆ Finset.Icc 1 ⌊a ^ (13 / 10 : ℝ)⌋₊ := by
    intro p hp
    obtain ⟨hpN, hpL⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hpN).pos, hpL⟩
  calc
    _ = 2 * a * ∑ p ∈ P, (p : ℝ) ^ (-(3 / 4) : ℝ) := by
      simp only [lowBudget, P, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    _ ≤ 2 * a * ∑ p ∈ Finset.Icc 1 ⌊a ^ (13 / 10 : ℝ)⌋₊,
        (p : ℝ) ^ (-(3 / 4) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg hP (fun _ _ _ => by positivity)
    _ ≤ _ := integer_head_work_le ha

private lemma sum_highBudget_le {a : ℝ} (ha : 1 ≤ a) (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, highBudget a p) ≤ 6 * a ^ (13 / 10 : ℝ) := by
  classical
  let P := (Nat.primesLE N).filter (fun p => ⌈a ^ (7 / 5 : ℝ)⌉₊ ≤ p)
  have hP : P ⊆ Finset.Icc ⌈a ^ (7 / 5 : ℝ)⌉₊ N := by
    intro p hp
    obtain ⟨hpN, hpL⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨hpL, Nat.le_of_mem_primesLE hpN⟩
  calc
    _ = 2 * a ^ 2 * ∑ p ∈ P, (p : ℝ) ^ (-(3 / 2) : ℝ) := by
      simp only [highBudget, P, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    _ ≤ 2 * a ^ 2 * ∑ p ∈ Finset.Icc ⌈a ^ (7 / 5 : ℝ)⌉₊ N,
        (p : ℝ) ^ (-(3 / 2) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg hP (fun _ _ _ => by positivity)
    _ ≤ _ := integer_tail_work_le ha N

private lemma complete_prime_work_lower {D a t : ℝ} (hD : 1 < D)
    (ha : 1 ≤ a) (haLo : D ^ (9 / 10 : ℝ) ≤ a) (haHi : a ≤ D)
    (haSmall : 2 ≤ a ^ (1 / 40 : ℝ)) (haLarge : a ^ (-(1 / 20) : ℝ) ≤ 1 / 2)
    (haGap : 2 ≤ a ^ (1 / 15 : ℝ))
    (htLo : 7 * Real.pi / (16 * Real.log D) ≤ t)
    (htHi : t ≤ 15 * Real.pi / (32 * Real.log D))
    {N : ℕ} (hN : ⌊2 * a ^ (4 / 3 : ℝ)⌋₊ ≤ N) :
    (centralPrimes a).card / (32 : ℝ) - 10 * a ^ (53 / 40 : ℝ) -
        6 * a ^ (13 / 10 : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, mobiusFactorCountParameterKernel (mobiusFactorCountPrimeArgument a t p) := by
  classical
  have ha0 : 0 < a := by linarith
  let g := fun p => mobiusFactorCountParameterKernel (mobiusFactorCountPrimeArgument a t p) + lowBudget a p + highBudget a p
  have hCP : centralPrimes a ⊆ Nat.primesLE N := by
    intro p hp
    obtain ⟨hpPrime, _, hpN⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
    exact Nat.mem_primesLE.mpr ⟨hpN.trans hN, hpPrime⟩
  have hg : ∀ p ∈ Nat.primesLE N, 0 ≤ g p := by
    intro p hp
    exact compensated_prime_work_nonneg hD ha haLo haHi haSmall haLarge
      htLo htHi (Nat.prime_of_mem_primesLE hp)
  have hc : ∀ p ∈ centralPrimes a, (1 / 32 : ℝ) ≤ g p := by
    intro p hp
    have hk := primeArgument_central_work hD ha haLo haHi haGap htLo htHi hp
    have hl := lowBudget_nonneg ha0.le p
    have hh := highBudget_nonneg a p
    dsimp [g]
    linarith
  have hsum : (centralPrimes a).card / (32 : ℝ) ≤ ∑ p ∈ Nat.primesLE N, g p := by
    calc
      _ = ∑ p ∈ centralPrimes a, (1 / 32 : ℝ) := by simp; ring
      _ ≤ ∑ p ∈ centralPrimes a, g p := Finset.sum_le_sum hc
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hCP (fun p hp _ => hg p hp)
  dsimp [g] at hsum
  simp only [Finset.sum_add_distrib] at hsum
  have hl := sum_lowBudget_le ha N
  have hh := sum_highBudget_le ha N
  linarith

private lemma eventually_centralPrimes_lower :
    ∀ᶠ a : ℝ in atTop, a ^ (4 / 3 : ℝ) / (4 * Real.log a) ≤
      (centralPrimes a).card := by
  have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 3)).eventually
    (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge
      (K := 2) (by norm_num))
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with a ha hA
  have ha0 : 0 < a := by linarith
  have hlog : 0 < Real.log a := Real.log_pos hA
  have hp : 0 < a ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos ha0 _
  have hc := GaloisForLFunctions.HTGeometry.card_primesInIoc
    (Nat.floor_le_floor (show a ^ (4 / 3 : ℝ) ≤ 2 * a ^ (4 / 3 : ℝ) by linarith))
  change ((centralPrimes a).card : ℝ) = _ at hc
  rw [← hc, Real.log_rpow ha0] at ha
  norm_num at ha
  apply le_trans _ ha
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.log a)).mpr
  field_simp
  nlinarith

private lemma eventually_integer_losses_small :
    ∀ᶠ a : ℝ in atTop,
      10 * a ^ (53 / 40 : ℝ) + 6 * a ^ (13 / 10 : ℝ) ≤
        a ^ (4 / 3 : ℝ) / (512 * Real.log a) := by
  have hlim := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 120)).tendsto_div_nhds_zero
  have hb := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8192))
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with a ha hA
  have ha0 : 0 < a := by linarith
  have hlog : 0 < Real.log a := Real.log_pos hA
  have hp : 0 < a ^ (1 / 120 : ℝ) := Real.rpow_pos_of_pos ha0 _
  have hsmall : Real.log a ≤ (1 / 8192 : ℝ) * a ^ (1 / 120 : ℝ) :=
    (div_le_iff₀ hp).mp ha.le
  have hm := mul_le_mul_of_nonneg_left hsmall
    (Real.rpow_nonneg ha0.le (53 / 40 : ℝ))
  have he : a ^ (53 / 40 : ℝ) * a ^ (1 / 120 : ℝ) = a ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_add ha0]
    norm_num
  have hmono : a ^ (13 / 10 : ℝ) ≤ a ^ (53 / 40 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hA.le (by norm_num)
  calc
    _ ≤ 16 * a ^ (53 / 40 : ℝ) := by linarith
    _ ≤ _ := by
      apply (le_div_iff₀ (by positivity : 0 < 512 * Real.log a)).mpr
      nlinarith [he]

/-- Complete prime work has positive superlinear parameter growth on a moving vertical sector.
Every prime up to the arbitrary truncation is retained; the truncation need only cover
the central interval. -/
theorem eventually_mobiusFactorCountPrimeWork_lower :
    ∀ᶠ D : ℝ in atTop, ∀ a t : ℝ,
      D ^ (9 / 10 : ℝ) ≤ a → a ≤ D →
      7 * Real.pi / (16 * Real.log D) ≤ t →
      t ≤ 15 * Real.pi / (32 * Real.log D) →
      ∀ N : ℕ, ⌊2 * a ^ (4 / 3 : ℝ)⌋₊ ≤ N →
        a ^ (4 / 3 : ℝ) / (256 * Real.log a) ≤
          ∑ p ∈ Nat.primesLE N, mobiusFactorCountParameterKernel (mobiusFactorCountPrimeArgument a t p) := by
  have hsmall : ∀ᶠ a : ℝ in atTop, 2 ≤ a ^ (1 / 40 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 40)).eventually (eventually_ge_atTop 2)
  have hlarge : ∀ᶠ a : ℝ in atTop, a ^ (-(1 / 20) : ℝ) ≤ 1 / 2 := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 20)).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    exact h.mono fun _ ha => ha.le
  have hgap : ∀ᶠ a : ℝ in atTop, 2 ≤ a ^ (1 / 15 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 15)).eventually (eventually_ge_atTop 2)
  have haAll : ∀ᶠ a : ℝ in atTop, 1 < a ∧ 2 ≤ a ^ (1 / 40 : ℝ) ∧
      a ^ (-(1 / 20) : ℝ) ≤ 1 / 2 ∧ 2 ≤ a ^ (1 / 15 : ℝ) ∧
      a ^ (4 / 3 : ℝ) / (4 * Real.log a) ≤ (centralPrimes a).card ∧
      10 * a ^ (53 / 40 : ℝ) + 6 * a ^ (13 / 10 : ℝ) ≤
        a ^ (4 / 3 : ℝ) / (512 * Real.log a) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hsmall, hlarge, hgap,
      eventually_centralPrimes_lower, eventually_integer_losses_small]
      with a h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨A, hA⟩ := eventually_atTop.mp haAll
  have hDlarge := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)).eventually
    (eventually_ge_atTop A)
  filter_upwards [hDlarge, eventually_gt_atTop (1 : ℝ)] with D hDA hD
  intro a t haLo haHi htLo htHi N hN
  obtain ⟨ha, haSmall, haLarge, haGap, haCount, haLoss⟩ := hA a (hDA.trans haLo)
  have hbound := complete_prime_work_lower hD ha.le haLo haHi haSmall haLarge
    haGap htLo htHi hN
  have hlog : 0 < Real.log a := Real.log_pos ha
  have ha0 : 0 < a := by linarith
  have hc : a ^ (4 / 3 : ℝ) / (128 * Real.log a) ≤ (centralPrimes a).card / 32 := by
    calc
      _ = (a ^ (4 / 3 : ℝ) / (4 * Real.log a)) / 32 := by
        rw [div_div]
        congr 1
        ring
      _ ≤ _ := div_le_div_of_nonneg_right haCount (by norm_num : (0 : ℝ) ≤ 32)
  have he : a ^ (4 / 3 : ℝ) / (256 * Real.log a) ≤
      a ^ (4 / 3 : ℝ) / (128 * Real.log a) -
        a ^ (4 / 3 : ℝ) / (512 * Real.log a) := by
    have heq : a ^ (4 / 3 : ℝ) / (128 * Real.log a) -
        a ^ (4 / 3 : ℝ) / (512 * Real.log a) -
        a ^ (4 / 3 : ℝ) / (256 * Real.log a) =
        a ^ (4 / 3 : ℝ) / (512 * Real.log a) := by field_simp; ring
    have hn : 0 ≤ a ^ (4 / 3 : ℝ) / (512 * Real.log a) := by positivity
    linarith
  linarith

end RHTower
