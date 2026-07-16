import GaloisForLFunctions.RHTower.SoninSemilocalGradingDeformation
import GaloisForLFunctions.RHTower.GammaConductorSchurCapacity
import GaloisForLFunctions.RHTower.HardyTitchmarshSemilocalSquare
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

open Complex Filter MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace RHTower

theorem exists_semilocalOnePrimeMatchedDilation
    {k p : ℕ} (hk : 0 < k) (hp : p.Prime) :
    ∃ M : ℕ, 0 < M ∧
      (8 * k : ℝ) < (p : ℝ) ^ (2 * M) ∧
      (p : ℝ) ^ (2 * M) ≤ 8 * p ^ 2 * k := by
  have hxpos : 0 < (8 * k : ℝ) := by positivity
  have hx1 : 1 ≤ Real.sqrt (8 * k : ℝ) := by
    rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) hxpos.le]
    norm_num
    norm_cast
    omega
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  obtain ⟨m, hmlo, hmhi⟩ := exists_nat_pow_near hx1 hp1
  refine ⟨m + 1, by omega, ?_, ?_⟩
  · rw [show 2 * (m + 1) = (m + 1) * 2 by omega, pow_mul]
    have hsqrt := Real.sq_sqrt hxpos.le
    nlinarith [sq_nonneg ((p : ℝ) ^ (m + 1) - Real.sqrt (8 * k : ℝ))]
  · have hstep : (p : ℝ) ^ (m + 1) ≤ p * Real.sqrt (8 * k : ℝ) := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left hmlo (by positivity)
    rw [show 2 * (m + 1) = (m + 1) * 2 by omega, pow_mul]
    have hsqrt := Real.sq_sqrt hxpos.le
    have hp0 : (0 : ℝ) ≤ p := by positivity
    nlinarith [sq_nonneg ((p : ℝ) ^ (m + 1)), sq_nonneg (p * Real.sqrt (8 * k : ℝ))]

theorem semilocalPrimePoissonRatio_sq
    {p : ℕ} (hp : p.Prime) :
    semilocalPrimePoissonRatio p ^ 2 = (p : ℝ)⁻¹ := by
  unfold semilocalPrimePoissonRatio
  rw [inv_pow, Real.sq_sqrt (by exact_mod_cast hp.pos.le)]

theorem semilocalPrimePoissonRatio_pow_two_mul
    {p : ℕ} (hp : p.Prime) (M : ℕ) :
    semilocalPrimePoissonRatio p ^ (2 * M) = ((p : ℝ) ^ M)⁻¹ := by
  rw [pow_mul, semilocalPrimePoissonRatio_sq hp, inv_pow]

theorem semilocalArchimedeanCharacteristic_nat_mul_log_sq
    {p : ℕ} (hp : p.Prime) (M : ℕ) :
    semilocalArchimedeanCharacteristic ((M : ℝ) * Real.log p) ^ 2 =
      2 * (p : ℝ) ^ M / (((p : ℝ) ^ M) ^ 2 + 1) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hx : 0 < (p : ℝ) ^ M := pow_pos hpR _
  rw [← Real.log_pow, semilocalArchimedeanCharacteristic_sq,
    Real.cosh_log hx]
  field_simp

theorem semilocalPrimePoissonCharacteristicProduct_sq
    {p : ℕ} (hp : p.Prime) (M : ℕ) :
    (semilocalPrimePoissonRatio p ^ M *
        semilocalArchimedeanCharacteristic ((M : ℝ) * Real.log p)) ^ 2 =
      2 / (((p : ℝ) ^ M) ^ 2 + 1) := by
  rw [mul_pow, ← pow_mul]
  rw [show M * 2 = 2 * M by omega,
    semilocalPrimePoissonRatio_pow_two_mul hp M,
    semilocalArchimedeanCharacteristic_nat_mul_log_sq hp M]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hx : (p : ℝ) ^ M ≠ 0 := (pow_pos hpR _).ne'
  field_simp

theorem tanh_nat_mul_log_prime
    {p : ℕ} (hp : p.Prime) (M : ℕ) :
    Real.tanh ((M : ℝ) * Real.log p) =
      (((p : ℝ) ^ M) ^ 2 - 1) / (((p : ℝ) ^ M) ^ 2 + 1) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hx : 0 < (p : ℝ) ^ M := pow_pos hpR _
  rw [← Real.log_pow, Real.tanh_eq_sinh_div_cosh,
    Real.sinh_log hx, Real.cosh_log hx]
  field_simp

theorem semilocalPrimePoissonCharacteristicProduct_lower
    {p : ℕ} (hp : p.Prime) (M : ℕ) :
    ((p : ℝ) ^ M)⁻¹ ≤
      semilocalPrimePoissonRatio p ^ M *
        semilocalArchimedeanCharacteristic ((M : ℝ) * Real.log p) := by
  let x : ℝ := (p : ℝ) ^ M
  let b : ℝ := semilocalPrimePoissonRatio p ^ M *
    semilocalArchimedeanCharacteristic ((M : ℝ) * Real.log p)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact one_le_pow₀ hp1
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hb : 0 ≤ b := by
    dsimp [b]
    exact mul_nonneg (pow_nonneg (semilocalPrimePoissonRatio_pos hp).le _)
      (semilocalArchimedeanCharacteristic_pos _).le
  have hsq : b ^ 2 = 2 / (x ^ 2 + 1) := by
    dsimp [b, x]
    exact semilocalPrimePoissonCharacteristicProduct_sq hp M
  apply (sq_le_sq₀ (inv_nonneg.mpr hx.le) hb).mp
  rw [hsq]
  have hden : 0 < x ^ 2 + 1 := by positivity
  rw [inv_pow, ← one_div]
  rw [div_le_div_iff₀ (sq_pos_of_pos hx) hden]
  nlinarith [sq_nonneg x]

theorem semilocalPrimePoissonCharacteristicProduct_upper
    {p : ℕ} (hp : p.Prime) (M : ℕ) :
    semilocalPrimePoissonRatio p ^ M *
        semilocalArchimedeanCharacteristic ((M : ℝ) * Real.log p) ≤
      2 * ((p : ℝ) ^ M)⁻¹ := by
  let x : ℝ := (p : ℝ) ^ M
  let b : ℝ := semilocalPrimePoissonRatio p ^ M *
    semilocalArchimedeanCharacteristic ((M : ℝ) * Real.log p)
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hx : 0 < x := by dsimp [x]; exact pow_pos hpR _
  have hb : 0 ≤ b := by
    dsimp [b]
    exact mul_nonneg (pow_nonneg (semilocalPrimePoissonRatio_pos hp).le _)
      (semilocalArchimedeanCharacteristic_pos _).le
  have hright : 0 ≤ 2 * x⁻¹ := mul_nonneg (by norm_num) (inv_nonneg.mpr hx.le)
  have hsq : b ^ 2 = 2 / (x ^ 2 + 1) := by
    dsimp [b, x]
    exact semilocalPrimePoissonCharacteristicProduct_sq hp M
  apply (sq_le_sq₀ hb hright).mp
  rw [hsq]
  have hden : 0 < x ^ 2 + 1 := by positivity
  rw [div_le_iff₀ hden]
  field_simp
  nlinarith [sq_nonneg x]

theorem one_sub_pow_le_inv_one_add_nat_mul
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (N : ℕ) :
    (1 - a) ^ N ≤ (1 + (N : ℝ) * a)⁻¹ := by
  have hden : 0 < 1 + (N : ℝ) * a := by positivity
  rw [inv_eq_one_div, le_div_iff₀ hden]
  have hprod : ∀ n : ℕ,
      (1 - a) ^ n * (1 + (n : ℝ) * a) ≤ 1 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ]
        push_cast
        have hbase : 0 ≤ (1 - a) ^ n := pow_nonneg (sub_nonneg.mpr ha1) _
        have hstep :
            (1 - a) * (1 + ((n : ℝ) + 1) * a) ≤
              1 + (n : ℝ) * a := by
          nlinarith [sq_nonneg a]
        calc
          (1 - a) ^ n * (1 - a) *
                (1 + ((n : ℝ) + 1) * a) =
              (1 - a) ^ n *
                ((1 - a) * (1 + ((n : ℝ) + 1) * a)) := by ring
          _ ≤ (1 - a) ^ n * (1 + (n : ℝ) * a) :=
            mul_le_mul_of_nonneg_left hstep hbase
          _ ≤ 1 := ih
  exact hprod N

theorem tanh_nat_mul_log_prime_pow_le
    {k p M : ℕ} (hk : 0 < k) (hp : p.Prime) :
    Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) ≤
      (((p : ℝ) ^ M) ^ 2 + 1) /
        (((p : ℝ) ^ M) ^ 2 + 1 + 4 * k) := by
  let x : ℝ := (p : ℝ) ^ M
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact one_le_pow₀ hp1
  let a : ℝ := 2 / (x ^ 2 + 1)
  have hden : 0 < x ^ 2 + 1 := by positivity
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one hden]
    nlinarith [sq_nonneg x]
  have hbern := one_sub_pow_le_inv_one_add_nat_mul ha0 ha1 (2 * k)
  have htanh : Real.tanh ((M : ℝ) * Real.log p) = 1 - a := by
    rw [tanh_nat_mul_log_prime hp M]
    dsimp [a, x]
    field_simp
    ring
  rw [htanh]
  calc
    (1 - a) ^ (2 * k) ≤ (1 + ((2 * k : ℕ) : ℝ) * a)⁻¹ := hbern
    _ = (x ^ 2 + 1) / (x ^ 2 + 1 + 4 * k) := by
      dsimp [a]
      push_cast
      field_simp
      ring

theorem tanh_nat_mul_log_prime_pow_le_sq_div
    {k p M : ℕ} (hk : 0 < k) (hp : p.Prime) :
    Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) ≤
      ((p : ℝ) ^ M) ^ 2 / (2 * k) := by
  let x : ℝ := (p : ℝ) ^ M
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact one_le_pow₀ hp1
  have h := tanh_nat_mul_log_prime_pow_le hk hp (M := M)
  change Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) ≤ x ^ 2 / (2 * k)
  change Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) ≤
    (x ^ 2 + 1) / (x ^ 2 + 1 + 4 * k) at h
  refine h.trans ?_
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hden : 0 < x ^ 2 + 1 + 4 * k := by positivity
  rw [div_le_div_iff₀ hden (by positivity : (0 : ℝ) < 2 * k)]
  have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  have hprod : 0 ≤ (2 * (k : ℝ)) * (x ^ 2 - 1) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hx2)
  nlinarith [sq_nonneg (x ^ 2), hprod]

theorem semilocalOnePrimeRawMagnitude_le_low
    {k p M : ℕ} (hk : 0 < k) (hp : p.Prime) :
    semilocalPrimePoissonRatio p ^ M *
          semilocalArchimedeanCharacteristic ((M : ℝ) * Real.log p) *
          Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) ≤
      (p : ℝ) ^ M / k := by
  let x : ℝ := (p : ℝ) ^ M
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hx : 0 < x := by dsimp [x]; positivity
  have hb := semilocalPrimePoissonCharacteristicProduct_upper hp M
  have ht := tanh_nat_mul_log_prime_pow_le_sq_div hk hp (M := M)
  have heven : Even (2 * k) := ⟨k, by omega⟩
  have ht0 : 0 ≤ Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) :=
    heven.pow_nonneg _
  have hupper0 : 0 ≤ 2 * x⁻¹ := by positivity
  calc
    semilocalPrimePoissonRatio p ^ M *
          semilocalArchimedeanCharacteristic ((M : ℝ) * Real.log p) *
          Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) ≤
        (2 * x⁻¹) * (x ^ 2 / (2 * k)) :=
      mul_le_mul hb ht ht0 hupper0
    _ = x / k := by field_simp

theorem semilocalOnePrimeRawMagnitude_le_tail
    {k p M : ℕ} (hp : p.Prime) :
    semilocalPrimePoissonRatio p ^ M *
          semilocalArchimedeanCharacteristic ((M : ℝ) * Real.log p) *
          Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) ≤
      2 * ((p : ℝ) ^ M)⁻¹ := by
  have hb := semilocalPrimePoissonCharacteristicProduct_upper hp M
  have heven : Even (2 * k) := ⟨k, by omega⟩
  have ht0 : 0 ≤ Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) :=
    heven.pow_nonneg _
  have hupper0 : 0 ≤ 2 * ((p : ℝ) ^ M)⁻¹ := by positivity
  have ht1 : Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) ≤ 1 := by
    calc
      Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) =
          |Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k)| :=
        (abs_of_nonneg ht0).symm
      _ = |Real.tanh ((M : ℝ) * Real.log p)| ^ (2 * k) := abs_pow _ _
      _ ≤ 1 ^ (2 * k) := pow_le_pow_left₀ (abs_nonneg _)
        (Real.abs_tanh_lt_one _).le _
      _ = 1 := one_pow _
  calc
    semilocalPrimePoissonRatio p ^ M *
          semilocalArchimedeanCharacteristic ((M : ℝ) * Real.log p) *
          Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) ≤
        (2 * ((p : ℝ) ^ M)⁻¹) * 1 :=
      mul_le_mul hb ht1 ht0 hupper0
    _ = _ := mul_one _

theorem tanh_nat_mul_log_prime_pow_lower_of_matched
    {k p M : ℕ} (hk : 0 < k) (hp : p.Prime)
    (hmatch : (8 * k : ℝ) < (p : ℝ) ^ (2 * M)) :
    (1 / 2 : ℝ) ≤
      Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) := by
  let x : ℝ := (p : ℝ) ^ M
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact one_le_pow₀ hp1
  have hxmatch : (8 * k : ℝ) < x ^ 2 := by
    dsimp [x]
    rw [show 2 * M = M * 2 by omega, pow_mul] at hmatch
    exact hmatch
  let a : ℝ := 1 - 1 / (4 * k)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha0 : 0 ≤ a := by
    dsimp [a]
    rw [sub_nonneg, div_le_one (by positivity : (0 : ℝ) < 4 * k)]
    nlinarith
  have htanha : a ≤ Real.tanh ((M : ℝ) * Real.log p) := by
    rw [tanh_nat_mul_log_prime hp M]
    dsimp [a, x]
    have hden : 0 < x ^ 2 + 1 := by positivity
    rw [le_div_iff₀ hden]
    field_simp
    nlinarith
  have hbern := one_add_mul_sub_le_pow
    (a := a) (show (-1 : ℝ) ≤ a by linarith) (2 * k)
  have halower : (1 / 2 : ℝ) ≤ a ^ (2 * k) := by
    apply le_trans ?_ hbern
    dsimp [a]
    push_cast
    field_simp
    norm_num
  exact halower.trans (pow_le_pow_left₀ ha0 htanha _)

theorem semilocalOnePrimeRawMagnitude_lower_of_matched
    {k p M : ℕ} (hk : 0 < k) (hp : p.Prime)
    (hmatch : (8 * k : ℝ) < (p : ℝ) ^ (2 * M)) :
    (2 * ((p : ℝ) ^ M))⁻¹ ≤
      semilocalPrimePoissonRatio p ^ M *
          semilocalArchimedeanCharacteristic ((M : ℝ) * Real.log p) *
          Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) := by
  have hb := semilocalPrimePoissonCharacteristicProduct_lower hp M
  have ht := tanh_nat_mul_log_prime_pow_lower_of_matched hk hp hmatch
  have hleft0 : 0 ≤ ((p : ℝ) ^ M)⁻¹ := by positivity
  have hb0 : 0 ≤ semilocalPrimePoissonRatio p ^ M *
      semilocalArchimedeanCharacteristic ((M : ℝ) * Real.log p) :=
    mul_nonneg (pow_nonneg (semilocalPrimePoissonRatio_pos hp).le _)
      (semilocalArchimedeanCharacteristic_pos _).le
  calc
    (2 * ((p : ℝ) ^ M))⁻¹ = ((p : ℝ) ^ M)⁻¹ * (1 / 2) := by ring
    _ ≤ (semilocalPrimePoissonRatio p ^ M *
          semilocalArchimedeanCharacteristic ((M : ℝ) * Real.log p)) *
          Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k) :=
      mul_le_mul hb ht (by norm_num) hb0

theorem semilocalArchimedeanJacobiNormalization_pow_four_mul_wallis
    (n : ℕ) :
    semilocalArchimedeanJacobiNormalization n ^ 4 *
        (Real.Wallis.W n * (2 * n + 1)) = 1 := by
  rw [show semilocalArchimedeanJacobiNormalization n ^ 4 =
      (semilocalArchimedeanJacobiNormalization n ^ 2) ^ 2 by ring,
    semilocalArchimedeanJacobiNormalization_sq,
    Real.Wallis.W_eq_factorial_ratio]
  field_simp
  ring

theorem wallis_half_le (n : ℕ) : (1 / 2 : ℝ) ≤ Real.Wallis.W n := by
  have h := Real.Wallis.le_W n
  have hratio : (1 / 2 : ℝ) ≤ ((2 : ℝ) * n + 1) / (2 * n + 2) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n + 2)]
    nlinarith
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := by
    have := Real.pi_gt_three
    linarith
  calc
    (1 / 2 : ℝ) ≤ ((2 : ℝ) * n + 1) / (2 * n + 2) := hratio
    _ ≤ ((2 : ℝ) * n + 1) / (2 * n + 2) * (Real.pi / 2) := by
      exact le_mul_of_one_le_right (by positivity) hpi
    _ ≤ Real.Wallis.W n := h

theorem wallis_le_two (n : ℕ) : Real.Wallis.W n ≤ 2 := by
  exact (Real.Wallis.W_le n).trans (by nlinarith [Real.pi_lt_four])

theorem semilocalArchimedeanJacobiNormalization_pow_four_bounds
    {n : ℕ} (hn : 0 < n) :
    (6 * n : ℝ)⁻¹ ≤ semilocalArchimedeanJacobiNormalization n ^ 4 ∧
      semilocalArchimedeanJacobiNormalization n ^ 4 ≤ (n : ℝ)⁻¹ := by
  let c := semilocalArchimedeanJacobiNormalization n
  let w := Real.Wallis.W n
  have hc : 0 < c := semilocalArchimedeanJacobiNormalization_pos n
  have hwpos : 0 < w := Real.Wallis.W_pos n
  have hprod : c ^ 4 * (w * (2 * n + 1)) = 1 := by
    dsimp [c, w]
    exact semilocalArchimedeanJacobiNormalization_pow_four_mul_wallis n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdenpos : 0 < w * (2 * n + 1) := by positivity
  have hc4 : c ^ 4 = (w * (2 * n + 1))⁻¹ := by
    exact eq_inv_of_mul_eq_one_left hprod
  have hdenUpper : w * (2 * n + 1) ≤ 6 * n := by
    have hw := wallis_le_two n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_le_mul_of_nonneg_right hw (by positivity : (0 : ℝ) ≤ 2 * n + 1)]
  have hdenLower : (n : ℝ) ≤ w * (2 * n + 1) := by
    have hw := wallis_half_le n
    have hfac : (n : ℝ) ≤ (1 / 2 : ℝ) * (2 * n + 1) := by linarith
    exact hfac.trans (mul_le_mul_of_nonneg_right hw (by positivity))
  rw [hc4]
  constructor
  · exact (inv_le_inv₀ (by positivity) hdenpos).2 hdenUpper
  · exact (inv_le_inv₀ hdenpos hnR).2 hdenLower

theorem sum_range_prime_pow_succ_le
    {p M : ℕ} (hp2 : 2 ≤ p) :
    (∑ m ∈ Finset.range M, (p : ℝ) ^ (m + 1)) ≤ 2 * (p : ℝ) ^ M := by
  induction M with
  | zero => norm_num
  | succ M ih =>
      rw [Finset.sum_range_succ]
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      have hpow : 0 ≤ (p : ℝ) ^ M := by positivity
      calc
        (∑ m ∈ Finset.range M, (p : ℝ) ^ (m + 1)) +
              (p : ℝ) ^ (M + 1) ≤
            2 * (p : ℝ) ^ M + (p : ℝ) ^ (M + 1) :=
          add_le_add ih le_rfl
        _ ≤ 2 * (p : ℝ) ^ (M + 1) := by
          rw [pow_succ]
          nlinarith

theorem tsum_two_mul_prime_inv_pow_add_le
    {p M : ℕ} (hp2 : 2 ≤ p) :
    (∑' j : ℕ, 2 * ((p : ℝ) ^ (M + j + 1))⁻¹) ≤
      2 * ((p : ℝ) ^ M)⁻¹ := by
  let q : ℝ := (p : ℝ)⁻¹
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < p := by positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqhalf : q ≤ 1 / 2 := by
    dsimp [q]
    simpa [one_div] using
      (inv_le_inv₀ hp0 (by norm_num : (0 : ℝ) < 2)).2 hpR
  have hq1 : q < 1 := hqhalf.trans_lt (by norm_num)
  have hs : Summable (fun j : ℕ => q ^ j) :=
    summable_geometric_of_norm_lt_one (by simpa [abs_of_nonneg hq0] using hq1)
  calc
    (∑' j : ℕ, 2 * ((p : ℝ) ^ (M + j + 1))⁻¹) =
        2 * ((p : ℝ) ^ M)⁻¹ * (∑' j : ℕ, q ^ (j + 1)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      dsimp [q]
      rw [inv_pow]
      ring_nf
    _ = 2 * ((p : ℝ) ^ M)⁻¹ *
          (q * (1 - q)⁻¹) := by
      rw [show (∑' j : ℕ, q ^ (j + 1)) = q * (∑' j : ℕ, q ^ j) by
        rw [← hs.tsum_mul_left]
        apply tsum_congr
        intro j
        rw [pow_succ']]
      rw [tsum_geometric_of_lt_one hq0 hq1]
    _ ≤ 2 * ((p : ℝ) ^ M)⁻¹ * 1 := by
      have hden : 0 < 1 - q := sub_pos.mpr hq1
      have hratio : q * (1 - q)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hden]
        linarith
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := mul_one _

theorem summable_two_mul_prime_inv_pow_add
    {p M : ℕ} (hp : 1 < p) :
    Summable (fun j : ℕ => 2 * ((p : ℝ) ^ (M + j + 1))⁻¹) := by
  let q : ℝ := (p : ℝ)⁻¹
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.trans' Nat.zero_lt_one
  have hqnorm : ‖q‖ < 1 := by
    dsimp [q]
    rw [abs_inv, abs_of_pos hp0]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp)
  have hs := summable_geometric_of_norm_lt_one hqnorm
  have hscaled := hs.mul_left (2 * ((p : ℝ) ^ M)⁻¹ * q)
  apply hscaled.congr
  intro j
  dsimp [q]
  rw [inv_pow]
  ring_nf

theorem semilocalOnePrimeEvenJacobiMagnitudeTerm_eq_normalization_mul_raw
    (k p m : ℕ) :
    semilocalOnePrimeEvenJacobiMagnitudeTerm k p m =
      semilocalArchimedeanJacobiNormalization (2 * k) *
        (semilocalPrimePoissonRatio p ^ (m + 1) *
          semilocalArchimedeanCharacteristic
            (((m + 1 : ℕ) : ℝ) * Real.log p) *
          Real.tanh (((m + 1 : ℕ) : ℝ) * Real.log p) ^ (2 * k)) := by
  unfold semilocalOnePrimeEvenJacobiMagnitudeTerm
  ring

theorem semilocalOnePrimeEvenJacobiMagnitudeTerm_le_low
    {k p : ℕ} (hk : 0 < k) (hp : p.Prime) (m : ℕ) :
    semilocalOnePrimeEvenJacobiMagnitudeTerm k p m ≤
      semilocalArchimedeanJacobiNormalization (2 * k) *
        ((p : ℝ) ^ (m + 1) / k) := by
  rw [semilocalOnePrimeEvenJacobiMagnitudeTerm_eq_normalization_mul_raw]
  exact mul_le_mul_of_nonneg_left
    (semilocalOnePrimeRawMagnitude_le_low hk hp)
    (semilocalArchimedeanJacobiNormalization_pos _).le

theorem semilocalOnePrimeEvenJacobiMagnitudeTerm_le_tail
    {k p : ℕ} (hp : p.Prime) (m : ℕ) :
    semilocalOnePrimeEvenJacobiMagnitudeTerm k p m ≤
      semilocalArchimedeanJacobiNormalization (2 * k) *
        (2 * ((p : ℝ) ^ (m + 1))⁻¹) := by
  rw [semilocalOnePrimeEvenJacobiMagnitudeTerm_eq_normalization_mul_raw]
  exact mul_le_mul_of_nonneg_left
    (semilocalOnePrimeRawMagnitude_le_tail hp)
    (semilocalArchimedeanJacobiNormalization_pos _).le

theorem semilocalOnePrimeEvenJacobiMagnitudeSeries_lower_of_matched
    {k p M : ℕ} (hk : 0 < k) (hp : p.Prime) (hM : 0 < M)
    (hmatch : (8 * k : ℝ) < (p : ℝ) ^ (2 * M)) :
    semilocalArchimedeanJacobiNormalization (2 * k) *
          (2 * ((p : ℝ) ^ M))⁻¹ ≤
      semilocalOnePrimeEvenJacobiMagnitudeSeries k p := by
  have hs := summable_semilocalOnePrimeEvenJacobiMagnitudeTerm (k := k) hp
  have hterm := semilocalOnePrimeRawMagnitude_lower_of_matched hk hp hmatch
  calc
    semilocalArchimedeanJacobiNormalization (2 * k) *
          (2 * ((p : ℝ) ^ M))⁻¹ ≤
        semilocalOnePrimeEvenJacobiMagnitudeTerm k p (M - 1) := by
      rw [semilocalOnePrimeEvenJacobiMagnitudeTerm_eq_normalization_mul_raw,
        Nat.sub_add_cancel hM]
      exact mul_le_mul_of_nonneg_left hterm
        (semilocalArchimedeanJacobiNormalization_pos _).le
    _ ≤ semilocalOnePrimeEvenJacobiMagnitudeSeries k p := by
      unfold semilocalOnePrimeEvenJacobiMagnitudeSeries
      exact hs.le_tsum (M - 1) (fun m _ =>
        (semilocalOnePrimeEvenJacobiMagnitudeTerm_pos hk hp m).le)

theorem semilocalOnePrimeEvenJacobiMagnitudeSeries_upper_at
    {k p M : ℕ} (hk : 0 < k) (hp : p.Prime) :
    semilocalOnePrimeEvenJacobiMagnitudeSeries k p ≤
      2 * semilocalArchimedeanJacobiNormalization (2 * k) *
        ((p : ℝ) ^ M / k + ((p : ℝ) ^ M)⁻¹) := by
  let c := semilocalArchimedeanJacobiNormalization (2 * k)
  have hc0 : 0 ≤ c := (semilocalArchimedeanJacobiNormalization_pos _).le
  have hs := summable_semilocalOnePrimeEvenJacobiMagnitudeTerm (k := k) hp
  have hsplit := hs.sum_add_tsum_nat_add M
  have hfinite :
      (∑ m ∈ Finset.range M,
          semilocalOnePrimeEvenJacobiMagnitudeTerm k p m) ≤
        2 * c * ((p : ℝ) ^ M / k) := by
    calc
      (∑ m ∈ Finset.range M,
          semilocalOnePrimeEvenJacobiMagnitudeTerm k p m) ≤
          ∑ m ∈ Finset.range M, c * ((p : ℝ) ^ (m + 1) / k) := by
        apply Finset.sum_le_sum
        intro m hm
        exact semilocalOnePrimeEvenJacobiMagnitudeTerm_le_low hk hp m
      _ = (c / k) *
          (∑ m ∈ Finset.range M, (p : ℝ) ^ (m + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ ≤ (c / k) * (2 * (p : ℝ) ^ M) := by
        exact mul_le_mul_of_nonneg_left
          (sum_range_prime_pow_succ_le hp.two_le) (by positivity)
      _ = 2 * c * ((p : ℝ) ^ M / k) := by ring
  have htailLeft : Summable (fun j : ℕ =>
      semilocalOnePrimeEvenJacobiMagnitudeTerm k p (j + M)) :=
    (summable_nat_add_iff M).2 hs
  have htailRight : Summable (fun j : ℕ =>
      c * (2 * ((p : ℝ) ^ (M + j + 1))⁻¹)) := by
    apply (summable_two_mul_prime_inv_pow_add hp.one_lt).mul_left c |>.congr
    intro j
    congr 2
  have htail :
      (∑' j : ℕ, semilocalOnePrimeEvenJacobiMagnitudeTerm k p (j + M)) ≤
        2 * c * ((p : ℝ) ^ M)⁻¹ := by
    calc
      (∑' j : ℕ, semilocalOnePrimeEvenJacobiMagnitudeTerm k p (j + M)) ≤
          ∑' j : ℕ, c * (2 * ((p : ℝ) ^ (M + j + 1))⁻¹) := by
        exact Summable.tsum_le_tsum (fun j => by
          simpa [add_comm, add_left_comm, add_assoc] using
            semilocalOnePrimeEvenJacobiMagnitudeTerm_le_tail
              (k := k) hp (j + M))
          htailLeft htailRight
      _ = c * (∑' j : ℕ, 2 * ((p : ℝ) ^ (M + j + 1))⁻¹) :=
        tsum_mul_left
      _ ≤ c * (2 * ((p : ℝ) ^ M)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (tsum_two_mul_prime_inv_pow_add_le hp.two_le) hc0
      _ = 2 * c * ((p : ℝ) ^ M)⁻¹ := by ring
  unfold semilocalOnePrimeEvenJacobiMagnitudeSeries
  rw [← hsplit]
  calc
    (∑ m ∈ Finset.range M,
        semilocalOnePrimeEvenJacobiMagnitudeTerm k p m) +
        ∑' j : ℕ, semilocalOnePrimeEvenJacobiMagnitudeTerm k p (j + M) ≤
      2 * c * ((p : ℝ) ^ M / k) + 2 * c * ((p : ℝ) ^ M)⁻¹ :=
        add_le_add hfinite htail
    _ = 2 * c * ((p : ℝ) ^ M / k + ((p : ℝ) ^ M)⁻¹) := by ring

theorem matched_inverse_pow_four_lower
    {k p M : ℕ} (hk : 0 < k) (hp : p.Prime)
    (hupper : (p : ℝ) ^ (2 * M) ≤ 8 * p ^ 2 * k) :
    (64 * (p : ℝ) ^ 4 * k ^ 2)⁻¹ ≤ (((p : ℝ) ^ M) ^ 4)⁻¹ := by
  let x : ℝ := (p : ℝ) ^ M
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hx : 0 < x := by dsimp [x]; exact pow_pos hpR _
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hx2 : x ^ 2 ≤ 8 * (p : ℝ) ^ 2 * k := by
    dsimp [x]
    rw [show 2 * M = M * 2 by omega, pow_mul] at hupper
    exact hupper
  have hx4 : x ^ 4 ≤ 64 * (p : ℝ) ^ 4 * k ^ 2 := by
    have hsquare := pow_le_pow_left₀ (sq_nonneg x) hx2 2
    nlinarith [hsquare]
  exact (inv_le_inv₀ (by positivity) (by positivity)).2 hx4

theorem matched_bracket_sq_upper
    {k p M : ℕ} (hk : 0 < k) (hp : p.Prime)
    (hlower : (8 * k : ℝ) < (p : ℝ) ^ (2 * M))
    (hupper : (p : ℝ) ^ (2 * M) ≤ 8 * p ^ 2 * k) :
    ((p : ℝ) ^ M / k + ((p : ℝ) ^ M)⁻¹) ^ 2 ≤
      18 * (p : ℝ) ^ 2 / k := by
  let x : ℝ := (p : ℝ) ^ M
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hx : 0 < x := by dsimp [x]; exact pow_pos hpR _
  have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hxLower : (8 * k : ℝ) < x ^ 2 := by
    dsimp [x]
    rw [show 2 * M = M * 2 by omega, pow_mul] at hlower
    exact hlower
  have hxUpper : x ^ 2 ≤ 8 * (p : ℝ) ^ 2 * k := by
    dsimp [x]
    rw [show 2 * M = M * 2 by omega, pow_mul] at hupper
    exact hupper
  have hkx : (k : ℝ) ≤ x ^ 2 / 8 := by linarith
  have hsum : x ^ 2 + k ≤ (9 / 8 : ℝ) * x ^ 2 := by linarith
  have hsum0 : 0 ≤ x ^ 2 + k := by positivity
  have hsq : (x ^ 2 + k) ^ 2 ≤ ((9 / 8 : ℝ) * x ^ 2) ^ 2 :=
    pow_le_pow_left₀ hsum0 hsum 2
  have hmul : x ^ 4 ≤ 8 * (p : ℝ) ^ 2 * k * x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hxUpper (sq_nonneg x)]
  change (x / k + x⁻¹) ^ 2 ≤ 18 * (p : ℝ) ^ 2 / k
  have hre : (x / k + x⁻¹) ^ 2 =
      (x ^ 2 + k) ^ 2 / (k ^ 2 * x ^ 2) := by
    field_simp
  rw [hre, div_le_iff₀ (mul_pos (sq_pos_of_pos hkR) (sq_pos_of_pos hx))]
  field_simp
  nlinarith [hsq, hmul]

theorem semilocalOnePrimeEvenJacobiMagnitudeSeries_pow_four_bounds
    {k p : ℕ} (hk : 0 < k) (hp : p.Prime) :
    (12288 * (p : ℝ) ^ 4 * k ^ 3)⁻¹ ≤
        semilocalOnePrimeEvenJacobiMagnitudeSeries k p ^ 4 ∧
      semilocalOnePrimeEvenJacobiMagnitudeSeries k p ^ 4 ≤
        2592 * (p : ℝ) ^ 4 / k ^ 3 := by
  obtain ⟨M, hM, hlower, hupper⟩ :=
    exists_semilocalOnePrimeMatchedDilation hk hp
  let x : ℝ := (p : ℝ) ^ M
  let c : ℝ := semilocalArchimedeanJacobiNormalization (2 * k)
  let S : ℝ := semilocalOnePrimeEvenJacobiMagnitudeSeries k p
  let b : ℝ := x / k + x⁻¹
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : 0 < x := by dsimp [x]; exact pow_pos hpR _
  have hc : 0 < c := by
    dsimp [c]
    exact semilocalArchimedeanJacobiNormalization_pos _
  have hS : 0 < S := by
    dsimp [S]
    exact semilocalOnePrimeEvenJacobiMagnitudeSeries_pos hk hp
  have hb : 0 < b := by dsimp [b]; positivity
  have hc4bounds :=
    semilocalArchimedeanJacobiNormalization_pow_four_bounds
      (n := 2 * k) (by omega)
  have hc4Lower : (12 * (k : ℝ))⁻¹ ≤ c ^ 4 := by
    dsimp [c]
    convert hc4bounds.1 using 1
    norm_num
    ring
  have hc4Upper : c ^ 4 ≤ (2 * (k : ℝ))⁻¹ := by
    dsimp [c]
    convert hc4bounds.2 using 1
    norm_num
  have hxinv := matched_inverse_pow_four_lower hk hp hupper
  change (64 * (p : ℝ) ^ 4 * k ^ 2)⁻¹ ≤ (x ^ 4)⁻¹ at hxinv
  have hseriesLower : c * (2 * x)⁻¹ ≤ S := by
    dsimp [c, x, S]
    exact semilocalOnePrimeEvenJacobiMagnitudeSeries_lower_of_matched
      hk hp hM hlower
  have hbaseLower :
      (12288 * (p : ℝ) ^ 4 * k ^ 3)⁻¹ ≤
        (c * (2 * x)⁻¹) ^ 4 := by
    have hmul :
        (12 * (k : ℝ))⁻¹ * (64 * (p : ℝ) ^ 4 * k ^ 2)⁻¹ ≤
          c ^ 4 * (x ^ 4)⁻¹ :=
      mul_le_mul hc4Lower hxinv (by positivity) (by positivity)
    convert mul_le_mul_of_nonneg_left hmul (show (0 : ℝ) ≤ 1 / 16 by norm_num) using 1 <;>
      field_simp <;> ring
  have hseriesUpper : S ≤ 2 * c * b := by
    dsimp [S, c, b, x]
    exact semilocalOnePrimeEvenJacobiMagnitudeSeries_upper_at hk hp
  have hb2 := matched_bracket_sq_upper hk hp hlower hupper
  change b ^ 2 ≤ 18 * (p : ℝ) ^ 2 / k at hb2
  have hb4 : b ^ 4 ≤ (18 * (p : ℝ) ^ 2 / k) ^ 2 := by
    have := pow_le_pow_left₀ (sq_nonneg b) hb2 2
    nlinarith [this]
  have hbaseUpper :
      (2 * c * b) ^ 4 ≤ 2592 * (p : ℝ) ^ 4 / k ^ 3 := by
    have hmul : c ^ 4 * b ^ 4 ≤
        (2 * (k : ℝ))⁻¹ * (18 * (p : ℝ) ^ 2 / k) ^ 2 :=
      mul_le_mul hc4Upper hb4 (pow_nonneg hb.le 4) (by positivity)
    calc
      (2 * c * b) ^ 4 = 16 * (c ^ 4 * b ^ 4) := by ring
      _ ≤ 16 * ((2 * (k : ℝ))⁻¹ *
          (18 * (p : ℝ) ^ 2 / k) ^ 2) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 2592 * (p : ℝ) ^ 4 / k ^ 3 := by
        field_simp
        ring
  constructor
  · exact hbaseLower.trans
      (pow_le_pow_left₀ (by positivity) hseriesLower 4)
  · exact (pow_le_pow_left₀ hS.le hseriesUpper 4).trans hbaseUpper

theorem semilocalOnePrimePoissonCoefficientPrefactor_bounds
    {p : ℕ} (hp : p.Prime) :
    (2 : ℝ) ≤ 2 * (1 - semilocalPrimePoissonRatio p ^ 2)⁻¹ ∧
      2 * (1 - semilocalPrimePoissonRatio p ^ 2)⁻¹ ≤ 4 := by
  have hr2 := semilocalPrimePoissonRatio_sq hp
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa [one_div] using
      (inv_le_inv₀ hp0 (by norm_num : (0 : ℝ) < 2)).2 hpR
  have hden0 : 0 < 1 - semilocalPrimePoissonRatio p ^ 2 := by
    rw [hr2]
    exact sub_pos.mpr (hinv.trans_lt (by norm_num))
  constructor
  · rw [le_mul_inv_iff₀ hden0]
    have hr20 : 0 ≤ semilocalPrimePoissonRatio p ^ 2 := sq_nonneg _
    nlinarith
  · rw [mul_inv_le_iff₀ hden0]
    rw [hr2]
    nlinarith

/-- Sharp fourth-power form of the card's `k^(-3/4)` Euler coefficient estimate. -/
theorem abs_semilocalOnePrimeEvenJacobiCoefficient_pow_four_bounds
    {k p : ℕ} (hk : 0 < k) (hp : p.Prime) :
    (768 * (p : ℝ) ^ 4 * k ^ 3)⁻¹ ≤
        |semilocalOnePrimeEvenJacobiCoefficient k p| ^ 4 ∧
      |semilocalOnePrimeEvenJacobiCoefficient k p| ^ 4 ≤
        663552 * (p : ℝ) ^ 4 / k ^ 3 := by
  let P : ℝ := 2 * (1 - semilocalPrimePoissonRatio p ^ 2)⁻¹
  let S : ℝ := semilocalOnePrimeEvenJacobiMagnitudeSeries k p
  have hP := semilocalOnePrimePoissonCoefficientPrefactor_bounds hp
  have hP0 : 0 ≤ P := (by norm_num : (0 : ℝ) ≤ 2).trans hP.1
  have hS := semilocalOnePrimeEvenJacobiMagnitudeSeries_pow_four_bounds hk hp
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact (semilocalOnePrimeEvenJacobiMagnitudeSeries_pos hk hp).le
  have hcoeff : |semilocalOnePrimeEvenJacobiCoefficient k p| = P * S := by
    dsimp [P, S]
    exact abs_semilocalOnePrimeEvenJacobiCoefficient_eq_magnitudeSeries hk hp
  rw [hcoeff, mul_pow]
  constructor
  · calc
      (768 * (p : ℝ) ^ 4 * k ^ 3)⁻¹ =
          16 * (12288 * (p : ℝ) ^ 4 * k ^ 3)⁻¹ := by
        field_simp
        ring
      _ ≤ 2 ^ 4 * S ^ 4 :=
        mul_le_mul (by norm_num : (16 : ℝ) ≤ 2 ^ 4) hS.1
          (by positivity) (by norm_num)
      _ ≤ P ^ 4 * S ^ 4 :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by norm_num) hP.1 4) (pow_nonneg hS0 4)
  · calc
      P ^ 4 * S ^ 4 ≤ 4 ^ 4 *
          (2592 * (p : ℝ) ^ 4 / k ^ 3) :=
        mul_le_mul (pow_le_pow_left₀ hP0 hP.2 4) hS.2
          (pow_nonneg hS0 4) (by norm_num)
      _ = 663552 * (p : ℝ) ^ 4 / k ^ 3 := by ring

theorem rpow_neg_three_quarters_pow_four
    {x : ℝ} (hx : 0 < x) :
    (x ^ (-3 / 4 : ℝ)) ^ 4 = (x ^ 3)⁻¹ := by
  rw [← Real.rpow_mul_natCast hx.le]
  norm_num
  rfl

/-- Literal `k^(-3/4)` version of the sharp one-prime coefficient estimate. -/
theorem abs_semilocalOnePrimeEvenJacobiCoefficient_sharp_order
    {p : ℕ} (hp : p.Prime) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ k : ℕ, 0 < k →
        c * (k : ℝ) ^ (-3 / 4 : ℝ) ≤
            |semilocalOnePrimeEvenJacobiCoefficient k p| ∧
          |semilocalOnePrimeEvenJacobiCoefficient k p| ≤
            C * (k : ℝ) ^ (-3 / 4 : ℝ) := by
  let A : ℝ := (768 * (p : ℝ) ^ 4)⁻¹
  let B : ℝ := 663552 * (p : ℝ) ^ 4
  let c : ℝ := A ^ (1 / 4 : ℝ)
  let C : ℝ := B ^ (1 / 4 : ℝ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hc : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos hA _
  have hC : 0 < C := by
    dsimp [C]
    exact Real.rpow_pos_of_pos hB _
  have hAB : A ≤ B := by
    dsimp [A, B]
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hp4 : (1 : ℝ) ≤ (p : ℝ) ^ 4 := one_le_pow₀ hp1
    have hleft : A ≤ 1 := by
      dsimp [A]
      rw [inv_le_one₀ (by positivity)]
      nlinarith
    have hright : (1 : ℝ) ≤ B := by
      dsimp [B]
      nlinarith
    exact hleft.trans hright
  have hcC : c ≤ C := by
    dsimp [c, C]
    exact Real.rpow_le_rpow hA.le hAB (by norm_num)
  refine ⟨c, C, hc, hcC, ?_⟩
  intro k hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpow := abs_semilocalOnePrimeEvenJacobiCoefficient_pow_four_bounds hk hp
  let y : ℝ := |semilocalOnePrimeEvenJacobiCoefficient k p|
  let L : ℝ := c * (k : ℝ) ^ (-3 / 4 : ℝ)
  let U : ℝ := C * (k : ℝ) ^ (-3 / 4 : ℝ)
  have hy0 : 0 ≤ y := by dsimp [y]; exact abs_nonneg _
  have hkr : 0 < (k : ℝ) ^ (-3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos hkR _
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hc4 : c ^ 4 = A := by
    dsimp [c]
    simpa [one_div] using
      Real.rpow_inv_natCast_pow hA.le (by norm_num : (4 : ℕ) ≠ 0)
  have hC4 : C ^ 4 = B := by
    dsimp [C]
    simpa [one_div] using
      Real.rpow_inv_natCast_pow hB.le (by norm_num : (4 : ℕ) ≠ 0)
  have hk4 := rpow_neg_three_quarters_pow_four hkR
  have hL4 : L ^ 4 = (768 * (p : ℝ) ^ 4 * k ^ 3)⁻¹ := by
    dsimp [L]
    rw [mul_pow, hc4, hk4]
    dsimp [A]
    field_simp
  have hU4 : U ^ 4 = 663552 * (p : ℝ) ^ 4 / k ^ 3 := by
    dsimp [U]
    rw [mul_pow, hC4, hk4]
    dsimp [B]
    field_simp
  change L ≤ y ∧ y ≤ U
  constructor
  · apply (pow_le_pow_iff_left₀ hL0 hy0 (by norm_num : (4 : ℕ) ≠ 0)).mp
    rw [hL4]
    exact hpow.1
  · apply (pow_le_pow_iff_left₀ hy0 hU0 (by norm_num : (4 : ℕ) ≠ 0)).mp
    rw [hU4]
    exact hpow.2

def semilocalOnePrimeGroundCommutatorRow (p k : ℕ) : ℝ :=
  (2 * k : ℝ) * semilocalOnePrimeEvenJacobiCoefficient k p

theorem natCast_mul_rpow_neg_three_quarters
    {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * (k : ℝ) ^ (-3 / 4 : ℝ) =
      (k : ℝ) ^ (1 / 4 : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    (k : ℝ) * (k : ℝ) ^ (-3 / 4 : ℝ) =
        (k : ℝ) ^ (1 : ℝ) * (k : ℝ) ^ (-3 / 4 : ℝ) := by
      rw [Real.rpow_one]
    _ = (k : ℝ) ^ ((1 : ℝ) + (-3 / 4 : ℝ)) :=
      (Real.rpow_add hkR _ _).symm
    _ = (k : ℝ) ^ (1 / 4 : ℝ) := by norm_num

/-- Card equation (1): the commutator ground row has sharp order `k^(1/4)`. -/
theorem abs_semilocalOnePrimeGroundCommutatorRow_sharp_order
    {p : ℕ} (hp : p.Prime) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ k : ℕ, 0 < k →
        c * (k : ℝ) ^ (1 / 4 : ℝ) ≤
            |semilocalOnePrimeGroundCommutatorRow p k| ∧
          |semilocalOnePrimeGroundCommutatorRow p k| ≤
            C * (k : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨c, C, hc, hcC, hcoeff⟩ :=
    abs_semilocalOnePrimeEvenJacobiCoefficient_sharp_order hp
  refine ⟨2 * c, 2 * C, by positivity,
    mul_le_mul_of_nonneg_left hcC (by norm_num), ?_⟩
  intro k hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have habs : |semilocalOnePrimeGroundCommutatorRow p k| =
      2 * (k : ℝ) * |semilocalOnePrimeEvenJacobiCoefficient k p| := by
    unfold semilocalOnePrimeGroundCommutatorRow
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ))]
  have hkpow := natCast_mul_rpow_neg_three_quarters hk
  rw [habs]
  constructor
  · calc
      2 * c * (k : ℝ) ^ (1 / 4 : ℝ) =
          2 * (k : ℝ) * (c * (k : ℝ) ^ (-3 / 4 : ℝ)) := by
        rw [← hkpow]
        ring
      _ ≤ 2 * (k : ℝ) * |semilocalOnePrimeEvenJacobiCoefficient k p| :=
        mul_le_mul_of_nonneg_left (hcoeff k hk).1 (by positivity)
  · calc
      2 * (k : ℝ) * |semilocalOnePrimeEvenJacobiCoefficient k p| ≤
          2 * (k : ℝ) * (C * (k : ℝ) ^ (-3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hcoeff k hk).2 (by positivity)
      _ = 2 * C * (k : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← hkpow]
        ring

/-- The actual one-prime commutator row is not uniformly bounded. -/
theorem semilocalOnePrimeGroundCommutatorRow_unbounded
    {p : ℕ} (hp : p.Prime) :
    ∀ B : ℝ, ∃ k : ℕ, 0 < k ∧
      B < |semilocalOnePrimeGroundCommutatorRow p k| := by
  obtain ⟨c, C, hc, hcC, hrow⟩ :=
    abs_semilocalOnePrimeGroundCommutatorRow_sharp_order hp
  have ht : Tendsto (fun k : ℕ => c * (k : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop |>.const_mul_atTop hc
  intro B
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp ht) (B + 1)
  let k := max N 1
  have hkN : N ≤ k := Nat.le_max_left _ _
  have hk : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _)
  refine ⟨k, hk, ?_⟩
  have hlower := (hrow k hk).1
  have hlarge := hN k hkN
  linarith

theorem summable_iff_of_positive_rpow_two_sided
    {f : ℕ → ℝ} {beta : ℝ}
    (hf0 : ∀ k, 0 ≤ f k)
    (horder : ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ k : ℕ, 0 < k →
        c * (k : ℝ) ^ beta ≤ f k ∧
          f k ≤ C * (k : ℝ) ^ beta) :
    Summable f ↔ beta < -1 := by
  obtain ⟨c, C, hc, hcC, hbound⟩ := horder
  constructor
  · intro hf
    have hfshift : Summable (fun n : ℕ => f (n + 1)) :=
      (summable_nat_add_iff 1).2 hf
    have hscaled : Summable (fun n : ℕ =>
        c * ((n + 1 : ℕ) : ℝ) ^ beta) :=
      Summable.of_nonneg_of_le (fun n => by positivity)
        (fun n => (hbound (n + 1) (by omega)).1) hfshift
    have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ beta) := by
      apply (hscaled.mul_left c⁻¹).congr
      intro n
      field_simp
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ beta) :=
      (summable_nat_add_iff 1).1 hshift
    exact Real.summable_nat_rpow.mp hbase
  · intro hbeta
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ beta) :=
      Real.summable_nat_rpow.mpr hbeta
    have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ beta) :=
      (summable_nat_add_iff 1).2 hbase
    have hmajor : Summable (fun n : ℕ =>
        C * ((n + 1 : ℕ) : ℝ) ^ beta) := hshift.mul_left C
    have hfshift : Summable (fun n : ℕ => f (n + 1)) :=
      Summable.of_nonneg_of_le (fun n => hf0 (n + 1))
        (fun n => (hbound (n + 1) (by omega)).2) hmajor
    exact (summable_nat_add_iff 1).1 hfshift

def semilocalOnePrimeGroundRowSmoothedSquare
    (p : ℕ) (alpha : ℝ) (k : ℕ) : ℝ :=
  (semilocalOnePrimeGroundCommutatorRow p k *
    ((2 * k + 1 : ℕ) : ℝ) ^ (-alpha)) ^ 2

theorem rpow_one_quarter_pow_two
    {x : ℝ} (hx : 0 < x) :
    (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
  rw [← Real.rpow_mul_natCast hx.le]
  norm_num

theorem rpow_neg_alpha_pow_two
    {x : ℝ} (hx : 0 < x) (alpha : ℝ) :
    (x ^ (-alpha)) ^ 2 = x ^ (-2 * alpha) := by
  rw [← Real.rpow_mul_natCast hx.le]
  congr 1
  ring

theorem rpow_half_mul_rpow_neg_two
    {x : ℝ} (hx : 0 < x) (alpha : ℝ) :
    x ^ (1 / 2 : ℝ) * x ^ (-2 * alpha) =
      x ^ (1 / 2 - 2 * alpha) := by
  rw [← Real.rpow_add hx]
  congr 1
  ring

theorem semilocalOnePrimeGroundRowSmoothedSquare_sharp_order
    {p : ℕ} (hp : p.Prime) (alpha : ℝ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ k : ℕ, 0 < k →
        c * (k : ℝ) ^ (1 / 2 - 2 * alpha) ≤
            semilocalOnePrimeGroundRowSmoothedSquare p alpha k ∧
          semilocalOnePrimeGroundRowSmoothedSquare p alpha k ≤
            C * (k : ℝ) ^ (1 / 2 - 2 * alpha) := by
  obtain ⟨c, C, hc, hcC, hrow⟩ :=
    abs_semilocalOnePrimeGroundCommutatorRow_sharp_order hp
  let z : ℝ := -2 * alpha
  have assemble : ∀ d D : ℝ, 0 < d → d ≤ D →
      (∀ k : ℕ, 0 < k →
        d * (k : ℝ) ^ z ≤ ((2 * k + 1 : ℕ) : ℝ) ^ z ∧
          ((2 * k + 1 : ℕ) : ℝ) ^ z ≤ D * (k : ℝ) ^ z) →
      ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
        ∀ k : ℕ, 0 < k →
          a * (k : ℝ) ^ (1 / 2 + z) ≤
              semilocalOnePrimeGroundRowSmoothedSquare p alpha k ∧
            semilocalOnePrimeGroundRowSmoothedSquare p alpha k ≤
              b * (k : ℝ) ^ (1 / 2 + z) := by
    intro d D hd hdD hweight
    refine ⟨c ^ 2 * d, C ^ 2 * D, by positivity, ?_, ?_⟩
    · exact mul_le_mul (pow_le_pow_left₀ hc.le hcC 2) hdD
        (by positivity) (by positivity)
    · intro k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hbase : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
      have hr := hrow k hk
      have hrLower :
          (c * (k : ℝ) ^ (1 / 4 : ℝ)) ^ 2 ≤
            |semilocalOnePrimeGroundCommutatorRow p k| ^ 2 :=
        pow_le_pow_left₀ (by positivity) hr.1 2
      have hrUpper :
          |semilocalOnePrimeGroundCommutatorRow p k| ^ 2 ≤
            (C * (k : ℝ) ^ (1 / 4 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hr.2 2
      have hw := hweight k hk
      have heq : semilocalOnePrimeGroundRowSmoothedSquare p alpha k =
          |semilocalOnePrimeGroundCommutatorRow p k| ^ 2 *
            ((2 * k + 1 : ℕ) : ℝ) ^ z := by
        unfold semilocalOnePrimeGroundRowSmoothedSquare
        rw [mul_pow, sq_abs, rpow_neg_alpha_pow_two hbase]
      rw [heq]
      constructor
      · calc
          c ^ 2 * d * (k : ℝ) ^ (1 / 2 + z) =
              (c * (k : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
                (d * (k : ℝ) ^ z) := by
            rw [mul_pow, rpow_one_quarter_pow_two hkR,
              Real.rpow_add hkR]
            ring
          _ ≤ |semilocalOnePrimeGroundCommutatorRow p k| ^ 2 *
                ((2 * k + 1 : ℕ) : ℝ) ^ z :=
            mul_le_mul hrLower hw.1 (by positivity) (sq_nonneg _)
      · calc
          |semilocalOnePrimeGroundCommutatorRow p k| ^ 2 *
                ((2 * k + 1 : ℕ) : ℝ) ^ z ≤
              (C * (k : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
                (D * (k : ℝ) ^ z) :=
            mul_le_mul hrUpper hw.2 (by positivity) (by positivity)
          _ = C ^ 2 * D * (k : ℝ) ^ (1 / 2 + z) := by
            rw [mul_pow, rpow_one_quarter_pow_two hkR,
              Real.rpow_add hkR]
            ring
  by_cases halpha : alpha ≤ 0
  · have hz0 : 0 ≤ z := by dsimp [z]; linarith
    have hD : 0 < (3 : ℝ) ^ z := Real.rpow_pos_of_pos (by norm_num) _
    have h1D : (1 : ℝ) ≤ 3 ^ z := by
      rw [← Real.one_rpow z]
      exact Real.rpow_le_rpow (by norm_num) (by norm_num) hz0
    obtain ⟨a, b, ha, hab, hb⟩ := assemble 1 (3 ^ z) zero_lt_one h1D (by
      intro k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hlow : (k : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show k ≤ 2 * k + 1 by omega)
      have hupp : ((2 * k + 1 : ℕ) : ℝ) ≤ 3 * (k : ℝ) := by
        exact_mod_cast (show 2 * k + 1 ≤ 3 * k by omega)
      constructor
      · simpa using Real.rpow_le_rpow hkR.le hlow hz0
      · calc
          ((2 * k + 1 : ℕ) : ℝ) ^ z ≤ (3 * (k : ℝ)) ^ z :=
            Real.rpow_le_rpow (by positivity) hupp hz0
          _ = 3 ^ z * (k : ℝ) ^ z := Real.mul_rpow (by norm_num) hkR.le)
    refine ⟨a, b, ha, hab, ?_⟩
    simpa [z, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hb
  · have hz0 : z ≤ 0 := by dsimp [z]; linarith
    have hd : 0 < (3 : ℝ) ^ z := Real.rpow_pos_of_pos (by norm_num) _
    have hd1 : (3 : ℝ) ^ z ≤ 1 := by
      rw [← Real.one_rpow z]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) hz0
    obtain ⟨a, b, ha, hab, hb⟩ := assemble (3 ^ z) 1 hd hd1 (by
      intro k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hlow : (k : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show k ≤ 2 * k + 1 by omega)
      have hupp : ((2 * k + 1 : ℕ) : ℝ) ≤ 3 * (k : ℝ) := by
        exact_mod_cast (show 2 * k + 1 ≤ 3 * k by omega)
      constructor
      · calc
          3 ^ z * (k : ℝ) ^ z = (3 * (k : ℝ)) ^ z :=
            (Real.mul_rpow (by norm_num) hkR.le).symm
          _ ≤ ((2 * k + 1 : ℕ) : ℝ) ^ z :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hupp hz0
      · simpa using Real.rpow_le_rpow_of_nonpos hkR hlow hz0)
    refine ⟨a, b, ha, hab, ?_⟩
    simpa [z, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hb

/-- Card equation (2): exact `alpha = 3/4` ground-row smoothing threshold. -/
theorem summable_semilocalOnePrimeGroundRowSmoothedSquare_iff
    {p : ℕ} (hp : p.Prime) (alpha : ℝ) :
    Summable (semilocalOnePrimeGroundRowSmoothedSquare p alpha) ↔
      3 / 4 < alpha := by
  rw [summable_iff_of_positive_rpow_two_sided
    (f := semilocalOnePrimeGroundRowSmoothedSquare p alpha)
    (beta := 1 / 2 - 2 * alpha)
    (fun k => sq_nonneg _)
    (semilocalOnePrimeGroundRowSmoothedSquare_sharp_order hp alpha)]
  constructor <;> intro h <;> linarith

/-! ### Transported ground-state quarter-derivative threshold -/

/-- Squared Jacobi coefficients of the transported semilocal ground state after applying the
spectral weight `(N∞ + 1)^alpha`. -/
def semilocalOnePrimeTransportedGroundDomainSquare
    (p : ℕ) (alpha : ℝ) (k : ℕ) : ℝ :=
  (semilocalOnePrimeEvenJacobiCoefficient k p *
    ((2 * k + 1 : ℕ) : ℝ) ^ alpha) ^ 2

/-- Away from the harmless zeroth coefficient, the transported ground-state domain summand is
uniformly comparable with the already-controlled commutator-row smoothing at exponent
`1 - alpha`. -/
theorem semilocalOnePrimeGroundDomainSquare_comparable
    (p : ℕ) (alpha : ℝ) {k : ℕ} (hk : 0 < k) :
    semilocalOnePrimeGroundRowSmoothedSquare p (1 - alpha) k ≤
        semilocalOnePrimeTransportedGroundDomainSquare p alpha k ∧
      semilocalOnePrimeTransportedGroundDomainSquare p alpha k ≤
        (9 / 4 : ℝ) *
          semilocalOnePrimeGroundRowSmoothedSquare p (1 - alpha) k := by
  let w : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  let r : ℝ := (2 * (k : ℝ)) / w
  let T : ℝ := semilocalOnePrimeTransportedGroundDomainSquare p alpha k
  let S : ℝ := semilocalOnePrimeGroundRowSmoothedSquare p (1 - alpha) k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hw : 0 < w := by dsimp [w]; positivity
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrUpper : r ≤ 1 := by
    dsimp [r, w]
    rw [div_le_one (by positivity)]
    push_cast
    linarith
  have hrLower : (2 / 3 : ℝ) ≤ r := by
    dsimp [r, w]
    rw [le_div_iff₀ (by positivity)]
    have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    nlinarith
  have hT0 : 0 ≤ T := by dsimp [T, semilocalOnePrimeTransportedGroundDomainSquare]; positivity
  have hrelation : S = r ^ 2 * T := by
    dsimp [S, r, T, w]
    unfold semilocalOnePrimeGroundRowSmoothedSquare
      semilocalOnePrimeTransportedGroundDomainSquare
      semilocalOnePrimeGroundCommutatorRow
    rw [show -(1 - alpha) = alpha - 1 by ring,
      Real.rpow_sub hw alpha 1, Real.rpow_one]
    field_simp
    ring
  have hrSqUpper : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg r]
  have hrSqLower : (4 / 9 : ℝ) ≤ r ^ 2 := by
    nlinarith [sq_nonneg (r - 2 / 3)]
  constructor
  · change S ≤ T
    rw [hrelation]
    simpa using mul_le_mul_of_nonneg_right hrSqUpper hT0
  · change T ≤ (9 / 4 : ℝ) * S
    have hscaled : (4 / 9 : ℝ) * T ≤ S := by
      rw [hrelation]
      exact mul_le_mul_of_nonneg_right hrSqLower hT0
    nlinarith

/-- **Sharp quarter-derivative law.**  The transported semilocal ground state belongs to the
`(N∞ + 1)^alpha` Jacobi domain exactly below `alpha = 1/4`. -/
theorem summable_semilocalOnePrimeTransportedGroundDomainSquare_iff
    {p : ℕ} (hp : p.Prime) (alpha : ℝ) :
    Summable (semilocalOnePrimeTransportedGroundDomainSquare p alpha) ↔
      alpha < 1 / 4 := by
  constructor
  · intro hT
    have hTshift : Summable (fun n : ℕ =>
        semilocalOnePrimeTransportedGroundDomainSquare p alpha (n + 1)) :=
      (summable_nat_add_iff 1).2 hT
    have hSshift : Summable (fun n : ℕ =>
        semilocalOnePrimeGroundRowSmoothedSquare p (1 - alpha) (n + 1)) :=
      Summable.of_nonneg_of_le (fun n => sq_nonneg _)
        (fun n => (semilocalOnePrimeGroundDomainSquare_comparable
          p alpha (by omega : 0 < n + 1)).1) hTshift
    have hS : Summable (semilocalOnePrimeGroundRowSmoothedSquare p (1 - alpha)) :=
      (summable_nat_add_iff 1).1 hSshift
    have hthreshold :=
      (summable_semilocalOnePrimeGroundRowSmoothedSquare_iff hp (1 - alpha)).1 hS
    linarith
  · intro halpha
    have hS : Summable (semilocalOnePrimeGroundRowSmoothedSquare p (1 - alpha)) :=
      (summable_semilocalOnePrimeGroundRowSmoothedSquare_iff hp (1 - alpha)).2 (by
        linarith)
    have hSshift : Summable (fun n : ℕ =>
        semilocalOnePrimeGroundRowSmoothedSquare p (1 - alpha) (n + 1)) :=
      (summable_nat_add_iff 1).2 hS
    have hmajor : Summable (fun n : ℕ =>
        (9 / 4 : ℝ) *
          semilocalOnePrimeGroundRowSmoothedSquare p (1 - alpha) (n + 1)) :=
      hSshift.mul_left (9 / 4 : ℝ)
    have hTshift : Summable (fun n : ℕ =>
        semilocalOnePrimeTransportedGroundDomainSquare p alpha (n + 1)) :=
      Summable.of_nonneg_of_le (fun n => sq_nonneg _)
        (fun n => (semilocalOnePrimeGroundDomainSquare_comparable
          p alpha (by omega : 0 < n + 1)).2) hmajor
    exact (summable_nat_add_iff 1).1 hTshift

/-! ### Semilocal polynomial-core disjointness -/

/-- The Mellin character has the Euler period `2π / log p`. -/
theorem mellinCharacter_add_eulerPeriod
    (p s : ℝ) (hp : 1 < p) :
    MellinL2.mellinCharacter p (s + 2 * Real.pi / Real.log p) =
      MellinL2.mellinCharacter p s := by
  have hlog : Real.log p ≠ 0 := ne_of_gt (Real.log_pos hp)
  unfold MellinL2.mellinCharacter
  rw [show Real.log p * (s + 2 * Real.pi / Real.log p) =
      Real.log p * s + 2 * Real.pi by field_simp]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The positive one-prime Euler metric is periodic in the spectral coordinate. -/
theorem semilocalPrimeWeight_periodic
    (p : ℝ) (hp : 1 < p) :
    Function.Periodic (fun s : ℝ => semilocalPrimeWeight p s)
      (2 * Real.pi / Real.log p) := by
  intro s
  change semilocalPrimeWeight p (s + 2 * Real.pi / Real.log p) =
    semilocalPrimeWeight p s
  rw [semilocalPrimeWeight_eq_symbol_sq, semilocalPrimeWeight_eq_symbol_sq]
  congr 2
  unfold semilocalPrimeSymbol
  rw [mellinCharacter_add_eulerPeriod p s hp]

@[simp]
theorem mellinCharacter_zero (p : ℝ) :
    MellinL2.mellinCharacter p 0 = 1 := by
  simp [MellinL2.mellinCharacter]

/-- At the half-period the Mellin character changes sign. -/
theorem mellinCharacter_half_eulerPeriod
    (p : ℝ) (hp : 1 < p) :
    MellinL2.mellinCharacter p (Real.pi / Real.log p) = -1 := by
  have hlog : Real.log p ≠ 0 := ne_of_gt (Real.log_pos hp)
  unfold MellinL2.mellinCharacter
  rw [show Real.log p * (Real.pi / Real.log p) = Real.pi by field_simp]
  exact Complex.exp_pi_mul_I

/-- The one-prime Euler metric is genuinely nonconstant: its half-period and zero values differ. -/
theorem semilocalPrimeWeight_halfPeriod_ne_zero
    (p : ℝ) (hp : 1 < p) :
    semilocalPrimeWeight p (Real.pi / Real.log p) ≠
      semilocalPrimeWeight p 0 := by
  rw [semilocalPrimeWeight_eq_symbol_sq, semilocalPrimeWeight_eq_symbol_sq]
  unfold semilocalPrimeSymbol
  rw [mellinCharacter_half_eulerPeriod p hp, mellinCharacter_zero]
  simp only [inv_neg, inv_one, mul_neg, mul_one, sub_neg_eq_add]
  have hsqrt : 0 < (Real.sqrt p)⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.2 (zero_lt_one.trans hp))
  intro h
  have hreal := congrArg (fun x : NNReal => (x : ℝ)) h
  simp only [NNReal.coe_pow, coe_nnnorm] at hreal
  have hplus : (1 + ((Real.sqrt p : ℂ))⁻¹) =
      ((1 + (Real.sqrt p)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have hminus : (1 - ((Real.sqrt p : ℂ))⁻¹) =
      ((1 - (Real.sqrt p)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hplus, hminus, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by linarith : 0 < 1 + (Real.sqrt p)⁻¹),
    abs_of_pos (by
      have hlt := sqrt_inv_lt_one p hp
      linarith : 0 < 1 - (Real.sqrt p)⁻¹)] at hreal
  nlinarith

/-- **Polynomial-core disjointness, pointwise form.**  A polynomial cannot equal the nonconstant
periodic Euler metric times another polynomial unless both vanish. -/
theorem semilocalPrimeWeight_polynomial_core_disjoint
    (p : ℝ) (hp : 1 < p) (P Q : Polynomial ℂ)
    (h : ∀ s : ℝ, P.eval (s : ℂ) =
      (((semilocalPrimeWeight p s : NNReal) : ℝ) : ℂ) * Q.eval (s : ℂ)) :
    P = 0 ∧ Q = 0 := by
  let period : ℝ := 2 * Real.pi / Real.log p
  let halfPeriod : ℝ := Real.pi / Real.log p
  let c0 : ℂ := (((semilocalPrimeWeight p 0 : NNReal) : ℝ) : ℂ)
  have hperiod0 : period ≠ 0 := by
    dsimp [period]
    exact div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (ne_of_gt (Real.log_pos hp))
  have hperiodic :
      Function.Periodic (fun s : ℝ => semilocalPrimeWeight p s) period := by
    simpa [period] using semilocalPrimeWeight_periodic p hp
  let orbit : ℕ → ℂ := fun n => (((n : ℝ) * period : ℝ) : ℂ)
  have horbit : Function.Injective orbit := by
    intro m n hmn
    apply Nat.cast_injective (R := ℝ)
    apply mul_right_cancel₀ hperiod0
    simpa [orbit] using congrArg Complex.re hmn
  have hP : P = Polynomial.C c0 * Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective horbit).mono
    rintro z ⟨n, rfl⟩
    have hw := (hperiodic.nsmul n) 0
    have hsample := h ((n : ℝ) * period)
    simp only [zero_add, nsmul_eq_mul] at hw
    simpa [orbit, c0, Polynomial.eval_mul, hw] using hsample
  have hQzero : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    let halfOrbit : ℕ → ℂ := fun n =>
      (((halfPeriod + (n : ℝ) * period : ℝ)) : ℂ)
    have hhalfOrbit : Function.Injective halfOrbit := by
      intro m n hmn
      apply Nat.cast_injective (R := ℝ)
      apply mul_right_cancel₀ hperiod0
      have hre := congrArg Complex.re hmn
      dsimp [halfOrbit] at hre
      linarith
    apply (Set.infinite_range_of_injective hhalfOrbit).mono
    rintro z ⟨n, rfl⟩
    have hw0 := (hperiodic.nsmul n) halfPeriod
    have hsample := h (halfPeriod + (n : ℝ) * period)
    have hhalfNe : semilocalPrimeWeight p halfPeriod ≠
        semilocalPrimeWeight p 0 := by
      simpa [halfPeriod] using semilocalPrimeWeight_halfPeriod_ne_zero p hp
    have hcoeff :
        (((semilocalPrimeWeight p 0 : NNReal) : ℝ) : ℂ) -
          (((semilocalPrimeWeight p halfPeriod : NNReal) : ℝ) : ℂ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hhalfNe)
    simp only [nsmul_eq_mul] at hw0
    rw [hP, Polynomial.eval_mul, Polynomial.eval_C] at hsample
    have heq :
        ((((semilocalPrimeWeight p 0 : NNReal) : ℝ) : ℂ) -
          (((semilocalPrimeWeight p halfPeriod : NNReal) : ℝ) : ℂ)) *
            Q.eval (((halfPeriod + (n : ℝ) * period : ℝ)) : ℂ) = 0 := by
      rw [hw0] at hsample
      linear_combination hsample
    exact (mul_eq_zero.mp heq).resolve_left hcoeff
  exact ⟨by rw [hP, hQzero, mul_zero], hQzero⟩

/-- **Polynomial-core disjointness in the spectral `L²` sense.**  Equality almost everywhere
against the positive Euler metric already forces both polynomial representatives to vanish. -/
theorem semilocalPrimeWeight_polynomial_core_disjoint_ae
    (p : ℝ) (hp : 1 < p) (P Q : Polynomial ℂ)
    (h : (fun s : ℝ => P.eval (s : ℂ)) =ᵐ[MeasureTheory.volume]
      fun s : ℝ =>
        (((semilocalPrimeWeight p s : NNReal) : ℝ) : ℂ) * Q.eval (s : ℂ)) :
    P = 0 ∧ Q = 0 := by
  have hweightNN : Continuous fun s : ℝ => semilocalPrimeWeight p s := by
    unfold semilocalPrimeWeight
    exact (((primeEulerFactor_continuous p hp).nnnorm).inv₀
      (fun s => nnnorm_ne_zero_iff.mpr (primeEulerFactor_ne_zero p hp s))).pow 2
  have hweightC : Continuous fun s : ℝ =>
      (((semilocalPrimeWeight p s : NNReal) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hweightNN)
  have hpoint := (Continuous.ae_eq_iff_eq MeasureTheory.volume
    (P.continuous.comp Complex.continuous_ofReal)
    (hweightC.mul (Q.continuous.comp Complex.continuous_ofReal))).mp h
  exact semilocalPrimeWeight_polynomial_core_disjoint p hp P Q
    (fun s => congrFun hpoint s)

/-- The inverse Euler multiplier has the same trivial intersection with the polynomial core. -/
theorem semilocalPrimeWeight_inv_polynomial_core_disjoint_ae
    (p : ℝ) (hp : 1 < p) (P Q : Polynomial ℂ)
    (h : (fun s : ℝ => P.eval (s : ℂ)) =ᵐ[MeasureTheory.volume]
      fun s : ℝ =>
        ((((semilocalPrimeWeight p s : NNReal) : ℝ)⁻¹ : ℝ) : ℂ) *
          Q.eval (s : ℂ)) :
    P = 0 ∧ Q = 0 := by
  have hforward : (fun s : ℝ => Q.eval (s : ℂ)) =ᵐ[MeasureTheory.volume]
      fun s : ℝ =>
        (((semilocalPrimeWeight p s : NNReal) : ℝ) : ℂ) * P.eval (s : ℂ) := by
    filter_upwards [h] with s hs
    have hwNN : semilocalPrimeWeight p s ≠ 0 :=
      semilocalPrimeWeight_ne_zero p hp s
    have hwR : ((semilocalPrimeWeight p s : NNReal) : ℝ) ≠ 0 := by
      exact_mod_cast hwNN
    have hwC : ((((semilocalPrimeWeight p s : NNReal) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast hwR
    calc
      Q.eval (s : ℂ) =
          (((semilocalPrimeWeight p s : NNReal) : ℝ) : ℂ) *
            (((((semilocalPrimeWeight p s : NNReal) : ℝ)⁻¹ : ℝ) : ℂ) *
              Q.eval (s : ℂ)) := by
        push_cast
        field_simp
      _ = (((semilocalPrimeWeight p s : NNReal) : ℝ) : ℂ) *
          P.eval (s : ℂ) := by rw [← hs]
  have hzero := semilocalPrimeWeight_polynomial_core_disjoint_ae p hp Q P hforward
  exact ⟨hzero.2, hzero.1⟩

end RHTower
