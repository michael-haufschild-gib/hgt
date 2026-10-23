import GaloisForLFunctions.ArithmeticCompensationTheory.TheCompensationDefectDecaysLogarithmically
import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicArbitraryLogRate

/-!
# The compensation defect decays faster than every power of the logarithm

The logarithmic rate `K/log⁶P` of the compensation defect came from a `log⁴` saving in the damped
divisor remainder, itself fed by a `log^{16}` saving in the Möbius harmonic sums. The corpus owns
every logarithmic power of the harmonic saving (`RHTower.Sieve.exists_abs_deningerHarmonicPartial_le_const_div_log_pow`),
and the signed hyperbola split of the remainder converts each of them:

* `exists_norm_pmPowerDampedDivisorRemainder_le_log_pow`: for `0 < ε < ½` and every `m`,
  `|R_ε(N)| ≤ 1 + C_m N^{1−ε}/log^m N` for all large `N` (cut the divisors at `N/log^{2k}N`,
  `k = m + 1`, and use the harmonic saving `log^{−3k}` beyond the cut);
* `exists_remainderEnergy_le_log_pow`: the pronic energy of the remainder up to `P` is
  `O(P^{(1−2ε)/2}) + O(1) + O(P^{1−2ε}/log^{2m}P)`;
* `exists_compensationDefect_le_inv_log_pow`: **for every `m`,
  `(1 − α_P)² + ‖R_P‖²/‖L_P‖² ≤ K_m/log^m P`** for all large `P`;
* `exists_abs_one_sub_pmCompensationAmplitude_le_log_pow`: the amplitude mismatch is
  `O(log^{−m}P)` for every `m`.

So the compensation of the large-prime sector by its complement is faster than every power of the
logarithm, at every fixed damping below one half. The absolute complete energy is
`O(P^{1−2ε}/log^m P)` for every `m` and still grows: a power saving would be a zero-free strip.
The signed block estimates below are those of `RHTower.PMRamanujanComplementarySourceBounds`, where
they are private.
-/

open Finset Filter Topology Complex ArithmeticFunction RHTower
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## Signed block estimates for the damped divisor remainder -/

private theorem acl_increasing_block (a : ℕ → ℂ) (w : ℕ → ℝ) {L M : ℕ}
    (hLM : L ≤ M) (hwL : 0 ≤ w L) (hw : Monotone w) {B : ℝ}
    (hB : ∀ k, L ≤ k → k ≤ M → ‖∑ n ∈ Ico L k, a n‖ ≤ B) :
    ‖∑ n ∈ Ico L M, (w n : ℂ)*a n‖ ≤ 2*B*w M := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB L le_rfl hLM)
  have hwM : 0 ≤ w M := hwL.trans (hw hLM)
  have hb := Sieve.abel_block_bound a (fun n => w M-w n) L M hLM
    (by simp) (fun n hn hnM => by linarith [hw (Nat.le_succ n)]) B hB
  have he : (∑ n ∈ Ico L M, (w n : ℂ)*a n) =
      (w M : ℂ)*(∑ n ∈ Ico L M, a n) -
        ∑ n ∈ Ico L M, ((w M-w n : ℝ) : ℂ)*a n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring
  rw [he]
  have ht : ‖(w M : ℂ)*(∑ n ∈ Ico L M, a n)‖ ≤ w M*B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwM]
    exact mul_le_mul_of_nonneg_left (hB M hLM le_rfl) hwM
  have hh := norm_sub_le ((w M : ℂ)*(∑ n ∈ Ico L M, a n))
    (∑ n ∈ Ico L M, ((w M-w n : ℝ) : ℂ)*a n)
  nlinarith [mul_nonneg hB0 hwL]

private theorem acl_harmonic_block {Y M : ℕ} (hYM : Y+1 ≤ M) {B : ℝ}
    (hB : ∀ k ≥ Y, |deningerHarmonicPartial k| ≤ B) :
    ‖∑ n ∈ Ico (Y+1) M, (moebius n : ℂ)/(n : ℂ)‖ ≤ 2*B := by
  have hM : 1 ≤ M := by omega
  have he : (∑ n ∈ Ico (Y+1) M, (moebius n : ℂ)/(n : ℂ)) =
      ((deningerHarmonicPartial (M-1)-deningerHarmonicPartial Y : ℝ) : ℂ) := by
    simp only [deningerHarmonicPartial, Complex.ofReal_sub, Complex.ofReal_sum,
      Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_natCast]
    rw [Finset.sum_Ico_eq_sub _ hYM, Nat.sub_add_cancel hM]
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact (abs_sub _ _).trans (by linarith [hB (M-1) (by omega), hB Y le_rfl])

private theorem acl_damped_block {ε : ℝ} (hε : ε < 1) {Y X : ℕ}
    (hYX : Y ≤ X) {B : ℝ} (hB : ∀ k ≥ Y, |deningerHarmonicPartial k| ≤ B) :
    ‖∑ n ∈ Ioc Y X, pmPowerDampedMobiusCoeff ε n‖ ≤
      4*B*((X+1 : ℕ) : ℝ)^(1-ε) := by
  have hmono : Monotone (fun n : ℕ => (n : ℝ)^(1-ε)) := by
    intro n m hnm
    exact Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnm) (by linarith)
  have hb := acl_increasing_block (fun n => (moebius n : ℂ)/(n : ℂ))
    (fun n => (n : ℝ)^(1-ε)) (by omega : Y+1 ≤ X+1)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) hmono
    (fun k hk hkX => acl_harmonic_block hk hB)
  have hs : Ioc Y X = Ico (Y+1) (X+1) := by ext n; simp
  rw [hs]
  have he (n : ℕ) (hn : n ∈ Ico (Y+1) (X+1)) :
      pmPowerDampedMobiusCoeff ε n = (((n : ℝ)^(1-ε) : ℝ) : ℂ)*((moebius n : ℂ)/(n : ℂ)) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from by have := (mem_Ico.mp hn).1; omega)
    rw [Real.rpow_sub hn0, Real.rpow_one]
    simp only [pmPowerDampedMobiusCoeff, Complex.ofReal_mul, Complex.ofReal_intCast,
      Real.rpow_neg hn0.le, Complex.ofReal_inv, Complex.ofReal_div, Complex.ofReal_natCast]
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn0)
    field_simp [hnc]
  rw [Finset.sum_congr rfl he]
  calc _ ≤ 2*(2*B)*((X+1 : ℕ) : ℝ)^(1-ε) := hb
       _ = _ := by ring

private theorem acl_density_block {ε : ℝ} (hε : 0 ≤ ε) {Y M : ℕ}
    (hYM : Y+1 ≤ M) {B : ℝ} (hB : ∀ k ≥ Y, |deningerHarmonicPartial k| ≤ B) :
    ‖∑ n ∈ Ico (Y+1) M, pmPowerDampedMobiusCoeff ε n/(n : ℂ)‖ ≤
      2*B*((Y+1 : ℕ) : ℝ)^(-ε) := by
  have hb := Sieve.abel_block_bound (fun n => (moebius n : ℂ)/(n : ℂ))
    (fun n => (n : ℝ)^(-ε)) (Y+1) M hYM (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun n hn hnM => Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast (show 0 < n from by omega))
      (by exact_mod_cast Nat.le_succ n) (by linarith)) (2*B)
    (fun k hk hkM => acl_harmonic_block hk hB)
  have he (n : ℕ) : pmPowerDampedMobiusCoeff ε n/(n : ℂ) =
      (((n : ℝ)^(-ε) : ℝ) : ℂ)*((moebius n : ℂ)/(n : ℂ)) := by
    simp only [pmPowerDampedMobiusCoeff, Complex.ofReal_mul, Complex.ofReal_intCast]
    ring
  simpa only [he] using hb

private theorem acl_density_tail {ε : ℝ} (hε : 0 < ε) (Y : ℕ) {B : ℝ}
    (hB : ∀ k ≥ Y, |deningerHarmonicPartial k| ≤ B) :
    ‖∑' k : ℕ, pmPowerDampedMobiusCoeff ε (k+(Y+1))/((k+(Y+1) : ℕ) : ℂ)‖ ≤
      2*B*((Y+1 : ℕ) : ℝ)^(-ε) := by
  have hs := (summable_nat_add_iff (Y+1)).mpr (summable_pmPowerDampedDivisorDensity_terms hε)
  apply le_of_tendsto hs.tendsto_sum_tsum_nat.norm
  apply Eventually.of_forall
  intro M
  have hb := acl_density_block hε.le (by omega : Y+1 ≤ (Y+1)+M) hB
  rw [Finset.sum_Ico_eq_sum_range] at hb
  simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel_right, Nat.add_comm] using hb

private theorem acl_floor_tail_bound {ε : ℝ} (hε : ε < 1) (Y N : ℕ) {B : ℝ}
    (hB : ∀ k ≥ Y, |deningerHarmonicPartial k| ≤ B) :
    ‖∑ k ∈ Icc 1 (N/(Y+1)), ∑ d ∈ Ioc Y (N/k), pmPowerDampedMobiusCoeff ε d‖ ≤
      4*B*((N/(Y+1) : ℕ) : ℝ)*((N+1 : ℕ) : ℝ)^(1-ε) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB Y le_rfl)
  calc
    _ ≤ ∑ k ∈ Icc 1 (N/(Y+1)),
        ‖∑ d ∈ Ioc Y (N/k), pmPowerDampedMobiusCoeff ε d‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Icc 1 (N/(Y+1)), 4*B*((N+1 : ℕ) : ℝ)^(1-ε) := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hYk : Y ≤ N/k
      · apply (acl_damped_block hε hYk hB).trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by
          exact_mod_cast (Nat.add_le_add_right (Nat.div_le_self N k) 1)) (by linarith)
      · rw [Ioc_eq_empty_of_le (by omega : N/k ≤ Y), sum_empty, norm_zero]
        positivity
    _ = _ := by simp; ring

private theorem acl_fract_head_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (Y N : ℕ) :
    ‖∑ d ∈ Icc 1 Y, pmPowerDampedMobiusCoeff ε d *
      ((Int.fract ((N : ℝ)/d) : ℝ) : ℂ)‖ ≤ 1+(Y : ℝ)^(1-ε)/(1-ε) := by
  apply (norm_sum_le _ _).trans
  refine le_trans ?_ (sum_rpow_neg_head_le hε hε1 Y)
  apply Finset.sum_le_sum
  intro d hd
  have hc : ‖pmPowerDampedMobiusCoeff ε d‖ ≤ (d : ℝ)^(-ε) := by
    rw [pmPowerDampedMobiusCoeff, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    apply mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (Int.fract_lt_one _).le (norm_nonneg _)).trans
    (by simpa using hc)

private theorem acl_remainder_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {Y N : ℕ} (hYN : Y ≤ N) {B : ℝ}
    (hB : ∀ k ≥ Y, |deningerHarmonicPartial k| ≤ B) :
    ‖pmPowerDampedDivisorRemainder ε N‖ ≤
      1+(Y : ℝ)^(1-ε)/(1-ε) +
      4*B*((N/(Y+1) : ℕ) : ℝ)*((N+1 : ℕ) : ℝ)^(1-ε) +
      2*B*(N : ℝ)*((Y+1 : ℕ) : ℝ)^(-ε) := by
  rw [pmPowerDampedDivisorRemainder_harmonic_split hε hYN]
  apply (norm_sub_le _ _).trans
  have hadd := norm_add_le
    (-(∑ d ∈ Icc 1 Y, pmPowerDampedMobiusCoeff ε d *
      ((Int.fract ((N : ℝ)/d) : ℝ) : ℂ)))
    (∑ k ∈ Icc 1 (N/(Y+1)), ∑ d ∈ Ioc Y (N/k), pmPowerDampedMobiusCoeff ε d)
  rw [norm_neg] at hadd
  have htail := mul_le_mul_of_nonneg_left (acl_density_tail hε Y hB) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  rw [norm_mul, Complex.norm_natCast]
  have hh := acl_fract_head_bound hε hε1 Y N
  have hf := acl_floor_tail_bound hε1 Y N hB
  linarith

private theorem acl_cutoff {N : ℕ} {L : ℝ} (hN : (1 : ℝ) ≤ N)
    (hL1 : 1 ≤ L) (hL : L ≤ Real.sqrt N/2) :
    let Y := ⌊(N : ℝ)/L⌋₊
    Y ≤ N ∧ Real.sqrt N ≤ (Y : ℝ) ∧ (Y : ℝ) ≤ (N : ℝ)/L ∧
      (N : ℝ)/((Y+1 : ℕ) : ℝ) ≤ L := by
  let Y := ⌊(N : ℝ)/L⌋₊
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hY : (Y : ℝ) ≤ (N : ℝ)/L := Nat.floor_le (div_nonneg hN0.le hL0.le)
  have hgap : (N : ℝ)/L < (Y : ℝ)+1 := Nat.lt_floor_add_one _
  have hs0 := Real.sqrt_nonneg (N : ℝ)
  have hs2 := Real.sq_sqrt hN0.le
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by nlinarith
  have hs : 2*Real.sqrt (N : ℝ) ≤ (N : ℝ)/L := by
    rw [le_div_iff₀ hL0]
    nlinarith
  refine ⟨?_, by dsimp only [Y] at *; linarith, hY, ?_⟩
  · apply Nat.floor_le_of_le
    exact (div_le_self hN0.le hL1)
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((Y+1 : ℕ) : ℝ))]
    have hh := (div_lt_iff₀ hL0).mp hgap
    push_cast
    nlinarith

private theorem acl_scaled_remainder_bound {ε L B : ℝ} {Y N : ℕ}
    (hε : 0 < ε) (hε1 : ε < 1) (hN : (1 : ℝ) ≤ N) (hL : 1 ≤ L)
    (hYN : Y ≤ N) (hY : (Y : ℝ) ≤ (N : ℝ)/L)
    (hJ : (N : ℝ)/((Y+1 : ℕ) : ℝ) ≤ L)
    (hB : ∀ k ≥ Y, |deningerHarmonicPartial k| ≤ B) :
    ‖pmPowerDampedDivisorRemainder ε N‖ ≤
      1+(N : ℝ)^(1-ε)/((1-ε)*L^(1-ε)) + 10*B*L*(N : ℝ)^(1-ε) := by
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB Y le_rfl)
  have hδ : 0 < 1-ε := sub_pos.mpr hε1
  have hypos : (0 : ℝ) < ((Y+1 : ℕ) : ℝ) := by positivity
  have hhead : (Y : ℝ)^(1-ε)/(1-ε) ≤
      (N : ℝ)^(1-ε)/((1-ε)*L^(1-ε)) := by
    calc
      _ ≤ ((N : ℝ)/L)^(1-ε)/(1-ε) :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hY hδ.le) hδ.le
      _ = _ := by rw [Real.div_rpow hN0.le hL0.le, div_div, mul_comm (L^(1-ε))]
  have hquot : ((N/(Y+1) : ℕ) : ℝ) ≤ L := by
    apply le_trans _ hJ
    simpa only [Nat.floor_div_eq_div] using
      (Nat.floor_le (by positivity : (0 : ℝ) ≤ (N : ℝ)/((Y+1 : ℕ) : ℝ)))
  have hsucc : ((N+1 : ℕ) : ℝ)^(1-ε) ≤ 2*(N : ℝ)^(1-ε) := by
    calc
      _ ≤ (2*(N : ℝ))^(1-ε) := Real.rpow_le_rpow (Nat.cast_nonneg _) (by push_cast; linarith) hδ.le
      _ = (2 : ℝ)^(1-ε)*(N : ℝ)^(1-ε) := Real.mul_rpow (by norm_num) hN0.le
      _ ≤ 2*(N : ℝ)^(1-ε) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
        calc (2 : ℝ)^(1-ε) ≤ (2 : ℝ)^(1 : ℝ) :=
               Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
             _ = _ := Real.rpow_one 2
  have hfloor : 4*B*((N/(Y+1) : ℕ) : ℝ)*((N+1 : ℕ) : ℝ)^(1-ε) ≤
      8*B*L*(N : ℝ)^(1-ε) := by
    have hh := mul_le_mul hquot hsucc (Real.rpow_nonneg (Nat.cast_nonneg _) _) hL0.le
    nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*B by positivity)]
  have hlower : (N : ℝ)/L ≤ ((Y+1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hL0]
    have hh := (div_le_iff₀ hypos).mp hJ
    linarith
  have hdensity : (N : ℝ)*((Y+1 : ℕ) : ℝ)^(-ε) ≤ L*(N : ℝ)^(1-ε) := by
    calc
      _ ≤ (N : ℝ)*((N : ℝ)/L)^(-ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (div_pos hN0 hL0)
          hlower (by linarith)) hN0.le
      _ = L^ε*(N : ℝ)^(1-ε) := by
        rw [Real.div_rpow hN0.le hL0.le, Real.rpow_sub hN0, Real.rpow_one,
          Real.rpow_neg hN0.le, Real.rpow_neg hL0.le]
        simp only [div_eq_mul_inv, inv_inv]
        ring
      _ ≤ L*(N : ℝ)^(1-ε) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
        calc L^ε ≤ L^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL hε1.le
             _ = _ := Real.rpow_one L
  have htail := mul_le_mul_of_nonneg_left hdensity (show 0 ≤ 2*B by positivity)
  have hb := acl_remainder_bound hε hε1 hYN hB
  nlinarith


/-! ## Every logarithmic power -/

/-- **The damped divisor remainder saves every power of the logarithm.** -/
theorem exists_norm_pmPowerDampedDivisorRemainder_le_log_pow {ε : ℝ} (hε : 0 < ε)
    (hεhalf : ε < 1 / 2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ‖pmPowerDampedDivisorRemainder ε N‖ ≤ 1 + C * (N : ℝ) ^ (1 - ε) / Real.log (N : ℝ) ^ m := by
  set k : ℕ := m + 1
  obtain ⟨A, hA, heA⟩ := Sieve.exists_abs_deningerHarmonicPartial_le_const_div_log_pow (3 * k)
    (by omega)
  obtain ⟨K, hK⟩ := eventually_atTop.mp heA
  set C₀ : ℝ := A * 2 ^ (3 * k)
  have hC₀ : 0 ≤ C₀ := by positivity
  have hδ : 0 < 1 - ε := by linarith
  refine ⟨1 / (1 - ε) + 10 * C₀, by positivity, ?_⟩
  have hsmall := ((isLittleO_log_rpow_rpow_atTop ((2 * k : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto tendsto_natCast_atTop_atTop).bound
      (c := 1 / 2) (by norm_num)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hroot := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (K : ℝ)
  filter_upwards [hsmall, hlog, hroot, eventually_ge_atTop 1] with N hsmallN hlogN hrootN hN
  dsimp only [Function.comp_def] at hsmallN hlogN hrootN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hNR
  have hl0 : 0 < Real.log (N : ℝ) := by linarith
  have hl1 : 1 ≤ Real.log (N : ℝ) := by linarith
  set L := Real.log (N : ℝ) ^ (2 * k)
  set Y := ⌊(N : ℝ) / L⌋₊
  have hL1 : 1 ≤ L := one_le_pow₀ hl1
  have hL : L ≤ Real.sqrt N / 2 := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hN0.le _), Real.rpow_natCast,
      ← Real.sqrt_eq_rpow] at hsmallN
    simp only [L]
    linarith
  obtain ⟨hYN, hYs, hY, hJ⟩ := acl_cutoff hNR hL1 hL
  have hYs0 : (0 : ℝ) < Y := (Real.sqrt_pos.2 hN0).trans_le hYs
  have hYK : K ≤ Y := by exact_mod_cast hrootN.trans hYs
  have hlogY : Real.log (N : ℝ) / 2 ≤ Real.log (Y : ℝ) := by
    rw [← Real.log_sqrt hN0.le]
    exact Real.log_le_log (Real.sqrt_pos.2 hN0) hYs
  have hB (j : ℕ) (hj : Y ≤ j) :
      |deningerHarmonicPartial j| ≤ C₀ / Real.log (N : ℝ) ^ (3 * k) := by
    have hlogj : Real.log (N : ℝ) / 2 ≤ Real.log (j : ℝ) :=
      hlogY.trans (Real.log_le_log hYs0 (by exact_mod_cast hj))
    calc
      _ ≤ A / Real.log (j : ℝ) ^ (3 * k) := hK j (hYK.trans hj)
      _ ≤ A / (Real.log (N : ℝ) / 2) ^ (3 * k) := div_le_div_of_nonneg_left hA
        (by positivity) (pow_le_pow_left₀ (by positivity) hlogj _)
      _ = _ := by simp only [C₀]; rw [div_pow]; field_simp
  have hb := acl_scaled_remainder_bound hε (by linarith : ε < 1) hNR hL1 hYN hY hJ hB
  have hm1 : Real.log (N : ℝ) ^ m ≤ Real.log (N : ℝ) ^ k := pow_le_pow_right₀ hl1 (by omega)
  have hp : Real.log (N : ℝ) ^ m ≤ L ^ (1 - ε) := by
    calc
      _ ≤ Real.log (N : ℝ) ^ k := hm1
      _ = Real.log (N : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ k).symm
      _ ≤ Real.log (N : ℝ) ^ (((2 * k : ℕ) : ℝ) * (1 - ε)) :=
        Real.rpow_le_rpow_of_exponent_le hl1 (by push_cast; nlinarith)
      _ = L ^ (1 - ε) := Real.rpow_natCast_mul hl0.le (2 * k) (1 - ε)
  have hm0 : 0 < Real.log (N : ℝ) ^ m := by positivity
  have hhead : (N : ℝ) ^ (1 - ε) / ((1 - ε) * L ^ (1 - ε)) ≤
      (N : ℝ) ^ (1 - ε) / ((1 - ε) * Real.log (N : ℝ) ^ m) :=
    div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) (by positivity)
      (mul_le_mul_of_nonneg_left hp hδ.le)
  have htail : 10 * (C₀ / Real.log (N : ℝ) ^ (3 * k)) * L * (N : ℝ) ^ (1 - ε) ≤
      10 * C₀ * (N : ℝ) ^ (1 - ε) / Real.log (N : ℝ) ^ m := by
    have he : 10 * (C₀ / Real.log (N : ℝ) ^ (3 * k)) * L * (N : ℝ) ^ (1 - ε) =
        10 * C₀ * (N : ℝ) ^ (1 - ε) / Real.log (N : ℝ) ^ k := by
      simp only [L]
      rw [show 3 * k = 2 * k + k by ring, pow_add]
      field_simp
    rw [he]
    exact div_le_div_of_nonneg_left (by positivity) hm0 hm1
  calc
    _ ≤ 1 + (N : ℝ) ^ (1 - ε) / ((1 - ε) * Real.log (N : ℝ) ^ m) +
        10 * C₀ * (N : ℝ) ^ (1 - ε) / Real.log (N : ℝ) ^ m := by linarith
    _ = _ := by field_simp; ring

/-- `(1 + B N^{1−ε})²/(N(N+1)) ≤ 2N^{−2} + 2B²N^{−2ε}`. -/
private theorem acl_weighted_sq_norm_le {z : ℂ} {ε B : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hz : ‖z‖ ≤ 1 + B * (N : ℝ) ^ (1 - ε)) :
    ‖z‖ ^ 2 / ((N : ℝ) * ((N : ℝ) + 1)) ≤
      2 * (N : ℝ) ^ (-2 : ℝ) + 2 * B ^ 2 * (N : ℝ) ^ (-2 * ε) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hb : ‖z‖ ^ 2 ≤ 2 + 2 * B ^ 2 * ((N : ℝ) ^ (1 - ε)) ^ 2 := by
    nlinarith [sq_nonneg (1 - B * (N : ℝ) ^ (1 - ε))]
  have hone : 1 / ((N : ℝ) * ((N : ℝ) + 1)) ≤ (N : ℝ) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hN0.le, Real.rpow_two]
    simpa only [one_div] using (one_div_le_one_div_of_le
      (by positivity : (0 : ℝ) < (N : ℝ) ^ 2)
      (by nlinarith : (N : ℝ) ^ 2 ≤ (N : ℝ) * ((N : ℝ) + 1)))
  have hp := rpow_sq_div_pronic_le (ε := ε) hN
  calc
    _ ≤ (2 + 2 * B ^ 2 * ((N : ℝ) ^ (1 - ε)) ^ 2) / ((N : ℝ) * ((N : ℝ) + 1)) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = 2 * (1 / ((N : ℝ) * ((N : ℝ) + 1))) +
        2 * B ^ 2 * (((N : ℝ) ^ (1 - ε)) ^ 2 / ((N : ℝ) * ((N : ℝ) + 1))) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hone (by norm_num))
      (mul_le_mul_of_nonneg_left hp (by positivity))

/-- **The remainder energy with every logarithmic saving.** -/
theorem exists_remainderEnergy_le_log_pow {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) (m : ℕ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ᶠ P : ℕ in atTop,
      (∑ N ∈ Icc 1 P, ‖pmPowerDampedDivisorRemainder ε N‖ ^ 2 / ((N : ℝ) * ((N : ℝ) + 1))) ≤
        2 * A ^ 2 * (1 + (P : ℝ) ^ ((1 - 2 * ε) / 2) / (1 - 2 * ε)) +
        2 * (∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ)) +
        (2 * C ^ 2 / Real.log (P : ℝ) ^ (2 * m)) * (1 + (P : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) := by
  obtain ⟨A, hA, hglobal⟩ := divisorRemainder_le_global hε hεhalf
  obtain ⟨C, hC, hc⟩ := exists_norm_pmPowerDampedDivisorRemainder_le_log_pow hε hεhalf m
  obtain ⟨K, hK⟩ := eventually_atTop.mp hc
  refine ⟨A, 2 ^ m * C, hA, by positivity, ?_⟩
  have hroot := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (K : ℝ)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [hroot, hlog, eventually_ge_atTop 1] with P hrootP hlogP hP
  dsimp only [Function.comp_def] at hrootP hlogP
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := zero_lt_one.trans_le hPR
  have hl0 : 0 < Real.log (P : ℝ) := by linarith
  have hδ : 0 < 1 - 2 * ε := by linarith
  set T := ⌊Real.sqrt (P : ℝ)⌋₊
  set w : ℕ → ℝ := fun N => ‖pmPowerDampedDivisorRemainder ε N‖ ^ 2 / ((N : ℝ) * ((N : ℝ) + 1))
  have hT : (T : ℝ) ≤ Real.sqrt (P : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hTP : T ≤ P := by
    apply Nat.floor_le_of_le
    nlinarith [Real.sq_sqrt hP0.le, Real.sqrt_nonneg (P : ℝ)]
  have hsmall : (∑ N ∈ Icc 1 T, w N) ≤
      2 * A ^ 2 * (1 + (P : ℝ) ^ ((1 - 2 * ε) / 2) / (1 - 2 * ε)) := by
    have hcell : ∀ N ∈ Icc 1 T, w N ≤ 2 * A ^ 2 * (N : ℝ) ^ (-(2 * ε)) := by
      intro N hN
      have hN1 := (mem_Icc.mp hN).1
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
      have hz := hglobal N hN1
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hz 2
      have hp := rpow_sq_div_pronic_le (ε := ε) hN1
      calc w N ≤ (A * (N : ℝ) ^ (1 - ε)) ^ 2 / ((N : ℝ) * ((N : ℝ) + 1)) :=
            div_le_div_of_nonneg_right hsq (by positivity)
        _ = A ^ 2 * (((N : ℝ) ^ (1 - ε)) ^ 2 / ((N : ℝ) * ((N : ℝ) + 1))) := by ring
        _ ≤ A ^ 2 * (N : ℝ) ^ (-2 * ε) := mul_le_mul_of_nonneg_left hp (by positivity)
        _ ≤ 2 * A ^ 2 * (N : ℝ) ^ (-(2 * ε)) := by
            rw [neg_mul]; nlinarith [Real.rpow_nonneg hN0.le (-(2 * ε)), sq_nonneg A]
    calc (∑ N ∈ Icc 1 T, w N) ≤ ∑ N ∈ Icc 1 T, 2 * A ^ 2 * (N : ℝ) ^ (-(2 * ε)) :=
          sum_le_sum hcell
      _ = 2 * A ^ 2 * (∑ N ∈ Icc 1 T, (N : ℝ) ^ (-(2 * ε))) := by rw [mul_sum]
      _ ≤ 2 * A ^ 2 * (1 + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) :=
          mul_le_mul_of_nonneg_left (sum_rpow_neg_head_le (by positivity : 0 < 2 * ε)
            (by linarith) T) (by positivity)
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply add_le_add le_rfl
          apply div_le_div_of_nonneg_right _ hδ.le
          calc (T : ℝ) ^ (1 - 2 * ε) ≤ (Real.sqrt (P : ℝ)) ^ (1 - 2 * ε) :=
                Real.rpow_le_rpow (Nat.cast_nonneg _) hT hδ.le
            _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP0.le]; congr 1; ring
  have hlargeTerm (N : ℕ) (hN : N ∈ Ioc T P) :
      w N ≤ 2 * (N : ℝ) ^ (-2 : ℝ) +
        (2 * (2 ^ m * C) ^ 2 / Real.log (P : ℝ) ^ (2 * m)) * (N : ℝ) ^ (-2 * ε) := by
    have hN1 : 1 ≤ N := by have := (mem_Ioc.mp hN).1; omega
    have hNr : Real.sqrt (P : ℝ) < N :=
      (Nat.floor_lt (Real.sqrt_nonneg _)).mp (mem_Ioc.mp hN).1
    have hNK : K ≤ N := by exact_mod_cast (hrootP.trans hNr.le)
    have hln : Real.log (P : ℝ) / 2 ≤ Real.log (N : ℝ) := by
      rw [← Real.log_sqrt hP0.le]
      exact Real.log_le_log (Real.sqrt_pos.2 hP0) hNr.le
    have hcoef : C / Real.log (N : ℝ) ^ m ≤ 2 ^ m * C / Real.log (P : ℝ) ^ m := by
      calc
        _ ≤ C / (Real.log (P : ℝ) / 2) ^ m := div_le_div_of_nonneg_left hC (by positivity)
          (pow_le_pow_left₀ (by positivity) hln m)
        _ = _ := by rw [div_pow]; field_simp
    have hz : ‖pmPowerDampedDivisorRemainder ε N‖ ≤
        1 + (2 ^ m * C / Real.log (P : ℝ) ^ m) * (N : ℝ) ^ (1 - ε) := by
      have hb := hK N hNK
      have hm := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (Nat.cast_nonneg N) (1 - ε))
      refine hb.trans ?_
      calc
        _ = 1 + (C / Real.log (N : ℝ) ^ m) * (N : ℝ) ^ (1 - ε) := by ring
        _ ≤ _ := add_le_add le_rfl hm
    have hw := acl_weighted_sq_norm_le hN1 hz
    simp only [w]
    convert hw using 2
    rw [div_pow, ← pow_mul, mul_comm m 2]
    ring
  have hlarge : (∑ N ∈ Ioc T P, w N) ≤ 2 * (∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ)) +
      (2 * (2 ^ m * C) ^ 2 / Real.log (P : ℝ) ^ (2 * m)) *
        (1 + (P : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) := by
    have hg : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := Real.summable_nat_rpow.mpr (by norm_num)
    calc
      _ ≤ ∑ N ∈ Ioc T P, (2 * (N : ℝ) ^ (-2 : ℝ) +
          (2 * (2 ^ m * C) ^ 2 / Real.log (P : ℝ) ^ (2 * m)) * (N : ℝ) ^ (-2 * ε)) :=
        Finset.sum_le_sum hlargeTerm
      _ ≤ ∑ N ∈ Icc 1 P, (2 * (N : ℝ) ^ (-2 : ℝ) +
          (2 * (2 ^ m * C) ^ 2 / Real.log (P : ℝ) ^ (2 * m)) * (N : ℝ) ^ (-2 * ε)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro N hN
          obtain ⟨hTN, hNP⟩ := mem_Ioc.mp hN
          exact mem_Icc.mpr ⟨by omega, hNP⟩
        · intro N _ _
          positivity
      _ = 2 * (∑ N ∈ Icc 1 P, (N : ℝ) ^ (-2 : ℝ)) +
          (2 * (2 ^ m * C) ^ 2 / Real.log (P : ℝ) ^ (2 * m)) *
            (∑ N ∈ Icc 1 P, (N : ℝ) ^ (-(2 * ε))) := by
        simp only [sum_add_distrib, mul_sum, neg_mul]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (hg.sum_le_tsum _
          (fun N _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity))
        (mul_le_mul_of_nonneg_left (sum_rpow_neg_head_le (by positivity : 0 < 2 * ε)
          (by linarith) P) (by positivity))
  have hu : Icc 1 P = Icc 1 T ∪ Ioc T P := by
    ext N
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hd : Disjoint (Icc 1 T) (Ioc T P) := by
    apply Finset.disjoint_left.mpr
    intro N hn hm
    have := (mem_Icc.mp hn).2
    have := (mem_Ioc.mp hm).1
    omega
  change (∑ N ∈ Icc 1 P, w N) ≤ _
  rw [hu, Finset.sum_union hd]
  linarith

/-- `log^j P / P^s → 0` along the integers. -/
theorem tendsto_log_pow_div_rpow (j : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun P : ℕ => Real.log P ^ j / (P : ℝ) ^ s) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (j : ℝ) hs).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun P => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_natCast]

/-- **The compensation defect decays faster than every power of the logarithm.** For
`0 < ε < ½` and every `m` there is `K` with `(1 − α_P)² + ‖R_P‖²/‖L_P‖² ≤ K/log^m P` for all
large `P`. -/
theorem exists_compensationDefect_le_inv_log_pow {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (m : ℕ) : ∃ K : ℝ, ∀ᶠ P : ℕ in atTop, compensationDefect ε P ≤ K / Real.log P ^ m := by
  obtain ⟨A, C, hA, hC, hrem⟩ := exists_remainderEnergy_le_log_pow hε hεhalf (m + 2)
  obtain ⟨T, hT, hpre⟩ := prefixEnergy_le hε
  obtain ⟨c, hc, hsec⟩ := sectorEnergy_eventually_lower hε
  set d : ℝ := 1 - 2 * ε with hddef
  have hd : 0 < d := by rw [hddef]; linarith
  set Z : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ)
  have hZ : 0 ≤ Z := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  set K₀ : ℝ := 8 * C ^ 2 * (1 + 1 / d) / c
  refine ⟨3 + K₀, ?_⟩
  have l1 := ((tendsto_log_pow_div_rpow (m + 2) hd).const_mul ((4 * A ^ 2 + 4 * Z) / c)).eventually
    (eventually_le_nhds (show ((4 * A ^ 2 + 4 * Z) / c) * 0 < 1 by rw [mul_zero]; norm_num))
  have l2 := ((tendsto_log_pow_div_rpow (m + 2) (half_pos hd)).const_mul
    (4 * A ^ 2 / (c * d))).eventually
    (eventually_le_nhds (show (4 * A ^ 2 / (c * d)) * 0 < 1 by rw [mul_zero]; norm_num))
  have l3 := ((tendsto_log_pow_div_rpow (m + 2) hε).const_mul (2 * T ^ 4 / c)).eventually
    (eventually_le_nhds (show (2 * T ^ 4 / c) * 0 < 1 by rw [mul_zero]; norm_num))
  have hlog3 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hrem, hsec, l1, l2, l3, eventually_ge_atTop 2, hlog3,
    eventually_compensationDefect_eq_relative hε hεhalf] with P hR hS h1 h2 h3 hP hlog1 hrel
  dsimp only [Function.comp_def] at hlog1
  have hP1 : (1 : ℝ) < P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hlog : 0 < Real.log P := Real.log_pos hP1
  set L : ℝ := Real.log P ^ (m + 2) with hLdef
  have hL : 0 < L := by positivity
  have hLL : L ≤ Real.log P ^ (2 * (m + 2)) := pow_le_pow_right₀ hlog1 (by omega)
  have hPd : 0 < (P : ℝ) ^ d := Real.rpow_pos_of_pos hP0 d
  have hPd2 : 0 < (P : ℝ) ^ (d / 2) := Real.rpow_pos_of_pos hP0 _
  have hPe : 0 < (P : ℝ) ^ ε := Real.rpow_pos_of_pos hP0 _
  have hPd1 : 1 ≤ (P : ℝ) ^ d := Real.one_le_rpow hP1.le hd.le
  have hsplit2 : (P : ℝ) ^ (d / 2) * (P : ℝ) ^ (d / 2) = (P : ℝ) ^ d := by
    rw [← Real.rpow_add hP0]; ring_nf
  have hsplit3 : (P : ℝ) ^ ε * (P : ℝ) ^ (1 - 3 * ε) = (P : ℝ) ^ d := by
    rw [← Real.rpow_add hP0, hddef]; ring_nf
  have m1 : (4 * A ^ 2 + 4 * Z) * L ≤ c * (P : ℝ) ^ d := by
    rw [div_mul_div_comm, div_le_one (by positivity)] at h1; linarith
  have m2 : 4 * A ^ 2 / d * L * (P : ℝ) ^ (d / 2) ≤ c * (P : ℝ) ^ d := by
    rw [div_mul_div_comm, div_le_one (by positivity)] at h2
    have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (P : ℝ) ^ (d / 2) / d)
    calc 4 * A ^ 2 / d * L * (P : ℝ) ^ (d / 2) = 4 * A ^ 2 * L * ((P : ℝ) ^ (d / 2) / d) := by
          ring
      _ ≤ c * d * (P : ℝ) ^ (d / 2) * ((P : ℝ) ^ (d / 2) / d) := this
      _ = c * (P : ℝ) ^ d := by rw [← hsplit2]; field_simp
  have m3 : 2 * T ^ 4 * (P : ℝ) ^ (1 - 3 * ε) * L ≤ c * (P : ℝ) ^ d := by
    rw [div_mul_div_comm, div_le_one (by positivity)] at h3
    have := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hP0.le (1 - 3 * ε))
    calc 2 * T ^ 4 * (P : ℝ) ^ (1 - 3 * ε) * L = 2 * T ^ 4 * L * (P : ℝ) ^ (1 - 3 * ε) := by
          ring
      _ ≤ c * (P : ℝ) ^ ε * (P : ℝ) ^ (1 - 3 * ε) := this
      _ = c * (P : ℝ) ^ d := by rw [mul_assoc, hsplit3]
  have m4 : 2 * C ^ 2 / Real.log P ^ (2 * (m + 2)) * (1 + (P : ℝ) ^ d / d) * L ≤
      K₀ / 4 * c * (P : ℝ) ^ d := by
    have hl2 : 0 < Real.log P ^ (2 * (m + 2)) := by positivity
    have h1' : 2 * C ^ 2 / Real.log P ^ (2 * (m + 2)) * (1 + (P : ℝ) ^ d / d) * L ≤
        2 * C ^ 2 * (1 + (P : ℝ) ^ d / d) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hLL (by positivity)
    have h2' : 1 + (P : ℝ) ^ d / d ≤ (1 + 1 / d) * (P : ℝ) ^ d := by
      have : (P : ℝ) ^ d / d = 1 / d * (P : ℝ) ^ d := by ring
      rw [this]; nlinarith
    calc _ ≤ 2 * C ^ 2 * (1 + (P : ℝ) ^ d / d) := h1'
      _ ≤ 2 * C ^ 2 * ((1 + 1 / d) * (P : ℝ) ^ d) := mul_le_mul_of_nonneg_left h2' (by positivity)
      _ = K₀ / 4 * c * (P : ℝ) ^ d := by simp only [K₀]; field_simp; ring
  set B : ℝ := 2 * (2 * A ^ 2 * (1 + (P : ℝ) ^ (d / 2) / d) + 2 * Z +
      2 * C ^ 2 / Real.log P ^ (2 * (m + 2)) * (1 + (P : ℝ) ^ d / d)) +
      2 * T ^ 4 * (P : ℝ) ^ (1 - 3 * ε)
  have hcomp : pmPowerDampedRamanujanPrefixEnergy ε (P ^ 2 - 1) (P - 1) ≤ B := by
    refine (prefixEnergy_mono ε _ (Nat.sub_le P 1)).trans ((hpre P (by omega)).trans ?_)
    have hR' := hR
    rw [show (1 - 2 * ε) / 2 = d / 2 by rw [hddef]] at hR'
    simp only [B]
    linarith
  have hBL : B * L ≤ (3 + K₀) * c * (P : ℝ) ^ d := by
    have e : B * L = (4 * A ^ 2 + 4 * Z) * L + 4 * A ^ 2 / d * L * (P : ℝ) ^ (d / 2) +
        2 * (2 * C ^ 2 / Real.log P ^ (2 * (m + 2)) * (1 + (P : ℝ) ^ d / d) * L) +
        2 * T ^ 4 * (P : ℝ) ^ (1 - 3 * ε) * L := by
      simp only [B]; field_simp; ring
    rw [e]
    have hK₀ : 0 ≤ K₀ * c * (P : ℝ) ^ d := by positivity
    linarith
  have hsecpos : 0 < pmRamanujanLargePrimeSectorEnergy ε P :=
    lt_of_lt_of_le (by positivity) hS
  rw [hrel, div_le_div_iff₀ hsecpos (by positivity)]
  have hlm : Real.log P ^ m * Real.log P ^ 2 = L := by rw [hLdef]; ring
  have hlow : c * (P : ℝ) ^ d ≤ pmRamanujanLargePrimeSectorEnergy ε P * Real.log P ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hS
    simpa [hddef] using hS
  have hK : 0 ≤ 3 + K₀ := by positivity
  calc pmPowerDampedRamanujanPrefixEnergy ε (P ^ 2 - 1) (P - 1) * Real.log P ^ m
      ≤ B * Real.log P ^ m := mul_le_mul_of_nonneg_right hcomp (by positivity)
    _ = B * L / Real.log P ^ 2 := by rw [← hlm]; field_simp
    _ ≤ (3 + K₀) * c * (P : ℝ) ^ d / Real.log P ^ 2 :=
        div_le_div_of_nonneg_right hBL (by positivity)
    _ ≤ (3 + K₀) * (pmRamanujanLargePrimeSectorEnergy ε P * Real.log P ^ 2) / Real.log P ^ 2 := by
        rw [mul_assoc]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlow hK) (by positivity)
    _ = (3 + K₀) * pmRamanujanLargePrimeSectorEnergy ε P := by field_simp

/-- **The amplitude mismatch decays faster than every power of the logarithm.** -/
theorem exists_abs_one_sub_pmCompensationAmplitude_le_log_pow {ε : ℝ} (hε : 0 < ε)
    (hεhalf : ε < 1 / 2) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ P : ℕ in atTop,
      |1 - pmCompensationAmplitude ε P| ≤ K / Real.log P ^ m := by
  obtain ⟨K, hK⟩ := exists_compensationDefect_le_inv_log_pow hε hεhalf (2 * m)
  refine ⟨Real.sqrt |K|, Real.sqrt_nonneg _, ?_⟩
  filter_upwards [hK, eventually_ge_atTop 2] with P hP hP2
  have hlog : 0 < Real.log P := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have htr : 0 ≤ pmTransverseEnergy ε P / pmRamanujanLargePrimeSectorEnergy ε P :=
    div_nonneg (pmCompleteHeadEnergy_eq_compensation hP2 ε).2
      (by unfold pmRamanujanLargePrimeSectorEnergy; positivity)
  have hsq : (1 - pmCompensationAmplitude ε P) ^ 2 ≤ |K| / (Real.log P ^ m) ^ 2 := by
    have h := hP.trans (div_le_div_of_nonneg_right (le_abs_self K) (by positivity))
    rw [compensationDefect] at h
    rw [← pow_mul, mul_comm m 2]
    linarith
  rw [← Real.sqrt_sq_eq_abs]
  calc Real.sqrt ((1 - pmCompensationAmplitude ε P) ^ 2)
      ≤ Real.sqrt (|K| / (Real.log P ^ m) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt |K| / Real.log P ^ m := by
        rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]

end GaloisForLFunctions.ArithmeticCompensationTheory
