import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanLogMass
import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicArbitraryLogRate
import GaloisForLFunctions.RHTower.GaussSpikeMass
import GaloisForLFunctions.RHTower.Sieve.DirichletBlockAbel

/-!
# Signed source bounds for complementary Ramanujan cancellation

Split the actual centered divisor remainder at a moving divisor cutoff. Both
large-divisor terms retain their Möbius signs: the finite quotient sum and the
infinite density tail. Harmonic Möbius cancellation gives a logarithmic saving
at every fixed damping below one half.

A separate coefficient-moment estimate controls the difference between the
actual natural Ramanujan prefix and the centered divisor remainder. These are
source estimates for the complementary-sector mixed-energy argument. Their
remaining positive energy power does not establish PM admission or RH.
-/

open Finset Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

private theorem pmc_increasing_block (a : ℕ → ℂ) (w : ℕ → ℝ) {L M : ℕ}
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

private theorem pmc_harmonic_block {Y M : ℕ} (hYM : Y+1 ≤ M) {B : ℝ}
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

private theorem pmc_damped_block {ε : ℝ} (hε : ε < 1) {Y X : ℕ}
    (hYX : Y ≤ X) {B : ℝ} (hB : ∀ k ≥ Y, |deningerHarmonicPartial k| ≤ B) :
    ‖∑ n ∈ Ioc Y X, pmPowerDampedMobiusCoeff ε n‖ ≤
      4*B*((X+1 : ℕ) : ℝ)^(1-ε) := by
  have hmono : Monotone (fun n : ℕ => (n : ℝ)^(1-ε)) := by
    intro n m hnm
    exact Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnm) (by linarith)
  have hb := pmc_increasing_block (fun n => (moebius n : ℂ)/(n : ℂ))
    (fun n => (n : ℝ)^(1-ε)) (by omega : Y+1 ≤ X+1)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) hmono
    (fun k hk hkX => pmc_harmonic_block hk hB)
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

private theorem pmc_density_block {ε : ℝ} (hε : 0 ≤ ε) {Y M : ℕ}
    (hYM : Y+1 ≤ M) {B : ℝ} (hB : ∀ k ≥ Y, |deningerHarmonicPartial k| ≤ B) :
    ‖∑ n ∈ Ico (Y+1) M, pmPowerDampedMobiusCoeff ε n/(n : ℂ)‖ ≤
      2*B*((Y+1 : ℕ) : ℝ)^(-ε) := by
  have hb := Sieve.abel_block_bound (fun n => (moebius n : ℂ)/(n : ℂ))
    (fun n => (n : ℝ)^(-ε)) (Y+1) M hYM (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun n hn hnM => Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast (show 0 < n from by omega))
      (by exact_mod_cast Nat.le_succ n) (by linarith)) (2*B)
    (fun k hk hkM => pmc_harmonic_block hk hB)
  have he (n : ℕ) : pmPowerDampedMobiusCoeff ε n/(n : ℂ) =
      (((n : ℝ)^(-ε) : ℝ) : ℂ)*((moebius n : ℂ)/(n : ℂ)) := by
    simp only [pmPowerDampedMobiusCoeff, Complex.ofReal_mul, Complex.ofReal_intCast]
    ring
  simpa only [he] using hb

private theorem pmc_density_tail {ε : ℝ} (hε : 0 < ε) (Y : ℕ) {B : ℝ}
    (hB : ∀ k ≥ Y, |deningerHarmonicPartial k| ≤ B) :
    ‖∑' k : ℕ, pmPowerDampedMobiusCoeff ε (k+(Y+1))/((k+(Y+1) : ℕ) : ℂ)‖ ≤
      2*B*((Y+1 : ℕ) : ℝ)^(-ε) := by
  have hs := (summable_nat_add_iff (Y+1)).mpr (summable_pmPowerDampedDivisorDensity_terms hε)
  apply le_of_tendsto hs.tendsto_sum_tsum_nat.norm
  apply Eventually.of_forall
  intro M
  have hb := pmc_density_block hε.le (by omega : Y+1 ≤ (Y+1)+M) hB
  rw [Finset.sum_Ico_eq_sum_range] at hb
  simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel_right, Nat.add_comm] using hb

private theorem pmc_floor_tail_swap (a : ℕ → ℂ) (Y N : ℕ) :
    (∑ d ∈ Ioc Y N, a d * ((N/d : ℕ) : ℂ)) =
      ∑ k ∈ Icc 1 (N/(Y+1)), ∑ d ∈ Ioc Y (N/k), a d := by
  classical
  have hrow (d : ℕ) (hd : d ∈ Ioc Y N) :
      a d * ((N/d : ℕ) : ℂ) =
        ∑ k ∈ Icc 1 (N/(Y+1)), if k*d ≤ N then a d else 0 := by
    have hd0 : 0 < d := by have := (mem_Ioc.mp hd).1; omega
    have hdiv : N/d ≤ N/(Y+1) :=
      Nat.div_le_div_left (by have := (mem_Ioc.mp hd).1; omega) (by omega)
    have hf : (Icc 1 (N/(Y+1))).filter (fun k => k*d ≤ N) = Icc 1 (N/d) := by
      ext k
      simp only [mem_filter, mem_Icc]
      rw [← Nat.le_div_iff_mul_le hd0]
      omega
    rw [← Finset.sum_filter, hf]
    simp [mul_comm]
  rw [Finset.sum_congr rfl hrow, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : 0 < k := (mem_Icc.mp hk).1
  have hf : (Ioc Y N).filter (fun d => k*d ≤ N) = Ioc Y (N/k) := by
    ext d
    simp only [mem_filter, mem_Ioc]
    rw [Nat.mul_comm k, ← Nat.le_div_iff_mul_le hk0]
    have := Nat.div_le_self N k
    omega
  rw [← Finset.sum_filter, hf]

/-- Exact signed hyperbola split, retaining the complete infinite density tail. -/
theorem pmPowerDampedDivisorRemainder_harmonic_split {ε : ℝ} (hε : 0 < ε) {Y N : ℕ}
    (hYN : Y ≤ N) :
    pmPowerDampedDivisorRemainder ε N =
      -(∑ d ∈ Icc 1 Y, pmPowerDampedMobiusCoeff ε d *
        ((Int.fract ((N : ℝ)/d) : ℝ) : ℂ)) +
      (∑ k ∈ Icc 1 (N/(Y+1)), ∑ d ∈ Ioc Y (N/k), pmPowerDampedMobiusCoeff ε d) -
      (N : ℂ)*(∑' k : ℕ,
        pmPowerDampedMobiusCoeff ε (k+(Y+1))/((k+(Y+1) : ℕ) : ℂ)) := by
  have hs := (summable_pmPowerDampedDivisorDensity_terms hε).sum_add_tsum_nat_add (Y+1)
  have hrange : range (Y+1) = insert 0 (Icc 1 Y) := by
    ext n
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hrange, Finset.sum_insert (by simp), pmPowerDampedMobiusCoeff_zero,
    zero_div, zero_add, ← pmPowerDampedDivisorDensity_eq_tsum hε] at hs
  have hsplit : Icc 1 N = Icc 1 Y ∪ Ioc Y N := by
    ext n
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hdisj : Disjoint (Icc 1 Y) (Ioc Y N) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have := (mem_Icc.mp hn).2
    have := (mem_Ioc.mp hn').1
    omega
  have hfloor (d : ℕ) : (⌊(N : ℝ)/d⌋ : ℂ) = ((N/d : ℕ) : ℂ) := by
    rw [← Int.natCast_floor_eq_floor (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      Int.cast_natCast, Nat.floor_div_eq_div]
  have hhead : (∑ d ∈ Icc 1 Y, pmPowerDampedMobiusCoeff ε d * ((N/d : ℕ) : ℂ)) -
      (N : ℂ)*(∑ d ∈ Icc 1 Y, pmPowerDampedMobiusCoeff ε d/(d : ℂ)) =
      -(∑ d ∈ Icc 1 Y, pmPowerDampedMobiusCoeff ε d *
        ((Int.fract ((N : ℝ)/d) : ℝ) : ℂ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← hfloor]
    simp only [Int.fract, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast,
      Complex.ofReal_intCast]
    ring
  rw [pmPowerDampedDivisorRemainder, pmPowerDampedDivisorSum_eq_floor_sum ε
    (Nat.cast_nonneg N) (by simp : ⌊(N : ℝ)⌋₊ ≤ N)]
  simp only [hfloor, Complex.ofReal_natCast]
  rw [hs.symm, hsplit, Finset.sum_union hdisj, pmc_floor_tail_swap]
  linear_combination hhead

private theorem pmc_floor_tail_bound {ε : ℝ} (hε : ε < 1) (Y N : ℕ) {B : ℝ}
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
      · apply (pmc_damped_block hε hYk hB).trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by
          exact_mod_cast (Nat.add_le_add_right (Nat.div_le_self N k) 1)) (by linarith)
      · rw [Ioc_eq_empty_of_le (by omega : N/k ≤ Y), sum_empty, norm_zero]
        positivity
    _ = _ := by simp; ring

private theorem pmc_fract_head_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
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

private theorem pmc_remainder_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
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
  have htail := mul_le_mul_of_nonneg_left (pmc_density_tail hε Y hB) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  rw [norm_mul, Complex.norm_natCast]
  have hh := pmc_fract_head_bound hε hε1 Y N
  have hf := pmc_floor_tail_bound hε1 Y N hB
  linarith

private theorem pmc_cutoff {N : ℕ} {L : ℝ} (hN : (1 : ℝ) ≤ N)
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

private theorem pmc_scaled_remainder_bound {ε L B : ℝ} {Y N : ℕ}
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
  have hb := pmc_remainder_bound hε hε1 hYN hB
  nlinarith

/-- Unconditional logarithmic cancellation for the actual small-damping source. -/
theorem pmPowerDampedDivisorRemainder_eventually_log_four {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ‖pmPowerDampedDivisorRemainder ε N‖ ≤
        1+C*(N : ℝ)^(1-ε)/Real.log (N : ℝ)^4 := by
  obtain ⟨A, hA, heA⟩ :=
    Sieve.exists_abs_deningerHarmonicPartial_le_const_div_log_pow 16 (by omega)
  obtain ⟨K, hK⟩ := eventually_atTop.mp heA
  let C₀ : ℝ := A*2^16
  have hC₀ : 0 ≤ C₀ := by positivity
  have hδ : 0 < 1-ε := by linarith
  refine ⟨1/(1-ε)+10*C₀, by positivity, ?_⟩
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (8 : ℝ)
    (by norm_num : (0 : ℝ) < 1/2)).comp_tendsto tendsto_natCast_atTop_atTop).bound
      (c := 1/2) (by norm_num)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hroot := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (K : ℝ)
  filter_upwards [hsmall, hlog, hroot, eventually_ge_atTop 1] with N hsmallN hlogN hrootN hN
  dsimp only [Function.comp_def] at hsmallN hlogN hrootN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hNR
  have hl0 : 0 < Real.log (N : ℝ) := by linarith
  have hl1 : 1 ≤ Real.log (N : ℝ) := by linarith
  let L := Real.log (N : ℝ)^8
  let Y := ⌊(N : ℝ)/L⌋₊
  have hL1 : 1 ≤ L := one_le_pow₀ hl1
  have hL : L ≤ Real.sqrt N/2 := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hN0.le _),
      show Real.log (N : ℝ)^(8 : ℝ) = Real.log (N : ℝ)^8 from Real.rpow_natCast _ 8,
      ← Real.sqrt_eq_rpow] at hsmallN
    dsimp only [L]
    linarith
  obtain ⟨hYN, hYs, hY, hJ⟩ := pmc_cutoff hNR hL1 hL
  have hYs0 : (0 : ℝ) < Y := (Real.sqrt_pos.2 hN0).trans_le hYs
  have hYK : K ≤ Y := by exact_mod_cast hrootN.trans hYs
  have hlogY : Real.log (N : ℝ)/2 ≤ Real.log (Y : ℝ) := by
    rw [← Real.log_sqrt hN0.le]
    exact Real.log_le_log (Real.sqrt_pos.2 hN0) hYs
  have hB (k : ℕ) (hk : Y ≤ k) :
      |deningerHarmonicPartial k| ≤ C₀/Real.log (N : ℝ)^16 := by
    have hlogk : Real.log (N : ℝ)/2 ≤ Real.log (k : ℝ) :=
      hlogY.trans (Real.log_le_log hYs0 (by exact_mod_cast hk))
    calc
      _ ≤ A/Real.log (k : ℝ)^16 := hK k (hYK.trans hk)
      _ ≤ A/(Real.log (N : ℝ)/2)^16 := div_le_div_of_nonneg_left hA
        (by positivity) (pow_le_pow_left₀ (by positivity) hlogk 16)
      _ = _ := by dsimp only [C₀]; rw [div_pow]; field_simp
  have hb := pmc_scaled_remainder_bound hε (by linarith : ε < 1) hNR hL1 hYN hY hJ hB
  have hp : Real.log (N : ℝ)^4 ≤ L^(1-ε) := by
    calc
      _ = Real.log (N : ℝ)^(4 : ℝ) := (Real.rpow_natCast _ 4).symm
      _ ≤ Real.log (N : ℝ)^((8 : ℝ)*(1-ε)) :=
        Real.rpow_le_rpow_of_exponent_le hl1 (by linarith)
      _ = L^(1-ε) := Real.rpow_natCast_mul hl0.le 8 (1-ε)
  have hhead : (N : ℝ)^(1-ε)/((1-ε)*L^(1-ε)) ≤
      (N : ℝ)^(1-ε)/((1-ε)*Real.log (N : ℝ)^4) := by
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) (by positivity)
      (mul_le_mul_of_nonneg_left hp hδ.le)
  have hpow : Real.log (N : ℝ)^4 ≤ Real.log (N : ℝ)^8 := by
    have hp4 : 1 ≤ Real.log (N : ℝ)^4 := one_le_pow₀ hl1
    nlinarith [sq_nonneg (Real.log (N : ℝ)^4-1),
      show (Real.log (N : ℝ)^4)^2 = Real.log (N : ℝ)^8 by ring]
  have htail : 10*(C₀/Real.log (N : ℝ)^16)*L*(N : ℝ)^(1-ε) ≤
      10*C₀*(N : ℝ)^(1-ε)/Real.log (N : ℝ)^4 := by
    calc
      _ = 10*C₀*(N : ℝ)^(1-ε)/Real.log (N : ℝ)^8 := by
        dsimp only [L]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
  calc
    _ ≤ 1+(N : ℝ)^(1-ε)/((1-ε)*Real.log (N : ℝ)^4) +
        10*C₀*(N : ℝ)^(1-ε)/Real.log (N : ℝ)^4 := by linarith
    _ = _ := by field_simp; ring

private theorem pmc_tail_weight_term {ε β : ℝ} (hε : 0 < ε) (hβ : 0 ≤ β)
    {Q d m : ℕ} (hQ : 0 < Q) (hd : 0 < d) (hm : Q < d*m) :
    ‖(moebius m : ℂ)*pmPowerDampedRamanujanWeight ε (d*m)‖ ≤
      (Q : ℝ)^(-β)*(d : ℝ)^(-(1+ε-β))*(m : ℝ)^(-(1+ε-β)) := by
  have hm0 : 0 < m := by nlinarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hdmR : (0 : ℝ) < (d*m : ℕ) := by exact_mod_cast (Nat.mul_pos hd hm0)
  have hmu : ‖(moebius m : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := m))
  calc
    _ ≤ ‖pmPowerDampedRamanujanWeight ε (d*m)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hmu
    _ ≤ 1/((d*m : ℕ) : ℝ)^(1+ε) := norm_pmPowerDampedRamanujanWeight_le hε (Nat.mul_pos hd hm0)
    _ = ((d*m : ℕ) : ℝ)^(-β)*((d*m : ℕ) : ℝ)^(-(1+ε-β)) := by
      rw [one_div, ← Real.rpow_neg hdmR.le, ← Real.rpow_add hdmR]
      congr 1
      ring
    _ ≤ (Q : ℝ)^(-β)*((d*m : ℕ) : ℝ)^(-(1+ε-β)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hdmR.le _)
      exact Real.rpow_le_rpow_of_nonpos hQR (by exact_mod_cast hm.le) (neg_nonpos.mpr hβ)
    _ = _ := by rw [Nat.cast_mul, Real.mul_rpow hdR.le hmR.le]; ring

private theorem pmc_cofactor_truncation_bound {ε β : ℝ} (hε : 0 < ε)
    (hβ : 0 ≤ β) (hβε : β < ε) {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) :
    ‖pmPowerDampedRamanujanCofactor ε Q d-pmPowerDampedMobiusCoeff ε d‖ ≤
      (Q : ℝ)^(-β)*(d : ℝ)^(-(ε-β)) *
        (∑' m : ℕ, (m : ℝ)^(-(1+ε-β))) := by
  let f : ℕ → ℂ := fun m => (moebius m : ℂ)*pmPowerDampedRamanujanWeight ε (d*m)
  have hf : Summable f :=
    (hasSum_norm_pmPowerDampedRamanujanWeight_multiples hε hd).summable.of_norm_bounded (by
      intro m
      dsimp only [f]
      rw [norm_mul]
      apply mul_le_of_le_one_left (norm_nonneg _)
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := m)))
  have hs := hf.sum_add_tsum_nat_add (Q/d+1)
  have hrange (J : ℕ) : range (J+1) = insert 0 (Icc 1 J) := by
    ext n
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hrange, Finset.sum_insert (by simp)] at hs
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0, zero_add] at hs
  have hinv : (∑' m, f m) = pmPowerDampedMobiusCoeff ε d/(d : ℂ) :=
    pmPowerDampedRamanujanWeight_multiples_inversion hε d
  rw [hinv] at hs
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : pmPowerDampedRamanujanCofactor ε Q d-pmPowerDampedMobiusCoeff ε d =
      -(d : ℂ)*(∑' k : ℕ, f (k+(Q/d+1))) := by
    dsimp only [pmPowerDampedRamanujanCofactor]
    change (d : ℂ)*(∑ m ∈ Icc 1 (Q/d), f m)-pmPowerDampedMobiusCoeff ε d = _
    have hh := congrArg (fun z : ℂ => (d : ℂ)*z) hs
    simp only [mul_div_cancel₀ _ hdc] at hh
    linear_combination hh
  let g : ℕ → ℝ := fun m => (m : ℝ)^(-(1+ε-β))
  have hg : Summable g := Real.summable_nat_rpow.mpr (by linarith)
  have hgs := (summable_nat_add_iff (Q/d+1)).mpr hg
  have hmaj (k : ℕ) : ‖f (k+(Q/d+1))‖ ≤
      ((Q : ℝ)^(-β)*(d : ℝ)^(-(1+ε-β)))*g (k+(Q/d+1)) := by
    apply pmc_tail_weight_term hε hβ hQ hd
    have hh : Q/d < k+(Q/d+1) := by omega
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd).mp hh
  have hb := Summable.tsum_le_tsum hmaj ((summable_nat_add_iff (Q/d+1)).mpr hf).norm
    (hgs.mul_left ((Q : ℝ)^(-β)*(d : ℝ)^(-(1+ε-β))))
  rw [tsum_mul_left] at hb
  have hshift : (∑' k : ℕ, g (k+(Q/d+1))) ≤ ∑' k : ℕ, g k := by
    exact tsum_comp_le_tsum_of_inj hg (fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun a b h => Nat.add_right_cancel h)
  have htail := (norm_tsum_le_tsum_norm ((summable_nat_add_iff (Q/d+1)).mpr hf).norm).trans
    (hb.trans (mul_le_mul_of_nonneg_left hshift (by positivity)))
  rw [he, norm_mul, norm_neg, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg d)).trans_eq
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  calc
    (d : ℝ)*((Q : ℝ)^(-β)*(d : ℝ)^(-(1+ε-β))*(∑' m, g m)) =
        (Q : ℝ)^(-β)*((d : ℝ)^(1 : ℝ)*(d : ℝ)^(-(1+ε-β)))*(∑' m, g m) := by
      rw [Real.rpow_one]
      ring
    _ = _ := by rw [← Real.rpow_add hdR, show (1 : ℝ)+ -(1+ε-β) = -(ε-β) by ring]

/-- Natural denominator truncation retains a power-saving source error whenever `β < ε`. -/
theorem norm_pmPowerDampedRamanujanCumulativePrefix_sub_remainder_le {ε β : ℝ} (hε : 0 < ε)
    (hβ : 0 ≤ β) (hβε : β < ε) {Q N : ℕ} (hQ : 0 < Q) (hNQ : N ≤ Q) :
    ‖pmPowerDampedRamanujanCumulativePrefix ε (Q-1) N-pmPowerDampedDivisorRemainder ε N‖ ≤
      (N : ℝ)*(Q : ℝ)^(-β)*(∑' m : ℕ, (m : ℝ)^(-(1+ε-β)))^2 := by
  let g : ℕ → ℝ := fun m => (m : ℝ)^(-(1+ε-β))
  let C : ℝ := ∑' m : ℕ, g m
  have hg : Summable g := Real.summable_nat_rpow.mpr (by linarith)
  have hC : 0 ≤ C := tsum_nonneg (fun m => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hfloor (d : ℕ) : (⌊(N : ℝ)/d⌋ : ℂ) = ((N/d : ℕ) : ℂ) := by
    rw [← Int.natCast_floor_eq_floor (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      Int.cast_natCast, Nat.floor_div_eq_div]
  have hsub : (∑ d ∈ Icc 1 Q, pmPowerDampedRamanujanCofactor ε Q d*((N/d : ℕ) : ℂ)) =
      ∑ d ∈ Icc 1 N, pmPowerDampedRamanujanCofactor ε Q d*((N/d : ℕ) : ℂ) := by
    symm
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right hNQ)
    intro d hd hnot
    have hNd : N < d := by
      have := (mem_Icc.mp hd).1
      simp only [mem_Icc, not_and] at hnot
      omega
    simp [Nat.div_eq_of_lt hNd]
  rw [pmPowerDampedRamanujanCumulativePrefix_eq_cofactor_floor hε,
    Nat.sub_add_cancel hQ, hsub, pmPowerDampedDivisorRemainder,
    pmPowerDampedDivisorSum_eq_floor_sum ε (Nat.cast_nonneg N) (by simp : ⌊(N : ℝ)⌋₊ ≤ N)]
  simp only [hfloor, Complex.ofReal_natCast, sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib,
    ← sub_mul]
  calc
    _ ≤ ∑ d ∈ Icc 1 N,
        ‖(pmPowerDampedRamanujanCofactor ε Q d-pmPowerDampedMobiusCoeff ε d)*((N/d : ℕ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Icc 1 N, (N : ℝ)*(Q : ℝ)^(-β)*C*g d := by
      apply Finset.sum_le_sum
      intro d hd
      have hd0 : 0 < d := (mem_Icc.mp hd).1
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
      have hb := pmc_cofactor_truncation_bound hε hβ hβε hQ hd0
      have hf : ((N/d : ℕ) : ℝ) ≤ (N : ℝ)/d := by
        simpa only [Nat.floor_div_eq_div] using
          (Nat.floor_le (by positivity : (0 : ℝ) ≤ (N : ℝ)/d))
      rw [norm_mul, Complex.norm_natCast]
      apply (mul_le_mul hb hf (Nat.cast_nonneg _) (by positivity)).trans_eq
      have he : (d : ℝ)^(-(ε-β))/(d : ℝ) = g d := by
        dsimp only [g]
        calc
          _ = (d : ℝ)^(-(ε-β))/(d : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_sub hdR]; congr 1; ring
      calc
        _ = (N : ℝ)*(Q : ℝ)^(-β)*C*((d : ℝ)^(-(ε-β))/(d : ℝ)) := by ring
        _ = _ := by rw [he]
    _ = (N : ℝ)*(Q : ℝ)^(-β)*C*(∑ d ∈ Icc 1 N, g d) := by rw [Finset.mul_sum]
    _ ≤ (N : ℝ)*(Q : ℝ)^(-β)*C*C := by
      apply mul_le_mul_of_nonneg_left (hg.sum_le_tsum _ (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
      positivity
    _ = _ := by dsimp only [C, g]; ring

end RHTower
