import GaloisForLFunctions.ArithmeticDefectRigidity.TheRenormalizedCofactorActsOnPowerRowsByZeta
import GaloisForLFunctions.ArithmeticDefectRigidity.TheCofactorLimitCarriesACyclicDilationAction

/-!
# The eta renormalization of the cofactor is pole-free

The 2-adic Euler factor `1 − 2^{1−ε}D₂` removes the cofactor pole without any trace. The
alternating cofactor sum
`H_ε v(n) = Σ_{j≤n} (−1)^{j+1} j^{-ε} v(⌊n/j⌋) = Σ_{j≤n} j^{-ε}v(⌊n/j⌋) − 2^{1−ε} Σ_{i≤n/2} i^{-ε} v(⌊⌊n/2⌋/i⌋)`
(`etaCofactorSum_eq`) is defined on every row and needs no domain or trace. On the actual receiver
it is `(I − 2^{1−ε}D₂)ρ_ε`; the pole power `c_ε n^{1−ε}` is cancelled exactly by `2^{1−ε}(n/2)^{1−ε}`,
so `H_ε A` is paid at every horizon (`exists_pronicNorm_etaCofactorSum_actual_le`). On power rows
`H_ε n^s = η(s + ε) n^s` modulo admitted rows, `η(z) = (1 − 2^{1−z})ζ(z)` the alternating zeta
function (`exists_pronicNorm_etaCofactorSum_powerRow_le`).

The tail of the alternating sum pairs consecutive dilations:
`Σ_{j>J} (−1)^{j+1} j^{-ε} D_j v = Σ_{odd j>J} [j^{-ε}(D_j − D_{j+1})v + (j^{-ε} − (j+1)^{-ε})D_{j+1}v]`,
so its pronic norm is controlled by the dilation modulus of continuity
(`pronicNorm_etaCofactorTail_le`). For an escaping actual limit the alternating cofactor packet is
bounded by the normalized eta tail (`alternatingPacket_le_of_tail`): the moving cofactor tail of
the joint extraction problem is exactly a dilation-regularity question.
-/

open Finset Filter Topology Complex RHTower
open GaloisForLFunctions.BezoutValuationIncidence (pronicNorm pronicNorm_nonneg pronicNorm_sq
  pronicNorm_add_le)
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The total cofactor sum `Σ_{j≤n} j^{-ε} v(⌊n/j⌋)`. -/
def totalCofactorSum (ε : ℝ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 n, (j : ℝ) ^ (-ε) * v (n / j)

/-- The alternating (eta) cofactor sum `Σ_{j≤n} (−1)^{j+1} j^{-ε} v(⌊n/j⌋)`. -/
def etaCofactorSum (ε : ℝ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 n, (-1 : ℝ) ^ (j + 1) * (j : ℝ) ^ (-ε) * v (n / j)

/-- **The 2-adic factorization.** `H_ε v(n) = S v(n) − 2^{1−ε} S v(⌊n/2⌋)`, `S` the total sum. -/
theorem etaCofactorSum_eq (ε : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    etaCofactorSum ε v n = totalCofactorSum ε v n -
      (2 : ℝ) ^ (1 - ε) * totalCofactorSum ε v (n / 2) := by
  -- `(−1)^{j+1} = 1 − 2·[2 ∣ j]`
  have hsign : ∀ j : ℕ, (-1 : ℝ) ^ (j + 1) = 1 - 2 * (if 2 ∣ j then 1 else 0) := by
    intro j
    rcases Nat.even_or_odd j with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [if_pos ⟨k, by ring⟩, pow_succ, ← two_mul, pow_mul]; norm_num
    · rw [if_neg (by omega), show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]; norm_num
  have heven : ∑ j ∈ Icc 1 n, (if 2 ∣ j then 1 else 0) * ((j : ℝ) ^ (-ε) * v (n / j)) =
      ∑ i ∈ Icc 1 (n / 2), ((2 * i : ℕ) : ℝ) ^ (-ε) * v (n / 2 / i) := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [← sum_filter]
    refine sum_nbij' (fun j => j / 2) (fun i => 2 * i) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [mem_filter, mem_Icc] at hj ⊢
      obtain ⟨⟨hj1, hjn⟩, ⟨k, rfl⟩⟩ := hj
      omega
    · intro i hi
      simp only [mem_filter, mem_Icc] at hi ⊢
      exact ⟨⟨by omega, by omega⟩, ⟨i, rfl⟩⟩
    · intro j hj
      simp only [mem_filter] at hj
      obtain ⟨-, ⟨k, rfl⟩⟩ := hj
      omega
    · intro i _; omega
    · intro j hj
      simp only [mem_filter] at hj
      obtain ⟨-, ⟨k, rfl⟩⟩ := hj
      rw [show 2 * k / 2 = k by omega, Nat.div_div_eq_div_mul]
  have hpow : ∀ i : ℕ, ((2 * i : ℕ) : ℝ) ^ (-ε) = (2 : ℝ) ^ (-ε) * (i : ℝ) ^ (-ε) := fun i => by
    push_cast; exact Real.mul_rpow (by norm_num) (Nat.cast_nonneg i)
  rw [etaCofactorSum, totalCofactorSum, totalCofactorSum]
  simp_rw [hsign, sub_mul, mul_assoc, sum_sub_distrib, one_mul]
  rw [← mul_sum, heven, mul_sum, mul_sum]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [hpow, show (2 : ℝ) ^ (1 - ε) = 2 * (2 : ℝ) ^ (-ε) by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num)]; ring]
  ring

/-! ### The actual receiver: a paid, trace-free inversion law -/

/-- The total cofactor sum of the actual receiver is the forcing `ρ_ε = c_ε n^{1−ε} + R_ε`. -/
theorem totalCofactorSum_actual (ε : SubcriticalDamping) {n : ℕ} (hn : 1 ≤ n) :
    totalCofactorSum ε (pmPowerDampedCenteredDivisorPrefix ε) n =
      forcingPower ε n + forcingRemainder ε n := by
  rw [totalCofactorSum, sum_rpow_mul_centeredPrefix_split (ε : ℝ) hn,
    ← inversionDefect_eq_centeredPrefix_add_offDiagonal (ε : ℝ) hn, forcingRemainder]
  ring

theorem totalCofactorSum_zero (ε : ℝ) (v : ℕ → ℝ) : totalCofactorSum ε v 0 = 0 := by
  simp [totalCofactorSum]

/-- **The eta form of the actual inversion law.**
`H_ε A(n) = R(n) − 2^{1−ε}R(⌊n/2⌋) + c_ε(n^{1−ε} − 2^{1−ε}⌊n/2⌋^{1−ε})`. -/
theorem etaCofactorSum_actual_eq (ε : SubcriticalDamping) {n : ℕ} (hn : 1 ≤ n) :
    etaCofactorSum ε (pmPowerDampedCenteredDivisorPrefix ε) n =
      forcingRemainder ε n - (2 : ℝ) ^ (1 - (ε : ℝ)) * forcingRemainder ε (n / 2) +
        forcingPowerCoefficient ε * ((n : ℝ) ^ (1 - (ε : ℝ)) -
          (2 : ℝ) ^ (1 - (ε : ℝ)) * ((n / 2 : ℕ) : ℝ) ^ (1 - (ε : ℝ))) := by
  rw [etaCofactorSum_eq, totalCofactorSum_actual ε hn]
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have h0 : n / 2 = 0 := Nat.div_eq_of_lt hn2
    have hα : 1 - (ε : ℝ) ≠ 0 := by linarith [ε.property.2]
    rw [h0, totalCofactorSum_zero, forcingRemainder_zero, Nat.cast_zero, Real.zero_rpow hα]
    simp only [forcingPower]; ring
  · rw [totalCofactorSum_actual ε (by omega)]
    simp only [forcingPower]; ring

/-- The cancelled pole: `0 ≤ n^α − 2^α ⌊n/2⌋^α ≤ 1` for `0 < α ≤ 1`. -/
theorem abs_rpow_sub_two_rpow_half_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    |(n : ℝ) ^ α - (2 : ℝ) ^ α * ((n / 2 : ℕ) : ℝ) ^ α| ≤ 1 := by
  have h2 : (2 : ℝ) ^ α * ((n / 2 : ℕ) : ℝ) ^ α = ((2 * (n / 2) : ℕ) : ℝ) ^ α := by
    push_cast; rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
  rw [h2]
  have hle : ((2 * (n / 2) : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.mul_div_le n 2
  have hge : (n : ℝ) - 1 ≤ ((2 * (n / 2) : ℕ) : ℝ) := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ ((2 * (n / 2) : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have hmono : ((2 * (n / 2) : ℕ) : ℝ) ^ α ≤ (n : ℝ) ^ α :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hle hα.le
  rw [abs_of_nonneg (by linarith)]
  -- concavity: `x^α ≤ (x − 1)^α + 1` on `x ≥ 1`
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow hα.ne']
  have hsub : (n : ℝ) ^ α ≤ ((2 * (n / 2) : ℕ) : ℝ) ^ α + 1 := by
    have hsa : ((n : ℝ) - 1 + 1) ^ α ≤ ((n : ℝ) - 1) ^ α + 1 ^ α :=
      Real.rpow_add_le_add_rpow (by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                                    linarith) zero_le_one hα.le hα1
    rw [sub_add_cancel, Real.one_rpow] at hsa
    have hm : ((n : ℝ) - 1) ^ α ≤ ((2 * (n / 2) : ℕ) : ℝ) ^ α :=
      Real.rpow_le_rpow (by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                            linarith) hge hα.le
    linarith
  linarith

theorem sum_Icc_one_div_sub_one_div_succ (T : ℕ) :
    ∑ n ∈ Icc 1 T, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) = 1 - 1 / ((T : ℝ) + 1) := by
  induction T with
  | zero => simp
  | succ T ih => rw [sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- **The eta-form inversion is paid without a trace.** `‖H_ε A‖_T ≤ 2B_ε + c_ε` at every horizon. -/
theorem exists_pronicNorm_etaCofactorSum_actual_le (ε : SubcriticalDamping) :
    ∃ B : ℝ, ∀ T : ℕ, pronicNorm T (etaCofactorSum ε (pmPowerDampedCenteredDivisorPrefix ε)) ≤ B := by
  set α : ℝ := 1 - (ε : ℝ) with hα
  have hα0 : 0 < α := by rw [hα]; linarith [ε.property.2]
  have hα1 : α ≤ 1 := by rw [hα]; linarith [ε.property.1]
  set c := forcingPowerCoefficient ε with hc
  have hc0 : 0 ≤ c := (forcingPowerCoefficient_pos ε).le
  set Bε := forcingRemainderBudget ε
  refine ⟨Bε + (2 : ℝ) ^ α * (Real.sqrt 2 * Bε) + c, fun T => ?_⟩
  have hR : pronicNorm T (forcingRemainder ε) ≤ Bε := pronicNorm_forcingRemainder_le ε T
  have hR2 : pronicNorm T (rowDilate 2 (forcingRemainder ε)) ≤ Real.sqrt 2 * Bε := by
    refine (pronicNorm_rowDilate_le (by norm_num) T _ (forcingRemainder_zero ε)).trans ?_
    rw [show (2 : ℝ) / (2 : ℕ) = 1 by norm_num, Real.sqrt_one, one_mul]
    exact hR.trans (le_mul_of_one_le_left (forcingRemainderBudget_nonneg ε)
      (Real.one_le_sqrt.mpr (by norm_num)))
  have hpole : pronicNorm T (fun n => c * ((n : ℝ) ^ α - (2 : ℝ) ^ α * ((n / 2 : ℕ) : ℝ) ^ α)) ≤
      c := by
    rw [pronicNorm]
    have hsum : ∑ n ∈ Icc 1 T, (c * ((n : ℝ) ^ α - (2 : ℝ) ^ α * ((n / 2 : ℕ) : ℝ) ^ α)) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) ≤ c ^ 2 := by
      have hterm : ∀ n ∈ Icc 1 T, (c * ((n : ℝ) ^ α - (2 : ℝ) ^ α * ((n / 2 : ℕ) : ℝ) ^ α)) ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1)) ≤ c ^ 2 * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hb := abs_rpow_sub_two_rpow_half_le hα0 hα1 n
        have hsq : ((n : ℝ) ^ α - (2 : ℝ) ^ α * ((n / 2 : ℕ) : ℝ) ^ α) ^ 2 ≤ 1 := by
          rw [← sq_abs]; nlinarith [abs_nonneg ((n : ℝ) ^ α - (2 : ℝ) ^ α * ((n / 2 : ℕ) : ℝ) ^ α)]
        rw [show 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * ((n : ℝ) + 1)) by
          field_simp; ring, mul_pow, mul_one_div]
        exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (sq_nonneg c) hsq) (by positivity)
      refine (sum_le_sum hterm).trans ?_
      rw [← mul_sum]
      rw [sum_Icc_one_div_sub_one_div_succ]
      have : 0 ≤ 1 / ((T : ℝ) + 1) := by positivity
      nlinarith [sq_nonneg c]
    calc Real.sqrt _ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hsum
      _ = c := Real.sqrt_sq hc0
  have hcongr : pronicNorm T (etaCofactorSum ε (pmPowerDampedCenteredDivisorPrefix ε)) =
      pronicNorm T (fun n => forcingRemainder ε n + (-(2 : ℝ) ^ α) * rowDilate 2 (forcingRemainder ε) n +
        c * ((n : ℝ) ^ α - (2 : ℝ) ^ α * ((n / 2 : ℕ) : ℝ) ^ α)) :=
    pronicNorm_congr fun n hn => by
      rw [etaCofactorSum_actual_eq ε (mem_Icc.mp hn).1, rowDilate]; ring
  rw [hcongr]
  have h1 := pronicNorm_add_le T (fun n => forcingRemainder ε n +
    (-(2 : ℝ) ^ α) * rowDilate 2 (forcingRemainder ε) n)
    (fun n => c * ((n : ℝ) ^ α - (2 : ℝ) ^ α * ((n / 2 : ℕ) : ℝ) ^ α))
  have h2 := pronicNorm_add_le T (forcingRemainder ε)
    (fun n => (-(2 : ℝ) ^ α) * rowDilate 2 (forcingRemainder ε) n)
  have h3 : pronicNorm T (fun n => (-(2 : ℝ) ^ α) * rowDilate 2 (forcingRemainder ε) n) =
      (2 : ℝ) ^ α * pronicNorm T (rowDilate 2 (forcingRemainder ε)) := by
    have hneg : pronicNorm T (fun n => (-(2 : ℝ) ^ α) * rowDilate 2 (forcingRemainder ε) n) =
        pronicNorm T (fun n => (2 : ℝ) ^ α * rowDilate 2 (forcingRemainder ε) n) := by
      simp only [BezoutValuationIncidence.pronicNorm, neg_mul, neg_sq]
    rw [hneg, pronicNorm_const_mul (by positivity)]
  have h2α : 0 ≤ (2 : ℝ) ^ α := by positivity
  nlinarith [h1, h2, h3, hR, hR2, hpole]

/-! ### The eta symbol on power rows -/

/-- The total cofactor sum of a real power row is the real part of the complex one. -/
theorem totalCofactorSum_powerRow (ε : ℝ) (a s : ℂ) (n : ℕ) :
    totalCofactorSum ε (powerRow a s) n = (a * powerRowCofactorSum ε s n).re := by
  rw [totalCofactorSum, powerRowCofactorSum, mul_sum, Complex.re_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [show (-((ε : ℝ) : ℂ)) = (((-(ε : ℝ)) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (Nat.cast_nonneg j), powerRow, mul_left_comm, Complex.re_ofReal_mul]

/-- The eta symbol `η_ε(s) = (1 − 2^{1−ε−s}) ζ(s + ε)`. -/
def etaSymbol (ε : ℝ) (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ ((1 - ε : ℝ) - s)) * riemannZeta (s + ε)

/-- **The eta symbol law.** For `0 < ε < 1` and `0 < Re s < 1 − ε`, modulo a row of bounded pronic
energy, `H_ε Re(a n^s) = Re(a η_ε(s) n^s)`; no pole term occurs. -/
theorem exists_pronicNorm_etaCofactorSum_powerRow_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (a : ℂ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 - ε) :
    ∃ B : ℝ, ∀ T : ℕ, pronicNorm T (fun n => etaCofactorSum ε (powerRow a s) n -
      powerRow (a * etaSymbol ε s) s n) ≤ B := by
  set α : ℝ := 1 - ε with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  have hα1 : α ≤ 1 := by rw [hα]; linarith
  have hs : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  obtain ⟨K, hK⟩ := norm_powerRowCofactorSum_sub_le hε0 hε1 hs0 hs1
  have hK0 : 0 ≤ K := by
    have h := hK 1 le_rfl
    have : 0 ≤ K * Real.sqrt ((1 : ℕ) : ℝ) ^ (s.re - ε) := (norm_nonneg _).trans h
    simpa using this
  set P := powerPoleTrace ε s
  set Z := riemannZeta (s + ε)
  -- the error of the total sum at a horizon `m`
  set err : ℕ → ℂ := fun m => powerRowCofactorSum ε s m - P * (((m : ℝ)) : ℂ) ^ ((α : ℝ) : ℂ) -
    Z * (((m : ℝ)) : ℂ) ^ s with herr
  have herr_le : ∀ m : ℕ, ‖err m‖ ≤ K * Real.sqrt m ^ (s.re - ε) + ‖powerRowCofactorSum ε s 0‖ := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [herr, powerRowCofactorSum, Complex.zero_cpow hs, Complex.ofReal_zero, Complex.zero_cpow (by exact_mod_cast hα0.ne' : ((α : ℝ) : ℂ) ≠ 0)]
      positivity
    · exact (hK m hm).trans (le_add_of_nonneg_right (norm_nonneg _))
  have hS0 : powerRowCofactorSum ε s 0 = 0 := by simp [powerRowCofactorSum]
  set θ := max (s.re - ε) 0 with hθ
  have hθ1 : θ < 1 := max_lt (by linarith) (by norm_num)
  set C := ‖a‖ * (3 * K + ‖P‖ + 2 * ‖Z‖ * (‖s‖ + 1)) with hC
  refine ⟨Real.sqrt (C ^ 2 * (1 + 1 / (1 - θ))), fun T => Real.sqrt_le_sqrt
    (TransHorizonIncidenceMechanics.sum_sq_le_of_abs_le_sqrt_rpow (by linarith : 0 < 1 - θ)
      (fun n hn => ?_) T)⟩
  rw [show 1 - (1 - θ) = θ by ring]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hpowθ : Real.sqrt n ^ (s.re - ε) ≤ Real.sqrt n ^ θ :=
    Real.rpow_le_rpow_of_exponent_le hsq1 (le_max_left _ _)
  have honeθ : 1 ≤ Real.sqrt n ^ θ := Real.one_le_rpow hsq1 (le_max_right _ _)
  set h := n / 2 with hh
  -- the two expansion errors
  have herrn : ‖err n‖ ≤ K * Real.sqrt n ^ θ :=
    (hK n hn).trans (mul_le_mul_of_nonneg_left hpowθ hK0)
  have herrh : ‖err h‖ ≤ K * Real.sqrt n ^ θ := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · have : err h = 0 := by
        rw [h0]; simp [herr, hS0, Complex.zero_cpow hs,
          Complex.zero_cpow (by exact_mod_cast hα0.ne' : ((α : ℝ) : ℂ) ≠ 0)]
      rw [this, norm_zero]; positivity
    · have hsqh : 1 ≤ Real.sqrt h := Real.one_le_sqrt.mpr (by exact_mod_cast hpos)
      have hhn : Real.sqrt h ≤ Real.sqrt n :=
        Real.sqrt_le_sqrt (by exact_mod_cast Nat.div_le_self n 2)
      calc ‖err h‖ ≤ K * Real.sqrt h ^ (s.re - ε) := hK h hpos
        _ ≤ K * Real.sqrt h ^ θ :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hsqh (le_max_left _ _)) hK0
        _ ≤ K * Real.sqrt n ^ θ :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hhn (le_max_right _ _)) hK0
  -- the rounding of `(n/2)^s`
  have hround : ‖(((n : ℝ) / 2 : ℝ) : ℂ) ^ s - (((h : ℕ) : ℝ) : ℂ) ^ s‖ ≤ ‖s‖ + 1 := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · rw [h0, Nat.cast_zero, Complex.ofReal_zero, Complex.zero_cpow hs, sub_zero,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      have : (n : ℝ) / 2 ≤ 1 := by
        have : n < 2 := by omega
        have : (n : ℝ) < 2 := by exact_mod_cast this
        linarith
      have := Real.rpow_le_one (by positivity) this hs0.le
      have := norm_nonneg s
      linarith
    · have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hpos
      have hle : ((h : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
        rw [hh]; exact Nat.cast_div_le
      have hlt : (n : ℝ) / 2 - ((h : ℕ) : ℝ) ≤ 1 := by
        have := (abs_le.mp (RHTower.Sieve.abs_natDiv_sub_div_le (N := n) (d := 2) (by norm_num))).1
        push_cast at this; rw [hh]; linarith
      have hmv := norm_ofReal_cpow_sub_le (z := s) (by linarith) hh0 le_rfl hle
      have hp : ((h : ℕ) : ℝ) ^ (s.re - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hpos) (by linarith)
      have hgap : 0 ≤ (n : ℝ) / 2 - ((h : ℕ) : ℝ) := by linarith
      calc _ ≤ ‖s‖ * ((h : ℕ) : ℝ) ^ (s.re - 1) * ((n : ℝ) / 2 - ((h : ℕ) : ℝ)) := hmv
        _ ≤ ‖s‖ * 1 * 1 := by gcongr
        _ ≤ ‖s‖ + 1 := by linarith
  -- the algebraic identity
  have h2s : (2 : ℂ) ^ ((α : ℝ) - s) * (((n : ℝ)) : ℂ) ^ s =
      (((2 : ℝ) ^ α : ℝ) : ℂ) * (((n : ℝ) / 2 : ℝ) : ℂ) ^ s := by
    rw [TransHorizonIncidenceMechanics.ofReal_div_cpow hn0 (by norm_num : (0 : ℝ) < 2),
      Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2), show ((α : ℝ) : ℂ) - s = (α : ℂ) + -s by ring,
      Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    push_cast; ring
  have hident : etaCofactorSum ε (powerRow a s) n - powerRow (a * etaSymbol ε s) s n =
      (a * (P * ((((n : ℝ) ^ α - (2 : ℝ) ^ α * ((h : ℕ) : ℝ) ^ α : ℝ)) : ℂ) +
        Z * ((((2 : ℝ) ^ α : ℝ) : ℂ) * ((((n : ℝ) / 2 : ℝ) : ℂ) ^ s - (((h : ℕ) : ℝ) : ℂ) ^ s)) +
        err n - (((2 : ℝ) ^ α : ℝ) : ℂ) * err h)).re := by
    rw [etaCofactorSum_eq, totalCofactorSum_powerRow, totalCofactorSum_powerRow, powerRow,
      etaSymbol, ← hα]
    have hSn : powerRowCofactorSum ε s n = P * (((n : ℝ)) : ℂ) ^ ((α : ℝ) : ℂ) +
        Z * (((n : ℝ)) : ℂ) ^ s + err n := by rw [herr]; ring
    have hSh : powerRowCofactorSum ε s h = P * (((h : ℕ) : ℝ) : ℂ) ^ ((α : ℝ) : ℂ) +
        Z * (((h : ℕ) : ℝ) : ℂ) ^ s + err h := by rw [herr]; ring
    rw [hSn, hSh, ← Complex.ofReal_cpow (Nat.cast_nonneg n),
      ← Complex.ofReal_cpow (Nat.cast_nonneg h)]
    rw [← Complex.re_ofReal_mul, ← Complex.sub_re, ← Complex.sub_re]
    congr 1
    have hZ : a * ((1 - (2 : ℂ) ^ ((α : ℝ) - s)) * Z) * (((n : ℝ)) : ℂ) ^ s =
        a * Z * (((n : ℝ)) : ℂ) ^ s - a * Z * ((2 : ℂ) ^ ((α : ℝ) - s) * (((n : ℝ)) : ℂ) ^ s) := by
      ring
    rw [hZ, h2s]
    push_cast
    ring
  rw [hident, hC, mul_assoc]
  refine (Complex.abs_re_le_norm _).trans ?_
  have h2α : (2 : ℝ) ^ α ≤ 2 := by
    calc (2 : ℝ) ^ α ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
      _ = 2 := Real.rpow_one 2
  have h2α0 : 0 ≤ (2 : ℝ) ^ α := by positivity
  have hpole := abs_rpow_sub_two_rpow_half_le hα0 hα1 n
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hnorm2 : ‖((((2 : ℝ) ^ α : ℝ)) : ℂ)‖ = (2 : ℝ) ^ α := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2α0]
  calc ‖P * ((((n : ℝ) ^ α - (2 : ℝ) ^ α * ((h : ℕ) : ℝ) ^ α : ℝ)) : ℂ) +
        Z * ((((2 : ℝ) ^ α : ℝ) : ℂ) * ((((n : ℝ) / 2 : ℝ) : ℂ) ^ s - (((h : ℕ) : ℝ) : ℂ) ^ s)) +
        err n - (((2 : ℝ) ^ α : ℝ) : ℂ) * err h‖
      ≤ ‖P‖ * 1 + ‖Z‖ * (2 * (‖s‖ + 1)) + K * Real.sqrt n ^ θ + 2 * (K * Real.sqrt n ^ θ) := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add ?_ ?_)) herrn)) ?_)
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hpole (norm_nonneg _)
        · rw [norm_mul, norm_mul, hnorm2]
          exact mul_le_mul_of_nonneg_left (mul_le_mul h2α hround (norm_nonneg _) (by norm_num))
            (norm_nonneg _)
        · rw [norm_mul, hnorm2]
          exact mul_le_mul h2α herrh (norm_nonneg _) (by norm_num)
    _ ≤ (3 * K + ‖P‖ + 2 * ‖Z‖ * (‖s‖ + 1)) * Real.sqrt n ^ θ := by
        have hP0 := norm_nonneg P
        have hZ0 : 0 ≤ ‖Z‖ * (2 * (‖s‖ + 1)) := by positivity
        nlinarith

/-! ### The paired tail -/

/-- Pairing consecutive terms: `Σ_{j∈(2K, 2T]} g(j) = Σ_{i∈[K, T)} (g(2i+1) + g(2i+2))`. -/
theorem sum_Ioc_two_mul_eq_pairs (g : ℕ → ℝ) (K T : ℕ) :
    ∑ j ∈ Ioc (2 * K) (2 * T), g j = ∑ i ∈ Ico K T, (g (2 * i + 1) + g (2 * i + 2)) := by
  rcases le_or_gt K T with hKT | hKT
  · induction T, hKT using Nat.le_induction with
    | base => simp
    | succ T hKT ih =>
      rw [show 2 * (T + 1) = 2 * T + 1 + 1 by ring, sum_Ioc_succ_top (by omega),
        sum_Ioc_succ_top (by omega), ih, sum_Ico_succ_top hKT]
      ring
  · rw [Finset.Ioc_eq_empty (by omega), Finset.Ico_eq_empty (by omega)]
    simp

/-- **The eta tail is a series of consecutive dilation differences.** For `ε ≥ 0`, `v(0) = 0`:
`‖Σ_{2K<j≤n} (−1)^{j+1} j^{-ε} v(⌊n/j⌋)‖_T ≤ Σ_{K≤i<T} [(2i+1)^{-ε}‖D_{2i+1}v − D_{2i+2}v‖_T +
  ((2i+1)^{-ε} − (2i+2)^{-ε})‖D_{2i+2}v‖_T]`. -/
theorem pronicNorm_etaCofactorTail_le {ε : ℝ} (hε : 0 ≤ ε) {v : ℕ → ℝ} (hv0 : v 0 = 0)
    (K T : ℕ) :
    pronicNorm T (fun n => ∑ j ∈ Ioc (2 * K) n, (-1 : ℝ) ^ (j + 1) * (j : ℝ) ^ (-ε) * v (n / j)) ≤
      ∑ i ∈ Ico K T, (((2 * i + 1 : ℕ) : ℝ) ^ (-ε) *
          pronicNorm T (fun n => v (n / (2 * i + 1)) - v (n / (2 * i + 2))) +
        (((2 * i + 1 : ℕ) : ℝ) ^ (-ε) - ((2 * i + 2 : ℕ) : ℝ) ^ (-ε)) *
          pronicNorm T (rowDilate (2 * i + 2) v)) := by
  set f : ℕ → ℕ → ℝ := fun j n => (-1 : ℝ) ^ (j + 1) * (j : ℝ) ^ (-ε) * v (n / j) with hf
  have hvanish : ∀ j n, n < j → f j n = 0 := fun j n h => by simp [hf, Nat.div_eq_of_lt h, hv0]
  have hrow : ∀ n ∈ Icc 1 T, ∑ j ∈ Ioc (2 * K) n, f j n =
      ∑ i ∈ Ico K T, ((((2 * i + 1 : ℕ) : ℝ) ^ (-ε)) * (v (n / (2 * i + 1)) - v (n / (2 * i + 2))) +
        (((2 * i + 1 : ℕ) : ℝ) ^ (-ε) - ((2 * i + 2 : ℕ) : ℝ) ^ (-ε)) *
          rowDilate (2 * i + 2) v n) := by
    intro n hn
    have hnT := (mem_Icc.mp hn).2
    have hext : ∑ j ∈ Ioc (2 * K) n, f j n = ∑ j ∈ Ioc (2 * K) (2 * T), f j n := by
      rcases le_or_gt n (2 * K) with hnK | hnK
      · rw [Finset.Ioc_eq_empty (by omega), sum_empty]
        exact (sum_eq_zero fun j hj => hvanish j n (by simp only [mem_Ioc] at hj; omega)).symm
      · rw [← Finset.sum_Ioc_consecutive _ (by omega : 2 * K ≤ n) (by omega : n ≤ 2 * T)]
        rw [sum_eq_zero (s := Ioc n (2 * T)) fun j hj => hvanish j n (by simp only [mem_Ioc] at hj; omega),
          add_zero]
    rw [hext, sum_Ioc_two_mul_eq_pairs (fun j => f j n)]
    refine sum_congr rfl fun i _ => ?_
    have e1 : (-1 : ℝ) ^ (2 * i + 1 + 1) = 1 := Even.neg_one_pow ⟨i + 1, by ring⟩
    have e2 : (-1 : ℝ) ^ (2 * i + 2 + 1) = -1 := Odd.neg_one_pow ⟨i + 1, by ring⟩
    show (-1 : ℝ) ^ (2 * i + 1 + 1) * ((2 * i + 1 : ℕ) : ℝ) ^ (-ε) * v (n / (2 * i + 1)) +
        (-1 : ℝ) ^ (2 * i + 2 + 1) * ((2 * i + 2 : ℕ) : ℝ) ^ (-ε) * v (n / (2 * i + 2)) =
      ((2 * i + 1 : ℕ) : ℝ) ^ (-ε) * (v (n / (2 * i + 1)) - v (n / (2 * i + 2))) +
        (((2 * i + 1 : ℕ) : ℝ) ^ (-ε) - ((2 * i + 2 : ℕ) : ℝ) ^ (-ε)) * v (n / (2 * i + 2))
    rw [e1, e2]
    ring
  rw [pronicNorm_congr hrow]
  refine (pronicNorm_sum_le T _ _).trans (sum_le_sum fun i _ => ?_)
  refine (pronicNorm_add_le T _ _).trans (add_le_add ?_ ?_)
  · rw [pronicNorm_const_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  · rw [pronicNorm_const_mul (sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos (by positivity)
      (by push_cast; linarith) (by linarith)))]

/-! ### The alternating packet of an escaping limit -/

/-- The alternating coefficients `a_j = (−1)^{j+1} j^{-ε}`. -/
def alternatingCoeff (ε : ℝ) (j : ℕ+) : ℝ := (-1 : ℝ) ^ ((j : ℕ) + 1) * ((j : ℕ) : ℝ) ^ (-ε)

/-- The first `2K` positive indices. -/
def alternatingSupport (K : ℕ) : Finset ℕ+ := (Icc 1 (2 * K)).image Nat.toPNat'

theorem sum_alternatingSupport (K : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ alternatingSupport K, f j = ∑ j ∈ Icc 1 (2 * K), f j := by
  have hinj : Set.InjOn Nat.toPNat' (Icc 1 (2 * K) : Finset ℕ) := by
    intro x hx y hy hxy
    have h := congrArg PNat.val hxy
    have hx0 : 0 < x := (mem_Icc.mp hx).1
    have hy0 : 0 < y := (mem_Icc.mp hy).1
    rwa [Nat.toPNat'_coe, Nat.toPNat'_coe, if_pos hx0, if_pos hy0] at h
  rw [alternatingSupport, sum_image hinj]
  refine sum_congr rfl fun x hx => ?_
  have hx0 : 0 < x := (mem_Icc.mp hx).1
  rw [Nat.toPNat'_coe, if_pos hx0]

/-- **The alternating packet of an escaping limit is bounded by the normalized eta tail.** If along
the extraction the eta tail beyond `2K` has pronic norm at most `τ √E_T` eventually, then the
alternating cofactor packet `Σ_{j≤2K} (−1)^{j+1} j^{-ε} v_j` of the limit has squared norm `≤ τ²`. -/
theorem alternatingPacket_le_of_tail (ε : SubcriticalDamping) (L : ActualCofactorLimit ε)
    (hesc : Tendsto (fun m => dampedMobiusEnergy ε (L.subsequence m + 1)) atTop atTop)
    {K : ℕ} {τ : ℝ}
    (htail : ∀ᶠ m in atTop, pronicNorm (L.subsequence m + 1) (fun n => ∑ j ∈ Ioc (2 * K) n,
      (-1 : ℝ) ^ (j + 1) * (j : ℝ) ^ (-(ε : ℝ)) * pmPowerDampedCenteredDivisorPrefix ε (n / j)) ≤
        τ * Real.sqrt (dampedMobiusEnergy ε (L.subsequence m + 1))) :
    ∑ j ∈ alternatingSupport K, ∑ k ∈ alternatingSupport K,
      alternatingCoeff ε j * alternatingCoeff ε k * L.kernel j k ≤ τ ^ 2 := by
  obtain ⟨B, hB⟩ := exists_pronicNorm_etaCofactorSum_actual_le ε
  set A := pmPowerDampedCenteredDivisorPrefix ε with hA
  have hB0 : 0 ≤ B := (pronicNorm_nonneg 0 _).trans (hB 0)
  -- the packet row is the eta sum minus its tail
  have hsplit : ∀ T : ℕ, ∀ n ∈ Icc 1 T, ∑ j ∈ alternatingSupport K, alternatingCoeff ε j * A (n / j) =
      etaCofactorSum ε A n - ∑ j ∈ Ioc (2 * K) n,
        (-1 : ℝ) ^ (j + 1) * (j : ℝ) ^ (-(ε : ℝ)) * A (n / j) := by
    intro T n _
    have h1 : ∑ j ∈ alternatingSupport K, alternatingCoeff ε j * A (n / j) =
        ∑ j ∈ Icc 1 (2 * K), (-1 : ℝ) ^ (j + 1) * (j : ℝ) ^ (-(ε : ℝ)) * A (n / j) :=
      sum_alternatingSupport K (fun j => (-1 : ℝ) ^ (j + 1) * (j : ℝ) ^ (-(ε : ℝ)) * A (n / j))
    rw [h1, etaCofactorSum]
    rcases le_or_gt n (2 * K) with hnK | hnK
    · rw [Finset.Ioc_eq_empty (by omega), sum_empty, sub_zero]
      have hsub : Icc 1 (2 * K) = Icc 1 n ∪ Ioc n (2 * K) := by
        ext j; simp only [mem_union, mem_Icc, mem_Ioc]; omega
      rw [hsub, sum_union (disjoint_left.mpr fun j h1 h2 => by
        simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
      rw [sum_eq_zero (s := Ioc n (2 * K)) fun j hj => by
        simp only [mem_Ioc] at hj
        simp [hA, Nat.div_eq_of_lt hj.1], add_zero]
    · have hsub : Icc 1 n = Icc 1 (2 * K) ∪ Ioc (2 * K) n := by
        ext j; simp only [mem_union, mem_Icc, mem_Ioc]; omega
      rw [hsub, sum_union (disjoint_left.mpr fun j h1 h2 => by
        simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
      ring
  -- normalized packet bound at each horizon of the extraction
  have hbound : ∀ᶠ m in atTop, Real.sqrt (∑ j ∈ alternatingSupport K, ∑ k ∈ alternatingSupport K,
      alternatingCoeff ε j * alternatingCoeff ε k * cofactorGram ε (L.subsequence m) j k) ≤
      τ + B / Real.sqrt (dampedMobiusEnergy ε (L.subsequence m + 1)) := by
    filter_upwards [htail] with m hm
    set T := L.subsequence m
    have hE := receiverEnergy_succ_pos ε T
    have hsE := Real.sqrt_pos.mpr hE
    rw [cofactorGram_quadratic_eq, Real.sqrt_div' _ hE.le, Real.sqrt_sq (pronicNorm_nonneg _ _),
      div_le_iff₀ hsE]
    have hrow := pronicNorm_congr (hsplit (T + 1))
    rw [hrow]
    have h1 := pronicNorm_add_le (T + 1) (etaCofactorSum ε A) (fun n => -(∑ j ∈ Ioc (2 * K) n,
      (-1 : ℝ) ^ (j + 1) * (j : ℝ) ^ (-(ε : ℝ)) * A (n / j)))
    have hneg : pronicNorm (T + 1) (fun n => -(∑ j ∈ Ioc (2 * K) n,
        (-1 : ℝ) ^ (j + 1) * (j : ℝ) ^ (-(ε : ℝ)) * A (n / j))) =
        pronicNorm (T + 1) (fun n => ∑ j ∈ Ioc (2 * K) n,
          (-1 : ℝ) ^ (j + 1) * (j : ℝ) ^ (-(ε : ℝ)) * A (n / j)) := by
      simp only [BezoutValuationIncidence.pronicNorm, neg_sq]
    rw [hneg] at h1
    have heq : (fun n => etaCofactorSum ε A n - ∑ j ∈ Ioc (2 * K) n,
        (-1 : ℝ) ^ (j + 1) * (j : ℝ) ^ (-(ε : ℝ)) * A (n / j)) =
        fun n => etaCofactorSum ε A n + -(∑ j ∈ Ioc (2 * K) n,
          (-1 : ℝ) ^ (j + 1) * (j : ℝ) ^ (-(ε : ℝ)) * A (n / j)) := by funext n; ring
    rw [heq]
    have hdiv : B / Real.sqrt (dampedMobiusEnergy ε (T + 1)) *
        Real.sqrt (dampedMobiusEnergy ε (T + 1)) = B := div_mul_cancel₀ _ hsE.ne'
    nlinarith [hB (T + 1), hm]
  -- pass to the limit
  have hlimP := L.packet_tendsto (alternatingSupport K) (alternatingCoeff ε) id
  have hlimS := (Real.continuous_sqrt.tendsto _).comp hlimP
  have hBlim : Tendsto (fun m => τ + B / Real.sqrt (dampedMobiusEnergy ε (L.subsequence m + 1)))
      atTop (𝓝 (τ + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp hesc))
  have hle := le_of_tendsto_of_tendsto hlimS hBlim hbound
  simp only [id, add_zero] at hle
  have hnn : 0 ≤ ∑ j ∈ alternatingSupport K, ∑ k ∈ alternatingSupport K,
      alternatingCoeff ε j * alternatingCoeff ε k * L.kernel j k :=
    L.packet_nonneg _ _
  calc _ = Real.sqrt (∑ j ∈ alternatingSupport K, ∑ k ∈ alternatingSupport K,
        alternatingCoeff ε j * alternatingCoeff ε k * L.kernel j k) ^ 2 := (Real.sq_sqrt hnn).symm
    _ ≤ τ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2

end GaloisForLFunctions.ArithmeticDefectRigidity
