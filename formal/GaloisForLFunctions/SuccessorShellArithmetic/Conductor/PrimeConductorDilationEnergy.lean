import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorHeadNorm
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPrimeRowsHaveAdjunctionEnergy

set_option autoImplicit false

/-!
# The exact square energy of prime dilations

The averaged prime generator on a squared gcd profile is its torsion
charge. Subtracting twice the packet-generator pairing cancels torsion
and leaves the diagonal conductor adjunction energy.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence
  CriticalArithmeticCorrelationTheory ArithmeticIntersectionTheory

private theorem hasSum_ramanujan_up_all_rows {m : ℕ} (hm : 0 < m) (n : ℕ) :
    HasSum (fun k : ℕ => vonMangoldt k / (k : ℝ) *
      (ramanujanLagCoefficient m (k * n) - ramanujanLagCoefficient m n))
      (ramanujanLogDivisorJet m n -
        (Real.log m + tameDifferent m) * ramanujanLagCoefficient m n) := by
  by_cases hn : n = 0
  · subst n
    have hz : ramanujanLogDivisorJet m 0 -
        (Real.log m + tameDifferent m) * ramanujanLagCoefficient m 0 = 0 := by
      rw [ramanujanLogDivisorJet_of_dvd hm (dvd_zero m),
        ramanujanLagCoefficient_of_dvd (dvd_zero m)]
      ring
    rw [hz]
    simpa only [Nat.mul_zero, sub_self, mul_zero] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  · have h := hasSum_ramanujan_correction m hm n (Nat.pos_of_ne_zero hn)
    rw [ramanujanDownCorrection_eq_neg_logDivisorJet m (Nat.pos_of_ne_zero hn), sub_neg_eq_add] at h
    have hv : -(Real.log m + tameDifferent m) * ramanujanLagCoefficient m n +
        ramanujanLogDivisorJet m n = ramanujanLogDivisorJet m n -
          (Real.log m + tameDifferent m) * ramanujanLagCoefficient m n := by ring
    rw [hv] at h
    apply h.congr_fun
    intro k
    rw [ramanujanUpCorrectionTerm, Nat.mul_comm n k]
    ring

private theorem period_sum_lag {M m : ℕ} (hM : 0 < M) (hm : m ∣ M) :
    (∑ n ∈ range M, ramanujanLagCoefficient m n) = if m = 1 then (M : ℝ) else 0 := by
  have hc (n : ℕ) : ramanujanLagCoefficient 1 n = 1 := by
    simpa only [Nat.totient_one, Nat.cast_one] using ramanujanLagCoefficient_of_dvd (one_dvd n)
  have h := sum_range_ramanujanLagCoefficient_mul (Nat.pos_of_dvd_of_pos hm hM)
    zero_lt_one hm (one_dvd M)
  by_cases hm1 : m = 1
  · subst m
    simpa only [hc, mul_one, Nat.totient_one, Nat.cast_one, ite_true] using h
  · simpa only [hc, mul_one, if_neg hm1] using h

private theorem period_sum_jet {M m : ℕ} (hM : 0 < M) (hm : m ∣ M) :
    (∑ n ∈ range M, ramanujanLogDivisorJet m n) = (M : ℝ) * vonMangoldt m := by
  have hm0 := Nat.pos_of_dvd_of_pos hm hM
  have h1 : 1 ∈ m.divisors := Nat.mem_divisors.mpr ⟨one_dvd m, hm0.ne'⟩
  calc
    _ = ∑ d ∈ m.divisors, ramanujanJetConductorWeight m d *
        (∑ n ∈ range M, ramanujanLagCoefficient d n) := by
      simp_rw [ramanujanLogDivisorJet_eq_weighted_conductors hm0]
      rw [sum_comm]
      simp only [mul_sum]
    _ = ∑ d ∈ m.divisors, ramanujanJetConductorWeight m d *
        (if d = 1 then (M : ℝ) else 0) := by
      apply sum_congr rfl
      intro d hd
      rw [period_sum_lag hM ((Nat.dvd_of_mem_divisors hd).trans hm)]
    _ = ramanujanJetConductorWeight m 1 * M := by
      simp only [mul_ite, mul_zero, sum_ite_eq', if_pos h1]
    _ = _ := by
      by_cases hm1 : m = 1
      · subst m
        simp only [ramanujanJetConductorWeight, ite_true, Nat.cast_one, Real.log_one,
          Nat.div_one, vonMangoldt_apply_one, add_zero, zero_mul, mul_zero]
      · simp only [ramanujanJetConductorWeight, if_neg (Ne.symm hm1), Nat.div_one, zero_add]
        ring

private theorem period_sum_packet_mul (M : ℕ) (f g : ℕ → ℝ) :
    (∑ n ∈ range M, divisorRamanujanPacket M f n * divisorRamanujanPacket M g n) =
      (M : ℝ) * ∑ m ∈ M.divisors, (m.totient : ℝ) * f m * g m := by
  calc
    _ = ∑ n ∈ range M, ∑ m ∈ M.divisors, ∑ l ∈ M.divisors,
        f m * g l * (ramanujanLagCoefficient m n * ramanujanLagCoefficient l n) := by
      apply sum_congr rfl
      intro n _
      simp only [divisorRamanujanPacket]
      rw [sum_mul]
      apply sum_congr rfl
      intro m _
      rw [mul_sum]
      apply sum_congr rfl
      intro l _
      ring
    _ = ∑ m ∈ M.divisors, ∑ l ∈ M.divisors, f m * g l *
        (∑ n ∈ range M, ramanujanLagCoefficient m n * ramanujanLagCoefficient l n) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      rw [sum_comm]
      simp only [mul_sum]
    _ = (M : ℝ) * ∑ m ∈ M.divisors, (m.totient : ℝ) * f m * g m := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      have hentry (l : ℕ) (hl : l ∈ M.divisors) :
          (∑ n ∈ range M, ramanujanLagCoefficient m n * ramanujanLagCoefficient l n) =
            if m = l then (M : ℝ) * l.totient else 0 :=
        sum_range_ramanujanLagCoefficient_mul (Nat.pos_of_mem_divisors hm)
          (Nat.pos_of_mem_divisors hl) (Nat.dvd_of_mem_divisors hm) (Nat.dvd_of_mem_divisors hl)
      rw [sum_congr rfl (fun l hl => congrArg (fun z => f m * g l * z) (hentry l hl)),
        sum_eq_single_of_mem m hm]
      · simp only [ite_true]
        ring
      · intro l _ hlm
        simp only [if_neg (Ne.symm hlm), mul_zero]

private theorem hasSum_divisorPacket_up (M : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    HasSum (fun k : ℕ => vonMangoldt k / (k : ℝ) *
      (divisorRamanujanPacket M f (k * n) - divisorRamanujanPacket M f n))
      (divisorJetPacket M f n - divisorRamanujanPacket M
        (fun m => (Real.log m + tameDifferent m) * f m) n) := by
  have h := hasSum_sum (s := M.divisors) (fun m hm =>
    (hasSum_ramanujan_up_all_rows (Nat.pos_of_mem_divisors hm) n).mul_left (f m))
  have hv : (∑ m ∈ M.divisors, f m *
      (ramanujanLogDivisorJet m n - (Real.log m + tameDifferent m) * ramanujanLagCoefficient m n)) =
      divisorJetPacket M f n - divisorRamanujanPacket M
        (fun m => (Real.log m + tameDifferent m) * f m) n := by
    simp only [divisorJetPacket, divisorRamanujanPacket, mul_sub, sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro m _
    ring
  rw [hv] at h
  apply h.congr_fun
  intro k
  simp only [divisorRamanujanPacket, mul_sub, mul_sum, sum_sub_distrib]
  congr 1 <;> apply sum_congr rfl <;> intro m _ <;> ring

private theorem hasSum_divisorPacket_up_mean {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    HasSum (fun k : ℕ => (1 / M) * vonMangoldt k / (k : ℝ) *
      (∑ n ∈ range M, (divisorRamanujanPacket M f (k * n) - divisorRamanujanPacket M f n)))
      (∑ m ∈ M.divisors, f m * vonMangoldt m) := by
  have h := (hasSum_sum (s := range M) (fun n _ => hasSum_divisorPacket_up M f n)).mul_left
    (1 / (M : ℝ))
  have hv : (1 / (M : ℝ)) *
      (∑ n ∈ range M, (divisorJetPacket M f n - divisorRamanujanPacket M
        (fun m => (Real.log m + tameDifferent m) * f m) n)) =
        ∑ m ∈ M.divisors, f m * vonMangoldt m := by
    have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    have hjet : (∑ n ∈ range M, divisorJetPacket M f n) =
        (M : ℝ) * ∑ m ∈ M.divisors, f m * vonMangoldt m := by
      simp only [divisorJetPacket]
      rw [sum_comm, mul_sum]
      apply sum_congr rfl
      intro m hm
      rw [← mul_sum, period_sum_jet hM (Nat.dvd_of_mem_divisors hm)]
      ring
    have hzero : (∑ n ∈ range M, divisorRamanujanPacket M
        (fun m => (Real.log m + tameDifferent m) * f m) n) = 0 := by
      simp only [divisorRamanujanPacket]
      rw [sum_comm]
      apply sum_eq_zero
      intro m hm
      rw [← mul_sum, period_sum_lag hM (Nat.dvd_of_mem_divisors hm)]
      by_cases hm1 : m = 1
      · subst m
        simp only [ite_true, Nat.cast_one, Real.log_one, tameDifferent,
          Nat.primeFactors_one, sum_empty, add_zero, zero_mul]
      · rw [if_neg hm1, mul_zero]
    rw [sum_sub_distrib, hjet, hzero, sub_zero]
    field_simp [hMR]
  rw [hv] at h
  apply h.congr_fun
  intro k
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro n _
  ring

private def reciprocalGcdCoefficient (M : ℕ) (V : ℕ → ℝ) (d : ℕ) : ℝ :=
  (1 / M) * ∑ j ∈ M.divisors, V (M / j) * ramanujanLagCoefficient j (M / d)

private theorem reciprocalGcdCoefficient_expansion {M : ℕ} (hM : 0 < M)
    (V : ℕ → ℝ) (n : ℕ) :
    V (Nat.gcd M n) = divisorRamanujanPacket M (reciprocalGcdCoefficient M V) n := by
  have hg : Nat.gcd M n ∈ M.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left M n, hM.ne'⟩
  have hk : M / Nat.gcd M n ∈ M.divisors := Nat.mem_divisors.mpr
    ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_left M n), hM.ne'⟩
  have he := divisor_profile_ramanujan_expansion hM hk (fun j => V (M / j))
  simp only [Nat.div_div_self (Nat.dvd_of_mem_divisors hg) hM.ne'] at he
  rw [he, divisorRamanujanPacket, mul_sum]
  apply sum_congr rfl
  intro d hd
  rw [ramanujanLagCoefficient_gcd_period (Nat.dvd_of_mem_divisors hd)]
  dsimp only [reciprocalGcdCoefficient]
  ring

private theorem reciprocalGcdCoefficient_mangoldt {M : ℕ} (hM : 0 < M) (V : ℕ → ℝ) :
    (∑ d ∈ M.divisors, reciprocalGcdCoefficient M V d * vonMangoldt d) =
      (1 / M) * ∑ j ∈ M.divisors, (j.totient : ℝ) * V (M / j) *
        (Real.log M - (Real.log j + tameDifferent j)) := by
  calc
    _ = (1 / M) * ∑ j ∈ M.divisors, V (M / j) *
        (∑ d ∈ M.divisors, vonMangoldt d * ramanujanLagCoefficient j (M / d)) := by
      simp only [reciprocalGcdCoefficient, mul_sum, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet j hM,
        ramanujanLagCoefficient_of_dvd (Nat.dvd_of_mem_divisors hj),
        ramanujanLogDivisorJet_of_dvd (Nat.pos_of_mem_divisors hj)
          (Nat.dvd_of_mem_divisors hj)]
      ring

private theorem packet_gcd_period (M : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    divisorRamanujanPacket M f (Nat.gcd M n) = divisorRamanujanPacket M f n := by
  unfold divisorRamanujanPacket
  apply sum_congr rfl
  intro d hd
  rw [ramanujanLagCoefficient_gcd_period (Nat.dvd_of_mem_divisors hd)]

private theorem hasSum_squarePacket_up_mean {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    HasSum (fun k : ℕ => (1 / M) * vonMangoldt k / (k : ℝ) *
      (∑ n ∈ range M, (divisorRamanujanPacket M f (k * n) ^ 2 - divisorRamanujanPacket M f n ^ 2)))
      (Real.log M * (∑ m ∈ M.divisors, (m.totient : ℝ) * f m ^ 2) - divisorJetEnergy M f) := by
  let V : ℕ → ℝ := fun n => divisorRamanujanPacket M f n ^ 2
  let b := reciprocalGcdCoefficient M V
  have he (n : ℕ) : divisorRamanujanPacket M b n = divisorRamanujanPacket M f n ^ 2 := by
    rw [← reciprocalGcdCoefficient_expansion hM V n]
    dsimp only [V]
    rw [packet_gcd_period]
  have h := hasSum_divisorPacket_up_mean hM b
  have hv : (∑ d ∈ M.divisors, b d * vonMangoldt d) =
      Real.log M * (∑ m ∈ M.divisors, (m.totient : ℝ) * f m ^ 2) - divisorJetEnergy M f := by
    rw [reciprocalGcdCoefficient_mangoldt hM V,
      divisorJetEnergy_eq_adjunction_spectrum hM f, ← divisorPacket_reciprocal_plancherel hM f]
    simp only [V, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro d _
    ring
  rw [hv] at h
  simpa only [he] using h

private theorem hasSum_packet_up_cross {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    HasSum (fun k : ℕ => (2 / M) * vonMangoldt k / (k : ℝ) *
      (∑ n ∈ range M, divisorRamanujanPacket M f n *
        (divisorRamanujanPacket M f (k * n) - divisorRamanujanPacket M f n)))
      (Real.log M * (∑ m ∈ M.divisors, (m.totient : ℝ) * f m ^ 2) - divisorJetEnergy M f -
        ∑ m ∈ M.divisors, (m.totient : ℝ) * (Real.log m + tameDifferent m) * f m ^ 2) := by
  let A : ℝ := ∑ m ∈ M.divisors, (m.totient : ℝ) * f m ^ 2
  let L : ℝ := ∑ m ∈ M.divisors, (m.totient : ℝ) * (Real.log m + tameDifferent m) * f m ^ 2
  let g : ℕ → ℝ := fun m => (Real.log m + tameDifferent m) * f m
  have h := (hasSum_sum (s := range M) (fun n _ =>
    (hasSum_divisorPacket_up M f n).mul_left (divisorRamanujanPacket M f n))).mul_left
      (2 / (M : ℝ))
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hg : (∑ n ∈ range M, divisorRamanujanPacket M f n * divisorRamanujanPacket M g n) =
      (M : ℝ) * L := by
    rw [period_sum_packet_mul]
    congr 1
    apply sum_congr rfl
    intro m _
    dsimp only [g]
    ring
  have hdiag : (∑ m ∈ M.divisors,
      (m.totient : ℝ) * (Real.log M + Real.log m + tameDifferent m) * f m ^ 2) =
        Real.log M * A + L := by
    dsimp only [A, L]
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro m _
    ring
  have henergy := divisorJetEnergy_eq_period_pairing hM f
  rw [hdiag] at henergy
  have hv : (2 / (M : ℝ)) *
      (∑ n ∈ range M, divisorRamanujanPacket M f n *
        (divisorJetPacket M f n - divisorRamanujanPacket M g n)) =
      Real.log M * A - divisorJetEnergy M f - L := by
    simp only [mul_sub, sum_sub_distrib]
    rw [hg]
    have hcancel : (2 / (M : ℝ)) * ((M : ℝ) * L) = 2 * L := by field_simp [hMR]
    rw [hcancel]
    linarith only [henergy]
  change HasSum _ ((2 / (M : ℝ)) *
    ∑ n ∈ range M, divisorRamanujanPacket M f n *
      (divisorJetPacket M f n - divisorRamanujanPacket M g n)) at h
  rw [hv] at h
  apply h.congr_fun
  intro k
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro n _
  ring

/-- The prime-weighted square of every dilation jump has exactly the diagonal conductor adjunction energy. -/
theorem hasSum_primeDilationPacket_sq {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    HasSum (fun k : ℕ => (1 / M) * vonMangoldt k / (k : ℝ) *
      (∑ n ∈ range M,
        (divisorRamanujanPacket M f (k * n) - divisorRamanujanPacket M f n) ^ 2))
      (∑ m ∈ M.divisors, (m.totient : ℝ) * (Real.log m + tameDifferent m) * f m ^ 2) := by
  have h := (hasSum_squarePacket_up_mean hM f).sub (hasSum_packet_up_cross hM f)
  have hv : (Real.log M * (∑ m ∈ M.divisors, (m.totient : ℝ) * f m ^ 2) - divisorJetEnergy M f) -
      (Real.log M * (∑ m ∈ M.divisors, (m.totient : ℝ) * f m ^ 2) - divisorJetEnergy M f -
        ∑ m ∈ M.divisors, (m.totient : ℝ) * (Real.log m + tameDifferent m) * f m ^ 2) =
      ∑ m ∈ M.divisors, (m.totient : ℝ) * (Real.log m + tameDifferent m) * f m ^ 2 := by ring
  rw [hv] at h
  apply h.congr_fun
  intro k
  simp only [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  ring

/-- Complete-period orthogonality is Euclidean norm in normalized conductor coordinates. -/
theorem sum_range_normalizedRamanujan_packet_sq (S : Finset ℕ) (a : ℕ → ℝ) (M : ℕ)
    (hS : ∀ m ∈ S, 0 < m) (hSM : ∀ m ∈ S, m ∣ M) :
    (∑ n ∈ range M, (∑ m ∈ S, a m * normalizedRamanujanMode m n) ^ 2) =
      (M : ℝ) * ∑ m ∈ S, a m ^ 2 := by
  calc
    _ = ∑ n ∈ range M,
        (∑ m ∈ S, (a m / Real.sqrt (m.totient : ℝ)) *
          BezoutValuationIncidence.ramanujanLagCoefficient m n) ^ 2 := by
      apply sum_congr rfl
      intro n _
      congr 1
      apply sum_congr rfl
      intro m hm
      rw [normalizedRamanujanMode_eq_coefficient (hS m hm)]
      ring
    _ = (M : ℝ) * ∑ m ∈ S, (a m / Real.sqrt (m.totient : ℝ)) ^ 2 * m.totient :=
      sum_range_ramanujan_packet_sq S (fun m => a m / Real.sqrt (m.totient : ℝ)) M hS hSM
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro m hm
      have hphi : (m.totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (hS m hm)).ne'
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), div_mul_cancel₀ _ hphi]

/-- Coefficients of a packet's change under one integer dilation. -/
def primeConductorDilationJump (Q : ℕ) (a : ℕ → ℝ) (k m : ℕ) : ℝ :=
  (∑ l ∈ Icc 1 Q, a l * primeConductorDilationMean m l k) - a m

private theorem normalized_mode_dilation_expansion {Q l : ℕ} (hl : l ∈ Icc 1 Q) (k n : ℕ) :
    (∑ m ∈ Icc 1 Q, primeConductorDilationMean m l k * normalizedRamanujanMode m n) =
      normalizedRamanujanMode l (k * n) := by
  have hl0 : 0 < l := (mem_Icc.mp hl).1
  let q := l / Nat.gcd l k
  have hq0 : 0 < q := Nat.div_pos (Nat.le_of_dvd hl0 (Nat.gcd_dvd_left l k))
    (Nat.gcd_pos_of_pos_left k hl0)
  have hqQ : q ≤ Q := (Nat.div_le_self l (Nat.gcd l k)).trans (mem_Icc.mp hl).2
  have hqmem : q ∈ Icc 1 Q := mem_Icc.mpr ⟨hq0, hqQ⟩
  have hqphi : Real.sqrt (q.totient : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hq0)).ne'
  have hlphi : Real.sqrt (l.totient : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hl0)).ne'
  have hratio : (l.totient : ℝ) /
      (Real.sqrt (q.totient : ℝ) * Real.sqrt (l.totient : ℝ)) =
      Real.sqrt (l.totient : ℝ) / Real.sqrt (q.totient : ℝ) := by
    apply (div_eq_iff (mul_ne_zero hqphi hlphi)).mpr
    symm
    calc
      _ = (Real.sqrt (l.totient : ℝ) / Real.sqrt (q.totient : ℝ) *
          Real.sqrt (q.totient : ℝ)) * Real.sqrt (l.totient : ℝ) := by ring
      _ = Real.sqrt (l.totient : ℝ) * Real.sqrt (l.totient : ℝ) := by
        rw [div_mul_cancel₀ _ hqphi]
      _ = _ := by rw [← sq, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [sum_eq_single_of_mem q hqmem]
  · rw [primeConductorDilationMean_eq_reduced hq0 hl0, if_pos rfl, hratio,
      normalizedRamanujanMode_dilate_reduced hl0]
  · intro m hm hmq
    rw [primeConductorDilationMean_eq_reduced (mem_Icc.mp hm).1 hl0, if_neg hmq, zero_mul]

/-- Dilation jumps stay in the same finite conductor packet, with their exact matrix coefficients. -/
theorem primeConductorDilationJump_packet (Q : ℕ) (a : ℕ → ℝ) (k n : ℕ) :
    (∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m * normalizedRamanujanMode m n) =
      (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m (k * n)) -
        ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n := by
  calc
    _ = (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
        a l * primeConductorDilationMean m l k * normalizedRamanujanMode m n) -
        ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n := by
      simp only [primeConductorDilationJump, sub_mul, sum_sub_distrib, sum_mul]
    _ = (∑ l ∈ Icc 1 Q, a l *
        (∑ m ∈ Icc 1 Q, primeConductorDilationMean m l k * normalizedRamanujanMode m n)) -
        ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n := by
      congr 1
      rw [sum_comm]
      apply sum_congr rfl
      intro l _
      rw [mul_sum]
      apply sum_congr rfl
      intro m _
      ring
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro l hl
      rw [normalized_mode_dilation_expansion hl]

/-- The period-mean square of a dilation jump is exactly its coefficient mass. -/
theorem primeConductorDilationJump_period_sq (Q : ℕ) (a : ℕ → ℝ) (k : ℕ) :
    (1 / (Q.factorial : ℝ)) * (∑ n ∈ range Q.factorial,
      ((∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m (k * n)) -
        ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2) =
      ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2 := by
  simp_rw [← primeConductorDilationJump_packet]
  rw [sum_range_normalizedRamanujan_packet_sq (Icc 1 Q) (primeConductorDilationJump Q a k)
    Q.factorial (fun m hm => (mem_Icc.mp hm).1)
    (fun m hm => Nat.dvd_factorial (mem_Icc.mp hm).1 (mem_Icc.mp hm).2)]
  have hM : (Q.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos Q).ne'
  field_simp [hM]

private def normalizedDivisorCoefficients (Q : ℕ) (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m ∈ Icc 1 Q then a m / Real.sqrt (m.totient : ℝ) else 0

private theorem icc_subset_factorial_divisors (Q : ℕ) : Icc 1 Q ⊆ Q.factorial.divisors := by
  intro m hm
  exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial (mem_Icc.mp hm).1 (mem_Icc.mp hm).2,
    (Nat.factorial_pos Q).ne'⟩

private theorem normalizedDivisorPacket_eq (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    divisorRamanujanPacket Q.factorial (normalizedDivisorCoefficients Q a) n =
      ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n := by
  have hsum : (∑ m ∈ Icc 1 Q, normalizedDivisorCoefficients Q a m *
      BezoutValuationIncidence.ramanujanLagCoefficient m n) =
      ∑ m ∈ Q.factorial.divisors, normalizedDivisorCoefficients Q a m *
        BezoutValuationIncidence.ramanujanLagCoefficient m n := by
    apply sum_subset (icc_subset_factorial_divisors Q)
    intro m _ hm
    simp only [normalizedDivisorCoefficients, if_neg hm, zero_mul]
  rw [divisorRamanujanPacket, ← hsum]
  apply sum_congr rfl
  intro m hm
  rw [normalizedDivisorCoefficients, if_pos hm, normalizedRamanujanMode_eq_coefficient (mem_Icc.mp hm).1]
  ring

private theorem normalizedDivisorCoefficients_energy (Q : ℕ) (a : ℕ → ℝ) :
    (∑ m ∈ Q.factorial.divisors, (m.totient : ℝ) *
      (Real.log m + ArithmeticIntersectionTheory.tameDifferent m) *
        normalizedDivisorCoefficients Q a m ^ 2) =
      ∑ m ∈ Icc 1 Q, (Real.log m + ArithmeticIntersectionTheory.tameDifferent m) * a m ^ 2 := by
  have hsum : (∑ m ∈ Icc 1 Q, (m.totient : ℝ) *
      (Real.log m + ArithmeticIntersectionTheory.tameDifferent m) *
        normalizedDivisorCoefficients Q a m ^ 2) =
      ∑ m ∈ Q.factorial.divisors, (m.totient : ℝ) *
        (Real.log m + ArithmeticIntersectionTheory.tameDifferent m) *
          normalizedDivisorCoefficients Q a m ^ 2 := by
    apply sum_subset (icc_subset_factorial_divisors Q)
    intro m _ hm
    simp only [normalizedDivisorCoefficients, if_neg hm, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
  rw [← hsum]
  apply sum_congr rfl
  intro m hm
  have hphi : (m.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hm).1).ne'
  rw [normalizedDivisorCoefficients, if_pos hm, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ = (Real.log m + ArithmeticIntersectionTheory.tameDifferent m) *
        ((a m ^ 2 / (m.totient : ℝ)) * m.totient) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hphi]

/-- The full prime-dilation square energy is diagonal in normalized conductor coordinates. -/
theorem hasSum_primeConductorDilationJump_sq (Q : ℕ) (a : ℕ → ℝ) :
    HasSum (fun k : ℕ => vonMangoldt k / (k : ℝ) *
      (∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2))
      (∑ m ∈ Icc 1 Q, (Real.log m + ArithmeticIntersectionTheory.tameDifferent m) * a m ^ 2) := by
  have h := hasSum_primeDilationPacket_sq (Nat.factorial_pos Q) (normalizedDivisorCoefficients Q a)
  rw [normalizedDivisorCoefficients_energy] at h
  simp only [normalizedDivisorPacket_eq] at h
  apply h.congr_fun
  intro k
  rw [← primeConductorDilationJump_period_sq Q a k]
  ring

/-- The completed upward prime row of a normalized packet is its divisor jet minus adjunction. -/
theorem hasSum_normalizedRamanujanPacket_up (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    HasSum (fun k : ℕ => vonMangoldt k / (k : ℝ) *
      ((∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m (k * n)) -
        ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n))
      (∑ m ∈ Icc 1 Q, a m *
        (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) -
          (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)) := by
  have h := hasSum_sum (s := Icc 1 Q) (fun m hm =>
    (hasSum_ramanujan_up_all_rows (mem_Icc.mp hm).1 n).mul_left
      (a m / Real.sqrt (m.totient : ℝ)))
  have hv : (∑ m ∈ Icc 1 Q, a m / Real.sqrt (m.totient : ℝ) *
      (ramanujanLogDivisorJet m n -
        (Real.log m + tameDifferent m) * ramanujanLagCoefficient m n)) =
      ∑ m ∈ Icc 1 Q, a m *
        (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) -
          (Real.log m + tameDifferent m) * normalizedRamanujanMode m n) := by
    apply sum_congr rfl
    intro m hm
    rw [normalizedRamanujanMode_eq_coefficient (mem_Icc.mp hm).1]
    ring
  rw [hv] at h
  apply h.congr_fun
  intro k
  rw [← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro m hm
  rw [normalizedRamanujanMode_eq_coefficient (mem_Icc.mp hm).1,
    normalizedRamanujanMode_eq_coefficient (mem_Icc.mp hm).1]
  ring

#print axioms hasSum_primeDilationPacket_sq
#print axioms sum_range_normalizedRamanujan_packet_sq
#print axioms primeConductorDilationJump_packet
#print axioms primeConductorDilationJump_period_sq
#print axioms hasSum_primeConductorDilationJump_sq
#print axioms hasSum_normalizedRamanujanPacket_up

end GaloisForLFunctions.SuccessorShellArithmetic
