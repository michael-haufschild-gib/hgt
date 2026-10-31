import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorPlancherel

/-!
# A ground-state square completion of the divisor jet

The logarithmic divisor jet couples conductors along prime-power divisor
edges. Totient weights give exact incoming tame-different charges and outgoing
logarithmic charges. Their quadratic completion is a sum of positive edge
squares. Its kernel consists exactly of constant divisor profiles, whose
Ramanujan packets are integer divisibility combs.

Complete-period orthogonality identifies these same squares with the actual
Ramanujan–divisor-jet pairing.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta
namespace GaloisForLFunctions.SuccessorShellArithmetic
open ArithmeticIntersectionTheory
noncomputable section


/-- Dirichlet associativity collapses every outgoing prime-power divisor chain. -/
theorem sum_divisor_chain_vonMangoldt (f : ArithmeticFunction ℝ) (M : ℕ) :
    (∑ m ∈ M.divisors, ∑ k ∈ m.divisors, f k * vonMangoldt (m / k)) =
      ∑ k ∈ M.divisors, f k * Real.log (M / k : ℕ) := by
  have hmul (m : ℕ) : (f * vonMangoldt) m =
      ∑ k ∈ m.divisors, f k * vonMangoldt (m / k) := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (fun k d => f k * vonMangoldt d)]
  calc
    _ = ∑ m ∈ M.divisors, (f * vonMangoldt) m :=
      sum_congr rfl fun m _ => (hmul m).symm
    _ = ((f * vonMangoldt) * (ζ : ArithmeticFunction ℝ)) M := coe_mul_zeta_apply.symm
    _ = (f * ArithmeticFunction.log) M := by rw [mul_assoc, vonMangoldt_mul_zeta]
    _ = _ := by
      rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
        (fun k d => f k * ArithmeticFunction.log d)]
      simp only [ArithmeticFunction.log_apply]

/-- The incoming conductor charge is the tame different times the totient. -/
theorem sum_divisor_vonMangoldt_mul_totient (m : ℕ) :
    (∑ k ∈ m.divisors, vonMangoldt (m / k) * (k.totient : ℝ)) =
      (m.totient : ℝ) * tameDifferent m := by
  have h := (Nat.sum_divisorsAntidiagonal
    (fun k d => (k.totient : ℝ) * vonMangoldt d) (n := m)).symm.trans
      (Nat.sum_divisorsAntidiagonal'
        (fun k d => (k.totient : ℝ) * vonMangoldt d) (n := m))
  have hflip : (∑ k ∈ m.divisors, vonMangoldt (m / k) * (k.totient : ℝ)) =
      ∑ d ∈ m.divisors, ((m / d).totient : ℝ) * vonMangoldt d := by
    simpa only [mul_comm] using h
  exact hflip.trans (totient_mul_vonMangoldt_eq m)

/-- The totient-weighted Dirichlet energy on the prime-power edges of a divisor lattice. -/
def divisorJetEnergy (M : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
    vonMangoldt (m / k) * (k.totient : ℝ) * (f m - f k) ^ 2

theorem divisorJetEnergy_nonneg (M : ℕ) (f : ℕ → ℝ) : 0 ≤ divisorJetEnergy M f :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)) (sq_nonneg _)

private def totientWeightedSquare (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => (n.totient : ℝ) * f n ^ 2, by simp⟩

private theorem totientWeightedSquare_apply (f : ℕ → ℝ) (n : ℕ) :
    totientWeightedSquare f n = (n.totient : ℝ) * f n ^ 2 := rfl

/-- Incoming and outgoing charges complete the divisor jet to exact positive squares. -/
theorem divisorJetEnergy_eq (M : ℕ) (f : ℕ → ℝ) :
    divisorJetEnergy M f =
      (∑ m ∈ M.divisors,
        (m.totient : ℝ) * (Real.log (M / m : ℕ) + tameDifferent m) * f m ^ 2) -
      2 * ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * f m * f k := by
  have hdown : (∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
      vonMangoldt (m / k) * (k.totient : ℝ) * f m ^ 2) =
      ∑ m ∈ M.divisors, (m.totient : ℝ) * tameDifferent m * f m ^ 2 := by
    apply sum_congr rfl
    intro m _
    rw [← sum_mul, sum_divisor_vonMangoldt_mul_totient]
  have hup : (∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
      vonMangoldt (m / k) * (k.totient : ℝ) * f k ^ 2) =
      ∑ m ∈ M.divisors, (m.totient : ℝ) * Real.log (M / m : ℕ) * f m ^ 2 := by
    simpa only [totientWeightedSquare_apply, mul_assoc, mul_left_comm, mul_comm] using
      sum_divisor_chain_vonMangoldt (totientWeightedSquare f) M
  have he : divisorJetEnergy M f =
      (∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * f m ^ 2) +
      (∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * f k ^ 2) -
      2 * ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * f m * f k := by
    rw [divisorJetEnergy, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m _
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    ring
  rw [he, hdown, hup, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro m _
  ring

/-- The only zero-energy profiles are constants on the divisor lattice. -/
theorem divisorJetEnergy_eq_zero_iff {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    divisorJetEnergy M f = 0 ↔ ∀ m ∈ M.divisors, f m = f 1 := by
  have hterm (m k : ℕ) :
      0 ≤ vonMangoldt (m / k) * (k.totient : ℝ) * (f m - f k) ^ 2 :=
    mul_nonneg (mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)) (sq_nonneg _)
  constructor
  · intro he
    have hrow (m : ℕ) (hm : m ∈ M.divisors) :
        (∑ k ∈ m.divisors,
          vonMangoldt (m / k) * (k.totient : ℝ) * (f m - f k) ^ 2) = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun m _ => sum_nonneg (fun k _ => hterm m k))).mp he m hm
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have hm0 := Nat.pos_of_mem_divisors hm
      by_cases hm1 : m = 1
      · simp only [hm1]
      have hp : m.minFac.Prime := Nat.minFac_prime hm1
      obtain ⟨k, hmk⟩ := Nat.minFac_dvd m
      have hkmdiv : k ∣ m := ⟨m.minFac, by simpa only [Nat.mul_comm] using hmk⟩
      have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hkmdiv hm0
      have hklt : k < m := by
        calc
          k = 1 * k := (one_mul _).symm
          _ < m.minFac * k := Nat.mul_lt_mul_of_pos_right hp.one_lt hk0
          _ = m := hmk.symm
      have hkM : k ∈ M.divisors :=
        Nat.mem_divisors.mpr ⟨hkmdiv.trans (Nat.dvd_of_mem_divisors hm), hM.ne'⟩
      have hquot : m / k = m.minFac :=
        Nat.eq_of_mul_eq_mul_right hk0 ((Nat.div_mul_cancel hkmdiv).trans hmk)
      have hw : 0 < vonMangoldt (m / k) * (k.totient : ℝ) := by
        rw [hquot, vonMangoldt_apply_prime hp]
        exact mul_pos (Real.log_pos (by exact_mod_cast hp.one_lt))
          (by exact_mod_cast Nat.totient_pos.mpr hk0)
      have hz := (sum_eq_zero_iff_of_nonneg (fun k _ => hterm m k)).mp (hrow m hm) k
        (Nat.mem_divisors.mpr ⟨hkmdiv, hm0.ne'⟩)
      have hsq : (f m - f k) ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left hw.ne'
      have hdiff : f m - f k = 0 := sq_eq_zero_iff.mp hsq
      exact (sub_eq_zero.mp hdiff).trans (ih k hklt hkM)
  · intro hf
    apply sum_eq_zero
    intro m hm
    apply sum_eq_zero
    intro k hk
    have hkM : k ∈ M.divisors := Nat.mem_divisors.mpr
      ⟨(Nat.dvd_of_mem_divisors hk).trans (Nat.dvd_of_mem_divisors hm), hM.ne'⟩
    rw [hf m hm, hf k hkM, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero]

/-- A finite Ramanujan packet on the divisors of one period. -/
def divisorRamanujanPacket (M : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ M.divisors, f m * BezoutValuationIncidence.ramanujanLagCoefficient m n

/-- The corresponding packet of logarithmic divisor jets. -/
def divisorJetPacket (M : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ M.divisors, f m * CriticalArithmeticCorrelationTheory.ramanujanLogDivisorJet m n

open BezoutValuationIncidence CriticalArithmeticCorrelationTheory

private theorem sum_range_divisorPacket_mul_mode {M k : ℕ}
    (hk : k ∈ M.divisors) (f : ℕ → ℝ) :
    (∑ n ∈ range M, divisorRamanujanPacket M f n * ramanujanLagCoefficient k n) =
      (M : ℝ) * k.totient * f k := by
  calc
    _ = ∑ n ∈ range M, ∑ j ∈ M.divisors,
        f j * (ramanujanLagCoefficient j n * ramanujanLagCoefficient k n) := by
      apply sum_congr rfl
      intro n _
      rw [divisorRamanujanPacket, sum_mul]
      apply sum_congr rfl
      intro j _
      ring
    _ = ∑ j ∈ M.divisors, f j *
        (∑ n ∈ range M, ramanujanLagCoefficient j n * ramanujanLagCoefficient k n) := by
      rw [sum_comm]
      simp only [mul_sum]
    _ = ∑ j ∈ M.divisors, if j = k then f k * ((M : ℝ) * k.totient) else 0 := by
      apply sum_congr rfl
      intro j hj
      rw [sum_range_ramanujanLagCoefficient_mul
        (Nat.pos_of_mem_divisors hj) (Nat.pos_of_mem_divisors hk)
        (Nat.dvd_of_mem_divisors hj) (Nat.dvd_of_mem_divisors hk)]
      by_cases hjk : j = k
      · subst j
        simp only [ite_true]
      · simp only [if_neg hjk, mul_zero]
    _ = _ := by
      rw [sum_ite_eq', if_pos hk]
      ring

private theorem sum_range_divisorPacket_mul_jet {M m : ℕ}
    (hM : 0 < M) (hm : m ∈ M.divisors) (f : ℕ → ℝ) :
    (∑ n ∈ range M, divisorRamanujanPacket M f n * ramanujanLogDivisorJet m n) =
      (M : ℝ) * ((m.totient : ℝ) * Real.log m * f m +
        ∑ k ∈ m.divisors, vonMangoldt (m / k) * (k.totient : ℝ) * f k) := by
  have hm0 := Nat.pos_of_mem_divisors hm
  have hmm : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hm0.ne'⟩
  have hkM (k : ℕ) (hk : k ∈ m.divisors) : k ∈ M.divisors :=
    Nat.mem_divisors.mpr
      ⟨(Nat.dvd_of_mem_divisors hk).trans (Nat.dvd_of_mem_divisors hm), hM.ne'⟩
  calc
    _ = ∑ k ∈ m.divisors, ramanujanJetConductorWeight m k *
        (∑ n ∈ range M, divisorRamanujanPacket M f n * ramanujanLagCoefficient k n) := by
      simp_rw [ramanujanLogDivisorJet_eq_weighted_conductors hm0, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      apply sum_congr rfl
      intro n _
      ring
    _ = (M : ℝ) * ∑ k ∈ m.divisors,
        ramanujanJetConductorWeight m k * (k.totient : ℝ) * f k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [sum_range_divisorPacket_mul_mode (hkM k hk) f]
      ring
    _ = _ := by
      congr 1
      simp only [ramanujanJetConductorWeight, add_mul, sum_add_distrib,
        ite_mul, zero_mul, sum_ite_eq', if_pos hmm]
      ring

/-- The complete-period packet pairing retains every directed conductor edge. -/
theorem sum_range_divisorPacket_mul_divisorJetPacket {M : ℕ}
    (hM : 0 < M) (f : ℕ → ℝ) :
    (∑ n ∈ range M, divisorRamanujanPacket M f n * divisorJetPacket M f n) =
      (M : ℝ) * ((∑ m ∈ M.divisors, (m.totient : ℝ) * Real.log m * f m ^ 2) +
        ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
          vonMangoldt (m / k) * (k.totient : ℝ) * f m * f k) := by
  calc
    _ = ∑ m ∈ M.divisors, f m *
        (∑ n ∈ range M, divisorRamanujanPacket M f n * ramanujanLogDivisorJet m n) := by
      simp only [divisorJetPacket, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      apply sum_congr rfl
      intro n _
      ring
    _ = _ := by
      rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro m hm
      rw [sum_range_divisorPacket_mul_jet hM hm f]
      have hc : f m * (∑ k ∈ m.divisors,
          vonMangoldt (m / k) * (k.totient : ℝ) * f k) =
          ∑ k ∈ m.divisors, vonMangoldt (m / k) * (k.totient : ℝ) * f m * f k := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k _
        ring
      calc
        _ = (M : ℝ) * ((m.totient : ℝ) * Real.log m * f m ^ 2) +
            (M : ℝ) * (f m * ∑ k ∈ m.divisors,
              vonMangoldt (m / k) * (k.totient : ℝ) * f k) := by ring
        _ = _ := by rw [hc]

/-- Exact square completion of the actual complete-period divisor-jet pairing. -/
theorem divisorJetEnergy_eq_period_pairing {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    divisorJetEnergy M f =
      (∑ m ∈ M.divisors,
        (m.totient : ℝ) * (Real.log M + Real.log m + tameDifferent m) * f m ^ 2) -
      (2 / M) * ∑ n ∈ range M, divisorRamanujanPacket M f n * divisorJetPacket M f n := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hquot (m : ℕ) (hm : m ∈ M.divisors) :
      Real.log (M / m : ℕ) = Real.log M - Real.log m := by
    have hm0 := Nat.pos_of_mem_divisors hm
    have hd := Nat.dvd_of_mem_divisors hm
    have hq0 : 0 < M / m := Nat.div_pos (Nat.le_of_dvd hM hd) hm0
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
    have hqR : ((M / m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    have hprod : ((M / m : ℕ) : ℝ) * m = (M : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hd
    have hl : Real.log (M : ℝ) = Real.log (M / m : ℕ) + Real.log m := by
      rw [← hprod, Real.log_mul hqR hmR]
    linarith only [hl]
  have hdiag :
      (∑ m ∈ M.divisors,
        (m.totient : ℝ) * (Real.log M + Real.log m + tameDifferent m) * f m ^ 2) =
      (∑ m ∈ M.divisors,
        (m.totient : ℝ) * (Real.log (M / m : ℕ) + tameDifferent m) * f m ^ 2) +
      2 * ∑ m ∈ M.divisors, (m.totient : ℝ) * Real.log m * f m ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro m hm
    rw [hquot m hm]
    ring
  rw [divisorJetEnergy_eq, hdiag, sum_range_divisorPacket_mul_divisorJetPacket hM f]
  field_simp [hMR]
  ring

/-- The zero-energy conductor packet is exactly the integer divisibility comb. -/
theorem divisorRamanujanPacket_eq_comb_of_energy_zero {M : ℕ}
    (hM : 0 < M) (f : ℕ → ℝ) (he : divisorJetEnergy M f = 0) (n : ℕ) :
    divisorRamanujanPacket M f n = f 1 * (if M ∣ n then (M : ℝ) else 0) := by
  have hf := (divisorJetEnergy_eq_zero_iff hM f).mp he
  have hpacket : (∑ m ∈ M.divisors, f m * ramanujanLagCoefficient m n) =
      ∑ m ∈ M.divisors, f 1 * ramanujanLagCoefficient m n :=
    sum_congr rfl (fun m hm => by rw [hf m hm])
  rw [divisorRamanujanPacket, hpacket, ← mul_sum]
  congr 1
  exact BezoutValuationIncidence.sum_divisors_ramanujanLagCoefficient M n

#print axioms sum_divisor_chain_vonMangoldt
#print axioms divisorJetEnergy_nonneg
#print axioms divisorJetEnergy_eq
#print axioms divisorJetEnergy_eq_zero_iff
#print axioms sum_range_divisorPacket_mul_divisorJetPacket
#print axioms divisorJetEnergy_eq_period_pairing
#print axioms divisorRamanujanPacket_eq_comb_of_energy_zero
end
end GaloisForLFunctions.SuccessorShellArithmetic
