import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.DivisorJetGroundState
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.RamanujanJetAdjunctionGap
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.RamanujanAutocorrelationWeights

/-!
# Autocorrelation smoothing of the divisor-jet square completion

Every finite signed source gives nonnegative Ramanujan autocorrelation
weights. Smoothing both the packet and its logarithmic jet equals weighting
one conductor packet by those weights. The resulting pairing has an exact
positive divisor-edge completion. Its incoming charge is the reduced-lag
adjunction deficit, which is therefore a positive semidefinite kernel.
-/

open Finset ArithmeticFunction
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence CriticalArithmeticCorrelationTheory ArithmeticIntersectionTheory
noncomputable section

/-- Conductor-edge energy with a weight on the lower conductor. -/
def weightedDivisorJetEnergy (M : ℕ) (b f : ℕ → ℝ) : ℝ :=
  ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
    vonMangoldt (m / k) * (k.totient : ℝ) * b k * (f m - f k) ^ 2

/-- Exact projection of a divisor packet onto one Ramanujan mode. -/
theorem sum_range_divisorPacket_mul_ramanujan {M k : ℕ}
    (hk : k ∈ M.divisors) (f : ℕ → ℝ) :
    (∑ n ∈ range M, divisorRamanujanPacket M f n * ramanujanLagCoefficient k n) =
      (M : ℝ) * k.totient * f k := by
  calc
    _ = ∑ j ∈ M.divisors, f j *
        (∑ n ∈ range M, ramanujanLagCoefficient j n * ramanujanLagCoefficient k n) := by
      simp only [divisorRamanujanPacket, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      ring
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
    _ = _ := by rw [sum_ite_eq', if_pos hk]; ring

private theorem packet_jet_projection {M m : ℕ}
    (hM : 0 < M) (hm : m ∈ M.divisors) (g : ℕ → ℝ) :
    (∑ n ∈ range M, divisorRamanujanPacket M g n * ramanujanLogDivisorJet m n) =
      (M : ℝ) * ((m.totient : ℝ) * Real.log m * g m +
        ∑ k ∈ m.divisors, vonMangoldt (m / k) * (k.totient : ℝ) * g k) := by
  have hm0 := Nat.pos_of_mem_divisors hm
  have hmm : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hm0.ne'⟩
  have hkM (k : ℕ) (hk : k ∈ m.divisors) : k ∈ M.divisors :=
    Nat.mem_divisors.mpr
      ⟨(Nat.dvd_of_mem_divisors hk).trans (Nat.dvd_of_mem_divisors hm), hM.ne'⟩
  calc
    _ = ∑ k ∈ m.divisors, ramanujanJetConductorWeight m k *
        (∑ n ∈ range M, divisorRamanujanPacket M g n * ramanujanLagCoefficient k n) := by
      simp_rw [ramanujanLogDivisorJet_eq_weighted_conductors hm0, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      apply sum_congr rfl
      intro n _
      ring
    _ = (M : ℝ) * ∑ k ∈ m.divisors,
        ramanujanJetConductorWeight m k * (k.totient : ℝ) * g k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [sum_range_divisorPacket_mul_ramanujan (hkM k hk) g]
      ring
    _ = _ := by
      congr 1
      simp only [ramanujanJetConductorWeight, add_mul, sum_add_distrib,
        ite_mul, zero_mul, sum_ite_eq', if_pos hmm]
      ring

/-- Bilinear period pairing keeps the orientation of every conductor edge. -/
theorem sum_range_divisorPacket_mul_divisorJetPacket_bilinear {M : ℕ}
    (hM : 0 < M) (g f : ℕ → ℝ) :
    (∑ n ∈ range M, divisorRamanujanPacket M g n * divisorJetPacket M f n) =
      (M : ℝ) * ((∑ m ∈ M.divisors, (m.totient : ℝ) * Real.log m * g m * f m) +
        ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
          vonMangoldt (m / k) * (k.totient : ℝ) * f m * g k) := by
  calc
    _ = ∑ m ∈ M.divisors, f m *
        (∑ n ∈ range M, divisorRamanujanPacket M g n * ramanujanLogDivisorJet m n) := by
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
      rw [packet_jet_projection hM hm g]
      have hc : f m * (∑ k ∈ m.divisors,
          vonMangoldt (m / k) * (k.totient : ℝ) * g k) =
          ∑ k ∈ m.divisors, vonMangoldt (m / k) * (k.totient : ℝ) * f m * g k := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k _
        ring
      calc
        _ = (M : ℝ) * ((m.totient : ℝ) * Real.log m * g m * f m) +
            (M : ℝ) * (f m * ∑ k ∈ m.divisors,
              vonMangoldt (m / k) * (k.totient : ℝ) * g k) := by ring
        _ = _ := by rw [hc]

private def weightedTotientSquare (b f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun k => (k.totient : ℝ) * b k * f k ^ 2, by simp⟩

private theorem weightedTotientSquare_apply (b f : ℕ → ℝ) (k : ℕ) :
    weightedTotientSquare b f k = (k.totient : ℝ) * b k * f k ^ 2 := rfl

/-- The outgoing logarithmic charge and incoming weighted jet complete every edge square. -/
theorem weightedDivisorJetEnergy_eq (M : ℕ) (b f : ℕ → ℝ) :
    weightedDivisorJetEnergy M b f =
      (∑ m ∈ M.divisors,
        ((m.totient : ℝ) * b m * Real.log (M / m : ℕ) +
          ∑ k ∈ m.divisors, vonMangoldt (m / k) * (k.totient : ℝ) * b k) * f m ^ 2) -
      2 * ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * b k * f m * f k := by
  have hout : (∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
      vonMangoldt (m / k) * (k.totient : ℝ) * b k * f k ^ 2) =
      ∑ m ∈ M.divisors, (m.totient : ℝ) * b m * Real.log (M / m : ℕ) * f m ^ 2 := by
    simpa only [weightedTotientSquare_apply, mul_assoc, mul_left_comm, mul_comm] using
      sum_divisor_chain_vonMangoldt (weightedTotientSquare b f) M
  have he : weightedDivisorJetEnergy M b f =
      (∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * b k * f m ^ 2) +
      (∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * b k * f k ^ 2) -
      2 * ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * b k * f m * f k := by
    rw [weightedDivisorJetEnergy, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m _
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    ring
  rw [he, hout, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro m _
  rw [← sum_mul]
  ring

private theorem log_divisor_quotient {M m : ℕ} (hM : 0 < M) (hm : m ∈ M.divisors) :
    Real.log (M / m : ℕ) = Real.log M - Real.log m := by
  have hd := Nat.dvd_of_mem_divisors hm
  have hm0 := Nat.pos_of_mem_divisors hm
  have hq0 : 0 < M / m := Nat.div_pos (Nat.le_of_dvd hM hd) hm0
  have hprod : ((M / m : ℕ) : ℝ) * m = (M : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel hd
  have hl : Real.log (M : ℝ) = Real.log (M / m : ℕ) + Real.log m := by
    rw [← hprod, Real.log_mul (by exact_mod_cast hq0.ne') (by exact_mod_cast hm0.ne')]
  linarith only [hl]

/-- Exact square completion of the smoothed packet and the unsmoothed logarithmic jet. -/
theorem weightedDivisorJetEnergy_eq_period_pairing {M : ℕ}
    (hM : 0 < M) (b f : ℕ → ℝ) :
    weightedDivisorJetEnergy M b f =
      (∑ m ∈ M.divisors,
        ((m.totient : ℝ) * b m * (Real.log M + Real.log m) +
          ∑ k ∈ m.divisors, vonMangoldt (m / k) * (k.totient : ℝ) * b k) * f m ^ 2) -
      (2 / M) * ∑ n ∈ range M,
        divisorRamanujanPacket M (fun k => b k * f k) n * divisorJetPacket M f n := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hdiag :
      (∑ m ∈ M.divisors,
        ((m.totient : ℝ) * b m * (Real.log M + Real.log m) +
          ∑ k ∈ m.divisors, vonMangoldt (m / k) * (k.totient : ℝ) * b k) * f m ^ 2) =
      (∑ m ∈ M.divisors,
        ((m.totient : ℝ) * b m * Real.log (M / m : ℕ) +
          ∑ k ∈ m.divisors, vonMangoldt (m / k) * (k.totient : ℝ) * b k) * f m ^ 2) +
      2 * ∑ m ∈ M.divisors, (m.totient : ℝ) * Real.log m * (b m * f m) * f m := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro m hm
    rw [log_divisor_quotient hM hm]
    ring
  have hedge : (∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
      vonMangoldt (m / k) * (k.totient : ℝ) * f m * (b k * f k)) =
      ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * b k * f m * f k := by
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro k _
    ring
  rw [weightedDivisorJetEnergy_eq, hdiag,
    sum_range_divisorPacket_mul_divisorJetPacket_bilinear hM, hedge]
  field_simp [hMR]
  ring

private theorem sourceSmoothing_divisorPacket (M : ℕ) (S : Finset ℕ)
    (a f : ℕ → ℝ) (n : ℕ) :
    finiteSourceSmoothing S a (divisorRamanujanPacket M f) n =
      ∑ k ∈ M.divisors, f k * finiteSourceSmoothing S a (ramanujanLagCoefficient k) n := by
  change finiteSourceSmoothing S a
    (fun t => ∑ k ∈ M.divisors, f k * ramanujanLagCoefficient k t) n = _
  rw [finiteSourceSmoothing_sum]
  apply sum_congr rfl
  intro k _
  rw [finiteSourceSmoothing_const_mul]

private theorem smoothed_packet_mode_projection {M k : ℕ}
    (hk : k ∈ M.divisors) (S : Finset ℕ) (a f : ℕ → ℝ) :
    (∑ n ∈ range M,
      finiteSourceSmoothing S a (divisorRamanujanPacket M f) n *
        finiteSourceSmoothing S a (ramanujanLagCoefficient k) n) =
      ∑ n ∈ range M,
        divisorRamanujanPacket M (fun j => ramanujanAutocorrelationWeight S a j * f j) n *
          ramanujanLagCoefficient k n := by
  rw [sum_range_divisorPacket_mul_ramanujan hk]
  calc
    _ = ∑ j ∈ M.divisors, f j *
        (∑ n ∈ range M, finiteSourceSmoothing S a (ramanujanLagCoefficient j) n *
          finiteSourceSmoothing S a (ramanujanLagCoefficient k) n) := by
      simp only [sourceSmoothing_divisorPacket, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      ring
    _ = ∑ j ∈ M.divisors,
        if j = k then f k * ((M : ℝ) * k.totient * ramanujanAutocorrelationWeight S a k) else 0 := by
      apply sum_congr rfl
      intro j hj
      rw [sum_range_smoothedRamanujan_mul
        (Nat.pos_of_mem_divisors hj) (Nat.pos_of_mem_divisors hk)
        (Nat.dvd_of_mem_divisors hj) (Nat.dvd_of_mem_divisors hk)]
      by_cases hjk : j = k
      · subst j
        simp only [ite_true]
      · simp only [if_neg hjk, mul_zero]
    _ = _ := by rw [sum_ite_eq', if_pos hk]; ring

private theorem sourceSmoothing_jet {m : ℕ} (hm : 0 < m) (S : Finset ℕ)
    (a : ℕ → ℝ) (n : ℕ) :
    finiteSourceSmoothing S a (ramanujanLogDivisorJet m) n =
      ∑ k ∈ m.divisors, ramanujanJetConductorWeight m k *
        finiteSourceSmoothing S a (ramanujanLagCoefficient k) n := by
  have hj : ramanujanLogDivisorJet m =
      fun t => ∑ k ∈ m.divisors, ramanujanJetConductorWeight m k * ramanujanLagCoefficient k t :=
    funext (ramanujanLogDivisorJet_eq_weighted_conductors hm)
  rw [hj, finiteSourceSmoothing_sum]
  apply sum_congr rfl
  intro k _
  rw [finiteSourceSmoothing_const_mul]

private theorem smoothed_packet_jet_pair {M m : ℕ}
    (hM : 0 < M) (hm : m ∈ M.divisors) (S : Finset ℕ) (a f : ℕ → ℝ) :
    (∑ n ∈ range M,
      finiteSourceSmoothing S a (divisorRamanujanPacket M f) n *
        finiteSourceSmoothing S a (ramanujanLogDivisorJet m) n) =
      ∑ n ∈ range M,
        divisorRamanujanPacket M (fun j => ramanujanAutocorrelationWeight S a j * f j) n *
          ramanujanLogDivisorJet m n := by
  have hm0 := Nat.pos_of_mem_divisors hm
  have hkM (k : ℕ) (hk : k ∈ m.divisors) : k ∈ M.divisors :=
    Nat.mem_divisors.mpr
      ⟨(Nat.dvd_of_mem_divisors hk).trans (Nat.dvd_of_mem_divisors hm), hM.ne'⟩
  calc
    _ = ∑ k ∈ m.divisors, ramanujanJetConductorWeight m k *
        (∑ n ∈ range M,
          finiteSourceSmoothing S a (divisorRamanujanPacket M f) n *
            finiteSourceSmoothing S a (ramanujanLagCoefficient k) n) := by
      simp only [sourceSmoothing_jet hm0, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      apply sum_congr rfl
      intro n _
      ring
    _ = ∑ k ∈ m.divisors, ramanujanJetConductorWeight m k *
        (∑ n ∈ range M,
          divisorRamanujanPacket M (fun j => ramanujanAutocorrelationWeight S a j * f j) n *
            ramanujanLagCoefficient k n) := by
      apply sum_congr rfl
      intro k hk
      rw [smoothed_packet_mode_projection (hkM k hk)]
    _ = _ := by
      simp_rw [ramanujanLogDivisorJet_eq_weighted_conductors hm0, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      apply sum_congr rfl
      intro n _
      ring

/-- Smoothing both physical packets equals weighting the first packet by the source autocorrelation. -/
theorem sum_range_smoothedPacket_mul_smoothedJetPacket {M : ℕ}
    (hM : 0 < M) (S : Finset ℕ) (a f : ℕ → ℝ) :
    (∑ n ∈ range M,
      finiteSourceSmoothing S a (divisorRamanujanPacket M f) n *
        finiteSourceSmoothing S a (divisorJetPacket M f) n) =
      ∑ n ∈ range M,
        divisorRamanujanPacket M (fun j => ramanujanAutocorrelationWeight S a j * f j) n *
          divisorJetPacket M f n := by
  have hs (n : ℕ) : finiteSourceSmoothing S a (divisorJetPacket M f) n =
      ∑ m ∈ M.divisors, f m * finiteSourceSmoothing S a (ramanujanLogDivisorJet m) n := by
    change finiteSourceSmoothing S a
      (fun t => ∑ m ∈ M.divisors, f m * ramanujanLogDivisorJet m t) n = _
    rw [finiteSourceSmoothing_sum]
    apply sum_congr rfl
    intro m _
    rw [finiteSourceSmoothing_const_mul]
  calc
    _ = ∑ m ∈ M.divisors, f m *
        (∑ n ∈ range M,
          finiteSourceSmoothing S a (divisorRamanujanPacket M f) n *
            finiteSourceSmoothing S a (ramanujanLogDivisorJet m) n) := by
      simp only [hs, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      apply sum_congr rfl
      intro n _
      ring
    _ = ∑ m ∈ M.divisors, f m *
        (∑ n ∈ range M,
          divisorRamanujanPacket M (fun j => ramanujanAutocorrelationWeight S a j * f j) n *
            ramanujanLogDivisorJet m n) := by
      apply sum_congr rfl
      intro m hm
      rw [smoothed_packet_jet_pair hM hm]
    _ = _ := by
      simp only [divisorJetPacket, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      apply sum_congr rfl
      intro n _
      ring

/-- Every finite signed source gives a nonnegative weighted divisor energy. -/
theorem weightedDivisorJetEnergy_autocorrelation_nonneg (M : ℕ) (S : Finset ℕ)
    (a f : ℕ → ℝ) :
    0 ≤ weightedDivisorJetEnergy M (ramanujanAutocorrelationWeight S a) f := by
  apply sum_nonneg
  intro m _
  apply sum_nonneg
  intro k _
  exact mul_nonneg (mul_nonneg
    (mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
    (ramanujanAutocorrelationWeight_nonneg S a k)) (sq_nonneg _)

/-- The literal smoothed packet–jet pairing has an exact positive conductor-edge completion. -/
theorem weightedDivisorJetEnergy_eq_source_pairing {M : ℕ}
    (hM : 0 < M) (S : Finset ℕ) (a f : ℕ → ℝ) :
    weightedDivisorJetEnergy M (ramanujanAutocorrelationWeight S a) f =
      (∑ m ∈ M.divisors,
        ((m.totient : ℝ) * ramanujanAutocorrelationWeight S a m * (Real.log M + Real.log m) +
          ∑ k ∈ m.divisors,
            vonMangoldt (m / k) * (k.totient : ℝ) * ramanujanAutocorrelationWeight S a k) * f m ^ 2) -
      (2 / M) * ∑ n ∈ range M,
        finiteSourceSmoothing S a (divisorRamanujanPacket M f) n *
          finiteSourceSmoothing S a (divisorJetPacket M f) n := by
  rw [weightedDivisorJetEnergy_eq_period_pairing hM,
    sum_range_smoothedPacket_mul_smoothedJetPacket hM]

private theorem totient_mul_autocorrelationWeight {k : ℕ} (hk : 0 < k)
    (S : Finset ℕ) (a : ℕ → ℝ) :
    (k.totient : ℝ) * ramanujanAutocorrelationWeight S a k =
      ∑ i ∈ S, ∑ j ∈ S, a i * a j * ramanujanLagCoefficient k (Nat.dist i j) := by
  have hp : (k.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hk).ne'
  rw [ramanujanAutocorrelationWeight]
  field_simp [hp]

private theorem lower_jet_sum {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (∑ k ∈ m.divisors, vonMangoldt (m / k) * ramanujanLagCoefficient k n) =
      ramanujanLogDivisorJet m n - Real.log m * ramanujanLagCoefficient m n := by
  have hmm : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hm.ne'⟩
  have he := ramanujanLogDivisorJet_eq_weighted_conductors hm n
  simp only [ramanujanJetConductorWeight, add_mul, sum_add_distrib,
    ite_mul, zero_mul, sum_ite_eq', if_pos hmm] at he
  linarith only [he]

/-- The exact incoming smoothing charge is the reduced-lag adjunction deficit. -/
theorem sum_divisor_autocorrelationWeight_eq_adjunction_charge {m : ℕ}
    (hm : 0 < m) (S : Finset ℕ) (a : ℕ → ℝ) :
    (∑ k ∈ m.divisors,
      vonMangoldt (m / k) * (k.totient : ℝ) * ramanujanAutocorrelationWeight S a k) =
      ∑ i ∈ S, ∑ j ∈ S, a i * a j * ramanujanLagCoefficient m (Nat.dist i j) *
        (tameDifferent m -
          (Real.log (m / Nat.gcd m (Nat.dist i j) : ℕ) +
            tameDifferent (m / Nat.gcd m (Nat.dist i j)))) := by
  calc
    _ = ∑ k ∈ m.divisors, ∑ i ∈ S, ∑ j ∈ S,
        a i * a j * (vonMangoldt (m / k) * ramanujanLagCoefficient k (Nat.dist i j)) := by
      apply sum_congr rfl
      intro k hk
      rw [mul_assoc, totient_mul_autocorrelationWeight (Nat.pos_of_mem_divisors hk), mul_sum]
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ = ∑ i ∈ S, ∑ k ∈ m.divisors, ∑ j ∈ S,
        a i * a j * (vonMangoldt (m / k) * ramanujanLagCoefficient k (Nat.dist i j)) := by
      rw [sum_comm]
    _ = ∑ i ∈ S, ∑ j ∈ S, a i * a j *
        (∑ k ∈ m.divisors, vonMangoldt (m / k) * ramanujanLagCoefficient k (Nat.dist i j)) := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
      simp only [mul_sum]
    _ = _ := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [lower_jet_sum hm, ramanujanLogDivisorJet_eq_adjunction_gap hm]
      ring

/-- The reduced-lag adjunction deficit is positive semidefinite on every finite signed source. -/
theorem sum_adjunction_lag_charge_nonneg {m : ℕ}
    (hm : 0 < m) (S : Finset ℕ) (a : ℕ → ℝ) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S, a i * a j * ramanujanLagCoefficient m (Nat.dist i j) *
      (tameDifferent m -
        (Real.log (m / Nat.gcd m (Nat.dist i j) : ℕ) +
          tameDifferent (m / Nat.gcd m (Nat.dist i j)))) := by
  rw [← sum_divisor_autocorrelationWeight_eq_adjunction_charge hm]
  exact sum_nonneg fun k _ => mul_nonneg
    (mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
    (ramanujanAutocorrelationWeight_nonneg S a k)

#print axioms sum_range_divisorPacket_mul_divisorJetPacket_bilinear
#print axioms weightedDivisorJetEnergy_eq
#print axioms weightedDivisorJetEnergy_eq_period_pairing
#print axioms sum_range_smoothedPacket_mul_smoothedJetPacket
#print axioms weightedDivisorJetEnergy_autocorrelation_nonneg
#print axioms weightedDivisorJetEnergy_eq_source_pairing
#print axioms sum_divisor_autocorrelationWeight_eq_adjunction_charge
#print axioms sum_adjunction_lag_charge_nonneg
end
end GaloisForLFunctions.SuccessorShellArithmetic
