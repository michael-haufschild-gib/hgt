import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.DivisorJetGroundState
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.DivisorJetReciprocity
import GaloisForLFunctions.RHTower.CausallyAnchoredFutureAliasRegrouping

/-!
# The exact adjunction spectrum of the finite divisor graph

Totient-weighted Ramanujan reciprocity diagonalizes the prime-power divisor
energy, including its top valuation boundary. The mode `c_d(M/k)` has
adjunction eigenvalue `log d + tameDifferent d`. Reciprocal inversion gives
an exact spectral formula for every real divisor profile.

In the integer period the same quadratic form is multiplication by the
reduced-lag symbol `log(M/gcd(M,n)) + tameDifferent(M/gcd(M,n))`.
-/

open Finset ArithmeticFunction
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence CriticalArithmeticCorrelationTheory ArithmeticIntersectionTheory
noncomputable section

/-- The weighted graph generator, retaining both directions of each divisor edge. -/
def divisorJetGenerator (M : ℕ) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ a ∈ k.divisors, vonMangoldt (k / a) * (a.totient : ℝ) * (f k - f a)) +
    (k.totient : ℝ) * ∑ r ∈ (M / k).divisors, vonMangoldt r * (f k - f (k * r))

private theorem jet_lower_conductor_sum {k : ℕ} (hk : 0 < k) (n : ℕ) :
    (∑ a ∈ k.divisors, vonMangoldt (k / a) * ramanujanLagCoefficient a n) =
      ramanujanLogDivisorJet k n - Real.log k * ramanujanLagCoefficient k n := by
  have hkk : k ∈ k.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hk.ne'⟩
  have he := ramanujanLogDivisorJet_eq_weighted_conductors hk n
  simp only [ramanujanJetConductorWeight, add_mul, sum_add_distrib,
    ite_mul, zero_mul, sum_ite_eq', if_pos hkk] at he
  linarith only [he]

private theorem divisorJetGenerator_lower_mode {M d k : ℕ}
    (hM : 0 < M) (hd : d ∣ M) (hk : k ∣ M) :
    (∑ a ∈ k.divisors, vonMangoldt (k / a) * (a.totient : ℝ) *
      ramanujanLagCoefficient d (M / a)) =
        (d.totient : ℝ) * (ramanujanLogDivisorJet k (M / d) -
          Real.log k * ramanujanLagCoefficient k (M / d)) := by
  calc
    _ = (d.totient : ℝ) * ∑ a ∈ k.divisors,
        vonMangoldt (k / a) * ramanujanLagCoefficient a (M / d) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a ha
      have he := divisor_ramanujan_reciprocity hM hd
        ((Nat.dvd_of_mem_divisors ha).trans hk)
      calc
        _ = vonMangoldt (k / a) *
            ((a.totient : ℝ) * ramanujanLagCoefficient d (M / a)) := by ring
        _ = _ := by rw [he]; ring
    _ = _ := by rw [jet_lower_conductor_sum (Nat.pos_of_dvd_of_pos hk hM)]

private theorem divisorJetGenerator_upper_mode {M k : ℕ}
    (hM : 0 < M) (hk : k ∣ M) (d : ℕ) :
    (∑ r ∈ (M / k).divisors, vonMangoldt r * ramanujanLagCoefficient d (M / (k * r))) =
      Real.log (M / k : ℕ) * ramanujanLagCoefficient d (M / k) -
        ramanujanLogDivisorJet d (M / k) := by
  have hq : 0 < M / k :=
    Nat.div_pos (Nat.le_of_dvd hM hk) (Nat.pos_of_dvd_of_pos hk hM)
  simpa only [Nat.div_div_eq_div_mul] using
    sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet d hq

/-- Every reciprocal Ramanujan mode has its exact adjunction eigenvalue. -/
theorem divisorJetGenerator_ramanujan {M d k : ℕ}
    (hM : 0 < M) (hd : d ∣ M) (hk : k ∣ M) :
    divisorJetGenerator M (fun a => ramanujanLagCoefficient d (M / a)) k =
      (k.totient : ℝ) * (Real.log d + tameDifferent d) *
        ramanujanLagCoefficient d (M / k) := by
  have hdown :
      (∑ a ∈ k.divisors, vonMangoldt (k / a) * (a.totient : ℝ) *
        (ramanujanLagCoefficient d (M / k) - ramanujanLagCoefficient d (M / a))) =
      (k.totient : ℝ) * tameDifferent k * ramanujanLagCoefficient d (M / k) -
        (d.totient : ℝ) * (ramanujanLogDivisorJet k (M / d) -
          Real.log k * ramanujanLagCoefficient k (M / d)) := by
    simp only [mul_sub, sum_sub_distrib]
    rw [← sum_mul, sum_divisor_vonMangoldt_mul_totient,
      divisorJetGenerator_lower_mode hM hd hk]
    ring
  have hup :
      (∑ r ∈ (M / k).divisors, vonMangoldt r *
        (ramanujanLagCoefficient d (M / k) - ramanujanLagCoefficient d (M / (k * r)))) =
      ramanujanLogDivisorJet d (M / k) := by
    simp only [mul_sub, sum_sub_distrib]
    rw [← sum_mul, vonMangoldt_sum, divisorJetGenerator_upper_mode hM hk d]
    ring
  rw [divisorJetGenerator, hdown, hup]
  have hj := divisor_jet_reciprocity hM hd hk
  have hc := divisor_ramanujan_reciprocity hM hd hk
  linear_combination hj - Real.log k * hc

private theorem sum_divisor_chain_by_base {M : ℕ} (hM : 0 < M)
    (F : ℕ → ℕ → ℝ) :
    (∑ m ∈ M.divisors, ∑ k ∈ m.divisors, F m k) =
      ∑ k ∈ M.divisors, ∑ r ∈ (M / k).divisors, F (k * r) k := by
  calc
    _ = ∑ m ∈ M.divisors, ∑ r ∈ m.divisors, F m (m / r) := by
      apply sum_congr rfl
      intro m _
      exact (Nat.sum_div_divisors m (F m)).symm
    _ = ∑ k ∈ M.divisors, ∑ r ∈ (M / k).divisors, F (k * r) ((k * r) / r) :=
      _root_.RHTower.sum_divisors_sum_divisors_reindex hM.ne' (fun m r => F m (m / r))
    _ = _ := by
      apply sum_congr rfl
      intro k _
      apply sum_congr rfl
      intro r hr
      rw [Nat.mul_div_cancel _ (Nat.pos_of_mem_divisors hr)]

/-- The positive divisor-edge squares are exactly the graph generator's quadratic form. -/
theorem divisorJetEnergy_eq_generator {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    divisorJetEnergy M f = ∑ k ∈ M.divisors, f k * divisorJetGenerator M f k := by
  have hup :
      (∑ k ∈ M.divisors, f k * ((k.totient : ℝ) *
        ∑ r ∈ (M / k).divisors, vonMangoldt r * (f k - f (k * r)))) =
      ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * f k * (f k - f m) := by
    rw [sum_divisor_chain_by_base hM]
    apply sum_congr rfl
    intro k hk
    rw [mul_sum, mul_sum]
    apply sum_congr rfl
    intro r _
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_mem_divisors hk)]
    ring
  symm
  calc
    _ = (∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * f m * (f m - f k)) +
        ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
          vonMangoldt (m / k) * (k.totient : ℝ) * f k * (f k - f m) := by
      simp only [divisorJetGenerator, mul_add, sum_add_distrib]
      rw [hup]
      congr 1
      apply sum_congr rfl
      intro m _
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    _ = divisorJetEnergy M f := by
      rw [divisorJetEnergy, ← sum_add_distrib]
      apply sum_congr rfl
      intro m _
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro k _
      ring

#print axioms divisorJetGenerator_ramanujan
#print axioms divisorJetEnergy_eq_generator

private theorem divisorJetGenerator_add (M : ℕ) (f g : ℕ → ℝ) (k : ℕ) :
    divisorJetGenerator M (fun a => f a + g a) k =
      divisorJetGenerator M f k + divisorJetGenerator M g k := by
  have hfg (a : ℕ) : (f k + g k) - (f a + g a) = (f k - f a) + (g k - g a) := by ring
  simp only [divisorJetGenerator, hfg, mul_add, sum_add_distrib]
  ring

private theorem divisorJetGenerator_const_mul (M : ℕ) (c : ℝ) (f : ℕ → ℝ) (k : ℕ) :
    divisorJetGenerator M (fun a => c * f a) k = c * divisorJetGenerator M f k := by
  have hcf (a : ℕ) : c * f k - c * f a = c * (f k - f a) := by ring
  have hd : (∑ a ∈ k.divisors,
      vonMangoldt (k / a) * (a.totient : ℝ) * (c * (f k - f a))) =
      c * ∑ a ∈ k.divisors,
        vonMangoldt (k / a) * (a.totient : ℝ) * (f k - f a) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    ring
  have hu : (∑ r ∈ (M / k).divisors, vonMangoldt r * (c * (f k - f (k * r)))) =
      c * ∑ r ∈ (M / k).divisors, vonMangoldt r * (f k - f (k * r)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r _
    ring
  simp only [divisorJetGenerator, hcf]
  rw [hd, hu]
  ring

private theorem divisorJetGenerator_sum (M : ℕ) (S : Finset ℕ)
    (g : ℕ → ℕ → ℝ) (k : ℕ) :
    divisorJetGenerator M (fun a => ∑ d ∈ S, g d a) k =
      ∑ d ∈ S, divisorJetGenerator M (g d) k := by
  induction S using Finset.induction_on with
  | empty => simp [divisorJetGenerator]
  | @insert d S hd ih =>
    have he : (fun a => ∑ j ∈ insert d S, g j a) =
        (fun a => g d a + ∑ j ∈ S, g j a) := by
      funext a
      rw [sum_insert hd]
    rw [he, divisorJetGenerator_add, ih, sum_insert hd]

private theorem divisorJetGenerator_congr {M k : ℕ} (hM : 0 < M) (hk : k ∈ M.divisors)
    (f g : ℕ → ℝ) (hfg : ∀ a ∈ M.divisors, f a = g a) :
    divisorJetGenerator M f k = divisorJetGenerator M g k := by
  have hkM := Nat.dvd_of_mem_divisors hk
  unfold divisorJetGenerator
  rw [hfg k hk]
  apply congrArg₂ (· + ·)
  · apply sum_congr rfl
    intro a ha
    rw [hfg a (Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors ha).trans hkM, hM.ne'⟩)]
  · congr 1
    apply sum_congr rfl
    intro r hr
    have hkr : k * r ∈ M.divisors := Nat.mem_divisors.mpr
      ⟨(Nat.dvd_div_iff_mul_dvd hkM).mp (Nat.dvd_of_mem_divisors hr), hM.ne'⟩
    rw [hfg (k * r) hkr]

private theorem divisor_packet_reciprocal_coordinate {M d : ℕ}
    (hM : 0 < M) (hd : d ∣ M) (f : ℕ → ℝ) :
    (∑ k ∈ M.divisors,
      (k.totient : ℝ) * f k * ramanujanLagCoefficient d (M / k)) =
        (d.totient : ℝ) * divisorRamanujanPacket M f (M / d) := by
  rw [divisorRamanujanPacket, mul_sum]
  apply sum_congr rfl
  intro k hk
  have he := divisor_ramanujan_reciprocity hM hd (Nat.dvd_of_mem_divisors hk)
  calc
    _ = f k * ((k.totient : ℝ) * ramanujanLagCoefficient d (M / k)) := by ring
    _ = _ := by rw [he]; ring

/-- The finite divisor-edge energy has the exact adjunction spectrum, with every valuation boundary retained. -/
theorem divisorJetEnergy_eq_adjunction_spectrum {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    divisorJetEnergy M f = (1 / M) * ∑ d ∈ M.divisors,
      (d.totient : ℝ) * (Real.log d + tameDifferent d) *
        divisorRamanujanPacket M f (M / d) ^ 2 := by
  let a : ℕ → ℝ := fun d => (1 / M) * divisorRamanujanPacket M f (M / d)
  let g : ℕ → ℝ := fun k =>
    ∑ d ∈ M.divisors, a d * ramanujanLagCoefficient d (M / k)
  have hfg : ∀ k ∈ M.divisors, f k = g k := by
    intro k hk
    rw [divisor_profile_ramanujan_expansion hM hk f]
    change (1 / M) * (∑ d ∈ M.divisors,
      divisorRamanujanPacket M f (M / d) * ramanujanLagCoefficient d (M / k)) =
        ∑ d ∈ M.divisors, a d * ramanujanLagCoefficient d (M / k)
    rw [mul_sum]
    apply sum_congr rfl
    intro d _
    dsimp only [a]
    ring
  have hgen (k : ℕ) (hk : k ∈ M.divisors) :
      divisorJetGenerator M f k = ∑ d ∈ M.divisors,
        a d * ((k.totient : ℝ) * (Real.log d + tameDifferent d) *
          ramanujanLagCoefficient d (M / k)) := by
    rw [divisorJetGenerator_congr hM hk f g hfg]
    change divisorJetGenerator M
      (fun k => ∑ d ∈ M.divisors, a d * ramanujanLagCoefficient d (M / k)) k = _
    rw [divisorJetGenerator_sum]
    apply sum_congr rfl
    intro d hd
    rw [divisorJetGenerator_const_mul,
      divisorJetGenerator_ramanujan hM (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors hk)]
  rw [divisorJetEnergy_eq_generator hM f]
  calc
    _ = ∑ k ∈ M.divisors, ∑ d ∈ M.divisors,
        a d * (Real.log d + tameDifferent d) *
          ((k.totient : ℝ) * f k * ramanujanLagCoefficient d (M / k)) := by
      apply sum_congr rfl
      intro k hk
      rw [hgen k hk, mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ = ∑ d ∈ M.divisors, a d * (Real.log d + tameDifferent d) *
        (∑ k ∈ M.divisors,
          (k.totient : ℝ) * f k * ramanujanLagCoefficient d (M / k)) := by
      rw [sum_comm]
      simp only [mul_sum]
    _ = ∑ d ∈ M.divisors, a d * (Real.log d + tameDifferent d) *
        ((d.totient : ℝ) * divisorRamanujanPacket M f (M / d)) := by
      apply sum_congr rfl
      intro d hd
      rw [divisor_packet_reciprocal_coordinate hM (Nat.dvd_of_mem_divisors hd) f]
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      dsimp only [a]
      ring

#print axioms divisorJetEnergy_eq_adjunction_spectrum

private theorem divisorRamanujanPacket_gcd_period (M : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    divisorRamanujanPacket M f (Nat.gcd M n) = divisorRamanujanPacket M f n := by
  unfold divisorRamanujanPacket
  apply sum_congr rfl
  intro d hd
  rw [ramanujanLagCoefficient_gcd_period (Nat.dvd_of_mem_divisors hd)]

/-- In the integer period, the exact divisor energy is multiplication by the reduced-lag adjunction symbol. -/
theorem divisorJetEnergy_eq_period_symbol {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    divisorJetEnergy M f = (1 / M) * ∑ n ∈ range M,
      (Real.log (M / Nat.gcd M n : ℕ) + tameDifferent (M / Nat.gcd M n)) *
        divisorRamanujanPacket M f n ^ 2 := by
  have hp := sum_range_gcd_profile hM (fun g =>
    (Real.log (M / g : ℕ) + tameDifferent (M / g)) * divisorRamanujanPacket M f g ^ 2)
  simp only [divisorRamanujanPacket_gcd_period] at hp
  rw [divisorJetEnergy_eq_adjunction_spectrum hM f]
  congr 1
  calc
    _ = ∑ g ∈ M.divisors, ((M / g).totient : ℝ) *
        ((Real.log (M / g : ℕ) + tameDifferent (M / g)) *
          divisorRamanujanPacket M f g ^ 2) := by
      rw [← Nat.sum_div_divisors M (fun g => ((M / g).totient : ℝ) *
        ((Real.log (M / g : ℕ) + tameDifferent (M / g)) *
          divisorRamanujanPacket M f g ^ 2))]
      apply sum_congr rfl
      intro g hg
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hg) hM.ne']
      ring
    _ = _ := hp.symm

#print axioms divisorJetEnergy_eq_period_symbol
end
end GaloisForLFunctions.SuccessorShellArithmetic
