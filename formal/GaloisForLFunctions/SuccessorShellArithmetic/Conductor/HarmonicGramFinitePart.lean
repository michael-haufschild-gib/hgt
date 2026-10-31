import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.DivisorJetSpectrum
import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorMoments

/-!
# Exact harmonic finite parts on the conductor divisor lattice

Reciprocal Ramanujan inversion reduces every gcd-class harmonic sum to
the ordinary harmonic constant and the Mangoldt limits of nonpolar modes.
The logarithmic convolution then identifies the complete quadratic finite
part with positive divisor-edge energy plus one scalar counterterm.
Polarization exposes every mixed entry: only prime-power divisor edges survive.
-/

open Finset Filter ArithmeticFunction
open scoped Topology
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence CriticalArithmeticCorrelationTheory ArithmeticIntersectionTheory
noncomputable section

private theorem ramanujan_harmonic_finite_part {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, ramanujanLagCoefficient m n / (n : ℝ)) -
        (if m = 1 then Real.log N else 0)) atTop
      (𝓝 ((if m = 1 then Real.eulerMascheroniConstant else 0) - vonMangoldt m)) := by
  by_cases hm1 : m = 1
  · subst m
    have hc (n : ℕ) : ramanujanLagCoefficient 1 n = 1 := by
      simpa only [Nat.totient_one, Nat.cast_one] using
        ramanujanLagCoefficient_of_dvd (one_dvd n)
    simpa only [hc, ite_true, show vonMangoldt 1 = 0 from by simp,
      sub_zero, HTGeometry.sum_Icc_one_div_eq_harmonic] using
      Real.tendsto_harmonic_sub_log
  · simpa only [if_neg hm1, sub_zero, zero_sub,
      ramanujanNaturalCoefficient_re_eq_lagCoefficient] using
      _root_.RHTower.tendsto_pm_ramanujan_harmonic (by omega : 1 < m)

private theorem divisor_packet_harmonic_finite_part {M : ℕ} (hM : 0 < M)
    (a : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, divisorRamanujanPacket M a n / (n : ℝ)) -
        a 1 * Real.log N) atTop
      (𝓝 (a 1 * Real.eulerMascheroniConstant -
        ∑ d ∈ M.divisors, a d * vonMangoldt d)) := by
  have h1 : 1 ∈ M.divisors := Nat.mem_divisors.mpr ⟨one_dvd M, hM.ne'⟩
  have he (N : ℕ) :
      (∑ n ∈ Icc 1 N, divisorRamanujanPacket M a n / (n : ℝ)) - a 1 * Real.log N =
        ∑ d ∈ M.divisors, a d *
          ((∑ n ∈ Icc 1 N, ramanujanLagCoefficient d n / (n : ℝ)) -
            (if d = 1 then Real.log N else 0)) := by
    simp only [mul_sub, sum_sub_distrib, mul_ite, mul_zero, sum_ite_eq', if_pos h1]
    congr 1
    simp only [divisorRamanujanPacket, sum_div, mul_sum, mul_div_assoc]
    rw [sum_comm]
  have hlim := tendsto_finsetSum M.divisors (fun d hd =>
    (ramanujan_harmonic_finite_part (Nat.pos_of_mem_divisors hd)).const_mul (a d))
  have hv : (∑ d ∈ M.divisors, a d *
      ((if d = 1 then Real.eulerMascheroniConstant else 0) - vonMangoldt d)) =
      a 1 * Real.eulerMascheroniConstant - ∑ d ∈ M.divisors, a d * vonMangoldt d := by
    simp only [mul_sub, sum_sub_distrib, mul_ite, mul_zero, sum_ite_eq', if_pos h1]
  rw [hv] at hlim
  exact hlim.congr fun N => (he N).symm

private def gcdProfileCoefficient (M : ℕ) (V : ℕ → ℝ) (d : ℕ) : ℝ :=
  (1 / M) * ∑ j ∈ M.divisors, V (M / j) * ramanujanLagCoefficient j (M / d)

private theorem gcd_profile_expansion {M : ℕ} (hM : 0 < M) (V : ℕ → ℝ) (n : ℕ) :
    V (Nat.gcd M n) = divisorRamanujanPacket M (gcdProfileCoefficient M V) n := by
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
  dsimp only [gcdProfileCoefficient]
  ring

private theorem gcdProfileCoefficient_one (M : ℕ) (V : ℕ → ℝ) :
    gcdProfileCoefficient M V 1 =
      (1 / M) * ∑ j ∈ M.divisors, (j.totient : ℝ) * V (M / j) := by
  rw [gcdProfileCoefficient, Nat.div_one]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [ramanujanLagCoefficient_of_dvd (Nat.dvd_of_mem_divisors hj)]
  ring

private theorem gcdProfileCoefficient_mangoldt {M : ℕ} (hM : 0 < M) (V : ℕ → ℝ) :
    (∑ d ∈ M.divisors, gcdProfileCoefficient M V d * vonMangoldt d) =
      (1 / M) * ∑ j ∈ M.divisors, (j.totient : ℝ) * V (M / j) *
        (Real.log M - (Real.log j + tameDifferent j)) := by
  calc
    _ = (1 / M) * ∑ j ∈ M.divisors, V (M / j) *
        (∑ d ∈ M.divisors, vonMangoldt d * ramanujanLagCoefficient j (M / d)) := by
      simp only [gcdProfileCoefficient, mul_sum, sum_mul]
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

/-- The harmonic finite part of every function of the gcd is an exact adjunction average. -/
theorem tendsto_gcd_profile_harmonic_finitePart {M : ℕ} (hM : 0 < M) (V : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, V (Nat.gcd M n) / (n : ℝ)) -
        ((1 / M) * ∑ j ∈ M.divisors, (j.totient : ℝ) * V (M / j)) * Real.log N)
      atTop (𝓝 ((1 / M) * ∑ j ∈ M.divisors,
        (j.totient : ℝ) * V (M / j) *
          (Real.eulerMascheroniConstant - Real.log M + Real.log j + tameDifferent j))) := by
  have h := divisor_packet_harmonic_finite_part hM (gcdProfileCoefficient M V)
  simp only [← gcd_profile_expansion hM V, gcdProfileCoefficient_one,
    gcdProfileCoefficient_mangoldt hM V] at h
  convert h using 1
  congr 1
  simp only [mul_sum, sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  ring

private theorem packet_gcd_period (M : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    divisorRamanujanPacket M f (Nat.gcd M n) = divisorRamanujanPacket M f n := by
  unfold divisorRamanujanPacket
  apply sum_congr rfl
  intro d hd
  rw [ramanujanLagCoefficient_gcd_period (Nat.dvd_of_mem_divisors hd)]

/-- Reciprocal evaluation preserves the totient-weighted quadratic mass. -/
theorem divisorPacket_reciprocal_plancherel {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    (1 / M) * ∑ d ∈ M.divisors,
      (d.totient : ℝ) * divisorRamanujanPacket M f (M / d) ^ 2 =
        ∑ m ∈ M.divisors, (m.totient : ℝ) * f m ^ 2 := by
  have hp := sum_range_gcd_profile hM (fun n => divisorRamanujanPacket M f n ^ 2)
  simp only [packet_gcd_period] at hp
  have hflip : (∑ d ∈ M.divisors,
      (d.totient : ℝ) * divisorRamanujanPacket M f (M / d) ^ 2) =
      ∑ d ∈ M.divisors, ((M / d).totient : ℝ) * divisorRamanujanPacket M f d ^ 2 := by
    rw [← Nat.sum_div_divisors M (fun d =>
      ((M / d).totient : ℝ) * divisorRamanujanPacket M f d ^ 2)]
    apply sum_congr rfl
    intro d hd
    rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hM.ne']
  rw [hflip, ← hp]
  have hpl := sum_range_ramanujan_packet_sq M.divisors f M
    (fun _ hd => Nat.pos_of_mem_divisors hd) (fun _ hd => Nat.dvd_of_mem_divisors hd)
  change (1 / M) * (∑ n ∈ range M,
    (∑ m ∈ M.divisors, f m * ramanujanLagCoefficient m n) ^ 2) = _
  rw [hpl, ← mul_assoc]
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hcancel : (1 / (M : ℝ)) * M = 1 := by field_simp [hMR]
  rw [hcancel, one_mul]
  apply sum_congr rfl
  intro m _
  ring

/-- The complete harmonic Gram finite part is a scalar counterterm plus positive divisor-edge energy. -/
theorem tendsto_divisorPacket_sq_harmonic_finitePart {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, divisorRamanujanPacket M f n ^ 2 / (n : ℝ)) -
        (∑ m ∈ M.divisors, (m.totient : ℝ) * f m ^ 2) * Real.log N) atTop
      (𝓝 ((Real.eulerMascheroniConstant - Real.log M) *
        (∑ m ∈ M.divisors, (m.totient : ℝ) * f m ^ 2) + divisorJetEnergy M f)) := by
  have h := tendsto_gcd_profile_harmonic_finitePart hM
    (fun n => divisorRamanujanPacket M f n ^ 2)
  simp only [packet_gcd_period, divisorPacket_reciprocal_plancherel hM f] at h
  convert h using 1
  congr 1
  rw [divisorJetEnergy_eq_adjunction_spectrum hM f,
    ← divisorPacket_reciprocal_plancherel hM f]
  simp only [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  ring

#print axioms tendsto_gcd_profile_harmonic_finitePart
#print axioms divisorPacket_reciprocal_plancherel
#print axioms tendsto_divisorPacket_sq_harmonic_finitePart

private theorem log_divisor_quotient {M m : ℕ} (hM : 0 < M) (hm : m ∈ M.divisors) :
    Real.log (M / m : ℕ) = Real.log M - Real.log m := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hm).ne'
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have he : ((M / m : ℕ) : ℝ) = (M : ℝ) / m := by
    apply (eq_div_iff hmR).mpr
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hm)
  rw [he, Real.log_div hMR hmR]

/-- Only prime-power divisor edges contribute mixed terms to the harmonic finite part. -/
theorem tendsto_divisorPacket_sq_harmonic_primeLocal {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, divisorRamanujanPacket M f n ^ 2 / (n : ℝ)) -
        (∑ m ∈ M.divisors, (m.totient : ℝ) * f m ^ 2) * Real.log N) atTop
      (𝓝 ((∑ m ∈ M.divisors,
          (m.totient : ℝ) * (Real.eulerMascheroniConstant - Real.log m + tameDifferent m) *
            f m ^ 2) -
        2 * ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
          vonMangoldt (m / k) * (k.totient : ℝ) * f m * f k)) := by
  have he : (Real.eulerMascheroniConstant - Real.log M) *
        (∑ m ∈ M.divisors, (m.totient : ℝ) * f m ^ 2) + divisorJetEnergy M f =
      (∑ m ∈ M.divisors,
        (m.totient : ℝ) * (Real.eulerMascheroniConstant - Real.log m + tameDifferent m) *
          f m ^ 2) -
        2 * ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
          vonMangoldt (m / k) * (k.totient : ℝ) * f m * f k := by
    rw [divisorJetEnergy_eq, ← add_sub_assoc, mul_sum, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro m hm
    rw [log_divisor_quotient hM hm]
    ring
  exact he ▸ tendsto_divisorPacket_sq_harmonic_finitePart hM f

#print axioms tendsto_divisorPacket_sq_harmonic_primeLocal

private theorem weighted_square_polarization (S : Finset ℕ) (w f g : ℕ → ℝ) :
    ((∑ m ∈ S, w m * (f m + g m) ^ 2) -
        (∑ m ∈ S, w m * f m ^ 2) - (∑ m ∈ S, w m * g m ^ 2)) / 2 =
      ∑ m ∈ S, w m * f m * g m := by
  rw [← sum_sub_distrib, ← sum_sub_distrib, sum_div]
  apply sum_congr rfl
  intro m _
  ring

private theorem divisorPacket_add (M : ℕ) (f g : ℕ → ℝ) (n : ℕ) :
    divisorRamanujanPacket M (fun m => f m + g m) n =
      divisorRamanujanPacket M f n + divisorRamanujanPacket M g n := by
  simp only [divisorRamanujanPacket, add_mul, sum_add_distrib]

private theorem divisorJetEnergy_polarization (M : ℕ) (f g : ℕ → ℝ) :
    (divisorJetEnergy M (fun m => f m + g m) - divisorJetEnergy M f -
        divisorJetEnergy M g) / 2 =
      ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * (f m - f k) * (g m - g k) := by
  rw [divisorJetEnergy, divisorJetEnergy, divisorJetEnergy,
    ← sum_sub_distrib, ← sum_sub_distrib, sum_div]
  apply sum_congr rfl
  intro m _
  rw [← sum_sub_distrib, ← sum_sub_distrib, sum_div]
  apply sum_congr rfl
  intro k _
  ring

/-- Polarization retains every mixed conductor entry in the harmonic Gram finite part. -/
theorem tendsto_divisorPacket_mul_harmonic_finitePart {M : ℕ} (hM : 0 < M)
    (f g : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, divisorRamanujanPacket M f n * divisorRamanujanPacket M g n /
        (n : ℝ)) - (∑ m ∈ M.divisors, (m.totient : ℝ) * f m * g m) * Real.log N) atTop
      (𝓝 ((Real.eulerMascheroniConstant - Real.log M) *
        (∑ m ∈ M.divisors, (m.totient : ℝ) * f m * g m) +
        ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
          vonMangoldt (m / k) * (k.totient : ℝ) * (f m - f k) * (g m - g k))) := by
  have hf := tendsto_divisorPacket_sq_harmonic_finitePart hM f
  have hg := tendsto_divisorPacket_sq_harmonic_finitePart hM g
  have hfg := tendsto_divisorPacket_sq_harmonic_finitePart hM (fun m => f m + g m)
  have hlim := ((hfg.sub hf).sub hg).div_const 2
  have hmass := weighted_square_polarization M.divisors (fun m => (m.totient : ℝ)) f g
  have hjet := divisorJetEnergy_polarization M f g
  have he (N : ℕ) :
      (((∑ n ∈ Icc 1 N, divisorRamanujanPacket M (fun m => f m + g m) n ^ 2 / (n : ℝ)) -
          (∑ m ∈ M.divisors, (m.totient : ℝ) * (f m + g m) ^ 2) * Real.log N) -
        ((∑ n ∈ Icc 1 N, divisorRamanujanPacket M f n ^ 2 / (n : ℝ)) -
          (∑ m ∈ M.divisors, (m.totient : ℝ) * f m ^ 2) * Real.log N) -
        ((∑ n ∈ Icc 1 N, divisorRamanujanPacket M g n ^ 2 / (n : ℝ)) -
          (∑ m ∈ M.divisors, (m.totient : ℝ) * g m ^ 2) * Real.log N)) / 2 =
      (∑ n ∈ Icc 1 N, divisorRamanujanPacket M f n * divisorRamanujanPacket M g n /
        (n : ℝ)) - (∑ m ∈ M.divisors, (m.totient : ℝ) * f m * g m) * Real.log N := by
    have hsum :
        ((∑ n ∈ Icc 1 N, (divisorRamanujanPacket M f n + divisorRamanujanPacket M g n) ^ 2 /
          (n : ℝ)) - (∑ n ∈ Icc 1 N, divisorRamanujanPacket M f n ^ 2 / (n : ℝ)) -
          (∑ n ∈ Icc 1 N, divisorRamanujanPacket M g n ^ 2 / (n : ℝ))) / 2 =
        ∑ n ∈ Icc 1 N, divisorRamanujanPacket M f n * divisorRamanujanPacket M g n / (n : ℝ) := by
      simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        weighted_square_polarization (Icc 1 N) (fun n => (n : ℝ)⁻¹)
          (divisorRamanujanPacket M f) (divisorRamanujanPacket M g)
    simp only [divisorPacket_add]
    linear_combination hsum - Real.log N * hmass
  have hval :
      (((Real.eulerMascheroniConstant - Real.log M) *
          (∑ m ∈ M.divisors, (m.totient : ℝ) * (f m + g m) ^ 2) +
          divisorJetEnergy M (fun m => f m + g m)) -
        ((Real.eulerMascheroniConstant - Real.log M) *
          (∑ m ∈ M.divisors, (m.totient : ℝ) * f m ^ 2) + divisorJetEnergy M f) -
        ((Real.eulerMascheroniConstant - Real.log M) *
          (∑ m ∈ M.divisors, (m.totient : ℝ) * g m ^ 2) + divisorJetEnergy M g)) / 2 =
      (Real.eulerMascheroniConstant - Real.log M) *
        (∑ m ∈ M.divisors, (m.totient : ℝ) * f m * g m) +
        ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
          vonMangoldt (m / k) * (k.totient : ℝ) * (f m - f k) * (g m - g k) := by
    linear_combination (Real.eulerMascheroniConstant - Real.log M) * hmass + hjet
  rw [hval] at hlim
  exact hlim.congr he

#print axioms tendsto_divisorPacket_mul_harmonic_finitePart

private theorem divisorJet_bilinear_expansion (M : ℕ) (f g : ℕ → ℝ) :
    (∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
      vonMangoldt (m / k) * (k.totient : ℝ) * (f m - f k) * (g m - g k)) =
      (∑ m ∈ M.divisors,
        (m.totient : ℝ) * (Real.log (M / m : ℕ) + tameDifferent m) * f m * g m) -
      ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * (f m * g k + f k * g m) := by
  have hd := weighted_square_polarization M.divisors
    (fun m => (m.totient : ℝ) * (Real.log (M / m : ℕ) + tameDifferent m)) f g
  have he := divisorJetEnergy_polarization M f g
  rw [divisorJetEnergy_eq, divisorJetEnergy_eq, divisorJetEnergy_eq] at he
  have hc :
      (∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * (f m + g m) * (f k + g k)) -
      (∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * f m * f k) -
      (∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * g m * g k) =
      ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
        vonMangoldt (m / k) * (k.totient : ℝ) * (f m * g k + f k * g m) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m _
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    ring
  linear_combination -he + hd - hc

/-- The bilinear harmonic finite part has only diagonal and prime-power divisor couplings. -/
theorem tendsto_divisorPacket_mul_harmonic_primeLocal {M : ℕ} (hM : 0 < M)
    (f g : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, divisorRamanujanPacket M f n * divisorRamanujanPacket M g n /
        (n : ℝ)) - (∑ m ∈ M.divisors, (m.totient : ℝ) * f m * g m) * Real.log N) atTop
      (𝓝 ((∑ m ∈ M.divisors,
        (m.totient : ℝ) * (Real.eulerMascheroniConstant - Real.log m + tameDifferent m) *
          f m * g m) -
        ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
          vonMangoldt (m / k) * (k.totient : ℝ) * (f m * g k + f k * g m))) := by
  have he : (Real.eulerMascheroniConstant - Real.log M) *
        (∑ m ∈ M.divisors, (m.totient : ℝ) * f m * g m) +
        (∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
          vonMangoldt (m / k) * (k.totient : ℝ) * (f m - f k) * (g m - g k)) =
      (∑ m ∈ M.divisors,
        (m.totient : ℝ) * (Real.eulerMascheroniConstant - Real.log m + tameDifferent m) *
          f m * g m) -
        ∑ m ∈ M.divisors, ∑ k ∈ m.divisors,
          vonMangoldt (m / k) * (k.totient : ℝ) * (f m * g k + f k * g m) := by
    rw [divisorJet_bilinear_expansion, ← add_sub_assoc, mul_sum, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro m hm
    rw [log_divisor_quotient hM hm]
    ring
  exact he ▸ tendsto_divisorPacket_mul_harmonic_finitePart hM f g

#print axioms tendsto_divisorPacket_mul_harmonic_primeLocal

private def conductorIndicator (m k : ℕ) : ℝ := if k = m then 1 else 0

private theorem packet_indicator {M m : ℕ} (hm : m ∈ M.divisors) (n : ℕ) :
    divisorRamanujanPacket M (conductorIndicator m) n = ramanujanLagCoefficient m n := by
  simp only [divisorRamanujanPacket, conductorIndicator, ite_mul, one_mul, zero_mul,
    sum_ite_eq', if_pos hm]

private theorem indicator_weighted_square {S : Finset ℕ} {m : ℕ} (hm : m ∈ S)
    (w : ℕ → ℝ) :
    (∑ k ∈ S, w k * conductorIndicator m k ^ 2) = w m := by
  rw [sum_eq_single_of_mem m hm]
  · simp only [conductorIndicator, ite_true, one_pow, mul_one]
  · intro k _ hkm
    simp only [conductorIndicator, if_neg hkm, zero_pow (by norm_num : 2 ≠ 0), mul_zero]

private theorem indicator_divisor_coupling {M m : ℕ} (hm : m ∈ M.divisors) (l : ℕ) :
    (∑ a ∈ M.divisors, ∑ b ∈ a.divisors,
      vonMangoldt (a / b) * (b.totient : ℝ) * conductorIndicator m a * conductorIndicator l b) =
      if l ∣ m then vonMangoldt (m / l) * (l.totient : ℝ) else 0 := by
  rw [sum_eq_single_of_mem m hm]
  · have hmem : l ∈ m.divisors ↔ l ∣ m :=
      ⟨Nat.dvd_of_mem_divisors, fun h => Nat.mem_divisors.mpr
        ⟨h, (Nat.pos_of_mem_divisors hm).ne'⟩⟩
    simp only [conductorIndicator, ite_true, mul_one, mul_ite, mul_zero, sum_ite_eq', hmem]
  · intro a _ ham
    simp only [conductorIndicator, if_neg ham, mul_zero, zero_mul, sum_const_zero]

/-- The diagonal harmonic Gram finite part is the conductor's tame-different correction. -/
theorem tendsto_ramanujan_sq_harmonic_finitePart {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, ramanujanLagCoefficient m n ^ 2 / (n : ℝ)) -
        (m.totient : ℝ) * Real.log N) atTop
      (𝓝 ((m.totient : ℝ) *
        (Real.eulerMascheroniConstant - Real.log m + tameDifferent m))) := by
  have hmm : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hm.ne'⟩
  have h := tendsto_divisorPacket_sq_harmonic_primeLocal hm (conductorIndicator m)
  simpa only [packet_indicator hmm, indicator_weighted_square hmm,
    indicator_divisor_coupling hmm, if_pos (dvd_refl m), Nat.div_self hm,
    vonMangoldt_apply_one, zero_mul, mul_zero, sub_zero] using h

/-- Distinct conductors interact only along prime-power divisibility in the harmonic finite part. -/
theorem tendsto_ramanujan_mul_harmonic_of_ne {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hml : m ≠ l) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N,
      ramanujanLagCoefficient m n * ramanujanLagCoefficient l n / (n : ℝ)) atTop
      (𝓝 (-((if l ∣ m then vonMangoldt (m / l) * (l.totient : ℝ) else 0) +
        (if m ∣ l then vonMangoldt (l / m) * (m.totient : ℝ) else 0)))) := by
  let M := m * l
  have hM : 0 < M := Nat.mul_pos hm hl
  have hmM : m ∈ M.divisors := Nat.mem_divisors.mpr ⟨dvd_mul_right m l, hM.ne'⟩
  have hlM : l ∈ M.divisors := Nat.mem_divisors.mpr ⟨dvd_mul_left l m, hM.ne'⟩
  have hz (k : ℕ) : conductorIndicator m k * conductorIndicator l k = 0 := by
    by_cases hkm : k = m
    · subst k
      simp only [conductorIndicator, if_neg hml, mul_zero]
    · simp only [conductorIndicator, if_neg hkm, zero_mul]
  have hcross :
      (∑ a ∈ M.divisors, ∑ b ∈ a.divisors,
        vonMangoldt (a / b) * (b.totient : ℝ) *
          (conductorIndicator m a * conductorIndicator l b +
            conductorIndicator m b * conductorIndicator l a)) =
      (if l ∣ m then vonMangoldt (m / l) * (l.totient : ℝ) else 0) +
        (if m ∣ l then vonMangoldt (l / m) * (m.totient : ℝ) else 0) := by
    simp only [mul_add, sum_add_distrib]
    rw [← indicator_divisor_coupling hmM l, ← indicator_divisor_coupling hlM m]
    apply congrArg₂ (· + ·)
    · apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      ring
    · apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      ring
  have h := tendsto_divisorPacket_mul_harmonic_primeLocal hM
    (conductorIndicator m) (conductorIndicator l)
  simp only [packet_indicator hmM, packet_indicator hlM, mul_assoc, hz,
    mul_zero, sum_const_zero, zero_mul, sub_zero, zero_sub] at h
  simp only [mul_assoc] at hcross
  exact hcross ▸ h

#print axioms tendsto_ramanujan_sq_harmonic_finitePart
#print axioms tendsto_ramanujan_mul_harmonic_of_ne

end
end GaloisForLFunctions.SuccessorShellArithmetic
