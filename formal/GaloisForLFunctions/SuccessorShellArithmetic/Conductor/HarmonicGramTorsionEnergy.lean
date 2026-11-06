import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.HarmonicGramFinitePart
import GaloisForLFunctions.ArithmeticElectrostatics.TheTorsionCountertermIsLogarithmic

/-!
# The harmonic Gram finite part is torsion intersection energy

The sharp harmonic cutoff and the primitive torsion-orbit intersection
have the same mixed entries. The diagonal differs by Euler's constant.
Finite polarization identifies every packet's finite part, and the
logarithmic torsion counterterm bounds its absolute quadratic form.
-/

open Finset Filter ArithmeticFunction
open scoped Topology
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence CriticalArithmeticCorrelationTheory ArithmeticIntersectionTheory
  ArithmeticEffectivityTheory RenormalizedArithmeticPotentialTheory
noncomputable section

private theorem orbitIntersection_distinct_eq_add {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hml : m ≠ l) :
    orbitIntersection m l =
      (if l ∣ m then vonMangoldt (m / l) * (l.totient : ℝ) else 0) +
        (if m ∣ l then vonMangoldt (l / m) * (m.totient : ℝ) else 0) := by
  rw [orbitIntersection_eq hm hl hml]
  by_cases hlm : l ∣ m
  · have hnml : ¬ m ∣ l := fun h => hml (Nat.dvd_antisymm h hlm)
    simp only [if_pos hlm, if_neg hnml, add_zero]
    ring
  · simp only [if_neg hlm, zero_add]
    split_ifs <;> ring

/-- The sharp harmonic Gram finite part is Euler's scalar term minus torsion intersection. -/
theorem tendsto_ramanujan_harmonicGram_torsion {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, ramanujanLagCoefficient m n * ramanujanLagCoefficient l n / (n : ℝ)) -
        (if m = l then (m.totient : ℝ) else 0) * Real.log N) atTop
      (𝓝 (Real.eulerMascheroniConstant * (if m = l then (m.totient : ℝ) else 0) -
        orbitIntersection m l)) := by
  by_cases hml : m = l
  · subst l
    have he : Real.eulerMascheroniConstant * (m.totient : ℝ) - orbitIntersection m m =
        (m.totient : ℝ) * (Real.eulerMascheroniConstant - Real.log m + tameDifferent m) := by
      rw [ArithmeticElectrostatics.orbitIntersection_self_eq hm,
        ArithmeticElectrostatics.localCorrection_eq_totient_mul_tameDifferent]
      ring
    simpa only [ite_true, he, pow_two] using tendsto_ramanujan_sq_harmonic_finitePart hm
  · simpa only [if_neg hml, zero_mul, mul_zero, sub_zero, zero_sub,
      orbitIntersection_distinct_eq_add hm hl hml] using
      tendsto_ramanujan_mul_harmonic_of_ne hm hl hml

private theorem conductor_diagonal_sum (S : Finset ℕ) (f : ℕ → ℝ) (c : ℝ) :
    (∑ m ∈ S, ∑ l ∈ S, f m * f l * ((if m = l then (m.totient : ℝ) else 0) * c)) =
      c * ∑ m ∈ S, (m.totient : ℝ) * f m ^ 2 := by
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  rw [sum_eq_single_of_mem m hm]
  · simp only [ite_true]
    ring
  · intro l _ hlm
    simp only [if_neg (Ne.symm hlm), zero_mul, mul_zero]

/-- In the unit-mass conductor basis, the finite part is Euler's scalar minus normalized torsion intersection. -/
theorem tendsto_normalizedRamanujan_harmonicGram_torsion {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)) -
        (if m = l then Real.log N else 0)) atTop
      (𝓝 ((if m = l then Real.eulerMascheroniConstant else 0) -
        orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)))) := by
  let d := Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)
  have hc : (if m = l then (m.totient : ℝ) else 0) / d = if m = l then 1 else 0 := by
    by_cases hml : m = l
    · subst l
      have hφ : (m.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hm).ne'
      simp only [ite_true, d, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg _), div_self hφ]
    · simp only [if_neg hml, zero_div]
  have hs (N : ℕ) :
      (∑ n ∈ Icc 1 N, ramanujanLagCoefficient m n * ramanujanLagCoefficient l n / (n : ℝ)) / d =
      ∑ n ∈ Icc 1 N, normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ) := by
    rw [sum_div]
    apply sum_congr rfl
    intro n _
    rw [normalizedRamanujanMode_eq_coefficient hm, normalizedRamanujanMode_eq_coefficient hl]
    dsimp only [d]
    ring
  have hv :
      (Real.eulerMascheroniConstant * (if m = l then (m.totient : ℝ) else 0) -
        orbitIntersection m l) / d =
      (if m = l then Real.eulerMascheroniConstant else 0) - orbitIntersection m l / d := by
    rw [sub_div, mul_div_assoc, hc]
    split_ifs <;> ring
  have h := (tendsto_ramanujan_harmonicGram_torsion hm hl).div_const d
  rw [hv] at h
  refine h.congr fun N => ?_
  rw [sub_div, hs]
  have he : ((if m = l then (m.totient : ℝ) else 0) * Real.log N) / d =
      (if m = l then Real.log N else 0) := by
    calc
      _ = ((if m = l then (m.totient : ℝ) else 0) / d) * Real.log N := by ring
      _ = _ := by rw [hc]; split_ifs <;> ring
  rw [he]

/-- Along a divisor tower, the normalized harmonic entry is the Hecke charge with its totient ratio. -/
theorem tendsto_normalizedRamanujan_harmonicGram_multiple {m t : ℕ}
    (hm : 0 < m) (ht : 1 < t) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N,
      normalizedRamanujanMode m n * normalizedRamanujanMode (m * t) n / (n : ℝ)) atTop
      (𝓝 (-vonMangoldt t * (Real.sqrt (m.totient : ℝ) /
        Real.sqrt ((m * t).totient : ℝ)))) := by
  have hmt : 0 < m * t := Nat.mul_pos hm (by omega)
  have hne : m ≠ m * t := by
    intro h
    have he : m * 1 = m * t := by simpa only [Nat.mul_one] using h
    have ht1 := Nat.eq_of_mul_eq_mul_left hm he
    omega
  have h := tendsto_normalizedRamanujan_harmonicGram_torsion hm hmt
  simp only [if_neg hne, sub_zero, zero_sub, orbitIntersection_hecke hm ht] at h
  have hφ : 0 < Real.sqrt (m.totient : ℝ) := Real.sqrt_pos.mpr
    (by exact_mod_cast Nat.totient_pos.mpr hm)
  have hψ : 0 < Real.sqrt ((m * t).totient : ℝ) := Real.sqrt_pos.mpr
    (by exact_mod_cast Nat.totient_pos.mpr hmt)
  have he : -((m.totient : ℝ) * vonMangoldt t /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt ((m * t).totient : ℝ))) =
      -vonMangoldt t * (Real.sqrt (m.totient : ℝ) / Real.sqrt ((m * t).totient : ℝ)) := by
    have hs : Real.sqrt (m.totient : ℝ) ^ 2 = (m.totient : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg _)
    calc
      _ = -(Real.sqrt (m.totient : ℝ) ^ 2 * vonMangoldt t /
          (Real.sqrt (m.totient : ℝ) * Real.sqrt ((m * t).totient : ℝ))) := by rw [hs]
      _ = _ := by field_simp [hφ.ne', hψ.ne']
  exact he ▸ h

/-- Each prime-power conductor edge has exactly the logarithm of its prime as harmonic coupling. -/
theorem tendsto_normalizedRamanujan_harmonicGram_primePower {m p k : ℕ}
    (hm : 0 < m) (hp : p.Prime) (hk : 0 < k) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N,
      normalizedRamanujanMode m n * normalizedRamanujanMode (m * p ^ k) n / (n : ℝ)) atTop
      (𝓝 (-Real.log p * (Real.sqrt (m.totient : ℝ) /
        Real.sqrt ((m * p ^ k).totient : ℝ)))) := by
  rcases k with _ | k
  · omega
  · have ht : 1 < p ^ (k + 1) := by
      have hpow : 1 ≤ p ^ k := one_le_pow₀ hp.one_le
      rw [pow_succ]
      nlinarith only [hp.two_le, hpow]
    have hΛ : vonMangoldt (p ^ (k + 1)) = Real.log p := by
      rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
    simpa only [hΛ] using tendsto_normalizedRamanujan_harmonicGram_multiple hm ht

/-- A finite packet's harmonic quadratic mass is exactly its Gram expansion. -/
theorem sum_harmonic_packet_sq_eq_gram (S : Finset ℕ) (f : ℕ → ℝ)
    (u : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (∑ m ∈ S, f m * u m n) ^ 2 / (n : ℝ)) =
      ∑ m ∈ S, ∑ l ∈ S, f m * f l *
        (∑ n ∈ Icc 1 N, u m n * u l n / (n : ℝ)) := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ m ∈ S, ∑ l ∈ S,
        f m * f l * (u m n * u l n / (n : ℝ)) := by
      apply sum_congr rfl
      intro n _
      rw [pow_two, sum_mul, sum_div]
      apply sum_congr rfl
      intro m _
      rw [mul_sum, sum_div]
      apply sum_congr rfl
      intro l _
      ring
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      rw [sum_comm]
      simp only [mul_sum]

/-- Every finite conductor packet has the exact torsion-energy harmonic finite part. -/
theorem tendsto_ramanujanPacket_harmonic_torsion (S : Finset ℕ)
    (hS : ∀ m ∈ S, 0 < m) (f : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, (∑ m ∈ S, f m * ramanujanLagCoefficient m n) ^ 2 / (n : ℝ)) -
        (∑ m ∈ S, (m.totient : ℝ) * f m ^ 2) * Real.log N) atTop
      (𝓝 (Real.eulerMascheroniConstant * (∑ m ∈ S, (m.totient : ℝ) * f m ^ 2) -
        ∑ m ∈ S, ∑ l ∈ S, f m * f l * orbitIntersection m l)) := by
  have h := tendsto_finsetSum S fun m hm => tendsto_finsetSum S fun l hl =>
    (tendsto_ramanujan_harmonicGram_torsion (hS m hm) (hS l hl)).const_mul (f m * f l)
  have hr : (∑ m ∈ S, ∑ l ∈ S,
      f m * f l * (Real.eulerMascheroniConstant * (if m = l then (m.totient : ℝ) else 0) -
        orbitIntersection m l)) =
      Real.eulerMascheroniConstant * (∑ m ∈ S, (m.totient : ℝ) * f m ^ 2) -
        ∑ m ∈ S, ∑ l ∈ S, f m * f l * orbitIntersection m l := by
    simp only [mul_sub, sum_sub_distrib]
    congr 1
    convert conductor_diagonal_sum S f Real.eulerMascheroniConstant using 1
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro l _
    ring
  rw [hr] at h
  refine h.congr fun N => ?_
  simp only [mul_sub, sum_sub_distrib]
  rw [conductor_diagonal_sum, ← sum_harmonic_packet_sq_eq_gram]
  ring

private theorem orbitIntersection_nonneg {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    0 ≤ orbitIntersection m l := by
  by_cases hml : m = l
  · subst l
    rw [ArithmeticElectrostatics.orbitIntersection_self_eq hm,
      ArithmeticElectrostatics.localCorrection_eq_totient_mul_tameDifferent]
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left (tameDifferent_le_log hm) (Nat.cast_nonneg _))
  · exact ArithmeticElectrostatics.orbitIntersection_nonneg_of_ne hm hl hml

/-- Entrywise nonnegative intersections extend the torsion counterterm to the absolute signed pairing. -/
theorem abs_torsionPairing_le_two_log (Q : ℕ) (f : ℕ → ℝ) :
    |ArithmeticElectrostatics.torsionPairing Q f| ≤
      (2 * Real.log Q + (Real.log 4 + 4)) * ArithmeticElectrostatics.selfMass Q f := by
  have he : ArithmeticElectrostatics.selfMass Q (fun m => |f m|) =
      ArithmeticElectrostatics.selfMass Q f := by
    simp only [ArithmeticElectrostatics.selfMass, sq_abs]
  have h := ArithmeticElectrostatics.renormalizesAt_two_log Q (fun m => |f m|)
  rw [he] at h
  refine le_trans ?_ h
  unfold ArithmeticElectrostatics.torsionPairing
  calc
    _ ≤ ∑ m ∈ Icc 1 Q, |∑ l ∈ Icc 1 Q, f m * f l * orbitIntersection m l| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q, |f m * f l * orbitIntersection m l| :=
      sum_le_sum fun m _ => abs_sum_le_sum_abs _ _
    _ = _ := by
      apply sum_congr rfl
      intro m hm
      apply sum_congr rfl
      intro l hl
      rw [abs_mul, abs_mul, abs_of_nonneg
        (orbitIntersection_nonneg (mem_Icc.mp hm).1 (mem_Icc.mp hl).1)]

/-- The coarser absolute torsion bound. -/
theorem abs_torsionPairing_le_log (Q : ℕ) (f : ℕ → ℝ) :
    |ArithmeticElectrostatics.torsionPairing Q f| ≤
      (4 * Real.log Q + (Real.log 4 + 4)) * ArithmeticElectrostatics.selfMass Q f := by
  have hm : 0 ≤ ArithmeticElectrostatics.selfMass Q f :=
    sum_nonneg fun m _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  refine (abs_torsionPairing_le_two_log Q f).trans (mul_le_mul_of_nonneg_right ?_ hm)
  linarith only [Real.log_natCast_nonneg Q]

/-- The complete harmonic finite-part form has logarithmic operator size in conductor cutoff. -/
theorem abs_harmonicGram_finitePart_le_log (Q : ℕ) (f : ℕ → ℝ) :
    |Real.eulerMascheroniConstant * ArithmeticElectrostatics.selfMass Q f -
        ArithmeticElectrostatics.torsionPairing Q f| ≤
      (|Real.eulerMascheroniConstant| + 4 * Real.log Q + (Real.log 4 + 4)) *
        ArithmeticElectrostatics.selfMass Q f := by
  have hm : 0 ≤ ArithmeticElectrostatics.selfMass Q f :=
    sum_nonneg fun m _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  calc
    _ ≤ |Real.eulerMascheroniConstant * ArithmeticElectrostatics.selfMass Q f| +
        |ArithmeticElectrostatics.torsionPairing Q f| := abs_sub _ _
    _ ≤ |Real.eulerMascheroniConstant| * ArithmeticElectrostatics.selfMass Q f +
        (4 * Real.log Q + (Real.log 4 + 4)) * ArithmeticElectrostatics.selfMass Q f := by
      rw [abs_mul, abs_of_nonneg hm]
      exact add_le_add le_rfl (abs_torsionPairing_le_log Q f)
    _ = _ := by ring

#print axioms tendsto_ramanujan_harmonicGram_torsion
#print axioms tendsto_normalizedRamanujan_harmonicGram_torsion
#print axioms tendsto_normalizedRamanujan_harmonicGram_multiple
#print axioms tendsto_normalizedRamanujan_harmonicGram_primePower
#print axioms sum_harmonic_packet_sq_eq_gram
#print axioms tendsto_ramanujanPacket_harmonic_torsion
#print axioms abs_torsionPairing_le_log
#print axioms abs_harmonicGram_finitePart_le_log

end
end GaloisForLFunctions.SuccessorShellArithmetic
