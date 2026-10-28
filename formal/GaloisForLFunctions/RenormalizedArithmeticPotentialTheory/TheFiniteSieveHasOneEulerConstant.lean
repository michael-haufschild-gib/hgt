import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion

/-!
# A finite prime sieve has one Euler constant

Removing finitely many primes changes the harmonic density multiplicatively and
the normalized finite part additively. The Euler--Mascheroni constant occurs once:
the remaining correction is the sum of the deleted local Euler factors.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.HTGeometry

/-- The Euler constant after removing a finite set of prime factors. -/
def sieveEuler (Q : Finset Nat.Primes) : ℝ :=
  Real.eulerMascheroniConstant +
    ∑ p ∈ Q, Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1)

@[simp] theorem sieveEuler_empty : sieveEuler ∅ = Real.eulerMascheroniConstant := by
  simp [sieveEuler]

theorem sieveEuler_insert {p : Nat.Primes} {Q : Finset Nat.Primes} (hp : p ∉ Q) :
    sieveEuler (insert p Q) =
      sieveEuler Q + Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1) := by
  rw [sieveEuler, sum_insert hp, sieveEuler]
  ring

/-- Deleting one more prime subtracts a decimated copy of the old harmonic sum. -/
theorem sievedHarmonic_insert {p : Nat.Primes} {Q : Finset Nat.Primes} (hp : p ∉ Q)
    (N : ℕ) :
    sievedHarmonic (insert p Q) N =
      sievedHarmonic Q N - sievedHarmonic Q (N / (p : ℕ)) / (p : ℕ) := by
  classical
  let f : ℕ → ℝ := fun n =>
    if Nat.Coprime n (sievePrimorial Q) then 1 / (n : ℝ) else 0
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 N)
    (fun n => (p : ℕ) ∣ n) f
  have hcop : Nat.Coprime (p : ℕ) (sievePrimorial Q) := coprime_sievePrimorial hp
  have hmult : ∑ n ∈ (Icc 1 N).filter (fun n => (p : ℕ) ∣ n), f n =
      sievedHarmonic Q (N / (p : ℕ)) / (p : ℕ) := by
    rw [multiples_Icc p.2.pos,
      sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left p.2.pos h,
      sievedHarmonic, sum_filter, div_eq_mul_inv, sum_mul]
    refine sum_congr rfl fun n _ => ?_
    change (if Nat.Coprime ((p : ℕ) * n) (sievePrimorial Q) then
      1 / (((p : ℕ) * n : ℕ) : ℝ) else 0) =
        (if Nat.Coprime n (sievePrimorial Q) then 1 / (n : ℝ) else 0) *
          (((p : ℕ) : ℝ))⁻¹
    by_cases hn : Nat.Coprime n (sievePrimorial Q)
    · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨hcop, hn⟩), if_pos hn, Nat.cast_mul]
      ring
    · rw [if_neg (fun h => hn (Nat.coprime_mul_iff_left.mp h).2), if_neg hn, zero_mul]
  have hfree : ∑ n ∈ (Icc 1 N).filter (fun n => ¬ (p : ℕ) ∣ n), f n =
      sievedHarmonic (insert p Q) N := by
    rw [sum_filter, sievedHarmonic, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    simp only [coprime_sievePrimorial_insert_iff hp, f]
    split_ifs <;> simp_all
  have hfull : ∑ n ∈ Icc 1 N, f n = sievedHarmonic Q N := by
    rw [sievedHarmonic, sum_filter]
  rw [hmult, hfree, hfull] at hsplit
  linarith only [hsplit]

/-- The finite prime sieve has harmonic constant `δ_Q (γ + Σ log p/(p−1))`. -/
theorem tendsto_sievedHarmonic_sub_sieveEuler (Q : Finset Nat.Primes) :
    Tendsto (fun N : ℕ => sievedHarmonic Q N - sieveDensity Q * Real.log N) atTop
      (𝓝 (sieveDensity Q * sieveEuler Q)) := by
  classical
  induction Q using Finset.induction with
  | empty =>
      simpa [sievedHarmonic, ← sum_Icc_one_div_eq_harmonic] using
        Real.tendsto_harmonic_sub_log
  | insert p Q hp ih =>
      have hdec := ih.comp (tendsto_natDiv_atTop p.2.pos)
      have hlog := (tendsto_log_natDiv_sub_log p.2.pos).const_mul (sieveDensity Q)
      have hlim := ih.sub ((hdec.add hlog).div_const ((p : ℕ) : ℝ))
      have hpR : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
      have hconstant : sieveDensity Q * sieveEuler Q -
          (sieveDensity Q * sieveEuler Q + sieveDensity Q * -Real.log (p : ℕ)) /
            (p : ℕ) = sieveDensity (insert p Q) * sieveEuler (insert p Q) := by
        rw [sieveDensity_insert hp, sieveEuler_insert hp]
        have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by linarith only [hpR]
        have hp1 : ((p : ℕ) : ℝ) - 1 ≠ 0 := by linarith only [hpR]
        field_simp
        ring
      rw [hconstant] at hlim
      refine hlim.congr fun N => ?_
      rw [sievedHarmonic_insert hp, sieveDensity_insert hp]
      dsimp only [Function.comp]
      ring

/-- The Möbius formula for the sieve constant equals the sum of its local shifts. -/
theorem sieveHarmonicConstant_eq_sieveEuler (Q : Finset Nat.Primes) :
    sieveHarmonicConstant Q = sieveDensity Q * sieveEuler Q :=
  tendsto_nhds_unique (tendsto_sievedHarmonic_sub Q)
    (tendsto_sievedHarmonic_sub_sieveEuler Q)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
