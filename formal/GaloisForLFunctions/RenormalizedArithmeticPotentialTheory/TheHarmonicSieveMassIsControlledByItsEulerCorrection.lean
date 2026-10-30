import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSieveGroundMassHasALogarithmicMoment
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFiniteSieveUnitGramHasTwoHorizons

/-!
# Uniform harmonic comparison for finite prime sieves

Positive supported/coprime factorization and the geometric ground moment bound
compare the actual harmonic weights with sieve density times logarithmic scale.
The constants depend on the Euler correction, without a primorial error term.
-/

noncomputable section
open Finset
open scoped Classical
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open HTGeometry

/-- Every positive integer has a supported factor and a factor coprime to the sieve. -/
theorem exists_sieveFactorization (Q : Finset Nat.Primes) {n : ℕ} (hn : 0 < n) :
    ∃ a : SieveClass Q, ∃ b : ℕ,
      0 < b ∧ b.Coprime (sievePrimorial Q) ∧ (a : ℕ) * b = n := by
  let e : Q → ℕ := fun p => n.factorization (p : Nat.Primes)
  let a : SieveClass Q := (sieveValuationEquiv Q).symm e
  have ha (p : Q) : (a : ℕ).factorization (p : Nat.Primes) =
      n.factorization (p : Nat.Primes) :=
    congrFun ((sieveValuationEquiv Q).apply_symm_apply e) p
  have hadvd : (a : ℕ) ∣ n := by
    apply (Nat.factorization_prime_le_iff_dvd a.property.pos.ne' hn.ne').mp
    intro p hp
    let pp : Nat.Primes := ⟨p, hp⟩
    by_cases hpQ : pp ∈ Q
    · exact (ha ⟨pp, hpQ⟩).le
    · calc
        (a : ℕ).factorization p = 0 := factorization_eq_zero_of_notMem_sieve a.property hpQ
        _ ≤ n.factorization p := Nat.zero_le _
  have hb : 0 < n / (a : ℕ) := Nat.div_pos (Nat.le_of_dvd hn hadvd) a.property.pos
  have hcop : (n / (a : ℕ)).Coprime (sievePrimorial Q) := by
    apply Nat.coprime_of_dvd
    intro p hp hpb hpr
    let pp : Nat.Primes := ⟨p, hp⟩
    have hr : SieveSupported Q (sievePrimorial Q) := ⟨1, by simp⟩
    have hpQ : pp ∈ Q := hr.prime_dvd_mem hpr
    have hz : (n / (a : ℕ)).factorization p = 0 := by
      calc
        _ = n.factorization p - (a : ℕ).factorization p := by
          rw [Nat.factorization_div hadvd, Finsupp.tsub_apply]
        _ = n.factorization p - n.factorization p :=
          congrArg (fun k => n.factorization p - k) (ha ⟨pp, hpQ⟩)
        _ = 0 := Nat.sub_self _
    rcases (Nat.factorization_eq_zero_iff _ _).mp hz with hnp | hnd | hzero
    · exact hnp hp
    · exact hnd hpb
    · exact hb.ne' hzero
  exact ⟨a, n / (a : ℕ), hb, hcop, Nat.mul_div_cancel' hadvd⟩

/-- Supported integer classes up to an actual integer horizon. -/
def sieveClassPrefix (Q : Finset Nat.Primes) (N : ℕ) : Finset (SieveClass Q) :=
  Finset.subtype (SieveSupported Q) (Icc 1 N)

theorem mem_sieveClassPrefix (Q : Finset Nat.Primes) (N : ℕ) (n : SieveClass Q) :
    n ∈ sieveClassPrefix Q N ↔ (n : ℕ) ≤ N := by
  rw [sieveClassPrefix, Finset.mem_subtype, mem_Icc]
  exact and_iff_right n.property.pos

/-- Harmonic mass is monotone in the actual integer cutoff. -/
theorem sievedHarmonic_mono (Q : Finset Nat.Primes) : Monotone (sievedHarmonic Q) := by
  intro M N hMN
  unfold sievedHarmonic
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rcases mem_filter.mp hn with ⟨hnI, hnQ⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hnI).1, (mem_Icc.mp hnI).2.trans hMN⟩, hnQ⟩
  · intro n _ _
    exact div_nonneg zero_le_one (Nat.cast_nonneg _)

/-- Positive supported/coprime factorization partitions the full harmonic mass exactly. -/
theorem harmonicSum_eq_sum_sieveClassMass (Q : Finset Nat.Primes) (N : ℕ) :
    harmonicSum N = ∑ a ∈ sieveClassPrefix Q N, sieveClassMass Q a N := by
  have hsplit :
      (∑ a ∈ sieveClassPrefix Q N, ∑ k ∈ sieveUnits Q (N / (a : ℕ)),
        (1 : ℝ) / (((a : ℕ) * k : ℕ) : ℝ)) = harmonicSum N := by
    rw [← Finset.sum_sigma (sieveClassPrefix Q N)
      (fun a : SieveClass Q => sieveUnits Q (N / (a : ℕ)))
      (fun t : Σ _ : SieveClass Q, ℕ => (1 : ℝ) / (((t.1 : ℕ) * t.2 : ℕ) : ℝ))]
    unfold harmonicSum
    apply Finset.sum_bij (fun (t : Σ _ : SieveClass Q, ℕ) _ => (t.1 : ℕ) * t.2)
    · intro t ht
      rcases Finset.mem_sigma.mp ht with ⟨_, hk⟩
      have hkI := (mem_filter.mp hk).1
      refine mem_Icc.mpr ⟨Nat.mul_pos t.1.property.pos (mem_Icc.mp hkI).1, ?_⟩
      simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le t.1.property.pos).mp (mem_Icc.mp hkI).2
    · intro x hx y hy hxy
      have hxQ := (mem_filter.mp (Finset.mem_sigma.mp hx).2).2
      have hyQ := (mem_filter.mp (Finset.mem_sigma.mp hy).2).2
      obtain ⟨ha, hb⟩ := sieveFactorization_unique x.1.property y.1.property hxQ hyQ hxy
      exact Sigma.ext (Subtype.ext ha) (heq_of_eq hb)
    · intro n hn
      obtain ⟨a, b, hb, hcop, hab⟩ := exists_sieveFactorization Q (mem_Icc.mp hn).1
      have haN : (a : ℕ) ≤ N :=
        (Nat.le_of_dvd (mem_Icc.mp hn).1 ⟨b, hab.symm⟩).trans (mem_Icc.mp hn).2
      have hbN : b ≤ N / (a : ℕ) := by
        apply (Nat.le_div_iff_mul_le a.property.pos).mpr
        rw [Nat.mul_comm b, hab]
        exact (mem_Icc.mp hn).2
      exact ⟨⟨a, b⟩, Finset.mem_sigma.mpr ⟨(mem_sieveClassPrefix Q N a).mpr haN,
        mem_filter.mpr ⟨mem_Icc.mpr ⟨hb, hbN⟩, hcop⟩⟩, hab⟩
    · intro t _
      rfl
  rw [← hsplit]
  apply sum_congr rfl
  intro a _
  rw [sieveClassMass, sievedHarmonic, sum_div]
  change (∑ k ∈ sieveUnits Q (N / (a : ℕ)), (1 : ℝ) / (((a : ℕ) * k : ℕ) : ℝ)) =
    ∑ k ∈ sieveUnits Q (N / (a : ℕ)), ((1 : ℝ) / k) / (a : ℕ)
  exact sum_congr rfl fun k _ => by simp only [Nat.cast_mul, div_div, mul_comm]

/-- The sieve density converts harmonic factorization into an average over a probability measure. -/
theorem sieveDensity_mul_harmonicSum_eq (Q : Finset Nat.Primes) (N : ℕ) :
    sieveDensity Q * harmonicSum N =
      ∑ a ∈ sieveClassPrefix Q N, sieveClassDensity Q a * sievedHarmonic Q (N / (a : ℕ)) := by
  rw [harmonicSum_eq_sum_sieveClassMass Q N, mul_sum]
  exact sum_congr rfl fun a _ => by unfold sieveClassMass sieveClassDensity; ring

theorem sum_sieveClassDensity_le_one {Q : Finset Nat.Primes} (S : Finset (SieveClass Q)) :
    (∑ n ∈ S, sieveClassDensity Q n) ≤ 1 := by
  have h := Summable.sum_le_tsum S (fun n _ => (sieveClassDensity_pos n.property).le)
    (hasSum_sieveClassDensity Q).summable
  rwa [(hasSum_sieveClassDensity Q).tsum_eq] at h

/-- Sifting harmonic measure never costs more than the full Euler-product density. -/
theorem sieveDensity_mul_harmonicSum_le (Q : Finset Nat.Primes) (N : ℕ) :
    sieveDensity Q * harmonicSum N ≤ sievedHarmonic Q N := by
  rw [sieveDensity_mul_harmonicSum_eq]
  calc
    _ ≤ ∑ a ∈ sieveClassPrefix Q N, sieveClassDensity Q a * sievedHarmonic Q N :=
      sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
        (sievedHarmonic_mono Q (Nat.div_le_self N (a : ℕ))) (sieveClassDensity_pos a.property).le
    _ = sievedHarmonic Q N * ∑ a ∈ sieveClassPrefix Q N, sieveClassDensity Q a := by
      rw [mul_sum]
      exact sum_congr rfl fun a _ => mul_comm _ _
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (sum_sieveClassDensity_le_one (sieveClassPrefix Q N)) (sievedHarmonic_nonneg Q N)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
