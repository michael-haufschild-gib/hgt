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
    _ ≤ _ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (sum_sieveClassDensity_le_one (sieveClassPrefix Q N)) (sievedHarmonic_nonneg Q N)

/-- The finite supported prefix and its conductor tail partition the geometric mass. -/
theorem sum_sieveClassDensity_prefix_add_tail (Q : Finset Nat.Primes) (T : ℕ) :
    (∑ a ∈ sieveClassPrefix Q T, sieveClassDensity Q a) +
      (∑' a : SieveClass Q, if (T : ℝ) < (a : ℕ) then sieveClassDensity Q a else 0) = 1 := by
  have h := (hasSum_sieveClassDensity Q).summable.sum_add_tsum_compl
    (s := sieveClassPrefix Q T)
  rw [_root_.tsum_subtype ((↑(sieveClassPrefix Q T) : Set (SieveClass Q))ᶜ)
    (fun a : SieveClass Q => sieveClassDensity Q (a : ℕ)),
    (hasSum_sieveClassDensity Q).tsum_eq] at h
  convert h using 1
  congr 1
  apply tsum_congr
  intro a
  simp only [Set.indicator_apply, Set.mem_compl_iff, Finset.mem_coe,
    mem_sieveClassPrefix, not_le, Nat.cast_lt]

/-- A logarithmic cutoff twice the Euler correction retains at least half the ground mass. -/
theorem half_le_sum_sieveClassDensity_prefix (Q : Finset Nat.Primes) {T : ℕ}
    (hT : 1 < T)
    (hlog : 2 * (sieveEuler Q - Real.eulerMascheroniConstant) ≤ Real.log T) :
    (1 : ℝ) / 2 ≤ ∑ a ∈ sieveClassPrefix Q T, sieveClassDensity Q a := by
  have hTR : (1 : ℝ) < T := by exact_mod_cast hT
  have htail := tsum_sieveClassDensity_above_le Q hTR
  have hquot : (sieveEuler Q - Real.eulerMascheroniConstant) / Real.log T ≤ 1 / 2 :=
    (div_le_iff₀ (Real.log_pos hTR)).mpr (by linarith only [hlog])
  linarith only [sum_sieveClassDensity_prefix_add_tail Q T, htail, hquot]

private theorem exists_halfMassCutoff (Q : Finset Nat.Primes) :
    ∃ T : ℕ, 1 < T ∧
      Real.log T ≤ 2 * (sieveEuler Q - Real.eulerMascheroniConstant) + 3 ∧
      (1 : ℝ) / 2 ≤ ∑ a ∈ sieveClassPrefix Q T, sieveClassDensity Q a := by
  let z : ℝ := 2 * (sieveEuler Q - Real.eulerMascheroniConstant) + 2
  let T : ℕ := ⌈Real.exp z⌉₊
  have hz : 0 < z := by
    dsimp [z]
    linarith only [sieveEuler_correction_nonneg Q]
  have hexp : 1 < Real.exp z := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hz
  have hceil : Real.exp z ≤ (T : ℝ) := Nat.le_ceil _
  have hTR : (1 : ℝ) < T := hexp.trans_le hceil
  have hT : 1 < T := by exact_mod_cast hTR
  have hlower : z ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos z) hceil
  have hceilUpper : (T : ℝ) < Real.exp z + 1 := Nat.ceil_lt_add_one (Real.exp_pos z).le
  have hdouble : (T : ℝ) ≤ 2 * Real.exp z := by linarith only [hceilUpper, hexp]
  have hlogTwo : Real.log 2 ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hupper : Real.log T ≤ z + 1 := by
    have h := Real.log_le_log (zero_lt_one.trans hTR) hdouble
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero z), Real.log_exp] at h
    linarith only [h, hlogTwo]
  refine ⟨T, hT, ?_, half_le_sum_sieveClassDensity_prefix Q hT ?_⟩
  · dsimp [z] at hupper
    linarith only [hupper]
  · dsimp [z] at hlower
    linarith only [hlower]

private theorem sievedHarmonic_le_twice_dilated (Q : Finset Nat.Primes)
    {T N : ℕ} (hN : 0 < N)
    (hmass : (1 : ℝ) / 2 ≤ ∑ a ∈ sieveClassPrefix Q T, sieveClassDensity Q a) :
    sievedHarmonic Q N ≤ 2 * sieveDensity Q * harmonicSum (T * N) := by
  have hTN : T ≤ T * N := by simpa using Nat.mul_le_mul_left T hN
  have hprefix : sieveClassPrefix Q T ⊆ sieveClassPrefix Q (T * N) := by
    intro a ha
    exact (mem_sieveClassPrefix Q (T * N) a).mpr ((mem_sieveClassPrefix Q T a).mp ha |>.trans hTN)
  have hsmall (a : SieveClass Q) (ha : a ∈ sieveClassPrefix Q T) :
      N ≤ T * N / (a : ℕ) := by
    apply (Nat.le_div_iff_mul_le a.property.pos).mpr
    calc
      N * (a : ℕ) = (a : ℕ) * N := Nat.mul_comm _ _
      _ ≤ T * N := Nat.mul_le_mul_right N ((mem_sieveClassPrefix Q T a).mp ha)
  have hmain : sievedHarmonic Q N / 2 ≤ sieveDensity Q * harmonicSum (T * N) := by
    calc
      _ ≤ (∑ a ∈ sieveClassPrefix Q T, sieveClassDensity Q a) * sievedHarmonic Q N := by
        simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using
          mul_le_mul_of_nonneg_right hmass (sievedHarmonic_nonneg Q N)
      _ = ∑ a ∈ sieveClassPrefix Q T, sieveClassDensity Q a * sievedHarmonic Q N := sum_mul _ _ _
      _ ≤ ∑ a ∈ sieveClassPrefix Q T,
          sieveClassDensity Q a * sievedHarmonic Q (T * N / (a : ℕ)) :=
        sum_le_sum fun a ha => mul_le_mul_of_nonneg_left
          (sievedHarmonic_mono Q (hsmall a ha)) (sieveClassDensity_pos a.property).le
      _ ≤ ∑ a ∈ sieveClassPrefix Q (T * N),
          sieveClassDensity Q a * sievedHarmonic Q (T * N / (a : ℕ)) :=
        sum_le_sum_of_subset_of_nonneg hprefix fun a _ _ =>
          mul_nonneg (sieveClassDensity_pos a.property).le (sievedHarmonic_nonneg Q _)
      _ = _ := (sieveDensity_mul_harmonicSum_eq Q (T * N)).symm
  linarith only [hmain]

/-- Uniform harmonic upper bound with the same sieve density as the lower bound. -/
theorem sievedHarmonic_le_density_log_euler (Q : Finset Nat.Primes) (N : ℕ) :
    sievedHarmonic Q N ≤ 2 * sieveDensity Q *
      (Real.log (N + 1 : ℕ) + 2 * (sieveEuler Q - Real.eulerMascheroniConstant) + 4) := by
  obtain ⟨T, hT, hlogT, hmass⟩ := exists_halfMassCutoff Q
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [sievedHarmonic, Icc_eq_empty_of_lt (by omega : 0 < 1), filter_empty,
      sum_empty, Nat.cast_one, Real.log_one, zero_add]
    exact mul_nonneg (mul_nonneg (by norm_num) (sieveDensity_pos Q).le)
      (by linarith only [sieveEuler_correction_nonneg Q])
  have hH : harmonicSum (T * N) ≤ 1 + Real.log (T * N : ℕ) := by
    have h := harmonic_le_one_add_log (T * N)
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
    simpa only [harmonicSum, one_div] using h
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hT).ne'
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Nat.cast_mul, Real.log_mul hT0 hN0] at hH
  have hlogN : Real.log (N : ℝ) ≤ Real.log (N + 1 : ℕ) :=
    Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast Nat.le_succ N)
  calc
    _ ≤ 2 * sieveDensity Q * harmonicSum (T * N) := sievedHarmonic_le_twice_dilated Q hN hmass
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hH, hlogT, hlogN])
      (mul_nonneg (by norm_num) (sieveDensity_pos Q).le)

/-- The harmonic mass of a supported class retains its full logarithmic interval. -/
theorem sieveClassDensity_mul_log_sub_le_mass {Q : Finset Nat.Primes}
    (a : SieveClass Q) (N : ℕ) :
    sieveClassDensity Q a * (Real.log (N + 1 : ℕ) - Real.log (a : ℕ)) ≤
      sieveClassMass Q a N := by
  have ha : (0 : ℝ) < (a : ℕ) := by exact_mod_cast a.property.pos
  have hquot : N + 1 ≤ (N / (a : ℕ) + 1) * (a : ℕ) := by
    have hdiv := Nat.div_add_mod N (a : ℕ)
    have hmod := Nat.mod_lt N a.property.pos
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (N / (a : ℕ))]
    omega
  have hlog : Real.log (N + 1 : ℕ) ≤
      Real.log (N / (a : ℕ) + 1 : ℕ) + Real.log (a : ℕ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (N + 1 : ℕ))
      (show ((N + 1 : ℕ) : ℝ) ≤ (((N / (a : ℕ) + 1) * (a : ℕ) : ℕ) : ℝ) by
        exact_mod_cast hquot)
    rwa [Nat.cast_mul, Real.log_mul (by positivity) ha.ne'] at h
  have hH : Real.log (N / (a : ℕ) + 1 : ℕ) ≤ harmonicSum (N / (a : ℕ)) := by
    have h := log_add_one_le_harmonic (N / (a : ℕ))
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
    simpa only [harmonicSum, one_div] using h
  calc
    _ = (sieveDensity Q * (Real.log (N + 1 : ℕ) - Real.log (a : ℕ))) / (a : ℕ) := by
      unfold sieveClassDensity
      ring
    _ ≤ (sieveDensity Q * harmonicSum (N / (a : ℕ))) / (a : ℕ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [hlog, hH]) (sieveDensity_pos Q).le) ha.le
    _ ≤ sievedHarmonic Q (N / (a : ℕ)) / (a : ℕ) :=
      div_le_div_of_nonneg_right (sieveDensity_mul_harmonicSum_le Q _) ha.le
    _ = _ := rfl

/-- The class upper weight depends only on logarithmic scale and the Euler correction. -/
theorem sieveClassMass_le_density_log_euler {Q : Finset Nat.Primes}
    (a : SieveClass Q) (N : ℕ) :
    sieveClassMass Q a N ≤ 2 * sieveClassDensity Q a *
      (Real.log (N + 1 : ℕ) + 2 * (sieveEuler Q - Real.eulerMascheroniConstant) + 4) := by
  have ha : (0 : ℝ) < (a : ℕ) := by exact_mod_cast a.property.pos
  have hlog : Real.log (N / (a : ℕ) + 1 : ℕ) ≤ Real.log (N + 1 : ℕ) :=
    Real.log_le_log (by positivity)
      (by exact_mod_cast Nat.add_le_add_right (Nat.div_le_self N (a : ℕ)) 1)
  calc
    _ ≤ (2 * sieveDensity Q *
        (Real.log (N / (a : ℕ) + 1 : ℕ) +
          2 * (sieveEuler Q - Real.eulerMascheroniConstant) + 4)) / (a : ℕ) :=
      div_le_div_of_nonneg_right (sievedHarmonic_le_density_log_euler Q _) ha.le
    _ ≤ (2 * sieveDensity Q *
        (Real.log (N + 1 : ℕ) + 2 * (sieveEuler Q - Real.eulerMascheroniConstant) + 4)) / (a : ℕ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [hlog])
          (mul_nonneg (by norm_num) (sieveDensity_pos Q).le)) ha.le
    _ = _ := by unfold sieveClassDensity; ring

/-- Below the square-root horizon, geometric and harmonic class weights have universal comparison constants. -/
theorem sieveClassMass_comparable_to_density_log {Q : Finset Nat.Primes}
    (a : SieveClass Q) {N : ℕ} (haN : (a : ℕ) ^ 2 ≤ N + 1)
    (hN : 2 * (sieveEuler Q - Real.eulerMascheroniConstant) + 4 ≤ Real.log (N + 1 : ℕ)) :
    (Real.log (N + 1 : ℕ) / 2) * sieveClassDensity Q a ≤ sieveClassMass Q a N ∧
      sieveClassMass Q a N ≤ 4 * Real.log (N + 1 : ℕ) * sieveClassDensity Q a := by
  have ha : (0 : ℝ) < (a : ℕ) := by exact_mod_cast a.property.pos
  have hlog : 2 * Real.log (a : ℕ) ≤ Real.log (N + 1 : ℕ) := by
    have h := Real.log_le_log (sq_pos_of_pos ha)
      (show ((a : ℕ) : ℝ) ^ 2 ≤ (N + 1 : ℕ) by exact_mod_cast haN)
    rw [pow_two, Real.log_mul ha.ne' ha.ne'] at h
    linarith only [h]
  constructor
  · calc
      _ ≤ sieveClassDensity Q a * (Real.log (N + 1 : ℕ) - Real.log (a : ℕ)) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (by linarith only [hlog]) (sieveClassDensity_pos a.property).le
      _ ≤ _ := sieveClassDensity_mul_log_sub_le_mass a N
  · calc
      _ ≤ 2 * sieveClassDensity Q a *
          (Real.log (N + 1 : ℕ) + 2 * (sieveEuler Q - Real.eulerMascheroniConstant) + 4) :=
        sieveClassMass_le_density_log_euler a N
      _ ≤ 2 * sieveClassDensity Q a * (2 * Real.log (N + 1 : ℕ)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hN])
          (mul_nonneg (by norm_num) (sieveClassDensity_pos a.property).le)
      _ = _ := by ring


end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.harmonicSum_eq_sum_sieveClassMass
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.sieveDensity_mul_harmonicSum_le
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.sievedHarmonic_le_density_log_euler
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.sieveClassDensity_mul_log_sub_le_mass
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.sieveClassMass_le_density_log_euler
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.sieveClassMass_comparable_to_density_log
