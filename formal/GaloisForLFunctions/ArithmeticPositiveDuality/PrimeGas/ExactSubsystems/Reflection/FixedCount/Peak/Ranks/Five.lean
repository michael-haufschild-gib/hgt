import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Resolution
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Thermometry
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Crossing

/-! # The first five primes have a reflected peak match away from isometry -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Five

open Finset Real Filter Topology
open scoped ComplexConjugate

private def primes : Fin 5 → ℕ := ![2, 3, 5, 7, 11]

private theorem prime_entry (i : Fin 5) : (primes i).Prime := by
  fin_cases i <;> first | exact Nat.prime_two | exact Nat.prime_three | exact Nat.prime_five
                        | exact Nat.prime_seven | exact Nat.prime_eleven

private theorem increasing : StrictMono primes := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i <;> first | exact (show 2 < 3 by omega) | exact (show 3 < 5 by omega)
                        | exact (show 5 < 7 by omega) | exact (show 7 < 11 by omega)

private def atom (i : Fin 5) : Nat.Primes := ⟨primes i, prime_entry i⟩

/-- The packet of modes with labels 2, 3, 5, 7 and 11. -/
def packet : Finset Nat.Primes := univ.image atom

private def listed (i : Fin 5) : packet := ⟨atom i, mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩

private def listing : Fin 5 ≃ packet := Equiv.ofBijective listed ⟨
  fun _ _ h => increasing.injective (congrArg (fun i : packet => i.val.val) h),
  fun x => by
    obtain ⟨i,_,hi⟩ := mem_image.mp x.property
    exact ⟨i,Subtype.ext hi⟩⟩

theorem card_packet : packet.card = 5 := by
  simpa only [Fintype.card_coe,Fintype.card_fin] using (Fintype.card_congr listing).symm

private theorem energy_increases : StrictMono (fun i => primeEnergy (listed i)) :=
  fun i _ h => log_lt_log (Nat.cast_pos.mpr (prime_entry i).pos) (Nat.cast_lt.mpr (increasing h))

private theorem uniform_mean :
    0 < ∑ x : packet, ((primeEnergy x-primeEnergy (listed 4))+(primeEnergy x-primeEnergy (listed 0))) := by
  have h := log_lt_log (show 0 < ((2:ℝ)*11)^3 by positivity)
    (show ((2:ℝ)*11)^3 < (3*5*7)^2 by norm_num)
  rw [log_pow,log_pow,log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (11:ℝ) ≠ 0),
    log_mul (by norm_num : (3:ℝ)*5 ≠ 0) (by norm_num : (7:ℝ) ≠ 0),
    log_mul (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0)] at h
  rw [← Equiv.sum_comp listing]
  let slack (x : ℝ) := (log x-log 11)+(log x-log 2)
  change 0 < ∑ i : Fin 5, slack (primes i)
  simp only [Fin.sum_univ_succ, Finset.sum_empty, Finset.univ_eq_empty, add_zero]
  change 0 < slack 2 + (slack 3 + (slack 5 + (slack 7 + slack 11)))
  dsimp only [slack]
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h]

private theorem edge_order : primeEnergy (listed 1)-primeEnergy (listed 0) <
    primeEnergy (listed 4)-primeEnergy (listed 3) := by
  have h := log_lt_log (show 0 < (3:ℝ)*7 by positivity) (show (3:ℝ)*7 < 2*11 by norm_num)
  rw [log_mul (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (7:ℝ) ≠ 0),
    log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (11:ℝ) ≠ 0)] at h
  change log 3-log 2 < log 11-log 7
  linarith only [h]

private theorem eventual_order (n : ℕ) : ∀ᶠ t : ℝ in atTop,
    largest (read primeEnergy : Boson packet (n+1) → ℝ) t <
      largest (read primeEnergy : Boson packet (n+1) → ℝ) (-t) := by
  have low := boson_leakage n primeEnergy (listed 0) (listed 1)
    (energy_increases (show (0:Fin 5) < 1 by omega)) (by
      intro x hl hq
      obtain ⟨k,rfl⟩ := listing.surjective x
      have h₀ : k.val ≠ 0 := fun he => hl (congrArg listed (Fin.ext he))
      have h₁ : k.val ≠ 1 := fun he => hq (congrArg listed (Fin.ext he))
      exact energy_increases (show (1:Fin 5) < k by change 1 < k.val; omega))
  have high := boson_leakage n (fun i : packet => -primeEnergy i) (listed 4) (listed 3)
    (neg_lt_neg (energy_increases (show (3:Fin 5) < 4 by omega))) (by
      intro x hu hr
      obtain ⟨k,rfl⟩ := listing.surjective x
      have h₄ : k.val ≠ 4 := fun he => hu (congrArg listed (Fin.ext he))
      have h₃ : k.val ≠ 3 := fun he => hr (congrArg listed (Fin.ext he))
      exact neg_lt_neg (energy_increases (show k < (3:Fin 5) by change k.val < 3; omega)))
  rw [read_neg_fun] at high
  apply eventually_peak_lt edge_order low
  simpa only [largest_neg_energy, show -primeEnergy (listed 3) - -primeEnergy (listed 4) =
    primeEnergy (listed 4)-primeEnergy (listed 3) by ring] using high

/-- At every positive particle count, the first five primes have a common reflected peak
strictly to the right of the critical line. Their two leading ranks still distinguish the sides. -/
theorem first_five_alias (n : ℕ) : ∃ s : ℂ, 1/2 < s.re ∧
    measured packet (n+1) s = measured packet (n+1) (1-conj s) ∧
    measuredOdds packet (fun _ => n+1) (n+1) s ≠ measuredOdds packet (fun _ => n+1) (n+1) (1-conj s) := by
  have hl (i : packet) : primeEnergy (listed 0) ≤ primeEnergy i := by
    obtain ⟨k,rfl⟩ := listing.surjective i
    exact energy_increases.monotone (Fin.zero_le k)
  have hu (i : packet) : primeEnergy i ≤ primeEnergy (listed 4) := by
    obtain ⟨k,rfl⟩ := listing.surjective i
    exact energy_increases.monotone (Fin.le_last k)
  obtain ⟨t,ht,he⟩ := peak_crossing (read primeEnergy) (pure (n+1) (listed 0)) (pure (n+1) (listed 4))
    (fun x => by rw [read_pure,← read_const x]; exact read_mono x hl)
    (fun x => by rw [read_pure,← read_const x]; exact read_mono x hu)
    (boson_mean_positive (Nat.zero_lt_succ n) primeEnergy _ _ uniform_mean) (eventual_order n)
  let s : ℂ := ((1+t)/2 : ℝ)
  have temp : 2*s.re-1 = t := by change 2*((1+t)/2)-1=t; ring
  have flip : 2*(1-conj s).re-1 = -t := by rw [Complex.sub_re,Complex.one_re,Complex.conj_re,← temp]; ring
  have hr : 1/2 < s.re := by linarith only [temp,ht]
  refine ⟨s,hr,?_,?_⟩
  · rwa [measured_eq,measured_eq,temp,flip]
  · intro h
    have hiso := (ranked_match_iff_isometry packet (by rw [card_packet]; omega) n s).mp h
    exact hr.ne' ((split_isometric_iff s).mp hiso)

#print axioms card_packet
#print axioms first_five_alias

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Five
