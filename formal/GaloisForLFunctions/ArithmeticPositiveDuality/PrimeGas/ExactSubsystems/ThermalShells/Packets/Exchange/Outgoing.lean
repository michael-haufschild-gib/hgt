import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange.Temperature
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange.Wave

/-! # Isometry from the energy of two finite exchange sectors -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange

open Finset Real

private theorem sectorZ_pos {S : Finset Nat.Primes} (hs : S.Nontrivial) (i : Bool) (b : ℝ) :
    0 < sectorZ S i b := by
  obtain ⟨p,hp,q,hq,hne⟩ := hs
  apply sum_pos (fun _ _ => weight_pos _ _ _)
  exact ⟨pair p q,mem_levels.mpr ⟨p,hp,q,hq,Or.inr hne,pair_vector p q⟩⟩

private theorem energy_cross (S : Finset Nat.Primes) (b : ℝ) :
    (sectorZ S true b*sectorZ S false b)*(expectation S false b energy-expectation S true b energy) =
      singleZ S b*cross S b := by
  have z := partition_traces S b
  have t := additive_traces S b primeEnergy energy fun p q => energy_mul (quantum p) (quantum q)
  have zp : sectorZ S true b=(singleZ S b^2+singleZ S (2*b))/2 := by linarith only [z.1,z.2]
  have zm : sectorZ S false b=(singleZ S b^2-singleZ S (2*b))/2 := by linarith only [z.1,z.2]
  have tp : tested S true b energy = firstMoment S b primeEnergy*singleZ S b+firstMoment S (2*b) primeEnergy := by
    linarith only [t.1,t.2]
  have tm : tested S false b energy = firstMoment S b primeEnergy*singleZ S b-firstMoment S (2*b) primeEnergy := by
    linarith only [t.1,t.2]
  calc _ = sectorZ S true b * tested S false b energy - sectorZ S false b * tested S true b energy := by
             rw [← weighted_expectation S false b energy,← weighted_expectation S true b energy]
             ring
       _ = _ := by rw [zp,zm,tp,tm,cross]; ring

theorem energy_sign {S : Finset Nat.Primes} (hs : S.Nontrivial) {b : ℝ} (hb : b≠0) :
    0 < b*(expectation S false b energy-expectation S true b energy) := by
  have pos := mul_pos (singleZ_pos hs.nonempty b) (strict_cross hs hb)
  have eqv : singleZ S b*(b*cross S b) = (sectorZ S true b*sectorZ S false b)*
      (b*(expectation S false b energy-expectation S true b energy)) := by
    rw [mul_left_comm,← energy_cross]; ring
  rw [eqv] at pos
  exact (mul_pos_iff_of_pos_left (mul_pos (sectorZ_pos hs true b) (sectorZ_pos hs false b))).mp pos

theorem energy_equal_iff {S : Finset Nat.Primes} (hs : S.Nontrivial) (b : ℝ) :
    expectation S false b energy = expectation S true b energy ↔ b=0 := by
  constructor
  · intro h
    by_contra hb
    have hx := energy_sign hs hb
    rw [h,sub_self,mul_zero] at hx
    exact lt_irrefl _ hx
  · rintro rfl
    have h := energy_cross S 0
    simp only [cross,mul_zero,sub_self] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left
      (mul_ne_zero (sectorZ_pos hs true 0).ne' (sectorZ_pos hs false 0).ne'))

/-- Conditional mean total energy in the full outgoing pair basis. -/
def outgoingMean (S : Finset Nat.Primes) (squares : Bool) (s : ℂ) :=
  outputTest (levels S squares) s energy / outputTest (levels S squares) s (fun _ => 1)

theorem outgoing_eq (S : Finset Nat.Primes) (i : Bool) (s : ℂ) :
    outgoingMean S i s = expectation S i (2*s.re-1) energy := by
  have en (n : ℕ+) : 0 ≤ energy n := log_nonneg (by exact_mod_cast Nat.succ_le_of_lt n.pos)
  have numerator := (hasSum_output (levels S i) s energy (fun n _ => en n)).tsum_eq
  have denom := (hasSum_output (levels S i) s (fun _ => 1) (fun _ _ => zero_le_one)).tsum_eq
  rw [outgoingMean,outputTest,outputTest,numerator,denom]
  simp only [mul_one,expectation,tested,sectorZ,reading,shellMass,weight,neg_sub]

/-- The direction of the energy difference distinguishes the two sides of the critical line. -/
theorem outgoing_energy_sign {S : Finset Nat.Primes} (hs : S.Nontrivial) (s : ℂ) (h : s.re≠1/2) :
    0 < (2*s.re-1)*(outgoingMean S false s-outgoingMean S true s) := by
  rw [outgoing_eq,outgoing_eq]
  exact energy_sign hs (fun hz => h (by linarith only [hz]))

/-- Equality of two finite outgoing energy means characterizes isometric splitting on the full gas. -/
theorem split_isometric_iff_equal_exchange_energy {S : Finset Nat.Primes} (hs : S.Nontrivial) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      outgoingMean S false s = outgoingMean S true s := by
  rw [split_isometric_iff,outgoing_eq,outgoing_eq,energy_equal_iff hs]
  constructor <;> intro h <;> linarith only [h]

private theorem distinct_levels {p q : Nat.Primes} (hne : p≠q) :
    levels {p,q} false = {pair p q} := by
  ext n
  rw [mem_levels,mem_singleton]
  constructor
  · rintro ⟨u,hu,v,hv,hd,he⟩
    have hdiff := hd.resolve_left Bool.false_ne_true
    have hl := label.symm.injective (he.trans (pair_vector u v).symm)
    simp only [mem_insert,mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (hdiff rfl).elim
    · exact hl
    · exact hl.trans (pair_comm _ _)
    · exact (hdiff rfl).elim
  · rintro rfl
    exact ⟨p,mem_insert_self _ _,q,mem_insert_of_mem (mem_singleton_self _),Or.inr hne,pair_vector p q⟩

/-- In a two-mode packet the distinct sector has only one possible total energy. -/
theorem squarefree_pair_reading {p q : Nat.Primes} (hne : p≠q) (s : ℂ) :
    outgoingMean {p,q} false s = energy (pair p q) := by
  rw [outgoing_eq,expectation,tested,sectorZ]
  simp only [reading,distinct_levels hne,sum_singleton]
  exact mul_div_cancel_left₀ _ (weight_pos _ _ _).ne'

def twoThree : Finset Nat.Primes := {⟨2,Nat.prime_two⟩,⟨3,Nat.prime_three⟩}

/-- The products 4,6,9 and the squarefree product 6 suffice at every complex parameter. -/
theorem critical_line_iff_exchange_two_three (s : ℂ) :
    s.re=1/2 ↔ outgoingMean twoThree false s = outgoingMean twoThree true s := by
  have h : twoThree.Nontrivial := by
    refine ⟨⟨2,Nat.prime_two⟩,?_,⟨3,Nat.prime_three⟩,?_,?_⟩
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_singleton_self _)
    · intro eqv
      have n : (2:ℕ)=3 := congrArg Subtype.val eqv
      omega
  exact (split_isometric_iff s).symm.trans (split_isometric_iff_equal_exchange_energy h s)

/-- One finite mean, over the three integer labels 4, 6 and 9, detects the critical line. -/
theorem critical_line_iff_log_six (s : ℂ) :
    s.re=1/2 ↔ outgoingMean twoThree true s = log 6 := by
  let p : Nat.Primes := ⟨2,Nat.prime_two⟩
  let q : Nat.Primes := ⟨3,Nat.prime_three⟩
  have hn : p≠q := fun he => (by norm_num : (2:ℕ)≠3) (congrArg Subtype.val he)
  have e : energy (pair p q)=log 6 := by
    simp only [energy,pair,PNat.mul_coe,quantum,label_one_quantum]
    norm_num [p,q]
  rw [critical_line_iff_exchange_two_three,show outgoingMean twoThree false s = log 6 from
    (squarefree_pair_reading hn s).trans e,eq_comm]

#print axioms critical_line_iff_log_six
#print axioms outgoing_eq
#print axioms outgoing_energy_sign
#print axioms split_isometric_iff_equal_exchange_energy
#print axioms critical_line_iff_exchange_two_three

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange
