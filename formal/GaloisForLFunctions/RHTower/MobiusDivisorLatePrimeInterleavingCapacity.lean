import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeBlocks
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeCompensation
import GaloisForLFunctions.RHTower.MobiusDivisorPrimeFibreInterpolation

/-!
# Late-prime mass forces unbounded interleaving

A block of isolated late primes lowers the retained head by its entire positive
mass. The two endpoint energies bound that mass by the sum of their square
roots. Summing over any partition retains the full arithmetic late-prime mass.
Its superlinear growth excludes every fixed number of blocks under a fixed
multiple of the original diagonal, independently of internal prime order.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

/-- Late primes with a nonterminal source index. -/
def mobiusDivisorActiveLatePrimes (M : ℕ) : Finset ℕ :=
  (GaloisForLFunctions.HTGeometry.primesInIoc (M/2) M).erase M

/-- Active late primes satisfy the literal singleton-fibre isolation conditions. -/
theorem mem_mobiusDivisorActiveLatePrimes {M p : ℕ}
    (hp : p ∈ mobiusDivisorActiveLatePrimes M) : p.Prime ∧ p<M ∧ M≤2*p := by
  obtain ⟨hne,hp⟩ := mem_erase.mp hp
  obtain ⟨hprime,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  exact ⟨hprime,by omega,by omega⟩

private theorem unsigned_channel_self (M : ℕ) : divisorUnsignedDilationChannel M M=0 := by
  by_cases hM : M=0
  · simp [hM,divisorUnsignedDilationChannel,primeFreeDivisorDefect]
  · simp [divisorUnsignedDilationChannel,Icc_eq_empty_of_lt (by omega : M-1<M)]

/-- Removing the terminal zero channel retains the complete late-prime mass. -/
theorem sum_mobiusDivisorActiveLatePrimes (M : ℕ) :
    (∑ p ∈ mobiusDivisorActiveLatePrimes M,divisorUnsignedDilationChannel M p)=
      mobiusDivisorLatePrimeMass M := by
  unfold mobiusDivisorActiveLatePrimes mobiusDivisorLatePrimeMass
  apply sum_subset (erase_subset M _)
  intro p hp hn
  have he : p=M := by
    by_contra hne
    exact hn (mem_erase.mpr ⟨hne,hp⟩)
  subst p
  exact unsigned_channel_self M

/-- The magnitude of the retained head is bounded by the square root of complete retained energy. -/
theorem abs_mobiusDivisorSelectionHead_le_sqrt_energy (M : ℕ) (P : Finset ℕ) :
    |mobiusDivisorSelectionFibre M P ∅| ≤ Real.sqrt (mobiusDivisorSelectionEnergy M P) := by
  have h := sum_mobiusDivisorSelectionFibre_sq_le_energy M P {∅}
  simp only [sum_singleton] at h
  exact Real.abs_le_sqrt h

/-- Every isolated late block has capacity bounded by its two actual endpoint amplitudes. -/
theorem mobiusDivisorLateBlock_mass_le_endpoint_roots (M : ℕ) (P L : Finset ℕ)
    (hL : L ⊆ mobiusDivisorActiveLatePrimes M) (hfree : ∀ p ∈ L,p ∉ P) :
    (∑ p ∈ L,divisorUnsignedDilationChannel M p) ≤
      Real.sqrt (mobiusDivisorSelectionEnergy M P)+
        Real.sqrt (mobiusDivisorSelectionEnergy M (P ∪ L)) := by
  have hprime : ∀ p ∈ L,p.Prime ∧ p<M ∧ M≤2*p :=
    fun p hp => mem_mobiusDivisorActiveLatePrimes (hL hp)
  have hc : (∑ p ∈ L,mobiusDivisorDilationChannel M p) =
      -(∑ p ∈ L,divisorUnsignedDilationChannel M p) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro p hp
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
      ArithmeticFunction.moebius_apply_prime (hprime p hp).1]
    push_cast
    ring
  have he := mobiusDivisorSelectionHead_union_late_primes M P L hprime hfree
  rw [hc] at he
  have h0 := abs_mobiusDivisorSelectionHead_le_sqrt_energy M P
  have h1 := abs_mobiusDivisorSelectionHead_le_sqrt_energy M (P ∪ L)
  have ha := le_abs_self (mobiusDivisorSelectionFibre M P ∅)
  have hb := neg_le_abs (mobiusDivisorSelectionFibre M (P ∪ L) ∅)
  linarith only [he,h0,h1,ha,hb]

/-- A common endpoint energy ceiling bounds the entire positive mass of one late block. -/
theorem mobiusDivisorLateBlock_mass_le_of_energy_le (M : ℕ) (P L : Finset ℕ) (B : ℝ)
    (hL : L ⊆ mobiusDivisorActiveLatePrimes M) (hfree : ∀ p ∈ L,p ∉ P)
    (h0 : mobiusDivisorSelectionEnergy M P ≤ B)
    (h1 : mobiusDivisorSelectionEnergy M (P ∪ L) ≤ B) :
    (∑ p ∈ L,divisorUnsignedDilationChannel M p) ≤ 2*Real.sqrt B := by
  have h := mobiusDivisorLateBlock_mass_le_endpoint_roots M P L hL hfree
  have hs0 := Real.sqrt_le_sqrt h0
  have hs1 := Real.sqrt_le_sqrt h1
  linarith only [h,hs0,hs1]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Assigning each late prime to one block preserves its complete mass exactly once. -/
theorem sum_mobiusDivisorLatePrimePartition_mass (M : ℕ) (owner : ℕ → ι) :
    (∑ i : ι,∑ p ∈ (mobiusDivisorActiveLatePrimes M).filter (fun p => owner p=i),
      divisorUnsignedDilationChannel M p)=mobiusDivisorLatePrimeMass M := by
  simp_rw [sum_filter]
  rw [sum_comm]
  simp only [sum_ite_eq,mem_univ,if_true]
  exact sum_mobiusDivisorActiveLatePrimes M

/-- The full late-prime mass is charged to the actual endpoint amplitudes of every block partition. -/
theorem mobiusDivisorLatePrimeMass_le_partition_endpoints
    (M : ℕ) (owner : ℕ → ι) (P : ι → Finset ℕ)
    (hfree : ∀ i, ∀ p ∈ (mobiusDivisorActiveLatePrimes M).filter (fun p => owner p=i),p ∉ P i) :
    mobiusDivisorLatePrimeMass M ≤ ∑ i : ι,
      (Real.sqrt (mobiusDivisorSelectionEnergy M (P i))+
        Real.sqrt (mobiusDivisorSelectionEnergy M
          (P i ∪ (mobiusDivisorActiveLatePrimes M).filter (fun p => owner p=i)))) := by
  rw [← sum_mobiusDivisorLatePrimePartition_mass M owner]
  apply sum_le_sum
  intro i _
  exact mobiusDivisorLateBlock_mass_le_endpoint_roots M _ _ (filter_subset _ _) (hfree i)

/-- A fixed endpoint energy ceiling bounds the capacity of a partition by its number of blocks. -/
theorem mobiusDivisorLatePrimeMass_le_partition_capacity
    (M : ℕ) (owner : ℕ → ι) (P : ι → Finset ℕ) (B : ℝ)
    (hfree : ∀ i, ∀ p ∈ (mobiusDivisorActiveLatePrimes M).filter (fun p => owner p=i),p ∉ P i)
    (hbudget : ∀ i,mobiusDivisorSelectionEnergy M (P i) ≤ B ∧
      mobiusDivisorSelectionEnergy M
        (P i ∪ (mobiusDivisorActiveLatePrimes M).filter (fun p => owner p=i)) ≤ B) :
    mobiusDivisorLatePrimeMass M ≤ 2*(Fintype.card ι : ℝ)*Real.sqrt B := by
  rw [← sum_mobiusDivisorLatePrimePartition_mass M owner]
  calc
    _ ≤ ∑ i : ι,2*Real.sqrt B := sum_le_sum (fun i _ =>
      mobiusDivisorLateBlock_mass_le_of_energy_le M _ _ B (filter_subset _ _) (hfree i)
        (hbudget i).1 (hbudget i).2)
    _ = _ := by simp; ring

/-- Every fixed number of late-prime blocks eventually forces an endpoint above any fixed original-diagonal multiple. -/
theorem eventually_mobiusDivisorLatePrimePartition_exceeds_diagonal (K : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,∀ (owner : ℕ → Fin K) (P : Fin K → Finset ℕ),
      (∀ i, ∀ p ∈ (mobiusDivisorActiveLatePrimes (4*N)).filter (fun p => owner p=i),p ∉ P i) →
      ∃ i,C*mobiusDivisorSelectionEnergy (4*N) ∅ < mobiusDivisorSelectionEnergy (4*N) (P i) ∨
        C*mobiusDivisorSelectionEnergy (4*N) ∅ < mobiusDivisorSelectionEnergy (4*N)
          (P i ∪ (mobiusDivisorActiveLatePrimes (4*N)).filter (fun p => owner p=i)) := by
  have hT := tendsto_mobiusDivisorLatePrimeMass_div_atTop.eventually_gt_atTop
    (2*(K:ℝ)*Real.sqrt (722*|C|))
  filter_upwards [hT,eventually_ge_atTop (1:ℕ)] with N hT hN
  intro owner P hfree
  by_contra hbad
  push Not at hbad
  have hQ : 0 ≤ mobiusDivisorSelectionEnergy (4*N) ∅ := by
    rw [mobiusDivisorSelectionEnergy_empty]
    exact sum_nonneg (fun _ _ => sq_nonneg _)
  have hQbound : C*mobiusDivisorSelectionEnergy (4*N) ∅ ≤
      (722*|C|)*(4*N:ℕ)^(2 : ℕ) := by
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self C) hQ
    have h2 := mul_le_mul_of_nonneg_left (sum_mobiusDivisorDilationChannel_sq_le_quadratic (4*N))
      (abs_nonneg C)
    rw [← mobiusDivisorSelectionEnergy_empty] at h2
    nlinarith only [h1,h2]
  have hcap := mobiusDivisorLatePrimeMass_le_partition_capacity (4*N) owner P
    ((722*|C|)*(4*N:ℕ)^(2 : ℕ)) hfree (fun i =>
      ⟨(hbad i).1.trans hQbound,(hbad i).2.trans hQbound⟩)
  rw [Fintype.card_fin,Real.sqrt_mul (by positivity),Real.sqrt_sq_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (4*N))] at hcap
  have hpos : (0:ℝ)<4*N := by positivity
  have hlarge := (lt_div_iff₀ hpos).mp hT
  push_cast at hcap
  nlinarith only [hcap,hlarge]
end RHTower
