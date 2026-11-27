import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Shape
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Density
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Radicals.Temperature

/-! # The minimum number of elementary primes with an irrational thermal crossing -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing

open Finset Real Set
open _root_.HTGeometry (finiteGibbsPartition)

variable {I : Type*} [Fintype I]

private theorem centered_affine (E : I → ℝ) (K c : ℝ) :
    centered (fun i => E i/K-c) = fun i => centered E i/K := by
  funext i
  letI : Nonempty I := ⟨i⟩
  have hn : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [centered,meanEnergy,sum_sub_distrib,← sum_div,sum_const,card_univ,nsmul_eq_mul]
  field_simp
  ring

theorem affine_trace (E : I → ℝ) (K c b : ℝ) :
    oddTrace (centered (fun i => E i/K-c)) b=oddTrace (centered E) (b/K) := by
  rw [centered_affine]
  apply sum_congr rfl
  intro i _
  unfold oddTerm
  rw [show b*(centered E i/K)=(b/K)*centered E i by ring,
    show -b*(centered E i/K)=-(b/K)*centered E i by ring]

private def packet {n : ℕ} (p : Fin n ↪ Nat.Primes) := univ.map p

private theorem matches_packet {n : ℕ} (p : Fin n ↪ Nat.Primes) :
    Matches (fun i => log ((p i).val : ℝ)) (labelEnergy (elementary (S := packet p))) := by
  let f (i : Fin n) : packet p := ⟨p i,mem_map.mpr ⟨i,mem_univ _,rfl⟩⟩
  have bij : Function.Bijective f := by
    refine ⟨fun i j eq => p.injective (congrArg Subtype.val eq),?_⟩
    intro y
    obtain ⟨i,_,hi⟩ := mem_map.mp y.property
    exact ⟨i,Subtype.ext hi⟩
  exact ⟨Equiv.ofBijective f bij,fun _ => rfl⟩

/-- Every nonzero crossing of a packet with at least three distinct primes is irrational. -/
theorem irrational_of_crossing {S : Finset Nat.Primes} {t : ℝ} (hn : 2<S.card) (ht : t≠0)
    (eq : Coincides (elementary (S := S)) t) : Irrational t := by
  rintro ⟨q,rfl⟩
  rcases (rational_prime_packet S q).mp eq with rfl | small
  · exact ht (Rat.cast_zero)
  · omega

/-- For every size at least five, crossings occur arbitrarily close to zero using
only primes above an arbitrary cutoff. All spectra count prime labels separately. -/
theorem small_crossing (n M : ℕ) (hn : 5≤n) {ε : ℝ} (hε : 0<ε) :
    ∃ S : Finset Nat.Primes, S.card=n ∧ (∀ p ∈ S, M<p.val) ∧
      ∃ t ∈ Ioo (0 : ℝ) ε, Irrational t ∧ Coincides (elementary (S := S)) t := by
  obtain ⟨p,K,c,hK,large,above,hU⟩ := prime_dense (by omega : 0<n) crossing_open
    (crossing_nonempty n hn) M (2/ε)
  obtain ⟨b,hb,eq⟩ := crossing_between hU
  rw [affine_trace] at eq
  let t := b/K
  have ht : 0<t := div_pos (lt_trans zero_lt_one hb.1) hK
  have small : t<ε := (div_lt_iff₀ hK).mpr (hb.2.trans (by
    rw [mul_comm]; exact (div_lt_iff₀ hε).mp large))
  let S := packet p
  have size : S.card=n := by rw [show S=univ.map p from rfl,card_map,card_univ,Fintype.card_fin]
  have pair := Observation.centered_matches (matches_packet p)
  have hit : Coincides (elementary (S := S)) t := by
    rw [oddTrace_eq,sub_eq_zero] at eq
    unfold Coincides
    rw [← partition_congr pair,← partition_congr pair]
    exact eq.symm
  refine ⟨S,size,?_,t,⟨ht,small⟩,irrational_of_crossing (by omega) ht.ne' hit,hit⟩
  intro q hq
  obtain ⟨i,_,rfl⟩ := mem_map.mp hq
  exact above i

/-- Among packet sizes at least three, the exact existence threshold for any
positive crossing is five, even with prescribed prime and damping cutoffs. -/
theorem crossing_iff (n M : ℕ) (hn : 3≤n) {ε : ℝ} (hε : 0<ε) :
    (∃ S : Finset Nat.Primes, S.card=n ∧ (∀ p ∈ S, M<p.val) ∧
      ∃ t ∈ Ioo (0 : ℝ) ε, Coincides (elementary (S := S)) t) ↔ 5≤n := by
  constructor
  · rintro ⟨S,hS,_,t,ht,eq⟩
    by_contra! small
    rcases (small_real_prime_packet S (by omega) t).mp eq with hz | low
    · exact ht.1.ne' hz
    · omega
  · intro size
    obtain ⟨S,hS,large,t,ht,_,eq⟩ := small_crossing n M size hε
    exact ⟨S,hS,large,t,ht,eq⟩

#print axioms affine_trace
#print axioms irrational_of_crossing
#print axioms small_crossing
#print axioms crossing_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing
