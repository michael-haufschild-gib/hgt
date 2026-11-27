import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Schedule.Realization
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Packets

/-! # Open thermal sign patterns realized by elementary primes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Schedule

open Finset Real Set

variable {n q : ℕ}

def reading (S : Finset Nat.Primes) (t : ℝ) :=
  oddTrace (centered (labelEnergy (elementary (S := S)))) t

theorem reading_zero (S : Finset Nat.Primes) (t : ℝ) :
    reading S t=0 ↔ Coincides (elementary (S := S)) t := by
  rw [reading,oddTrace_eq,sub_eq_zero]
  exact eq_comm

private theorem schedule_open (t b : Fin q → ℝ) :
    IsOpen {E : Fin n → ℝ | ∀ j, 0<b j*oddTrace (centered E) (t j)} := by
  have cont (j : Fin q) : Continuous (fun E : Fin n → ℝ => b j*oddTrace (centered E) (t j)) := by
    unfold oddTrace oddTerm centered meanEnergy
    fun_prop
  have ranges : {E : Fin n → ℝ | ∀ j, 0<b j*oddTrace (centered E) (t j)} =
      ⋂ j : Fin q, {E : Fin n → ℝ | 0 < b j*oddTrace (centered E) (t j)} := by
    ext E; simp only [mem_setOf_eq,mem_iInter]
  rw [ranges]
  exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (cont j)

private theorem packet_reading (p : Fin n ↪ Nat.Primes) (t : ℝ) :
    reading (univ.map p) t=oddTrace (centered (fun i => log ((p i).val : ℝ))) t := by
  let S := univ.map p
  have eq : Set.range p=(↑S : Set Nat.Primes) := by simp [S]
  let e : Fin n ≃ S := p.toEquivRange.trans (Equiv.setCongr eq)
  have pair : Matches (fun i => log ((p i).val : ℝ)) (labelEnergy (elementary (S := S))) :=
    ⟨e,fun _ => rfl⟩
  have c := Observation.centered_matches pair
  unfold reading
  rw [oddTrace_eq,oddTrace_eq,partition_congr c,partition_congr c]

/-- Simultaneous signed measurements at arbitrarily prescribed relative temperatures.
Every sign survives affine approximation by a single packet of distinct primes. -/
theorem signs_on_primes (dim : 2*q+1≤n) (t : Fin q ↪o Ioi (0 : ℝ)) (b : Fin q → ℝ)
    (nonzero : ∀ i, b i≠0) (M : ℕ) (A : ℝ) :
    ∃ (S : Finset Nat.Primes) (K : ℝ), S.card=n ∧ (∀ p ∈ S, M<p.val) ∧ 0<K ∧ A<K ∧
      ∀ j, 0<b j*reading S ((t j).val/K) := by
  obtain ⟨E,zero,pattern⟩ := signs_on_real_spectrum dim t b nonzero
  have openSet := schedule_open (n := n) (fun j => (t j).val) b
  have belongs : ∀ j, 0<b j*oddTrace (centered E) (t j).val := by rwa [centered_eq_of_sum_zero zero]
  obtain ⟨p,K,c,pos,large,above,signs⟩ := prime_dense (by omega : 0<n) openSet ⟨E,belongs⟩ M A
  refine ⟨univ.map p,K,by rw [card_map,card_univ,Fintype.card_fin],?_,pos,large,fun j => ?_⟩
  · intro z hz; obtain ⟨i,_,rfl⟩ := mem_map.mp hz; exact above i
  · rw [packet_reading,← affine_trace (fun i => log ((p i).val : ℝ)) K c (t j).val]
    exact signs j

#print axioms signs_on_primes

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Schedule
