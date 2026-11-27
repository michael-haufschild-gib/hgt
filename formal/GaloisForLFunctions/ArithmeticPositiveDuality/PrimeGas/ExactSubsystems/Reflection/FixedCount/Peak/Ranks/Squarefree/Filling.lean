import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Squarefree.Exchange
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Ordered

/-! # Adjacent gaps at the two filling boundaries of a squarefree sector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Squarefree

open Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {r : ℕ}

private def initialModesEmbedding (a : Fin r ≃ I) (k : ℕ) (h : k+1 < r) : Fin (k+1) ↪ I where
  toFun j := a ⟨j.val,by omega⟩
  inj' _ _ he := Fin.ext (congrArg (Fin.val (n := r)) (a.injective he))

private def initialModes (a : Fin r ≃ I) (k : ℕ) (h : k+1 < r) := univ.map (initialModesEmbedding a k h)

omit [Fintype I] [DecidableEq I] in
private theorem mem_initialModes (a : Fin r ≃ I) (k : ℕ) (h : k+1 < r) (i : I) :
    i ∈ initialModes a k h ↔ (a.symm i).val ≤ k := by
  constructor
  · rintro hi
    obtain ⟨j,_,hj⟩ := mem_map.mp hi
    subst i
    change (a.symm (a ⟨j.val,_⟩)).val ≤ k
    rw [a.symm_apply_apply]
    exact Nat.le_of_lt_succ j.isLt
  · intro hi
    exact mem_map.mpr ⟨⟨(a.symm i).val,by omega⟩,mem_univ _,a.apply_symm_apply i⟩

/-- For a strictly increasing enumeration, the first excitation crosses its filling boundary. -/
theorem ordered_exchange (e : I → ℝ) (a : Fin r ≃ I) (inc : StrictMono (fun i => e (a i)))
    (k : ℕ) (h : k+1 < r) : ∃ u v : Sector I (k+1), FirstTwo (cost e) u v ∧
      cost e v-cost e u = e (a ⟨k+1,h⟩)-e (a ⟨k,by omega⟩) := by
  let p : Fin r := ⟨k,by omega⟩
  let q : Fin r := ⟨k+1,h⟩
  apply first_exchange e (initialModes a k h) (by simp [initialModes]) (a p) (a q)
  · rw [mem_initialModes,a.symm_apply_apply]
  · rw [mem_initialModes,a.symm_apply_apply]
    exact Nat.not_succ_le_self k
  · exact inc (Nat.lt_succ_self k : p < q)
  · intro i hi
    rw [mem_initialModes] at hi
    simpa only [a.apply_symm_apply] using inc.monotone (show a.symm i ≤ p from hi)
  · intro i hi
    rw [mem_initialModes] at hi
    simpa only [a.apply_symm_apply] using inc.monotone (show q ≤ a.symm i from Nat.lt_of_not_ge hi)

private theorem increasing_energy (S : Finset Nat.Primes) :
    StrictMono (fun i => primeEnergy (enumeration S i)) :=
  fun i j h => energy_inc (hi := i.isLt) (hj := j.isLt) h

private def descending (S : Finset Nat.Primes) : Fin S.card ≃ S :=
  Fin.revOrderIso.toEquiv.trans (enumeration S)

private theorem decreasing_energy (S : Finset Nat.Primes) :
    StrictMono (fun i => -primeEnergy (descending S i)) := by
  intro i j h
  apply neg_lt_neg
  exact (increasing_energy S) (Fin.rev_strictAnti h)

variable (S : Finset Nat.Primes) (k : ℕ) (h : k+1 < S.card)

/-- The two low gaps are read from opposite sides of the prime list when the sign changes. -/
theorem filling_gaps :
    ∃ l q u v : Sector S (k+1),
      FirstTwo (cost primeEnergy) l q ∧ FirstTwo (fun x => -cost primeEnergy x) u v ∧
      cost primeEnergy q-cost primeEnergy l = gap S k h ∧
      cost primeEnergy u-cost primeEnergy v = gap S (S.card-k-2) (by omega) := by
  obtain ⟨l,q,low,dl⟩ := ordered_exchange primeEnergy (enumeration S) (increasing_energy S) k h
  obtain ⟨u,v,high,du⟩ := ordered_exchange (fun i : S => -primeEnergy i) (descending S) (decreasing_energy S) k h
  have negcost : (cost (fun i : S => -primeEnergy i) : Sector S (k+1) → ℝ) = fun x => -cost primeEnergy x := by
    funext x
    simp only [cost,sum_neg_distrib]
  rw [negcost] at high du
  refine ⟨l,q,u,v,low,high,dl,?_⟩
  have a : descending S ⟨k,by omega⟩ = mode S (S.card-k-2+1) (by omega) := by
    apply congrArg (enumeration S)
    apply Fin.ext
    change S.card-(k+1) = S.card-k-2+1
    omega
  have b : descending S ⟨k+1,h⟩ = mode S (S.card-k-2) (by omega) := by
    apply congrArg (enumeration S)
    apply Fin.ext
    change S.card-(k+1+1) = S.card-k-2
    omega
  rw [a,b] at du
  unfold gap
  linarith only [du]

#print axioms ordered_exchange
#print axioms filling_gaps

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Squarefree
