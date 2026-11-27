import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts.Cost

/-! # State budgets for binary observations on arbitrary finite three-shell Gibbs laws -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts

open Finset
open _root_.HTGeometry (finiteGibbsStateWeight)

/-- Binary reading of the normalized Gibbs law at signed damping t. -/
def bit {I : Type*} [Fintype I] (p : Nat.Primes) (a : I → ℕ) (t : ℝ) :=
  positiveBit (finiteGibbsStateWeight t (primeModes p a))

private theorem bit_iff {I : Type*} [Fintype I] (p : Nat.Primes) (a : I → ℕ) (t : ℝ) :
    bit p a t ↔ 0<oddTrace (centered (primeModes p a)) t := by
  let E := primeModes p a
  change 0<oddTrace (centered (Observation.information (finiteGibbsStateWeight t E))) 1 ↔ _
  rw [funext (Observation.gibbs_information E t),centered_affine]
  simp only [oddTrace,oddTerm,one_mul,neg_mul,E]

private theorem bit_congr {I J : Type*} [Fintype I] [Fintype J]
    (p : Nat.Primes) {a : I → ℕ} {b : J → ℕ} (m : Matches a b) (t : ℝ) :
    bit p a t ↔ bit p b t := by
  obtain ⟨e,h⟩ := m
  have energy : Matches (primeModes p a) (primeModes p b) := ⟨e,fun i => by simp only [primeModes,h i]⟩
  obtain ⟨f,eq⟩ := Observation.centered_matches energy
  have same := Fintype.sum_equiv f (fun i => oddTerm t (centered (primeModes p a) i))
    (fun i => oddTerm t (centered (primeModes p b) i)) (fun i => congrArg (oddTerm t) (eq i))
  simp only [bit_iff,oddTrace,same]

private theorem collect {I : Type*} [Fintype I] (a : I → ℕ) (cap : ∀ i, a i≤2) :
    ∃ l j r : ℕ, l+j+r=Fintype.card I ∧ Matches (occupations l j r) a := by
  classical
  let L := {i : I // a i=0}
  let H := {i : I // a i≠0}
  let J := {i : H // a i.val=1}
  let R := {i : H // a i.val≠1}
  let l := (Fintype.equivFin L).symm
  let j := (Fintype.equivFin J).symm
  let r := (Fintype.equivFin R).symm
  let e₁ := (Equiv.sumCongr j r).trans (Equiv.sumCompl (fun i : H => a i.val=1))
  let e := (Equiv.sumCongr l e₁).trans (Equiv.sumCompl (fun i : I => a i=0))
  refine ⟨_,_,_,?_,e,?_⟩
  · simpa only [Fintype.card_sum,Fintype.card_fin,Nat.add_assoc] using Fintype.card_congr e
  · rintro (i | (i | i))
    · exact (l i).property.symm
    · exact (j i).property.symm
    · change 2=a (r i).val.val
      have hi := cap (r i).val.val
      have first := (r i).val.property
      have second := (r i).property
      omega

/-- Any ordering of n physical states is allowed, including repeated labels
and missing levels. The integer criterion is exact for the normalized Gibbs bits. -/
theorem gibbs_budget_iff (p : Nat.Primes) {t u : ℝ} (ht : 0<t) (lt : t<u) (n : ℕ) :
    (∃ a : Fin n → ℕ, (∀ i, a i≤2) ∧ ¬(bit p a t ↔ bit p a u)) ↔
      admissibleCount p t u n := by
  rw [← feasible_iff p ht lt]
  constructor
  · rintro ⟨a,cap,sep⟩
    obtain ⟨l,j,r,count,m⟩ := collect a cap
    refine ⟨l,j,r,count.trans (Fintype.card_fin n),?_⟩
    have tbit := (bit_congr p m t).symm
    have ubit := (bit_congr p m u).symm
    rwa [tbit,ubit,bit_iff,bit_iff] at sep
  · rintro ⟨l,j,r,count,sep⟩
    have size : Fintype.card (States l j r)=n := by
      simpa only [States,Fintype.card_sum,Fintype.card_fin,Nat.add_assoc] using count
    let e := (Fintype.equivFinOfCardEq size).symm
    let b := occupations l j r
    have m : Matches (b ∘ e) b := ⟨e,fun _ => rfl⟩
    refine ⟨b ∘ e,fun i => ?_,?_⟩
    · change b (e i)≤2
      rcases e i with i | (i | i) <;> simp [b,occupations]
    · rwa [bit_congr p m t,bit_congr p m u,bit_iff,bit_iff]

#print axioms gibbs_budget_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts
