import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts.Crossing
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts.Vacuum

/-! # The complete critical-line response of the smallest crossing packet -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts

open Finset Real
open _root_.HTGeometry (finiteGibbsStateWeight)

/-- On adjacent shells the smaller extreme multiplicity controls the
arithmetic obstruction. Middle multiplicities can exceed the prime. -/
theorem rare_edge_transcendental (p : Nat.Primes) (h j m : ℕ) (hp : 0<h) (hm : 0 < m)
    (cop : ¬p.val ∣ h) {t : ℝ} (ht : 0<t) (zero : reading p h j (h+m) t=0) :
    Transcendental ℚ t := by
  let a := occupations h j (h+m)
  let n := h+j+(h+m)
  letI : Nonempty (States h j (h+m)) := ⟨Sum.inl ⟨0,hp⟩⟩
  have mult : Sparse.multiplicity a 0=h := by
    have sum : (∑ i, if a i=0 then (1 : ℕ) else 0)=h := by
      simp only [Fintype.sum_sum_type,a,occupations,Sum.elim_inl,Sum.elim_inr]
      simp
    simpa only [Sparse.multiplicity,sum_boole,Nat.cast_id] using sum
  have size : Fintype.card (States h j (h+m))=n := by
    simp only [States,Fintype.card_sum,Fintype.card_fin,n,Nat.add_assoc]
  have mass : (∑ i, a i)=n+m := by
    simp only [a,occupations,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,n]
    omega
  have edge (i) : Fintype.card (States h j (h+m))*a i<2*∑ k, a k := by
    rw [size,mass]
    have cap : a i≤2 := by rcases i with i | (i | i) <;> simp [a,occupations]
    exact (Nat.mul_le_mul_left n cap).trans_lt (by omega)
  exact vacuum_transcendental p a (by rwa [mult]) edge (by rwa [mult]) ht ((agrees_odd _ _).mpr zero)

/-- Exactly one positive damping fools the smallest crossing packet, and that
damping is transcendental for every prime. -/
theorem nine_positive_tie (p : Nat.Primes) :
    ∃ τ : ℝ, 0<τ ∧ Transcendental ℚ τ ∧ ∀ t : ℝ, 0<t → (reading p 1 6 2 t=0 ↔ t=τ) := by
  obtain ⟨z,⟨hz,zero⟩,uniq⟩ := unique_tie_of_crosses p 1 6 1 (nine_state_witness p)
  have tr := rare_edge_transcendental p 1 6 1 zero_lt_one zero_lt_one p.property.not_dvd_one hz zero
  exact ⟨z,hz,tr,fun t ht => ⟨fun h => uniq t ⟨ht,h⟩,fun eq => eq ▸ zero⟩⟩

/-- The normalized nine-state law ties exactly on the norm-preserving line
and on two parallel lines at one transcendental damping magnitude. -/
theorem nine_split_law (p : Nat.Primes) :
    ∃ τ : ℝ, 0<τ ∧ Transcendental ℚ τ ∧ ∀ s : ℂ,
      let E := primeModes p (occupations 1 6 2)
      lawOrder (finiteGibbsStateWeight (2*s.re-1) E) 1 ↔
        (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) ∨ |2*s.re-1|=τ := by
  obtain ⟨z,hz,tr,test⟩ := nine_positive_tie p
  refine ⟨z,hz,tr,fun s => ?_⟩
  let E := primeModes p (occupations 1 6 2)
  let d := 2*s.re-1
  dsimp only
  rw [gibbs_order,one_mul,split_isometric_iff]
  change agrees E d ↔ s.re=1/2 ∨ |d|=z
  have line : s.re=1/2 ↔ d=0 := by dsimp only [d]; constructor <;> intro h <;> linarith only [h]
  rw [line,← agrees_abs]
  by_cases flat : d=0
  · simp only [flat,abs_zero,agrees,neg_zero,iff_self,true_or]
  · have hit := test |d| (abs_pos.mpr flat)
    simp only [flat,false_or,agrees_odd]
    exact hit

#print axioms rare_edge_transcendental
#print axioms nine_positive_tie
#print axioms nine_split_law

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts
