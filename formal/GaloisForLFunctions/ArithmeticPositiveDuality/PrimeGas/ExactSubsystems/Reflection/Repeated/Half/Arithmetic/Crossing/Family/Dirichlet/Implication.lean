import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.BlindSets

/-! # When one thermal reflection test forces another -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Set

def kernel (t : ℝ) : Ideal PolynomialRing := RingHom.ker (value t).toRingHom

/-- Every physical finite spectrum passing t also passes u. -/
def Forces (t u : ℝ) := ∀ n (a : Fin n → ℕ+), agrees (energy ∘ a) t → agrees (energy ∘ a) u

private theorem failed_inclusion {t u : ℝ} (h : ¬kernel t ≤ kernel u) :
    ∃ P : PolynomialRing, value t P=0 ∧ value u P ≠ 0 := by
  contrapose! h
  exact fun P hP => h P hP

/-- Positive orders are universally linked precisely by specialization of the
prime coordinates at one of the two signs of the target order. -/
theorem forces_iff {t u : ℝ} (ht : 0<t) (hu : 0<u) :
    Forces t u ↔ kernel t ≤ kernel u ∨ kernel t ≤ kernel (-u) := by
  constructor
  · intro force
    by_contra! missing
    obtain ⟨P,pt,pu⟩ := failed_inclusion missing.1
    obtain ⟨Q,qt,qu⟩ := failed_inclusion missing.2
    let R := P^2+Q^2
    have root (s : ℝ) : value s R=0 ↔ value s P=0 ∧ value s Q=0 := squares_root P Q s
    have hn : R ≠ 0 := fun z => pu ((root u).mp (by rw [z,map_zero])).1
    obtain ⟨n,a,_,read⟩ := polynomial_spectrum R hn
    have atU := (read u hu).mp (force n a ((read t ht).mpr (Or.inl ((root t).mpr ⟨pt,qt⟩))))
    exact atU.elim (fun h => pu ((root u).mp h).1) (fun h => qu ((root (-u)).mp h).2)
  · intro inclusion n a read
    by_cases symm : Reflects (energy ∘ a)
    · exact reflection_agrees symm u
    have size := size_of_asymmetric a symm
    have hit : certificate a ∈ kernel t := (certificate_root a size t).mpr read
    apply (certificate_root a size u).mp
    exact inclusion.elim (fun h => h hit) (fun h => (certificate_sign symm u).mp (h hit))

theorem attainable_finite {S : Set ℝ} (h : Attainable S) : S.Finite := by
  obtain ⟨_,a,_,rfl⟩ := h
  exact finite_blind (energy ∘ a)

theorem contains_resonant {t : ℝ} (ht : 0<t) :
    (∃ S, Attainable S ∧ t ∈ S) ↔ Resonant t := by
  classical
  have iff := schedule_iff {t} (by simpa using ht)
  constructor
  · rintro ⟨_,⟨n,a,asym,rfl⟩,hit⟩
    exact iff.mp ⟨n,a,asym,by simpa using hit.2.1⟩ t (Finset.mem_singleton_self t)
  · intro h
    obtain ⟨n,a,asym,hit⟩ := iff.mpr (by simpa using h)
    exact ⟨_,⟨n,a,asym,rfl⟩,ht,hit t (Finset.mem_singleton_self t),asym⟩

theorem forces_sets {t u : ℝ} (ht : 0<t) (hu : 0<u) :
    Forces t u ↔ ∀ S, Attainable S → t ∈ S → u ∈ S := by
  constructor
  · rintro h _ ⟨n,a,asym,rfl⟩ hit
    exact ⟨hu,h n a hit.2.1,asym⟩
  · intro h n a hit
    by_cases refl : Reflects (energy ∘ a)
    · exact reflection_agrees refl u
    exact (h _ ⟨n,a,refl,rfl⟩ ⟨ht,hit,refl⟩).2.1

#print axioms forces_iff
#print axioms contains_resonant
#print axioms forces_sets

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
