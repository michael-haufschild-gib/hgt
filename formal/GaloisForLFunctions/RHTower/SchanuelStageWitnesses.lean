import GaloisForLFunctions.RHTower.SchanuelWeldApex
import GaloisForLFunctions.RHTower.ExpAlgebraicTranscendental
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Stagewise form of the Schanuel interface, and its first two stages

Schanuel's conjecture is carried in the corpus as one `Prop` interface quantified over the family
size.  Splitting it stagewise isolates exactly which stages are open: the empty and one-element
stages hold unconditionally.  The latter is Hermite–Lindemann: for every nonzero complex number,
either it or its exponential is transcendental.  Thus stage two is the first genuinely open stage.
-/

namespace GaloisForLFunctions.RHTower

/-- The extraction form of Schanuel's conjecture at one fixed family size. -/
def SchanuelExtractionAt (n : ℕ) : Prop :=
  ∀ x : Fin n → ℂ, LinearIndependent ℚ x →
    ∃ t : Fin n → ℂ, Function.Injective t ∧
      (∀ i, t i ∈ Set.range x ∪ Set.range (fun j => Complex.exp (x j))) ∧
      AlgebraicIndependent ℚ t

/-- The interface is exactly the conjunction of its stages. -/
theorem schanuelConjecture_iff_forall_stage :
    SchanuelConjecture ↔ ∀ n, SchanuelExtractionAt n := by
  constructor
  · intro h n x hx
    exact h n x hx
  · intro h n x hx
    exact h n x hx

/-- Stage zero holds unconditionally. -/
theorem schanuelExtractionAt_zero : SchanuelExtractionAt 0 := by
  intro x _
  refine ⟨x, ?_, ?_, algebraicIndependent_empty_type⟩
  · intro a b _
    exact a.elim0
  · intro i
    exact i.elim0

/-- **Stage one is Hermite–Lindemann.**  The one-element stage of the extraction form holds exactly
when for every nonzero complex number either it or its exponential is transcendental over `ℚ`. -/
theorem schanuelExtractionAt_one_iff :
    SchanuelExtractionAt 1 ↔
      ∀ z : ℂ, z ≠ 0 → Transcendental ℚ z ∨ Transcendental ℚ (Complex.exp z) := by
  constructor
  · intro h z hz
    have hli : LinearIndependent ℚ (fun _ : Fin 1 => z) := by
      rw [linearIndependent_unique_iff]
      exact hz
    obtain ⟨t, _, hmem, hind⟩ := h _ hli
    have htrans : Transcendental ℚ (t 0) :=
      algebraicIndependent_unique_type_iff.mp hind
    rcases hmem 0 with hcase | hcase
    · obtain ⟨j, hj⟩ := hcase
      rw [← hj] at htrans
      exact Or.inl htrans
    · obtain ⟨j, hj⟩ := hcase
      rw [← hj] at htrans
      exact Or.inr htrans
  · intro h x hx
    have hx0 : x 0 ≠ 0 := by
      have := linearIndependent_unique_iff.mp hx
      simpa using this
    rcases h (x 0) hx0 with htrans | htrans
    · refine ⟨fun _ => x 0, ?_, ?_, ?_⟩
      · intro a b _
        exact Subsingleton.elim a b
      · intro i
        exact Or.inl ⟨0, rfl⟩
      · exact algebraicIndependent_unique_type_iff.mpr htrans
    · refine ⟨fun _ => Complex.exp (x 0), ?_, ?_, ?_⟩
      · intro a b _
        exact Subsingleton.elim a b
      · intro i
        exact Or.inr ⟨0, rfl⟩
      · exact algebraicIndependent_unique_type_iff.mpr htrans

/-- **Stage one holds unconditionally.**  This is Hermite–Lindemann, with the algebraic case
discharged by `exp_algebraic_transcendental`. -/
theorem schanuelExtractionAt_one : SchanuelExtractionAt 1 := by
  rw [schanuelExtractionAt_one_iff]
  intro z hz
  by_cases hzalg : IsAlgebraic ℤ z
  · exact Or.inr (exp_algebraic_transcendental hzalg hz)
  · left
    intro hzalgQ
    exact hzalg ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hzalgQ)

end GaloisForLFunctions.RHTower
