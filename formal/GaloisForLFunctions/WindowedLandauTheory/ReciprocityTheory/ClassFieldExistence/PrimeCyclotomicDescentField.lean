import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-! Adjoining the p-th roots of unity for a prime p gives a finite
cyclic extension of a number field. -/

open scoped Cyclotomic

namespace GlobalTheory.Reciprocity

variable (K : Type) [Field K] [NumberField K]

theorem primeCyclotomicField_isCyclic (p : ℕ) (hp : p.Prime) :
    IsCyclic (CyclotomicField p K ≃ₐ[K] CyclotomicField p K) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  let hζ := IsCyclotomicExtension.zeta_spec p K (CyclotomicField p K)
  exact isCyclic_of_injective (hζ.autToPow K) (hζ.autToPow_injective K)

theorem primeCyclotomicField_hasEnoughRootsOfUnity (p : ℕ) (hp : p.Prime) :
    HasEnoughRootsOfUnity (CyclotomicField p K) p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact ⟨⟨_, IsCyclotomicExtension.zeta_spec p K (CyclotomicField p K)⟩,
    rootsOfUnity.isCyclic (CyclotomicField p K) p⟩

end GlobalTheory.Reciprocity
