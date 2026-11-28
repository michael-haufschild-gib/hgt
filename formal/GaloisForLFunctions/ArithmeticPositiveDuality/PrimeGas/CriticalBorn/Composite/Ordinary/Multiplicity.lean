import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Shells
import GaloisForLFunctions.PrimeTorusTheory.TheDiagonalRange

/-! # Uniform multiplicity bounds for ordinary occupation labels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary

open Finset
open GaloisForLFunctions.PrimeTorusTheory

theorem product_val {m : ℕ} {x : ℝ} (q : Fin m → PrimeAt x) :
    (productLabel q : ℕ)=tupleProd q :=
  map_prod PNat.coeMonoidHom (fun i => primeLabel (q i)) univ

/-- Unique factorization confines the ordered representations of a fixed
integer to a permutation orbit of its m elementary factors. -/
theorem multiplicity_bounds {m : ℕ} {x : ℝ} {n : ℕ+} (hn : n∈shells m x) :
    1 ≤ multiplicity m x n ∧ multiplicity m x n ≤ m.factorial := by
  obtain ⟨u,_,rfl⟩ := mem_image.mp hn
  constructor
  · exact card_pos.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
  · have fibers : (univ.filter fun v : Fin m → PrimeAt x => productLabel v=productLabel u) =
        univ.filter fun v : Fin m → PrimeAt x => tupleProd v=tupleProd u := by
      ext v
      simp only [mem_filter,mem_univ,true_and,←product_val]
      exact ⟨congrArg (fun n : ℕ+ => (n:ℕ)),fun h => PNat.coe_injective h⟩
    rw [multiplicity,fibers]
    exact card_fiber_le (fun p hp => (Nat.mem_primesBelow.mp hp).2) u

/-- On a tuple of distinct primes every permutation gives a different
ordered factorization, attaining the factorial bound exactly. -/
theorem multiplicity_injective {m : ℕ} {x : ℝ} (u : Fin m → PrimeAt x) (hu : Function.Injective u) :
    multiplicity m x (productLabel u) = m.factorial := by
  classical
  let permute (σ : Equiv.Perm (Fin m)) := u ∘ σ
  have inj : Function.Injective permute := by
    intro σ τ hs
    exact Equiv.ext fun i => hu (congrFun hs i)
  have sub : univ.image permute ⊆ univ.filter (fun v : Fin m → PrimeAt x => productLabel v=productLabel u) := by
    intro v hv
    obtain ⟨σ,_,rfl⟩ := mem_image.mp hv
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    exact Equiv.prod_comp σ (fun i => primeLabel (u i))
  have lower := card_le_card sub
  rw [card_image_of_injective _ inj,card_univ,Fintype.card_perm,Fintype.card_fin] at lower
  exact le_antisymm (multiplicity_bounds (mem_image_of_mem productLabel (mem_univ u))).2 lower

#print axioms multiplicity_injective
#print axioms product_val
#print axioms multiplicity_bounds

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary
