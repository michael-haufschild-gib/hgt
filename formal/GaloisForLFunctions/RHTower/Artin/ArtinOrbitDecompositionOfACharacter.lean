import GaloisForLFunctions.RHTower.Artin.ArtinIdempotentsOfAnAbelianNormalSubgroup
import GaloisForLFunctions.RHTower.Artin.ArtinClassFunctionInduction
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# A character is a sum of functions induced from stabilizers

Let `A` be an abelian normal subgroup of a finite group `E`, `ρ` a representation of `E`, and
for a linear character `χ` of `A` let `T_χ` be its stabilizer in `E` and
`F_χ(g) = tr(ρ(g) e_χ)`. Put `m_χ = Ind_{T_χ}^E F_χ` (`stabilizerInduced`).

* `|T_χ| · m_χ(g) = Σ_{x ∈ E} F_{x • χ}(g)` (`card_mul_stabilizerInduced`), because `F_χ` vanishes
  off `T_χ` and `F_χ(x g x⁻¹) = F_{x⁻¹ • χ}(g)`.
* The right side is constant on the orbits of `E`, and summed over all `χ` it is `|E|` times the
  character of `ρ`. Regrouping by orbits, with the orbit–stabilizer count
  (`sum_eq_sum_orbit_representatives`), gives

  `character of ρ = Σ_{orbits} m_χ`   (`character_eq_sum_stabilizerInduced`).

So the character lies in every additive group of functions that contains all `m_χ`
(`character_mem_of_stabilizerInduced_mem`).
-/

open scoped Classical BigOperators IsMulCommutative

noncomputable section

universe u w

namespace GaloisForLFunctions

attribute [local instance] finiteLinearCharacter fintypeLinearCharacter conjCharacterAction

/-! ### Sums over the orbits of a finite group action -/

/-- **A sum of an invariant function over a finite set with a group action is a sum over
representatives of the orbits**, each weighted by the size `|E| / |Stab|` of its orbit. -/
theorem sum_eq_sum_orbit_representatives {E : Type u} [Group E] [Fintype E] {X : Type u}
    [Fintype X] [MulAction E X] (n : X → ℂ) (hn : ∀ (y : E) (x : X), n (y • x) = n x) :
    ∑ x : X, n x = ∑ q : Quotient (MulAction.orbitRel E X),
      ((Nat.card E : ℂ) / Nat.card (MulAction.stabilizer E (Quotient.out q))) *
        n (Quotient.out q) := by
  rw [← Finset.sum_fiberwise Finset.univ (Quotient.mk (MulAction.orbitRel E X)) n]
  refine Finset.sum_congr rfl fun q _ => ?_
  -- the fibre of `q` is the orbit of its representative
  have hfib : ∀ x : X, Quotient.mk (MulAction.orbitRel E X) x = q ↔
      x ∈ MulAction.orbit E (Quotient.out q) := by
    intro x
    constructor
    · intro hx
      have hq : Quotient.mk (MulAction.orbitRel E X) x =
          Quotient.mk (MulAction.orbitRel E X) (Quotient.out q) := by rw [hx, Quotient.out_eq]
      exact MulAction.orbitRel_apply.mp (Quotient.exact hq)
    · intro hx
      have hq := Quotient.sound (s := MulAction.orbitRel E X) (MulAction.orbitRel_apply.mpr hx)
      rw [hq, Quotient.out_eq]
  -- on the fibre the function is constant
  have hconst : ∀ x : X, Quotient.mk (MulAction.orbitRel E X) x = q → n x = n (Quotient.out q) := by
    intro x hx
    obtain ⟨y, hy⟩ := (hfib x).mp hx
    rw [← hy]
    exact hn y _
  -- orbit–stabilizer
  have hcard : ∀ s : Finset X, (∀ x, x ∈ s ↔ Quotient.mk (MulAction.orbitRel E X) x = q) →
      s.card * Nat.card (MulAction.stabilizer E (Quotient.out q)) = Nat.card E := by
    intro s hs
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group E (Quotient.out q)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← h]
    congr 1
    exact (Fintype.card_of_subtype (p := fun x => x ∈ MulAction.orbit E (Quotient.out q)) s
      fun x => (hs x).trans (hfib x)).symm
  have hT : (Nat.card (MulAction.stabilizer E (Quotient.out q)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [Finset.sum_congr rfl fun x hx => hconst x (Finset.mem_filter.mp hx).2, Finset.sum_const,
    nsmul_eq_mul]
  congr 1
  rw [eq_div_iff hT, ← Nat.cast_mul,
    hcard _ fun x => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ x))]

/-! ### The functions induced from the stabilizers -/

variable {E : Type u} [Group E] [Fintype E] (A : Subgroup E) [A.Normal] [IsMulCommutative A]
  {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ E V)

/-- `m_χ = Ind_{T_χ}^E F_χ`: the function induced from the stabilizer of `χ`. -/
def stabilizerInduced (χ : LinearCharacter A) : E → ℂ :=
  inducedFunction (MulAction.stabilizer E χ) fun t => isotypicTrace A ρ χ (t : E)

/-- `|T_χ| · m_χ(g) = Σ_x F_{x • χ}(g)`. -/
theorem card_mul_stabilizerInduced (χ : LinearCharacter A) (g : E) :
    (Nat.card (MulAction.stabilizer E χ) : ℂ) * stabilizerInduced A ρ χ g =
      ∑ x : E, isotypicTrace A ρ (x • χ) g := by
  -- `F_χ` vanishes off the stabilizer, so it is its own extension by zero
  have hext : ∀ y : E, extendByZero (MulAction.stabilizer E χ)
      (fun t => isotypicTrace A ρ χ (t : E)) y = isotypicTrace A ρ χ y := by
    intro y
    by_cases hy : y ∈ MulAction.stabilizer E χ
    · exact extendByZero_of_mem _ _ hy
    · rw [extendByZero_of_notMem _ _ hy]
      exact (isotypicTrace_eq_zero A ρ fun h => hy (MulAction.mem_stabilizer_iff.mpr h)).symm
  have hcard : (Nat.card (MulAction.stabilizer E χ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [stabilizerInduced, inducedFunction, mul_inv_cancel_left₀ hcard,
    Finset.sum_congr rfl fun x _ => hext (x * g * x⁻¹),
    Finset.sum_congr rfl fun x _ => isotypicTrace_conj A ρ χ x g]
  exact Equiv.sum_comp (Equiv.inv E) fun x => isotypicTrace A ρ (x • χ) g

/-- **The character is the sum, over the orbits of the characters of `A`, of the functions
induced from the stabilizers.** -/
theorem character_eq_sum_stabilizerInduced (g : E) :
    ρ.character g = ∑ q : Quotient (MulAction.orbitRel E (LinearCharacter A)),
      stabilizerInduced A ρ (Quotient.out q) g := by
  have hE : (Nat.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- summed over all characters, the orbit sums give `|E|` times the character
  have h1 : ∑ χ : LinearCharacter A, ∑ x : E, isotypicTrace A ρ (x • χ) g =
      (Nat.card E : ℂ) * ρ.character g := by
    have h : ∀ x : E, ∑ χ : LinearCharacter A, isotypicTrace A ρ (x • χ) g = ρ.character g :=
      fun x => by
        rw [← sum_isotypicTrace A ρ g]
        exact Equiv.sum_comp (MulAction.toPerm x) fun χ => isotypicTrace A ρ χ g
    rw [Finset.sum_comm, Finset.sum_congr rfl fun x _ => h x, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]
  -- the orbit sums are constant on orbits
  have h2 := sum_eq_sum_orbit_representatives (E := E)
    (fun χ : LinearCharacter A => ∑ x : E, isotypicTrace A ρ (x • χ) g) fun y χ => by
      rw [← Equiv.sum_comp (Equiv.mulRight y) fun x => isotypicTrace A ρ (x • χ) g]
      refine Finset.sum_congr rfl fun x _ => ?_
      show isotypicTrace A ρ (x • y • χ) g = isotypicTrace A ρ ((x * y) • χ) g
      rw [mul_smul]
  have h3 : ∀ q : Quotient (MulAction.orbitRel E (LinearCharacter A)),
      ((Nat.card E : ℂ) / Nat.card (MulAction.stabilizer E (Quotient.out q))) *
        ∑ x : E, isotypicTrace A ρ (x • Quotient.out q) g =
      (Nat.card E : ℂ) * stabilizerInduced A ρ (Quotient.out q) g := by
    intro q
    have hT : (Nat.card (MulAction.stabilizer E (Quotient.out q)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [← card_mul_stabilizerInduced]
    field_simp
  rw [h1, Finset.sum_congr rfl fun q _ => h3 q, ← Finset.mul_sum] at h2
  exact mul_left_cancel₀ hE h2

/-- **The character lies in every additive group of functions that contains the functions
induced from the stabilizers.** -/
theorem character_mem_of_stabilizerInduced_mem (S : AddSubgroup (E → ℂ))
    (h : ∀ χ : LinearCharacter A, stabilizerInduced A ρ χ ∈ S) : ρ.character ∈ S := by
  have e : ρ.character = ∑ q : Quotient (MulAction.orbitRel E (LinearCharacter A)),
      stabilizerInduced A ρ (Quotient.out q) := by
    funext g
    rw [character_eq_sum_stabilizerInduced A ρ g, Finset.sum_apply]
  rw [e]
  exact AddSubgroup.sum_mem _ fun q _ => h _

end GaloisForLFunctions
