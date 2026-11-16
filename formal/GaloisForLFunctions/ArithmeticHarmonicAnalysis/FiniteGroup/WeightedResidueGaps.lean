import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
# Gaps below complete residue weights

Suppose `N` nonnegative weights represent the residue classes modulo
`N` exactly once. The integers outside their nonnegative arithmetic
progressions are parametrized by the integers below each weight in its
residue class. Thus their number is the sum of the weight quotients.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Integers outside the progressions starting at a complete family of residue weights. -/
abbrev WeightedResidueGaps {N : ℕ} (D : Fin N → ℕ) :=
  {m : ℕ // ¬ ∃ i : Fin N, ∃ k : ℕ, N * k + D i = m}

variable {N : ℕ} (hN : 0 < N) (D : Fin N → ℕ)
    (hresidue : ∀ i j, D i % N = D j % N → i = j)

private def gapCoordinateMap : (Σ i : Fin N, Fin (D i / N)) → WeightedResidueGaps D :=
  fun a => ⟨N * a.2.val + D a.1 % N, by
    rintro ⟨j, k, hj⟩
    have hmod := congrArg (fun t => t % N) hj
    simp only [Nat.mul_add_mod_self_left, Nat.mod_mod] at hmod
    have heq := hresidue j a.1 hmod
    subst j
    have hlt : N * a.2.val + D a.1 % N < D a.1 := by
      calc
        _ < N * (D a.1 / N) + D a.1 % N :=
          Nat.add_lt_add_right ((Nat.mul_lt_mul_left hN).mpr a.2.isLt) _
        _ = D a.1 := Nat.div_add_mod _ _
    have hle : D a.1 ≤ N * k + D a.1 := Nat.le_add_left _ _
    omega⟩

private theorem gapCoordinateMap_injective :
    Function.Injective (gapCoordinateMap hN D hresidue) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  have hv := congrArg Subtype.val h
  change N * k.val + D i % N = N * l.val + D j % N at hv
  have hmod := congrArg (fun t => t % N) hv
  simp only [Nat.mul_add_mod_self_left, Nat.mod_mod] at hmod
  have hi := hresidue i j hmod
  subst j
  have hk : k = l := Fin.ext
    (Nat.eq_of_mul_eq_mul_left hN (Nat.add_right_cancel hv))
  subst l
  rfl

private theorem gapCoordinateMap_surjective :
    Function.Surjective (gapCoordinateMap hN D hresidue) := by
  intro m
  let ρ : Fin N → Fin N := fun i => ⟨D i % N, Nat.mod_lt _ hN⟩
  have hρ : Function.Injective ρ := by
    intro i j h
    exact hresidue i j (congrArg Fin.val h)
  obtain ⟨i, hi⟩ := (Finite.surjective_of_injective hρ) ⟨m.val % N, Nat.mod_lt _ hN⟩
  have hmod : D i % N = m.val % N := congrArg Fin.val hi
  have hk : m.val / N < D i / N := by
    by_contra h
    have hle : D i / N ≤ m.val / N := Nat.le_of_not_gt h
    apply m.property
    refine ⟨i, m.val / N - D i / N, ?_⟩
    calc
      N * (m.val / N - D i / N) + D i =
          N * (m.val / N - D i / N) + (N * (D i / N) + D i % N) := by
            rw [Nat.div_add_mod]
      _ = N * ((m.val / N - D i / N) + D i / N) + D i % N := by
        rw [Nat.mul_add, Nat.add_assoc]
      _ = N * (m.val / N) + m.val % N := by rw [Nat.sub_add_cancel hle, hmod]
      _ = m.val := Nat.div_add_mod _ _
  refine ⟨⟨i, ⟨m.val / N, hk⟩⟩, Subtype.ext ?_⟩
  change N * (m.val / N) + D i % N = m.val
  rw [hmod, Nat.div_add_mod]

/-- Every gap has a unique residue character and an index below that character's weight quotient. -/
def weightedResidueGapEquiv : (Σ i : Fin N, Fin (D i / N)) ≃ WeightedResidueGaps D :=
  Equiv.ofBijective (gapCoordinateMap hN D hresidue)
    ⟨gapCoordinateMap_injective hN D hresidue, gapCoordinateMap_surjective hN D hresidue⟩

include hN hresidue in
/-- Complete residue weights leave exactly the sum of their quotients many gaps. -/
theorem weightedResidueGaps_card :
    Nat.card (WeightedResidueGaps D) = ∑ i : Fin N, D i / N := by
  rw [← Nat.card_congr (weightedResidueGapEquiv hN D hresidue), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  simp only [Fintype.card_fin]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
