import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.AffineMomentSystem

/-!
# Sharpness of the affine Helly bound over every field

The coordinate equations `xᵢ = 0`, together with `∑ xᵢ = 1`, give `N + 1`
inconsistent affine equations in `N` variables. Deleting the sum equation
admits the zero point; deleting a coordinate equation admits the corresponding
unit vector. Consequently every subsystem of at most `N` equations is
consistent, including subsystems listed with repetition.

The same example applies to paired moment equations by setting `zᵢ = 1` and
`wᵢ = xᵢ`. The construction includes the zero-dimensional case and requires
no restriction on the characteristic or cardinality of the field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem
open MvPolynomial Module Classical
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Coordinate rows and one additional row summing all coordinates. -/
def obstructionRow : Option ι → ι → K
  | none => 1
  | some i => Pi.single i 1

/-- Coordinate values are zero, while the prescribed sum is one. -/
def obstructionValue : Option ι → K
  | none => 1
  | some _ => 0

/-- Deleting the sum equation permits zero; deleting coordinate `i` permits its unit vector. -/
def omissionPoint : Option ι → ι → K
  | none => 0
  | some i => Pi.single i 1

/-- The omission point satisfies every equation except the deleted one. -/
theorem omissionPoint_spec (j k : Option ι) (hk : k ≠ j) :
    eval (omissionPoint K j) (momentLinearForm K (obstructionRow K k)) =
      obstructionValue K k := by
  rw [eval_momentLinearForm]
  cases j with
  | none =>
    cases k with
    | none => exact False.elim (hk rfl)
    | some k => simp [omissionPoint, obstructionRow, obstructionValue]
  | some j =>
    cases k with
    | none => simp [omissionPoint, obstructionRow, obstructionValue]
    | some k =>
      have hkj : k ≠ j := fun h => hk (congrArg Option.some h)
      simp [omissionPoint, obstructionRow, obstructionValue, Pi.single_apply, Ne.symm hkj]

/-- Vanishing of every coordinate contradicts their prescribed sum of one. -/
theorem coordinate_obstruction_incompatible :
    ¬ Compatible K (obstructionRow K : Option ι → ι → K) (obstructionValue K) := by
  intro h
  obtain ⟨x, hx⟩ := (compatible_iff_exists_point K _ _).mp h
  have hz : x = 0 := by
    funext i
    have hi := hx (some i)
    rw [eval_momentLinearForm] at hi
    simpa [obstructionRow, obstructionValue, Pi.single_apply, ite_mul] using hi
  have hn := hx none
  rw [eval_momentLinearForm] at hn
  simp [hz, obstructionRow, obstructionValue] at hn

/-- Every deletion from the inconsistent family is consistent. -/
theorem coordinate_obstruction_delete_compatible (j : Option ι) :
    Compatible K (fun k : {k : Option ι // k ≠ j} => obstructionRow K k.1)
      (fun k => obstructionValue K k.1) := by
  apply (compatible_iff_exists_point K _ _).mpr
  exact ⟨omissionPoint K j, fun k => omissionPoint_spec K j k.1 k.2⟩

/-- A list of at most `N` equations omits one of the `N + 1` constraints. -/
theorem coordinate_obstruction_small_subsystem_compatible (n : ℕ)
    (f : Fin n → Option ι) (hn : n ≤ Fintype.card ι) :
    Compatible K (obstructionRow K ∘ f) (obstructionValue K ∘ f) := by
  have hns : ¬ Function.Surjective f := by
    intro hs
    have hc := Fintype.card_le_of_surjective f hs
    rw [Fintype.card_option, Fintype.card_fin] at hc
    omega
  have hex : ∃ j, ∀ i, f i ≠ j := by
    by_contra h
    apply hns
    intro j
    by_contra hj
    apply h
    exact ⟨j, fun i hi => hj ⟨i, hi⟩⟩
  obtain ⟨j, hj⟩ := hex
  apply (compatible_iff_exists_point K _ _).mpr
  exact ⟨omissionPoint K j, fun i => omissionPoint_spec K j (f i) (hj i)⟩

/-- Testing all subsystems of size at most `N` cannot establish consistency in `N` variables. -/
theorem affine_helly_bound_sharp :
    ∃ (a : Option ι → ι → K) (b : Option ι → K),
      ¬ Compatible K a b ∧
      ∀ n ≤ Fintype.card ι, ∀ f : Fin n → Option ι, Compatible K (a ∘ f) (b ∘ f) := by
  exact ⟨obstructionRow K, obstructionValue K, coordinate_obstruction_incompatible K,
    fun n hn f => coordinate_obstruction_small_subsystem_compatible K n f hn⟩

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem.affine_helly_bound_sharp
