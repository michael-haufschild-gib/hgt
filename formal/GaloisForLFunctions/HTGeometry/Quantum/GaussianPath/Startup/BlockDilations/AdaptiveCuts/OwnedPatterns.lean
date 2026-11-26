import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.BondSelector
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.PartitionTransfer

/-! # Pattern counting on the actual weakest-bond partition -/

open MeasureTheory ProbabilityTheory Finset Set
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
variable {ι I B J : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [Nonempty I]
  [LinearOrder I] [Fintype B] [Fintype J]

/-- Select the first minimum of the bond energy in each buffer. -/
def owners (L : B→I→Fin 9→ι) (x : ι→ℝ) (b : B) : I :=
  Classical.choose (existsUnique_firstMinimum (fun i => bondSquare (L b i) x))

def ownerCell (L : B→I→Fin 9→ι) (p : B→I) : Set (ι→ℝ) :=
  {x | ∀ b, IsFirstMinimum (fun i => bondSquare (L b i) x) (p b)}

omit [Fintype ι] [DecidableEq ι] [Fintype B] in
theorem ownerCell_iff (L : B→I→Fin 9→ι) (p : B→I) (x : ι→ℝ) :
    x∈ownerCell L p ↔ p=owners L x := by
  constructor
  · intro h
    funext b
    exact (Classical.choose_spec (existsUnique_firstMinimum (fun i => bondSquare (L b i) x))).2 _ (h b)
  · rintro rfl b
    exact (Classical.choose_spec (existsUnique_firstMinimum (fun i => bondSquare (L b i) x))).1

omit [Fintype ι] [DecidableEq ι] [Nonempty I] in
theorem measurable_ownerCell (L : B→I→Fin 9→ι) (p : B→I) : MeasurableSet (ownerCell L p) := by
  have h : ownerCell L p=⋂ b, {x | IsFirstMinimum (fun i => bondSquare (L b i) x) (p b)} := by
    ext x
    simp [ownerCell]
  rw [h]
  exact MeasurableSet.iInter (fun b => measurable_bond_owner (L b) (p b))

/-- Every mask expands all nine coordinates on every selected seam.
The largest pattern count on one actual partition suffices to bound
the probability of the observable measured on its own partition. -/
theorem weakest_bond_pattern_cap (L : B→I→Fin 9→ι) (S : (B→I)→J→Finset ι)
    (hS : ∀ p j b k, L b (p b) k∈S p j) (Z : (B→I)→Set (ι→ℝ))
    (hZ : ∀ p, MeasurableSet (Z p)) {a : ℝ} (ha : 1≤a) :
    open Classical in
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    ∀ M : ℝ, (∀ x, ((univ.filter fun j => expand (S (owners L x) j) a x∈Z (owners L x)).card:ℝ)≤M) →
      μ.real {x | x∈Z (owners L x)}*(Fintype.card J:ℝ) ≤ a^Fintype.card ι*M := by
  classical
  intro μ M hM
  let E (p : B→I) := ownerCell L p ∩ Z p
  have hE (p : B→I) : MeasurableSet (E p) := (measurable_ownerCell L p).inter (hZ p)
  have howner (x : ι→ℝ) (p : B→I) (j : J) (h : expand (S p j) a x∈E p) : p=owners L x := by
    apply (ownerCell_iff L p x).mp
    intro b
    exact expanded_owner_reflects (L b) (S p j) ha x (p b) (h.1 b) (hS p j b)
  have hset : {x | x∈Z (owners L x)}=⋃ p, E p := by
    ext x
    constructor
    · intro hx
      exact mem_iUnion.mpr ⟨owners L x,(ownerCell_iff ..).mpr rfl,hx⟩
    · rintro hx
      obtain ⟨p,hp,hx⟩ := mem_iUnion.mp hx
      change x∈Z (owners L x)
      rwa [←(ownerCell_iff L p x).mp hp]
  rw [hset]
  apply (mul_le_mul_of_nonneg_right (measureReal_iUnion_fintype_le E) (Nat.cast_nonneg _)).trans
  apply partition_pattern_cap S E hE (owners L) ha howner M
  intro x
  apply le_trans _ (hM x)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro j hj
  have hjE := (mem_filter.mp (p:=fun y => expand (S (owners L x) y) a x∈E (owners L x)) hj).2
  exact mem_filter.mpr ⟨mem_univ _,hjE.2⟩

#print axioms weakest_bond_pattern_cap
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
