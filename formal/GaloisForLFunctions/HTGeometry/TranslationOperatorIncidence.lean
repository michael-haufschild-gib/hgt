import GaloisForLFunctions.HTGeometry.FacetQuotientDomain
import GaloisForLFunctions.HTGeometry.FullPeriodExtraction

/-!
# Transporting an annihilation dictionary into periods

A shift operator acting on functions turns an algebraic annihilation into a period.  Translation by
`a` fixes `G` exactly when `a` is a period of `G`, so a dictionary sending the vertex coordinate
`x_v` to `T_(a v) - id` converts "`x_v` annihilates the facet separator" into "`a v` is a period of
its realization".  Vertex incidence for the period group is then the facet complement, verbatim.

The same dictionary converts freeness of the complete integral facet orbit into the statement that
the facet's integral lattice meets the period group only at the origin -- the hypothesis the facet
certificate's lattice-class injectivity needs.
-/

namespace GaloisForLFunctions.HTGeometry

variable {W : Type*} [AddCommGroup W] {Y : Type*}

/-- Translation of a function by a group element. -/
def translateOp (a : W) (G : W → Y) : W → Y := fun z => G (z + a)

@[simp]
theorem translateOp_zero (G : W → Y) : translateOp 0 G = G := by
  funext z
  rw [translateOp, add_zero]

theorem translateOp_add (a b : W) (G : W → Y) :
    translateOp a (translateOp b G) = translateOp (a + b) G := by
  funext z
  rw [translateOp, translateOp, translateOp, add_assoc]

/-- **Translation fixes a function exactly at its periods.** -/
theorem translateOp_eq_self_iff (a : W) (G : W → Y) :
    translateOp a G = G ↔ a ∈ translationPeriods G := by
  constructor
  · intro h z
    exact congrFun h z
  · intro h
    funext z
    exact h z

/-- **Vertex incidence from an annihilation dictionary.**  If translation by `a v` fixes the
realization exactly for the vertices outside the facet, the period group's vertex incidence is the
facet complement. -/
theorem mem_translationPeriods_iff_of_translateOp {α : Type*} {a : α → W} {G : W → Y}
    {A : Finset α} (h : ∀ v : α, translateOp (a v) G = G ↔ v ∉ A) (v : α) :
    a v ∈ translationPeriods G ↔ v ∉ A := by
  rw [← translateOp_eq_self_iff]
  exact h v

/-- **A free integral orbit meets the periods only at the origin.**  If distinct integral exponents
translate the realization to distinct functions, no nonzero integral combination of the vertex
displacements is a period.  This is the hypothesis the certificate's lattice-class injectivity
consumes. -/
theorem eq_zero_of_mem_translationPeriods_of_injective {α : Type*} [Fintype α] {a : α → W}
    {G : W → Y} (hinj : Function.Injective fun n : α → ℤ => translateOp (∑ v, (n v) • a v) G)
    (k : α → ℤ) (hk : (∑ v, (k v) • a v) ∈ translationPeriods G) : k = 0 := by
  have h1 : translateOp (∑ v, (k v) • a v) G = G := (translateOp_eq_self_iff _ _).mpr hk
  have hsum0 : (∑ v, ((0 : α → ℤ) v) • a v) = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [Pi.zero_apply, zero_zsmul]
  have h2 : translateOp (∑ v, ((0 : α → ℤ) v) • a v) G = G := by
    rw [hsum0, translateOp_zero]
  exact hinj (h1.trans h2.symm)

end GaloisForLFunctions.HTGeometry
