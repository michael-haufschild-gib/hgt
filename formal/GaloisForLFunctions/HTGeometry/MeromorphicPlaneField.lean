import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Topology.DiscreteSubset

/-!
# The field of meromorphic functions on the plane

Two meromorphic functions on `ℂ` define the same meromorphic function exactly when they agree near
every point off that point, that is, when they agree along the codiscrete filter.  Germs along that
filter therefore carry the genuine field of meromorphic functions on `ℂ`:

* `meromorphicPlaneSubring` — the germs represented by a meromorphic function;
* `MeromorphicPlane` — that subring with its field structure, the inverse of a nonzero germ being
  the pointwise inverse, which is meromorphic and inverts it off the discrete zero set;
* `isOpen_of_mem_planeCodiscrete` — a codiscrete set is open, its complement being closed and
  discrete.

Unlike a fraction field of entire functions, this carrier contains every meromorphic function
directly: no factorisation theorem is needed to represent `℘`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The codiscrete filter of the plane: a set belongs to it exactly when it contains a punctured
neighbourhood of every point. -/
noncomputable abbrev planeCodiscrete : Filter ℂ := Filter.codiscreteWithin (Set.univ : Set ℂ)

theorem mem_planeCodiscrete {S : Set ℂ} :
    S ∈ planeCodiscrete ↔ ∀ x : ℂ, S ∈ 𝓝[≠] x := by
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  simp

theorem eventuallyEq_planeCodiscrete_iff {f g : ℂ → ℂ} :
    f =ᶠ[planeCodiscrete] g ↔ ∀ x : ℂ, f =ᶠ[𝓝[≠] x] g := by
  constructor
  · intro h x
    exact (mem_planeCodiscrete.mp h) x
  · intro h
    exact mem_planeCodiscrete.mpr fun x => h x

/-- A codiscrete set of the plane is open: its complement is closed and discrete. -/
theorem isOpen_of_mem_planeCodiscrete {S : Set ℂ} (hS : S ∈ planeCodiscrete) : IsOpen S := by
  have hclosed : IsClosed ((Set.univ : Set ℂ) \ S) :=
    isClosed_sdiff_of_codiscreteWithin hS isClosed_univ
  have hcompl : Sᶜ = (Set.univ : Set ℂ) \ S := by
    ext z; simp
  rw [← isClosed_compl_iff, hcompl]
  exact hclosed

/-- The subring of germs along the codiscrete filter that are represented by a meromorphic
function. -/
noncomputable def meromorphicPlaneSubring : Subring (Germ planeCodiscrete ℂ) where
  carrier := {g | ∃ f : ℂ → ℂ, (∀ z, MeromorphicAt f z) ∧ (f : Germ planeCodiscrete ℂ) = g}
  zero_mem' := ⟨0, fun z => MeromorphicAt.const 0 z, rfl⟩
  one_mem' := ⟨1, fun z => MeromorphicAt.const 1 z, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, fun z => (hf z).add (hg z), rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, fun z => (hf z).mul (hg z), rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, fun z => (hf z).neg, rfl⟩

theorem mem_meromorphicPlaneSubring_coe {f : ℂ → ℂ} (hf : ∀ z, MeromorphicAt f z) :
    (f : Germ planeCodiscrete ℂ) ∈ meromorphicPlaneSubring := ⟨f, hf, rfl⟩

/-- **A meromorphic function with a nonzero germ is invertible.**  Either its order is `⊤`
everywhere, in which case it vanishes on a codiscrete set, or it is nowhere locally zero and its
pointwise inverse is meromorphic and inverts it off the discrete zero set. -/
theorem exists_inv_of_ne_zero {g : Germ planeCodiscrete ℂ}
    (hg : g ∈ meromorphicPlaneSubring) (hne : g ≠ 0) :
    ∃ h ∈ meromorphicPlaneSubring, g * h = 1 := by
  obtain ⟨f, hf, rfl⟩ := hg
  have hmerOn : MeromorphicOn f Set.univ := fun w _ => hf w
  have hnetop : ∀ z : ℂ, meromorphicOrderAt f z ≠ ⊤ := by
    intro z htop
    refine hne ?_
    have hall : ∀ x : ℂ, meromorphicOrderAt f x = ⊤ := by
      intro x
      by_contra hx
      exact htop (hmerOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
        (Set.mem_univ x) (Set.mem_univ z) hx)
    have hzero : (f : Germ planeCodiscrete ℂ) = ((0 : ℂ → ℂ) : Germ planeCodiscrete ℂ) := by
      refine Germ.coe_eq.mpr (eventuallyEq_planeCodiscrete_iff.mpr fun x => ?_)
      exact meromorphicOrderAt_eq_top_iff.mp (hall x)
    simpa using hzero
  refine ⟨(f⁻¹ : ℂ → ℂ), ⟨f⁻¹, fun z => (hf z).inv, rfl⟩, ?_⟩
  have hset : {z : ℂ | f z ≠ 0} ∈ planeCodiscrete := by
    refine mem_planeCodiscrete.mpr fun x => ?_
    exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf x)).mp (hnetop x)
  have hprod : (f * f⁻¹ : ℂ → ℂ) =ᶠ[planeCodiscrete] (1 : ℂ → ℂ) := by
    filter_upwards [hset] with z hz
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
    exact mul_inv_cancel₀ hz
  exact Germ.coe_eq.mpr hprod

theorem one_ne_zero_germ :
    ((1 : ℂ → ℂ) : Germ planeCodiscrete ℂ) ≠ ((0 : ℂ → ℂ) : Germ planeCodiscrete ℂ) := by
  intro h
  have heq := eventuallyEq_planeCodiscrete_iff.mp (Germ.coe_eq.mp h) 0
  obtain ⟨z, hz⟩ := heq.exists
  simp only [Pi.one_apply, Pi.zero_apply] at hz
  exact one_ne_zero hz

/-- **The field of meromorphic functions on the plane.** -/
def MeromorphicPlane : Type := meromorphicPlaneSubring

noncomputable instance : CommRing MeromorphicPlane :=
  inferInstanceAs (CommRing meromorphicPlaneSubring)

theorem isField_meromorphicPlane : IsField MeromorphicPlane := by
  refine ⟨⟨0, 1, ?_⟩, mul_comm, ?_⟩
  · intro h
    exact one_ne_zero_germ (congrArg Subtype.val h).symm
  · intro x hne
    have hne' : (show (meromorphicPlaneSubring : Type) from x).1 ≠ 0 := by
      intro h
      exact hne (Subtype.ext h)
    obtain ⟨h, hh, hgh⟩ :=
      exists_inv_of_ne_zero (show (meromorphicPlaneSubring : Type) from x).2 hne'
    exact ⟨show MeromorphicPlane from ⟨h, hh⟩, Subtype.ext hgh⟩

noncomputable instance : Field MeromorphicPlane := isField_meromorphicPlane.toField

/-- The germ underlying an element of the meromorphic plane field. -/
def MeromorphicPlane.germ (x : MeromorphicPlane) : Germ planeCodiscrete ℂ :=
  (show (meromorphicPlaneSubring : Type) from x).1

theorem MeromorphicPlane.germ_injective : Function.Injective MeromorphicPlane.germ := by
  intro x y h
  exact Subtype.ext h

/-- The germ of a meromorphic function, as an element of the meromorphic plane field. -/
noncomputable def ofMeromorphic (f : ℂ → ℂ) (hf : ∀ z, MeromorphicAt f z) : MeromorphicPlane :=
  show MeromorphicPlane from ⟨(f : Germ planeCodiscrete ℂ), ⟨f, hf, rfl⟩⟩

@[simp] theorem germ_ofMeromorphic (f : ℂ → ℂ) (hf : ∀ z, MeromorphicAt f z) :
    (ofMeromorphic f hf).germ = (f : Germ planeCodiscrete ℂ) := rfl

theorem ofMeromorphic_eq_iff {f g : ℂ → ℂ} (hf : ∀ z, MeromorphicAt f z)
    (hg : ∀ z, MeromorphicAt g z) :
    ofMeromorphic f hf = ofMeromorphic g hg ↔ ∀ x : ℂ, f =ᶠ[𝓝[≠] x] g := by
  constructor
  · intro h
    have := congrArg MeromorphicPlane.germ h
    rw [germ_ofMeromorphic, germ_ofMeromorphic] at this
    exact eventuallyEq_planeCodiscrete_iff.mp (Germ.coe_eq.mp this)
  · intro h
    refine MeromorphicPlane.germ_injective ?_
    rw [germ_ofMeromorphic, germ_ofMeromorphic]
    exact Germ.coe_eq.mpr (eventuallyEq_planeCodiscrete_iff.mpr h)

/-- The Weierstrass `℘` of a period lattice, as an element of the meromorphic plane field. -/
noncomputable def weierstrassPElement (L : PeriodPair) : MeromorphicPlane :=
  ofMeromorphic L.weierstrassP L.meromorphic_weierstrassP

/-- The derivative of `℘`, as an element of the meromorphic plane field. -/
noncomputable def derivWeierstrassPElement (L : PeriodPair) : MeromorphicPlane :=
  ofMeromorphic L.derivWeierstrassP L.meromorphic_derivWeierstrassP

end GaloisForLFunctions.HTGeometry
