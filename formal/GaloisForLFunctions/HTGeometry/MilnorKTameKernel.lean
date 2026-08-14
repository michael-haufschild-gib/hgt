import GaloisForLFunctions.HTGeometry.MilnorKTameSymbol
import GaloisForLFunctions.HTGeometry.MilnorKDegFunctoriality

/-!
# The tame kernel controls the torsion of `K_2^M`

The tame symbols at a family of places assemble into a map out of `K_2^M(K)` whose kernel is the
tame kernel.  When every residue field has a finite unit group and every class has trivial tame
symbol at almost every place, the image of a class is annihilated by the product of the orders of
its finitely many nonzero components.  So every class has a nonzero multiple in the tame kernel, and
therefore `K_2^M(K)` is torsion as soon as the tame kernel is.

For a number field this is the elementary half of the statement that `K_2^M` is torsion: the places
are the finite places, the residue fields are finite, and a fixed symbol is a unit pair at almost
every place.  What remains is exactly the finiteness of the tame kernel.

* `tameKernel` : **the tame kernel of a family of tame data.**
* `tameFiniteSupport`, `tame_finiteSupport_of_symbols` : almost-everywhere vanishing is inherited
  from symbols to all classes.
* `exists_zsmul_mem_tameKernel` : **every class has a nonzero multiple in the tame kernel.**
* `milnorKDegTwo_torsion_of_tameKernel_torsion` : **torsion of the tame kernel forces torsion of
  `K_2^M`.**
-/

namespace GaloisForLFunctions.HTGeometry

section TameKernel

variable {K : Type*} [Field K] {ι : Type*} {κ : ι → Type*} [∀ i, Field (κ i)]
variable (D : ∀ i, TameData K (κ i))

/-- **The tame kernel**: the degree-two classes with trivial tame symbol at every place. -/
def tameKernel : AddSubgroup (MilnorKDeg K 2) := ⨅ i, ((D i).tameHom).ker

theorem mem_tameKernel_iff (x : MilnorKDeg K 2) :
    x ∈ tameKernel D ↔ ∀ i, (D i).tameHom x = 0 := by
  rw [tameKernel, AddSubgroup.mem_iInf]
  exact forall_congr' fun i => AddMonoidHom.mem_ker

/-- The classes whose tame symbol vanishes at all but finitely many places. -/
def tameFiniteSupport : AddSubgroup (MilnorKDeg K 2) where
  carrier := {x | {i | (D i).tameHom x ≠ 0}.Finite}
  zero_mem' := by
    refine Set.Finite.subset Set.finite_empty ?_
    intro i hi
    exact absurd (map_zero ((D i).tameHom)) hi
  add_mem' := by
    intro x y hx hy
    refine Set.Finite.subset (hx.union hy) ?_
    intro i hi
    by_contra hnot
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hnot
    exact hi (by rw [map_add, hnot.1, hnot.2, add_zero])
  neg_mem' := by
    intro x hx
    refine Set.Finite.subset hx ?_
    intro i hi hzero
    exact hi (by rw [map_neg, hzero, neg_zero])

/-- **Almost-everywhere vanishing is inherited from the symbols**: the symbol classes generate, and
the condition is closed under sums and negatives. -/
theorem tame_finiteSupport_of_symbols
    (h : ∀ a b : Kˣ, {i | (D i).tameHom (milnorClassDeg K 2 ⟨[a, b], rfl⟩) ≠ 0}.Finite)
    (x : MilnorKDeg K 2) : {i | (D i).tameHom x ≠ 0}.Finite := by
  refine milnorKDeg_mem_of_gen (tameFiniteSupport D) (fun s => ?_) x
  obtain ⟨a, b, hs⟩ : ∃ a b : Kˣ, s.val = [a, b] := by
    rcases s with ⟨l, hl⟩
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · exact absurd hl (by simp)
    · exact absurd hl (by simp)
    · exact ⟨a, b, rfl⟩
    · exact absurd hl (by simp)
  rw [show s = (⟨[a, b], rfl⟩ : MilnorSymbolDeg K 2) from Subtype.ext hs]
  exact h a b

/-- **Every class has a nonzero multiple in the tame kernel.**  Its finitely many nonzero tame
symbols lie in finite groups, so the product of their orders annihilates all of them at once. -/
theorem exists_zsmul_mem_tameKernel [∀ i, Finite (κ i)ˣ] (x : MilnorKDeg K 2)
    (hx : {i | (D i).tameHom x ≠ 0}.Finite) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ tameKernel D := by
  classical
  haveI : ∀ i, Finite (Additive (κ i)ˣ) := fun i => Finite.of_equiv _ Additive.ofMul
  set N : ℕ := ∏ i ∈ hx.toFinset, addOrderOf ((D i).tameHom x) with hN
  have hNpos : 0 < N := by
    refine Finset.prod_pos fun i _ => ?_
    exact addOrderOf_pos _
  refine ⟨(N : ℤ), Int.natCast_ne_zero.2 hNpos.ne', ?_⟩
  rw [mem_tameKernel_iff]
  intro i
  rw [map_zsmul, natCast_zsmul]
  by_cases hi : (D i).tameHom x = 0
  · rw [hi, smul_zero]
  · have hmem : i ∈ hx.toFinset := hx.mem_toFinset.2 hi
    refine (addOrderOf_dvd_iff_nsmul_eq_zero).1 ?_
    exact hN ▸ Finset.dvd_prod_of_mem _ hmem

/-- **Torsion of the tame kernel forces torsion of `K_2^M`.**  This is the elementary half of the
statement that the degree-two Milnor `K`-group of a number field is torsion: what it leaves open is
exactly the finiteness of the tame kernel. -/
theorem milnorKDegTwo_torsion_of_tameKernel_torsion [∀ i, Finite (κ i)ˣ]
    (hfin : ∀ x : MilnorKDeg K 2, {i | (D i).tameHom x ≠ 0}.Finite)
    (htame : ∀ y ∈ tameKernel D, y ∈ torsionAddSubgroup (MilnorKDeg K 2))
    (x : MilnorKDeg K 2) : x ∈ torsionAddSubgroup (MilnorKDeg K 2) := by
  obtain ⟨n, hn, hmem⟩ := exists_zsmul_mem_tameKernel D x (hfin x)
  obtain ⟨m, hm, hzero⟩ := htame _ hmem
  refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
  rw [mul_smul]
  exact hzero

end TameKernel

end GaloisForLFunctions.HTGeometry
