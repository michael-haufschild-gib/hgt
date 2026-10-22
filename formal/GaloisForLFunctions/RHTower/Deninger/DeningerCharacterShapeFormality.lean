import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Set.UnionLift

/-!
# The unit space of a field and its lattice filtration

The units of a field modulo its roots of unity form a torsion-free abelian group.  Its finitely
generated subgroups are therefore free, they are directed under inclusion, and they exhaust the
whole group: the unit space is the filtered colimit of its lattices.

Two consequences of that filtration are recorded here.  A compatible family of homomorphisms on
the lattices glues to a single homomorphism on the unit space, and two homomorphisms agreeing on
every lattice are equal — the character group of the unit space is the inverse limit of the
character groups of its lattices.  And the exterior algebra of the unit space is the union of the
exterior algebras of its lattices, so forming exterior algebras commutes with the filtration.

The `n`-th power map of the units acts on the unit space as multiplication by `n`, which is the
Frobenius equivariance of the whole picture.

* `DeningerUnitLattice`, `deningerUnitSpace_isTorsionFree` : the unit space is torsion-free.
* `deningerUnitClass_zpow` : the `n`-th power map is multiplication by `n`.
* `deningerLatticeFree` : finitely generated subgroups of a torsion-free group are free.
* `deningerFGSubmodule_directed`, `deningerFGSubmodule_iSup_top` : the lattices are filtered and
  exhaust.
* `deningerLatticeLift`, `deningerLatticeHom_ext` : homomorphisms out of the unit space are the
  inverse limit of homomorphisms out of its lattices.
* `deningerExterior_iSup_adjoin` : exterior algebras commute with the filtration.
-/

namespace RHTower

section UnitSpace

variable (F : Type*) [Field F]

/-- **The unit space of a field**: the units modulo their torsion, that is modulo the roots of
unity. -/
abbrev DeningerUnitLattice : Type _ :=
  (Additive Fˣ) ⧸ Submodule.torsion ℤ (Additive Fˣ)

/-- **The unit space is torsion-free.**  The torsion subgroup of the units is exactly the group of
roots of unity, and a quotient by the full torsion is torsion-free. -/
theorem deningerUnitSpace_isTorsionFree :
    Module.IsTorsionFree ℤ (DeningerUnitLattice F) :=
  Submodule.QuotientTorsion.instIsTorsionFree

variable {F}

/-- The class of a unit in the unit space. -/
def deningerUnitClass (x : Fˣ) : DeningerUnitLattice F :=
  Submodule.Quotient.mk (Additive.ofMul x)

theorem deningerUnitClass_surjective : Function.Surjective (deningerUnitClass (F := F)) := by
  intro y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Additive.toMul a, rfl⟩

/-- **The torsion of the units is the set of roots of unity.** -/
theorem deningerTorsion_iff_isOfFinOrder (x : Fˣ) :
    Additive.ofMul x ∈ Submodule.torsion ℤ (Additive Fˣ) ↔ IsOfFinOrder x := by
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨a, ha⟩
    have hne : (a : ℤ) ≠ 0 := nonZeroDivisors.ne_zero a.2
    have hx : x ^ (a : ℤ) = 1 := ha
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · refine isOfFinOrder_iff_pow_eq_one.mpr ⟨(-a : ℤ).toNat, ?_, ?_⟩
      · omega
      · have : x ^ (-(a : ℤ)) = 1 := by rw [zpow_neg, hx, inv_one]
        rwa [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
    · refine isOfFinOrder_iff_pow_eq_one.mpr ⟨(a : ℤ).toNat, ?_, ?_⟩
      · omega
      · rwa [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  · intro hfin
    obtain ⟨n, hn, hx⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    show x ^ ((n : ℤ)) = 1
    rwa [zpow_natCast]

theorem deningerUnitClass_eq_zero_iff (x : Fˣ) :
    deningerUnitClass x = 0 ↔ IsOfFinOrder x := by
  rw [deningerUnitClass, Submodule.Quotient.mk_eq_zero, deningerTorsion_iff_isOfFinOrder]

/-- **Frobenius equivariance.**  Raising a unit to the `n`-th power is multiplication by `n` on the
unit space. -/
theorem deningerUnitClass_zpow (x : Fˣ) (n : ℤ) :
    deningerUnitClass (x ^ n) = n • deningerUnitClass x := rfl

theorem deningerUnitClass_mul (x y : Fˣ) :
    deningerUnitClass (x * y) = deningerUnitClass x + deningerUnitClass y := rfl

end UnitSpace

section Lattices

variable {M : Type*} [AddCommGroup M]

/-- **A finitely generated subgroup of a torsion-free abelian group is free.** -/
theorem deningerLatticeFree [Module.IsTorsionFree ℤ M] {N : Submodule ℤ M} (hN : N.FG) :
    Module.Free ℤ N := by
  haveI : Module.Finite ℤ N := Module.Finite.iff_fg.mpr hN
  haveI : Module.IsTorsionFree ℤ N :=
    Function.Injective.moduleIsTorsionFree N.subtype (Submodule.injective_subtype N)
      (fun _ _ => rfl)
  exact Module.free_of_finite_type_torsion_free'

/-- The lattices of a module: its finitely generated submodules. -/
abbrev DeningerLattice (M : Type*) [AddCommGroup M] : Type _ :=
  {N : Submodule ℤ M // N.FG}

instance : Nonempty (DeningerLattice M) := ⟨⟨⊥, Submodule.fg_bot⟩⟩

/-- **The lattices are directed under inclusion.** -/
theorem deningerFGSubmodule_directed :
    Directed (· ≤ ·) (fun N : DeningerLattice M => (N : Submodule ℤ M)) := by
  intro N₁ N₂
  exact ⟨⟨(N₁ : Submodule ℤ M) ⊔ (N₂ : Submodule ℤ M), N₁.2.sup N₂.2⟩,
    le_sup_left, le_sup_right⟩

/-- **The lattices exhaust the module.** -/
theorem deningerFGSubmodule_iSup_top :
    ⨆ N : DeningerLattice M, (N : Submodule ℤ M) = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  refine Submodule.mem_iSup_of_directed _ deningerFGSubmodule_directed |>.mpr ?_
  exact ⟨⟨Submodule.span ℤ {x}, Submodule.fg_span_singleton x⟩,
    Submodule.mem_span_singleton_self x⟩

end Lattices

section LatticeLift

variable {M A : Type*} [AddCommGroup M] [AddCommGroup A]

/-- Every element lies in some member of a directed exhausting family. -/
theorem deningerLattice_exists_mem {ι : Type*} [Nonempty ι] (W : ι → Submodule ℤ M)
    (hdir : Directed (· ≤ ·) W) (htop : ⨆ i, W i = ⊤) (x : M) : ∃ i, x ∈ W i := by
  have hx : x ∈ ⨆ i, W i := htop ▸ Submodule.mem_top
  exact (Submodule.mem_iSup_of_directed W hdir).mp hx

/-- A compatible family of homomorphisms takes the same value on a common element. -/
theorem deningerLattice_compat {ι : Type*} (W : ι → Submodule ℤ M)
    (hdir : Directed (· ≤ ·) W) (g : ∀ i, W i →ₗ[ℤ] A)
    (hg : ∀ i j (h : W i ≤ W j) (x : W i), g j (Submodule.inclusion h x) = g i x)
    (i j : ι) (x : M) (hxi : x ∈ W i) (hxj : x ∈ W j) :
    g i ⟨x, hxi⟩ = g j ⟨x, hxj⟩ := by
  obtain ⟨k, hik, hjk⟩ := hdir i j
  rw [← hg i k hik ⟨x, hxi⟩, ← hg j k hjk ⟨x, hxj⟩]
  rfl

/-- The function glued from a compatible family of homomorphisms on a directed exhausting
family of submodules. -/
noncomputable def deningerLatticeFun {ι : Type*} [Nonempty ι] (W : ι → Submodule ℤ M)
    (hdir : Directed (· ≤ ·) W) (htop : ⨆ i, W i = ⊤) (g : ∀ i, W i →ₗ[ℤ] A)
    (hg : ∀ i j (h : W i ≤ W j) (x : W i), g j (Submodule.inclusion h x) = g i x) : M → A :=
  fun x =>
    Set.iUnionLift (fun i => (W i : Set M)) (fun i y => g i ⟨y.1, y.2⟩)
      (fun i j y hyi hyj => deningerLattice_compat W hdir g hg i j y hyi hyj)
      Set.univ
      (fun y _ => Set.mem_iUnion.mpr (deningerLattice_exists_mem W hdir htop y))
      ⟨x, Set.mem_univ x⟩

theorem deningerLatticeFun_apply {ι : Type*} [Nonempty ι] (W : ι → Submodule ℤ M)
    (hdir : Directed (· ≤ ·) W) (htop : ⨆ i, W i = ⊤) (g : ∀ i, W i →ₗ[ℤ] A)
    (hg : ∀ i j (h : W i ≤ W j) (x : W i), g j (Submodule.inclusion h x) = g i x)
    {i : ι} (x : M) (hx : x ∈ W i) :
    deningerLatticeFun W hdir htop g hg x = g i ⟨x, hx⟩ :=
  Set.iUnionLift_mk (i := i) ⟨x, hx⟩ (Set.mem_univ x)

/-- **A compatible family of homomorphisms on the lattices glues.**  This is the surjectivity half
of the statement that homomorphisms out of the filtered colimit are the inverse limit of the
homomorphisms out of its members. -/
noncomputable def deningerLatticeLift {ι : Type*} [Nonempty ι] (W : ι → Submodule ℤ M)
    (hdir : Directed (· ≤ ·) W) (htop : ⨆ i, W i = ⊤) (g : ∀ i, W i →ₗ[ℤ] A)
    (hg : ∀ i j (h : W i ≤ W j) (x : W i), g j (Submodule.inclusion h x) = g i x) :
    M →ₗ[ℤ] A where
  toFun := deningerLatticeFun W hdir htop g hg
  map_add' x y := by
    obtain ⟨i, hi⟩ := deningerLattice_exists_mem W hdir htop x
    obtain ⟨j, hj⟩ := deningerLattice_exists_mem W hdir htop y
    obtain ⟨k, hik, hjk⟩ := hdir i j
    have hxk : x ∈ W k := hik hi
    have hyk : y ∈ W k := hjk hj
    rw [deningerLatticeFun_apply W hdir htop g hg x hxk,
      deningerLatticeFun_apply W hdir htop g hg y hyk,
      deningerLatticeFun_apply W hdir htop g hg (x + y) (Submodule.add_mem _ hxk hyk)]
    exact map_add (g k) ⟨x, hxk⟩ ⟨y, hyk⟩
  map_smul' c x := by
    obtain ⟨i, hi⟩ := deningerLattice_exists_mem W hdir htop x
    rw [deningerLatticeFun_apply W hdir htop g hg x hi,
      deningerLatticeFun_apply W hdir htop g hg (c • x) (Submodule.smul_mem _ c hi)]
    exact map_smul (g i) c ⟨x, hi⟩

theorem deningerLatticeLift_apply {ι : Type*} [Nonempty ι] (W : ι → Submodule ℤ M)
    (hdir : Directed (· ≤ ·) W) (htop : ⨆ i, W i = ⊤) (g : ∀ i, W i →ₗ[ℤ] A)
    (hg : ∀ i j (h : W i ≤ W j) (x : W i), g j (Submodule.inclusion h x) = g i x)
    {i : ι} (x : M) (hx : x ∈ W i) :
    deningerLatticeLift W hdir htop g hg x = g i ⟨x, hx⟩ :=
  deningerLatticeFun_apply W hdir htop g hg x hx

/-- **Homomorphisms are determined by their restrictions to the lattices.**  This is the
injectivity half of the inverse-limit statement. -/
theorem deningerLatticeHom_ext {ι : Type*} [Nonempty ι] (W : ι → Submodule ℤ M)
    (hdir : Directed (· ≤ ·) W) (htop : ⨆ i, W i = ⊤) {f₁ f₂ : M →ₗ[ℤ] A}
    (h : ∀ (i : ι) (x : W i), f₁ (x : M) = f₂ (x : M)) : f₁ = f₂ := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨i, hi⟩ := deningerLattice_exists_mem W hdir htop x
  exact h i ⟨x, hi⟩

end LatticeLift

section ExteriorColimit

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Exterior algebras commute with a filtered exhausting family.**  The subalgebras generated by
the generators of the members exhaust the exterior algebra, because every generator already lies in
one member. -/
theorem deningerExterior_iSup_adjoin {ι : Type*} [Nonempty ι] (W : ι → Submodule R M)
    (hdir : Directed (· ≤ ·) W) (htop : ⨆ i, W i = ⊤) :
    ⨆ i, Algebra.adjoin R (ExteriorAlgebra.ι R '' (W i : Set M)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← CliffordAlgebra.adjoin_range_ι (Q := (0 : QuadraticForm R M)), Algebra.adjoin_le_iff]
  rintro _ ⟨m, rfl⟩
  have hm : m ∈ ⨆ i, W i := htop ▸ Submodule.mem_top
  obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed W hdir).mp hm
  have hmem : ExteriorAlgebra.ι R m ∈ Algebra.adjoin R (ExteriorAlgebra.ι R '' (W i : Set M)) :=
    Algebra.subset_adjoin ⟨m, hi, rfl⟩
  exact (le_iSup (fun i => Algebra.adjoin R (ExteriorAlgebra.ι R '' (W i : Set M))) i) hmem

end ExteriorColimit

section FreeUnitAmalgamation

open scoped TensorProduct

variable {R : Type*} [CommRing R]

/-- **The unit-amalgamated coefficient of the free algebra is the amalgamating algebra.**  This is
the underived shadow of base change along the free-unit equivalence: tensoring an algebra with the
base over itself gives that algebra back. -/
noncomputable def deningerUnitAmalgam (K : Type*) [CommRing K] [Algebra R K] :
    R ⊗[R] K ≃ₐ[R] K :=
  Algebra.TensorProduct.lid R K

/-- **Base change along an equivalence is an equivalence.**  Replacing the unit algebra by an
equivalent one does not change the amalgamated coefficient. -/
noncomputable def deningerBaseChangeCongr {P C K : Type*} [CommRing P] [CommRing C] [CommRing K]
    [Algebra R P] [Algebra R C] [Algebra R K] (e : P ≃ₐ[R] C) :
    P ⊗[R] K ≃ₐ[R] C ⊗[R] K :=
  Algebra.TensorProduct.congr e (AlgEquiv.refl)

end FreeUnitAmalgamation

end RHTower

