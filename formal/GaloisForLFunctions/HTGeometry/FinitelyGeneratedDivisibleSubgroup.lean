import GaloisForLFunctions.HTGeometry.DivisibilityFirewall
import GaloisForLFunctions.Bottcher.MonodromyObstruction

/-!
# Divisible subgroups of finitely generated abelian groups

A finitely generated abelian group has no nonzero divisible subgroup.  This is the exact
finite-generation step that breaks the finite-coefficient divisibility firewall in applications to
Moore reciprocity and tame kernels.
-/

namespace GaloisForLFunctions.HTGeometry

open DirectSum

/-- A finitely generated abelian group on which every positive multiplication map is surjective is
zero. -/
theorem eq_zero_of_fg_of_nsmul_surjective
    {A : Type*} [AddCommGroup A] [AddGroup.FG A]
    (hdiv : ∀ n : ℕ, 0 < n → ∀ x : A, ∃ y : A, n • y = x) :
    ∀ x : A, x = 0 := by
  have htor : AddMonoid.IsTorsion A := by
    by_contra hntor
    obtain ⟨ψ, hψ⟩ := exists_zmod_surjection_of_not_isTorsion hntor 2
    have hzero : ∀ x : A, ψ x = 0 :=
      Bottcher.addMonoidHom_eq_zero_of_nsmulDivisible_finite_codomain ψ hdiv
    obtain ⟨x, hx⟩ := hψ 1
    have hone : (1 : ZMod 2) = 0 := hx.symm.trans (hzero x)
    exact one_ne_zero hone
  letI : Finite A := AddCommGroup.finite_of_fg_torsion A htor
  intro x
  have hcard : 0 < Nat.card A := Nat.card_pos
  obtain ⟨y, hy⟩ := hdiv (Nat.card A) hcard x
  rw [← hy]
  exact card_nsmul_eq_zero'

/-- A finitely generated divisible abelian group is subsingleton. -/
theorem subsingleton_of_fg_of_nsmul_surjective
    {A : Type*} [AddCommGroup A] [AddGroup.FG A]
    (hdiv : ∀ n : ℕ, 0 < n → ∀ x : A, ∃ y : A, n • y = x) :
    Subsingleton A := by
  constructor
  intro x y
  rw [eq_zero_of_fg_of_nsmul_surjective hdiv x,
    eq_zero_of_fg_of_nsmul_surjective hdiv y]

/-- Every divisible additive subgroup of a finitely generated abelian group is zero. -/
theorem addSubgroup_eq_bot_of_fg_of_nsmulDivisible
    {A : Type*} [AddCommGroup A] [AddGroup.FG A]
    (D : AddSubgroup A)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ x : A, x ∈ D →
      ∃ y : A, y ∈ D ∧ n • y = x) :
    D = ⊥ := by
  letI : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.2 inferInstance
  letI : IsNoetherian ℤ A := inferInstance
  have hsub : (AddSubgroup.toIntSubmodule D).FG := IsNoetherian.noetherian _
  have hDfg : D.FG := by
    exact (Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule D)).1 hsub
  letI : AddGroup.FG D := (AddGroup.fg_iff_addSubgroup_fg D).2 hDfg
  have hdivD : ∀ n : ℕ, 0 < n → ∀ x : D, ∃ y : D, n • y = x := by
    intro n hn x
    obtain ⟨y, hyD, hy⟩ := hdiv n hn x x.2
    exact ⟨⟨y, hyD⟩, Subtype.ext hy⟩
  apply le_antisymm
  · intro x hx
    have hz : (⟨x, hx⟩ : D) = 0 :=
      eq_zero_of_fg_of_nsmul_surjective hdivD ⟨x, hx⟩
    simpa using congrArg Subtype.val hz
  · exact bot_le

/-- A divisible subgroup contained in a finitely generated subgroup is zero; the ambient group
itself need not be finitely generated. -/
theorem addSubgroup_eq_bot_of_le_fg_of_nsmulDivisible
    {A : Type*} [AddCommGroup A]
    (D T : AddSubgroup A) [AddGroup.FG T] (hDT : D ≤ T)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ x : A, x ∈ D →
      ∃ y : A, y ∈ D ∧ n • y = x) :
    D = ⊥ := by
  let E : AddSubgroup T := D.comap T.subtype
  have hdivE : ∀ n : ℕ, 0 < n → ∀ x : T, x ∈ E →
      ∃ y : T, y ∈ E ∧ n • y = x := by
    intro n hn x hx
    obtain ⟨y, hyD, hy⟩ := hdiv n hn x hx
    refine ⟨⟨y, hDT hyD⟩, hyD, ?_⟩
    exact Subtype.ext hy
  have hE : E = ⊥ := addSubgroup_eq_bot_of_fg_of_nsmulDivisible E hdivE
  apply le_antisymm
  · intro x hx
    have hxE : (⟨x, hDT hx⟩ : T) ∈ E := hx
    have hxbot : (⟨x, hDT hx⟩ : T) ∈ (⊥ : AddSubgroup T) := hE ▸ hxE
    have hz : (⟨x, hDT hx⟩ : T) = 0 := hxbot
    simpa using congrArg Subtype.val hz
  · exact bot_le

/-- A direct sum of finite abelian groups is torsion, even when the index type is infinite. -/
theorem directSumFinite_isTorsion
    {ι : Type*} {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    [∀ i, Finite (G i)] : AddMonoid.IsTorsion (⨁ i, G i) := by
  classical
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨1, by simp⟩
  | of i y =>
      exact (DirectSum.of G i).isOfFinAddOrder (isOfFinAddOrder_of_finite y)
  | add x y hx hy => exact hx.add hy

/-- Every homomorphism from a divisible abelian group to a direct sum of finite groups is zero. -/
theorem addMonoidHom_eq_zero_of_nsmulDivisible_directSumFinite
    {A : Type*} [AddCommGroup A]
    {ι : Type*} {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    [∀ i, Finite (G i)]
    (φ : A →+ ⨁ i, G i)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ x : A, ∃ y : A, n • y = x) :
    ∀ x : A, φ x = 0 := by
  intro x
  apply directSumFinite_eq_zero_of_forall_nsmul
  intro n hn
  obtain ⟨y, hy⟩ := hdiv n (Nat.pos_of_ne_zero hn) x
  refine ⟨φ y, ?_⟩
  rw [← map_nsmul, hy]

/-- Every divisible subgroup lies in the kernel of a homomorphism to a direct sum of finite
groups. -/
theorem addSubgroup_le_ker_of_nsmulDivisible_directSumFinite
    {A : Type*} [AddCommGroup A]
    {ι : Type*} {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    [∀ i, Finite (G i)]
    (D : AddSubgroup A) (φ : A →+ ⨁ i, G i)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ x : A, x ∈ D →
      ∃ y : A, y ∈ D ∧ n • y = x) :
    D ≤ φ.ker := by
  intro x hx
  apply directSumFinite_eq_zero_of_forall_nsmul
  intro n hn
  obtain ⟨y, _hyD, hy⟩ := hdiv n (Nat.pos_of_ne_zero hn) x hx
  refine ⟨φ y, ?_⟩
  rw [← map_nsmul, hy]

/-- Moore-style assembly: a finitely generated abelian group mapping to a direct sum of finite
groups is torsion when its kernel is divisible. -/
theorem isTorsion_of_fg_of_ker_nsmulDivisible_directSumFinite
    {A : Type*} [AddCommGroup A] [AddGroup.FG A]
    {ι : Type*} {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    [∀ i, Finite (G i)]
    (φ : A →+ ⨁ i, G i)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ x : A, x ∈ φ.ker →
      ∃ y : A, y ∈ φ.ker ∧ n • y = x) :
    AddMonoid.IsTorsion A := by
  have hker : φ.ker = ⊥ :=
    addSubgroup_eq_bot_of_fg_of_nsmulDivisible φ.ker hdiv
  have hinj : Function.Injective φ := (φ.ker_eq_bot_iff).mp hker
  intro x
  obtain ⟨n, hn, hzero⟩ :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mp (directSumFinite_isTorsion (φ x))
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨n, hn, hinj ?_⟩
  rw [map_nsmul, hzero, map_zero]

/-- Moore-style assembly in its tame-kernel form: the whole source is torsion when the divisible
kernel lies inside a finitely generated subgroup.  No finite-generation premise is placed on the
ambient source. -/
theorem isTorsion_of_ker_le_fg_of_ker_nsmulDivisible_directSumFinite
    {A : Type*} [AddCommGroup A]
    {ι : Type*} {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    [∀ i, Finite (G i)]
    (φ : A →+ ⨁ i, G i) (T : AddSubgroup A) [AddGroup.FG T]
    (hkerT : φ.ker ≤ T)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ x : A, x ∈ φ.ker →
      ∃ y : A, y ∈ φ.ker ∧ n • y = x) :
    AddMonoid.IsTorsion A := by
  have hker : φ.ker = ⊥ :=
    addSubgroup_eq_bot_of_le_fg_of_nsmulDivisible φ.ker T hkerT hdiv
  have hinj : Function.Injective φ := (φ.ker_eq_bot_iff).mp hker
  intro x
  obtain ⟨n, hn, hzero⟩ :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mp (directSumFinite_isTorsion (φ x))
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨n, hn, hinj ?_⟩
  rw [map_nsmul, hzero, map_zero]

end GaloisForLFunctions.HTGeometry
