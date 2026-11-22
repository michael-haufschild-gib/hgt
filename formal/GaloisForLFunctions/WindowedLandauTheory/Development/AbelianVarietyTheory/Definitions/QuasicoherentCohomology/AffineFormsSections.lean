import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineFormsLocalization
import Mathlib.Tactic.Abel
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Sheafification leaves relative differential forms unchanged on affine opens. -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace GlobalTheory.SchemeCohomology

private theorem surjective_of_local_denominators {A M N : Type*} [CommRing A]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (θ : M →ₗ[A] N) (Z : A → Submodule A N)
    (hcompat : ∀ g h, Z g ≤ Z (g * h))
    (hunit : ∀ g (m : ℕ) n, g ^ m • n ∈ Z g → n ∈ Z g)
    (hsep : ∀ S : Set A, Ideal.span S = ⊤ → ∀ n, (∀ g ∈ S, n ∈ Z g) → n = 0)
    (hzero : ∀ g x, θ x ∈ Z g → ∃ m : ℕ, g ^ m • x = 0)
    (hcover : ∀ n, Ideal.span {g | ∃ (m : ℕ) (x : M), g ^ m • n - θ x ∈ Z g} = ⊤) :
    Function.Surjective θ := by
  intro n
  obtain ⟨T, hT, hspan⟩ := (Ideal.span_eq_top_iff_finite _).1 (hcover n)
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (LinearMap.range θ) _ (hcover n) n ?_
  rintro ⟨g, m, x, hx⟩
  -- Compare the local numerators after clearing denominators on each overlap.
  have overlap (i : T) : ∃ r : ℕ, g ^ r • (g ^ m • n - θ x) ∈ Z i := by
    obtain ⟨m', x', hx'⟩ := hT i.prop
    have eq : θ (g ^ m • x' - i.val ^ m' • x) =
        i.val ^ m' • (g ^ m • n - θ x) - g ^ m • (i.val ^ m' • n - θ x') := by
      simp only [map_sub, map_smul, smul_sub, smul_comm (i.val ^ m') (g ^ m)]
      abel
    have hz : θ (g ^ m • x' - i.val ^ m' • x) ∈ Z (i.val * g) := by
      rw [eq]
      exact sub_mem (Submodule.smul_mem _ _ (mul_comm g i.val ▸ hcompat g i.val hx))
        (Submodule.smul_mem _ _ (hcompat i.val g hx'))
    obtain ⟨r, hr⟩ := hzero _ _ hz
    have hr' := congrArg θ hr
    rw [map_smul, eq, map_zero, smul_sub, sub_eq_zero] at hr'
    refine ⟨r, hunit i.val (r + m') _ ?_⟩
    have e : i.val ^ (r + m') • g ^ r • (g ^ m • n - θ x) =
        (i.val * g) ^ r • i.val ^ m' • (g ^ m • n - θ x) := by
      rw [smul_smul, smul_smul, pow_add, mul_pow]
      exact congrArg (fun a : A => a • (g ^ m • n - θ x))
        (mul_right_comm (i.val ^ r) (i.val ^ m') (g ^ r))
    rw [e, hr']
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hx')
  choose r hr using overlap
  let R := Finset.univ.sup r
  have h0 : g ^ R • (g ^ m • n - θ x) = 0 := hsep T hspan _ fun i hi => by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := r) (Finset.mem_univ ⟨i, hi⟩))
    rw [show R = c + r ⟨i, hi⟩ from hc, pow_add, mul_smul]
    exact Submodule.smul_mem _ _ (hr ⟨i, hi⟩)
  rw [smul_sub, sub_eq_zero] at h0
  refine ⟨R + m, g ^ R • x, ?_⟩
  rw [map_smul, ← h0, pow_add, mul_smul]

universe u

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (s : X ⟶ Spec (CommRingCat.of k))

private instance sectionRingModule (F : X.Modules) (U : X.Opens) :
    Module (SectionRing s U) Γ(F, U) :=
  inferInstanceAs (Module Γ(X, U) Γ(F, U))

variable (n : ℕ)

/-- The sheafification map on sections of the presheaf of differential forms. -/
def formsOnToSections (U : X.Opens) :
    FormsOn s U n →ₗ[SectionRing s U] Γ(relativeForms s n, U) :=
  ((toRelativeForms s n).app (op U)).hom

theorem formsOnToSections_res {U V : X.Opens} (i : V ⟶ U) (x : FormsOn s U n) :
    (relativeForms s n).presheaf.map i.op (formsOnToSections s n U x) =
      formsOnToSections s n V (ExteriorDifferentials.map (sectionRes s i) n x) :=
  (PresheafOfModules.naturality_apply (toRelativeForms s n) i.op x).symm

private theorem exists_restriction_zero {U : X.Opens} {x : FormsOn s U n}
    (hx : formsOnToSections s n U x = 0) {p : X} (hp : p ∈ U) :
    ∃ (V : X.Opens) (i : V ⟶ U), p ∈ V ∧ ExteriorDifferentials.map (sectionRes s i) n x = 0 := by
  have h := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) (formsPresheaf s n).presheaf) (X := op U) x 0
    (by rw [map_zero]; exact hx)
  obtain ⟨V, i, hi, hpV⟩ := h p hp
  exact ⟨V, i, hpV, hi.trans (map_zero _)⟩

private theorem exists_local_lift {U : X.Opens} (y : Γ(relativeForms s n, U))
    {p : X} (hp : p ∈ U) :
    ∃ (V : X.Opens) (i : V ⟶ U), p ∈ V ∧ ∃ x : FormsOn s V n,
      formsOnToSections s n V x = (relativeForms s n).presheaf.map i.op y := by
  have h := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) (formsPresheaf s n).presheaf) (U := op U) y
  obtain ⟨V, i, ⟨x, hx⟩, hpV⟩ := h p hp
  exact ⟨V, i, hpV, x, hx⟩

private theorem span_eq_top_of_basicOpen_cover {U : X.Opens} (hU : IsAffineOpen U)
    {T : Set (SectionRing s U)} (h : ∀ p ∈ U, ∃ g ∈ T, p ∈ X.basicOpen (U := U) g) :
    Ideal.span T = ⊤ :=
  (hU.self_le_iSup_basicOpen_iff (s := T)).1 fun p hp =>
    have ⟨g, hg, hp'⟩ := h p hp
    Opens.mem_iSup.2 ⟨⟨g, hg⟩, hp'⟩

private theorem formsOnToSections_injective {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (formsOnToSections s n U) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule (SectionRing s U) _)
    {g | ∃ m : ℕ, g ^ m • x = 0} (span_eq_top_of_basicOpen_cover s hU ?_) x fun g => g.2
  intro p hp
  obtain ⟨V, i, hpV, hzero⟩ := exists_restriction_zero s n hx hp
  obtain ⟨g, hg, hpg⟩ := hU.exists_basicOpen_le ⟨p, hpV⟩ hp
  refine ⟨g, (formsOn_basicOpen hU g n).2 x ?_, hpg⟩
  have hi : (homOfLE (X.basicOpen_le (U := U) g) : X.basicOpen g ⟶ U) = homOfLE hg ≫ i :=
    Subsingleton.elim _ _
  change ExteriorDifferentials.map (sectionRes s (homOfLE (X.basicOpen_le (U := U) g))) n x = 0
  rw [hi, sectionRes_comp, ExteriorDifferentials.map_comp, hzero, map_zero]

private def relativeFormsResKer {U V : X.Opens} (i : V ⟶ U) :
    Submodule (SectionRing s U) Γ(relativeForms s n, U) := by
  letI : Module (SectionRing s U) Γ(relativeForms s n, V) :=
    Module.compHom _ (sectionRes s i).toRingHom
  let L : Γ(relativeForms s n, U) →ₗ[SectionRing s U] Γ(relativeForms s n, V) :=
    { ((relativeForms s n).presheaf.map i.op).hom with
      map_smul' r y := (relativeForms s n).map_smul i r y }
  exact L.ker

private theorem formsOnToSections_surjective {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective (formsOnToSections s n U) := by
  let M := relativeForms s n
  let basic (g : SectionRing s U) : X.basicOpen g ⟶ U := homOfLE (X.basicOpen_le g)
  let Z (g : SectionRing s U) := relativeFormsResKer s n (basic g)
  have hZ (g : SectionRing s U) (y : Γ(M, U)) :
      y ∈ Z g ↔ M.presheaf.map (basic g).op y = 0 := Iff.rfl
  refine surjective_of_local_denominators _ Z ?_ ?_ ?_ ?_ ?_
  · intro g h y hy
    have hg : X.basicOpen (U := U) (g * h) ≤ X.basicOpen g :=
      (X.basicOpen_mul g h).trans_le inf_le_left
    have e : basic (g * h) = homOfLE hg ≫ basic g := Subsingleton.elim _ _
    rw [hZ, e, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, (hZ _ _).1 hy, map_zero]
  · intro g m y hy
    have hz := (hZ _ _).1 hy
    have hs := M.map_smul (basic g) (show Γ(X, U) from g ^ m) y
    have hp := map_pow (X.presheaf.map (basic g).op).hom (show Γ(X, U) from g) m
    have hm : (X.presheaf.map (basic g).op g) ^ m • M.presheaf.map (basic g).op y = 0 :=
      (congrArg (fun a : Γ(X, X.basicOpen g) => a • M.presheaf.map (basic g).op y) hp).symm.trans
        (hs.symm.trans hz)
    have hu : IsUnit (X.presheaf.map (basic g).op g) := X.toRingedSpace.isUnit_res_basicOpen g
    exact (hZ _ _).2 (((hu.pow m).smul_eq_zero).1 hm)
  · intro T hT y hy
    exact TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
      (fun g : T => X.basicOpen g.val) U (fun g => basic g.val)
      ((hU.self_le_iSup_basicOpen_iff (s := T)).2 hT) y 0 fun g =>
        ((hZ _ _).1 (hy g.val g.prop)).trans (map_zero _).symm
  · intro g x hx
    rw [hZ, formsOnToSections_res] at hx
    exact (formsOn_basicOpen hU g n).2 x
      ((formsOnToSections_injective s n (hU.basicOpen g)) (hx.trans (map_zero _).symm))
  · intro y
    apply span_eq_top_of_basicOpen_cover s hU
    intro p hp
    obtain ⟨V, i, hpV, x, hx⟩ := exists_local_lift s n y hp
    obtain ⟨g, hg, hpg⟩ := hU.exists_basicOpen_le ⟨p, hpV⟩ hp
    let j : X.basicOpen g ⟶ V := homOfLE hg
    obtain ⟨m, z, hz⟩ := (formsOn_basicOpen hU g n).1 (ExteriorDifferentials.map (sectionRes s j) n x)
    have e : basic g = j ≫ i := Subsingleton.elim _ _
    refine ⟨g, ⟨m, z, (hZ _ _).2 ?_⟩, hpg⟩
    rw [map_sub, sub_eq_zero]
    have hpow := map_pow (X.presheaf.map (basic g).op).hom (show Γ(X, U) from g) m
    have hres : M.presheaf.map (basic g).op y = M.presheaf.map j.op (M.presheaf.map i.op y) := by
      rw [e, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    have hleft := formsOnToSections_res s n j x
    rw [hx] at hleft
    have hz' : (sectionRes s (basic g) g) ^ m • ExteriorDifferentials.map (sectionRes s j) n x =
        ExteriorDifferentials.map (sectionRes s (basic g)) n z := hz
    have hright := formsOnToSections_res s n (basic g) z
    rw [← hz'] at hright
    exact (M.map_smul (basic g) (show Γ(X, U) from g ^ m) y).trans
      ((congrArg₂ (fun (a : Γ(X, X.basicOpen g)) (b : Γ(M, X.basicOpen g)) => a • b)
        hpow (hres.trans hleft)).trans
        (((formsOnToSections s n (X.basicOpen g)).map_smul _ _).symm.trans hright.symm))

/-- Sections of the sheaf on an affine open are the forms of its section ring. -/
def affineFormsSections {U : X.Opens} (hU : IsAffineOpen U) :
    FormsOn s U n ≃ₗ[SectionRing s U] Γ(relativeForms s n, U) :=
  LinearEquiv.ofBijective (formsOnToSections s n U)
    ⟨formsOnToSections_injective s n hU, formsOnToSections_surjective s n hU⟩

@[simp] theorem affineFormsSections_apply {U : X.Opens} (hU : IsAffineOpen U) (x : FormsOn s U n) :
    affineFormsSections s n hU x = formsOnToSections s n U x := rfl

end GlobalTheory.SchemeCohomology
