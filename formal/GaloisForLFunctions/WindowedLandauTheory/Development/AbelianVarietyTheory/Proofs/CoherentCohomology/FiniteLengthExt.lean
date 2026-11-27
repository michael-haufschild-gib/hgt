import GaloisForLFunctions.HTGeometry.RegularLocalDomain
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! Ext into a regular local ring for modules of finite length. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing

namespace GlobalTheory.FiniteLengthComplex

variable {R : Type} [CommRing R]

/-- Change the first argument of Ext along an isomorphism of modules. -/
noncomputable def extCongrLeft {X X' : ModuleCat.{0} R} (e : X ≅ X') (Y : ModuleCat.{0} R) (n : ℕ) :
    Abelian.Ext.{0} X' Y n ≃ₗ[R] Abelian.Ext.{0} X Y n :=
  LinearEquiv.ofLinear ((Ext.mk₀ e.hom).precompOfLinear R Y (zero_add n))
    ((Ext.mk₀ e.inv).precompOfLinear R Y (zero_add n))
    (by ext x; simp) (by ext x; simp)

private theorem subsingleton_ext_of_isZero_left {X : ModuleCat.{0} R} (h : IsZero X) (Y : ModuleCat.{0} R)
    (n : ℕ) : Subsingleton (Abelian.Ext.{0} X Y n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.mk₀_id_comp x, h.eq_zero_of_src (𝟙 X), Ext.mk₀_zero, Ext.zero_comp]

private theorem shortExact_submodule {M : Type} [AddCommGroup M] [Module R M] (N : Submodule R M) :
    (ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ
      (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ N) N.subtype_injective
    N.mkQ_surjective

private theorem nonempty_iso_residue [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] :
    Nonempty (ModuleCat.of R M ≅ ModuleCat.of R (R ⧸ maximalIdeal R)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R M›
  obtain rfl := eq_maximalIdeal hI
  exact ⟨e.toModuleIso⟩

/-- A composition series reduces Ext vanishing to the residue field. -/
theorem subsingleton_ext_of_isFiniteLength [IsLocalRing R] (Y : ModuleCat.{0} R) (n : ℕ)
    (hk : Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y n))
    (M : Type) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Subsingleton (Abelian.Ext.{0} (ModuleCat.of R M) Y n) := by
  induction hM with
  | of_subsingleton =>
    exact subsingleton_ext_of_isZero_left (ModuleCat.isZero_of_subsingleton _) Y n
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨e⟩ := nonempty_iso_residue (R := R) (M ⧸ N)
    have h3 := (extCongrLeft e Y n).symm.toEquiv.subsingleton
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₂ (shortExact_submodule N) Y x
      (@Subsingleton.elim _ ih _ _)
    rw [@Subsingleton.elim _ h3 y 0]
    exact Ext.comp_zero _ _ _ _ _

/-- If residue-field Ext is concentrated in one degree, its length in that
degree is additive across every composition series. -/
theorem length_ext_of_isFiniteLength [IsLocalRing R] (Y : ModuleCat.{0} R) (g : ℕ)
    (hk : ∀ n, n ≠ g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y n))
    (M : Type) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Module.length R (Abelian.Ext.{0} (ModuleCat.of R M) Y g) = Module.length R M *
      Module.length R (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y g) := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
    have := subsingleton_ext_of_isZero_left
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R M)) Y g
    rw [Module.length_eq_zero, Module.length_eq_zero (M := M), zero_mul]
  | @of_simple_quotient M _ _ N _ hN ih =>
    obtain ⟨e⟩ := nonempty_iso_residue (R := R) (M ⧸ N)
    have hS := shortExact_submodule N
    rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N), Module.length_eq_one R (M ⧸ N), add_mul, one_mul, ← ih,
      (extCongrLeft e Y g).length_eq, add_comm]
    refine Module.length_eq_add_of_exact
      ((Ext.mk₀ (ModuleCat.ofHom N.mkQ)).precompOfLinear R Y (zero_add g))
      ((Ext.mk₀ (ModuleCat.ofHom N.subtype)).precompOfLinear R Y (zero_add g)) ?_ ?_ ?_
    · cases g with
      | zero =>
        have := hS.epi_g
        exact Ext.precomp_mk₀_injective_of_epi Y (ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ
          (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero).g
      | succ g =>
        rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y x hx (add_comm 1 g)
        rw [@Subsingleton.elim _ (subsingleton_ext_of_isFiniteLength Y g (hk g (by omega)) N hN) y 0]
        exact Ext.comp_zero _ _ _ _ _
    · intro x
      have := hk (g + 1) (by omega)
      have h3 := (extCongrLeft e Y (g + 1)).symm.toEquiv.subsingleton
      exact Ext.contravariant_sequence_exact₁ hS Y x (add_comm 1 g) (@Subsingleton.elim _ h3 _ _)
    · intro x
      refine ⟨fun hx => Ext.contravariant_sequence_exact₂ hS Y x hx, ?_⟩
      rintro ⟨y, rfl⟩
      change (Ext.mk₀ _).comp ((Ext.mk₀ _).comp y (zero_add g)) (zero_add g) = 0
      rw [Ext.mk₀_comp_mk₀_assoc, ← ModuleCat.ofHom_comp,
        (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero]
      simp

/-- Vanishing against the coefficient ring implies vanishing against finite free modules. -/
theorem subsingleton_ext_free (X : ModuleCat.{0} R) (n : ℕ)
    (h : Subsingleton (Abelian.Ext.{0} X (ModuleCat.of R R) n))
    (F : ModuleCat.{0} R) [Module.Free R F] [Module.Finite R F] :
    Subsingleton (Abelian.Ext.{0} X F n) := by
  let b := Module.Free.chooseBasis R F
  have hid : 𝟙 F = ∑ i, (ModuleCat.ofHom (b.coord i) : F ⟶ ModuleCat.of R R) ≫
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R F (b i)) : ModuleCat.of R R ⟶ F) := by
    ext x
    simp [ModuleCat.hom_sum, b.sum_repr x]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.comp_mk₀_id x, hid, Ext.mk₀_sum, Ext.comp_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    Subsingleton.elim (x.comp _ _) 0, Ext.zero_comp]

/-- Ext from the residue field to a regular local ring is concentrated in
the length of a regular sequence generating the maximal ideal. -/
theorem subsingleton_ext_residue [IsRegularLocalRing R] (g : ℕ) (hg : ringKrullDim R = g)
    (n : ℕ) (hn : n ≠ g) :
    Subsingleton (Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) n) := by
  obtain ⟨xs, hlen, hgen, hreg⟩ :=
    GaloisForLFunctions.HTGeometry.exists_isRingRegularSeq_maximalIdeal R
  have hreg' := (GaloisForLFunctions.HTGeometry.isRingRegularSeq_iff_isRegular xs).mp hreg
  have hlen' : xs.length = g := by
    have hdim := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hg, ← hlen] at hdim
    exact_mod_cast hdim
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · refine ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) _ ?_ _ ?_ xs ?_ hreg'
      n (hlen' ▸ hlt)
    · rw [Module.support_eq_zeroLocus]
      change PrimeSpectrum.zeroLocus (Module.annihilator R (R ⧸ maximalIdeal R) : Set R) ⊆ _
      rw [Ideal.annihilator_quotient]
    · rw [smul_eq_mul, Ideal.mul_top]
      exact (maximalIdeal.isMaximal R).ne_top.lt_top
    · intro r hr
      rw [← hgen]
      exact Ideal.subset_span hr
  · have key := ModuleCat.projectiveDimension_quotient_eq_length.{0} xs hreg'
    rw [projectiveDimension_eq_of_iso (Shrink.linearEquiv R _).toModuleIso, hgen, hlen'] at key
    have : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) g :=
      (projectiveDimension_le_iff _ g).mp key.le
    exact HasProjectiveDimensionLT.subsingleton _ (g + 1) n hgt _

end GlobalTheory.FiniteLengthComplex
