import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FiniteFreeApproximation
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FlatCochainCone
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Tactic.TermCongr

/-! Finite projective models of bounded flat complexes with finite cohomology. -/

open CategoryTheory TensorProduct
open scoped TensorProduct

universe u v w

namespace GlobalTheory

section QuasiIso

variable {R : Type u} [Ring R]

theorem shortComplex_quasiIso_iff {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T) :
    ShortComplex.QuasiIso φ ↔
      (∀ y : T.X₂, T.g y = 0 → ∃ (x : S.X₂) (z : T.X₁), S.g x = 0 ∧ T.f z + φ.τ₂ x = y) ∧
      (∀ (x : S.X₂) (z : T.X₁), S.g x = 0 → T.f z = φ.τ₂ x → ∃ w : S.X₁, S.f w = x) := by
  let γ := ShortComplex.leftHomologyMapData φ S.moduleCatLeftHomologyData
    T.moduleCatLeftHomologyData
  let φK : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom := γ.φK.hom
  let φH : (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) →ₗ[R]
    (LinearMap.ker T.g.hom ⧸ LinearMap.range T.moduleCatToCycles) := γ.φH.hom
  have hi : ∀ x, (φK x : T.X₂) = φ.τ₂ x := fun x => congr($(γ.commi).hom x)
  have hπ : ∀ x, φH (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φK x) :=
    fun x => congr($(γ.commπ).hom x)
  rw [γ.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective φH ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun y hy => ?_, fun x z hx hz => ?_⟩
    · obtain ⟨x, hx⟩ := h2 (Submodule.Quotient.mk ⟨y, hy⟩)
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hπ] at hx
      obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).1 hx.symm
      refine ⟨x, z, x.2, ?_⟩
      have : T.f z = y - φK x := congrArg Subtype.val hz
      rw [this, hi, sub_add_cancel]
    · have : φH (Submodule.Quotient.mk ⟨x, hx⟩) = 0 := by
        rw [hπ, Submodule.Quotient.mk_eq_zero]
        exact ⟨z, Subtype.ext (hz.trans (hi ⟨x, hx⟩).symm)⟩
      obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).1
        ((injective_iff_map_eq_zero _).1 h1 _ this)
      exact ⟨w, congrArg Subtype.val hw⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
    · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hπ, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨z, hz⟩ := hx
      obtain ⟨w, hw⟩ := h2 x z x.2 ((congrArg Subtype.val hz).trans (hi x))
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨w, Subtype.ext hw⟩
    · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨x, z, hx, hz⟩ := h1 y y.2
      refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
      rw [hπ]
      symm
      refine (Submodule.Quotient.eq _).2 ⟨z, Subtype.ext ?_⟩
      change T.f z = y - φK ⟨x, hx⟩
      rw [hi, ← hz, add_sub_cancel_right]

theorem cochain_d_d_apply (K : CochainComplex (ModuleCat.{v} R) ℕ) (i j k : ℕ) (x : K.X i) :
    (K.d j k).hom ((K.d i j).hom x) = 0 := congr($(K.d_comp_d i j k).hom x)

theorem cochain_comm_apply {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) (i j : ℕ)
    (x : K.X i) : (C.d i j).hom ((φ.f i).hom x) = (φ.f j).hom ((K.d i j).hom x) :=
  congr($(φ.comm i j).hom x)

theorem quasiIsoAt_zero_iff {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) :
    QuasiIsoAt φ 0 ↔
      (∀ y : C.X 0, (C.d 0 1).hom y = 0 → ∃ x : K.X 0, (K.d 0 1).hom x = 0 ∧ (φ.f 0).hom x = y) ∧
      (∀ x : K.X 0, (K.d 0 1).hom x = 0 → (φ.f 0).hom x = 0 → x = 0) := by
  rw [quasiIsoAt_iff' φ 0 0 1 (by simp) (by simp), shortComplex_quasiIso_iff]
  have hK : ∀ x, (K.d 0 0).hom x = 0 := fun x => by rw [K.shape 0 0 (by simp)]; rfl
  have hC : ∀ x, (C.d 0 0).hom x = 0 := fun x => by rw [C.shape 0 0 (by simp)]; rfl
  change (∀ y : C.X 0, (C.d 0 1).hom y = 0 → ∃ (x : K.X 0) (z : C.X 0), (K.d 0 1).hom x = 0 ∧
    (C.d 0 0).hom z + (φ.f 0).hom x = y) ∧ (∀ (x : K.X 0) (z : C.X 0), (K.d 0 1).hom x = 0 →
      (C.d 0 0).hom z = (φ.f 0).hom x → ∃ w : K.X 0, (K.d 0 0).hom w = x) ↔ _
  simp only [hK, hC, zero_add]
  refine and_congr (forall₂_congr fun y _ => ?_) ⟨fun h x h1 h2 => ?_, fun h x _ h1 h2 => ?_⟩
  · exact ⟨fun ⟨x, _, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, 0, h⟩⟩
  · obtain ⟨_, hw⟩ := h x 0 h1 h2.symm
    exact hw.symm
  · exact ⟨0, (h x h1 h2.symm).symm⟩

theorem quasiIsoAt_succ_iff {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) (p : ℕ) :
    QuasiIsoAt φ (p + 1) ↔
      (∀ y : C.X (p + 1), (C.d (p + 1) (p + 2)).hom y = 0 →
        ∃ (x : K.X (p + 1)) (z : C.X p), (K.d (p + 1) (p + 2)).hom x = 0 ∧
          (C.d p (p + 1)).hom z + (φ.f (p + 1)).hom x = y) ∧
      (∀ (x : K.X (p + 1)) (z : C.X p), (K.d (p + 1) (p + 2)).hom x = 0 →
        (C.d p (p + 1)).hom z = (φ.f (p + 1)).hom x → ∃ w : K.X p, (K.d p (p + 1)).hom w = x) := by
  rw [quasiIsoAt_iff' φ p (p + 1) (p + 2) (by simp) (by simp), shortComplex_quasiIso_iff]
  rfl

theorem quasiIso_iff_coneExact {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) :
    QuasiIso φ ↔ ConeExact (K := fun p => K.X p) (C := fun p => C.X p)
      (fun p => (K.d p (p + 1)).hom) (fun p => (C.d p (p + 1)).hom) (fun p => (φ.f p).hom) := by
  rw [quasiIso_iff]
  constructor
  · intro h
    have h0 := (quasiIsoAt_zero_iff φ).1 (h 0)
    have h1 := fun p => (quasiIsoAt_succ_iff φ p).1 (h (p + 1))
    refine ⟨fun x hx hx' => h0.2 x hx' hx, fun c k hc hk => ?_, fun p c k hc hk => ?_⟩
    · obtain ⟨w, rfl⟩ := (h1 0).2 k c hk hc
      obtain ⟨x, hx, hx'⟩ := h0.1 (c - (φ.f 0).hom w)
        (by rw [map_sub, cochain_comm_apply, sub_eq_zero]; exact hc)
      exact ⟨x + w, by rw [map_add, hx', sub_add_cancel], by rw [map_add, hx]; exact zero_add _⟩
    · obtain ⟨w, rfl⟩ := (h1 (p + 1)).2 k c hk hc
      obtain ⟨x, z, hx, hx'⟩ := (h1 p).1 (c - (φ.f (p + 1)).hom w)
        (by rw [map_sub, cochain_comm_apply, sub_eq_zero]; exact hc)
      exact ⟨z, x + w, by rw [map_add, ← add_assoc, hx', sub_add_cancel],
        by rw [map_add, hx, zero_add]⟩
  · rintro ⟨h0, h1, h2⟩ (_ | p)
    · refine (quasiIsoAt_zero_iff φ).2 ⟨fun y hy => ?_, fun x hx hx' => h0 x hx' hx⟩
      obtain ⟨x, hx, hx'⟩ := h1 y 0 (by rw [map_zero]; exact hy) (map_zero _)
      exact ⟨x, hx', hx⟩
    · refine (quasiIsoAt_succ_iff φ p).2 ⟨fun y hy => ?_, fun x z hx hz => ?_⟩
      · obtain ⟨z, x, hx, hx'⟩ := h2 p y 0 (by rw [map_zero]; exact hy) (map_zero _)
        exact ⟨x, z, hx', hx⟩
      · cases p with
        | zero =>
          obtain ⟨w, -, hw⟩ := h1 z x hz hx
          exact ⟨w, hw⟩
        | succ p =>
          obtain ⟨-, w, -, hw⟩ := h2 p z x hz hx
          exact ⟨w, hw⟩

end QuasiIso

section Main

open Limits

variable {R : Type u} [CommRing R]

theorem coneExact_lTensor_of_quasiIso {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C)
    [hφ : QuasiIso φ] (hK : ∀ p, Module.Flat R (K.X p)) (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p))
    (M : Type*) [AddCommGroup M] [Module R M] :
    ConeExact (K := fun p => M ⊗[R] K.X p) (C := fun p => M ⊗[R] C.X p)
      (fun p => (K.d p (p + 1)).hom.lTensor M) (fun p => (C.d p (p + 1)).hom.lTensor M)
      (fun p => (φ.f p).hom.lTensor M) :=
  ConeExact.lTensor (K := fun p => K.X p) (C := fun p => C.X p)
    (dK := fun p => (K.d p (p + 1)).hom) (dC := fun p => (C.d p (p + 1)).hom)
    (φ := fun p => (φ.f p).hom) ((quasiIso_iff_coneExact φ).1 hφ)
    (fun _ => cochain_d_d_apply K _ _ _) (fun _ => cochain_d_d_apply C _ _ _)
    (fun _ => cochain_comm_apply φ _ _) n
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hnK p hp))
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hnC p hp)) M

theorem quasiIso_tensorLeft_of_flat {K C : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ C)
    [QuasiIso φ] (hK : ∀ p, Module.Flat R (K.X p)) (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p))
    (M : ModuleCat.{u} R) :
    QuasiIso (((MonoidalCategory.tensorLeft M).mapHomologicalComplex _).map φ) :=
  (quasiIso_iff_coneExact _).2 (coneExact_lTensor_of_quasiIso φ hK hC n hnK hnC M)

instance extendScalars_additive {S : Type w} [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{u, w, v} f).Additive where
  map_add {M N} g h := by
    letI := f.toAlgebra
    ext m
    exact tmul_add (R := R) (1 : S) (g.hom m) (h.hom m)

theorem quasiIso_extendScalars_of_flat {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C)
    [QuasiIso φ] (hK : ∀ p, Module.Flat R (K.X p)) (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p))
    {S : Type w} [CommRing S] (f : R →+* S) :
    QuasiIso (((ModuleCat.extendScalars.{u, w, v} f).mapHomologicalComplex _).map φ) :=
  (quasiIso_iff_coneExact _).2 (coneExact_lTensor_of_quasiIso φ hK hC n hnK hnC
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))

theorem finite_ker_quotient_of_finite_homology (C : CochainComplex (ModuleCat.{v} R) ℕ)
    (i j k : ℕ) (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k)
    [Module.Finite R (C.homology j)] :
    Module.Finite R (LinearMap.ker (C.d j k).hom ⧸
      (LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j k).hom).subtype) := by
  have e := (C.homologyIsoSc' i j k hi hk ≪≫ (C.sc' i j k).moduleCatHomologyIso).toLinearEquiv
  have h : Module.Finite R (LinearMap.ker (C.d j k).hom ⧸
    LinearMap.range (C.sc' i j k).moduleCatToCycles) := Module.Finite.equiv e
  refine Module.Finite.equiv (Submodule.quotEquivOfEq
    (LinearMap.range (C.sc' i j k).moduleCatToCycles) _ ?_)
  ext x
  exact ⟨fun ⟨y, hy⟩ => ⟨y, congrArg Subtype.val hy⟩, fun ⟨y, hy⟩ => ⟨y, Subtype.ext hy⟩⟩

/-- In degree zero take the image in `C⁰ × K¹` so the cone is exact in degree −1. -/
private theorem exists_finite_complex_quasiIso [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (hn : ∀ p, n < p → IsZero (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p)) :
    ∃ (K : CochainComplex (ModuleCat.{u} R) ℕ) (φ : K ⟶ C),
      (∀ p, n < p → IsZero (K.X p)) ∧ (∀ p, Module.Finite R (K.X p)) ∧
      (∀ p, 1 ≤ p → Module.Free R (K.X p)) ∧ QuasiIso φ := by
  obtain ⟨m, δ, ψ, hm, hδ, hψ, h0, h1⟩ := exists_free_complex (n + 1) C.X
    (fun p => (C.d p (p + 1)).hom) (LinearMap.range (C.d 0 0).hom)
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hn p hp))
    (finite_ker_quotient_of_finite_homology C 0 0 1 (by simp) (by simp))
    (fun p => finite_ker_quotient_of_finite_homology C p (p + 1) (p + 2) (by simp) (by simp))
  have hC : ∀ x, (C.d 0 0).hom x = 0 := fun x => by rw [C.shape 0 0 (by simp)]; rfl
  let N := LinearMap.range ((ψ 0).prod (δ 0))
  let X : ℕ → ModuleCat.{u} R := fun p => match p with
    | 0 => ModuleCat.of R N
    | p + 1 => ModuleCat.of R (Fin (m (p + 1)) → R)
  let d : ∀ p, X p ⟶ X (p + 1) := fun p => match p with
    | 0 => ModuleCat.ofHom (LinearMap.snd R _ _ ∘ₗ N.subtype)
    | p + 1 => ModuleCat.ofHom (δ (p + 1))
  let f : ∀ p, X p ⟶ C.X p := fun p => match p with
    | 0 => ModuleCat.ofHom (LinearMap.fst R _ _ ∘ₗ N.subtype)
    | p + 1 => ModuleCat.ofHom (ψ (p + 1))
  have hd : ∀ p, d p ≫ d (p + 1) = 0 := by
    rintro (_ | p)
    · refine ModuleCat.hom_ext (LinearMap.ext ?_)
      rintro ⟨_, x, rfl⟩
      exact hδ 0 x
    · exact ModuleCat.hom_ext (LinearMap.ext (hδ (p + 1)))
  have hf : ∀ p, f p ≫ C.d p (p + 1) = d p ≫ f (p + 1) := by
    rintro (_ | p)
    · refine ModuleCat.hom_ext (LinearMap.ext ?_)
      rintro ⟨_, x, rfl⟩
      exact hψ 0 x
    · exact ModuleCat.hom_ext (LinearMap.ext (hψ (p + 1)))
  let K : CochainComplex (ModuleCat.{u} R) ℕ := CochainComplex.of X d hd
  have hKd : ∀ p, K.d p (p + 1) = d p := fun p => by simp [K, CochainComplex.of_d]
  let φ : K ⟶ C :=
    { f := f
      comm' := by
        rintro i _ rfl
        rw [hKd]
        exact hf i }
  refine ⟨K, φ, ?_, ?_, ?_, ?_⟩
  · rintro (_ | p) hp
    · omega
    · refine ModuleCat.isZero_iff_subsingleton.2 ?_
      change Subsingleton (Fin (m (p + 1)) → R)
      rw [hm _ hp]
      infer_instance
  · rintro (_ | p)
    · exact inferInstanceAs (Module.Finite R N)
    · exact inferInstanceAs (Module.Finite R (Fin (m (p + 1)) → R))
  · rintro (_ | p) hp
    · omega
    · exact inferInstanceAs (Module.Free R (Fin (m (p + 1)) → R))
  · rw [quasiIso_iff_coneExact]
    simp only [hKd]
    refine ⟨fun x hx hx' => Subtype.ext (Prod.ext hx hx'), fun c k h h' => ?_, h1⟩
    obtain ⟨x, ⟨y, hy⟩, hx⟩ := h0 c k h h'
    rw [hC] at hy
    exact ⟨⟨_, x, rfl⟩, (sub_eq_zero.1 hy.symm).symm, hx⟩

theorem flat_zero_of_quasiIso {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C)
    [hφ : QuasiIso φ] (hK : ∀ p, 1 ≤ p → Module.Flat R (K.X p))
    (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p)) :
    Module.Flat R (K.X 0) :=
  haveI : ∀ p, Module.Flat R (K.X (p + 1)) := fun p => hK _ (Nat.le_add_left 1 p)
  ConeExact.flat_zero (K := fun p => K.X p) (C := fun p => C.X p)
    (dK := fun p => (K.d p (p + 1)).hom) (dC := fun p => (C.d p (p + 1)).hom)
    (φ := fun p => (φ.f p).hom) ((quasiIso_iff_coneExact φ).1 hφ)
    (fun _ => cochain_d_d_apply K _ _ _) (fun _ => cochain_d_d_apply C _ _ _)
    (fun _ => cochain_comm_apply φ _ _) n
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hnK p hp))
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hnC p hp))

/-- The finite projective approximation is a quasi-isomorphism after arbitrary base change. -/
theorem exists_finite_projective_complex_quasiIso [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (hn : ∀ p, n < p → IsZero (C.X p))
    (hflat : ∀ p, Module.Flat R (C.X p)) (hfin : ∀ p, Module.Finite R (C.homology p)) :
    ∃ (K : CochainComplex (ModuleCat.{u} R) ℕ) (φ : K ⟶ C),
      (∀ p, n < p → IsZero (K.X p)) ∧ (∀ p, Module.Finite R (K.X p)) ∧
      (∀ p, 1 ≤ p → Module.Free R (K.X p)) ∧ (∀ p, Module.Projective R (K.X p)) ∧
      QuasiIso φ ∧
      (∀ M : ModuleCat.{u} R,
        QuasiIso (((MonoidalCategory.tensorLeft M).mapHomologicalComplex _).map φ)) ∧
      (∀ (S : Type w) [CommRing S] [Algebra R S], QuasiIso
        (((ModuleCat.extendScalars.{u, w, u} (algebraMap R S)).mapHomologicalComplex _).map φ)) := by
  obtain ⟨K, φ, h1, h2, h3, h4⟩ := exists_finite_complex_quasiIso C n hn hfin
  have h5 : ∀ p, 1 ≤ p → Module.Flat R (K.X p) := fun p hp => by
    have := h3 p hp
    infer_instance
  have h6 : ∀ p, Module.Flat R (K.X p) := by
    rintro (_ | p)
    · exact flat_zero_of_quasiIso φ h5 hflat n h1 hn
    · exact h5 _ (Nat.le_add_left 1 p)
  refine ⟨K, φ, h1, h2, h3, fun p => ?_, h4,
    quasiIso_tensorLeft_of_flat φ h6 hflat n h1 hn,
    fun S _ _ => quasiIso_extendScalars_of_flat φ h6 hflat n h1 hn _⟩
  have := Module.finitePresentation_of_finite R (K.X p)
  exact Module.Flat.projective_of_finitePresentation

end Main

end GlobalTheory
