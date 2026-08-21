import GaloisForLFunctions.HTGeometry.ChainSubcomplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Quotient complexes and the long exact sequence of a pair

Quotienting a chain complex of modules by a differential-stable degreewise submodule gives a chain
complex, and the inclusion and the projection form a short exact sequence

  `0 → P → K → K/P → 0`,

whose homology long exact sequence is the long exact sequence of the pair when `K` is the singular
chains of a space and `P` the chains supported in a subspace.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

namespace ModuleSubcomplex

variable {R : Type} [CommRing R] {K : ChainComplex (ModuleCat.{v} R) ℕ}

/-- The differential induced on the quotient. -/
noncomputable def quotD (P : ModuleSubcomplex R K) (k : ℕ) :
    ModuleCat.of R ((K.X (k + 1)) ⧸ P.carrier (k + 1))
      ⟶ ModuleCat.of R ((K.X k) ⧸ P.carrier k) :=
  ModuleCat.ofHom
    (Submodule.mapQ (P.carrier (k + 1)) (P.carrier k) ((K.d (k + 1) k).hom)
      (fun x hx => P.bd_mem k x hx))

/-- The quotient chain complex `K/P`. -/
noncomputable def quotComplex (P : ModuleSubcomplex R K) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of R ((K.X k) ⧸ P.carrier k)) P.quotD (by
    intro k
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective (P.carrier (k + 2)) x
    show Submodule.Quotient.mk ((K.d (k + 1) k) ((K.d (k + 2) (k + 1)) c))
      = (0 : (K.X k) ⧸ P.carrier k)
    rw [chain_d_d_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.zero_mem _))

theorem quotComplex_d (P : ModuleSubcomplex R K) (k : ℕ) :
    P.quotComplex.d (k + 1) k = P.quotD k :=
  ChainComplex.of_d (fun k => ModuleCat.of R ((K.X k) ⧸ P.carrier k)) P.quotD k

/-- The projection onto the quotient complex. -/
noncomputable def proj (P : ModuleSubcomplex R K) : K ⟶ P.quotComplex where
  f k := ModuleCat.ofHom (P.carrier k).mkQ
  comm' := by
    rintro i j (hij : j + 1 = i)
    subst hij
    rw [quotComplex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun c => rfl)

/-- The short complex `P → K → K/P`. -/
noncomputable def shortComplex (P : ModuleSubcomplex R K) :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk P.incl P.proj (by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
    exact (Submodule.Quotient.mk_eq_zero _).mpr c.2)

/-- **The sequence of a subcomplex and its quotient is short exact.** -/
theorem shortExact (P : ModuleSubcomplex R K) : P.shortComplex.ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun k => ?_
  refine ModuleCat.shortComplex_shortExact _ (fun c => ?_) (fun a b hab => ?_) (fun c => ?_)
  · refine ⟨fun hc => ⟨⟨c, (Submodule.Quotient.mk_eq_zero _).mp hc⟩, rfl⟩, ?_⟩
    rintro ⟨x, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr x.2
  · exact Subtype.ext hab
  · exact Submodule.Quotient.mk_surjective _ c

/-- The connecting map of the pair. -/
noncomputable def connecting (P : ModuleSubcomplex R K) (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j) :
    P.quotComplex.homology i ⟶ P.complex.homology j :=
  (P.shortExact).δ i j hij

theorem homology_exact₁ (P : ModuleSubcomplex R K) (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp P.shortExact i j hij)).Exact :=
  ShortComplex.ShortExact.homology_exact₁ P.shortExact i j hij

theorem homology_exact₂ (P : ModuleSubcomplex R K) (i : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap P.shortComplex.f i)
      (HomologicalComplex.homologyMap P.shortComplex.g i)
      (by rw [← HomologicalComplex.homologyMap_comp, P.shortComplex.zero,
        HomologicalComplex.homologyMap_zero])).Exact :=
  ShortComplex.ShortExact.homology_exact₂ P.shortExact i

theorem homology_exact₃ (P : ModuleSubcomplex R K) (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ P.shortExact i j hij)).Exact :=
  ShortComplex.ShortExact.homology_exact₃ P.shortExact i j hij

/-! ### Maps of subcomplexes -/

variable {L : ChainComplex (ModuleCat.{v} R) ℕ}

/-- A chain map carrying one subcomplex into another. -/
structure Hom (P : ModuleSubcomplex R K) (Q : ModuleSubcomplex R L) where
  /-- The underlying chain map. -/
  map : K ⟶ L
  /-- It carries the subcomplex into the subcomplex. -/
  mem : ∀ (k : ℕ) (x : K.X k), x ∈ P.carrier k → (map.f k) x ∈ Q.carrier k

namespace Hom

variable {P : ModuleSubcomplex R K} {Q : ModuleSubcomplex R L}

theorem comm_apply (φ : Hom P Q) (k : ℕ) (x : K.X (k + 1)) :
    (φ.map.f k) ((K.d (k + 1) k) x) = (L.d (k + 1) k) ((φ.map.f (k + 1)) x) := by
  have h := φ.map.comm (k + 1) k
  have h2 := congrArg (fun ψ : K.X (k + 1) ⟶ L.X k => ModuleCat.Hom.hom ψ x) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2.symm

/-- The induced map of subcomplexes. -/
noncomputable def subMap (φ : Hom P Q) : P.complex ⟶ Q.complex where
  f k := ModuleCat.ofHom (((φ.map.f k).hom).restrict (fun x hx => φ.mem k x hx))
  comm' := by
    rintro i j (hij : j + 1 = i)
    subst hij
    rw [ModuleSubcomplex.complex_d, ModuleSubcomplex.complex_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact (φ.comm_apply j _).symm

/-- The induced map of quotient complexes. -/
noncomputable def quotMap (φ : Hom P Q) : P.quotComplex ⟶ Q.quotComplex where
  f k := ModuleCat.ofHom
    (Submodule.mapQ (P.carrier k) (Q.carrier k) ((φ.map.f k).hom) (fun x hx => φ.mem k x hx))
  comm' := by
    rintro i j (hij : j + 1 = i)
    subst hij
    rw [ModuleSubcomplex.quotComplex_d, ModuleSubcomplex.quotComplex_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective (P.carrier (j + 1)) x
    show (Submodule.Quotient.mk ((L.d (j + 1) j) ((φ.map.f (j + 1)) c)) : (L.X j) ⧸ Q.carrier j)
      = Submodule.Quotient.mk ((φ.map.f j) ((K.d (j + 1) j) c))
    rw [φ.comm_apply j c]

/-- The induced map of short exact sequences. -/
noncomputable def shortComplexHom (φ : Hom P Q) : P.shortComplex ⟶ Q.shortComplex where
  τ₁ := φ.subMap
  τ₂ := φ.map
  τ₃ := φ.quotMap
  comm₁₂ := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    exact ModuleCat.hom_ext (LinearMap.ext fun x => rfl)
  comm₂₃ := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    exact ModuleCat.hom_ext (LinearMap.ext fun x => rfl)

end Hom

/-! ### Restricting a subcomplex to a larger subcomplex -/

set_option linter.unusedVariables false in
/-- A subcomplex contained in another, viewed inside it. -/
noncomputable def restrictTo (P Q : ModuleSubcomplex R K) (hle : ∀ k, Q.carrier k ≤ P.carrier k) :
    ModuleSubcomplex R P.complex where
  carrier k := (Q.carrier k).comap (P.carrier k).subtype
  bd_mem k x hx := by
    rw [ModuleSubcomplex.complex_d]
    exact Q.bd_mem k x.1 hx

set_option linter.unusedVariables false in
/-- The inclusion realising a subcomplex of a subcomplex as a subcomplex of the ambient complex. -/
noncomputable def restrictHom (P Q : ModuleSubcomplex R K)
    (hle : ∀ k, Q.carrier k ≤ P.carrier k) : Hom (restrictTo P Q hle) Q where
  map := P.incl
  mem _ _ hx := hx

theorem isIso_restrictHom_subMap (P Q : ModuleSubcomplex R K)
    (hle : ∀ k, Q.carrier k ≤ P.carrier k) (k : ℕ) :
    IsIso ((restrictHom P Q hle).subMap.f k) := by
  refine ⟨ModuleCat.ofHom
    { toFun := fun y : Q.carrier k => (⟨⟨(y : K.X k), hle k y.2⟩, y.2⟩ :
        (Q.carrier k).comap (P.carrier k).subtype)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, ?_, ?_⟩
  · exact ModuleCat.hom_ext (LinearMap.ext fun z => rfl)
  · exact ModuleCat.hom_ext (LinearMap.ext fun z => rfl)

instance isIso_restrictHom_subMap' (P Q : ModuleSubcomplex R K)
    (hle : ∀ k, Q.carrier k ≤ P.carrier k) :
    IsIso ((restrictHom P Q hle).subMap) := by
  haveI : ∀ k, IsIso (((restrictHom P Q hle).subMap).f k) :=
    fun k => isIso_restrictHom_subMap P Q hle k
  exact HomologicalComplex.Hom.isIso_of_components _


/-- The chain map between two subcomplexes ordered by inclusion. -/
noncomputable def leHom {P Q : ModuleSubcomplex R K} (h : ∀ k, P.carrier k ≤ Q.carrier k) :
    P.complex ⟶ Q.complex where
  f k := ModuleCat.ofHom (Submodule.inclusion (h k))
  comm' := by
    rintro i j (hij : j + 1 = i)
    subst hij
    rw [ModuleSubcomplex.complex_d, ModuleSubcomplex.complex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => rfl)

end ModuleSubcomplex

/-- Singular homology of a space. -/
noncomputable def singularHomology (R : Type) [CommRing R] (X : Type v) [TopologicalSpace X]
    (i : ℕ) : ModuleCat R :=
  (singChainComplex R X).homology i

/-- Relative singular homology of a pair. -/
noncomputable def relativeHomology (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]
    (S : Set X) (i : ℕ) : ModuleCat R :=
  (subcomplexOfSubset R S).quotComplex.homology i

end GaloisForLFunctions.HTGeometry
