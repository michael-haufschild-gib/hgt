import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GenericExteriorDifferentials
import GaloisForLFunctions.HTGeometry.KaehlerAlgHomGenericVanishing

/-! Realization of differential forms of a smooth affine chart inside the
exterior algebra of the function field. -/

noncomputable section

open KaehlerDifferential GaloisForLFunctions.HTGeometry

namespace GlobalTheory.CechDR

variable (k E : Type*) [Field k] [Field E] [Algebra k E]

/-- The exterior algebra of the differentials of the function field. -/
abbrev DR := ExteriorAlgebra E Ω[E⁄k]

scoped instance drBaseAlgebra : Algebra k (DR k E) :=
  Algebra.compHom (DR k E) (algebraMap k E)

scoped instance drBaseModule : Module k (DR k E) :=
  (drBaseAlgebra k E).toModule

scoped instance drBaseTower : IsScalarTower k E (DR k E) :=
  IsScalarTower.of_compHom k E (DR k E)

end GlobalTheory.CechDR

namespace GlobalTheory.PD

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

section Pullback

variable {A : Type*} [CommRing A] [Algebra k A] (f : A →ₐ[k] E) (p : ℕ)

private def intoGeneric : ExteriorDifferentials k A p →ₗ[k] DR k E where
  toFun ω := ExteriorDifferentials.map f p ω
  map_add' ω η := congrArg Subtype.val ((ExteriorDifferentials.map f p).map_add ω η)
  map_smul' c ω := by
    change ((ExteriorDifferentials.map f p ((algebraMap k A c) • ω) :
      ExteriorDifferentials k E p) : DR k E) = _
    have hc : f.toRingHom (algebraMap k A c) = algebraMap k E c := f.commutes c
    rw [LinearMap.map_smulₛₗ, hc, Submodule.coe_smul_of_tower]
    rfl

private theorem intoGeneric_smul_wedge (a : A) (v : Fin p → A) :
    intoGeneric f p (a • exteriorPower.ιMulti A p (fun i => D k A (v i))) =
      f a • ExteriorAlgebra.ιMulti E p (fun i => D k E (f (v i))) := by
  change ((ExteriorDifferentials.map f p
    (a • exteriorPower.ιMulti A p fun i => D k A (v i))) : DR k E) = _
  rw [LinearMap.map_smulₛₗ, ExteriorDifferentials.map_ιMulti]
  simp only [algHomKaehlerMap_D]
  rfl

private theorem span_wedges_d :
    Submodule.span A (Set.range (fun v : Fin p → A =>
      exteriorPower.ιMulti A p (fun i => D k A (v i)))) = ⊤ := by
  have h : Set.range (fun v : Fin p → A => exteriorPower.ιMulti A p (fun i => D k A (v i))) =
      exteriorPower.ιMulti A p '' {w | Set.range w ⊆ Set.range (D k A)} := by
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨fun i => D k A (v i), ?_, rfl⟩
      rintro w ⟨i, rfl⟩
      exact ⟨v i, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      choose v hv using fun i => hw (Set.mem_range_self i)
      exact ⟨v, congrArg (exteriorPower.ιMulti A p) (funext hv)⟩
  rw [h]
  exact exteriorPower.ιMulti_span_of_span A p Ω[A⁄k] (span_range_derivation k A)

private theorem range_intoGeneric :
    LinearMap.range (intoGeneric f p) = Submodule.span k {ω | ∃ a : A, ∃ v : Fin p → A,
      ω = f a • ExteriorAlgebra.ιMulti E p (fun i => D k E (f (v i)))} := by
  let T := Submodule.span k {ω | ∃ a : A, ∃ v : Fin p → A,
    ω = f a • ExteriorAlgebra.ιMulti E p (fun i => D k E (f (v i)))}
  apply le_antisymm
  · rintro _ ⟨ω, rfl⟩
    have hω : ω ∈ Submodule.span A (Set.range (fun v : Fin p → A =>
        exteriorPower.ιMulti A p (fun i => D k A (v i)))) :=
      (span_wedges_d (k := k) (A := A) p).symm ▸ Submodule.mem_top
    suffices he : ∀ a : A, intoGeneric f p (a • ω) ∈ T by
      simpa only [one_smul] using he 1
    induction hω using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨v, rfl⟩ := hw
      intro a
      rw [intoGeneric_smul_wedge]
      exact Submodule.subset_span ⟨a, v, rfl⟩
    | zero => intro a; rw [smul_zero, map_zero]; exact zero_mem _
    | add u v _ _ hu hv =>
      intro a
      rw [smul_add, map_add]
      exact Submodule.add_mem _ (hu a) (hv a)
    | smul b u _ hu =>
      intro a
      rw [smul_smul]
      exact hu (a * b)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, v, rfl⟩
    exact ⟨a • exteriorPower.ιMulti A p (fun i => D k A (v i)), intoGeneric_smul_wedge f p a v⟩

end Pullback

variable (k E)

/-- Forms whose coefficients and differentiated functions belong to the chart algebra. -/
def omB (B : Subalgebra k E) (p : ℕ) : Submodule k (DR k E) :=
  Submodule.span k {ω | ∃ b ∈ B, ∃ v : Fin p → E, (∀ i, v i ∈ B) ∧
    ω = b • ExteriorAlgebra.ιMulti E p (fun i => D k E (v i))}

local instance chartFormsModule (B : Subalgebra k E) (p : ℕ) :
    Module k (ExteriorDifferentials k B p) :=
  exteriorPowerModule (A := k) (B := B) p

/-- Extend a chart form to the function field and retain its homogeneous degree. -/
def genericForm (B : Subalgebra k E) (p : ℕ) :
    ExteriorDifferentials k B p →ₗ[k] DR k E :=
  intoGeneric B.val p

theorem genericForm_apply (B : Subalgebra k E) (p : ℕ) (ω : ExteriorDifferentials k B p) :
    genericForm k E B p ω = (ExteriorDifferentials.map B.val p ω : DR k E) := rfl

/-- The image of all chart forms equals the span of wedges of chart functions. -/
theorem range_genericForm (B : Subalgebra k E) (p : ℕ) :
    LinearMap.range (genericForm k E B p) = omB k E B p := by
  unfold genericForm omB
  rw [range_intoGeneric]
  congr 1
  ext ω
  constructor
  · rintro ⟨b, v, rfl⟩
    exact ⟨b, b.2, fun i => v i, fun i => (v i).2, rfl⟩
  · rintro ⟨b, hb, v, hv, rfl⟩
    exact ⟨⟨b, hb⟩, fun i => ⟨v i, hv i⟩, rfl⟩

/-- A smooth affine chart embeds in rational forms with image the
regular forms in the given degree. -/
def genericFormEquiv (B : Subalgebra k E) [IsFractionRing B E] [Algebra.Smooth k B] (p : ℕ) :
    ExteriorDifferentials k B p ≃ₗ[k] omB k E B p := by
  have h : Function.Injective (genericForm k E B p) := by
    intro a b hab
    apply exteriorDifferentials_map_fraction_injective B.val rfl p
    exact Subtype.val_injective hab
  exact (LinearEquiv.ofInjective (genericForm k E B p) h).trans
    (LinearEquiv.ofEq _ _ (range_genericForm k E B p))

end GlobalTheory.PD
