import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.GradedLieLaw
import GaloisForLFunctions.HTGeometry.ManifoldClosedStokes
import GaloisForLFunctions.HTGeometry.ManifoldDeRhamCohomology

/-!
# Law-valued differential forms, connections and curvature

For a graded Lie algebra `G` on `V`, `V`-valued `p`-forms are `Ω^p(M) ⊗ V` (`LawForm`).  The
tensor-product graded bracket is `[α ⊗ u, β ⊗ v] = (−1)^{|u| deg β} (α ∧ β) ⊗ [u, v]`
(`lawBracket`, with `|u|` the internal degree of the left factor) and the differential acts on the
form factor (`lawDiff`; the internal differential is zero).

A total-degree-one connection for a law concentrated in degrees `−1, −2, −3` has components
`a₂ ∈ Ω² ⊗ L₋₁`, `a₃ ∈ Ω³ ⊗ L₋₂`, `a₄ ∈ Ω⁴ ⊗ L₋₃` (`LawConnection`); its curvature
`Curv(a) = da + ½[a, a]` has the form-degree components `curv3`, …, `curv8`.  Strict morphisms of
graded Lie algebras act on coefficients and commute with `d`, the bracket, and hence curvature
(`LawConnection.curv5_map`).

On a closed oriented manifold the integral of top forms extends to `V`-valued top forms
(`lawIntegral`), commutes with observers and kills exact forms (`lawIntegral_lawDiff`); it descends
to de Rham cohomology (`cohomologyIntegral`, `lawCohomologyIntegral_lawClass`).
-/

open DifferentialGeometry TensorProduct
open scoped Manifold ContDiff

namespace GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (I M V) in
/-- `V`-valued differential `p`-forms `Ω^p(M) ⊗ V`. -/
abbrev LawForm (p : ℕ) := DifferentialForm I M p ⊗[ℝ] V

/-- The wedge product as a bilinear map. -/
noncomputable def wedgeBilin (p r : ℕ) :
    DifferentialForm I M p →ₗ[ℝ] DifferentialForm I M r →ₗ[ℝ] DifferentialForm I M (p + r) :=
  LinearMap.mk₂ ℝ DifferentialForm.wedge DifferentialForm.add_wedge DifferentialForm.smul_wedge
    DifferentialForm.wedge_add DifferentialForm.wedge_smul

/-- **The tensor-product graded bracket**: on pure tensors
`[α ⊗ u, β ⊗ v] = (−1)^{|u| deg β} (α ∧ β) ⊗ [u, v]`, where `i = |u|` is the internal degree of the
left factor. -/
noncomputable def lawBracket (G : GradedLieAlgebra V) (i : ℤ) (p r : ℕ) :
    LawForm I M V p →ₗ[ℝ] LawForm I M V r →ₗ[ℝ] LawForm I M V (p + r) :=
  koszulSign i r • TensorProduct.map₂ (wedgeBilin p r) G.bracket

theorem lawBracket_tmul (G : GradedLieAlgebra V) (i : ℤ) {p r : ℕ} (α : DifferentialForm I M p)
    (u : V) (β : DifferentialForm I M r) (v : V) :
    lawBracket G i p r (α ⊗ₜ u) (β ⊗ₜ v) =
      koszulSign i r • (DifferentialForm.wedge α β ⊗ₜ G.bracket u v) := by
  simp [lawBracket, TensorProduct.map₂_apply_tmul, wedgeBilin]

/-- The differential of law-valued forms (the internal differential being zero). -/
noncomputable def lawDiff [BoundarylessManifold I M] (p : ℕ) :
    LawForm I M V p →ₗ[ℝ] LawForm I M V (p + 1) :=
  TensorProduct.map (DifferentialForm.exteriorDerivativeLinearMap p) LinearMap.id

theorem lawDiff_tmul [BoundarylessManifold I M] {p : ℕ} (α : DifferentialForm I M p) (u : V) :
    lawDiff p (α ⊗ₜ u) = DifferentialForm.exteriorDerivative α ⊗ₜ u := rfl

variable (I M V) in
/-- A total-degree-one law connection for a law concentrated in degrees `−1, −2, −3`: its components
are a `2`-form with values in degree `−1`, a `3`-form with values in degree `−2` and a `4`-form
with values in degree `−3`. -/
structure LawConnection where
  c2 : LawForm I M V 2
  c3 : LawForm I M V 3
  c4 : LawForm I M V 4

namespace LawConnection

instance : Add (LawConnection I M V) := ⟨fun a b => ⟨a.c2 + b.c2, a.c3 + b.c3, a.c4 + b.c4⟩⟩

instance : Zero (LawConnection I M V) := ⟨⟨0, 0, 0⟩⟩

@[simp] theorem add_c2 (a b : LawConnection I M V) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem add_c3 (a b : LawConnection I M V) : (a + b).c3 = a.c3 + b.c3 := rfl
@[simp] theorem add_c4 (a b : LawConnection I M V) : (a + b).c4 = a.c4 + b.c4 := rfl

variable [BoundarylessManifold I M] (G : GradedLieAlgebra V)

/-- Curvature `Curv(a) = da + ½[a, a]` in form degree `3`. -/
noncomputable def curv3 (a : LawConnection I M V) : LawForm I M V 3 := lawDiff 2 a.c2

/-- Curvature in form degree `4`. -/
noncomputable def curv4 (a : LawConnection I M V) : LawForm I M V 4 :=
  lawDiff 3 a.c3 + (1 / 2 : ℝ) • lawBracket G (-1) 2 2 a.c2 a.c2

/-- Curvature in form degree `5`. -/
noncomputable def curv5 (a : LawConnection I M V) : LawForm I M V 5 :=
  lawDiff 4 a.c4 +
    (1 / 2 : ℝ) • (lawBracket G (-1) 2 3 a.c2 a.c3 + lawBracket G (-2) 3 2 a.c3 a.c2)

/-- Curvature in form degree `6`. -/
noncomputable def curv6 (a : LawConnection I M V) : LawForm I M V 6 :=
  (1 / 2 : ℝ) • (lawBracket G (-1) 2 4 a.c2 a.c4 + lawBracket G (-3) 4 2 a.c4 a.c2 +
    lawBracket G (-2) 3 3 a.c3 a.c3)

/-- Curvature in form degree `7`. -/
noncomputable def curv7 (a : LawConnection I M V) : LawForm I M V 7 :=
  (1 / 2 : ℝ) • (lawBracket G (-2) 3 4 a.c3 a.c4 + lawBracket G (-3) 4 3 a.c4 a.c3)

/-- Curvature in form degree `8`. -/
noncomputable def curv8 (a : LawConnection I M V) : LawForm I M V 8 :=
  (1 / 2 : ℝ) • lawBracket G (-3) 4 4 a.c4 a.c4

end LawConnection

/-! ## Observers -/

variable {V' : Type*} [AddCommGroup V'] [Module ℝ V']

/-- The action of a linear map of coefficients on law-valued forms. -/
def lawMap (q : V →ₗ[ℝ] V') (p : ℕ) : LawForm I M V p →ₗ[ℝ] LawForm I M V' p :=
  TensorProduct.map LinearMap.id q

theorem lawMap_tmul (q : V →ₗ[ℝ] V') {p : ℕ} (α : DifferentialForm I M p) (u : V) :
    lawMap q p (α ⊗ₜ u) = α ⊗ₜ q u := rfl

theorem lawMap_lawDiff [BoundarylessManifold I M] (q : V →ₗ[ℝ] V') (p : ℕ)
    (A : LawForm I M V p) : lawMap q (p + 1) (lawDiff p A) = lawDiff p (lawMap q p A) := by
  induction A using TensorProduct.induction_on with
  | zero => simp
  | tmul α u => rfl
  | add A B hA hB => simp [map_add, hA, hB]

/-- **Bracket naturality** under a strict morphism of graded Lie algebras. -/
theorem lawMap_lawBracket {G : GradedLieAlgebra V} {G' : GradedLieAlgebra V'}
    (q : GradedLieHom G G') (i : ℤ) (p r : ℕ) (A : LawForm I M V p) (B : LawForm I M V r) :
    lawMap q.toLinearMap (p + r) (lawBracket G i p r A B) =
      lawBracket G' i p r (lawMap q.toLinearMap p A) (lawMap q.toLinearMap r B) := by
  induction A using TensorProduct.induction_on with
  | zero => simp
  | tmul α u =>
    induction B using TensorProduct.induction_on with
    | zero => simp
    | tmul β v =>
      rw [lawBracket_tmul, lawMap_tmul, lawMap_tmul, lawBracket_tmul, map_smul, lawMap_tmul,
        q.map_bracket]
    | add B C hB hC => simp [map_add, hB, hC]
  | add A B hA hB => simp [map_add, LinearMap.add_apply, hA, hB]

/-- The image of a law connection under a coefficient map. -/
def LawConnection.map (q : V →ₗ[ℝ] V') (a : LawConnection I M V) : LawConnection I M V' :=
  ⟨lawMap q 2 a.c2, lawMap q 3 a.c3, lawMap q 4 a.c4⟩

/-- **Curvature naturality**: a strict observer maps curvature to curvature. -/
theorem LawConnection.curv5_map [BoundarylessManifold I M] {G : GradedLieAlgebra V}
    {G' : GradedLieAlgebra V'} (q : GradedLieHom G G') (a : LawConnection I M V) :
    (a.map q.toLinearMap).curv5 G' = lawMap q.toLinearMap 5 (a.curv5 G) := by
  simp only [LawConnection.curv5, LawConnection.map, map_add, map_smul]
  rw [← lawMap_lawDiff, ← lawMap_lawBracket, ← lawMap_lawBracket]

theorem LawConnection.curv4_map [BoundarylessManifold I M] {G : GradedLieAlgebra V}
    {G' : GradedLieAlgebra V'} (q : GradedLieHom G G') (a : LawConnection I M V) :
    (a.map q.toLinearMap).curv4 G' = lawMap q.toLinearMap 4 (a.curv4 G) := by
  simp only [LawConnection.curv4, LawConnection.map, map_add, map_smul]
  rw [← lawMap_lawDiff, ← lawMap_lawBracket]

theorem LawConnection.curv3_map [BoundarylessManifold I M] (q : V →ₗ[ℝ] V')
    (a : LawConnection I M V) :
    (a.map q).curv3 = lawMap q 3 a.curv3 := by
  simp only [LawConnection.curv3, LawConnection.map]
  rw [← lawMap_lawDiff]

/-! ## Integration of law-valued top forms -/

section Integration

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M]
  [I.Boundaryless] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] {n : ℕ}
  (o : ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n)) (b : Fin n → E)

/-- The integral of top forms as a linear functional. -/
def topFormIntegralLinear : DifferentialForm I M n →ₗ[ℝ] ℝ where
  toFun := topFormIntegral μ o e b
  map_add' := topFormIntegral_add μ o e b
  map_smul' c α := by rw [topFormIntegral_smul]; rfl

/-- The integral of `V`-valued top forms: `∫ (α ⊗ u) = (∫ α) u`. -/
def lawIntegral : LawForm I M V n →ₗ[ℝ] V :=
  (TensorProduct.lid ℝ V).toLinearMap ∘ₗ
    TensorProduct.map (topFormIntegralLinear μ o e b) LinearMap.id

theorem lawIntegral_tmul (α : DifferentialForm I M n) (u : V) :
    lawIntegral μ o e b (α ⊗ₜ u) = topFormIntegral μ o e b α • u := by
  simp [lawIntegral, topFormIntegralLinear]

/-- Observers commute with integration. -/
theorem lawIntegral_lawMap {V' : Type*} [AddCommGroup V'] [Module ℝ V'] (q : V →ₗ[ℝ] V')
    (A : LawForm I M V n) :
    lawIntegral μ o e b (lawMap q n A) = q (lawIntegral μ o e b A) := by
  induction A using TensorProduct.induction_on with
  | zero => simp
  | tmul α u => rw [lawMap_tmul, lawIntegral_tmul, lawIntegral_tmul, map_smul]
  | add A B hA hB => simp [map_add, hA, hB]

/-- **Stokes for law-valued forms** on a closed oriented manifold. -/
theorem lawIntegral_lawDiff {k : ℕ} (o : ManifoldOrientation I M (k + 1))
    (e : Orientation ℝ E (Fin (k + 1))) (b : Fin (k + 1) → E) (B : LawForm I M V k) :
    lawIntegral μ o e b (lawDiff k B) = 0 := by
  induction B using TensorProduct.induction_on with
  | zero => simp
  | tmul β u =>
    rw [lawDiff_tmul, lawIntegral_tmul, topFormIntegral_exteriorDerivative_eq_zero, zero_smul]
  | add A B hA hB => simp [map_add, hA, hB]

end Integration

/-! ## de Rham classes of top forms and their integral -/

section Cohomology

open _root_.HTGeometry

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M]
  [I.Boundaryless] {k : ℕ}

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M] in
/-- Every top form is closed. -/
theorem topForm_mem_cocycles (hk : Module.finrank ℝ E = k + 1)
    (α : DifferentialForm I M (k + 1)) :
    α ∈ (SmoothDeRham.complex (IM := I) (M := M)).cocycles (k + 1) := by
  rw [DeningerCochainComplex.mem_cocycles_iff]
  exact SmoothDeRham.differentialForm_eq_zero_of_finrank_lt (by omega) _

/-- The de Rham class of a top form. -/
def topClass (hk : Module.finrank ℝ E = k + 1) :
    DifferentialForm I M (k + 1) →ₗ[ℝ]
      (SmoothDeRham.complex (IM := I) (M := M)).cohomology (k + 1) :=
  ((SmoothDeRham.complex (IM := I) (M := M)).coboundariesInCocycles (k + 1)).mkQ ∘ₗ
    LinearMap.codRestrict _ LinearMap.id (topForm_mem_cocycles hk)

variable (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] (o : ManifoldOrientation I M (k + 1))
  (e : Orientation ℝ E (Fin (k + 1))) (b : Fin (k + 1) → E)

/-- The integral descends to top-degree de Rham cohomology, by Stokes. -/
def cohomologyIntegral :
    (SmoothDeRham.complex (IM := I) (M := M)).cohomology (k + 1) →ₗ[ℝ] ℝ :=
  ((SmoothDeRham.complex (IM := I) (M := M)).coboundariesInCocycles (k + 1)).liftQ
    ((topFormIntegralLinear μ o e b).comp
      ((SmoothDeRham.complex (IM := I) (M := M)).cocycles (k + 1)).subtype) (by
      intro x hx
      change (x : DifferentialForm I M (k + 1)) ∈
        (SmoothDeRham.complex (IM := I) (M := M)).coboundaries (k + 1) at hx
      rw [DeningerCochainComplex.coboundaries_succ] at hx
      obtain ⟨β, hβ⟩ := hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, ← hβ]
      exact topFormIntegral_exteriorDerivative_eq_zero μ o e b β)

theorem cohomologyIntegral_topClass (hk : Module.finrank ℝ E = k + 1)
    (α : DifferentialForm I M (k + 1)) :
    cohomologyIntegral μ o e b (topClass hk α) = topFormIntegral μ o e b α := rfl

/-- The `V`-valued de Rham class of a law-valued top form. -/
def lawClass (hk : Module.finrank ℝ E = k + 1) :
    LawForm I M V (k + 1) →ₗ[ℝ]
      (SmoothDeRham.complex (IM := I) (M := M)).cohomology (k + 1) ⊗[ℝ] V :=
  TensorProduct.map (topClass hk) LinearMap.id

/-- The integral of a `V`-valued de Rham class. -/
def lawCohomologyIntegral :
    (SmoothDeRham.complex (IM := I) (M := M)).cohomology (k + 1) ⊗[ℝ] V →ₗ[ℝ] V :=
  (TensorProduct.lid ℝ V).toLinearMap ∘ₗ
    TensorProduct.map (cohomologyIntegral μ o e b) LinearMap.id

theorem lawCohomologyIntegral_lawClass (hk : Module.finrank ℝ E = k + 1)
    (A : LawForm I M V (k + 1)) :
    lawCohomologyIntegral μ o e b (lawClass hk A) = lawIntegral μ o e b A := by
  induction A using TensorProduct.induction_on with
  | zero => simp
  | tmul α u =>
    simp [lawCohomologyIntegral, lawClass, lawIntegral_tmul, cohomologyIntegral_topClass]
  | add A B hA hB => simp [map_add, hA, hB]

end Cohomology

end

end GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry
