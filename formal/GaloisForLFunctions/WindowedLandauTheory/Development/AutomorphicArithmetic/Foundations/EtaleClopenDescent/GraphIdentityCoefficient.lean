import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SpecializedDiagonalIdentity
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginExteriorPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphTensorPullback

/-! At a fixed point, the graph restriction of an identity tensor has
affine volume coefficient equal to the trace of the exterior
cotangent map. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open KaehlerDifferential GaloisForLFunctions.HTGeometry
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

section Transport

variable {k E L : Type} [Field k] [Field E] [Field L] [Algebra k E] [Algebra k L]
  {B : Subalgebra k E} {C : Subalgebra k L} {e : B →ₐ[k] k} {f : C →ₐ[k] k}

/-- A field map preserving values at a point restricts to the local
chart algebra there. -/
def localMapOfVal (j : E →ₐ[k] L)
    (h : ∀ v c, Val B e v c → Val C f (j v) c) : loc B e →ₐ[k] loc C f :=
  (j.comp (loc B e).val).codRestrict (loc C f) fun a =>
    ((val_iff_loc C f _ _).mp
      (h a (locEval B e a) ((val_iff_loc B e _ _).mpr ⟨a.2, rfl⟩))).choose

theorem locEval_localMapOfVal (j : E →ₐ[k] L)
    (h : ∀ v c, Val B e v c → Val C f (j v) c) (a : loc B e) :
    locEval C f (localMapOfVal j h a) = locEval B e a :=
  ((val_iff_loc C f _ _).mp
    (h a (locEval B e a) ((val_iff_loc B e _ _).mpr ⟨a.2, rfl⟩))).choose_spec

private theorem weighted_sum_kronecker {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (g b : ι → κ → R) (a : κ → κ → R)
    (h : ∀ I J, ∑ j, g j I * b j J = if I = J then 1 else 0) :
    (∑ j, ∑ I, ∑ J, b j I * a I J * g j J) = ∑ I, a I I := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.sum_comm]
  have he (J : κ) (j : ι) : b j I * a I J * g j J = a I J * (g j J * b j I) := by
    ac_rfl
  simp_rw [he, ← Finset.mul_sum, h, mul_ite, mul_one, mul_zero]
  simp

end Transport

variable {k F E L : Type} [Field k] [CharZero k] [IsAlgClosed k] [Field F] [Field E] [Field L]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [IsScalarTower F E L]
  {d n p q : ℕ} {x : Fin (d + 1) → F}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "B" => rB k E x {0}
local notation "C" => rB k L x {0}
local notation "P" => Set.powersetCard (Fin d) p
local notation "j₁" => IsScalarTower.toAlgHom k E L

private theorem pullbackDR_originAffineVolume :
    pullbackDR j₁ (originAffineVolume k E x) = originAffineVolume k L x := by
  simp only [originAffineVolume, pullbackDR_wedge, algHomKaehlerMap_D,
    IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply]

/-- The residue of the affine volume coefficient of the graph image
is the degree-`p` coefficient of the cotangent determinant polynomial. -/
theorem IsFinCover.exists_graphIdentityCoefficient (hE : IsFinCover k E x)
    (hL : IsFinCover k L x) [IsReduced (B ⧸ originIdeal k E x)]
    [IsReduced (C ⧸ originIdeal k L x)]
    (j₂ : E →ₐ[k] L) (e : OriginFibrePoint k E x) (f : OriginFibrePoint k L x)
    (hfix : ∀ v c, Val B e.1 v c → Val C f.1 (j₁ v) c ∧ Val C f.1 (j₂ v) c)
    (A : Matrix (Fin d) (Fin d) k)
    (hrow : ∀ m, ∃ (c : C) (g : Fin d → C), f.1 c ≠ 0 ∧
      (c : L) * j₂ (algebraMap F E (x m.succ / x 0)) =
        ∑ l, (g l : L) * algebraMap F L (x l.succ / x 0) ∧
      ∀ l, f.1 (g l) = f.1 c * A m l)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hpq : q + p = d)
    (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    (u : Fin n → ExteriorDifferentials k E q) (v : Fin n → ExteriorDifferentials k E p)
    (hu : ∀ j, (u j : DR k E) ∈ omB k E B q) (hv : ∀ j, (v j : DR k E) ∈ omB k E B p)
    (hact : ∀ a : ExteriorDifferentials k E p, ∑ j, traceWedgeLeftDual (F := F) τ (u j) a • v j =
      (∏ l : Fin d, x l.succ / x 0) • a) :
    ∃ s : L, graphFormPullback j₁ j₂ (∑ j, u j ⊗ₜ[k] v j) = s • originAffineVolume k L x ∧
      Val C f.1 s ((1 + (Polynomial.X : Polynomial k) • A.map Polynomial.C).det.coeff p) := by
  classical
  let R := loc C f.1
  let ev := locEval C f.1
  let m₁ := localMapOfVal j₁ (fun b c hb => (hfix b c hb).1)
  let m₂ := localMapOfVal j₂ (fun b c hb => (hfix b c hb).2)
  obtain ⟨g, b, hg, hb, hδ⟩ :=
    hE.exists_specializedIdentityFamily τ hτ hpq ρ hρ e u v hu hv hact
  obtain ⟨D, hD, hdiff⟩ := hL.exists_originDifferentialRows f
    (fun m => j₂ (algebraMap F E (x m.succ / x 0))) A hrow
  let A' := D.map (R.val)
  let a (I J : P) := originExteriorEntry D I J
  let s : R := ∑ j, ∑ I : P, ∑ J : P, m₂ (b j I) * a I J * m₁ (g j J)
  have hpull (I : P) := hL.pullbackDR_originCoordinateForm_eq_sum j₂ A' hdiff I
  have hpull₁ (j : Fin n) (J : P) :
      pullbackDR j₁ (u j : DR k E) * (originCoordinateForm k L x J : DR k L) =
        (m₁ (g j J) : L) • originAffineVolume k L x := by
    rw [← pullbackDR_originCoordinateForm (k := k) (E := E) (L := L),
      ← map_mul, hg, pullbackDR_smul, pullbackDR_originAffineVolume]
    rfl
  have hcoeff (I J : P) : (a I J : L) = originExteriorEntry A' I J :=
    map_originExteriorEntry R.val.toRingHom D I J
  refine ⟨s, ?_, (val_iff_loc C f.1 _ _).mpr ⟨s.2, ?_⟩⟩
  · rw [map_sum]
    change (∑ j, graphFormPullback j₁ j₂ (u j ⊗ₜ[k] v j)) = R.val s • originAffineVolume k L x
    simp only [s, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [graphFormPullback_tmul, hb j]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, pullbackDR_smul, hpull,
      Finset.smul_sum, Finset.mul_sum, mul_smul_comm, hpull₁, smul_smul, map_mul]
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
    rw [← hcoeff] <;> rfl
  · change ev s = _
    have he (I J : P) : ev (a I J) = originExteriorEntry A I J := by
      calc
        _ = originExteriorEntry (D.map ev.toRingHom) I J :=
          map_originExteriorEntry ev.toRingHom D I J
        _ = _ := congrArg (fun M : Matrix (Fin d) (Fin d) k => originExteriorEntry M I J) hD
    have hm₁ (a : loc B e.1) : ev (m₁ a) = locEval B e.1 a :=
      locEval_localMapOfVal j₁ (fun v c hv => (hfix v c hv).1) a
    have hm₂ (a : loc B e.1) : ev (m₂ a) = locEval B e.1 a :=
      locEval_localMapOfVal j₂ (fun v c hv => (hfix v c hv).2) a
    dsimp only [s]
    simp only [map_sum, map_mul, he, hm₁, hm₂]
    exact (weighted_sum_kronecker (fun j I => locEval B e.1 (g j I))
      (fun j I => locEval B e.1 (b j I)) (originExteriorEntry A) hδ).trans
        (sum_originExteriorEntry_eq_coeff A)

end GlobalTheory.PD
