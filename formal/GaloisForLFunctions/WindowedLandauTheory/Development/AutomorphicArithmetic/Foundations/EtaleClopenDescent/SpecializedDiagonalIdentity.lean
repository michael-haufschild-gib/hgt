import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginFormCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginFibreSpecialization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveAffineIdentityTensor
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RegularChartFormProduct

/-! A regular tensor acting as the identity under the field trace
specializes to the identity on the exterior space of an origin fibre
point. A section supported there isolates its contribution to the
trace. -/

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

private theorem basis_coordinates_of_scaled_basis {R V ι κ : Type} [CommRing R]
    [AddCommGroup V] [Module R V] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (e : Module.Basis κ R V) (v : ι → V) (b : ι → κ → R)
    (hb : ∀ j, v j = ∑ J, b j J • e J) (c : ι → R) (I J : κ) (s : R)
    (h : ∑ j, c j • v j = s • e I) :
    ∑ j, c j * b j J = if I = J then s else 0 := by
  have he (j : ι) : e.coord J (v j) = b j J := by
    rw [hb j, map_sum]
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, mul_ite]
  have hJ := congrArg (e.coord J) h
  simp only [map_sum, map_smul, he] at hJ
  simpa only [smul_eq_mul, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, mul_ite, mul_one, mul_zero] using hJ

variable {k F E : Type} [Field k] [CharZero k] [IsAlgClosed k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d n p q : ℕ} {x : Fin (d + 1) → F}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "B" => rB k E x {0}
local notation "P" => Set.powersetCard (Fin d) p
local notation "W" => ExteriorDifferentials k E p

omit [CharZero k] [IsAlgClosed k] in
private theorem coordinateForm_mem_omB (I : P) :
    (originCoordinateForm k E x I : DR k E) ∈ omB k E B p := by
  rw [originCoordinateForm, exteriorPower.ιMulti_family, exteriorPower.ιMulti_apply_coe]
  refine Submodule.subset_span ⟨1, one_mem _, fun i =>
    algebraMap F E (x ((Set.powersetCard.ofFinEmbEquiv.symm I i).succ) / x 0),
    fun _ => tco_mem k E x _, (one_smul E _).symm⟩

omit [CharZero k] [IsAlgClosed k] [Algebra k F] [IsScalarTower k F E] in
private theorem traceWedgeLeftDual_smul_of_volume (τ : DR k E →ₗ[E] E)
    (u : ExteriorDifferentials k E q) (v : W) (ω : DR k E)
    (s : F) (a g r : E) (h : (u : DR k E) * (v : DR k E) = g • ω)
    (hτ : τ ω = algebraMap F E s) (hr : r = a * g) :
    traceWedgeLeftDual (F := F) τ u (a • v) = s * Algebra.trace F E r := by
  rw [traceWedgeLeftDual_apply, Submodule.coe_smul, mul_smul_comm, h,
    smul_smul, map_smul, hτ, smul_eq_mul, ← hr, mul_comm r, ← Algebra.smul_def s r,
    map_smul, smul_eq_mul]

/-- The fibre values of the two coordinate families satisfy the
Kronecker-delta identity. -/
theorem IsFinCover.exists_specializedIdentityFamily (h : IsFinCover k E x)
    [IsReduced (B ⧸ originIdeal k E x)]
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hpq : q + p = d)
    (ρ : F →ₗ[k] k) (hρ : IsRes x ρ) (e : OriginFibrePoint k E x)
    (u : Fin n → ExteriorDifferentials k E q) (v : Fin n → W)
    (hu : ∀ j, (u j : DR k E) ∈ omB k E B q)
    (hv : ∀ j, (v j : DR k E) ∈ omB k E B p)
    (hact : ∀ a : W, ∑ j, traceWedgeLeftDual (F := F) τ (u j) a • v j =
      (∏ l : Fin d, x l.succ / x 0) • a) :
    ∃ g b : Fin n → P → loc B e.1,
      (∀ j I, (u j : DR k E) * originCoordinateForm k E x I =
        (g j I : E) • originAffineVolume k E x) ∧
      (∀ j, v j = ∑ I, (b j I : E) • originCoordinateForm k E x I) ∧
      ∀ I J, ∑ j, locEval B e.1 (g j I) * locEval B e.1 (b j J) =
        if I = J then 1 else 0 := by
  classical
  let C := loc B e.1
  let ev := locEval B e.1
  let η (I : P) := originCoordinateForm k E x I
  let s : F := ∏ l : Fin d, x l.succ / x 0
  have hs : s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun l _ =>
    div_ne_zero (h.pd.ne l.succ) (h.pd.ne 0)
  have hτvol : τ (originAffineVolume k E x) = algebraMap F E s := by
    rw [originAffineVolume_eq_smul h.pd, map_smul, hτ.1, smul_eq_mul, mul_one]
    exact (map_prod (algebraMap F E) _ _).symm
  obtain ⟨basis, hbasis⟩ := h.exists_originCoordinateFormBasis p
  have hreg (j : Fin n) (I : P) :
      (u j : DR k E) * (η I : DR k E) ∈ omB k E B d := by
    have hw : (u j : DR k E) * (η I : DR k E) ∈ omB k E B (q + p) :=
      mul_mem_omB (hu j) (coordinateForm_mem_omB I)
    exact (congrArg (fun m => (u j : DR k E) * (η I : DR k E) ∈ omB k E B m) hpq).mp hw
  choose g hg using fun j I => h.exists_localOriginVolumeCoefficient e _
    (omB_mono (le_loc B e.1) d (hreg j I))
  choose b hb using fun j => h.exists_originFormCoordinates e (v j) (hv j)
  refine ⟨g, b, hg, hb, fun I J => ?_⟩
  have hgv (j : Fin n) : Val B e.1 (g j I : E) (ev (g j I)) :=
    (val_iff_loc B e.1 _ _).mpr ⟨(g j I).2, rfl⟩
  obtain ⟨a, r, ha, hr, hval⟩ := h.exists_fibreSupportedCoefficients e _ _ hgv
  let aC : C := Subalgebra.inclusion (le_loc B e.1) a
  let t (j : Fin n) := Algebra.trace F E (r j)
  have ht (j : Fin n) : Val B e.1 (algebraMap F E (t j)) (ev (g j I)) := by
    have hres := h.residue_trace_fibreSupportedCoefficients e ρ hρ (r j) _ (fun e' => hval e' j)
    exact hres ▸ h.val_trace_origin e ρ hρ (r j)
  choose hmem heval using fun j => (val_iff_loc B e.1 _ _).mp (ht j)
  let tC (j : Fin n) : C := ⟨_, hmem j⟩
  have htrace (j : Fin n) :
      traceWedgeLeftDual (F := F) τ (u j) ((a : E) • η I) = s * t j :=
    traceWedgeLeftDual_smul_of_volume τ (u j) (η I) _ s a (g j I) (r j) (hg j I) hτvol (hr j)
  have hcontr := hact ((a : E) • η I)
  simp only [htrace, mul_smul, ← Finset.smul_sum] at hcontr
  have heq := smul_right_injective W hs hcontr
  have htE (j : Fin n) : t j • v j = algebraMap F E (t j) • v j :=
    (IsScalarTower.algebraMap_smul E (t j) (v j)).symm
  have hb' (j : Fin n) : v j = ∑ K, (b j K : E) • basis K := by
    simpa only [← hbasis] using hb j
  have heq' : ∑ j, algebraMap F E (t j) • v j = (a : E) • basis I := by
    simpa only [htE, η, ← hbasis] using heq
  have hJ := basis_coordinates_of_scaled_basis basis v (fun j K => (b j K : E))
    hb' (fun j => algebraMap F E (t j)) I J (a : E) heq'
  have hcoord : ∑ j, tC j * b j J = if I = J then aC else 0 := by
    apply Subtype.ext
    change C.val (∑ j, tC j * b j J) = C.val (if I = J then aC else 0)
    have htC (j : Fin n) : (tC j : E) = algebraMap F E (t j) := rfl
    have haC : (aC : E) = a := rfl
    simpa only [map_sum, map_mul, apply_ite, map_zero, Subalgebra.val_apply, htC, haC] using hJ
  have htEval (j : Fin n) : ev (tC j) = ev (g j I) := heval j
  have haEval : ev aC = 1 := (locEval_inclusion B e.1 a).trans ha
  have heC := congrArg ev hcoord
  change ∑ j, ev (g j I) * ev (b j J) = if I = J then 1 else 0
  simpa only [map_sum, map_mul, htEval, apply_ite, haEval, map_zero] using heC

end GlobalTheory.PD
