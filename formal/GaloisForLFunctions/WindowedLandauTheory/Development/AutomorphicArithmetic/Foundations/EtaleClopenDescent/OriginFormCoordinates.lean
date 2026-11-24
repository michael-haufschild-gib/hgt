import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginCoordinateBasis
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FormDenominatorLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveLogarithmicForms
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ComplementaryExteriorCoordinate
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginVolumeCochain
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LocalChartFormLattice

/-! Regular exterior forms have affine coordinate coefficients in the
local ring at any point of the reduced origin fibre. -/

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

open GlobalTheory.WH GaloisForLFunctions.HTGeometry

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {p : ℕ}

variable (k E x) in
/-- The wedge of the affine coordinate differentials selected by the
ordered subset. -/
def originCoordinateForm (I : Set.powersetCard (Fin d) p) : ExteriorDifferentials k E p :=
  exteriorPower.ιMulti_family E p
    (fun j => D k E (algebraMap F E (x j.succ / x 0))) I

omit [CharZero k] in
/-- The coordinate wedges are a basis over the rational function field. -/
theorem IsFinCover.exists_originCoordinateFormBasis (h : IsFinCover k E x) (p : ℕ) :
    ∃ b : Module.Basis (Set.powersetCard (Fin d) p) E (ExteriorDifferentials k E p),
      ∀ I, b I = originCoordinateForm k E x I := by
  obtain ⟨b, hb⟩ := h.exists_coordinateDifferentialBasis
  refine ⟨b.exteriorPower p, fun I => ?_⟩
  rw [exteriorPower.basis_apply, originCoordinateForm, show
    (b : Fin d → Ω[E⁄k]) = (fun j => D k E (algebraMap F E (x j.succ / x 0))) from funext hb]

omit [CharZero k] in
private theorem map_coordinateWedge {C : Type} [CommRing C] [Algebra k C]
    (f : C →ₐ[k] E) (b : Module.Basis (Fin d) C Ω[C⁄k]) (v : Fin d → Ω[E⁄k])
    (hv : ∀ j, algHomKaehlerMap f (b j) = v j) (I : Set.powersetCard (Fin d) p) :
    ExteriorDifferentials.map f p ((b.exteriorPower p) I) =
      exteriorPower.ιMulti_family E p v I := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, ExteriorDifferentials.map_ιMulti]
  simp only [exteriorPower.ιMulti_family]
  refine congrArg (fun z => exteriorPower.ιMulti E p z) ?_
  funext i
  exact hv _

omit [CharZero k] in
private theorem pullback_eq_sum_coordinates {C η : Type} [CommRing C] [Algebra k C]
    [Algebra C E] [IsScalarTower k C E] [Fintype η]
    (b : Module.Basis η C (ExteriorDifferentials k C p)) (w : ExteriorDifferentials k C p)
    (v : η → ExteriorDifferentials k E p)
    (hv : ∀ i, algebraFormPullback k C E p (b i) = v i) :
    algebraFormPullback k C E p w = ∑ i, algebraMap C E (b.repr w i) • v i := by
  conv_lhs => rw [← b.sum_repr w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← IsScalarTower.algebraMap_smul E, hv]

/-- Local coefficients of regular forms are obtained by expanding the
form in the exterior basis of the origin coordinate differentials. -/
theorem IsFinCover.exists_localOriginFormCoordinates (h : IsFinCover k E x)
    [IsReduced ((rB k E x {0}) ⧸ originIdeal k E x)] (e : OriginFibrePoint k E x)
    (u : ExteriorDifferentials k E p)
    (hu : (u : DR k E) ∈ omB k E (loc (rB k E x {0}) e.1) p) :
    ∃ c : Set.powersetCard (Fin d) p → loc (rB k E x {0}) e.1,
      u = ∑ I, (c I : E) • originCoordinateForm k E x I := by
  let B := rB k E x {0}
  let q : Ideal B := RingHom.ker e.1.toRingHom
  letI : q.IsPrime := (algebraPointKernel_isMaximal e.1).isPrime
  let C := Localization.AtPrime q
  let f : C →ₐ[k] E := localChartEmbedding B e.1
  letI : Algebra C E := f.toRingHom.toAlgebra
  letI : IsScalarTower k C E := .of_algebraMap_eq fun a => (f.commutes a).symm
  letI : IsScalarTower B C E := .of_algebraMap_eq fun a =>
    (localChartEmbedding_algebraMap B e.1 a).symm
  have hBasis : ∃ b : Module.Basis (Fin d) C Ω[C⁄k], ∀ j,
      b j = D k C (algebraMap B C ⟨_, tco_mem k E x j⟩) := h.exists_originCoordinateBasis e
  obtain ⟨b, hb⟩ := hBasis
  obtain ⟨s, hs⟩ := exists_chartForm_denominator B p e.1 u hu
  obtain ⟨w, hw⟩ := (mem_formRange_localization_iff q.primeCompl (C := C) u).mpr
    ⟨s, (mem_omB_iff_pullback_range B ((s : B) • u)).mp hs⟩
  let c := (b.exteriorPower p).repr w
  have hD (j : Fin d) : algHomKaehlerMap f (b j) =
      D k E (algebraMap F E (x j.succ / x 0)) := by
    rw [hb j, algHomKaehlerMap_D]
    exact congrArg (D k E) (localChartEmbedding_algebraMap B e.1 ⟨_, tco_mem k E x j⟩)
  have hf (I : Set.powersetCard (Fin d) p) :
      algebraFormPullback k C E p ((b.exteriorPower p) I) =
        originCoordinateForm k E x I := by
    rw [algebraFormPullback_eq_map k C E f rfl]
    exact map_coordinateWedge f b _ hD I
  refine ⟨fun I => ⟨f (c I), c I, rfl⟩, ?_⟩
  change u = ∑ I, algebraMap C E (c I) • originCoordinateForm k E x I
  exact hw.symm.trans (pullback_eq_sum_coordinates (b.exteriorPower p) w _ hf)

/-- Regular forms on the origin chart admit local coefficients at
each point of the reduced fibre. -/
theorem IsFinCover.exists_originFormCoordinates (h : IsFinCover k E x)
    [IsReduced ((rB k E x {0}) ⧸ originIdeal k E x)] (e : OriginFibrePoint k E x)
    (u : ExteriorDifferentials k E p) (hu : (u : DR k E) ∈ omB k E (rB k E x {0}) p) :
    ∃ c : Set.powersetCard (Fin d) p → loc (rB k E x {0}) e.1,
      u = ∑ I, (c I : E) • originCoordinateForm k E x I :=
  h.exists_localOriginFormCoordinates e u (omB_mono (le_loc _ _) p hu)

omit [CharZero k] in
theorem IsFinCover.originAffineVolume_ne_zero (h : IsFinCover k E x) :
    originAffineVolume k E x ≠ 0 := by
  rw [originAffineVolume_eq_smul h.pd]
  refine smul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ =>
    (map_ne_zero _).mpr (div_ne_zero (h.pd.ne j.succ) (h.pd.ne 0))) ?_
  obtain ⟨τ, hτ⟩ := h.topDegreeForms.1
  intro he
  exact zero_ne_one ((map_zero τ).symm.trans ((congrArg τ he).symm.trans hτ.1))

/-- A local top form is a local multiple of the affine volume. -/
theorem IsFinCover.exists_localOriginVolumeCoefficient (h : IsFinCover k E x)
    [IsReduced ((rB k E x {0}) ⧸ originIdeal k E x)] (e : OriginFibrePoint k E x)
    (w : DR k E) (hw : w ∈ omB k E (loc (rB k E x {0}) e.1) d) :
    ∃ c : loc (rB k E x {0}) e.1, w = (c : E) • originAffineVolume k E x := by
  classical
  have hwdeg : w ∈ ExteriorDifferentials k E d :=
    omB_le_degree (B := loc (rB k E x {0}) e.1) (p := d) hw
  let u : ExteriorDifferentials k E d := ⟨w, hwdeg⟩
  let I : Set.powersetCard (Fin d) d := ⟨Finset.univ, by simp⟩
  have hI (J : Set.powersetCard (Fin d) d) : J = I := by
    apply Subtype.ext
    exact Finset.eq_univ_of_card J.1 (J.property.trans (Fintype.card_fin d).symm)
  have he : (fun j : Fin d => j) =
      (Finset.univ : Finset (Fin d)).orderEmbOfFin I.property :=
    Finset.orderEmbOfFin_unique I.property (fun _ => Finset.mem_univ _) strictMono_id
  have hvol : (originCoordinateForm k E x I : DR k E) = originAffineVolume k E x := by
    rw [originCoordinateForm, exteriorPower.ιMulti_family, exteriorPower.ιMulti_apply_coe,
      originAffineVolume]
    change ExteriorAlgebra.ιMulti E d (fun j => D k E
      (algebraMap F E (x (((Finset.univ : Finset (Fin d)).orderEmbOfFin I.property j).succ) / x 0))) = _
    exact congrArg (fun f : Fin d → Fin d => ExteriorAlgebra.ιMulti E d fun j =>
      D k E (algebraMap F E (x (f j).succ / x 0))) he.symm
  obtain ⟨c, hc⟩ := h.exists_localOriginFormCoordinates e u hw
  rw [Finset.sum_eq_single I (fun J _ hne => (hne (hI J)).elim) (by simp)] at hc
  refine ⟨c I, ?_⟩
  have hcoe := congrArg (fun v : ExteriorDifferentials k E d => (v : DR k E)) hc
  change w = (c I : E) • (originCoordinateForm k E x I : DR k E) at hcoe
  exact hcoe.trans (congrArg ((c I : E) • ·) hvol)

/-- The affine volume coefficient of an origin-chart form is regular
at each reduced fibre point. -/
theorem IsFinCover.originVolumeCoefficient_mem_loc (h : IsFinCover k E x)
    [IsReduced ((rB k E x {0}) ⧸ originIdeal k E x)] (e : OriginFibrePoint k E x)
    (v : E) (hv : v • originAffineVolume k E x ∈ omB k E (rB k E x {0}) d) :
    v ∈ loc (rB k E x {0}) e.1 := by
  obtain ⟨c, hc⟩ := h.exists_localOriginVolumeCoefficient e _
    (omB_mono (le_loc _ _) d hv)
  have hv' := smul_left_injective E h.originAffineVolume_ne_zero hc
  rw [hv']
  exact c.property

end GlobalTheory.PD
