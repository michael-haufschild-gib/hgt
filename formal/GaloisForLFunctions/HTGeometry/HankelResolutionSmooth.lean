import GaloisForLFunctions.HTGeometry.HankelResolutionMorphism
import GaloisForLFunctions.HTGeometry.HankelIncidenceChartRing
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The Hankel incidence variety is smooth

`Y → Spec K` (through `Spec B_0`) is smooth: smoothness is local on the source, `Y` is covered by
the evaluation charts `D₊(G(k))`, and on each chart the structure map is `Spec` of
`K → B_{(G(k))} ≅ K[a_1, …, a_r, b_1, …, b_{N-j}]` (`chartRingEquiv`).

* `HTGeometry.hankelYStruct` : `Y → Spec K`.
* `HTGeometry.hankelYStruct_smooth`.
* `HTGeometry.hankelResolution_comp_struct` : `π` is a morphism over `K`.
-/

namespace HTGeometry

open AlgebraicGeometry CategoryTheory

universe u

variable {K : Type u} [Field K] {r N j : ℕ}

variable (K r N j) in
/-- **The structure map** `Y → Spec B_0 → Spec K`. -/
noncomputable def hankelYStruct : HankelY K r N j ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero (quotGrading K r N j) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (quotGrading K r N j 0)))

/-- The structure map on a chart. -/
theorem awayι_hankelYStruct (k : Fin (r + 1)) :
    Proj.awayι (quotGrading K r N j) (qChart K r N j k) (qChart_mem j k) one_pos ≫
        hankelYStruct K r N j
      = Spec.map (CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom _ _).comp
          (algebraMap K (quotGrading K r N j 0)))) := by
  rw [hankelYStruct, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- **The chart rings are smooth over `K`.** -/
theorem smooth_chart (hj : j + r ≤ N) (k : Fin (r + 1)) :
    ((HomogeneousLocalization.fromZeroRingHom (quotGrading K r N j)
      (Submonoid.powers (qChart K r N j k))).comp
        (algebraMap K (quotGrading K r N j 0))).Smooth := by
  have h : (HomogeneousLocalization.fromZeroRingHom (quotGrading K r N j)
      (Submonoid.powers (qChart K r N j k))).comp (algebraMap K (quotGrading K r N j 0))
      = (chartRingEquiv K r N hj (node K k)).toRingHom.comp (algebraMap K (ChartPoly K r (N - j))) := by
    refine RingHom.ext fun c => ?_
    exact (chartRingEquiv_C hj (node K k) c).symm
  rw [h]
  haveI : Algebra.Smooth K (ChartPoly K r (N - j)) := {}
  exact RingHom.Smooth.comp (RingHom.smooth_algebraMap.mpr inferInstance)
    (RingHom.Smooth.of_bijective (chartRingEquiv K r N hj (node K k)).bijective)

/-- **`Y` is smooth over `K`.** -/
theorem hankelYStruct_smooth [CharZero K] (hj : j + r ≤ N) : Smooth (hankelYStruct K r N j) := by
  refine IsZariskiLocalAtSource.of_iSup_eq_top (hankelChart K r N j)
    (iSup_hankelChart_eq_top (K := K) (r := r) (N := N) j) fun k => ?_
  have hι : (hankelChart K r N j k).ι = (Proj.basicOpenIsoSpec (quotGrading K r N j)
      (qChart K r N j k) (qChart_mem j k) one_pos).hom ≫
        Proj.awayι (quotGrading K r N j) (qChart K r N j k) (qChart_mem j k)
          one_pos := by
    rw [Proj.awayι, Iso.hom_inv_id_assoc]
  rw [hι, Category.assoc, MorphismProperty.cancel_left_of_respectsIso @Smooth, awayι_hankelYStruct,
    HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact smooth_chart hj k

/-- **`π` is a morphism over `K`.** -/
theorem hankelResolution_over [CharZero K] (hj : j + r ≤ N) :
    hankelResolution K r N hj ≫ Spec.map (CommRingCat.ofHom (algebraMap K (SecantRing K r N j)))
      = hankelYStruct K r N j := by
  have h1 : CommRingCat.ofHom (algebraMap K (SecantRing K r N j))
      = CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin N) K)) ≫
          CommRingCat.ofHom (Ideal.Quotient.mk (secantIdealUpTo K N r j)) := rfl
  have h2 : CommRingCat.ofHom (algebraMap K (quotGrading K r N j 0))
      = CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin N) K)) ≫
          CommRingCat.ofHom (momentToZero K r N j) := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => Subtype.ext ?_)
    simp [momentToZero, momentEmbed]
    rfl
  rw [h1, Spec.map_comp, ← Category.assoc, hankelResolution_comp_quotient, hankelYStruct, h2,
    Spec.map_comp, Category.assoc]

end HTGeometry
