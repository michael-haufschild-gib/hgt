/-
The actual Sonin projection modulo compact operators.

For two orthogonal constraints with compact mixed blocks and strict alternating block, the
projection onto the common kernel differs compactly from the formal complement of the two
forbidden projections. The proof first obtains an exact resolvent formula and then isolates every
non-complement term inside the compact ideal.
-/
import GaloisForLFunctions.RHTower.SoninEulerQuadraticCorner

noncomputable section

namespace RHTower

open ContinuousLinearMap
open MeasureTheory FourierTransform SchwartzMap
open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [CompleteSpace H]

/-- The inverse of the strict alternating correction operator. -/
def soninProjectionResolvent
    (A B : Submodule Complex H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1) : H →L[Complex] H :=
  ↑((Units.oneSub (soninAlternatingBlock A B) hT)⁻¹)

/-- Exact two-projection resolvent formula for the projection onto the common kernel. -/
theorem soninIntersectionProjection_eq_resolventFormula
    (A B : Submodule Complex H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1) :
    soninIntersectionProjection A B =
      A.orthogonal.starProjection -
        A.orthogonal.starProjection * soninProjectionResolvent A B hT *
          B.starProjection * A.orthogonal.starProjection := by
  let T : H →L[Complex] H := soninAlternatingBlock A B
  let e : (H →L[Complex] H)ˣ := Units.oneSub T (by simpa [T] using hT)
  let V : H →L[Complex] H := (↑(e⁻¹) : H →L[Complex] H)
  apply ContinuousLinearMap.ext
  intro x
  let xE : H := A.orthogonal.starProjection x
  let u : H := V (B.starProjection xE)
  let c : H := A.orthogonal.starProjection u
  let z : H := xE - c
  have hres : (1 - T) u = B.starProjection xE := by
    change ((↑e : H →L[Complex] H) * (↑(e⁻¹) : H →L[Complex] H))
        (B.starProjection xE) = B.starProjection xE
    rw [← Units.val_mul]
    simp
  have hres' : u - T u = B.starProjection xE := by
    simpa using hres
  have hTu : T u ∈ B := by
    change B.starProjection (A.starProjection (B.starProjection u)) ∈ B
    exact B.starProjection_apply_mem _
  have huB : u ∈ B := by
    have hu : u = B.starProjection xE + T u := sub_eq_iff_eq_add.mp hres'
    rw [hu]
    exact B.add_mem (B.starProjection_apply_mem _) hTu
  have hBu : B.starProjection u = u := B.starProjection_eq_self_iff.mpr huB
  have hTu_eq : T u = B.starProjection (A.starProjection u) := by
    change B.starProjection (A.starProjection (B.starProjection u)) = _
    rw [hBu]
  have hc : c = u - A.starProjection u := by
    simp [c]
  have hcB : B.starProjection c = B.starProjection xE := by
    calc
      B.starProjection c = B.starProjection (u - A.starProjection u) := by rw [hc]
      _ = B.starProjection u - B.starProjection (A.starProjection u) := map_sub _ _ _
      _ = u - T u := by rw [hBu, hTu_eq]
      _ = B.starProjection xE := hres'
  have hxEA : xE ∈ A.orthogonal := A.orthogonal.starProjection_apply_mem x
  have hzmem : z ∈ A.orthogonal ⊓ B.orthogonal := by
    constructor
    · exact A.orthogonal.sub_mem hxEA (A.orthogonal.starProjection_apply_mem u)
    · exact B.starProjection_apply_eq_zero_iff.mp (by simp [z, hcB])
  have hcSup : c ∈ A ⊔ B := by
    rw [hc]
    exact (A ⊔ B).sub_mem ((le_sup_right : B ≤ A ⊔ B) huB)
      ((le_sup_left : A ≤ A ⊔ B) (A.starProjection_apply_mem u))
  have hxsub : x - xE = A.starProjection x := by
    simp [xE]
  have hxzSup : x - z ∈ A ⊔ B := by
    have hdecomp : x - z = (x - xE) + c := by
      dsimp [z]
      abel
    rw [hdecomp, hxsub]
    exact (A ⊔ B).add_mem
      ((le_sup_left : A ≤ A ⊔ B) (A.starProjection_apply_mem x)) hcSup
  have hsupOrth : A ⊔ B ≤ (A.orthogonal ⊓ B.orthogonal).orthogonal := by
    rw [Submodule.inf_orthogonal]
    exact (A ⊔ B).le_orthogonal_orthogonal
  have hproj : soninIntersectionProjection A B x = z := by
    change (A.orthogonal ⊓ B.orthogonal).starProjection x = z
    exact (A.orthogonal ⊓ B.orthogonal).eq_starProjection_of_mem_orthogonal hzmem
      (hsupOrth hxzSup)
  rw [hproj]
  change z = xE - A.orthogonal.starProjection (V (B.starProjection xE))
  rfl

/-- If both mixed projection blocks are compact, the common-kernel projection is the formal
complement of the two forbidden projections modulo compact operators. -/
theorem isCompactOperator_soninIntersectionProjection_sub_complement
    (A B : Submodule Complex H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1)
    (hAB : IsCompactOperator (A.starProjection * B.starProjection))
    (hBA : IsCompactOperator (B.starProjection * A.starProjection)) :
    IsCompactOperator
      ((soninIntersectionProjection A B -
        (1 - A.starProjection - B.starProjection)) : H →L[Complex] H) := by
  let T : H →L[Complex] H := soninAlternatingBlock A B
  let e : (H →L[Complex] H)ˣ := Units.oneSub T (by simpa [T] using hT)
  let V : H →L[Complex] H := (↑(e⁻¹) : H →L[Complex] H)
  let E : H →L[Complex] H := A.orthogonal.starProjection
  have hTcompact : IsCompactOperator T := by
    have h := hBA.comp_clm B.starProjection
    simpa [T, soninAlternatingBlock, Function.comp_def] using! h
  have hVmul : V * (1 - T) = 1 := by
    change (↑(e⁻¹) : H →L[Complex] H) * (↑e : H →L[Complex] H) = 1
    rw [← Units.val_mul]
    simp
  have hVsub : V - 1 = V * T := by
    calc
      V - 1 = V - V * (1 - T) := by rw [hVmul]
      _ = V * T := by noncomm_ring
  have hVsubCompact : IsCompactOperator ((V - 1) : H →L[Complex] H) := by
    rw [hVsub]
    exact hTcompact.clm_comp V
  have hPRP : IsCompactOperator
      (A.starProjection * B.starProjection * A.starProjection) :=
    hAB.comp_clm A.starProjection
  have hmiddle : IsCompactOperator
      ((E * (V - 1) * B.starProjection * E) : H →L[Complex] H) := by
    have hright := hVsubCompact.comp_clm (B.starProjection * E)
    have hleft := hright.clm_comp E
    simpa only [mul_apply_eq_comp, _root_.sub_apply, one_apply_eq_self,
      map_sub] using! hleft
  rw [soninIntersectionProjection_eq_resolventFormula A B hT]
  have hE : E = 1 - A.starProjection := by
    simpa [E] using A.starProjection_orthogonal'
  rw [← hE]
  change IsCompactOperator
    (((E - E * V * B.starProjection * E) - (E - B.starProjection)) :
      H →L[Complex] H)
  have halgebra :
      (E - E * V * B.starProjection * E) - (E - B.starProjection) =
        A.starProjection * B.starProjection + B.starProjection * A.starProjection -
          A.starProjection * B.starProjection * A.starProjection -
            E * (V - 1) * B.starProjection * E := by
    rw [hE]
    noncomm_ring
  rw [halgebra]
  exact (hAB.add hBA).sub hPRP |>.sub hmiddle

private def reflectedSchwartz (g : SchwartzMap ℝ Complex) : SchwartzMap ℝ Complex :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    ((LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv) g

private theorem l2Reflection_toLp_reflectedSchwartz (g : SchwartzMap ℝ Complex) :
    l2Reflection (g.toLp 2) = (reflectedSchwartz g).toLp 2 := by
  rfl

private theorem fourierInv_reflectedSchwartz (g : SchwartzMap ℝ Complex) :
    FourierTransform.fourierInv g =
      reflectedSchwartz (FourierTransform.fourier g) := by
  simpa [reflectedSchwartz] using SchwartzMap.fourierInv_apply_eq g

/-- On real `L²`, inverse Fourier transform is forward Fourier transform followed by reflection. -/
theorem fourierUnitary_symm_eq_reflection_fourier (f : SoninL2) :
    fourierUnitary.symm f = l2Reflection (fourierUnitary f) := by
  let p : SoninL2 → Prop := fun f ↦
    fourierUnitary.symm f = l2Reflection (fourierUnitary f)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact fourierUnitary.symm.continuous
    · exact l2Reflection.continuous.comp fourierUnitary.continuous
  · intro g
    change fourierUnitary.symm (g.toLp 2) =
      l2Reflection (fourierUnitary (g.toLp 2))
    change FourierTransform.fourierInv (g.toLp 2) =
      l2Reflection (FourierTransform.fourier (g.toLp 2))
    rw [SchwartzMap.toLp_fourierInv_eq, fourierInv_reflectedSchwartz,
      SchwartzMap.toLp_fourier_eq, l2Reflection_toLp_reflectedSchwartz]

/-- The physical-after-Fourier mixed central block is compact. This supplies the order opposite
to the existing Fourier-after-physical block without assuming an adjoint-compactness theorem. -/
theorem isCompactOperator_centralPhysicalFourierBlock (a : ℝ) (ha : 0 < a) :
    IsCompactOperator
      ((centralPhysicalForbidden a).starProjection *
        (centralFourierForbidden a).starProjection) := by
  let A : SoninL2 →L[Complex] SoninL2 :=
    indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
  let F : SoninL2 →L[Complex] SoninL2 :=
    fourierUnitary.toLinearIsometry.toContinuousLinearMap
  let J : SoninL2 →L[Complex] SoninL2 := l2Reflection
  let K : SoninL2 →L[Complex] SoninL2 := cutoffFourierCutoff (-a) a (-a) a
  have hK : IsCompactOperator K := by
    simpa [K] using isCompactOperator_cutoffFourierCutoff (-a) a (-a) a (by linarith)
  have hEq :
      (centralPhysicalForbidden a).starProjection *
          (centralFourierForbidden a).starProjection = J * K * F := by
    change (physicalForbidden (centralInterval a)
        (measurableSet_centralInterval a)).starProjection *
      (fourierForbidden (centralInterval a)
        (measurableSet_centralInterval a)).starProjection = J * K * F
    rw [← indicatorCutoff_eq_physicalForbidden_starProjection,
      ← fourierCutoff_eq_fourierForbidden_starProjection]
    apply ContinuousLinearMap.ext
    intro f
    change A (fourierUnitary.symm (A (fourierUnitary f))) =
      J (K (F f))
    rw [fourierUnitary_symm_eq_reflection_fourier]
    change indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        (l2Reflection (fourierUnitary
          (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
            (fourierUnitary f)))) = J (K (F f))
    rw [← l2Reflection_indicatorCutoff_central]
    dsimp [J, K, F, cutoffFourierCutoff]
    rfl
  rw [hEq]
  exact (hK.comp_clm F).clm_comp J

/-- The actual ambient Sonin projection is the formal physical/Fourier complement modulo compact
operators. -/
theorem isCompactOperator_centralSoninProjection_sub_complement
    (a : ℝ) (ha : 0 < a) :
    IsCompactOperator
      ((centralSoninProjection a -
        (1 - indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) -
          fourierCutoff (centralInterval a) (measurableSet_centralInterval a))) :
        SoninL2 →L[Complex] SoninL2) := by
  rw [centralSoninProjection_eq_soninIntersectionProjection]
  have h := isCompactOperator_soninIntersectionProjection_sub_complement
    (centralPhysicalForbidden a) (centralFourierForbidden a)
    (norm_centralSoninAlternatingBlock_lt_one a ha)
    (isCompactOperator_centralPhysicalFourierBlock a ha)
    (isCompactOperator_centralFourierPhysicalBlock a ha)
  simpa [centralPhysicalForbidden, centralFourierForbidden,
    indicatorCutoff_eq_physicalForbidden_starProjection,
    fourierCutoff_eq_fourierForbidden_starProjection] using! h

/-- The same compact-complement identity on the actual even Sonin Hilbert carrier. -/
theorem isCompactOperator_evenCentralSoninProjection_sub_complement
    (a : ℝ) (ha : 0 < a) :
    IsCompactOperator
      ((evenCentralSoninProjection a -
        (1 - evenIndicatorCutoff a - evenFourierCutoff a)) :
        evenSubspace →L[Complex] evenSubspace) := by
  let T : SoninL2 →L[Complex] SoninL2 :=
    centralSoninProjection a -
      (1 - indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) -
        fourierCutoff (centralInterval a) (measurableSet_centralInterval a))
  have hT : IsCompactOperator T := by
    simpa [T] using isCompactOperator_centralSoninProjection_sub_complement a ha
  have hmap : Set.MapsTo T evenSubspace evenSubspace := by
    intro f hf
    change centralSoninProjection a f -
      (f - indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f -
        fourierCutoff (centralInterval a) (measurableSet_centralInterval a) f) ∈ evenSubspace
    exact evenSubspace.sub_mem
      (centralSoninProjection_mapsTo_evenSubspace a hf)
      (evenSubspace.sub_mem
        (evenSubspace.sub_mem hf (indicatorCutoff_central_mapsTo_evenSubspace a hf))
        (fourierCutoff_central_mapsTo_evenSubspace a hf))
  have hrestrict : IsCompactOperator (T.restrict hmap) := by
    exact (hT.comp_clm evenSubspace.subtypeL).codRestrict
      (fun f ↦ hmap f.property)
      (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace evenSubspace)).isClosed
  have heq : T.restrict hmap =
      evenCentralSoninProjection a -
        (1 - evenIndicatorCutoff a - evenFourierCutoff a) := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    rfl
  rw [← heq]
  exact hrestrict

end RHTower
