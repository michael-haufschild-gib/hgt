import GaloisForLFunctions.HTGeometry.CayleyBoundaryL2Unitary
import GaloisForLFunctions.HTGeometry.HardyBoundaryCayleyIdentification
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanCircleTraceCocycle
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanQuantizedCalculus
import GaloisForLFunctions.RHTower.Suzuki.SuzukiModelSpaceOrthogonal
import GaloisForLFunctions.RHTower.ConnesConsaniOnePrimeSourceDefect

open Complex MeasureTheory Filter
open scoped ENNReal NNReal lp InnerProductSpace

namespace RHTower

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- Circle Hardy boundary in the additive Fourier coordinate. -/
def ccmAddCircleHardyBoundary :
    HardyDisk →ₗᵢ[ℂ] CCMCircleL2 :=
  circleLpAddCircleLinearIsometryEquiv.toLinearIsometry.comp hardyDiskBoundary

@[simp] theorem ccmAddCircleHardyBoundary_single (n : ℕ) :
    ccmAddCircleHardyBoundary (lp.single 2 n (1 : ℂ) : HardyDisk) =
      (fourierLp 2 (n : ℤ) : CCMCircleL2) := by
  change circleLpAddCircleLinearIsometryEquiv
      (hardyDiskBoundary (lp.single 2 n (1 : ℂ) : HardyDisk)) = _
  rw [hardyDiskBoundary_single]
  exact circleLpToAddCircleLinearIsometry_circleMonomial n

/-- Full-space Cayley unitary in the additive circle coordinate used by the Gauss block. -/
def ccmCircleLineCayleyUnitary : CCMCircleL2 ≃ₗᵢ[ℂ] SoninL2 :=
  circleLpAddCircleLinearIsometryEquiv.symm.trans circleLineCayleyUnitary

@[simp] theorem ccmCircleLineCayleyUnitary_addHardyBoundary (f : HardyDisk) :
    ccmCircleLineCayleyUnitary (ccmAddCircleHardyBoundary f) =
      I • ((hardyDiskLineCayleyUnitary f : UpperHardyL2) : SoninL2) := by
  change circleLineCayleyUnitary
      (circleLpAddCircleLinearIsometryEquiv.symm
        (circleLpAddCircleLinearIsometryEquiv (hardyDiskBoundary f))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, circleLineCayleyUnitary_apply,
    circleLineCayleyIsometry_hardyDiskBoundary]

/-- Circle Hardy projection fixes the exact nonnegative Hardy boundary. -/
theorem ccmCircleHardyProjection_addHardyBoundary (f : HardyDisk) :
    ccmCircleHardyProjection (ccmAddCircleHardyBoundary f) =
      ccmAddCircleHardyBoundary f := by
  let A : HardyDisk →L[ℂ] CCMCircleL2 :=
    ccmCircleHardyProjection.comp ccmAddCircleHardyBoundary.toContinuousLinearMap
  let B : HardyDisk →L[ℂ] CCMCircleL2 :=
    ccmAddCircleHardyBoundary.toContinuousLinearMap
  have hAB : A = B := by
    apply ext_of_eq_on_single (p := (2 : ℝ≥0∞)) (by norm_num)
    intro n c
    rw [show (lp.single 2 n c : HardyDisk) =
        c • (lp.single 2 n (1 : ℂ) : HardyDisk) by
      apply lp.ext
      funext k
      simp [lp.single_apply, Pi.single_apply]]
    simp only [map_smul]
    congr 1
    change ccmCircleHardyProjection
        (ccmAddCircleHardyBoundary (lp.single 2 n 1)) =
      ccmAddCircleHardyBoundary (lp.single 2 n 1)
    rw [ccmAddCircleHardyBoundary_single, ccmCircleHardyProjection_fourierLp,
      if_pos (Int.natCast_nonneg n)]
  exact DFunLike.congr_fun hAB f

/-- The additive-circle Hardy projection is symmetric. -/
theorem ccmCircleHardyProjection_symmetric :
    ccmCircleHardyProjection.toLinearMap.IsSymmetric := by
  intro u v
  let E := (fourierBasis (T := (1 : ℝ))).repr
  let D := GaloisForLFunctions.lpDiagonalCLM ccmCircleHardyIndicator zero_le_one
    norm_ccmCircleHardyIndicator_le_one
  change inner ℂ (E.symm (D (E u))) v = inner ℂ u (E.symm (D (E v)))
  calc
    inner ℂ (E.symm (D (E u))) v =
        inner ℂ (E (E.symm (D (E u)))) (E v) :=
      (E.inner_map_map (E.symm (D (E u))) v).symm
    _ = inner ℂ (D (E u)) (E v) := by rw [E.apply_symm_apply]
    _ = inner ℂ (E u) (D (E v)) := by
      rw [GaloisForLFunctions.lpDiagonalCLM_inner
        ccmCircleHardyIndicator zero_le_one norm_ccmCircleHardyIndicator_le_one
        zero_le_one (fun j => by simpa using norm_ccmCircleHardyIndicator_le_one j)]
      congr 1
      apply lp.ext
      funext j
      change (starRingEnd ℂ) (ccmCircleHardyIndicator j) * E v j =
        ccmCircleHardyIndicator j * E v j
      by_cases hj : 0 ≤ j <;> simp [ccmCircleHardyIndicator, hj]
    _ = inner ℂ (E u) (E (E.symm (D (E v)))) := by rw [E.apply_symm_apply]
    _ = inner ℂ u (E.symm (D (E v))) :=
      E.inner_map_map u (E.symm (D (E v)))

/-- Closed- and open-positive-ray cutoffs agree on `L²`. -/
theorem ccmPositiveHalfLineProjection_eq_posRayProj :
    ccmPositiveHalfLineProjection = posRayProj := by
  change indicatorCutoff (Set.Ici 0) measurableSet_Ici = posRayProj
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hne : ∀ᵐ x : ℝ, x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [
    indicatorCutoff_ae (Set.Ici 0) measurableSet_Ici f,
    posRayProj_coeFn f, hne] with x hclosed hopen hx
  rw [hclosed, hopen]
  by_cases hpos : 0 < x
  · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hpos.le)]
    simp [posRaySymbol, hpos]
  · have hneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hx
    rw [Set.indicator_of_notMem (by simpa using hneg)]
    simp [posRaySymbol, hpos]

theorem posRayProj_mem_halfLineL2 (f : SoninL2) :
    posRayProj f ∈ halfLineL2 := by
  rw [mem_halfLineL2_iff]
  filter_upwards [posRayProj_coeFn f] with x hx hneg
  rw [hx]
  have hnot : ¬x ∈ Set.Ioi (0 : ℝ) := by simpa using (not_lt_of_ge hneg.le)
  simp [posRaySymbol, hnot]

theorem posRayProj_eq_self_of_mem_halfLineL2 {f : SoninL2}
    (hf : f ∈ halfLineL2) : posRayProj f = f := by
  apply Lp.ext
  have hne : ∀ᵐ x : ℝ, x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [posRayProj_coeFn f, (mem_halfLineL2_iff f).mp hf, hne]
      with x hx hsupport hne0
  rw [hx]
  by_cases hpos : 0 < x
  · simp [posRaySymbol, hpos]
  · have hneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hne0
    rw [hsupport hneg]
    simp

/-- The line Hardy projection has range exactly the lower Hardy boundary space. -/
theorem range_ccmHardyProjection_eq_hardyL2_orthogonal :
    LinearMap.range ccmHardyProjection.toLinearMap = hardyL2ᗮ := by
  rw [hardyL2_orthogonal]
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    let z : SoninL2 := ccmPositiveHalfLineProjection (fourierUnitary.symm y)
    refine ⟨z, ?_, rfl⟩
    change ccmPositiveHalfLineProjection (fourierUnitary.symm y) ∈ halfLineL2
    rw [ccmPositiveHalfLineProjection_eq_posRayProj]
    exact posRayProj_mem_halfLineL2 _
  · rintro x ⟨z, hz, rfl⟩
    refine ⟨fourierUnitary z, ?_⟩
    change ccmHardyProjection (fourierUnitary z) = fourierUnitary z
    rw [ccmHardyProjection_apply, LinearIsometryEquiv.symm_apply_apply,
      ccmPositiveHalfLineProjection_eq_posRayProj,
      posRayProj_eq_self_of_mem_halfLineL2 hz]

theorem ccmHardyProjection_eq_self_of_mem_hardyL2_orthogonal
    {f : SoninL2} (hf : f ∈ hardyL2ᗮ) : ccmHardyProjection f = f := by
  rw [← range_ccmHardyProjection_eq_hardyL2_orthogonal] at hf
  obtain ⟨g, rfl⟩ := hf
  have hP := ccmHardyProjection_idempotent
  rw [isIdempotentElem_iff] at hP
  exact DFunLike.congr_fun hP g

theorem ccmHardyProjection_eq_zero_of_mem_hardyL2
    {f : SoninL2} (hf : f ∈ hardyL2) : ccmHardyProjection f = 0 := by
  have hPf : ccmHardyProjection f ∈ hardyL2ᗮ := by
    rw [← range_ccmHardyProjection_eq_hardyL2_orthogonal]
    exact ⟨f, rfl⟩
  have horth : inner ℂ f (ccmHardyProjection f) = 0 :=
    (Submodule.mem_orthogonal hardyL2 (ccmHardyProjection f)).mp hPf f hf
  have hsym := ccmHardyProjection_symmetric f (ccmHardyProjection f)
  have hidem := ccmHardyProjection_idempotent
  rw [isIdempotentElem_iff] at hidem
  have hidemf := DFunLike.congr_fun hidem f
  simp only [mul_apply_eq_comp] at hidemf
  have hself : inner ℂ (ccmHardyProjection f) (ccmHardyProjection f) = 0 := by
    calc
      inner ℂ (ccmHardyProjection f) (ccmHardyProjection f) =
          inner ℂ f (ccmHardyProjection (ccmHardyProjection f)) := hsym
      _ = inner ℂ f (ccmHardyProjection f) := by rw [hidemf]
      _ = 0 := horth
  exact inner_self_eq_zero.mp hself

/-- Positive circle Fourier modes land in the upper Hardy boundary. -/
theorem ccmCircleLineCayleyUnitary_fourierLp_of_nonneg_mem_hardyL2
    {j : ℤ} (hj : 0 ≤ j) :
    ccmCircleLineCayleyUnitary (fourierLp 2 j : CCMCircleL2) ∈ hardyL2 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  rw [← ccmAddCircleHardyBoundary_single,
    ccmCircleLineCayleyUnitary_addHardyBoundary]
  exact Submodule.smul_mem _ I
    (hardyDiskLineCayleyUnitary
      (lp.single 2 n (1 : ℂ) : HardyDisk)).property

/-- Negative circle Fourier modes land in the lower Hardy boundary. -/
theorem ccmCircleLineCayleyUnitary_fourierLp_of_neg_mem_hardyL2_orthogonal
    {j : ℤ} (hj : j < 0) :
    ccmCircleLineCayleyUnitary (fourierLp 2 j : CCMCircleL2) ∈ hardyL2ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  let yh : UpperHardyL2 := ⟨y, hy⟩
  let f : HardyDisk := hardyDiskLineCayleyUnitary.symm yh
  have hf : hardyDiskLineCayleyUnitary f = yh := by
    exact hardyDiskLineCayleyUnitary.apply_symm_apply yh
  have hQj : ccmCircleHardyProjection (fourierLp 2 j : CCMCircleL2) = 0 := by
    rw [ccmCircleHardyProjection_fourierLp, if_neg (not_le.mpr hj)]
  have hinnerCircle :
      inner ℂ (fourierLp 2 j : CCMCircleL2) (ccmAddCircleHardyBoundary f) = 0 := by
    calc
      inner ℂ (fourierLp 2 j : CCMCircleL2) (ccmAddCircleHardyBoundary f) =
          inner ℂ (fourierLp 2 j : CCMCircleL2)
            (ccmCircleHardyProjection (ccmAddCircleHardyBoundary f)) := by
        rw [ccmCircleHardyProjection_addHardyBoundary]
      _ = inner ℂ (ccmCircleHardyProjection (fourierLp 2 j : CCMCircleL2))
          (ccmAddCircleHardyBoundary f) :=
        (ccmCircleHardyProjection_symmetric
          (fourierLp 2 j : CCMCircleL2) (ccmAddCircleHardyBoundary f)).symm
      _ = 0 := by rw [hQj, inner_zero_left]
  have hinnerLine :
      inner ℂ (ccmCircleLineCayleyUnitary (fourierLp 2 j : CCMCircleL2))
        (ccmCircleLineCayleyUnitary (ccmAddCircleHardyBoundary f)) = 0 := by
    rw [ccmCircleLineCayleyUnitary.inner_map_map, hinnerCircle]
  rw [ccmCircleLineCayleyUnitary_addHardyBoundary, hf] at hinnerLine
  change inner ℂ (ccmCircleLineCayleyUnitary (fourierLp 2 j : CCMCircleL2))
      (I • y) = 0 at hinnerLine
  rw [inner_smul_right] at hinnerLine
  have hzero := (mul_eq_zero.mp hinnerLine).resolve_left I_ne_zero
  have hconj := congrArg (starRingEnd ℂ) hzero
  rwa [inner_conj_symm, map_zero] at hconj

/-- Exact basis form of the Hardy-projection Cayley transport. -/
theorem ccmHardyProjection_ccmCircleLineCayleyUnitary_fourierLp (j : ℤ) :
    ccmHardyProjection
        (ccmCircleLineCayleyUnitary (fourierLp 2 j : CCMCircleL2)) =
      ccmCircleLineCayleyUnitary
        ((1 - ccmCircleHardyProjection) (fourierLp 2 j : CCMCircleL2)) := by
  by_cases hj : 0 ≤ j
  · rw [ccmHardyProjection_eq_zero_of_mem_hardyL2
        (ccmCircleLineCayleyUnitary_fourierLp_of_nonneg_mem_hardyL2 hj)]
    simp [ccmCircleHardyProjection_fourierLp, hj]
  · have hjneg : j < 0 := lt_of_not_ge hj
    rw [ccmHardyProjection_eq_self_of_mem_hardyL2_orthogonal
        (ccmCircleLineCayleyUnitary_fourierLp_of_neg_mem_hardyL2_orthogonal hjneg)]
    simp [ccmCircleHardyProjection_fourierLp, hj]

/-- Exact operator intertwining of circle and source-line Hardy projections. -/
theorem ccmHardyProjection_ccmCircleLineCayleyUnitary :
    ccmHardyProjection.comp
        ccmCircleLineCayleyUnitary.toLinearIsometry.toContinuousLinearMap =
      ccmCircleLineCayleyUnitary.toLinearIsometry.toContinuousLinearMap.comp
        (1 - ccmCircleHardyProjection) := by
  apply ContinuousLinearMap.ext_on
    (show Dense ((Submodule.span ℂ (Set.range
      (fourierBasis (T := (1 : ℝ))))) : Set CCMCircleL2) by
      rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
        (fourierBasis (T := (1 : ℝ))).dense_span]
      rfl)
  rintro _ ⟨j, rfl⟩
  rw [coe_fourierBasis]
  exact ccmHardyProjection_ccmCircleLineCayleyUnitary_fourierLp j

/-! ## Literal one-prime multiplier on the multiplicative circle -/

/-- The line source symbol extended through the Cayley embedding; the omitted endpoint is set to
zero and hence does not affect the `L²` multiplier. -/
def connesConsaniOnePrimeCircleSymbol (p : Nat.Primes) : Circle → ℂ :=
  Function.extend circleCayley (connesConsaniOnePrimeScatteringSymbol p) 0

theorem measurable_connesConsaniOnePrimeCircleSymbol (p : Nat.Primes) :
    Measurable (connesConsaniOnePrimeCircleSymbol p) := by
  exact (continuous_circleCayley.measurableEmbedding injective_circleCayley).measurable_extend
    (continuous_connesConsaniOnePrimeScatteringSymbol p).measurable measurable_zero

@[simp] theorem connesConsaniOnePrimeCircleSymbol_circleCayley
    (p : Nat.Primes) (t : ℝ) :
    connesConsaniOnePrimeCircleSymbol p (circleCayley t) =
      connesConsaniOnePrimeScatteringSymbol p t := by
  exact Function.Injective.extend_apply injective_circleCayley _ _ t

theorem norm_connesConsaniOnePrimeCircleSymbol_le_one
    (p : Nat.Primes) (z : Circle) :
    ‖connesConsaniOnePrimeCircleSymbol p z‖ ≤ 1 := by
  classical
  by_cases hz : z ∈ Set.range circleCayley
  · obtain ⟨t, rfl⟩ := hz
    rw [connesConsaniOnePrimeCircleSymbol_circleCayley,
      norm_connesConsaniOnePrimeScatteringSymbol]
  · rw [connesConsaniOnePrimeCircleSymbol, Function.extend_apply' _ _ z hz]
    simp

/-- Literal one-prime product multiplier on multiplicative-circle `L²`. -/
def connesConsaniOnePrimeCircleMultiplier (p : Nat.Primes) :
    Lp ℂ 2 circleLebesgue →L[ℂ] Lp ℂ 2 circleLebesgue :=
  lpBoundedMulCLM (p := 2) (μ := circleLebesgue)
    (measurable_connesConsaniOnePrimeCircleSymbol p) zero_le_one
    (norm_connesConsaniOnePrimeCircleSymbol_le_one p)

/-- Bounded-multiplier realization of the literal source symbol on line `L²`. -/
def connesConsaniOnePrimeLineLpMultiplier (p : Nat.Primes) :
    SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (continuous_connesConsaniOnePrimeScatteringSymbol p).measurable zero_le_one
    (fun t => by rw [norm_connesConsaniOnePrimeScatteringSymbol])

theorem connesConsaniOnePrimeScatteringMultiplier_eq_lineLpMultiplier
    (p : Nat.Primes) :
    connesConsaniOnePrimeScatteringMultiplier p =
      connesConsaniOnePrimeLineLpMultiplier p := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [
    connesConsaniOnePrimeScatteringMultiplier_ae p f,
    lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (continuous_connesConsaniOnePrimeScatteringSymbol p).measurable zero_le_one
      (fun t => by rw [norm_connesConsaniOnePrimeScatteringSymbol]) f]
      with t hsource hlp
  rw [hsource]
  change connesConsaniOnePrimeScatteringSymbol p t * f t =
    (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
      (continuous_connesConsaniOnePrimeScatteringSymbol p).measurable zero_le_one
      (fun t => by rw [norm_connesConsaniOnePrimeScatteringSymbol]) f) t
  rw [hlp]

/-- Exact Cayley transport of the literal one-prime product multiplier. -/
theorem circleLineCayleyUnitary_onePrimeCircleMultiplier
    (p : Nat.Primes) (f : Lp ℂ 2 circleLebesgue) :
    circleLineCayleyUnitary (connesConsaniOnePrimeCircleMultiplier p f) =
      connesConsaniOnePrimeLineLpMultiplier p (circleLineCayleyUnitary f) := by
  rw [circleLineCayleyUnitary_apply]
  have htransport := circleLineCayleyIsometry_mul
    (measurable_connesConsaniOnePrimeCircleSymbol p) zero_le_one
    (norm_connesConsaniOnePrimeCircleSymbol_le_one p) f
  rw [show connesConsaniOnePrimeCircleMultiplier p =
      lpBoundedMulCLM (p := 2) (μ := circleLebesgue)
        (measurable_connesConsaniOnePrimeCircleSymbol p) zero_le_one
        (norm_connesConsaniOnePrimeCircleSymbol_le_one p) from rfl]
  rw [htransport]
  apply Lp.ext
  filter_upwards [
    lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
      ((measurable_connesConsaniOnePrimeCircleSymbol p).comp
        continuous_circleCayley.measurable) zero_le_one
      (fun x => norm_connesConsaniOnePrimeCircleSymbol_le_one p (circleCayley x))
      (circleLineCayleyIsometry f),
    lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (continuous_connesConsaniOnePrimeScatteringSymbol p).measurable zero_le_one
      (fun t => by rw [norm_connesConsaniOnePrimeScatteringSymbol])
      (circleLineCayleyIsometry f)] with t hleft hright
  rw [hleft]
  change (connesConsaniOnePrimeCircleSymbol p ∘ circleCayley) t *
      circleLineCayleyIsometry f t =
    (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
      (continuous_connesConsaniOnePrimeScatteringSymbol p).measurable zero_le_one
      (fun t => by rw [norm_connesConsaniOnePrimeScatteringSymbol])
      (circleLineCayleyIsometry f)) t
  rw [hright, Function.comp_apply,
    connesConsaniOnePrimeCircleSymbol_circleCayley]

/-! ## Full source defect transported to the circle -/

/-- Nonnegative-frequency Hardy projection on multiplicative-circle `L²`. -/
def ccmMultiplicativeCircleHardyProjection :
    Lp ℂ 2 circleLebesgue →L[ℂ] Lp ℂ 2 circleLebesgue :=
  circleLpAddCircleLinearIsometryEquiv.symm.toLinearIsometry.toContinuousLinearMap.comp
    (ccmCircleHardyProjection.comp
      circleLpAddCircleLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap)

/-- Exact source-line projection transport in multiplicative-circle coordinates. -/
theorem ccmHardyProjection_circleLineCayleyUnitary :
    ccmHardyProjection.comp
        circleLineCayleyUnitary.toLinearIsometry.toContinuousLinearMap =
      circleLineCayleyUnitary.toLinearIsometry.toContinuousLinearMap.comp
        (1 - ccmMultiplicativeCircleHardyProjection) := by
  apply ContinuousLinearMap.ext
  intro f
  have h := congrArg (fun T : CCMCircleL2 →L[ℂ] SoninL2 =>
      T (circleLpAddCircleLinearIsometryEquiv f))
    ccmHardyProjection_ccmCircleLineCayleyUnitary
  change ccmHardyProjection
      (circleLineCayleyUnitary f) =
    circleLineCayleyUnitary
      ((1 - ccmMultiplicativeCircleHardyProjection) f)
  simpa [ccmCircleLineCayleyUnitary,
    ccmMultiplicativeCircleHardyProjection] using h

theorem one_sub_ccmHardyProjection_circleLineCayleyUnitary
    (f : Lp ℂ 2 circleLebesgue) :
    (1 - ccmHardyProjection) (circleLineCayleyUnitary f) =
      circleLineCayleyUnitary (ccmMultiplicativeCircleHardyProjection f) := by
  have h := DFunLike.congr_fun ccmHardyProjection_circleLineCayleyUnitary f
  change ccmHardyProjection (circleLineCayleyUnitary f) =
    circleLineCayleyUnitary ((1 - ccmMultiplicativeCircleHardyProjection) f) at h
  change circleLineCayleyUnitary f -
      ccmHardyProjection (circleLineCayleyUnitary f) =
    circleLineCayleyUnitary (ccmMultiplicativeCircleHardyProjection f)
  rw [h]
  rw [sub_apply, one_apply_eq_self, map_sub]
  module

/-- Literal circle crossblock exactly unitarily equivalent to the one-prime source defect. -/
def connesConsaniOnePrimeCircleSourceDefect (p : Nat.Primes) :
    Lp ℂ 2 circleLebesgue →L[ℂ] Lp ℂ 2 circleLebesgue :=
  ccmMultiplicativeCircleHardyProjection *
    connesConsaniOnePrimeCircleMultiplier p *
      (1 - ccmMultiplicativeCircleHardyProjection)

/-- Exact source-faithful full-defect Cayley transport. -/
theorem connesConsaniOnePrimeSourceDefect_circleLineCayleyUnitary
    (p : Nat.Primes) :
    (connesConsaniOnePrimeSourceDefect p).comp
        circleLineCayleyUnitary.toLinearIsometry.toContinuousLinearMap =
      circleLineCayleyUnitary.toLinearIsometry.toContinuousLinearMap.comp
        (connesConsaniOnePrimeCircleSourceDefect p) := by
  apply ContinuousLinearMap.ext
  intro f
  change (1 - ccmHardyProjection)
      (connesConsaniOnePrimeScatteringMultiplier p
        (ccmHardyProjection (circleLineCayleyUnitary f))) =
    circleLineCayleyUnitary
      (ccmMultiplicativeCircleHardyProjection
        (connesConsaniOnePrimeCircleMultiplier p
          ((1 - ccmMultiplicativeCircleHardyProjection) f)))
  have hP := DFunLike.congr_fun ccmHardyProjection_circleLineCayleyUnitary f
  change ccmHardyProjection (circleLineCayleyUnitary f) =
    circleLineCayleyUnitary ((1 - ccmMultiplicativeCircleHardyProjection) f) at hP
  rw [hP, connesConsaniOnePrimeScatteringMultiplier_eq_lineLpMultiplier,
    ← circleLineCayleyUnitary_onePrimeCircleMultiplier,
    one_sub_ccmHardyProjection_circleLineCayleyUnitary]

end

end RHTower
