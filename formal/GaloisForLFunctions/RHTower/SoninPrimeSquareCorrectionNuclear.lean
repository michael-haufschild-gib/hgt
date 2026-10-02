import GaloisForLFunctions.RHTower.SoninPrimeSquareTimeBandNuclear
import GaloisForLFunctions.RHTower.SoninCorrectionRightFactor
import GaloisForLFunctions.RHTower.SoninTimeBandSchatten
import GaloisForLFunctions.RHTower.SoninLudersPinching
import GaloisForLFunctions.RHTower.SoninSemilocalRelativeTrace

noncomputable section
namespace RHTower
local notation "Op" => (SoninL2 →L[ℂ] SoninL2)
local notation "S1" => SchattenOneOperator SoninL2


private def leftTraceAction {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : H →L[ℂ] H) : SchattenOneOperator H →L[ℂ] SchattenOneOperator H :=
  LinearMap.mkContinuous
    { toFun := fun T => ⟨L ∘L T.val, memSchattenClass_one_comp_left T.property L⟩
      map_add' := by
        intro S T
        apply SchattenOneOperator.ext
        apply ContinuousLinearMap.ext
        intro x
        change L (S.val x + T.val x) = L (S.val x) + L (T.val x)
        exact map_add L _ _
      map_smul' := by
        intro c T
        apply SchattenOneOperator.ext
        apply ContinuousLinearMap.ext
        intro x
        change L (c • T.val x) = c • L (T.val x)
        exact map_smul L c _ }
    ‖L‖ (fun T => traceNorm_comp_left_le T.summable L)

private def rightTraceAction {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : H →L[ℂ] H) : SchattenOneOperator H →L[ℂ] SchattenOneOperator H :=
  LinearMap.mkContinuous
    { toFun := fun T => ⟨T.val ∘L R, memSchattenClass_one_comp_right T.property R⟩
      map_add' := by intro S T; apply SchattenOneOperator.ext; rfl
      map_smul' := by intro c T; apply SchattenOneOperator.ext; rfl }
    ‖R‖ (fun T => by
      change traceNorm H (T.val ∘L R) ≤ ‖R‖ * traceNorm H T.val
      simpa only [mul_comm] using traceNorm_comp_right_le T.summable R)

private def traceAdjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    SchattenOneOperator H →ₗᵢ⋆[ℂ] SchattenOneOperator H where
  toFun T := ⟨ContinuousLinearMap.adjoint T.val,
    (memRectSchattenClass_iff_memSchattenClass 1 _).mp
      ((memRectSchattenClass_adjoint_iff 1 T.val).mpr
        ((memRectSchattenClass_iff_memSchattenClass 1 T.val).mpr T.property))⟩
  map_add' S T := by
    apply SchattenOneOperator.ext
    exact (ContinuousLinearMap.adjoint : (H →L[ℂ] H) ≃ₗᵢ⋆[ℂ] (H →L[ℂ] H)).map_add S.val T.val
  map_smul' c T := by
    apply SchattenOneOperator.ext
    exact (ContinuousLinearMap.adjoint : (H →L[ℂ] H) ≃ₗᵢ⋆[ℂ] (H →L[ℂ] H)).map_smulₛₗ c T.val
  norm_map' T := by
    change traceNorm H (ContinuousLinearMap.adjoint T.val) = traceNorm H T.val
    rw [← rectTraceNorm_eq_traceNorm, ← rectTraceNorm_eq_traceNorm, rectTraceNorm_adjoint]

private def primeSquareDilationSource (p : Nat.Primes) : Op :=
  soninLogPrimePowerCoefficient (p, 0) •
    dilationSum (soninPrimePowerScale (p, 0)) (one_lt_soninPrimePowerScale (p, 0))

private theorem source_reflection (p : Nat.Primes) (f : SoninL2) :
    primeSquareDilationSource p (l2Reflection f) =
      l2Reflection (primeSquareDilationSource p f) := by
  simp only [primeSquareDilationSource, smul_apply, map_smul, l2Reflection_dilationSum]

private theorem source_fourier_inverse (p : Nat.Primes) (f : SoninL2) :
    primeSquareDilationSource p (fourierUnitary.symm f) =
      fourierUnitary.symm (primeSquareDilationSource p f) := by
  apply fourierUnitary.injective
  simp only [primeSquareDilationSource, smul_apply, map_smul,
    fourierUnitary_dilationSum, fourierUnitary.apply_symm_apply]

private theorem source_adjoint (p : Nat.Primes) :
    ContinuousLinearMap.adjoint (primeSquareDilationSource p) = primeSquareDilationSource p := by
  rw [primeSquareDilationSource, soninLogPrimePowerCoefficient_primeSquare]
  rw [(ContinuousLinearMap.adjoint : Op ≃ₗᵢ⋆[ℂ] Op).map_smulₛₗ]
  rw [Complex.conj_ofReal, adjoint_dilationSum_eq_self]

/-- The original weighted residual bundled with its proved trace-class membership. -/
def soninWeightedPrimePowerNuclearSource (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) : S1 :=
  ⟨centralSoninWeightedPrimePowerResidual a pk,
    (centralSoninWeightedPrimePowerResidual_mem_timeBandIdeal a ha pk).memSchattenClass_one⟩

/-- The original prime-square source acting on the exact projection correction. -/
def soninPrimeSquareCorrectionLeftSource (a : ℝ) (ha : 0 < a) (p : Nat.Primes) : S1 :=
  ⟨primeSquareDilationSource p ∘L centralSoninProjectionCorrection a,
    memSchattenClass_one_comp_left
      (centralSoninProjectionCorrection_memSchattenClass_one a ha) _⟩

private theorem source_right_factor_algebra {M : Type*} [Ring M]
    (A B J W F U R K X : M)
    (hJ : J = A * B * (1 - A * W) + B * A * W)
    (hAB : A * B = R * K * F) (hBA : B * A = U * K)
    (hXR : X * R = R * X) (hXU : X * U = U * X) :
    R * (X * K) * (F * (1 - A * W)) + U * (X * K) * W = X * J := by
  rw [hJ, hAB, hBA]
  calc
    _ = (X * R) * K * (F * (1 - A * W)) + (X * U) * K * W := by
      rw [hXR, hXU]
      noncomm_ring
    _ = _ := by noncomm_ring

private theorem timeBand_cutoff_left_factor (a : ℝ) (ha : 0 < a) :
    fourierCutoff (centralInterval a) (measurableSet_centralInterval a) *
      indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) =
    fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap *
      fullTimeBandFourier (-a) a (-a) a (neg_le_self ha.le) := by
  apply ContinuousLinearMap.ext
  intro f
  have hk := congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T f)
    (fullTimeBandFourier_eq_cutoffFourierCutoff (-a) a (-a) a (neg_le_self ha.le))
  change fullTimeBandFourier (-a) a (-a) a (neg_le_self ha.le) f =
    indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (fourierUnitary (indicatorCutoff (centralInterval a)
        (measurableSet_centralInterval a) f)) at hk
  change fourierCutoff (centralInterval a) (measurableSet_centralInterval a)
      (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f) =
    fourierUnitary.symm (fullTimeBandFourier (-a) a (-a) a (neg_le_self ha.le) f)
  rw [fourierCutoff_apply]
  exact congrArg fourierUnitary.symm hk.symm

/-- The actual correction's right factors preserve the admitted unsquared
prime-square source, with no regularity premise on the resolvent. -/
theorem summable_soninPrimeSquareCorrectionLeftSource (a : ℝ) (ha : 0 < a) :
    Summable (soninPrimeSquareCorrectionLeftSource a ha) := by
  let A : Op := indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
  let B : Op := fourierCutoff (centralInterval a) (measurableSet_centralInterval a)
  let W := soninCorrectionSourceRightFactor a ha
  let F : Op := fourierUnitary.toLinearIsometry.toContinuousLinearMap
  let U : Op := fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap
  let R : Op := l2Reflection
  let K := fullTimeBandFourier (-a) a (-a) a (neg_le_self ha.le)
  let X := soninPrimeSquareTimeBandSource a (-a) a ha.le
  have hBA : B * A = U * K := timeBand_cutoff_left_factor a ha
  have hAB : A * B = R * K * F := by
    apply ContinuousLinearMap.ext
    intro f
    change A (fourierUnitary.symm (A (fourierUnitary f))) = R (K (F f))
    rw [fourierUnitary_symm_eq_reflection_fourier]
    change indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (l2Reflection (fourierUnitary (A (fourierUnitary f)))) = _
    rw [← l2Reflection_indicatorCutoff_central]
    dsimp only [K]
    rw [fullTimeBandFourier_eq_cutoffFourierCutoff]
    rfl
  have hJ : centralSoninProjectionCorrection a = A * B * (1 - A * W) + B * A * W := by
    dsimp only [A, B]
    rw [indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection]
    exact centralSoninProjectionCorrection_eq_timeBand_rightFactors a ha
  have hX : Summable X := summable_soninPrimeSquareTimeBandSource a (-a) a ha.le
  have hL := (rightTraceAction (F * (1 - A * W))).summable
    ((leftTraceAction R).summable hX)
  have hR := (rightTraceAction W).summable ((leftTraceAction U).summable hX)
  apply (hL.add hR).congr
  intro p
  apply SchattenOneOperator.ext
  change R * (primeSquareDilationSource p * K) * (F * (1 - A * W)) +
      U * (primeSquareDilationSource p * K) * W =
        primeSquareDilationSource p * centralSoninProjectionCorrection a
  have hDR : primeSquareDilationSource p * R = R * primeSquareDilationSource p := by
    apply ContinuousLinearMap.ext
    intro f
    exact source_reflection p f
  have hDU : primeSquareDilationSource p * U = U * primeSquareDilationSource p := by
    apply ContinuousLinearMap.ext
    intro f
    exact source_fourier_inverse p f
  exact source_right_factor_algebra A B _ W F U R K
    (primeSquareDilationSource p) hJ hAB hBA hDR hDU

/-- Both exact correction-response legs of the original prime-square mode
assemble unconditionally in trace norm. -/
theorem summable_soninPrimeSquareNuclearResidual (a : ℝ) (ha : 0 < a) :
    Summable (fun p : Nat.Primes => soninWeightedPrimePowerNuclearSource a ha (p, 0)) := by
  have hY := summable_soninPrimeSquareCorrectionLeftSource a ha
  have hL := (leftTraceAction (1 - centralSoninProjection a)).summable hY
  have hR := (rightTraceAction (centralSoninFormalComplement a)).summable
    ((traceAdjoint (H := SoninL2)).toContinuousLinearMap.summable hY)
  apply (hL.sub hR).congr
  intro p
  apply SchattenOneOperator.ext
  change (1 - centralSoninProjection a) *
      (primeSquareDilationSource p * centralSoninProjectionCorrection a) -
      ContinuousLinearMap.adjoint
        (primeSquareDilationSource p * centralSoninProjectionCorrection a) *
        centralSoninFormalComplement a = centralSoninWeightedPrimePowerResidual a (p, 0)
  rw [adjoint_mul_soninL2, adjoint_centralSoninProjectionCorrection, source_adjoint]
  rw [centralSoninWeightedPrimePowerResidual, centralSoninPrimePowerResidual,
    centralSoninDilationCornerResidual_eq_correction_factorization]
  dsimp only [primeSquareDilationSource]
  simp only [smul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc]

end RHTower

