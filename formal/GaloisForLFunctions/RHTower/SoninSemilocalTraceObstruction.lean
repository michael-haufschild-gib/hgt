/-
# Bounded-response obstruction to the projection-correction Sonin trace

The Hilbert--Schmidt pairing used in `SoninSemilocalRelativeTrace` is a legitimate finite
scalarization, but it cannot equal the von-Mangoldt source at every prime power.  Its geometric
response is uniformly bounded in the dilation scale, whereas the required static response
`log(p^m)` is unbounded already along the powers of two.

This retires the projection-correction pairing as a source trace.  It does not obstruct a genuine
semilocal trace formula whose test operator has logarithmically growing trace.
-/
import GaloisForLFunctions.RHTower.SoninSemilocalFluxSource

noncomputable section

namespace RHTower

open ContinuousLinearMap

/-- The formal-principal lower dilation corner has a scale-independent operator-norm bound. -/
theorem norm_centralSoninPrincipalDilationCorner_le
    (a p : ℝ) (hp : 1 < p) :
    ‖centralSoninPrincipalDilationCorner a p hp‖ ≤ 4 := by
  let Q₀ := centralSoninFormalComplement a
  let D := dilationSum p hp
  have hQ₀ : ‖Q₀‖ ≤ 1 := by
    simpa [Q₀] using norm_centralSoninFormalComplement_le_one a
  have hOneSubQ₀ : ‖(1 : SoninL2 →L[ℂ] SoninL2) - Q₀‖ ≤ 2 := by
    calc
      ‖(1 : SoninL2 →L[ℂ] SoninL2) - Q₀‖ ≤ ‖(1 : SoninL2 →L[ℂ] SoninL2)‖ + ‖Q₀‖ :=
        norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (by simp) hQ₀
      _ = 2 := by norm_num
  have hD : ‖D‖ ≤ 2 := by
    dsimp [D]
    apply (dilationSum p hp).opNorm_le_bound (by norm_num)
    intro f
    rw [dilationSum_apply]
    calc
      ‖dilation p (zero_lt_one.trans hp) f +
          dilation p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) f‖
          ≤ ‖dilation p (zero_lt_one.trans hp) f‖ +
            ‖dilation p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) f‖ := norm_add_le _ _
      _ = 2 * ‖f‖ := by
        rw [(dilation p (zero_lt_one.trans hp)).norm_map,
          (dilation p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp))).norm_map]
        ring
  rw [centralSoninPrincipalDilationCorner, crossBoundary]
  calc
    ‖((1 : SoninL2 →L[ℂ] SoninL2) - Q₀) * D * Q₀‖
        ≤ ‖(1 : SoninL2 →L[ℂ] SoninL2) - Q₀‖ * ‖D‖ * ‖Q₀‖ := by
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg Q₀))
    _ ≤ 2 * 2 * 1 := by
      gcongr
    _ = 4 := by norm_num

/-- The coefficient-free response of the projection-correction pairing is uniformly bounded in
the prime-power scale.  The bound depends only on the fixed Sonin cutoff. -/
theorem norm_soninSemilocalGeometricTraceResponse_le
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    ‖soninSemilocalGeometricTraceResponse a pk‖ ≤
      Real.sqrt (hsNormSq (centralSoninProjectionCorrection a)) *
        Real.sqrt (1024 * hsNormSq (centralSoninProjectionCorrection a)) := by
  let p := soninSemilocalPrimePowerScale pk
  let hp := one_lt_soninSemilocalPrimePowerScale pk
  let C := centralSoninProjectionCorrection a
  let P := centralSoninPrincipalDilationCorner a p hp
  let R := centralSoninDilationCornerResidual a p hp
  let L := centralSoninRelativeGramLinearCross a p hp
  have hC : IsHilbertSchmidt C := by
    simpa [C] using centralSoninProjectionCorrection_isHilbertSchmidt a ha
  have hR : IsHilbertSchmidt R := by
    simpa [R] using centralSoninDilationCornerResidual_isHilbertSchmidt a p ha hp
  have hL : IsHilbertSchmidt L := by
    simpa [L] using centralSoninRelativeGramLinearCross_isHilbertSchmidt a p ha hp
  have hP : ‖P‖ ≤ 4 := by
    simpa [P] using norm_centralSoninPrincipalDilationCorner_le a p hp
  have hRbound : hsNormSq R ≤ 16 * hsNormSq C := by
    simpa [R, C] using centralSoninDilationCornerResidual_hsNormSq_le a p ha hp
  have hPR : hsNormSq (ContinuousLinearMap.adjoint P * R) ≤ 16 * hsNormSq R := by
    calc
      hsNormSq (ContinuousLinearMap.adjoint P * R)
          ≤ ‖ContinuousLinearMap.adjoint P‖ ^ 2 * hsNormSq R := by
            simpa only [ContinuousLinearMap.comp_def] using
              hsNormSq_comp_left_le hR (ContinuousLinearMap.adjoint P)
      _ = ‖P‖ ^ 2 * hsNormSq R := by
        rw [(ContinuousLinearMap.adjoint :
          (SoninL2 →L[ℂ] SoninL2) ≃ₗᵢ⋆[ℂ]
            (SoninL2 →L[ℂ] SoninL2)).norm_map]
      _ ≤ 16 * hsNormSq R := by
        apply mul_le_mul_of_nonneg_right _ (hsNormSq_nonneg R)
        nlinarith [norm_nonneg P]
  have hRP : hsNormSq (ContinuousLinearMap.adjoint R * P) ≤ 16 * hsNormSq R := by
    calc
      hsNormSq (ContinuousLinearMap.adjoint R * P)
          ≤ ‖P‖ ^ 2 * hsNormSq (ContinuousLinearMap.adjoint R) := by
            simpa only [ContinuousLinearMap.comp_def] using
              hsNormSq_comp_right_le hR.adjoint P
      _ = ‖P‖ ^ 2 * hsNormSq R := by rw [hR.hsNormSq_adjoint]
      _ ≤ 16 * hsNormSq R := by
        apply mul_le_mul_of_nonneg_right _ (hsNormSq_nonneg R)
        nlinarith [norm_nonneg P]
  have hLbound : hsNormSq L ≤ 1024 * hsNormSq C := by
    rw [show L = ContinuousLinearMap.adjoint P * R +
        ContinuousLinearMap.adjoint R * P by
      rfl]
    calc
      hsNormSq (ContinuousLinearMap.adjoint P * R +
          ContinuousLinearMap.adjoint R * P)
          ≤ 2 * hsNormSq (ContinuousLinearMap.adjoint P * R) +
            2 * hsNormSq (ContinuousLinearMap.adjoint R * P) :=
              hsNormSq_add_le (hR.comp_left (ContinuousLinearMap.adjoint P))
                (hR.adjoint.comp_right P)
      _ ≤ 64 * hsNormSq R := by nlinarith
      _ ≤ 1024 * hsNormSq C := by nlinarith [hsNormSq_nonneg R]
  rw [soninSemilocalGeometricTraceResponse]
  change ‖hsInner C L‖ ≤ _
  calc
    ‖hsInner C L‖ ≤ hsNorm C * hsNorm L := norm_hsInner_le hC hL
    _ = Real.sqrt (hsNormSq C) * Real.sqrt (hsNormSq L) := rfl
    _ ≤ Real.sqrt (hsNormSq C) * Real.sqrt (1024 * hsNormSq C) := by
      gcongr
    _ = Real.sqrt (hsNormSq (centralSoninProjectionCorrection a)) *
        Real.sqrt (1024 * hsNormSq (centralSoninProjectionCorrection a)) := by
          rfl

/-- The semilocal response bound with the projection-correction energy eliminated in favor of
the two positive time--frequency overlap channels.  This is the direct semilocal consumer of the
two-projection Hilbert--Schmidt energy split. -/
theorem norm_soninSemilocalGeometricTraceResponse_le_timeBand_add_exterior
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    ‖soninSemilocalGeometricTraceResponse a pk‖ ≤
      Real.sqrt
          (hsNormSq
              ((centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection) +
            hsNormSq (centralSoninExteriorOverlap a)) *
        Real.sqrt
          (1024 *
            (hsNormSq
                ((centralFourierForbidden a).starProjection *
                  (centralPhysicalForbidden a).starProjection) +
              hsNormSq (centralSoninExteriorOverlap a))) := by
  rw [← hsNormSq_centralSoninProjectionCorrection_eq_timeBand_add_exterior a ha]
  exact norm_soninSemilocalGeometricTraceResponse_le a ha pk

/-- **The projection-correction scalarization cannot be the semilocal source trace.**  Its
uniformly bounded response cannot equal `log(p^m)` for all prime powers. -/
theorem not_soninSemilocalFluxNormalization :
    ¬ SoninSemilocalFluxNormalization := by
  intro hnorm
  let C := centralSoninProjectionCorrection 1
  let B := Real.sqrt (hsNormSq C) * Real.sqrt (1024 * hsNormSq C)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (B / Real.log 2)
  have hBN : B < (N : ℝ) * Real.log 2 := by
    rwa [div_lt_iff₀ hlog2] at hN
  let twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
  let pk : Nat.Primes × ℕ := (twoPrime, N)
  have hub := norm_soninSemilocalGeometricTraceResponse_le 1 zero_lt_one pk
  have heq := hnorm pk
  rw [heq] at hub
  have hlength : ‖soninSemilocalLogScaleLength pk‖ =
      ((N + 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [soninSemilocalLogScaleLength]
    dsimp [pk, twoPrime]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    · norm_num
    · exact mul_pos (by positivity) hlog2
  rw [hlength] at hub
  change ((N + 1 : ℕ) : ℝ) * Real.log 2 ≤ B at hub
  have hstrict : B < ((N + 1 : ℕ) : ℝ) * Real.log 2 := by
    calc
      B < (N : ℝ) * Real.log 2 := hBN
      _ < ((N + 1 : ℕ) : ℝ) * Real.log 2 := by
        norm_num
        nlinarith
  exact (not_lt_of_ge hub) hstrict

/-- Consequently, the canonical finite Sonin pairing fails to equal the finite von-Mangoldt
source on at least one compact-support prime-power test. -/
theorem exists_finiteSoninSemilocalRelativeTrace_ne_vonMangoldt :
    ∃ f : SoninPrimePowerTest,
      canonicalFiniteSoninSemilocalRelativeTrace f ≠ finiteVonMangoldtCentralTrace f := by
  by_contra h
  simp only [not_exists, not_ne_iff] at h
  exact not_soninSemilocalFluxNormalization
    (soninSemilocalFluxNormalization_iff_finiteTrace_eq_vonMangoldt.mpr h)

end RHTower
