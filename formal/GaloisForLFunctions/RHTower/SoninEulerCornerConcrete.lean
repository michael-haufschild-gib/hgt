import GaloisForLFunctions.RHTower.SoninAlternatingBlockStrict
import GaloisForLFunctions.RHTower.SoninEulerCornerNoncompact
import GaloisForLFunctions.RHTower.SoninL2ShellNull

noncomputable section

open MeasureTheory Set
open Filter Topology

namespace RHTower

set_option maxHeartbeats 1000000

/-! ### Concrete fixed-cutoff Sonin carrier -/
def centralPhysicalForbidden (a : ℝ) : Submodule ℂ SoninL2 :=
  physicalForbidden (Set.Icc (-a) a) measurableSet_Icc

instance centralPhysicalForbidden_hasOrthogonalProjection (a : ℝ) :
    (centralPhysicalForbidden a).HasOrthogonalProjection := by
  rw [centralPhysicalForbidden]
  infer_instance

def centralFourierForbidden (a : ℝ) : Submodule ℂ SoninL2 :=
  fourierForbidden (Set.Icc (-a) a) measurableSet_Icc

instance centralFourierForbidden_hasOrthogonalProjection (a : ℝ) :
    (centralFourierForbidden a).HasOrthogonalProjection := by
  rw [centralFourierForbidden]
  infer_instance

def centralSoninCarrier (a : ℝ) : Submodule ℂ SoninL2 :=
  (centralPhysicalForbidden a)ᗮ ⊓ (centralFourierForbidden a)ᗮ

theorem centralSoninCarrier_isClosed (a : ℝ) :
    IsClosed (centralSoninCarrier a : Set SoninL2) := by
  simpa [centralSoninCarrier] using
    (centralPhysicalForbidden a).isClosed_orthogonal.inter
      (centralFourierForbidden a).isClosed_orthogonal

instance centralSoninCarrier_completeSpace (a : ℝ) :
    CompleteSpace (centralSoninCarrier a) :=
  (centralSoninCarrier_isClosed a).completeSpace_coe

instance centralForbiddenOrthogonalInf_hasOrthogonalProjection (a : ℝ) :
    ((centralPhysicalForbidden a)ᗮ ⊓
      (centralFourierForbidden a)ᗮ).HasOrthogonalProjection := by
  change (centralSoninCarrier a).HasOrthogonalProjection
  infer_instance

instance soninL2_nontrivial : Nontrivial SoninL2 := by
  apply nontrivial_of_ne
    (evenShellVector 1 2 (by norm_num) (by norm_num) 0) 0
  intro hzero
  have hnorm := (evenShellVector_orthonormal 1 2 (by norm_num) (by norm_num)).norm_eq_one 0
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

def centralSoninProjection (a : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  (centralSoninCarrier a).starProjection

theorem centralSoninProjection_eq_soninIntersectionProjection (a : ℝ) :
    centralSoninProjection a =
      soninIntersectionProjection (centralPhysicalForbidden a) (centralFourierForbidden a) := rfl

/-- The positive one-prime Euler weight in the physical dilation model. -/
def positiveEulerDilationOperator (p : ℝ) (hp : 1 < p) :
    SoninL2 →L[ℂ] SoninL2 :=
  ((1 + p⁻¹ : ℝ) : ℂ) • (1 : SoninL2 →L[ℂ] SoninL2) +
    (-((Real.sqrt p : ℂ)⁻¹)) • dilationSum p hp

/-- The Fourier-forbidden/physical-forbidden two-factor block is compact. -/
theorem isCompactOperator_centralFourierPhysicalBlock (a : ℝ) (ha : 0 < a) :
    IsCompactOperator
      ((centralFourierForbidden a).starProjection *
        (centralPhysicalForbidden a).starProjection) := by
  change IsCompactOperator
    ((fourierForbidden (Set.Icc (-a) a) measurableSet_Icc).starProjection *
      (physicalForbidden (Set.Icc (-a) a) measurableSet_Icc).starProjection)
  rw [← fourierCutoff_eq_fourierForbidden_starProjection,
    ← indicatorCutoff_eq_physicalForbidden_starProjection]
  have hcompact := isCompactOperator_cutoffFourierCutoff (-a) a (-a) a (by linarith)
  have hpull := hcompact.clm_comp
    fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap
  simpa [fourierCutoff, cutoffFourierCutoff, Function.comp_def] using hpull

/-- The central time-frequency alternating block is a strict contraction. -/
theorem norm_centralSoninAlternatingBlock_lt_one (a : ℝ) (ha : 0 < a) :
    ‖soninAlternatingBlock (centralPhysicalForbidden a) (centralFourierForbidden a)‖ < 1 := by
  apply norm_soninAlternatingBlock_lt_one_of_compact_of_inf_eq_bot
  · exact isCompactOperator_soninAlternatingBlock_of_compact_left
      (centralPhysicalForbidden a) (centralFourierForbidden a)
      (isCompactOperator_centralFourierPhysicalBlock a ha)
  · simpa [centralPhysicalForbidden, centralFourierForbidden] using
      physicalForbidden_inf_fourierForbidden_eq_bot a

/-- The central Sonin projection asymptotically fixes the explicit symmetric shell sequence. -/
theorem centralSoninProjection_evenShellVector_tendsto
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    Tendsto (fun n =>
      ‖centralSoninProjection a
          (evenShellVector a (p * a) ha (by nlinarith) n) -
        evenShellVector a (p * a) ha (by nlinarith) n‖) atTop (𝓝 0) := by
  let A : Submodule ℂ SoninL2 := centralPhysicalForbidden a
  let B : Submodule ℂ SoninL2 := centralFourierForbidden a
  letI : (Aᗮ ⊓ Bᗮ).HasOrthogonalProjection := by
    dsimp [A, B]
    infer_instance
  have hblock : ‖soninAlternatingBlock A B‖ < 1 := by
    simpa [A, B] using norm_centralSoninAlternatingBlock_lt_one a ha
  have hgA : ∀ n, evenShellVector a (p * a) ha (by nlinarith) n ∈ Aᗮ := by
    intro n
    simpa [A, centralPhysicalForbidden] using
      evenShellVector_mem_physicalForbidden_orthogonal a p ha hp n
  have hBnull : Tendsto (fun n =>
      ‖B.starProjection (evenShellVector a (p * a) ha (by nlinarith) n)‖)
      atTop (𝓝 0) := by
    simpa [B, centralFourierForbidden] using
      fourierForbidden_starProjection_evenShellVector_tendsto_zero
        a (p * a) ha (by nlinarith)
  have h := soninIntersectionProjection_tendsto_shell A B hblock
    (evenShellVector a (p * a) ha (by nlinarith)) hgA hBnull
  rw [centralSoninProjection_eq_soninIntersectionProjection]
  simpa [A, B] using h

/-- After Sonin correction, the dilation sum still crosses the physical cutoff with norm tending
to one. -/
theorem centralPhysicalProjection_dilationSum_correctedShell_tendsto
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    Tendsto (fun n =>
      ‖(centralPhysicalForbidden a).starProjection
        (dilationSum p hp
          (centralSoninProjection a
            (evenShellVector a (p * a) ha (by nlinarith) n)))‖) atTop (𝓝 1) := by
  let A : Submodule ℂ SoninL2 := centralPhysicalForbidden a
  let W : SoninL2 →L[ℂ] SoninL2 := dilationSum p hp
  let g : ℕ → SoninL2 := evenShellVector a (p * a) ha (by nlinarith)
  have happroxNorm : Tendsto (fun n => ‖centralSoninProjection a (g n) - g n‖)
      atTop (𝓝 0) := by
    simpa [g] using centralSoninProjection_evenShellVector_tendsto a p ha hp
  have hdiffNorm : Tendsto (fun n =>
      ‖A.starProjection (W (centralSoninProjection a (g n))) -
        A.starProjection (W (g n))‖) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n =>
        ‖A.starProjection ∘L W‖ * ‖centralSoninProjection a (g n) - g n‖)
        atTop (𝓝 0) := by
      simpa using happroxNorm.const_mul ‖A.starProjection ∘L W‖
    apply squeeze_zero (fun n => norm_nonneg _) _ hupper
    intro n
    calc
      ‖A.starProjection (W (centralSoninProjection a (g n))) -
          A.starProjection (W (g n))‖ =
          ‖(A.starProjection ∘L W) (centralSoninProjection a (g n) - g n)‖ := by
            rw [map_sub]
            rfl
      _ ≤ ‖A.starProjection ∘L W‖ * ‖centralSoninProjection a (g n) - g n‖ :=
        (A.starProjection ∘L W).le_opNorm _
  apply tendsto_norm_of_norm_sub_tendsto_zero_of_norm_eq hdiffNorm
  intro n
  simpa [A, W, g, centralPhysicalForbidden,
    ← indicatorCutoff_eq_physicalForbidden_starProjection] using
      norm_physicalCutoff_dilationSum_evenShellVector a p ha hp n

/-- **Concrete fixed-cutoff Sonin Euler corner theorem.** For every positive cutoff and every
scale `p > 1`, the lower corner of `U_p + U_p*` across the common physical/Fourier Sonin cutoff is
not compact. All analytic inputs are discharged in the concrete `L²(ℝ)` model. -/
theorem centralSoninDilationCorner_not_isCompactOperator
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ¬ IsCompactOperator
      (crossBoundary (centralSoninProjection a) (dilationSum p hp) :
        SoninL2 →L[ℂ] SoninL2) := by
  let A : Submodule ℂ SoninL2 := centralPhysicalForbidden a
  let B : Submodule ℂ SoninL2 := centralFourierForbidden a
  letI : (Aᗮ ⊓ Bᗮ).HasOrthogonalProjection := by
    dsimp [A, B]
    infer_instance
  let g : ℕ → SoninL2 := evenShellVector a (p * a) ha (by nlinarith)
  have hblock : ‖soninAlternatingBlock A B‖ < 1 := by
    simpa [A, B] using norm_centralSoninAlternatingBlock_lt_one a ha
  have hg : Orthonormal ℂ g := by
    simpa [g] using evenShellVector_orthonormal a (p * a) ha (by nlinarith)
  have hgA : ∀ n, g n ∈ Aᗮ := by
    intro n
    simpa [g, A, centralPhysicalForbidden] using
      evenShellVector_mem_physicalForbidden_orthogonal a p ha hp n
  have hBnull : Tendsto (fun n => ‖B.starProjection (g n)‖) atTop (𝓝 0) := by
    simpa [g, B, centralFourierForbidden] using
      fourierForbidden_starProjection_evenShellVector_tendsto_zero
        a (p * a) ha (by nlinarith)
  have hcross : Tendsto (fun n =>
      ‖A.starProjection
        (dilationSum p hp (soninIntersectionProjection A B (g n)))‖)
      atTop (𝓝 1) := by
    have h := centralPhysicalProjection_dilationSum_correctedShell_tendsto a p ha hp
    rw [centralSoninProjection_eq_soninIntersectionProjection] at h
    simpa [A, B, g] using h
  have hsource := sonin_crossBoundary_not_isCompactOperator_of_shell
    A B hblock (dilationSum p hp) g hg hgA hBnull 1 zero_lt_one hcross
  rw [centralSoninProjection_eq_soninIntersectionProjection]
  simpa [A, B] using hsource

/-- The constant term of the positive Euler weight cannot cross the Sonin projection, so its
corner is exactly the nonzero Euler coefficient times the dilation corner. -/
theorem centralPositiveEulerCorner_eq_smul (a p : ℝ) (hp : 1 < p) :
    (crossBoundary (centralSoninProjection a) (positiveEulerDilationOperator p hp) :
        SoninL2 →L[ℂ] SoninL2) =
      (-((Real.sqrt p : ℂ)⁻¹)) •
        (crossBoundary (centralSoninProjection a) (dilationSum p hp) :
          SoninL2 →L[ℂ] SoninL2) := by
  have hQ : IsIdempotentElem (centralSoninProjection a) := by
    rw [centralSoninProjection]
    exact (centralSoninCarrier a).isIdempotentElem_starProjection
  exact crossBoundary_affine (centralSoninProjection a) hQ
    ((1 + p⁻¹ : ℝ) : ℂ) (-((Real.sqrt p : ℂ)⁻¹)) (dilationSum p hp)

/-- The concrete one-prime positive Euler metric corner is noncompact for every positive cutoff
and every scale `p > 1`. -/
theorem centralPositiveEulerCorner_not_isCompactOperator
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ¬ IsCompactOperator
      (crossBoundary (centralSoninProjection a) (positiveEulerDilationOperator p hp) :
        SoninL2 →L[ℂ] SoninL2) := by
  rw [centralPositiveEulerCorner_eq_smul]
  intro hcompact
  let b : ℂ := -((Real.sqrt p : ℂ)⁻¹)
  let T : SoninL2 →L[ℂ] SoninL2 :=
    crossBoundary (centralSoninProjection a) (dilationSum p hp)
  have hb : b ≠ 0 := by
    dsimp [b]
    simp [Real.sqrt_ne_zero'.mpr (zero_lt_one.trans hp)]
  have hcompact' : IsCompactOperator (b • T) := by
    simpa [b, T] using hcompact
  have hunscaled : IsCompactOperator (b⁻¹ • (b • T)) := hcompact'.smul b⁻¹
  have heq : b⁻¹ • (b • T) = T := by
    rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
  apply centralSoninDilationCorner_not_isCompactOperator a p ha hp
  change IsCompactOperator T
  rw [← heq]
  exact hunscaled

/-- Prime-indexed specialization of the concrete positive Euler corner theorem. -/
theorem centralPrimePositiveEulerCorner_not_isCompactOperator
    (a : ℝ) (p : ℕ) (ha : 0 < a) (hp : p.Prime) :
    ¬ IsCompactOperator
      (crossBoundary (centralSoninProjection a)
        (positiveEulerDilationOperator (p : ℝ) (by exact_mod_cast hp.one_lt)) :
        SoninL2 →L[ℂ] SoninL2) :=
  centralPositiveEulerCorner_not_isCompactOperator a (p : ℝ) ha (by
    exact_mod_cast hp.one_lt)

end RHTower
