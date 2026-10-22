import GaloisForLFunctions.RHTower.CauchyTransformHardy
import GaloisForLFunctions.RHTower.HardyBlaschkeMultiplier
import GaloisForLFunctions.RHTower.Suzuki.SuzukiModelSpaceOrthogonal

open Complex Filter Topology MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

abbrev RealLineL2 := Lp ℂ 2 (volume : Measure ℝ)
abbrev UpperHardyL2 := RHTower.hardyL2
abbrev LowerHardyL2 := RHTower.hardyL2ᗮ

local instance hardyHorizontalLayerLeakageLocalInst1 : CompleteSpace UpperHardyL2 :=
  RHTower.isClosed_hardyL2.completeSpace_coe

local instance hardyHorizontalLayerLeakageLocalInst2 : CompleteSpace LowerHardyL2 :=
  RHTower.hardyL2.isClosed_orthogonal.completeSpace_coe

/-- Actual anti-causal Hardy compression `P₋ M|H²₊` of a bounded whole-line operator. -/
def hardyLeakage (M : RealLineL2 →L[ℂ] RealLineL2) :
    UpperHardyL2 →L[ℂ] LowerHardyL2 :=
  LowerHardyL2.orthogonalProjectionOnto.comp
    (M.comp UpperHardyL2.subtypeL)

theorem hardyLeakage_id :
    hardyLeakage (ContinuousLinearMap.id ℂ RealLineL2) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  change LowerHardyL2.orthogonalProjectionOnto (f : RealLineL2) = 0
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
  rw [show LowerHardyL2ᗮ = RHTower.hardyL2 by
    exact Submodule.orthogonal_orthogonal RHTower.hardyL2]
  exact f.property

/-- The upper-half-plane Cauchy atom, in the lower Hardy space. -/
def upperCauchyFeature (a : ℝ) (ha : 0 < a) : LowerHardyL2 :=
  let w : ℂ := (a : ℂ) * I
  have hw : 0 < w.im := by simp [w, ha]
  ⟨(RHTower.memLp_cauchyKernel (ne_of_gt hw)).toLp
      (fun x : ℝ => (((x : ℝ) : ℂ) - w)⁻¹),
    RHTower.cauchyKernel_mem_hardyL2_orthogonal hw⟩

/-- The lower-half-plane Cauchy atom, in the upper Hardy space. -/
def lowerCauchyFeature (a : ℝ) (ha : 0 < a) : UpperHardyL2 :=
  let w : ℂ := -(a : ℂ) * I
  have hw : w.im < 0 := by simp [w, ha]
  ⟨(RHTower.memLp_cauchyKernel (ne_of_lt hw)).toLp
      (fun x : ℝ => (((x : ℝ) : ℂ) - w)⁻¹),
    RHTower.cauchyKernel_mem_hardyL2 hw⟩

theorem coe_upperCauchyFeature {a : ℝ} (ha : 0 < a) :
    ((((upperCauchyFeature a ha : LowerHardyL2) : RealLineL2) : ℝ → ℂ))
      =ᵐ[volume] fun x : ℝ => (((x : ℝ) : ℂ) - (a : ℂ) * I)⁻¹ := by
  simpa [upperCauchyFeature] using
    (RHTower.memLp_cauchyKernel
      (show ((a : ℂ) * I).im ≠ 0 by simpa using ne_of_gt ha)).coeFn_toLp

theorem coe_lowerCauchyFeature {a : ℝ} (ha : 0 < a) :
    ((((lowerCauchyFeature a ha : UpperHardyL2) : RealLineL2) : ℝ → ℂ))
      =ᵐ[volume] fun x : ℝ => (((x : ℝ) : ℂ) + (a : ℂ) * I)⁻¹ := by
  simpa [lowerCauchyFeature, sub_eq_add_neg] using
    (RHTower.memLp_cauchyKernel
      (show (-(a : ℂ) * I).im ≠ 0 by simpa using ne_of_gt ha)).coeFn_toLp

/-- The Hardy inner product with a lower Cauchy atom is its upper Cauchy transform. -/
theorem inner_lowerCauchyFeature {a : ℝ} (ha : 0 < a) (f : UpperHardyL2) :
    inner ℂ (lowerCauchyFeature a ha) f =
      ∫ x : ℝ, ((f : RealLineL2) : ℝ → ℂ) x /
        (((x : ℝ) : ℂ) - (a : ℂ) * I) := by
  rw [UpperHardyL2.coe_inner, MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [coe_lowerCauchyFeature ha] with x hx
  rw [RCLike.inner_apply, hx, map_inv₀, div_eq_mul_inv, map_add, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  have hstar : (starRingEnd ℂ) (a : ℂ) = (a : ℂ) := by
    apply Complex.ext <;> simp
  rw [hstar]
  ring

/-- The Cauchy atom at height `a` has squared norm `π/a`. -/
theorem inner_lowerCauchyFeature_self {a : ℝ} (ha : 0 < a) :
    inner ℂ (lowerCauchyFeature a ha) (lowerCauchyFeature a ha) =
      ((Real.pi / a : ℝ) : ℂ) := by
  rw [inner_lowerCauchyFeature]
  have hpair := integral_cauchyPair (w := (a : ℂ) * I) (by simpa using ha)
  calc
    (∫ x : ℝ, ((lowerCauchyFeature a ha : UpperHardyL2) : RealLineL2) x /
        (((x : ℝ) : ℂ) - (a : ℂ) * I)) =
        ∫ x : ℝ, ((((x : ℝ) : ℂ) + (a : ℂ) * I)⁻¹) /
          (((x : ℝ) : ℂ) - (a : ℂ) * I) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [coe_lowerCauchyFeature ha] with x hx
      rw [hx]
    _ = ∫ x : ℝ, ((((x : ℂ) - (a : ℂ) * I) *
          ((x : ℂ) - starRingEnd ℂ ((a : ℂ) * I)))⁻¹) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [mul_inv_rev]
      simp [div_eq_mul_inv, map_mul]
    _ = ((Real.pi / a : ℝ) : ℂ) := by simpa using hpair

/-- Boundary derivative of one matched half-plane Blaschke pair. -/
def infinitesimalBlaschkeSymbol (a : ℝ) (x : ℝ) : ℂ :=
  (-2 * I) / (((x : ℝ) : ℂ) - (a : ℂ) * I)

theorem measurable_infinitesimalBlaschkeSymbol (a : ℝ) :
    Measurable (infinitesimalBlaschkeSymbol a) := by
  unfold infinitesimalBlaschkeSymbol
  fun_prop

theorem norm_infinitesimalBlaschkeSymbol_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ‖infinitesimalBlaschkeSymbol a x‖ ≤ 2 / a := by
  rw [infinitesimalBlaschkeSymbol, norm_div]
  have hden : a ≤ ‖((x : ℝ) : ℂ) - (a : ℂ) * I‖ := by
    rw [Complex.norm_def]
    simp [Complex.normSq_apply]
    change a ≤ Real.sqrt (x * x + a * a)
    have hs := Real.sq_sqrt
      (add_nonneg (mul_self_nonneg x) (mul_self_nonneg a))
    have hsnn := Real.sqrt_nonneg (x * x + a * a)
    nlinarith [mul_self_nonneg x]
  norm_num [norm_mul]
  gcongr

/-- Whole-line multiplication by the one-layer infinitesimal Blaschke symbol. -/
def infinitesimalBlaschkeMul (a : ℝ) (ha : 0 < a) :
    RealLineL2 →L[ℂ] RealLineL2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (measurable_infinitesimalBlaschkeSymbol a) (by positivity)
    (norm_infinitesimalBlaschkeSymbol_le ha)

theorem coeFn_infinitesimalBlaschkeMul {a : ℝ} (ha : 0 < a) (f : RealLineL2) :
    ((infinitesimalBlaschkeMul a ha f : RealLineL2) : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => infinitesimalBlaschkeSymbol a x * (f : ℝ → ℂ) x := by
  unfold infinitesimalBlaschkeMul
  exact lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    (measurable_infinitesimalBlaschkeSymbol a) (by positivity)
    (norm_infinitesimalBlaschkeSymbol_le ha) f

theorem infinitesimalBlaschkeSymbol_eq_blaschkeDiff {a : ℝ} (ha : 0 < a) (x : ℝ) :
    infinitesimalBlaschkeSymbol a x =
      (-(a : ℂ)⁻¹) * (RHTower.blaschkeSymbol ((a : ℂ) * I) x - 1) := by
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ha)
  have hw : (((a : ℂ) * I).im) ≠ 0 := by simpa using ne_of_gt ha
  have hx := RHTower.ofReal_sub_ne_zero hw x
  have hstar : (starRingEnd ℂ) ((a : ℂ) * I) = -(a : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [infinitesimalBlaschkeSymbol, RHTower.blaschkeSymbol, hstar]
  let d : ℂ := (x : ℂ) - (a : ℂ) * I
  let n : ℂ := (x : ℂ) - -(a : ℂ) * I
  have hd : d ≠ 0 := by simpa [d] using hx
  have hdinv : d * d⁻¹ = 1 := mul_inv_cancel₀ hd
  have hndiff : n - d = 2 * (a : ℂ) * I := by
    simp only [n, d]
    ring
  have hfrac :
      (n / d - 1) =
        (2 * (a : ℂ) * I) * d⁻¹ := by
    rw [div_eq_mul_inv, ← hdinv]
    calc
      n * d⁻¹ - d * d⁻¹ = (n - d) * d⁻¹ := by ring
      _ = (2 * (a : ℂ) * I) * d⁻¹ := by rw [hndiff]
  have hcoeff :
      (-(a : ℂ)⁻¹) * (2 * (a : ℂ) * I) = -2 * I := by
    calc
      (-(a : ℂ)⁻¹) * (2 * (a : ℂ) * I) =
          -(2 * ((a : ℂ)⁻¹ * (a : ℂ)) * I) := by ring
      _ = -2 * I := by rw [inv_mul_cancel₀ ha0]; ring
  change (-2 * I) / d = (-(a : ℂ)⁻¹) * (n / d - 1)
  rw [hfrac, ← mul_assoc, hcoeff, div_eq_mul_inv]

theorem infinitesimalBlaschkeMul_apply_eq_blaschkeDiff {a : ℝ} (ha : 0 < a)
    (f : RealLineL2) :
    infinitesimalBlaschkeMul a ha f =
      (-(a : ℂ)⁻¹) • (RHTower.blaschkeMul ((a : ℂ) * I) f - f) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_infinitesimalBlaschkeMul ha f,
    RHTower.coeFn_blaschkeMul ((a : ℂ) * I) f,
    MeasureTheory.Lp.coeFn_sub (RHTower.blaschkeMul ((a : ℂ) * I) f) f,
    MeasureTheory.Lp.coeFn_smul (-(a : ℂ)⁻¹)
      (RHTower.blaschkeMul ((a : ℂ) * I) f - f)] with x hM hB hsub hsmul
  rw [hM, hsmul, Pi.smul_apply, smul_eq_mul, hsub, Pi.sub_apply, hB,
    infinitesimalBlaschkeSymbol_eq_blaschkeDiff ha]
  ring

theorem blaschkeMul_lowerCauchyFeature {a : ℝ} (ha : 0 < a) :
    RHTower.blaschkeMul ((a : ℂ) * I)
        ((lowerCauchyFeature a ha : UpperHardyL2) : RealLineL2) =
      ((upperCauchyFeature a ha : LowerHardyL2) : RealLineL2) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [RHTower.coeFn_blaschkeMul ((a : ℂ) * I)
      ((lowerCauchyFeature a ha : UpperHardyL2) : RealLineL2),
    coe_lowerCauchyFeature ha, coe_upperCauchyFeature ha] with x hB hl hu
  rw [hB, hl, hu, RHTower.blaschkeSymbol]
  have hp : ((x : ℂ) - (a : ℂ) * I) ≠ 0 :=
    RHTower.ofReal_sub_ne_zero (by simpa using ne_of_gt ha) x
  have hm : ((x : ℂ) + (a : ℂ) * I) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hstar : (starRingEnd ℂ) ((a : ℂ) * I) = -(a : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hstar]
  field_simp
  ring

theorem infinitesimalBlaschkeMul_lowerCauchyFeature {a : ℝ} (ha : 0 < a) :
    infinitesimalBlaschkeMul a ha
        ((lowerCauchyFeature a ha : UpperHardyL2) : RealLineL2) =
      (a : ℂ)⁻¹ • ((lowerCauchyFeature a ha : UpperHardyL2) : RealLineL2) -
        (a : ℂ)⁻¹ • ((upperCauchyFeature a ha : LowerHardyL2) : RealLineL2) := by
  rw [infinitesimalBlaschkeMul_apply_eq_blaschkeDiff ha,
    blaschkeMul_lowerCauchyFeature ha]
  module

/-- Remove the unique Cauchy-evaluation component at height `a`. -/
def cauchyZeroRemainder {a : ℝ} (ha : 0 < a) (f : UpperHardyL2) : UpperHardyL2 :=
  f - ((a : ℂ) * (Real.pi : ℂ)⁻¹ * inner ℂ (lowerCauchyFeature a ha) f) •
    lowerCauchyFeature a ha

theorem inner_lowerCauchyFeature_cauchyZeroRemainder {a : ℝ} (ha : 0 < a)
    (f : UpperHardyL2) :
    inner ℂ (lowerCauchyFeature a ha) (cauchyZeroRemainder ha f) = 0 := by
  rw [cauchyZeroRemainder, inner_sub_right,
    inner_smul_right (lowerCauchyFeature a ha) (lowerCauchyFeature a ha),
    inner_lowerCauchyFeature_self ha]
  let q : ℂ := inner ℂ (lowerCauchyFeature a ha) f
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ha)
  have hpi0 : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hscale :
      ((a : ℂ) * (Real.pi : ℂ)⁻¹) * ((Real.pi / a : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [ha0, hpi0]
  have hcancel :
      ((a : ℂ) * (Real.pi : ℂ)⁻¹ * q) * ((Real.pi / a : ℝ) : ℂ) = q := by
    calc
      ((a : ℂ) * (Real.pi : ℂ)⁻¹ * q) * ((Real.pi / a : ℝ) : ℂ) =
          (((a : ℂ) * (Real.pi : ℂ)⁻¹) * ((Real.pi / a : ℝ) : ℂ)) * q := by ring
      _ = q := by rw [hscale, one_mul]
  change q - ((a : ℂ) * (Real.pi : ℂ)⁻¹ * q) *
    ((Real.pi / a : ℝ) : ℂ) = 0
  rw [hcancel, sub_self]

theorem integral_cauchyZeroRemainder {a : ℝ} (ha : 0 < a) (f : UpperHardyL2) :
    (∫ x : ℝ, (((cauchyZeroRemainder ha f : UpperHardyL2) : RealLineL2) : ℝ → ℂ) x /
      (((x : ℝ) : ℂ) - (a : ℂ) * I)) = 0 := by
  rw [← inner_lowerCauchyFeature ha]
  exact inner_lowerCauchyFeature_cauchyZeroRemainder ha f

/-- Division of the Cauchy-zero remainder by its upper-half-plane zero remains Hardy. -/
def blaschkeCauchyZeroQuotient {a : ℝ} (ha : 0 < a)
    (f : UpperHardyL2) : UpperHardyL2 :=
  ⟨RHTower.blaschkeMul ((a : ℂ) * I)
      ((cauchyZeroRemainder ha f : UpperHardyL2) : RealLineL2),
    RHTower.blaschkeMul_mem_hardyL2 (by simpa using ha)
      (cauchyZeroRemainder ha f).property (integral_cauchyZeroRemainder ha f)⟩

/-- The Hardy component left after isolating the unique anti-Hardy Cauchy atom. -/
def infinitesimalBlaschkeUpperPart {a : ℝ} (ha : 0 < a)
    (f : UpperHardyL2) : UpperHardyL2 :=
  (-(a : ℂ)⁻¹) • (blaschkeCauchyZeroQuotient ha f - cauchyZeroRemainder ha f) +
    ((Real.pi : ℂ)⁻¹ * inner ℂ (lowerCauchyFeature a ha) f) •
      lowerCauchyFeature a ha

/-- Exact ambient Hardy/anti-Hardy split of the infinitesimal Blaschke multiplier. -/
theorem infinitesimalBlaschkeMul_decomposition {a : ℝ} (ha : 0 < a)
    (f : UpperHardyL2) :
    infinitesimalBlaschkeMul a ha ((f : UpperHardyL2) : RealLineL2) =
      ((infinitesimalBlaschkeUpperPart ha f : UpperHardyL2) : RealLineL2) +
        (-(Real.pi : ℂ)⁻¹ * inner ℂ (lowerCauchyFeature a ha) f) •
          ((upperCauchyFeature a ha : LowerHardyL2) : RealLineL2) := by
  let q : ℂ := inner ℂ (lowerCauchyFeature a ha) f
  let c : ℂ := (a : ℂ) * (Real.pi : ℂ)⁻¹ * q
  have hf :
      ((f : UpperHardyL2) : RealLineL2) =
        ((cauchyZeroRemainder ha f : UpperHardyL2) : RealLineL2) +
          c • ((lowerCauchyFeature a ha : UpperHardyL2) : RealLineL2) := by
    change ((f : UpperHardyL2) : RealLineL2) =
      ((((f - c • lowerCauchyFeature a ha) +
        c • lowerCauchyFeature a ha : UpperHardyL2) : UpperHardyL2) : RealLineL2)
    exact congrArg (fun u : UpperHardyL2 => (u : RealLineL2))
      (sub_add_cancel f (c • lowerCauchyFeature a ha)).symm
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ha)
  have hcoeff : c * (a : ℂ)⁻¹ = (Real.pi : ℂ)⁻¹ * q := by
    calc
      c * (a : ℂ)⁻¹ =
          ((a : ℂ) * (a : ℂ)⁻¹) * ((Real.pi : ℂ)⁻¹ * q) := by
            simp only [c]
            ring
      _ = (Real.pi : ℂ)⁻¹ * q := by rw [mul_inv_cancel₀ ha0, one_mul]
  rw [hf, map_add, map_smul,
    infinitesimalBlaschkeMul_apply_eq_blaschkeDiff ha,
    infinitesimalBlaschkeMul_lowerCauchyFeature ha]
  change
    (-(a : ℂ)⁻¹) •
        (((blaschkeCauchyZeroQuotient ha f : UpperHardyL2) : RealLineL2) -
          ((cauchyZeroRemainder ha f : UpperHardyL2) : RealLineL2)) +
      c • ((a : ℂ)⁻¹ •
          ((lowerCauchyFeature a ha : UpperHardyL2) : RealLineL2) -
        (a : ℂ)⁻¹ •
          ((upperCauchyFeature a ha : LowerHardyL2) : RealLineL2)) =
      (-(a : ℂ)⁻¹) •
          (((blaschkeCauchyZeroQuotient ha f : UpperHardyL2) : RealLineL2) -
            ((cauchyZeroRemainder ha f : UpperHardyL2) : RealLineL2)) +
        ((Real.pi : ℂ)⁻¹ * q) •
          ((lowerCauchyFeature a ha : UpperHardyL2) : RealLineL2) +
      (-(Real.pi : ℂ)⁻¹ * q) •
        ((upperCauchyFeature a ha : LowerHardyL2) : RealLineL2)
  simp only [smul_sub, smul_smul, hcoeff]
  module

/-- The genuine Hardy compression of one infinitesimal Blaschke layer is rank one. -/
theorem hardyLeakage_infinitesimalBlaschkeMul {a : ℝ} (ha : 0 < a) :
    hardyLeakage (infinitesimalBlaschkeMul a ha) =
      (-(Real.pi : ℂ)⁻¹) •
        InnerProductSpace.rankOne ℂ (upperCauchyFeature a ha)
          (lowerCauchyFeature a ha) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  change inner ℂ g
      (LowerHardyL2.orthogonalProjectionOnto
        (infinitesimalBlaschkeMul a ha
          ((f : UpperHardyL2) : RealLineL2))) =
    inner ℂ g
      ((((-(Real.pi : ℂ)⁻¹) •
        InnerProductSpace.rankOne ℂ (upperCauchyFeature a ha)
          (lowerCauchyFeature a ha)) : UpperHardyL2 →L[ℂ] LowerHardyL2) f)
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have horth :
      inner ℂ ((g : LowerHardyL2) : RealLineL2)
        ((infinitesimalBlaschkeUpperPart ha f : UpperHardyL2) : RealLineL2) = 0 :=
    inner_eq_zero_symm.mp
      ((Submodule.mem_orthogonal RHTower.hardyL2
        ((g : LowerHardyL2) : RealLineL2)).mp g.property
          ((infinitesimalBlaschkeUpperPart ha f : UpperHardyL2) : RealLineL2)
          (infinitesimalBlaschkeUpperPart ha f).property)
  let r : ℂ := -(Real.pi : ℂ)⁻¹ *
    inner ℂ (lowerCauchyFeature a ha) f
  have hrank :
      ((((-(Real.pi : ℂ)⁻¹) •
        InnerProductSpace.rankOne ℂ (upperCauchyFeature a ha)
          (lowerCauchyFeature a ha)) : UpperHardyL2 →L[ℂ] LowerHardyL2) f) =
        r • upperCauchyFeature a ha := by
    rw [smul_apply, InnerProductSpace.rankOne_apply, smul_smul]
  calc
    inner ℂ ((g : LowerHardyL2) : RealLineL2)
        (infinitesimalBlaschkeMul a ha
          ((f : UpperHardyL2) : RealLineL2)) =
      inner ℂ ((g : LowerHardyL2) : RealLineL2)
        (((infinitesimalBlaschkeUpperPart ha f : UpperHardyL2) : RealLineL2) +
          r •
            ((upperCauchyFeature a ha : LowerHardyL2) : RealLineL2)) :=
      congrArg (fun v : RealLineL2 =>
        inner ℂ ((g : LowerHardyL2) : RealLineL2) v)
        (by simpa only [r] using infinitesimalBlaschkeMul_decomposition ha f)
    _ = inner ℂ ((g : LowerHardyL2) : RealLineL2)
        (r • ((upperCauchyFeature a ha : LowerHardyL2) : RealLineL2)) := by
      rw [inner_add_right, horth, zero_add]
    _ = inner ℂ g (r • upperCauchyFeature a ha) :=
      (LowerHardyL2.coe_inner g (r • upperCauchyFeature a ha)).symm
    _ = inner ℂ g
        ((((-(Real.pi : ℂ)⁻¹) •
          InnerProductSpace.rankOne ℂ (upperCauchyFeature a ha)
            (lowerCauchyFeature a ha)) : UpperHardyL2 →L[ℂ] LowerHardyL2) f) :=
      congrArg (fun v : LowerHardyL2 => inner ℂ g v) hrank.symm

/-- Analytic companion in the full derivative of a matched Blaschke pair. -/
def infinitesimalBlaschkeInvSymbol (a : ℝ) (x : ℝ) : ℂ :=
  (-2 * I) / (((x : ℝ) : ℂ) + (a : ℂ) * I)

theorem infinitesimalBlaschkeInvSymbol_eq_blaschkeInvDiff {a : ℝ} (ha : 0 < a)
    (x : ℝ) :
    infinitesimalBlaschkeInvSymbol a x =
      (a : ℂ)⁻¹ * (RHTower.blaschkeSymbolInv ((a : ℂ) * I) x - 1) := by
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hden : ((x : ℂ) + (a : ℂ) * I) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hstar : (starRingEnd ℂ) ((a : ℂ) * I) = -(a : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [infinitesimalBlaschkeInvSymbol, RHTower.blaschkeSymbolInv, hstar]
  let d : ℂ := (x : ℂ) + (a : ℂ) * I
  let n : ℂ := (x : ℂ) - (a : ℂ) * I
  have hd : d ≠ 0 := by simpa [d] using hden
  have hdinv : d * d⁻¹ = 1 := mul_inv_cancel₀ hd
  have hndiff : n - d = -2 * (a : ℂ) * I := by
    simp only [n, d]
    ring
  have hfrac : n / d - 1 = (-2 * (a : ℂ) * I) * d⁻¹ := by
    rw [div_eq_mul_inv, ← hdinv]
    calc
      n * d⁻¹ - d * d⁻¹ = (n - d) * d⁻¹ := by ring
      _ = (-2 * (a : ℂ) * I) * d⁻¹ := by rw [hndiff]
  have hcoeff : (a : ℂ)⁻¹ * (-2 * (a : ℂ) * I) = -2 * I := by
    calc
      (a : ℂ)⁻¹ * (-2 * (a : ℂ) * I) =
          -2 * ((a : ℂ)⁻¹ * (a : ℂ)) * I := by ring
      _ = -2 * I := by rw [inv_mul_cancel₀ ha0, mul_one]
  rw [show (x : ℂ) - -(a : ℂ) * I = d by simp [d]]
  change (-2 * I) / d = (a : ℂ)⁻¹ * (n / d - 1)
  rw [hfrac, ← mul_assoc, hcoeff, div_eq_mul_inv]

/-- Whole-line multiplier by the analytic companion symbol. -/
def infinitesimalBlaschkeInvMul (a : ℝ) :
    RealLineL2 →L[ℂ] RealLineL2 :=
  (a : ℂ)⁻¹ •
    (RHTower.blaschkeMulInv ((a : ℂ) * I) - ContinuousLinearMap.id ℂ RealLineL2)

theorem coeFn_infinitesimalBlaschkeInvMul {a : ℝ} (ha : 0 < a) (f : RealLineL2) :
    ((infinitesimalBlaschkeInvMul a f : RealLineL2) : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => infinitesimalBlaschkeInvSymbol a x * (f : ℝ → ℂ) x := by
  filter_upwards [RHTower.coeFn_blaschkeMulInv ((a : ℂ) * I) f,
    MeasureTheory.Lp.coeFn_sub (RHTower.blaschkeMulInv ((a : ℂ) * I) f) f,
    MeasureTheory.Lp.coeFn_smul (a : ℂ)⁻¹
      (RHTower.blaschkeMulInv ((a : ℂ) * I) f - f)] with x hB hsub hsmul
  rw [infinitesimalBlaschkeInvMul, smul_apply, sub_apply,
    ContinuousLinearMap.id_apply, hsmul, Pi.smul_apply, smul_eq_mul, hsub,
    Pi.sub_apply, hB, infinitesimalBlaschkeInvSymbol_eq_blaschkeInvDiff ha]
  ring

theorem infinitesimalBlaschkeInvMul_mem_hardyL2 {a : ℝ} (ha : 0 < a)
    (f : UpperHardyL2) :
    infinitesimalBlaschkeInvMul a ((f : UpperHardyL2) : RealLineL2) ∈
      RHTower.hardyL2 := by
  change (a : ℂ)⁻¹ •
      (RHTower.blaschkeMulInv ((a : ℂ) * I)
          ((f : UpperHardyL2) : RealLineL2) -
        ((f : UpperHardyL2) : RealLineL2)) ∈ RHTower.hardyL2
  exact RHTower.hardyL2.smul_mem _
    (RHTower.hardyL2.sub_mem
      (RHTower.blaschkeMulInv_mem_hardyL2 (by simpa using ha) f.property) f.property)

theorem hardyLeakage_infinitesimalBlaschkeInvMul {a : ℝ} (ha : 0 < a) :
    hardyLeakage (infinitesimalBlaschkeInvMul a) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  change LowerHardyL2.orthogonalProjectionOnto
      (infinitesimalBlaschkeInvMul a ((f : UpperHardyL2) : RealLineL2)) = 0
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
  rw [show LowerHardyL2ᗮ = RHTower.hardyL2 by
    exact Submodule.orthogonal_orthogonal RHTower.hardyL2]
  exact infinitesimalBlaschkeInvMul_mem_hardyL2 ha f

theorem hardyLeakage_add (M N : RealLineL2 →L[ℂ] RealLineL2) :
    hardyLeakage (M + N) = hardyLeakage M + hardyLeakage N := by
  ext f
  simp [hardyLeakage]

theorem hardyLeakage_smul (c : ℂ) (M : RealLineL2 →L[ℂ] RealLineL2) :
    hardyLeakage (c • M) = c • hardyLeakage M := by
  ext f
  simp [hardyLeakage]

theorem norm_hardyLeakage_le (M : RealLineL2 →L[ℂ] RealLineL2) :
    ‖hardyLeakage M‖ ≤ ‖M‖ := by
  have hsub : ‖UpperHardyL2.subtypeL‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound UpperHardyL2.subtypeL (by norm_num)
    intro f
    simp
  have hinner : ‖M.comp UpperHardyL2.subtypeL‖ ≤ ‖M‖ := by
    calc
      ‖M.comp UpperHardyL2.subtypeL‖ ≤ ‖M‖ * ‖UpperHardyL2.subtypeL‖ :=
        ContinuousLinearMap.opNorm_comp_le M UpperHardyL2.subtypeL
      _ ≤ ‖M‖ * 1 := mul_le_mul_of_nonneg_left hsub (norm_nonneg M)
      _ = ‖M‖ := mul_one _
  calc
    ‖hardyLeakage M‖ ≤ ‖LowerHardyL2.orthogonalProjectionOnto‖ *
        ‖M.comp UpperHardyL2.subtypeL‖ :=
      ContinuousLinearMap.opNorm_comp_le LowerHardyL2.orthogonalProjectionOnto
        (M.comp UpperHardyL2.subtypeL)
    _ ≤ 1 * ‖M‖ := mul_le_mul
      (Submodule.orthogonalProjectionOnto_norm_le LowerHardyL2) hinner
      (norm_nonneg (M.comp UpperHardyL2.subtypeL)) (by norm_num)
    _ = ‖M‖ := one_mul _

theorem hardyLeakage_sub (M N : RealLineL2 →L[ℂ] RealLineL2) :
    hardyLeakage (M - N) = hardyLeakage M - hardyLeakage N := by
  ext f
  simp [hardyLeakage]

theorem norm_hardyLeakage_sub_le (M N : RealLineL2 →L[ℂ] RealLineL2) :
    ‖hardyLeakage M - hardyLeakage N‖ ≤ ‖M - N‖ := by
  rw [← hardyLeakage_sub]
  exact norm_hardyLeakage_le (M - N)

theorem tendsto_hardyLeakage {α : Type*} {l : Filter α}
    {F : α → (RealLineL2 →L[ℂ] RealLineL2)} {M : RealLineL2 →L[ℂ] RealLineL2}
    (hF : Tendsto F l (𝓝 M)) :
    Tendsto (fun x => hardyLeakage (F x)) l (𝓝 (hardyLeakage M)) := by
  refine (tendsto_iff_norm_sub_tendsto_zero
    (E := UpperHardyL2 →L[ℂ] LowerHardyL2)).mpr ?_
  apply squeeze_zero'
  · exact Eventually.of_forall fun x =>
      norm_nonneg (hardyLeakage (F x) - hardyLeakage M)
  · exact Eventually.of_forall fun x => norm_hardyLeakage_sub_le (F x) M
  · exact (tendsto_iff_norm_sub_tendsto_zero
      (E := RealLineL2 →L[ℂ] RealLineL2)).mp hF

end GaloisForLFunctions.HTGeometry
