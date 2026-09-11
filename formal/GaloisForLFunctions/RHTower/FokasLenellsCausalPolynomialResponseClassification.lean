import GaloisForLFunctions.RHTower.FokasLenellsCausalCauchyPairing
import GaloisForLFunctions.RHTower.FokasLenellsCausalLeftPolynomialClassification
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedCoordinateDensity
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundaryOrbits
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-! Polynomial responses of genuine rational Cauchy data determine bounded L2 operators.
Actual scalar Cauchy pairings continue disk eigenvector identities to the full pole
half-plane. Boundedness then forces precisely the constant and positive-affine classes. -/
open Complex MeasureTheory Set Filter Topology Polynomial
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPolynomialResponseLowerComplete : CompleteSpace (hardyL2ᗮ) :=
  hardyL2.isClosed_orthogonal.completeSpace_coe

private theorem high_pole_rate_norm {w : ℂ} (hw : 1 < w.im) : ‖causalPoleRate w‖ ≤ 1 := by
  have hn : 1 < ‖w‖ := hw.trans_le ((le_abs_self w.im).trans (Complex.abs_im_le_norm w))
  have hp : 0 < ‖w‖ := lt_trans zero_lt_one hn
  calc
    ‖causalPoleRate w‖ = (1 / ‖w‖) / 2 := by
      simp only [causalPoleRate, norm_div, norm_neg, Complex.norm_I]
      norm_num
    _ ≤ 1 := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      apply (div_le_iff₀ hp).2
      nlinarith

private theorem high_pole_response (F : ℂ → ℂ) (T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ)
    (hT : ∀ q : causalBoundedDiskRate,
      T (causalBoundedDiskEigenvector q).val = F q.val • (causalBoundedDiskEigenvector q).val)
    {w : ℂ} (hw : 1 < w.im) :
    T (causalCauchyEigenvector ⟨w, lt_trans zero_lt_one hw⟩) =
      F (causalPoleRate w) • causalCauchyEigenvector ⟨w, lt_trans zero_lt_one hw⟩ := by
  let q : causalBoundedDiskRate :=
    ⟨causalPoleRate w, causalPoleRate_re_neg ⟨w, lt_trans zero_lt_one hw⟩, high_pole_rate_norm hw⟩
  have hp : causalEigenPole ⟨q.val, q.property.1⟩ = ⟨w, lt_trans zero_lt_one hw⟩ :=
    Subtype.ext (causalPoleRate_involution w)
  have he : (causalLeftEigenvector ⟨q.val, q.property.1⟩).val =
      causalCauchyEigenvector ⟨w, lt_trans zero_lt_one hw⟩ :=
    congrArg causalCauchyEigenvector hp
  let c : ℂ := (‖causalLeftEigenvector ⟨q.val, q.property.1⟩‖ : ℂ)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (causalLeftEigenvector_ne_zero ⟨q.val, q.property.1⟩)))
  have hq : (causalBoundedDiskEigenvector q).val =
      c • causalCauchyEigenvector ⟨w, lt_trans zero_lt_one hw⟩ :=
    congrArg (fun v : hardyL2ᗮ => c • v) he
  apply smul_right_injective (hardyL2ᗮ) hc
  calc
    c • T (causalCauchyEigenvector ⟨w, lt_trans zero_lt_one hw⟩) =
        T (c • causalCauchyEigenvector ⟨w, lt_trans zero_lt_one hw⟩) := (map_smul T c _).symm
    _ = F (causalPoleRate w) • (c • causalCauchyEigenvector ⟨w, lt_trans zero_lt_one hw⟩) :=
      (congrArg T hq).symm.trans ((hT q).trans (congrArg (fun v : hardyL2ᗮ => F q.val • v) hq))
    _ = c • (F (causalPoleRate w) • causalCauchyEigenvector ⟨w, lt_trans zero_lt_one hw⟩) :=
      smul_comm _ _ _

private theorem analytic_pole_rate :
    AnalyticOnNhd ℂ causalPoleRate {w : ℂ | 0 < w.im} := by
  intro w hw
  change 0 < w.im at hw
  have hne : w ≠ 0 := by
    intro h
    simpa only [h, Complex.zero_im, lt_self_iff_false] using hw
  change AnalyticAt ℂ (fun z : ℂ => -(I / z) / 2) w
  exact (analyticAt_const.div analyticAt_id hne).neg.div analyticAt_const (by norm_num)

private theorem response_continuation (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ) (T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ)
    (hT : ∀ q : causalBoundedDiskRate,
      T (causalBoundedDiskEigenvector q).val = F q.val • (causalBoundedDiskEigenvector q).val)
    (w : {z : ℂ // 0 < z.im}) :
    T (causalCauchyEigenvector w) = F (causalPoleRate w.val) • causalCauchyEigenvector w := by
  apply ext_inner_left ℂ
  intro f
  let H : ℂ → ℂ := fun z => causalCauchyPairing (T.adjoint f) z -
    F (causalPoleRate z) * causalCauchyPairing f z
  have hpair (g : hardyL2ᗮ) : AnalyticOnNhd ℂ (causalCauchyPairing g) {z : ℂ | 0 < z.im} :=
    (analyticOnNhd_causalCauchyPairing g).mono (fun _ hz => ne_of_gt hz)
  have hana : AnalyticOnNhd ℂ H {z : ℂ | 0 < z.im} :=
    (hpair (T.adjoint f)).sub ((hF.comp analytic_pole_rate (fun _ _ => Set.mem_univ _)).mul (hpair f))
  have hhigh (z : ℂ) (hz : 1 < z.im) : H z = 0 := by
    have he := high_pole_response F T hT hz
    change causalCauchyPairing (T.adjoint f) z - F (causalPoleRate z) * causalCauchyPairing f z = 0
    rw [causalCauchyPairing_adjoint T f ⟨z, lt_trans zero_lt_one hz⟩,
      causalCauchyPairing_eq_inner f ⟨z, lt_trans zero_lt_one hz⟩, he, inner_smul_right, sub_self]
  have hnear : H =ᶠ[𝓝 (2 * I)] 0 := by
    have hopen : IsOpen {z : ℂ | 1 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have hm : (2 * I : ℂ) ∈ {z : ℂ | 1 < z.im} := by norm_num
    have hpatch : ∀ᶠ z : ℂ in 𝓝 (2 * I), 1 < z.im := hopen.mem_nhds hm
    exact hpatch.mono (fun z hz => hhigh z hz)
  have hall : Set.EqOn H 0 {z : ℂ | 0 < z.im} :=
    hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_im_gt 0).isPreconnected (by norm_num : (2 * I : ℂ).im > 0) hnear
  have hh := hall w.property
  change causalCauchyPairing (T.adjoint f) w.val -
    F (causalPoleRate w.val) * causalCauchyPairing f w.val = 0 at hh
  rw [causalCauchyPairing_adjoint T f w, causalCauchyPairing_eq_inner f w] at hh
  exact (sub_eq_zero.mp hh).trans (inner_smul_right _ _ _).symm

private theorem left_response_bound (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ) (T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ)
    (hT : ∀ q : causalBoundedDiskRate,
      T (causalBoundedDiskEigenvector q).val = F q.val • (causalBoundedDiskEigenvector q).val)
    (z : ℂ) (hz : z.re < 0) : ‖F z‖ ≤ ‖T‖ := by
  let w := causalEigenPole ⟨z, hz⟩
  have he : T (causalCauchyEigenvector w) = F z • causalCauchyEigenvector w := by
    simpa only [w, causalPoleRate_eigenPole] using response_continuation F hF T hT w
  have hn : 0 < ‖causalCauchyEigenvector w‖ :=
    norm_pos_iff.mpr (causalCauchyEigenvector_ne_zero w)
  have hb := T.le_opNorm (causalCauchyEigenvector w)
  rw [he, norm_smul] at hb
  exact (mul_le_mul_iff_left₀ hn).mp hb

private theorem operator_eq_of_disk_eq (T U : hardyL2ᗮ →L[ℂ] hardyL2ᗮ)
    (h : ∀ q : causalBoundedDiskRate,
      T (causalBoundedDiskEigenvector q).val = U (causalBoundedDiskEigenvector q).val) : T = U := by
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr
      topologicalClosure_span_causalBoundedDiskEigenvector_eq_top)
  rintro v ⟨q, rfl⟩
  exact h q

private theorem forward_disk_response (a : ℝ≥0) (b : ℂ) (q : causalBoundedDiskRate) :
    (Complex.exp b • causalLowerCauchyEvolution a) (causalBoundedDiskEigenvector q).val =
      Complex.exp ((((a : ℝ) : ℂ) * q.val) + b) • (causalBoundedDiskEigenvector q).val := by
  let v : hardyL2ᗮ := (causalLeftEigenvector ⟨q.val, q.property.1⟩).val
  let c : ℂ := (‖causalLeftEigenvector ⟨q.val, q.property.1⟩‖ : ℂ)⁻¹
  change Complex.exp b • causalLowerCauchyEvolution a (c • v) =
    Complex.exp ((((a : ℝ) : ℂ) * q.val) + b) • (c • v)
  have he : causalLowerCauchyEvolution a v = Complex.exp (((a : ℝ) : ℂ) * q.val) • v :=
    causalLowerCauchyEvolution_leftEigenvector a ⟨q.val, q.property.1⟩
  rw [map_smul, he, Complex.exp_add]
  simp only [smul_smul]
  congr 1
  ring

/-- A bounded L2 operator has polynomial eigenvalues on the actual disk-rate
rational family exactly when both the polynomial and operator are scalar constants. -/
theorem causalCauchyPolynomialResponse_iff (p : ℂ[X]) (T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ) :
    (∀ q : causalBoundedDiskRate,
      T (causalBoundedDiskEigenvector q).val = p.eval q.val • (causalBoundedDiskEigenvector q).val) ↔
      ∃ b : ℂ, p = C b ∧ T = b • ContinuousLinearMap.id ℂ (hardyL2ᗮ) := by
  constructor
  · intro hT
    have hb : ∃ B : ℝ, ∀ z : ℂ, z.re < 0 → ‖p.eval z‖ ≤ B :=
      ⟨‖T‖, left_response_bound (fun z => p.eval z) (AnalyticOnNhd.eval_polynomial p) T hT⟩
    obtain ⟨b, hp⟩ := (causalLeftPolynomial_norm_bounded_iff p).mp hb
    refine ⟨b, hp, operator_eq_of_disk_eq T _ (fun q => ?_)⟩
    simpa only [hp, Polynomial.eval_C, smul_apply,
      ContinuousLinearMap.id_apply] using hT q
  · rintro ⟨b, rfl, rfl⟩ q
    simp

/-- A bounded L2 operator has exponential-polynomial eigenvalues on the actual
rational disk family exactly for a scalar multiple of positive-time Cauchy evolution. -/
theorem causalCauchyExponentialPolynomialResponse_iff (p : ℂ[X])
    (T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ) :
    (∀ q : causalBoundedDiskRate,
      T (causalBoundedDiskEigenvector q).val =
        Complex.exp (p.eval q.val) • (causalBoundedDiskEigenvector q).val) ↔
      ∃ a : ℝ≥0, ∃ b : ℂ, p = C ((a : ℝ) : ℂ) * X + C b ∧
        T = Complex.exp b • causalLowerCauchyEvolution a := by
  constructor
  · intro hT
    have hb : ∃ B : ℝ, ∀ z : ℂ, z.re < 0 → ‖Complex.exp (p.eval z)‖ ≤ B :=
      ⟨‖T‖, left_response_bound (fun z => Complex.exp (p.eval z))
        (AnalyticOnNhd.eval_polynomial p).cexp T hT⟩
    obtain ⟨a, b, hp⟩ := (causalLeftPolynomial_exp_bounded_iff p).mp hb
    refine ⟨a, b, hp, operator_eq_of_disk_eq T _ (fun q => ?_)⟩
    have he := hT q
    rw [hp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_C] at he
    exact he.trans (forward_disk_response a b q).symm
  · rintro ⟨a, b, rfl, rfl⟩ q
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using
      forward_disk_response a b q

end
end RHTower.FokasLenells
