import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.BesselFourierSmoothness
import GaloisForLFunctions.HTGeometry.ComplexAnalysis.PureJetAlgebra

/-!
# Exact horizontal jets of cubic Fourier–Bessel series

Pure Wirtinger differentiation raises the corresponding linear frequency weight to an
integer power. Subexponential coefficient bounds justify every derivative of the sum.
The actual residual source has no constant mode after its first horizontal derivative.
-/

open Complex Set
open scoped ContDiff ComplexConjugate Classical
open HTGeometry
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
noncomputable section

lemma CuspSubexponential.holWeight_pow {c : O → ℂ} (hc : CuspSubexponential c) (n : ℕ) :
    CuspSubexponential (fun h => cuspHolWeight h ^ n * c h) := by
  induction n with
  | zero => simpa only [pow_zero, one_mul] using hc
  | succ n ih =>
      simpa only [pow_succ', mul_assoc] using ih.holWeight

lemma CuspSubexponential.antiholWeight_pow {c : O → ℂ} (hc : CuspSubexponential c) (n : ℕ) :
    CuspSubexponential (fun h => cuspAntiholWeight h ^ n * c h) := by
  induction n with
  | zero => simpa only [pow_zero, one_mul] using hc
  | succ n ih =>
      simpa only [pow_succ', mul_assoc] using ih.antiholWeight

/-- Every horizontal slice is smooth, uniformly in the choice of complex Bessel order. -/
theorem contDiff_besselPlaneSeries_slice (ν : ℂ) {c : O → ℂ} (hc : CuspSubexponential c)
    (v : ℝ) (hv : 0 < v) : ContDiff ℝ ∞ (fun z => besselPlaneSeries ν c (v, z)) := by
  apply contDiff_iff_contDiffAt.2
  intro z
  have hm : (v, z) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ) := ⟨hv, mem_univ z⟩
  exact ((contDiffOn_besselPlaneSeries ν hc).contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hm)).comp z
      (contDiffAt_const.prodMk contDiffAt_id)

lemma besselPlaneSeries_slice_fderiv_apply (ν : ℂ) {c : O → ℂ} (hc : CuspSubexponential c)
    (v : ℝ) (hv : 0 < v) (z w : ℂ) :
    fderiv ℝ (fun u => besselPlaneSeries ν c (v, u)) z w =
      besselPlaneSeries ν (fun h => cuspHolWeight h * c h) (v, z) * w +
      besselPlaneSeries ν (fun h => cuspAntiholWeight h * c h) (v, z) * conj w := by
  have hi : HasFDerivAt (fun u : ℂ => (v, u))
      ((0 : ℂ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℂ)) z :=
    (hasFDerivAt_const v z).prodMk (hasFDerivAt_id z)
  have hf := (besselPlaneSeries_hasFDerivAt ν hc (v, z) hv).differentiableAt.hasFDerivAt
  have hd : HasFDerivAt (fun u => besselPlaneSeries ν c (v, u))
      ((fderiv ℝ (besselPlaneSeries ν c) (v, z)).comp
        ((0 : ℂ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℂ))) z := hf.comp z hi
  rw [hd.fderiv]
  change fderiv ℝ (besselPlaneSeries ν c) (v, z) (0, w) = _
  rw [besselPlaneSeries_fderiv_apply ν hc _ _ hv]
  simp only [Complex.ofReal_zero, zero_mul, zero_add]

/-- One holomorphic or antiholomorphic derivative multiplies the Fourier coefficient. -/
theorem besselPlaneSeries_wirtinger (ν : ℂ) {c : O → ℂ} (hc : CuspSubexponential c)
    (v : ℝ) (hv : 0 < v) (z : ℂ) :
    dz (fun u => besselPlaneSeries ν c (v, u)) z =
        besselPlaneSeries ν (fun h => cuspHolWeight h * c h) (v, z) ∧
    dzbar (fun u => besselPlaneSeries ν c (v, u)) z =
        besselPlaneSeries ν (fun h => cuspAntiholWeight h * c h) (v, z) := by
  simp only [dz, dzbar, wirtingerHol, wirtingerAntihol,
    besselPlaneSeries_slice_fderiv_apply ν hc v hv, map_one, mul_one, Complex.conj_I,
    mul_neg]
  constructor
  · linear_combination
      -(besselPlaneSeries ν (fun h => cuspHolWeight h * c h) (v, z) -
        besselPlaneSeries ν (fun h => cuspAntiholWeight h * c h) (v, z)) / 2 * Complex.I_sq
  · linear_combination
      (besselPlaneSeries ν (fun h => cuspHolWeight h * c h) (v, z) -
        besselPlaneSeries ν (fun h => cuspAntiholWeight h * c h) (v, z)) / 2 * Complex.I_sq

/-- Every pure holomorphic derivative has the exact frequency-power coefficient. -/
theorem iteratedDz_besselPlaneSeries (ν : ℂ) {c : O → ℂ} (hc : CuspSubexponential c)
    (v : ℝ) (hv : 0 < v) (n : ℕ) :
    iteratedDz n (fun z => besselPlaneSeries ν c (v, z)) =
      fun z => besselPlaneSeries ν (fun h => cuspHolWeight h ^ n * c h) (v, z) := by
  induction n with
  | zero => simp only [iteratedDz, pow_zero, one_mul]
  | succ n ih =>
      rw [iteratedDz, ih]
      funext z
      simpa only [pow_succ', mul_assoc] using
        (besselPlaneSeries_wirtinger ν (hc.holWeight_pow n) v hv z).1

/-- Every pure antiholomorphic derivative has the conjugate-frequency-power coefficient. -/
theorem iteratedDzbar_besselPlaneSeries (ν : ℂ) {c : O → ℂ} (hc : CuspSubexponential c)
    (v : ℝ) (hv : 0 < v) (n : ℕ) :
    iteratedDzbar n (fun z => besselPlaneSeries ν c (v, z)) =
      fun z => besselPlaneSeries ν (fun h => cuspAntiholWeight h ^ n * c h) (v, z) := by
  induction n with
  | zero => simp only [iteratedDzbar, pow_zero, one_mul]
  | succ n ih =>
      rw [iteratedDzbar, ih]
      funext z
      simpa only [pow_succ', mul_assoc] using
        (besselPlaneSeries_wirtinger ν (hc.antiholWeight_pow n) v hv z).2

/-- Multiplication of one coefficient factors out of its individual Fourier mode. -/
lemma besselPlaneTerm_weight (ν : ℂ) (c m : O → ℂ) (h : O) (p : ℝ × ℂ) :
    besselPlaneTerm ν (fun j => m j * c j) h p = m h * besselPlaneTerm ν c h p := by
  by_cases hh : h = 0
  · simp only [besselPlaneTerm, if_pos hh, mul_zero]
  · simp only [besselPlaneTerm, if_neg hh]
    ring

/-- Conjugation and coefficient multiplication act termwise on the actual sum. -/
lemma conjugate_besselPlaneSeries_weight (ν : ℂ) (c m : O → ℂ) (p : ℝ × ℂ) :
    conj (besselPlaneSeries ν (fun h => m h * c h) p) =
      ∑' h : O, conj (m h) * conj (besselPlaneTerm ν c h p) := by
  change star (∑' h : O, besselPlaneTerm ν (fun j => m j * c j) h p) = _
  rw [tsum_star]
  apply tsum_congr
  intro h
  rw [besselPlaneTerm_weight, star_mul]
  exact mul_comm _ _

/-- The positive-ray and cosh Bessel conventions give the same individual cubic mode. -/
lemma cubicBesselTerm_eq_besselPlaneTerm (c : O → ℂ) (h : O) (p : ℝ × ℂ)
    (hp : 0 < p.1) :
    cubicBesselTerm c h p = (p.1 : ℂ) * besselPlaneTerm (1 / 3) c h p := by
  by_cases hh : h = 0
  · simp only [cubicBesselTerm, cubicBesselAmplitude, besselPlaneTerm, if_pos hh, zero_mul,
      mul_zero]
  · have hx : 0 < 4 * Real.pi * ‖cuspFrequency h‖ * p.1 := by
      have := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
      positivity
    simp only [cubicBesselTerm, cubicBesselAmplitude, besselPlaneTerm, if_neg hh]
    rw [GaloisForLFunctions.SpectralTheoryOfTheCubicCover.schlafliBesselK_eq_modifiedBesselKOrder _ hx]
    ring

/-- Positive-order jets remove the constant cusp mode and multiply each nonzero frequency. -/
theorem iteratedDz_const_add_besselPlaneSeries (ν : ℂ) {c : O → ℂ}
    (hc : CuspSubexponential c) (v : ℝ) (hv : 0 < v) (a b : ℂ) (n : ℕ) :
    iteratedDz (n + 1) (fun z => a + b * besselPlaneSeries ν c (v, z)) =
      fun z => b * besselPlaneSeries ν
        (fun h => cuspHolWeight h ^ (n + 1) * c h) (v, z) := by
  have hs := contDiff_besselPlaneSeries_slice ν hc v hv
  have hfirst : dz (fun z => a + b * besselPlaneSeries ν c (v, z)) =
      fun z => b * besselPlaneSeries ν (fun h => cuspHolWeight h * c h) (v, z) := by
    funext z
    rw [dz_const_add_of_differentiable
      ((contDiff_const.mul hs).differentiable (by simp) z),
      dz_const_mul_of_differentiable (hs.differentiable (by simp) z),
      (besselPlaneSeries_wirtinger ν hc v hv z).1]
  rw [iteratedDz_succ_right, hfirst, iteratedDz_const_mul
    (contDiff_besselPlaneSeries_slice ν hc.holWeight v hv),
    iteratedDz_besselPlaneSeries ν hc.holWeight v hv]
  simp only [pow_succ, mul_assoc]

/-- The actual source's positive holomorphic jets have no residual analytic premise. -/
theorem cubicSource_iteratedDz_bessel (v : ℝ) (hv : 0 < v) (n : ℕ) :
    iteratedDz (n + 1)
        (fun z => cubicSourceResidualFunction (cuspCoordinateLift (v, z))) =
      fun z => (v : ℂ) * besselPlaneSeries (1 / 3)
        (fun h => cuspHolWeight h ^ (n + 1) * rationalSourceResidualFourierCoefficient h)
          (v, z) := by
  have he : (fun z => cubicSourceResidualFunction (cuspCoordinateLift (v, z))) =
      fun z => (3 * (Real.pi : ℂ) * constantArithmeticResidue) * (v : ℂ) ^ (2 / 3 : ℂ) +
        (v : ℂ) * besselPlaneSeries (1 / 3) rationalSourceResidualFourierCoefficient (v, z) :=
    funext (fun z => cubicSourceResidualFunction_eq_besselPlaneSeries (v, z) hv)
  rw [he]
  exact iteratedDz_const_add_besselPlaneSeries (1 / 3)
    rationalSourceResidualFourierCoefficient_subexponential v hv _ _ n

/-- The actual cubic source is smooth along every positive horizontal slice. -/
theorem cubicSource_horizontal_contDiff (v : ℝ) (hv : 0 < v) :
    ContDiff ℝ ∞ (fun z => cubicSourceResidualFunction (cuspCoordinateLift (v, z))) := by
  apply contDiff_iff_contDiffAt.2
  intro z
  have hm : (v, z) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ) := ⟨hv, mem_univ z⟩
  exact (cubicSourceResidualFunction_coordinate_contDiffOn.contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hm)).comp z
      (contDiffAt_const.prodMk contDiffAt_id)

/-- The Gauss-twist source has exactly the conjugated holomorphic frequency powers. -/
theorem conjugate_cubicSource_iteratedDzbar_bessel (v : ℝ) (hv : 0 < v) (n : ℕ) :
    iteratedDzbar (n + 1)
        (fun z => conj (cubicSourceResidualFunction (cuspCoordinateLift (v, z)))) =
      fun z => (v : ℂ) * conj (besselPlaneSeries (1 / 3)
        (fun h => cuspHolWeight h ^ (n + 1) * rationalSourceResidualFourierCoefficient h)
          (v, z)) := by
  rw [iteratedDzbar_conjugate (cubicSource_horizontal_contDiff v hv),
    cubicSource_iteratedDz_bessel v hv]
  simp only [map_mul, Complex.conj_ofReal]

end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
