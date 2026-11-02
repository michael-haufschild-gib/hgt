import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineDiscreteJacobian
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineFrequencySeparation

/-!
# Exact finite moments with prescribed spline coefficients

A finite positive prime-logarithm spectrum admits every sufficiently small
complex moment vector using distinct heights in a fixed-length interval above
any sufficiently large height. Every coefficient is exactly `(sinh z / z)^8`;
all multiplicities are one. The interval length and normalized residual radius
are independent of the starting height.

The proof moves a fine grid through bounded dual primitives. Explicit row,
nonlinear, and denominator errors make the normalized moment map a half-Lipschitz
perturbation of the identity. A closed-ball inverse realizes the target, while
quarter-spacing displacement preserves distinctness.
-/

open Finset Complex Metric
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι]

lemma splineGridAverage_sub (f g : ℝ → ℂ) (a h : ℝ) (n : ℕ) :
    splineGridAverage (fun x => f x-g x) a h n=
      splineGridAverage f a h n-splineGridAverage g a h n := by
  simp only [splineGridAverage, sum_sub_distrib, sub_div]

lemma corrected_spline_grid_mem {δ H h ρ : ℝ} (hδ : 0 < δ) {t : ι → ℝ}
    (ht : ∀ i, 0 < t i) (hh : 0 < h) {n : ℕ} {y : ι → ℂ} (hy : ‖y‖ ≤ ρ)
    (hdisp : splineHeightCorrectionBound δ t*ρ ≤ h/4) (j : Fin n) :
    H+h+j.val*h+splineHeightCorrection δ t y (H+h+j.val*h) ∈
      Set.Icc H (H+((n : ℝ)+1)*h) := by
  have hb := (abs_splineHeightCorrection_le hδ ht y (H+h+j.val*h)).trans
    (mul_le_mul_of_nonneg_left hy (splineHeightCorrectionBound_nonneg hδ ht))
  have hp := abs_le.mp (hb.trans hdisp)
  have hj : (j.val : ℝ)+1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  constructor
  · nlinarith only [hp.1, mul_nonneg hj0 hh.le, hh]
  · nlinarith only [hp.2, mul_le_mul_of_nonneg_right hj hh.le, hh]

lemma corrected_spline_grid_injective {δ H h ρ : ℝ} (hδ : 0 < δ) {t : ι → ℝ}
    (ht : ∀ i, 0 < t i) (hh : 0 < h) {n : ℕ} {y : ι → ℂ} (hy : ‖y‖ ≤ ρ)
    (hdisp : splineHeightCorrectionBound δ t*ρ ≤ h/4) :
    Function.Injective (fun j : Fin n =>
      H+h+j.val*h+splineHeightCorrection δ t y (H+h+j.val*h)) := by
  have hb (j : Fin n) : |splineHeightCorrection δ t y (H+h+j.val*h)| ≤ h/4 :=
    ((abs_splineHeightCorrection_le hδ ht y (H+h+j.val*h)).trans
      (mul_le_mul_of_nonneg_left hy (splineHeightCorrectionBound_nonneg hδ ht))).trans hdisp
  apply StrictMono.injective
  intro j k hjk
  have hjkR : (j.val : ℝ)+1 ≤ k.val := by exact_mod_cast (Nat.succ_le_iff.mpr hjk)
  have hj := abs_le.mp (hb j)
  have hk := abs_le.mp (hb k)
  nlinarith only [hj.2, hk.1, mul_le_mul_of_nonneg_right hjkR hh.le, hh]

/-- The normalized exact moment map on a translated grid. -/
def exactSplineGridMap (H δ : ℝ) (t : ι → ℝ) (h : ℝ) (n : ℕ) (y : ι → ℂ) : ι → ℂ :=
  fun i => splineGridAverage (fun x => normalizedSplineNumerator H δ (t i)
    (x+splineHeightCorrection δ t y x)) (H+h) h n

lemma norm_exactSplineGridMap_zero_le {H δ Λ η : ℝ} (hH : 0 < H) (hδ : 0 < δ)
    {t : ι → ℝ} (hΛ : 0 < Λ) (hη : 0 < η) {n : ℕ} (hn : 0 < n)
    (hfreq : ∀ i j, |t i+splineShift j| ≤ 2*Λ)
    (hgap : ∀ i j, η ≤ |t i+splineShift j|) (i : ι) :
    ‖exactSplineGridMap H δ t (Real.pi/(2*Λ)) n 0 i‖ ≤
      2*Λ*splineNumeratorBound δ/(η*n)+
        8*(((n : ℝ)+1)*(Real.pi/(2*Λ))+δ)*splineNumeratorBound δ/H := by
  let h := Real.pi/(2*Λ)
  let C := ((n : ℝ)+1)*h
  have hh : 0 < h := by dsimp only [h]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hz : ∀ x, splineHeightCorrection δ t (0 : ι → ℂ) x=0 := by
    intro x
    simp [splineHeightCorrection]
  have hb : ‖splineGridAverage (shiftedSplineNumerator δ (t i)) (H+h) h n‖ ≤
      2*Λ*splineNumeratorBound δ/(η*n) := by
    rw [splineGridAverage, norm_div, Complex.norm_natCast]
    refine (div_le_div_of_nonneg_right
      (norm_grid_spline_numerator_sum_le hΛ hη (hfreq i) (hgap i) δ (H+h) n) hnR.le).trans_eq ?_
    ring
  have he : ‖splineGridAverage (fun x =>
      (splineHeightFactor H δ x-1)*shiftedSplineNumerator δ (t i) x) (H+h) h n‖ ≤
      8*(C+δ)*splineNumeratorBound δ/H := by
    apply norm_splineGridAverage_le hn
    intro j
    have hj : (j.val : ℝ)+1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
    have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
    have hx : H ≤ H+h+j.val*h := by nlinarith only [mul_nonneg hj0 hh.le, hh]
    have hx' : H+h+j.val*h ≤ H+C := by
      dsimp only [C]
      nlinarith only [mul_le_mul_of_nonneg_right hj hh.le, hh]
    rw [norm_mul]
    refine (mul_le_mul (norm_splineHeightFactor_sub_one_le hH hδ.le hx hx')
      (norm_shiftedSplineNumerator_le δ (t i) _) (norm_nonneg _)
      (by positivity : 0 ≤ 8*(C+δ)/H)).trans_eq ?_
    ring
  have hid (x : ℝ) : normalizedSplineNumerator H δ (t i) x=
      shiftedSplineNumerator δ (t i) x+
        (splineHeightFactor H δ x-1)*shiftedSplineNumerator δ (t i) x := by
    unfold normalizedSplineNumerator
    ring
  simp only [exactSplineGridMap, hz, add_zero, hid, splineGridAverage_add]
  exact (norm_add_le _ _).trans (add_le_add hb he)

#print axioms corrected_spline_grid_injective
#print axioms norm_exactSplineGridMap_zero_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι]

/-- Explicit scalar errors suffice for inversion of the exact spline moment map. -/
theorem exactSplineGridMap_approximates_identity {H δ h ρ : ℝ} (hH : 0 < H) (hδ : 0 < δ)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) (hinj : Function.Injective t)
    (hh : 0 < h) (hρ : 0 ≤ ρ) {n : ℕ} (hn : 0 < n)
    (hdisp : splineHeightCorrectionBound δ t*ρ ≤ h/4)
    (hjac : ∀ i, (∑ j, splineJacobianEntryBound δ (t i) (t j))/((n : ℝ)*h)+
      (∑ j, splinePairLipschitzBound δ (t i) (t j))*h ≤ 1/4)
    (herr : ∀ i, splineSecondBound δ (t i)*(splineHeightCorrectionBound δ t)^2*ρ+
      splineNormalizationErrorBound H δ (t i) (((n : ℝ)+1)*h)*splineHeightCorrectionBound δ t ≤ 1/4) :
    ApproximatesLinearOn (exactSplineGridMap H δ t h n)
      (ContinuousLinearMap.id ℝ (ι → ℂ)) (closedBall 0 ρ) (1/2) := by
  intro y hy z hz
  have hy' : ‖y‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hy
  have hz' : ‖z‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hz
  change ‖exactSplineGridMap H δ t h n y-exactSplineGridMap H δ t h n z-(y-z)‖ ≤
    (1/2 : ℝ)*‖y-z‖
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (1/2 : ℝ)*‖y-z‖)).mpr
  intro i
  have he : ‖splineGridAverage (fun x =>
      normalizedSplineNumerator H δ (t i) (x+splineHeightCorrection δ t y x)-
      normalizedSplineNumerator H δ (t i) (x+splineHeightCorrection δ t z x)-
      shiftedSplineSlope δ (t i) x*((splineHeightCorrection δ t y x-splineHeightCorrection δ t z x : ℝ) : ℂ))
      (H+h) h n‖ ≤ (1/4 : ℝ)*‖y-z‖ := by
    apply norm_splineGridAverage_le hn
    intro j
    exact (norm_exact_corrected_spline_increment_le hH hδ ht hρ hz' hy' i (H+h+j.val*h)
      (corrected_spline_grid_mem hδ ht hh hz' hdisp j)
      (corrected_spline_grid_mem hδ ht hh hy' hdisp j)).trans
      (mul_le_mul_of_nonneg_right (herr i) (norm_nonneg _))
  have hj := (norm_spline_discrete_jacobian_defect_le hδ ht hinj hh hn (H+h) (y-z) i).trans
    (mul_le_mul_of_nonneg_right (hjac i) (norm_nonneg _))
  have hid : exactSplineGridMap H δ t h n y i-exactSplineGridMap H δ t h n z i-(y-z) i=
      splineGridAverage (fun x =>
        normalizedSplineNumerator H δ (t i) (x+splineHeightCorrection δ t y x)-
        normalizedSplineNumerator H δ (t i) (x+splineHeightCorrection δ t z x)-
        shiftedSplineSlope δ (t i) x*((splineHeightCorrection δ t y x-splineHeightCorrection δ t z x : ℝ) : ℂ))
        (H+h) h n+
      (splineGridAverage (fun x => shiftedSplineSlope δ (t i) x*
        (splineHeightCorrection δ t (y-z) x : ℂ)) (H+h) h n-(y-z) i) := by
    simp_rw [splineHeightCorrection_sub]
    rw [splineGridAverage_sub, splineGridAverage_sub]
    unfold exactSplineGridMap
    ring
  change ‖exactSplineGridMap H δ t h n y i-exactSplineGridMap H δ t h n z i-(y-z) i‖ ≤ _
  rw [hid]
  exact (norm_add_le _ _).trans ((add_le_add he hj).trans_eq (by ring))

#print axioms exactSplineGridMap_approximates_identity
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι]

lemma exactSplineGridMap_eq (H δ : ℝ) (t : ι → ℝ) (h : ℝ) (n : ℕ)
    (y : ι → ℂ) (i : ι) :
    exactSplineGridMap H δ t h n y i=(H : ℂ)^8/(n : ℂ)*
      ∑ j : Fin n,
        (Complex.sinh ((δ : ℂ)+((H+h+j.val*h+splineHeightCorrection δ t y (H+h+j.val*h) : ℝ) : ℂ)*Complex.I)/
          ((δ : ℂ)+((H+h+j.val*h+splineHeightCorrection δ t y (H+h+j.val*h) : ℝ) : ℂ)*Complex.I))^8*
        phase (t i) (H+h+j.val*h+splineHeightCorrection δ t y (H+h+j.val*h)) := by
  simp only [exactSplineGridMap, splineGridAverage, normalizedSplineNumerator_eq, mul_assoc,
    ← mul_sum]
  ring

/-- Small normalized targets are realized by distinct nodes and unit spline coefficients. -/
theorem exists_exact_spline_grid_correction {H δ h ρ : ℝ} (hH : 0 < H) (hδ : 0 < δ)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) (hinj : Function.Injective t)
    (hh : 0 < h) (hρ : 0 ≤ ρ) {n : ℕ} (hn : 0 < n)
    (hdisp : splineHeightCorrectionBound δ t*ρ ≤ h/4)
    (hjac : ∀ i, (∑ j, splineJacobianEntryBound δ (t i) (t j))/((n : ℝ)*h)+
      (∑ j, splinePairLipschitzBound δ (t i) (t j))*h ≤ 1/4)
    (herr : ∀ i, splineSecondBound δ (t i)*(splineHeightCorrectionBound δ t)^2*ρ+
      splineNormalizationErrorBound H δ (t i) (((n : ℝ)+1)*h)*splineHeightCorrectionBound δ t ≤ 1/4)
    (hbase : ‖exactSplineGridMap H δ t h n 0‖ ≤ ρ/4)
    {v : ι → ℂ} (hv : ‖v‖ ≤ ρ/4) :
    ∃ γ : Fin n → ℝ, Function.Injective γ ∧
      (∀ j, γ j ∈ Set.Icc H (H+((n : ℝ)+1)*h)) ∧
      ∀ i, (H : ℂ)^8/(n : ℂ)*
        (∑ j, (Complex.sinh ((δ : ℂ)+(γ j : ℂ)*Complex.I)/
          ((δ : ℂ)+(γ j : ℂ)*Complex.I))^8*phase (t i) (γ j))=v i := by
  obtain ⟨y,hy,he⟩ := exists_small_solution_of_half_defect hρ
    (exactSplineGridMap_approximates_identity hH hδ ht hinj hh hρ hn hdisp hjac herr) hbase hv
  refine ⟨fun j => H+h+j.val*h+splineHeightCorrection δ t y (H+h+j.val*h),
    corrected_spline_grid_injective hδ ht hh hy hdisp, ?_, ?_⟩
  · intro j
    exact corrected_spline_grid_mem hδ ht hh hy hdisp j
  · intro i
    rw [← exactSplineGridMap_eq]
    exact congrFun he i

#print axioms exists_exact_spline_grid_correction
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι]

lemma splinePairLipschitzBound_nonneg {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (t : ℝ) :
    0 ≤ splinePairLipschitzBound δ t s := by
  have hd : 0 ≤ splineDualBound δ s := (norm_nonneg _).trans
    (norm_splineDual_le (s := s) hδ (by linarith only [hs]) 0)
  have hi : 0 ≤ inverseSplineBound δ := (norm_nonneg _).trans
    (norm_inverseSplineNumerator_le hδ 0)
  have h2 : 0 ≤ splineSecondBound δ t := sum_nonneg fun _ _ => abs_nonneg _
  have h1 : 0 ≤ splineSlopeBound δ t := sum_nonneg fun _ _ => abs_nonneg _
  exact add_nonneg (mul_nonneg h2 hd) (mul_nonneg h1 hi)

lemma splineJacobianEntryBound_nonneg {δ s t : ℝ} (hδ : 0 < δ) (hs : 0 < s) (ht : 0 < t) :
    0 ≤ splineJacobianEntryBound δ t s := by
  have hb : 0 ≤ splinePairBoundaryBound δ s := (norm_nonneg _).trans
    (norm_spline_pair_le (s := s) hδ hs t 0)
  have hts : 0 < t+s := add_pos ht hs
  unfold splineJacobianEntryBound
  positivity

/-- Exact finite interpolation with explicit parameter formulas and a node-count bound. -/
theorem exists_prescribed_spline_finite_correction_data {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) (hinj : Function.Injective t)
    (hgap : ∀ i j, η ≤ |t i+splineShift j|) :
    ∃ Λ ρ H₀ : ℝ, ∃ n : ℕ, 0 < Λ ∧ 0 < ρ ∧ 0 < H₀ ∧ 0 < n ∧
      Λ=1+((∑ i, |t i|)+8)+4*Real.pi*(∑ i, ∑ j, splinePairLipschitzBound δ (t i) (t j)) ∧
      ρ=min ((Real.pi/(2*Λ))/(4*(splineHeightCorrectionBound δ t+1)))
        (1/(8*((∑ i, splineSecondBound δ (t i))*(splineHeightCorrectionBound δ t)^2+1))) ∧
      H₀=1+64*((((n : ℝ)+1)*(Real.pi/(2*Λ))+δ)*(∑ i, splineSlopeBound δ (t i))+
        splineNumeratorBound δ)*splineHeightCorrectionBound δ t+
        64*(((n : ℝ)+1)*(Real.pi/(2*Λ))+δ)*splineNumeratorBound δ/ρ ∧
      (n : ℝ) ≤ 2+8*(∑ i, ∑ j, splineJacobianEntryBound δ (t i) (t j))/(Real.pi/(2*Λ))+
        16*Λ*splineNumeratorBound δ/(η*ρ) ∧
      ∀ H : ℝ, H₀ ≤ H → ∀ r : ι → ℂ, (∀ i, ‖r i‖ ≤ (ρ/4)*n/H^8) →
      ∃ γ : Fin n → ℝ, Function.Injective γ ∧
        (∀ j, γ j ∈ Set.Icc H (H+((n : ℝ)+1)*(Real.pi/(2*Λ)))) ∧
        ∀ i, (∑ j, (Complex.sinh ((δ : ℂ)+(γ j : ℂ)*Complex.I)/
          ((δ : ℂ)+(γ j : ℂ)*Complex.I))^8*phase (t i) (γ j))=r i := by
  classical
  let L := ∑ i, |t i|
  let A := ∑ i, ∑ j, splineJacobianEntryBound δ (t i) (t j)
  let J := ∑ i, ∑ j, splinePairLipschitzBound δ (t i) (t j)
  let P := splineHeightCorrectionBound δ t
  let Q := ∑ i, splineSecondBound δ (t i)
  let G := ∑ i, splineSlopeBound δ (t i)
  let B := splineNumeratorBound δ
  have hL : 0 ≤ L := sum_nonneg fun _ _ => abs_nonneg _
  have hArow (i : ι) : 0 ≤ ∑ j, splineJacobianEntryBound δ (t i) (t j) :=
    sum_nonneg fun j _ => splineJacobianEntryBound_nonneg hδ (ht j) (ht i)
  have hJrow (i : ι) : 0 ≤ ∑ j, splinePairLipschitzBound δ (t i) (t j) :=
    sum_nonneg fun j _ => splinePairLipschitzBound_nonneg hδ (ht j) (t i)
  have hQi (i : ι) : 0 ≤ splineSecondBound δ (t i) := sum_nonneg fun _ _ => abs_nonneg _
  have hGi (i : ι) : 0 ≤ splineSlopeBound δ (t i) := sum_nonneg fun _ _ => abs_nonneg _
  have hA : 0 ≤ A := sum_nonneg fun i _ => hArow i
  have hJ : 0 ≤ J := sum_nonneg fun i _ => hJrow i
  have hP : 0 ≤ P := splineHeightCorrectionBound_nonneg hδ ht
  have hQ : 0 ≤ Q := sum_nonneg fun i _ => hQi i
  have hG : 0 ≤ G := sum_nonneg fun i _ => hGi i
  have hB : 0 ≤ B := splineNumeratorBound_nonneg δ
  obtain ⟨Λ,ρ,H₀,n,hΛ,hΛL,hρ,hH₀,hn,hdisp,hJh,hAn,hquad,hBn,hΛeq,hρeq,hH₀eq,hnUpper,hheight⟩ :=
    exists_spline_correction_parameters hδ hL hη hA hJ hP hQ hG hB
  let h := Real.pi/(2*Λ)
  let C := ((n : ℝ)+1)*h
  have hh : 0 < h := by dsimp only [h]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfreq (i : ι) (j : Fin 9) : |t i+splineShift j| ≤ 2*Λ := by
    have hi : |t i| ≤ L := single_le_sum (f := fun j : ι => |t j|)
      (fun _ _ => abs_nonneg _) (mem_univ i)
    have ha : |t i+splineShift j| ≤ |t i|+|splineShift j| := by
      simpa only [Real.norm_eq_abs] using norm_add_le (t i) (splineShift j)
    exact ((ha.trans (add_le_add hi (abs_splineShift_le j))).trans hΛL).trans (by linarith only [hΛ])
  have hjac (i : ι) : (∑ j, splineJacobianEntryBound δ (t i) (t j))/((n : ℝ)*h)+
      (∑ j, splinePairLipschitzBound δ (t i) (t j))*h ≤ 1/4 := by
    have hAi : ∑ j, splineJacobianEntryBound δ (t i) (t j) ≤ A :=
      single_le_sum (fun i _ => hArow i) (mem_univ i)
    have hJi : ∑ j, splinePairLipschitzBound δ (t i) (t j) ≤ J :=
      single_le_sum (fun i _ => hJrow i) (mem_univ i)
    have h1 := (div_le_div_of_nonneg_right hAi (mul_pos hnR hh).le).trans hAn
    have h2 := (mul_le_mul_of_nonneg_right hJi hh.le).trans hJh
    linarith only [h1,h2]
  refine ⟨Λ,ρ,H₀,n,hΛ,hρ,hH₀,hn,hΛeq,hρeq,hH₀eq,hnUpper,?_⟩
  intro H hHH r hr
  have hH := hH₀.trans_le hHH
  obtain ⟨hEH,hBH⟩ := hheight H hHH
  have herr (i : ι) : splineSecondBound δ (t i)*P^2*ρ+
      splineNormalizationErrorBound H δ (t i) C*P ≤ 1/4 := by
    have hQle : splineSecondBound δ (t i) ≤ Q := single_le_sum (fun i _ => hQi i) (mem_univ i)
    have hGle : splineSlopeBound δ (t i) ≤ G := single_le_sum (fun i _ => hGi i) (mem_univ i)
    have h1 := (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hQle (sq_nonneg P)) hρ.le).trans hquad
    have h2 : splineNormalizationErrorBound H δ (t i) C*P ≤
        8*((C+δ)*G+B)*P/H := by
      unfold splineNormalizationErrorBound
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hH.le
      apply mul_le_mul_of_nonneg_right _ hP
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (mul_le_mul_of_nonneg_left hGle (add_pos hC hδ).le) le_rfl
    have h3 := h2.trans hEH
    linarith only [h1,h3]
  have hbase : ‖exactSplineGridMap H δ t h n 0‖ ≤ ρ/4 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ ρ/4)).mpr
    intro i
    have hi := norm_exactSplineGridMap_zero_le hH hδ hΛ hη hn hfreq hgap i
    have hb := add_le_add hBn hBH
    exact hi.trans (hb.trans_eq (by ring))
  let v : ι → ℂ := fun i => (H : ℂ)^8/(n : ℂ)*r i
  have hv : ‖v‖ ≤ ρ/4 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ ρ/4)).mpr
    intro i
    change ‖(H : ℂ)^8/(n : ℂ)*r i‖ ≤ _
    rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hH, Complex.norm_natCast]
    refine (mul_le_mul_of_nonneg_left (hr i) (by positivity : 0 ≤ H^8/(n : ℝ))).trans_eq ?_
    field_simp [hH.ne',hnR.ne']
  obtain ⟨γ,hγinj,hγmem,hγeq⟩ := exists_exact_spline_grid_correction
    hH hδ ht hinj hh hρ.le hn hdisp hjac herr hbase hv
  refine ⟨γ,hγinj,hγmem,?_⟩
  intro i
  have hHC : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  exact mul_left_cancel₀ (div_ne_zero (pow_ne_zero 8 hHC) hnC) (hγeq i)

/-- Every finite positive, nonresonant spectrum admits exact small spline moments
with distinct unit-multiplicity nodes in an interval of fixed length. -/
theorem exists_prescribed_spline_finite_correction {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) (hinj : Function.Injective t)
    (hgap : ∀ i j, η ≤ |t i+splineShift j|) :
    ∃ n : ℕ, ∃ C H₀ ε : ℝ, 0 < n ∧ 0 < C ∧ 0 < H₀ ∧ 0 < ε ∧
      ∀ H : ℝ, H₀ ≤ H → ∀ r : ι → ℂ, (∀ i, ‖r i‖ ≤ ε*n/H^8) →
      ∃ γ : Fin n → ℝ, Function.Injective γ ∧
        (∀ j, γ j ∈ Set.Icc H (H+C)) ∧
        ∀ i, (∑ j, (Complex.sinh ((δ : ℂ)+(γ j : ℂ)*Complex.I)/
          ((δ : ℂ)+(γ j : ℂ)*Complex.I))^8*phase (t i) (γ j))=r i := by
  obtain ⟨Λ,ρ,H₀,n,hΛ,hρ,hH₀,hn,_hΛeq,_hρeq,_hH₀eq,_hnUpper,hrealize⟩ :=
    exists_prescribed_spline_finite_correction_data hδ hη ht hinj hgap
  refine ⟨n,((n : ℝ)+1)*(Real.pi/(2*Λ)),H₀,ρ/4,hn,?_,hH₀,by positivity,hrealize⟩
  positivity

#print axioms exists_prescribed_spline_finite_correction_data
#print axioms exists_prescribed_spline_finite_correction
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι]

/-- Prime-logarithm cone frequencies satisfy every nonresonance condition needed
for exact finite spline correction. -/
theorem exists_two_prime_prescribed_spline_finite_correction {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {δ : ℝ} (hδ : 0 < δ)
    (t : ι → PositiveCone (Real.log p) (Real.log q)) (hinj : Function.Injective t) :
    ∃ n : ℕ, ∃ C H₀ ε : ℝ, 0 < n ∧ 0 < C ∧ 0 < H₀ ∧ 0 < ε ∧
      ∀ H : ℝ, H₀ ≤ H → ∀ r : ι → ℂ, (∀ i, ‖r i‖ ≤ ε*n/H^8) →
      ∃ γ : Fin n → ℝ, Function.Injective γ ∧
        (∀ j, γ j ∈ Set.Icc H (H+C)) ∧
        ∀ i, (∑ j, (Complex.sinh ((δ : ℂ)+(γ j : ℂ)*Complex.I)/
          ((δ : ℂ)+(γ j : ℂ)*Complex.I))^8*phase (t i).val (γ j))=r i := by
  obtain ⟨η,hη,hgap⟩ := exists_cone_spline_shift_gap hp hq hpq
  have ht (i : ι) : 0 < (t i).val := (t i).property.1
  have hti : Function.Injective (fun i => (t i).val) :=
    fun _ _ he => hinj (Subtype.ext he)
  apply exists_prescribed_spline_finite_correction hδ hη ht hti
  intro i j
  have he : (((8 : ℤ)-2*(j.val : ℤ) : ℤ) : ℝ)=splineShift j := by
    simp only [splineShift, Int.cast_sub, Int.cast_ofNat, Int.cast_mul, Int.cast_natCast]
  have hr : |(((8 : ℤ)-2*(j.val : ℤ) : ℤ) : ℝ)| ≤ 8 := by
    rw [he]
    exact abs_splineShift_le j
  simpa only [he] using hgap (t i) (8-2*(j.val : ℤ)) hr

#print axioms exists_two_prime_prescribed_spline_finite_correction
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
