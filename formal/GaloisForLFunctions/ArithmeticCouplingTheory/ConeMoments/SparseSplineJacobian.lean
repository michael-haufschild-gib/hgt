import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SparseSplineSampling
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineNodeAverages
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineDiscreteJacobian

/-!
# Sparse spline Jacobian bounds

Continuous ordinary and conjugate pairings control the real node-motion
Jacobian after simultaneous stratified sampling. The row error is the
continuous endpoint bound divided by the node count plus twice the frequency
count times the sampling error.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι] {n : ℕ}

lemma norm_splineNodeAverage_sub_center_le (hn : 0 < n) (x : Fin n → ℝ)
    {f : ℝ → ℂ} {a A ε : ℝ} {z : ℂ}
    (hmean : ‖(∫ u in a..(a+n), f u)-(n:ℂ)*z‖ ≤ A)
    (hsample : ‖splineNodeAverage x f-(∫ u in a..(a+n), f u)/(n:ℂ)‖ ≤ ε) :
    ‖splineNodeAverage x f-z‖ ≤ A/(n:ℝ)+ε := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : splineNodeAverage x f-z=
      ((∫ u in a..(a+n), f u)-(n:ℂ)*z)/(n:ℂ)+
      (splineNodeAverage x f-(∫ u in a..(a+n), f u)/(n:ℂ)) := by
    field_simp [hnC]
    ring
  rw [he]
  refine (norm_add_le _ _).trans (add_le_add ?_ hsample)
  rw [norm_div,Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hmean hnR.le

/-- Simultaneous sampling and continuous biorthogonality control the entire
real node-motion Jacobian with polynomial finite-data costs. -/
theorem norm_sparse_spline_jacobian_defect_le {δ a ε : ℝ} (hδ : 0 < δ)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) (hinj : Function.Injective t)
    (hn : 0 < n) (x : Fin n → ℝ)
    (hsample : ∀ k : SplineSamplingIndex ι,
      ‖splineNodeAverage x (splineSamplingFamily δ t k)-
        (∫ u in a..(a+n), splineSamplingFamily δ t k u)/(n:ℂ)‖ ≤ ε)
    (y : ι → ℂ) (i : ι) :
    ‖splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*
      (splineHeightCorrection δ t y u:ℂ))-y i‖ ≤
      ((∑ j, splineJacobianEntryBound δ (t i) (t j))/(n:ℝ)+
        2*(Fintype.card ι:ℝ)*ε)*‖y‖ := by
  classical
  let A : ι → ι → ℝ := fun i j =>
    (2*splinePairBoundaryBound δ (t j)+2/|t i-t j|)/(n:ℝ)+ε
  let B : ι → ι → ℝ := fun i j =>
    (2*splinePairBoundaryBound δ (t j)+
      2*((1+splineRatio δ)^8/(t i+t j)*(1/(1-splineRatio δ)^8)))/(n:ℝ)+ε
  have hA (i j : ι) :
      ‖splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*splineDual δ (t j) u)-
        (if i=j then 1 else 0)‖ ≤ A i j := by
    by_cases hij : i=j
    · subst j
      have hm := norm_integral_spline_pair_self_sub_length_le hδ (ht i) a (a+n)
      rw [show a+(n:ℝ)-a=(n:ℝ) by ring] at hm
      have hm' : ‖(∫ u in a..(a+n), shiftedSplineSlope δ (t i) u*splineDual δ (t i) u)-
          (n:ℂ)*(1:ℂ)‖ ≤ 2*splinePairBoundaryBound δ (t i) := by simpa using hm
      simpa only [A,ite_true,sub_self,abs_zero,div_zero,add_zero] using
        norm_splineNodeAverage_sub_center_le hn x hm' (hsample (.inr (.inl (i,i))))
    · have hm := norm_integral_spline_pair_le_of_ne hδ (ht j)
        (fun he => hij (hinj he)) a (a+n)
      have hm' : ‖(∫ u in a..(a+n), shiftedSplineSlope δ (t i) u*splineDual δ (t j) u)-
          (n:ℂ)*(0:ℂ)‖ ≤ 2*splinePairBoundaryBound δ (t j)+2/|t i-t j| := by
        simpa only [mul_zero,sub_zero] using hm
      simpa only [A,if_neg hij,sub_zero] using
        norm_splineNodeAverage_sub_center_le hn x hm' (hsample (.inr (.inl (i,j))))
  have hB (i j : ι) :
      ‖splineNodeAverage x (fun u => shiftedSplineSlope δ (t i) u*
        (starRingEnd ℂ) (splineDual δ (t j) u))‖ ≤ B i j := by
    have hm := norm_integral_spline_conj_pair_le hδ (ht j) (ht i) a (a+n)
    have hm' : ‖(∫ u in a..(a+n), shiftedSplineSlope δ (t i) u*
        (starRingEnd ℂ) (splineDual δ (t j) u))-(n:ℂ)*(0:ℂ)‖ ≤
        2*splinePairBoundaryBound δ (t j)+
          2*((1+splineRatio δ)^8/(t i+t j)*(1/(1-splineRatio δ)^8)) := by
      simpa only [mul_zero,sub_zero] using hm
    simpa only [B,sub_zero] using
      norm_splineNodeAverage_sub_center_le hn x hm' (hsample (.inr (.inr (i,j))))
  refine (norm_splineNodeAverage_slope_correction_sub_le x hA hB y i).trans_eq ?_
  congr 1
  have hentry (j : ι) : A i j+B i j=splineJacobianEntryBound δ (t i) (t j)/(n:ℝ)+2*ε := by
    dsimp only [A,B,splineJacobianEntryBound]
    ring
  simp_rw [hentry]
  rw [sum_add_distrib,← sum_div]
  simp only [sum_const,card_univ,nsmul_eq_mul]
  ring

#print axioms norm_sparse_spline_jacobian_defect_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
