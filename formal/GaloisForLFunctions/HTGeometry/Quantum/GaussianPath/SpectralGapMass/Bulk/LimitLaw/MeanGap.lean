import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.LimitLaw.EnergyAndGap
import GaloisForLFunctions.RHTower.MobiusIncidenceClockGiniFisherFourUnit
import GaloisForLFunctions.HTGeometry.ExpSquareRayTail

/-! # Absolute first moment of the physical pair gap -/
open MeasureTheory ProbabilityTheory Filter Finset Real Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section

private theorem gap_second_moment_le {n : ℕ} (u : PathShell n) :
    (∫ x, x^2 ∂(listLaw (scaledGap u) : Measure ℝ)) ≤ 4*(shellVariance u/(n+2:ℕ)) := by
  let D : ℝ := Fintype.card (Fin (n+2)→Bool)
  let N : ℝ := (n+2:ℕ)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hD : 0 < D := Nat.cast_pos.mpr Fintype.card_pos
  have hE : (∑ i, (scaledEnergy u i)^2)=D*(shellVariance u/N) := by
    simp only [scaledEnergy,div_pow,sq_sqrt hN.le,←sum_div]
    rw [(FluxOccupation.path_spectral_moments u).2]
    simp only [D,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,N,shellVariance]
    ring
  have hpair (i j : Fin (n+2)→Bool) :
      (scaledEnergy u i-scaledEnergy u j)^2 ≤ 2*((scaledEnergy u i)^2+(scaledEnergy u j)^2) := by
    nlinarith only [sq_nonneg (scaledEnergy u i+scaledEnergy u j)]
  have hs := sum_le_sum (s:=univ) fun i _ => sum_le_sum (s:=univ) fun j _ => hpair i j
  have he : (∑ i, ∑ j, 2*((scaledEnergy u i)^2+(scaledEnergy u j)^2)) =
      4*D*(∑ i, (scaledEnergy u i)^2) := by
    simp only [←mul_sum,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,D]
    ring
  rw [he,hE] at hs
  rw [integral_listLaw,Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type]
  change (D*D)⁻¹*_ ≤ 4*(shellVariance u/N)
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by field_simp)

/-- First absolute moment of a centered Gaussian of variance twenty-four. -/
theorem gaussian_gap_absolute_integral :
    (∫ x : ℝ, |x| ∂gaussianReal 0 24)=48/sqrt (48*π) := by
  let c := (sqrt (48*π))⁻¹
  have hpdf (x : ℝ) : gaussianPDFReal 0 24 x • |x| = c*(|x| *exp (-(1/48*x^2))) := by
    simp only [gaussianPDFReal,NNReal.coe_ofNat,sub_zero,smul_eq_mul,c]
    rw [show 2*π*24=48*π by ring,show -(x^2)/(2*24)= -(1/48*x^2) by ring]
    ring
  have hr := integral_Ioi_id_mul_expNegSq (b:=(1/48:ℝ)) (a:=0) (by norm_num)
  have htail : (∫ x in Ioi (0:ℝ), x*exp (-(1/48*x^2)))=24 := by norm_num at hr ⊢; exact hr
  have hfull := integral_comp_abs (f:=fun x : ℝ => x*exp (-(1/48*x^2)))
  simp only [sq_abs,htail] at hfull
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (24:NNReal)≠0)]
  simp only [hpdf,integral_const_mul,hfull,c]
  ring

/-- The mean absolute energy difference over all pairs, divided by √N,
tends almost surely to the first absolute moment of a Gaussian of variance 24. -/
theorem gaussian_mean_absolute_gap :
    ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto (fun n =>
      ∫ x : ℝ, |x| ∂(listLaw (scaledGap (pathPauliDisorderShell ω n)) : Measure ℝ))
      atTop (𝓝 (48/sqrt (48*π))) := by
  filter_upwards [gaussian_energy_and_gap_laws,gaussian_variance_per_site] with ω h hv
  rw [←gaussian_gap_absolute_integral]
  apply _root_.RHTower.tendsto_integral_abs_of_weak_of_uniform_sq (C:=52) (by norm_num) h.2
  · filter_upwards [hv.eventually_lt_const (by norm_num : (12:ℝ)<13)] with n hn
    refine ⟨integrable_listLaw _ _,(gap_second_moment_le _).trans ?_⟩
    change _ ≤ (52:ℝ)
    exact (mul_le_mul_of_nonneg_left hn.le (by norm_num : (0:ℝ) ≤ 4)).trans_eq (by norm_num)
  · exact (memLp_id_gaussianReal' (μ:=0) (v:=24) 2 (by simp)).integrable_sq
  · rw [gaussianZero_integral_sq]
    norm_num

#print axioms gaussian_mean_absolute_gap
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
