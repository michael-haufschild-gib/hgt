import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Conditioning.Gibbs
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Window.AnalyticMoments
import GaloisForLFunctions.RHTower.Sieve.MoebiusDoubleLogRealCutoff

/-! # Energy moments with a moving largest-prime cutoff -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime

open Filter Topology Set _root_.RHTower _root_.RHTower.BAGTrace

def cutoffScale (c : ℝ) (h : Ioi (0:ℝ)) := h.val*Real.log (primeCut c h)

private theorem raw_cut_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun h : Ioi (0:ℝ) => Real.exp (c/h.val)) criticalApproach atTop := by
  have hv : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  simpa only [div_eq_mul_inv,Function.comp_def] using
    Real.tendsto_exp_atTop.comp ((tendsto_inv_nhdsGT_zero.comp hv).const_mul_atTop hc)

theorem primeCut_atTop {c : ℝ} (hc : 0 < c) : Tendsto (primeCut c) criticalApproach atTop :=
  tendsto_nat_floor_atTop.comp (raw_cut_atTop hc)

theorem cutoffScale_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (cutoffScale c) criticalApproach (𝓝 c) := by
  have H := (Sieve.tendsto_log_natFloor_div_log_one.comp (raw_cut_atTop hc)).const_mul c
  rw [mul_one] at H
  apply H.congr
  intro h
  change c*(Real.log (primeCut c h)/Real.log (Real.exp (c/h.val))) = h.val*Real.log (primeCut c h)
  have hh : h.val ≠ 0 := (show 0 < h.val from h.property).ne'
  rw [Real.log_exp]
  field_simp [hc.ne',hh]

private theorem unit_partition (N : ℕ) (w : ℂ) :
    Window.unitTransform N w = Window.partition N (Window.windowTemperature N w)/Window.partition N 1 := by
  have H := Window.energyMoment_eq N 0 w
  simpa only [Window.unitTransform,Complex.ofReal_zero,zero_add,Window.windowTemperature,zero_div,sub_zero] using H

/-- Exact change of scale from the conditioned energy to the finite trace at unit temperature. -/
theorem transform_unit {c : ℝ} {h : Ioi (0:ℝ)} (hN : 2 ≤ primeCut c h) (z : ℂ) :
    momentProbe c h 0 z = Window.unitTransform (primeCut c h) ((cutoffScale c h:ℂ)*(z-1))/
      Window.unitTransform (primeCut c h) (-(cutoffScale c h:ℂ)) := by
  let N := primeCut c h
  have hL : (Real.log N:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast (show 1 < N from hN))).ne'
  have hs (w : ℂ) : Window.windowTemperature N ((cutoffScale c h:ℂ)*(w-1)) =
      1+(1-w)*(h.val:ℂ) := by
    change 1-((h.val*Real.log N:ℝ):ℂ)*(w-1)/(Real.log N:ℂ) = _
    rw [Complex.ofReal_mul]
    field_simp [hL]
    ring
  have hP : Window.partition N 1 ≠ 0 := by
    rw [show (1:ℂ) = ((1:ℝ):ℂ) by norm_cast,Window.partition_real]
    exact Complex.ofReal_ne_zero.mpr (finiteSquarefreePartition_pos _ _).ne'
  rw [transform_partition,unit_partition,unit_partition]
  change _ = (Window.partition N (Window.windowTemperature N ((cutoffScale c h:ℂ)*(z-1)))/Window.partition N 1)/
    (Window.partition N (Window.windowTemperature N (-(cutoffScale c h:ℂ)))/Window.partition N 1)
  rw [show -(cutoffScale c h:ℂ) = (cutoffScale c h:ℂ)*((0:ℂ)-1) by ring,hs z,hs 0,sub_zero,one_mul]
  exact (div_div_div_cancel_right₀ hP _ _).symm

private theorem affine_jet (F : ℂ → ℂ) (hF : Differentiable ℂ F) (a q : ℂ) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w => F (a*(w-1))/q) z =
      a^k*iteratedDeriv k F (a*(z-1))/q := by
  let g := fun w : ℂ => F (a*w)
  have hg : ContDiff ℂ k g := hF.contDiff.comp (contDiff_const.mul contDiff_id)
  have hs (w : ℂ) : F (a*(w-1))/q = q⁻¹*g (w+(-1)) := by
    rw [div_eq_inv_mul,sub_eq_add_neg]
  have hshift : ContDiffAt ℂ k (fun w : ℂ => g (w+(-1))) z :=
    (hg.comp (contDiff_id.add (contDiff_const (c := (-1:ℂ))))).contDiffAt
  rw [funext hs,iteratedDeriv_const_mul q⁻¹ hshift]
  have ht := congrFun (iteratedDeriv_comp_add_const k g (-1)) z
  have hm := congrFun (iteratedDeriv_comp_const_mul (n := k) hF.contDiff a) (z+(-1))
  change iteratedDeriv k g (z+(-1)) = a^k*iteratedDeriv k F (a*(z+(-1))) at hm
  rw [ht,hm,sub_eq_add_neg,div_eq_inv_mul]

/-- The limiting conditional moment generating function, including all complex probes. -/
def limitTransform (c : ℝ) (z : ℂ) :=
  criticalEulerCarrier ((c:ℂ)*(z-1))/criticalEulerCarrier (-(c:ℂ))

theorem limitTransform_jet (c : ℝ) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (limitTransform c) z =
      (c:ℂ)^k*iteratedDeriv k criticalEulerCarrier ((c:ℂ)*(z-1))/criticalEulerCarrier (-(c:ℂ)) :=
  affine_jet _ (fun u => ((criticalEulerExponent_hasDerivAt u).cexp).differentiableAt) _ _ k z

/-- Every energy-weighted conditional transform converges, even at a moving complex probe. -/
theorem conditioned_jet_limit {c : ℝ} (hc : 0 < c) (k : ℕ) {v : Ioi (0:ℝ) → ℂ} {z : ℂ}
    (hv : Tendsto v criticalApproach (𝓝 z)) :
    Tendsto (fun h => momentProbe c h k (v h)) criticalApproach (𝓝 (iteratedDeriv k (limitTransform c) z)) := by
  have hd := (Complex.continuous_ofReal.tendsto c).comp (cutoffScale_limit hc)
  have hj := Window.unit_jet_moving (primeCut_atTop hc) (hd.mul (hv.sub_const 1)) k
  have h0 := Window.unit_jet_moving (primeCut_atTop hc) hd.neg 0
  simp only [iteratedDeriv_zero] at h0
  have H := ((hd.pow k).mul hj).div h0 (Complex.exp_ne_zero _)
  rw [← limitTransform_jet] at H
  apply H.congr'
  filter_upwards [tendsto_atTop.mp (primeCut_atTop hc) 2] with h hN
  rw [← transform_derivative]
  rw [show momentProbe c h 0 = _ from funext (transform_unit hN),
    affine_jet _ (Window.unit_entire _) _ _ k]
  rfl

theorem conditioned_transform_limit {c : ℝ} (hc : 0 < c) (z : ℂ) :
    Tendsto (fun h => momentProbe c h 0 z) criticalApproach (𝓝 (limitTransform c z)) :=
  conditioned_jet_limit hc 0 tendsto_const_nhds

#print axioms primeCut_atTop
#print axioms cutoffScale_limit
#print axioms transform_unit
#print axioms limitTransform_jet
#print axioms conditioned_jet_limit
#print axioms conditioned_transform_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime
