import GaloisForLFunctions.ExceptionalLayerTheory.RecoveringZeroMultiplicityFromParabolicHadamardReadings
import GaloisForLFunctions.ExceptionalLayerTheory.ShrinkingDiskAreasAtARadialPole
import GaloisForLFunctions.RHTower.XiLogDerivNotHolonomic

/-!
# Multiplicity from the areas of higher logarithmic derivatives

At an order-m point the j-th derivative of ξ'/ξ has leading polar
coefficient of magnitude m j!. In a disk of radius a/u its level
u^(j+1) consequently has scaled area π min(a,(m j!)^(1/(j+1)))².
For j=1 a sufficiently wide aperture reads the linear multiplicity
directly. A unit aperture distinguishes zeros from regular points
at every derivative order.
-/

noncomputable section
open Complex Filter MeasureTheory Metric Set Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The actual superlevel set of the j-th logarithmic derivative in an
aperture of radius a/u, omitting its centre. -/
def xiDerivativeWindow (j : ℕ) (ρ : ℂ) (a u : ℝ) :=
  {z | z∈ball ρ (a/u) ∧ z≠ρ ∧ u^(j+1)<‖iteratedDeriv j (logDeriv xi) z‖}

private abbrev rootExponent (j : ℕ) := ((j+1:ℕ):ℝ)⁻¹
private def rootSignal (j : ℕ) (z : ℂ) := ‖iteratedDeriv j (logDeriv xi) z‖^(rootExponent j)
private theorem hroot (j : ℕ) : 0<rootExponent j := by unfold rootExponent; positivity

theorem analyticAt_iterated_log_derivative {f : ℂ → ℂ} {z : ℂ}
    (ha : AnalyticAt ℂ f z) (hz : f z≠0) (j : ℕ) :
    AnalyticAt ℂ (iteratedDeriv j (logDeriv f)) z := by
  induction j with
  | zero =>
    rw [iteratedDeriv_zero,logDeriv]
    exact ha.deriv.div ha hz
  | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- The logarithmic derivative and all its derivatives are analytic at
every regular point of ξ. -/
theorem analyticAt_hadamard_derivative {z : ℂ} (hz : xi z≠0) (j : ℕ) :
    AnalyticAt ℂ (iteratedDeriv j (logDeriv xi)) z :=
  analyticAt_iterated_log_derivative (xi_differentiable.analyticAt z) hz j

/-- Taking the (j+1)-st root turns the pole of the j-th logarithmic
derivative into a radial singularity of degree one. -/
theorem analytic_log_derivative_radial_residue {f : ℂ → ℂ} {ρ : ℂ}
    (ha : AnalyticAt ℂ f ρ) (hn : analyticOrderAt f ρ≠⊤) (j : ℕ) :
    Tendsto (fun z => dist z ρ*‖iteratedDeriv j (logDeriv f) z‖^(((j+1:ℕ):ℝ)⁻¹))
      (𝓝[≠] ρ) (𝓝 ((((analyticOrderAt f ρ).toNat:ℝ)*j.factorial)^(((j+1:ℕ):ℝ)⁻¹))) := by
  by_cases hz : f ρ=0
  · have h := (logDeriv_iteratedDeriv_residue_of_zero ha hn hz j).norm
    simp only [norm_mul,norm_pow,Complex.norm_natCast,norm_neg,norm_one,one_pow,one_mul] at h
    have hs := h.rpow_const (p:=rootExponent j) (Or.inr (hroot j).le)
    apply hs.congr
    intro z
    change (‖z-ρ‖^(j+1)*‖iteratedDeriv j (logDeriv f) z‖)^rootExponent j=_
    simp only [rootExponent,dist_eq_norm,
      Real.mul_rpow (pow_nonneg (norm_nonneg _) _) (norm_nonneg _),
      Real.pow_rpow_inv_natCast (norm_nonneg _) (Nat.succ_ne_zero j)]
  · have hc := (analyticAt_iterated_log_derivative ha hz j).continuousAt.norm.rpow_const
      (p:=rootExponent j) (Or.inr (hroot j).le)
    have hdist : ContinuousAt (fun z : ℂ => dist z ρ) ρ := continuousAt_id.dist continuousAt_const
    have hp : Tendsto (fun z => dist z ρ*‖iteratedDeriv j (logDeriv f) z‖^(rootExponent j))
        (𝓝[≠] ρ) (𝓝 (dist ρ ρ*‖iteratedDeriv j (logDeriv f) ρ‖^(rootExponent j))) :=
      (hdist.mul hc).tendsto.mono_left nhdsWithin_le_nhds
    have he : analyticOrderAt f ρ=0 := analyticOrderAt_eq_zero.mpr (Or.inr hz)
    rw [he,ENat.toNat_zero,Nat.cast_zero,zero_mul,Real.zero_rpow (hroot j).ne']
    simpa only [dist_self,zero_mul] using hp

/-- The radial leading coefficient at every point of ξ, including its
regular points. -/
theorem xi_log_derivative_radial_residue (ρ : ℂ) (j : ℕ) :
    Tendsto (fun z => dist z ρ*‖iteratedDeriv j (logDeriv xi) z‖^(((j+1:ℕ):ℝ)⁻¹))
      (𝓝[≠] ρ) (𝓝 (((hadamardOrder ρ:ℝ)*j.factorial)^(((j+1:ℕ):ℝ)⁻¹))) :=
  analytic_log_derivative_radial_residue (xi_differentiable.analyticAt ρ) (xi_order_ne_top ρ) j

/-- The full aperture profile holds at both genuine zeros and regular
points for every derivative order and every nonnegative aperture. -/
theorem xi_derivative_area_profile (ρ : ℂ) (j : ℕ) {a : ℝ} (ha : 0≤a) :
    Tendsto (fun u : ℝ => u^2*volume.real (xiDerivativeWindow j ρ a u)) atTop
      (𝓝 (Real.pi*(min a (((hadamardOrder ρ:ℝ)*j.factorial)^(((j+1:ℕ):ℝ)⁻¹)))^2)) := by
  have hp : 0≤((hadamardOrder ρ:ℝ)*j.factorial)^rootExponent j :=
    Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
  apply (radial_level_area_profile (f:=rootSignal j) hp (xi_log_derivative_radial_residue ρ j) ha).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  have he : radialLevelWindow (rootSignal j) ρ a u = xiDerivativeWindow j ρ a u := by
    ext z
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    change u<‖iteratedDeriv j (logDeriv xi) z‖^rootExponent j ↔
      u^(j+1)<‖iteratedDeriv j (logDeriv xi) z‖
    rw [← Real.rpow_lt_rpow_iff (pow_nonneg hu.le _) (norm_nonneg _) (hroot j)]
    rw [show (u^(j+1))^(rootExponent j)=u from
      Real.pow_rpow_inv_natCast hu.le (Nat.succ_ne_zero j)]
  rw [he]

/-- Above aperture √m, the first derivative's area has coefficient πm.
At a regular point the limiting coefficient is zero. -/
theorem first_hadamard_derivative_area (ρ : ℂ) {a : ℝ}
    (ha : Real.sqrt (hadamardOrder ρ)≤a) :
    Tendsto (fun u : ℝ => u^2*volume.real (xiDerivativeWindow 1 ρ a u)) atTop
      (𝓝 (Real.pi*(hadamardOrder ρ:ℝ))) := by
  have h := xi_derivative_area_profile ρ 1 ((Real.sqrt_nonneg _).trans ha)
  have he : ((hadamardOrder ρ:ℝ)*(1:ℕ).factorial)^(((1+1:ℕ):ℝ)⁻¹)=Real.sqrt (hadamardOrder ρ) := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rwa [he,min_eq_right ha,Real.sq_sqrt (Nat.cast_nonneg _)] at h

/-- A unit aperture gives the same binary decision at every derivative
order. Its limiting area coefficient is π at each zero and zero elsewhere. -/
theorem unit_aperture_detects_xi_zeros (ρ : ℂ) (j : ℕ) :
    Tendsto (fun u : ℝ => u^2*volume.real (xiDerivativeWindow j ρ 1 u)) atTop
      (𝓝 (if xi ρ=0 then Real.pi else 0)) := by
  have h := xi_derivative_area_profile ρ j (a:=1) zero_le_one
  by_cases hz : xi ρ=0
  · have hm : 1≤hadamardOrder ρ := Nat.one_le_iff_ne_zero.mpr
      (fun hn => (hadamardOrder_zero_iff ρ).mp hn hz)
    have hC : (1:ℝ)≤(hadamardOrder ρ:ℝ)*j.factorial := one_le_mul_of_one_le_of_one_le
      (by exact_mod_cast hm) (by exact_mod_cast j.factorial_pos)
    have hroot' : 1≤((hadamardOrder ρ:ℝ)*j.factorial)^(((j+1:ℕ):ℝ)⁻¹) :=
      Real.one_le_rpow hC (hroot j).le
    simpa only [if_pos hz,min_eq_left hroot',one_pow,mul_one] using h
  · have hn : ((j+1:ℕ):ℝ)⁻¹ ≠ 0 := (hroot j).ne'
    simpa only [if_neg hz,(hadamardOrder_zero_iff ρ).mpr hz,Nat.cast_zero,zero_mul,
      Real.zero_rpow hn,min_eq_right zero_le_one,zero_pow (by decide : 2≠0),
      mul_zero] using h

#print axioms xi_derivative_area_profile
#print axioms first_hadamard_derivative_area
#print axioms unit_aperture_detects_xi_zeros
end GaloisForLFunctions.ExceptionalLayerTheory
