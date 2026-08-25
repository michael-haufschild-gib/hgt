import GaloisForLFunctions.HTGeometry.BoundedRealPartHardy
import GaloisForLFunctions.HTGeometry.BallLogarithm
import GaloisForLFunctions.HTGeometry.DiskMultiplierBoundary
import GaloisForLFunctions.HTGeometry.HardyDiskRadialPointwise

/-!
# Hardy boundary of a bounded invertible analytic logarithm

A disk multiplier bounded away from zero has a normalized analytic logarithm.  Its real part is
bounded from the multiplier's upper and lower modulus bounds, hence the logarithm belongs to `H²`.
Taking one common radial subsequence proves the exact almost-everywhere exponential identity between
the multiplier boundary and the logarithm's Hardy boundary.
-/

open Complex Filter Metric Real Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A bounded invertible disk multiplier admits a normalized analytic logarithm with bounded real
part. -/
theorem exists_boundedRealPart_log
    (phi : DiskMultiplier) {c : ℝ} (hc : 0 < c)
    (hlo : ∀ z ∈ ball (0 : ℂ) 1, c ≤ ‖phi.fn z‖) :
    ∃ g : ℂ → ℂ, ∃ C : ℝ,
      DifferentiableOn ℂ g (ball 0 1) ∧ g 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) 1,
        phi.fn z = phi.fn 0 * Complex.exp (g z)) ∧
      ∀ z ∈ ball (0 : ℂ) 1, |(g z).re| ≤ C := by
  have hne : ∀ z ∈ ball (0 : ℂ) 1, phi.fn z ≠ 0 :=
    fun z hz => norm_pos_iff.mp (lt_of_lt_of_le hc (hlo z hz))
  obtain ⟨g, hg, hg0, hgeq⟩ := exists_log_on_ball (by norm_num) phi.diff hne
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have hphi0pos : 0 < ‖phi.fn 0‖ := lt_of_lt_of_le hc (hlo 0 h0mem)
  let C : ℝ := max |Real.log (c / ‖phi.fn 0‖)|
    |Real.log (phi.bd / ‖phi.fn 0‖)|
  refine ⟨g, C, hg, hg0, hgeq, ?_⟩
  intro z hz
  have hmod := congrArg norm (hgeq z hz)
  rw [norm_mul, Complex.norm_exp] at hmod
  have hratio : Real.exp (g z).re = ‖phi.fn z‖ / ‖phi.fn 0‖ := by
    rw [eq_div_iff hphi0pos.ne']
    simpa [mul_comm] using hmod.symm
  have hratioPos : 0 < ‖phi.fn z‖ / ‖phi.fn 0‖ :=
    div_pos (lt_of_lt_of_le hc (hlo z hz)) hphi0pos
  have hre : (g z).re = Real.log (‖phi.fn z‖ / ‖phi.fn 0‖) := by
    rw [← hratio, Real.log_exp]
  have hlower : Real.log (c / ‖phi.fn 0‖) ≤ (g z).re := by
    rw [hre]
    exact Real.log_le_log
      (div_pos hc hphi0pos)
      (div_le_div_of_nonneg_right (hlo z hz) hphi0pos.le)
  have hupper : (g z).re ≤ Real.log (phi.bd / ‖phi.fn 0‖) := by
    rw [hre]
    exact Real.log_le_log hratioPos
      (div_le_div_of_nonneg_right (phi.bd_le z hz) hphi0pos.le)
  rw [abs_le]
  constructor
  · calc
      -C ≤ -|Real.log (c / ‖phi.fn 0‖)| :=
        neg_le_neg (le_max_left _ _)
      _ ≤ Real.log (c / ‖phi.fn 0‖) := neg_abs_le _
      _ ≤ (g z).re := hlower
  · exact hupper.trans (le_trans (le_abs_self _) (le_max_right _ _))

/-- Normalized bounded-real-part analytic logarithm of a bounded invertible multiplier. -/
structure BoundedInvertibleLog (phi : DiskMultiplier) where
  fn : ℂ → ℂ
  bound : ℝ
  diff : DifferentiableOn ℂ fn (ball 0 1)
  zero : fn 0 = 0
  center_ne_zero : phi.fn 0 ≠ 0
  exp_eq : ∀ z ∈ ball (0 : ℂ) 1,
    phi.fn z = phi.fn 0 * Complex.exp (fn z)
  re_bound : ∀ z ∈ ball (0 : ℂ) 1, |(fn z).re| ≤ bound

/-- Choose the normalized logarithm supplied by a positive global lower modulus bound. -/
noncomputable def BoundedInvertibleLog.ofLowerBound
    (phi : DiskMultiplier) {c : ℝ} (hc : 0 < c)
    (hlo : ∀ z ∈ ball (0 : ℂ) 1, c ≤ ‖phi.fn z‖) :
    BoundedInvertibleLog phi :=
  Classical.choice (by
    obtain ⟨g, C, hg, hg0, hgeq, hC⟩ :=
      exists_boundedRealPart_log phi hc hlo
    have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
    have hcenter : phi.fn 0 ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le hc (hlo 0 h0mem))
    exact ⟨⟨g, C, hg, hg0, hcenter, hgeq, hC⟩⟩)

/-- `H²` coefficient vector of the analytic logarithm. -/
def BoundedInvertibleLog.hardy {phi : DiskMultiplier}
    (L : BoundedInvertibleLog phi) : HardyDisk :=
  boundedRealPartHardy L.diff L.zero L.re_bound

theorem BoundedInvertibleLog.hardyFun_eq {phi : DiskMultiplier}
    (L : BoundedInvertibleLog phi) {z : ℂ} (hz : ‖z‖ < 1) :
    hardyFun L.hardy z = L.fn z :=
  hardyFun_boundedRealPartHardy L.diff L.zero L.re_bound hz

/-- Exact a.e. boundary exponential identity for the multiplier and its `H²` logarithm. -/
theorem BoundedInvertibleLog.boundary_exp_ae
    {phi : DiskMultiplier} (L : BoundedInvertibleLog phi) :
    diskMultiplierBoundaryFun phi =ᵐ[circleLebesgue]
      fun z => phi.fn 0 * Complex.exp
        ((hardyDiskBoundary L.hardy : Circle → ℂ) z) := by
  obtain ⟨base, hbase, hlog⟩ := exists_hardyDiskRadialBoundary_subseq_ae L.hardy
  obtain ⟨ns, hns, hphi⟩ :=
    exists_diskMultiplierRadialBoundary_subseq_ae_of_strictMono phi hbase
  filter_upwards [hlog, hphi] with z hzlog hzphi
  have hzlogSub : Tendsto
      (fun i => hardyDiskRadialBoundaryFun (base (ns i)) L.hardy z)
      atTop (𝓝 ((hardyDiskBoundary L.hardy : Circle → ℂ) z)) :=
    hzlog.comp hns.tendsto_atTop
  have hright : Tendsto
      (fun i => phi.fn 0 * Complex.exp
        (hardyDiskRadialBoundaryFun (base (ns i)) L.hardy z))
      atTop (𝓝 (phi.fn 0 * Complex.exp
        ((hardyDiskBoundary L.hardy : Circle → ℂ) z))) :=
    tendsto_const_nhds.mul (Complex.continuous_exp.tendsto _ |>.comp hzlogSub)
  have hradial (i : ℕ) :
      diskMultiplierRadialBoundaryFun (base (ns i)) phi z =
        phi.fn 0 * Complex.exp
          (hardyDiskRadialBoundaryFun (base (ns i)) L.hardy z) := by
    let w : ℂ := (hardyDiskAbelRadius (base (ns i)) : ℂ) * (z : ℂ)
    have hw : w ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hardyDiskAbelRadius_nonneg _), Circle.norm_coe, mul_one]
      exact hardyDiskAbelRadius_lt_one _
    rw [diskMultiplierRadialBoundaryFun, hardyDiskRadialBoundaryFun]
    rw [L.exp_eq w hw]
    congr 2
    have hwnorm : ‖w‖ < 1 := by
      simpa [mem_ball, dist_zero_right] using hw
    exact (L.hardyFun_eq hwnorm).symm
  have hright' : Tendsto
      (fun i => diskMultiplierRadialBoundaryFun (base (ns i)) phi z)
      atTop (𝓝 (phi.fn 0 * Complex.exp
        ((hardyDiskBoundary L.hardy : Circle → ℂ) z))) :=
    hright.congr' (Eventually.of_forall fun i => (hradial i).symm)
  exact tendsto_nhds_unique hzphi hright'

end GaloisForLFunctions.HTGeometry
