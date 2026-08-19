import GaloisForLFunctions.RHTower.RealTwistDeficitTransfer

/-!
# Divergence of the prime clock energy at every nonzero frequency

The one-line deficit `log log x − log ‖ζ(1 + 1/log x + iτ)‖` is a lower bound for the prime clock
energy `∑_{p ≤ x} (1 − cos(τ log p))/p`.  For a fixed nonzero frequency the shifted point tends to
`1 + iτ`, where `ζ` is continuous and nonzero, so the subtracted logarithm stays bounded and the
clock energy diverges.  Two distinct heights of the prime torus therefore separate at the
logarithmic-integral rate.
-/

open Filter Topology

namespace RHTower

noncomputable section

theorem tendsto_zetaLinePoint_shift (τ : ℝ) :
    Tendsto (fun x : ℝ => zetaLinePoint (1 + 1 / Real.log x) τ) atTop
      (nhds (zetaLinePoint 1 τ)) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop := Real.tendsto_log_atTop
  have hinv : Tendsto (fun x : ℝ => 1 / Real.log x) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hlog
  have hσ : Tendsto (fun x : ℝ => 1 + 1 / Real.log x) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hcont : Continuous fun σ : ℝ => zetaLinePoint σ τ := by
    unfold zetaLinePoint
    fun_prop
  exact (hcont.tendsto 1).comp hσ

theorem zetaLinePoint_ne_one {τ : ℝ} (hτ : τ ≠ 0) : zetaLinePoint 1 τ ≠ 1 := by
  intro hcon
  have him : (zetaLinePoint 1 τ).im = τ := by
    simp [zetaLinePoint]
  rw [hcon] at him
  simp at him
  exact hτ him.symm

/-- **The prime clock energy diverges at every nonzero frequency.** -/
theorem tendsto_primeClockEnergy_atTop {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto (fun x : ℝ => primeClockEnergy τ x) atTop atTop := by
  have hne : zetaLinePoint 1 τ ≠ 1 := zetaLinePoint_ne_one hτ
  have hzero : riemannZeta (zetaLinePoint 1 τ) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    rw [zetaLinePoint_re]
  have hcontζ : ContinuousAt riemannZeta (zetaLinePoint 1 τ) :=
    (differentiableAt_riemannZeta hne).continuousAt
  have hcomp : Tendsto (fun x : ℝ => riemannZeta (zetaLinePoint (1 + 1 / Real.log x) τ)) atTop
      (nhds (riemannZeta (zetaLinePoint 1 τ))) :=
    hcontζ.tendsto.comp (tendsto_zetaLinePoint_shift τ)
  have hlognorm : Tendsto
      (fun x : ℝ => Real.log ‖riemannZeta (zetaLinePoint (1 + 1 / Real.log x) τ)‖) atTop
      (nhds (Real.log ‖riemannZeta (zetaLinePoint 1 τ)‖)) := by
    have hnorm : Tendsto (fun x : ℝ => ‖riemannZeta (zetaLinePoint (1 + 1 / Real.log x) τ)‖)
        atTop (nhds ‖riemannZeta (zetaLinePoint 1 τ)‖) := hcomp.norm
    exact (Real.continuousAt_log (by simpa using hzero)).tendsto.comp hnorm
  have hloglog : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hdeficit : Tendsto (fun x : ℝ => zetaLineDeficit τ x) atTop atTop := by
    have hsum := hloglog.atTop_add hlognorm.neg
    refine hsum.congr fun x => ?_
    rw [zetaLineDeficit]
    ring
  refine Filter.tendsto_atTop_mono' atTop ?_
    (Filter.tendsto_atTop_add_const_right atTop (-zetaDeficitConst) hdeficit)
  filter_upwards [eventually_ge_atTop (Real.exp 2)] with x hx
  have := zetaLineDeficit_sub_le_primeClockEnergy (τ := τ) (x := x) hx
  linarith

end

end RHTower
