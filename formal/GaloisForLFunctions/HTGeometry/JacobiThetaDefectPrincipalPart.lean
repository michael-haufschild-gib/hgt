import GaloisForLFunctions.HTGeometry.JacobiThetaExactDivisor

open Complex Set Filter
open scoped Topology

namespace GaloisForLFunctions

noncomputable section

def ThetaNonlatticeShift (τ h : ℂ) : Prop :=
  ¬ ∃ m n : ℤ, h = m + n * τ

def thetaLogDerivDefect (h z τ : ℂ) : ℂ :=
  thetaLogDeriv (z + h) τ - thetaLogDeriv z τ

theorem theta_add_nonzero_at_lattice_of_nonlattice {τ h : ℂ} (hτ : 0 < τ.im)
    (hh : ThetaNonlatticeShift τ h) (m n : ℤ) :
    jacobiTheta₂ (thetaHalfPeriod τ + m + n * τ + h) τ ≠ 0 := by
  intro hz
  obtain ⟨a, b, hab⟩ :=
    (jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice hτ).mp hz
  apply hh
  refine ⟨a - m, b - n, ?_⟩
  push_cast
  linear_combination hab

theorem theta_sub_nonzero_at_lattice_of_nonlattice {τ h : ℂ} (hτ : 0 < τ.im)
    (hh : ThetaNonlatticeShift τ h) (m n : ℤ) :
    jacobiTheta₂ (thetaHalfPeriod τ + m + n * τ - h) τ ≠ 0 := by
  intro hz
  obtain ⟨a, b, hab⟩ :=
    (jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice hτ).mp hz
  apply hh
  refine ⟨m - a, n - b, ?_⟩
  push_cast
  linear_combination -hab

theorem continuousAt_thetaLogDeriv_of_ne_zero {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : jacobiTheta₂ z τ ≠ 0) :
    ContinuousAt (thetaLogDeriv · τ) z := by
  exact ((jacobiTheta₂'_analyticOnNhd_fst τ hτ) z (mem_univ z)).continuousAt.div
    ((jacobiTheta₂_analyticOnNhd_fst τ hτ) z (mem_univ z)).continuousAt hz

/-- The theta defect has residue `-1` on the base theta orbit. -/
theorem tendsto_thetaLogDerivDefect_normalized_base {τ h : ℂ} (hτ : 0 < τ.im)
    (hh : ThetaNonlatticeShift τ h) (m n : ℤ) :
    let p := thetaHalfPeriod τ + m + n * τ
    Tendsto (fun z : ℂ => (z - p) * thetaLogDerivDefect h z τ)
      (𝓝[≠] p) (𝓝 (-1)) := by
  dsimp only
  let p : ℂ := thetaHalfPeriod τ + m + n * τ
  have hsing := tendsto_thetaLogDeriv_normalized_lattice hτ m n
  have hreg0 : ContinuousAt (thetaLogDeriv · τ) (p + h) :=
    continuousAt_thetaLogDeriv_of_ne_zero hτ
      (by simpa [p, add_assoc] using theta_add_nonzero_at_lattice_of_nonlattice hτ hh m n)
  have hregAt : ContinuousAt (fun z : ℂ => thetaLogDeriv (z + h) τ) p :=
    hreg0.comp_of_eq (by fun_prop) rfl
  have hreg : Tendsto (fun z : ℂ => thetaLogDeriv (z + h) τ)
      (𝓝[≠] p) (𝓝 (thetaLogDeriv (p + h) τ)) := hregAt.continuousWithinAt
  have hzero : Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 0) := by
    have hid : Tendsto (fun z : ℂ => z) (𝓝 p) (𝓝 p) := tendsto_id
    convert (hid.sub tendsto_const_nhds).mono_left nhdsWithin_le_nhds using 1
    simp
  have hregTerm : Tendsto (fun z : ℂ => (z - p) * thetaLogDeriv (z + h) τ)
      (𝓝[≠] p) (𝓝 0) := by
    convert hzero.mul hreg using 1
    all_goals simp
  have hdiff := hregTerm.sub hsing
  simpa [thetaLogDerivDefect, p, mul_sub] using hdiff

/-- The theta defect has residue `+1` on the shifted theta orbit. -/
theorem tendsto_thetaLogDerivDefect_normalized_shifted {τ h : ℂ} (hτ : 0 < τ.im)
    (hh : ThetaNonlatticeShift τ h) (m n : ℤ) :
    let p := thetaHalfPeriod τ + m + n * τ
    let q := p - h
    Tendsto (fun z : ℂ => (z - q) * thetaLogDerivDefect h z τ)
      (𝓝[≠] q) (𝓝 1) := by
  dsimp only
  let p : ℂ := thetaHalfPeriod τ + m + n * τ
  let q : ℂ := p - h
  let f : ℂ → ℂ := fun z => jacobiTheta₂ (z + h) τ
  have hqh : q + h = p := by dsimp [q]; ring
  have hfan : AnalyticAt ℂ f q := by
    have hinner : AnalyticAt ℂ (fun z : ℂ => z + h) q := by fun_prop
    have hc := ((jacobiTheta₂_analyticOnNhd_fst τ hτ) (q + h) (mem_univ _)).comp
      (f := fun z : ℂ => z + h) hinner
    simpa [f, Function.comp_def] using hc
  have hf0 : f q = 0 := by
    dsimp [f, q, p]
    convert jacobiTheta₂_thetaHalfPeriod_add_lattice_eq_zero τ m n using 1
    all_goals ring
  have hfderiv : deriv f q = jacobiTheta₂' p τ := by
    have hadd : HasDerivAt (fun z : ℂ => z + h) 1 q := (hasDerivAt_id q).add_const h
    have hcomp := (hasDerivAt_jacobiTheta₂_fst (q + h) hτ).comp q hadd
    simpa [f, hqh] using hcomp.deriv
  have hfp : jacobiTheta₂' p τ ≠ 0 := by
    simpa [p] using jacobiTheta₂'_thetaHalfPeriod_add_lattice_ne_zero hτ m n
  have hsing0 := hfan.tendsto_mul_logDeriv_simple_zero hf0 (hfderiv.symm ▸ hfp)
  have hlogeq : ∀ z : ℂ, logDeriv f z = thetaLogDeriv (z + h) τ := by
    intro z
    rw [logDeriv_apply, thetaLogDeriv]
    have hadd : HasDerivAt (fun w : ℂ => w + h) 1 z := (hasDerivAt_id z).add_const h
    have hd := (hasDerivAt_jacobiTheta₂_fst (z + h) hτ).comp z hadd
    rw [show deriv f z = jacobiTheta₂' (z + h) τ by simpa [f] using hd.deriv]
  have hsing : Tendsto (fun z : ℂ => (z - q) * thetaLogDeriv (z + h) τ)
      (𝓝[≠] q) (𝓝 1) := by
    simpa only [hlogeq] using hsing0
  have hreg0 : ContinuousAt (thetaLogDeriv · τ) q :=
    continuousAt_thetaLogDeriv_of_ne_zero hτ
      (by simpa [q, p] using theta_sub_nonzero_at_lattice_of_nonlattice hτ hh m n)
  have hreg : Tendsto (fun z : ℂ => thetaLogDeriv z τ)
      (𝓝[≠] q) (𝓝 (thetaLogDeriv q τ)) := hreg0.continuousWithinAt
  have hzero : Tendsto (fun z : ℂ => z - q) (𝓝[≠] q) (𝓝 0) := by
    have hid : Tendsto (fun z : ℂ => z) (𝓝 q) (𝓝 q) := tendsto_id
    convert (hid.sub tendsto_const_nhds).mono_left nhdsWithin_le_nhds using 1
    simp
  have hregTerm : Tendsto (fun z : ℂ => (z - q) * thetaLogDeriv z τ)
      (𝓝[≠] q) (𝓝 0) := by
    convert hzero.mul hreg using 1
    all_goals simp
  have hdiff := hsing.sub hregTerm
  simpa [thetaLogDerivDefect, q, mul_sub] using hdiff

end
end GaloisForLFunctions
