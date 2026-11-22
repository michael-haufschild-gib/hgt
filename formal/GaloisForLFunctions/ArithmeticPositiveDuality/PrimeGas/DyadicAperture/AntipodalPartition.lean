import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.RejectedHeat
import GaloisForLFunctions.HTGeometry.EulerQGammaContinuation
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The common double pole at maximal aperture

Removed occupations have a holomorphic partition throughout the open
half-plane to the right of the critical line. All clock times preserve
the principal part of the squared zeta partition at one.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Binary

open SampledClocks CopyExchange Set Filter Topology

theorem correction_analytic (t : ℝ) : AnalyticOnNhd ℂ (correction t) {s : ℂ | 1/2 < s.re} := by
  intro s hs
  change 1/2 < s.re at hs
  let β := (1/2+s.re)/2
  have hβ : 1/2 < β := by dsimp [β]; linarith only [hs]
  have hbs : β < s.re := by dsimp [β]; linarith only [hs]
  let U := {w : ℂ | β < w.re}
  have hu : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  let F (x : {x // rejected t x}) (w : ℂ) := wordHeat w x.val
  have hsum : Summable (fun x : {x // rejected t x} => ‖F x (β:ℂ)‖) :=
    (sectorHeat_iff _ _).mp ((rejected_heat_iff t (β:ℂ)).mpr fun _ => hβ)
  have hf (x : {x // rejected t x}) : DifferentiableOn ℂ (F x) U := by
    change DifferentiableOn ℂ (fun w => wordHeat w x.val) U
    simp only [wordHeat_total,heat]
    fun_prop
  have hb (x : {x // rejected t x}) (w : ℂ) (hw : w ∈ U) : ‖F x w‖ ≤ ‖F x (β:ℂ)‖ := by
    simp only [F,wordHeat_total,norm_heat,Complex.ofReal_re,Real.exp_le_exp]
    apply mul_le_mul_of_nonneg_right (neg_le_neg (show β < w.re from hw).le)
    exact Real.log_nonneg (by exact_mod_cast (∏ i, x.val i).pos)
  exact (Complex.differentiableOn_tsum_of_summable_norm hsum hf hu hb).analyticOnNhd hu s hbs

/-- Continuation of the measured maximal-aperture partition into Re(s)>1/2. -/
def continued (t : ℝ) (s : ℂ) := riemannZeta s^2-correction t s

theorem continued_trace (t : ℝ) (s : {z : ℂ // AbsoluteHeat (measured t Real.pi) z}) :
    ContinuousLinearMap.opTrace (sectorHeat (measured t Real.pi) s) = continued t s.val := maximal_trace t s

theorem continued_meromorphic (t : ℝ) : MeromorphicOn (continued t) {z : ℂ | 1/2 < z.re} :=
  fun s hs => ((HTGeometry.meromorphicAt_riemannZeta s).pow 2).sub (correction_analytic t s hs).meromorphicAt

theorem continued_regular (t : ℝ) : AnalyticOnNhd ℂ (fun z => continued t z-riemannZeta z^2)
    {z : ℂ | 1/2 < z.re} := by
  have he : (fun z => continued t z-riemannZeta z^2) = fun z => -correction t z := by
    funext z
    unfold continued
    ring
  rw [he]
  exact fun s hs => (correction_analytic t s hs).neg

theorem leading_double_pole (t : ℝ) :
    Tendsto (fun s : ℂ => (s-1)^2*continued t s) (𝓝[≠] 1) (𝓝 1) := by
  have hc := (correction_analytic t 1 (by norm_num)).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (1:ℂ) ≤ 𝓝 1)
  have hz : Tendsto (fun s : ℂ => s-1) (𝓝[≠] 1) (𝓝 0) := by
    simpa only [id_eq,sub_self] using (tendsto_id.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (1:ℂ) ≤ 𝓝 1)).sub_const 1
  have h := (riemannZeta_residue_one.pow 2).sub ((hz.pow 2).mul hc)
  simp only [one_pow,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,sub_zero] at h
  refine h.congr fun s => ?_
  unfold continued
  ring

#print axioms correction_analytic
#print axioms continued_trace
#print axioms continued_meromorphic
#print axioms continued_regular
#print axioms leading_double_pole

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Binary
