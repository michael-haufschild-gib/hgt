import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.Regularity
import GaloisForLFunctions.HTGeometry.GeneralDirichletLandau
import GaloisForLFunctions.U0.U0NaturalBoundary

/-! # The real abscissa is singular for every exterior wave -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology U0NaturalBoundary
open HTGeometry (gdTwistTerm gdSeries general_landau_summable_transfer)

private def tiltedMass (v : MissingWave) (n : ℕ+) := occupationProbability v n * Real.exp (energy n)

private def splitFrequency (n : ℕ+) := 2*energy n

private theorem response_eq_general (v : MissingWave) (s : ℂ) :
    compositionResponse v s = gdSeries (tiltedMass v) splitFrequency s := by
  apply tsum_congr
  intro n
  change (occupationProbability v n:ℂ)*Complex.exp (-(2*s-1)*(energy n:ℂ)) =
    ((occupationProbability v n * Real.exp (energy n):ℝ):ℂ)*Complex.exp (-(s*((2*energy n:ℝ):ℂ)))
  rw [Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_mul,mul_assoc,← Complex.exp_add]
  push_cast
  congr 2
  ring

private theorem finiteSplit_general (v : MissingWave) (x : ℝ) :
    Summable (gdTwistTerm (tiltedMass v) splitFrequency x 0) ↔ finiteSplit v (x:ℂ) := by
  rw [← response_absolute_iff]
  have he (n : ℕ+) : gdTwistTerm (tiltedMass v) splitFrequency x 0 n =
      ‖(occupationProbability v n:ℂ)*heat (2*(x:ℂ)-1) n‖ := by
    rw [compositionTerm_norm,gdTwistTerm,tiltedMass,splitFrequency,pow_zero,mul_one,
      mul_assoc,← Real.exp_add,shellMass,Complex.ofReal_re,mul_comm (occupationProbability v n)]
    congr 2
    ring
  exact (congrArg Summable (funext he)).to_iff

/-- Positivity makes the real point of every individual split abscissa an obstruction to analytic continuation from its right half-plane. -/
theorem real_split_abscissa_singular (v : MissingWave) :
    ¬ ContinuesAcross (compositionResponse v) {s : ℂ | splitAbscissa v < s.re} (splitAbscissa v:ℂ) := by
  classical
  let θ := splitAbscissa v
  rintro ⟨g,hg,he⟩
  let G := fun s : ℂ => if θ < s.re then compositionResponse v s else g s
  have hG : AnalyticAt ℂ G (θ:ℂ) := by
    apply hg.congr
    filter_upwards [eventually_nhdsWithin_iff.mp he] with s hs
    by_cases h : θ < s.re
    · exact (hs h).trans (if_pos h).symm
    · exact (if_neg h).symm
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hG.eventually_analyticAt
  let d := r/8
  have hd : 0 < d := div_pos hr (by norm_num)
  let R : NNReal := ⟨4*d,by positivity⟩
  have hc : dist (((θ+d+d:ℝ):ℂ)) (θ:ℂ) = 2*d := by
    rw [dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      show θ+d+d-θ = 2*d by ring,abs_of_nonneg (by positivity)]
  have hdiff : DifferentiableOn ℂ G (Metric.closedBall (((θ+d+d:ℝ):ℂ)) (R:ℝ)) := by
    intro z hz
    have hz' : dist z (((θ+d+d:ℝ):ℂ)) ≤ 4*d := hz
    have ht := dist_triangle z (((θ+d+d:ℝ):ℂ)) (θ:ℂ)
    rw [hc] at ht
    have hrad : r = 8*d := by dsimp [d]; ring
    have hb : z ∈ Metric.ball (θ:ℂ) r := lt_of_le_of_lt ht (by linarith only [hz',hrad,hd])
    exact (hball hb).differentiableAt.differentiableWithinAt
  have hstart := (finiteSplit_general v (θ+d)).mpr ((finiteSplit_iff_abscissa v _).mpr
    (Or.inl (show θ < θ+d by linarith only [hd])))
  have hsmall := general_landau_summable_transfer
    (a := tiltedMass v) (lam := splitFrequency)
    (fun n => mul_nonneg ((exteriorLaw v).property.1 n) (Real.exp_pos _).le)
    (fun n => mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
      (Real.log_nonneg (show (1:ℝ) ≤ n.val by exact_mod_cast n.pos)))
    hstart hd hdiff
    (fun s hs => (if_pos (show θ < s.re by linarith only [hs,hd])).trans (response_eq_general v s))
    (σ := θ-d) (show θ+d+d-4*d < θ-d by linarith only [hd])
  have hbad := (finiteSplit_iff_abscissa v _).mp ((finiteSplit_general v _).mp hsmall)
  change θ < θ-d ∨ θ = θ-d ∧ _ at hbad
  rcases hbad with h | ⟨h,_⟩ <;> linarith only [h,hd]

/-- A regular germ of the measured response extends to an entire right half-plane exactly when that half-plane lies above the split abscissa. -/
theorem response_halfPlane_iff (v : MissingWave) (a : ℝ) :
    (∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | a < s.re} ∧
      ∃ z : ℂ, a < z.re ∧ splitAbscissa v < z.re ∧ G =ᶠ[𝓝 z] compositionResponse v) ↔
      splitAbscissa v ≤ a := by
  constructor
  · rintro ⟨G,hG,z,_,hz,he⟩
    by_contra! ha
    apply real_split_abscissa_singular v
    have hG' : AnalyticOnNhd ℂ G {w : ℂ | splitAbscissa v < w.re} := fun w hw => hG w (ha.trans hw)
    have hF : AnalyticOnNhd ℂ (compositionResponse v) {w : ℂ | splitAbscissa v < w.re} :=
      fun _ hw => compositionResponse_analytic_at v hw
    have hagree := hG'.eqOn_of_preconnected_of_eventuallyEq hF (convex_halfSpace_re_gt _).isPreconnected hz he
    exact ⟨G,hG _ ha,Filter.eventually_of_mem self_mem_nhdsWithin (fun _ hw => hagree hw)⟩
  · intro ha
    have hz : a < a+1 := lt_add_one a
    exact ⟨compositionResponse v,fun _ hw => compositionResponse_analytic_at v (ha.trans_lt hw),
      ((a+1:ℝ):ℂ),hz,ha.trans_lt hz,Filter.EventuallyEq.rfl⟩

#print axioms real_split_abscissa_singular
#print axioms response_halfPlane_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
