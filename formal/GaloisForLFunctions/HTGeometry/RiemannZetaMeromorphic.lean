import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Riemann zeta function is meromorphic on the plane

Off the point `1` the zeta function is analytic, because it is differentiable on the complement of
`1`, which is a neighbourhood of every other point.  At `1` the completed functional equation
presents it, on a punctured neighbourhood, as an entire function and two explicit simple poles
divided by the real gamma factor, and meromorphy depends only on the germ off the point.

mathlib records the pole of `ζ` only through the residue limit, so this global statement is not
available there.  It is the analytic input of a finite Euler modification: multiplying `ζ` by a
finite product of Euler factors leaves the result meromorphic on the whole plane.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Away from its pole the zeta function is analytic. -/
theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [(isOpen_ne (x := (1 : ℂ))).mem_nhds hs] with z hz
  exact differentiableAt_riemannZeta hz

/-- The real gamma factor is analytic on the right half plane. -/
theorem analyticAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  rw [analyticAt_iff_eventually_differentiableAt]
  have hopen : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  filter_upwards [hopen] with z hz
  have hGdef : Gammaℝ = fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) := by
    funext w
    exact Complex.Gammaℝ_def w
  rw [hGdef]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) z :=
    (differentiableAt_id.neg.div_const 2).const_cpow (Or.inl hpi)
  have hgam : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) z := by
    refine (Complex.differentiableAt_Gamma (z / 2) ?_).comp z (differentiableAt_id.div_const 2)
    intro m hm
    have hre : (z / 2).re = -(m : ℝ) := by
      rw [hm]
      simp
    have hre' : (z / 2).re = z.re / 2 := by simp
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [hre'] at hre
    linarith
  exact hpow.mul hgam

/-- **The zeta function is meromorphic on the whole plane.** -/
theorem meromorphicOn_riemannZeta : MeromorphicOn riemannZeta Set.univ := by
  intro s _
  by_cases hs : s = 1
  · subst hs
    have hform : (fun z : ℂ =>
        (completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) / Gammaℝ z)
        =ᶠ[𝓝[≠] (1 : ℂ)] riemannZeta := by
      have hne : ∀ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), z ≠ 0 :=
        nhdsWithin_le_nhds ((isOpen_ne (x := (0 : ℂ))).mem_nhds (by norm_num))
      filter_upwards [hne] with z hz
      rw [riemannZeta_def_of_ne_zero hz, completedRiemannZeta_eq]
    refine MeromorphicAt.congr ?_ hform
    have hzero : AnalyticAt ℂ (fun z : ℂ => completedRiemannZeta₀ z - 1 / z) 1 :=
      (differentiable_completedZeta₀.analyticAt 1).sub
        (analyticAt_const.div (analyticAt_id) (by norm_num))
    have hpole : MeromorphicAt (fun z : ℂ => 1 / (1 - z)) 1 :=
      (analyticAt_const (v := (1 : ℂ))).meromorphicAt.div
        (analyticAt_const.sub analyticAt_id).meromorphicAt
    have hnum : MeromorphicAt
        (fun z : ℂ => completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) 1 :=
      hzero.meromorphicAt.sub hpole
    have hden : MeromorphicAt Gammaℝ 1 :=
      (analyticAt_Gammaℝ (by norm_num)).meromorphicAt
    exact hnum.div hden
  · exact (analyticAt_riemannZeta hs).meromorphicAt

end GaloisForLFunctions.HTGeometry
