import GaloisForLFunctions.RHTower.FiniteDirichletDivisorPoleSurvival
import Mathlib.Analysis.Meromorphic.Order

/-!
# Meromorphic obstruction to finite-source Mellin continuation

The literal finite-source Mellin expression is globally meromorphic. A germ
of equality at four propagates on a connected half-plane through the order
of the meromorphic discrepancy. Its unconditional surviving critical poles
exclude any analytic continuation to a half-plane whose edge is below one.
-/

noncomputable section
open Complex Filter Set Topology
namespace RHTower

/-- The full finite Mellin expression is meromorphic at every point. -/
lemma meromorphicAt_finiteDirichletDivisorMellin
    (a : ℕ →₀ ℂ) (ha : a 0 = 0) (Q : Finset Nat.Primes) (c s : ℂ) :
    MeromorphicAt (finiteDirichletDivisorMellin a Q c) s := by
  have hshift : AnalyticAt ℂ (fun z : ℂ => z - 1 / 2) s := by fun_prop
  have hnum : MeromorphicAt
      (fun z : ℂ => finiteDirichletDivisorSource a c (z - 1 / 2)) s :=
    (meromorphicAt_finiteDirichletDivisorSource a ha c _).comp_analyticAt hshift
  have he : AnalyticAt ℂ (fun z : ℂ => finitePrimeEulerDenominator Q (z - 1 / 2)) s :=
    ((differentiable_finitePrimeEulerDenominator Q).analyticAt _).comp hshift
  have hden : AnalyticAt ℂ (fun z : ℂ =>
      finitePrimeEulerDenominator Q (z - 1 / 2) * (2 * z * (z - 1 / 2))) s :=
    he.mul (by fun_prop)
  exact hnum.div hden.meromorphicAt

/-- No analytic function on a half-plane containing the surviving critical
poles can have the literal nonzero finite-source Mellin germ at four. -/
lemma no_analytic_finiteDirichletDivisorMellin_continuation
    (a : ℕ →₀ ℂ) (ha : a 0 = 0) (hne : a ≠ 0) (Q : Finset Nat.Primes) (c : ℂ)
    {b : ℝ} (hb : b < 1) {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H {s : ℂ | b < s.re})
    (hgerm : H =ᶠ[𝓝 (4 : ℂ)] finiteDirichletDivisorMellin a Q c) : False := by
  let F := finiteDirichletDivisorMellin a Q c
  let U : Set ℂ := {s : ℂ | b < s.re}
  have hsub : MeromorphicOn (H - F) U := by
    intro s hs
    exact (hH s hs).meromorphicAt.sub (meromorphicAt_finiteDirichletDivisorMellin a ha Q c s)
  have h4 : (4 : ℂ) ∈ U := by change b < (4 : ℂ).re; norm_num; linarith
  have htop4 : meromorphicOrderAt (H - F) (4 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [hgerm.filter_mono nhdsWithin_le_nhds] with z hz
    exact sub_eq_zero.mpr hz
  obtain ⟨t, _, _, _, _, hpole⟩ :=
    exists_high_simpleCritical_finiteDirichletDivisorMellin_pole a ha hne Q c 0
  have hpoint : linePt t + 1 / 2 ∈ U := by
    change b < (linePt t + 1 / 2).re
    rw [Complex.add_re, linePt_re]
    norm_num
    exact hb
  have htop : meromorphicOrderAt (H - F) (linePt t + 1 / 2) = ⊤ := by
    by_contra hn
    exact (hsub.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_halfSpace_re_gt b).isPreconnected hpoint h4 hn) htop4
  have heq : H =ᶠ[𝓝[≠] (linePt t + 1 / 2)] F := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp htop] with z hz
    exact sub_eq_zero.mp hz
  have hord := meromorphicOrderAt_congr heq
  have hnonneg := (hH _ hpoint).meromorphicOrderAt_nonneg
  rw [hord, hpole] at hnonneg
  exact (not_le_of_gt (show ((-1 : ℤ) : WithTop ℤ) < 0 by
    exact_mod_cast (show (-1 : ℤ) < 0 by omega))) hnonneg

end RHTower
