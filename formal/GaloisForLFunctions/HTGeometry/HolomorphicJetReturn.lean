import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The holomorphic jet-return bridge (Cauchy's theorem for return times)

The finite-phase argument (§5, eq. 28) needs: when the translates of a holomorphic function converge
locally uniformly, *every derivative* converges as well ("Cauchy's theorem gives the same
convergence for every derivative").  This file supplies that bridge from mathlib's Weierstrass
theorem `TendstoLocallyUniformlyOn.deriv`, iterating it to all orders.

It converts the sup-metric / local-uniform return of the almost-periodic hull (`AlmostPeriodicHull`)
into convergence of the full differential jet, which is what the recurrence-collapse step consumes.
-/

open Filter Topology

namespace GaloisForLFunctions

/-- Every iterated derivative of a function holomorphic on an open set is again holomorphic there. -/
theorem differentiableOn_iteratedDeriv {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) : ∀ j : ℕ, DifferentiableOn ℂ (iteratedDeriv j g) U
  | 0 => by simpa using hg
  | j + 1 => by
      rw [iteratedDeriv_succ]
      exact ((differentiableOn_iteratedDeriv hU hg j).analyticOnNhd hU).deriv.differentiableOn

/-- Local uniform convergence of holomorphic functions propagates locally uniformly through every
iterated derivative.  This is the compact-open, all-orders form of the holomorphic jet-return
principle; pointwise convergence of a chosen jet is an immediate specialization. -/
theorem iteratedDeriv_tendstoLocallyUniformlyOn_of_locallyUniform
    {ι : Type*} {φ : Filter ι} {U : Set ℂ}
    (hU : IsOpen U) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) :
    ∀ j : ℕ, TendstoLocallyUniformlyOn
      (fun n => iteratedDeriv j (F n)) (iteratedDeriv j f) φ U
  | 0 => by simpa using hconv
  | j + 1 => by
      have hdiff_j : ∀ᶠ n in φ,
          DifferentiableOn ℂ (iteratedDeriv j (F n)) U := by
        filter_upwards [hF] with n hn
        exact differentiableOn_iteratedDeriv hU hn j
      have hderiv :=
        (iteratedDeriv_tendstoLocallyUniformlyOn_of_locallyUniform
          hU hconv hF j).deriv hdiff_j hU
      simpa only [Function.comp_def, ← iteratedDeriv_succ] using hderiv

/-- **Jet return / Cauchy derivative convergence.**  If holomorphic functions `F n` converge to `f`
locally uniformly on an open set `U`, then at every point `z₀ ∈ U` and every order `j`, the `j`-th
derivatives converge: `F n⁽ʲ⁾(z₀) → f⁽ʲ⁾(z₀)`.  This is the all-orders derivative convergence used to
turn a return sequence into convergence of the whole differential jet. -/
theorem iteratedDeriv_tendsto_of_locallyUniform {ι : Type*} {φ : Filter ι} {U : Set ℂ}
    (hU : IsOpen U) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
    (j : ℕ) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    Tendsto (fun n => iteratedDeriv j (F n) z₀) φ (nhds (iteratedDeriv j f z₀)) := by
  exact (iteratedDeriv_tendstoLocallyUniformlyOn_of_locallyUniform
    hU hconv hF j).tendsto_at hz₀

/-- Iterated differentiation commutes with an affine shift:
`(fun w ↦ f (w + c))⁽ʲ⁾(z) = f⁽ʲ⁾(z + c)`. -/
theorem iteratedDeriv_comp_add_const (j : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    iteratedDeriv j (fun w => f (w + c)) z = iteratedDeriv j f (z + c) := by
  induction j generalizing z with
  | zero => simp
  | succ j ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hfun : iteratedDeriv j (fun w => f (w + c)) = fun w => iteratedDeriv j f (w + c) :=
        funext ih
      rw [hfun, deriv_comp_add_const]

/-- **Full differential-jet return (§5, eq. 28, all orders).**  Let `f` be holomorphic on a
vertically-invariant open set `U` (e.g. a vertical strip), let `T_l → +∞` be return times along which
the vertical translates `f(· + iT_l)` converge to `f` locally uniformly on `U`, and let `z₀ ∈ U`.
Then the whole differential jet returns: `f⁽ʲ⁾(z₀ + iT_l) → f⁽ʲ⁾(z₀)` for every order `j`.  This is
the jet-return convergence consumed by `recurrence_collapse_to_autonomous`. -/
theorem jet_return_of_translate_locallyUniform {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    {T : ℕ → ℝ}
    (hF : ∀ l : ℕ, DifferentiableOn ℂ (fun z => f (z + (T l : ℂ) * Complex.I)) U)
    (hconv : TendstoLocallyUniformlyOn
      (fun l z => f (z + (T l : ℂ) * Complex.I)) f Filter.atTop U)
    (j : ℕ) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    Filter.Tendsto (fun l => iteratedDeriv j f (z₀ + (T l : ℂ) * Complex.I))
      Filter.atTop (nhds (iteratedDeriv j f z₀)) := by
  have hbridge := iteratedDeriv_tendsto_of_locallyUniform hU hconv
    (Filter.Eventually.of_forall hF) j hz₀
  refine hbridge.congr (fun l => ?_)
  exact iteratedDeriv_comp_add_const j ((T l : ℂ) * Complex.I) f z₀

end GaloisForLFunctions
