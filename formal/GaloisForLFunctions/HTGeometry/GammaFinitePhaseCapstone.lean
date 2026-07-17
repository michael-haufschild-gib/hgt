import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn
import GaloisForLFunctions.HTGeometry.GammaFiniteProjectiveLaw

/-!
# Finite-phase capstone: the recurrence collapse for a holomorphic almost-periodic function

This ties together the pieces built for the finite-phase theorem (§5).  A holomorphic `f` on a
vertically-invariant open set, whose vertical translates return locally uniformly along `T_l → +∞`
(the almost-periodicity input, `AlmostPeriodicHull`), has its full differential jet return
(`HolomorphicJetReturn`); if in addition the Gamma-field coefficients of a finite differential
relation have the one-point projective boundary (§1 eq. 5), then the relation collapses to a
nontrivial autonomous algebraic differential relation (`GammaFiniteProjectiveLaw`).  This is eq. (8):
`f` is differentially algebraic over the constants.

Only two inputs remain hypotheses, and each is exactly the object whose supplying theory is being
built elsewhere in this development: the *local-uniform translate return* (from the Bohr hull) and
the *coefficient projective boundary* (from the Gamma monomial valuation / prime-torus law).
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- A differential monomial of `f`: `∏ⱼ (f⁽ʲ⁾)^{α_j}`, indexed by a finitely-supported exponent
vector `α`. -/
def diffMonomial (f : ℂ → ℂ) (α : ℕ →₀ ℕ) (s : ℂ) : ℂ :=
  ∏ j ∈ α.support, (iteratedDeriv j f s) ^ (α j)

/-- The differential monomial returns along a jet-return sequence: if every derivative order returns
(`f⁽ʲ⁾(z₀ + iT_l) → f⁽ʲ⁾(z₀)`), then `M_α(z₀ + iT_l) → M_α(z₀)`. -/
theorem diffMonomial_return {f : ℂ → ℂ} {T : ℕ → ℝ} {z₀ : ℂ} (α : ℕ →₀ ℕ)
    (hjet : ∀ j : ℕ, Tendsto (fun l => iteratedDeriv j f (z₀ + (T l : ℂ) * Complex.I))
      atTop (nhds (iteratedDeriv j f z₀))) :
    Tendsto (fun l => diffMonomial f α (z₀ + (T l : ℂ) * Complex.I)) atTop
      (nhds (diffMonomial f α z₀)) := by
  unfold diffMonomial
  exact tendsto_finsetProd _ (fun j _ => (hjet j).pow (α j))

/-- **Finite-phase recurrence collapse for a holomorphic function (§5, eq. 8).**  Let `f` be
holomorphic on a vertically-invariant open `U`, satisfying a finite differential relation
`∑_{α∈E} F_α · M_α = 0` with Gamma-field coefficients `F_α` and differential monomials
`M_α = diffMonomial f α`.  Suppose:
* the vertical translates `f(· + iT_l)` return to `f` locally uniformly on `U` (almost periodicity);
* the coefficients have the one-point projective boundary `F_α/F_β → d_α` (eq. 5), with `F_β`
  nonvanishing along the return times.

Then the constant-coefficient relation `∑_α d_α · M_α(z₀) = 0` holds with a nonzero coefficient
vector (`d_β = 1`): `f` satisfies a nontrivial autonomous algebraic differential relation. -/
theorem holomorphic_recurrence_collapse {ι : Type*} (E : Finset ι)
    {U : Set ℂ} (hU : IsOpen U) (f : ℂ → ℂ) (exps : ι → (ℕ →₀ ℕ))
    (F : ι → ℂ → ℂ) (β : ι) (hβ : β ∈ E) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (T : ℕ → ℝ) (d : ι → ℂ)
    (hFdiff : ∀ᶠ l in atTop,
      DifferentiableOn ℂ (fun z => f (z + (T l : ℂ) * Complex.I)) U)
    (hFconv : TendstoLocallyUniformlyOn
      (fun l z => f (z + (T l : ℂ) * Complex.I)) f atTop U)
    (hrel : ∀ s : ℂ, ∑ α ∈ E, F α s * diffMonomial f (exps α) s = 0)
    (hFβ : ∀ l : ℕ, F β (z₀ + (T l : ℂ) * Complex.I) ≠ 0)
    (hcoeff : ∀ α ∈ E, Tendsto
      (fun l => F α (z₀ + (T l : ℂ) * Complex.I) / F β (z₀ + (T l : ℂ) * Complex.I))
      atTop (nhds (d α))) :
    (∑ α ∈ E, d α * diffMonomial f (exps α) z₀ = 0) ∧ d β = 1 := by
  have hjet : ∀ j : ℕ, Tendsto (fun l => iteratedDeriv j f (z₀ + (T l : ℂ) * Complex.I))
      atTop (nhds (iteratedDeriv j f z₀)) := by
    intro j
    have hbridge := iteratedDeriv_tendsto_of_locallyUniform hU hFconv hFdiff j hz₀
    refine hbridge.congr (fun l => ?_)
    exact congrFun
      (_root_.iteratedDeriv_comp_add_const j f ((T l : ℂ) * Complex.I)) z₀
  exact recurrence_collapse_to_autonomous E F (fun α => diffMonomial f (exps α)) β hβ z₀ T d
    hrel hFβ hcoeff (fun α _ => diffMonomial_return (exps α) hjet)

end

end GaloisForLFunctions
