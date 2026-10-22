import GaloisForLFunctions.HTGeometry.EntireQuotientNormalForm

/-!
# Local analytic quotients with matching zero orders

`localQuotientOn f g U` is the meromorphic normal form on `U` of the quotient `f / g`. When `f`
and `g` are analytic on a neighbourhood of every point of `U`, `f` is not locally identically zero
at any point of `U`, and `f` and `g` vanish to the same order at every point of `U`, the quotient is
analytic and nowhere zero on `U`, and `f = (f / g) · g` holds pointwise on `U`.

## Main results

- `localQuotientOn_analytic_nonvanishing_factorization`: under equal orders, `localQuotientOn f g U`
  is analytic on `U`, nonvanishing on `U`, and satisfies `f z = localQuotientOn f g U z * g z` for
  `z ∈ U`.

## Hypotheses

The theorem assumes `f` and `g` analytic on a neighbourhood of `U`, finite analytic order of `f`
at every point of `U`, and `analyticOrderAt f z = analyticOrderAt g z` for every `z ∈ U`. It is
otherwise unconditional.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The meromorphic normal form on `U` of `f / g` (`toMeromorphicNFOn`), which fills in removable
singularities of the pointwise quotient. -/
def localQuotientOn (f g : ℂ → ℂ) (U : Set ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (f / g) U

/-- If `f`, `g` are analytic on `U`, `f` has finite order at each point of `U`, and the orders of
`f` and `g` agree on `U`, then `q = localQuotientOn f g U` is analytic and nonvanishing on `U` and
`f = q · g` on `U`. -/
theorem localQuotientOn_analytic_nonvanishing_factorization
    {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hfinite : ∀ z ∈ U, analyticOrderAt f z ≠ ⊤)
    (horder : ∀ z ∈ U, analyticOrderAt f z = analyticOrderAt g z) :
    AnalyticOnNhd ℂ (localQuotientOn f g U) U ∧
      (∀ z ∈ U, localQuotientOn f g U z ≠ 0) ∧
      ∀ z ∈ U, f z = localQuotientOn f g U z * g z := by
  have hmer : MeromorphicOn (f / g) U := hf.meromorphicOn.div hg.meromorphicOn
  have hrawOrder : ∀ z ∈ U, meromorphicOrderAt (f / g) z = 0 := by
    intro z hz
    rw [meromorphicOrderAt_div (hf z hz).meromorphicAt (hg z hz).meromorphicAt,
      (hf z hz).meromorphicOrderAt_eq, (hg z hz).meromorphicOrderAt_eq,
      ← horder z hz]
    simp [hfinite z hz]
  have hanalytic : AnalyticOnNhd ℂ (localQuotientOn f g U) U := by
    intro z hz
    have hNF := meromorphicNFOn_toMeromorphicNFOn (f / g) U hz
    apply hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hmer hz,
      hrawOrder z hz]
  refine ⟨hanalytic, ?_, ?_⟩
  · intro z hz
    have hNF := meromorphicNFOn_toMeromorphicNFOn (f / g) U hz
    apply hNF.meromorphicOrderAt_eq_zero_iff.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hmer hz,
      hrawOrder z hz]
  · intro z hz
    by_cases hgz : g z = 0
    · have hfz : f z = 0 := by
        by_contra hfz
        have hfo : analyticOrderAt f z = 0 :=
          (hf z hz).analyticOrderAt_eq_zero.mpr hfz
        have hgo : analyticOrderAt g z ≠ 0 := by
          intro h
          exact ((hg z hz).analyticOrderAt_eq_zero.mp h) hgz
        exact hgo ((horder z hz).symm.trans hfo)
      rw [hfz, hgz, mul_zero]
    · have hraw : AnalyticAt ℂ (f / g) z := (hf z hz).div (hg z hz) hgz
      have heq := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hmer hz
      have hself : toMeromorphicNFAt (f / g) z = f / g :=
        toMeromorphicNFAt_eq_self.mpr hraw.meromorphicNFAt
      rw [hself] at heq
      have hvalue := heq.eq_of_nhds
      rw [localQuotientOn, hvalue]
      exact (div_mul_cancel₀ _ hgz).symm

end GaloisForLFunctions.HTGeometry
