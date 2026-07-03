/-
# Independence of `u₀` from every finite Kummer layer of `ψ = bottcherCoord ∘ f^[N]`

The strengthening of the m-step theorem.  `u0_mstep_independence` gives `NoRelation ℂ(z) ψ u₀` for
every viable parameter.  Here we descend it through the finite Böttcher-tower roots: if `χ` is ANY
`2^k`-th root of `ψ` in the meromorphic field (i.e. `χ^(2^k) = ψ`), then `u₀` and `χ` are still
algebraically independent over `ℂ(z)`.

The engine is a purely algebraic **Kummer descent** valid for arbitrary fields `K ⊆ M`:

    `NoRelation K (Fⁿ) G  ⟹  NoRelation K F G`   (any `n`).

Because `Fⁿ ∈ K[F]`, the transcendence degree of `K(F, G)` equals that of `K(Fⁿ, G)`; so a relation
between `F` and `G` would force one between `Fⁿ` and `G`.  Proven directly on the bivariate-eval
definition of `NoRelation`, by the two-case split on whether `P(·, G)` degenerates: either `G` is
already algebraic over `K` (`P.map (aeval G) = 0`), or `F` is algebraic over the subalgebra
`ℂ⟨G⟩ = range(aeval G)`, whence `Fⁿ` is too (`IsAlgebraic.pow`) and the relation lifts back through
the surjection `K[Y][X] ↠ (range aeval G)[X]`.  No transcendence-basis machinery, no MvPolynomial
bridge.

This is the algebraic half of the "full finite Böttcher tower" connection: it turns the SINGLE
branch `ψ` into its whole `2`-power root tower without any new analytic input.  The remaining
geometric half — identifying a specific analytic root `χ` on the window with the actual inverse
Böttcher branch `φ_b` via the functional equation `ψ = φ_b^(2^N)` — is the separate bridge tracked
in the `φ_b`-lift ticket.
-/
import GaloisForLFunctions.U0.U0PhiMStepFar

open Complex Set Bottcher Polynomial
open U0MStepBranch U0PhiMStep U0MeroCarrier U0PhiMStepFar

namespace U0MStepKummer

/-! ## The abstract Kummer descent -/

/-- **Kummer descent for `NoRelation`.**  For arbitrary fields `K ⊆ M` and any `n`, a nonzero
polynomial relation between `F` and `G` over `K` would produce one between `F^n` and `G`.  Hence
`NoRelation K (F^n) G` (algebraic independence of the *power* and `G`) already forces
`NoRelation K F G` (independence of the *root* and `G`).  This is the transcendence-degree fact
`trdeg K(F,G) = trdeg K(F^n,G)` in bivariate-elimination form. -/
theorem noRelation_pow_descent {K M : Type*} [Field K] [Field M] [Algebra K M]
    (F G : M) (n : ℕ) (hFn : NoRelation K (F ^ n) G) : NoRelation K F G := by
  intro P hP
  by_contra hPne
  set φ : Polynomial K →ₐ[K] M := (aeval G : Polynomial K →ₐ[K] M) with hφ
  set S : Subalgebra K M := φ.range with hS
  have hval : (algebraMap S M).comp φ.rangeRestrict.toRingHom = φ.toRingHom :=
    congrArg AlgHom.toRingHom φ.val_comp_rangeRestrict
  by_cases hmap : P.map φ.toRingHom = 0
  · -- Case B: `G` is algebraic over `K` — a nonzero coefficient of `P` is killed.
    have hex : ∃ i, P.coeff i ≠ 0 := by
      by_contra h
      push Not at h
      exact hPne (Polynomial.ext (fun i => by rw [h i, Polynomial.coeff_zero]))
    obtain ⟨i, hi⟩ := hex
    have hcoeff0 : φ (P.coeff i) = 0 := by
      have h := congrArg (fun q => q.coeff i) hmap
      simpa [Polynomial.coeff_map] using h
    have hQrel : ((C (P.coeff i)).map φ.toRingHom).eval (F ^ n) = 0 := by
      rw [Polynomial.map_C, Polynomial.eval_C]; exact hcoeff0
    have hQ0 : (C (P.coeff i) : Polynomial (Polynomial K)) = 0 := hFn _ hQrel
    rw [Polynomial.C_eq_zero] at hQ0
    exact hi hQ0
  · -- Case A: `F` is algebraic over `S = range(aeval G)`, hence so is `F^n`.
    set P' : Polynomial S := P.map φ.rangeRestrict.toRingHom with hP'
    have hmapP' : P'.map (algebraMap S M) = P.map φ.toRingHom := by
      rw [hP', Polynomial.map_map, hval]
    have hP'ne : P' ≠ 0 := by
      intro h; apply hmap; rw [← hmapP', h, Polynomial.map_zero]
    have hFalg : IsAlgebraic S F := by
      refine ⟨P', hP'ne, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hmapP']
      exact hP
    obtain ⟨q, hq0, hqeval⟩ := hFalg.pow n
    obtain ⟨Q, hQ⟩ := Polynomial.map_surjective φ.rangeRestrict.toRingHom
      (φ.rangeRestrict_surjective) q
    have hmapQ : Q.map φ.toRingHom = q.map (algebraMap S M) := by
      rw [← hQ, Polynomial.map_map, hval]
    have hQrel : (Q.map φ.toRingHom).eval (F ^ n) = 0 := by
      rw [hmapQ, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
      exact hqeval
    have hQ0 : Q = 0 := hFn _ hQrel
    rw [hQ0, Polynomial.map_zero] at hQ
    exact hq0 hQ.symm

/-! ## Independence of `u₀` from the Kummer layers of the m-step branch -/

/-- **`u₀ ⟂ (every finite Kummer layer of `ψ`)` — unconditional, over the whole viable region.**
For every viable parameter and every `k`, there is a window disk on which, for ANY `2^k`-th root `χ`
of the m-step branch `ψ = bottcherCoord ∘ f_b^[N]` (an element of the meromorphic field with
`χ^(2^k) = ψ`), `u₀` and `χ` are algebraically independent over `ℂ(z)`.  Obtained by feeding the
m-step independence `NoRelation ℂ(z) ψ u₀` to the Kummer descent with `n = 2^k`.  This lifts the
single-branch independence to the entire finite Böttcher-tower of roots, with no new analytic
input. -/
theorem u0_mstep_kummer_independence {b : ℂ}
    (hviab : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) (k : ℕ) :
    ∃ (r : ℝ) (N : ℕ) (hr : 1 < r)
      (hcl : ∀ z : ℂ, ‖z‖ ≤ r → (quadratic b)^[N] z ∈ escapeOpen b),
      letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
        (annMB_nonempty hr)
      letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
        (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
          (annMB_infinite hr)).toAlgebra
      ∀ χ : meroField (annMB r),
        χ ^ (2 ^ k)
            = algebraMap (analyticSubring (annMB r)) (meroField (annMB r)) (psiNAn hcl) →
          NoRelation (RatFunc ℂ) χ
            (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
              (u0AnSub annMB_subset_Ext)) := by
  obtain ⟨r, N, hr, hcl, hNoRel⟩ := u0_mstep_independence hviab
  refine ⟨r, N, hr, hcl, ?_⟩
  letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
    (annMB_nonempty hr)
  letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
    (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
      (annMB_infinite hr)).toAlgebra
  intro χ hχ
  refine noRelation_pow_descent χ _ (2 ^ k) ?_
  rw [hχ]
  exact hNoRel

end U0MStepKummer
