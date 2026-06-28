/-
# Böttcher tower — the `hRigid` (both-connected) lane

The `hRigid` slot of `Bottcher.q62_independence` (`Q62.lean`):
`(¬ Disc c₁ ∨ ¬ Disc c₂) → NoRelation K (φ c₁) (φ c₂)`. The mixed sub-case (exactly one disconnected)
is already settled by `Bottcher.q62_mixed` from the disconnected coordinate's monodromy alone, with NO
Eremenko–van Strien input. The irreducible content of `hRigid` is therefore the **both-connected** case
`q62_both_connected`, where neither coordinate carries monodromy — the E–vS smooth-piece rigidity
obstruction (arXiv:0810.2260).

This file owns that lane (new file, per `HRIGID_HANDOFF.md`; it only *consumes* the unalterable
`Q62.lean`). The first brick is the **algebraic reduction**: `NoRelation K F G` is exactly
*`G` transcendental over `K`* together with *`F` transcendental over the subalgebra `K[G]`*. The former is
the (already-available) Böttcher-coordinate transcendence; the latter — `F = φ_{c₁}` not algebraic over
`K[φ_{c₂}]` for two distinct connected parameters — is the precise statement the E–vS sub-tower must
discharge. So `q62_both_connected` reduces to a single named analytic input, `TranscendentalOverAdjoin`,
with everything else proven here from Mathlib.
-/
import GaloisForLFunctions.Bottcher.Q62

open Polynomial

namespace Bottcher

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- **`F` is transcendental over the subalgebra `K[G] = Algebra.adjoin K {G}`** (direct form): no nonzero
`M`-polynomial whose coefficients all lie in `K[G]` has `F` as a root. For `F = φ_{c₁}`, `G = φ_{c₂}` and
two distinct connected nonexceptional parameters this is the Eremenko–van Strien rigidity obstruction —
the one deep analytic input of the both-connected case. -/
def TranscendentalOverAdjoin (F G : M) : Prop :=
  ∀ R : Polynomial M, R ≠ 0 →
    (∀ j, R.coeff j ∈ Algebra.adjoin K ({G} : Set M)) → R.eval F ≠ 0

/-- **Algebraic reduction of `NoRelation` (the hRigid algebra core).** If `G` is transcendental over `K`
and `F` is transcendental over the subalgebra `K[G]`, then `(F, G)` satisfy no nonzero bivariate
polynomial relation over `K`. Proof: a relation `P(F,G)=0` makes `F` a root of `R = P.map(aeval G)`, a
polynomial with coefficients in `K[G]`; `R ≠ 0` (else every `aeval G (P.coeff j) = 0`, so by
transcendence of `G` every `P.coeff j = 0`, i.e. `P = 0`), contradicting transcendence of `F` over
`K[G]`. -/
theorem noRelation_of_transcendence (F G : M) (hG : Transcendental K G)
    (hF : TranscendentalOverAdjoin (K := K) F G) :
    NoRelation K F G := by
  intro P hP
  by_contra hP0
  set R : Polynomial M := P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom with hRdef
  have hRcoeff : ∀ j, R.coeff j ∈ Algebra.adjoin K ({G} : Set M) := by
    intro j
    rw [hRdef, Polynomial.coeff_map, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨P.coeff j, rfl⟩
  have hRne : R ≠ 0 := by
    intro hR0
    apply hP0
    refine Polynomial.ext fun j => ?_
    have h0 : (aeval G : Polynomial K →ₐ[K] M) (P.coeff j) = 0 := by
      have hc := congrArg (fun p => Polynomial.coeff p j) hR0
      simpa [hRdef, Polynomial.coeff_map] using hc
    rw [Polynomial.coeff_zero]
    by_contra hc
    exact hG ⟨P.coeff j, hc, h0⟩
  exact hF R hRne hRcoeff hP

/-- **q62 — both-connected case, reduced to the E–vS rigidity input.** For `F = φ_{c₁}`, `G = φ_{c₂}` with
both parameters connected (and `G` transcendental over `K`, available from the Böttcher-coordinate
transcendence), the algebraic independence `NoRelation K F G` follows from the single analytic obstruction
`TranscendentalOverAdjoin F G` — `φ_{c₁}` not algebraic over `K[φ_{c₂}]`, the Eremenko–van Strien
smooth-piece rigidity statement the sub-tower discharges. -/
theorem q62_both_connected (F G : M) (hG : Transcendental K G)
    (hRigidInput : TranscendentalOverAdjoin (K := K) F G) :
    NoRelation K F G :=
  noRelation_of_transcendence F G hG hRigidInput

/-- The variable-swap `K`-algebra automorphism of `K[X][Y]`: outer `Y ↦ C X`, inner `X ↦ Y`. -/
noncomputable def swapVars : Polynomial (Polynomial K) →ₐ[K] Polynomial (Polynomial K) :=
  Polynomial.aevalTower (Polynomial.aeval (Polynomial.X : Polynomial (Polynomial K)))
    (Polynomial.C (Polynomial.X : Polynomial K))

/-- The evaluation `K`-algebra hom `K[X][Y] → M`, `X ↦ G` (inner), `Y ↦ F` (outer); `NoRelation K F G`
is exactly its injectivity, and `evalHom F G P = (P.map (aeval G)).eval F`. -/
noncomputable def evalHom (F G : M) : Polynomial (Polynomial K) →ₐ[K] M :=
  Polynomial.aevalTower (Polynomial.aeval G) F

theorem evalHom_apply (F G : M) (P : Polynomial (Polynomial K)) :
    evalHom F G P = (P.map (Polynomial.aeval G : Polynomial K →ₐ[K] M).toRingHom).eval F := by
  have h : evalHom (K := K) F G P
      = P.eval₂ (Polynomial.aeval G : Polynomial K →ₐ[K] M).toRingHom F := rfl
  rw [h, Polynomial.eval₂_eq_eval_map]

theorem noRelation_iff_evalHom_injective (F G : M) :
    NoRelation K F G ↔ Function.Injective (evalHom (K := K) F G) := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h P hP; exact h P (by rw [← evalHom_apply]; exact hP)
  · intro h P hP; exact h P (by rw [evalHom_apply]; exact hP)

/-- `evalHom F G ∘ swapVars = evalHom G F`: swapping the two variables swaps the two roots. -/
theorem evalHom_comp_swapVars (F G : M) :
    (evalHom (K := K) F G).comp swapVars = evalHom (K := K) G F := by
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    simp [swapVars, evalHom]
  · simp [swapVars, evalHom]

theorem swapVars_comp_swapVars :
    (swapVars (K := K)).comp swapVars = AlgHom.id K (Polynomial (Polynomial K)) := by
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    simp [swapVars]
  · simp [swapVars]

/-- **`NoRelation` is symmetric.** Algebraic independence does not depend on the order of the pair —
the variable-swap automorphism turns a relation for `(G, F)` into one for `(F, G)`. -/
theorem noRelation_symm {F G : M} (h : NoRelation K F G) : NoRelation K G F := by
  rw [noRelation_iff_evalHom_injective] at h ⊢
  have hinv : ∀ p, swapVars (K := K) (swapVars p) = p := fun p => by
    have := congrArg (fun f => f p) (swapVars_comp_swapVars (K := K)); simpa using this
  have hswap_inj : Function.Injective (swapVars (K := K)) := Function.LeftInverse.injective hinv
  intro a b hab
  have key : ∀ p, evalHom (K := K) G F p = evalHom (K := K) F G (swapVars p) := fun p => by
    rw [← AlgHom.comp_apply, evalHom_comp_swapVars]
  rw [key, key] at hab
  exact hswap_inj (h hab)

/-- **The assembled `hRigid` slot of `q62_independence`.** Given, per parameter, the analytic data its
Mandelbrot placement supplies — for a *disconnected* coordinate its dyadic monodromy (scaling it, fixing
the other) plus the other's transcendence; for the *both-connected* case the Böttcher transcendence and
the Eremenko–van Strien rigidity input `TranscendentalOverAdjoin` — the `hRigid` branch
`(¬ Disc c₁ ∨ ¬ Disc c₂) → NoRelation K (φ c₁) (φ c₂)` is assembled by case split: a mixed case uses
`q62_mixed` (with `noRelation_symm` when the disconnected coordinate is `c₂`), the both-connected case
uses `q62_both_connected`. This is the exact term `q62_independence` consumes; only the named analytic
inputs remain (the disc-lane monodromy and the E–vS rigidity input). -/
theorem hRigid_assemble (φ : ℂ → M) (Disc : ℂ → Prop) (c₁ c₂ : ℂ)
    (hData1 : Disc c₁ → φ c₁ ≠ 0 ∧ Transcendental K (φ c₂) ∧
      ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (φ c₂) = φ c₂ ∧ σ ζ = ζ ∧ σ (φ c₁) = ζ * φ c₁)
    (hData2 : Disc c₂ → φ c₂ ≠ 0 ∧ Transcendental K (φ c₁) ∧
      ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (φ c₁) = φ c₁ ∧ σ ζ = ζ ∧ σ (φ c₂) = ζ * φ c₂)
    (hBoth : ¬ Disc c₁ → ¬ Disc c₂ →
      Transcendental K (φ c₂) ∧ TranscendentalOverAdjoin (K := K) (φ c₁) (φ c₂)) :
    (¬ Disc c₁ ∨ ¬ Disc c₂) → NoRelation K (φ c₁) (φ c₂) := by
  intro hdisj
  by_cases h1 : Disc c₁
  · have h2 : ¬ Disc c₂ := hdisj.resolve_left (not_not.mpr h1)
    obtain ⟨hF, hG, mono⟩ := hData1 h1
    exact q62_mixed (φ c₁) (φ c₂) hF hG mono
  · by_cases h2 : Disc c₂
    · obtain ⟨hF, hG, mono⟩ := hData2 h2
      exact noRelation_symm (q62_mixed (φ c₂) (φ c₁) hF hG mono)
    · obtain ⟨hG, hrig⟩ := hBoth h1 h2
      exact q62_both_connected (φ c₁) (φ c₂) hG hrig

/-- **Top q62 assembly from the separated hDisc and hRigid data.**  This is the final abstract join:
`hDisc` handles the both-disconnected branch of `q62_independence`; `hRigid_assemble` handles every
branch with at least one connected parameter, using monodromy for the mixed cases and
`TranscendentalOverAdjoin` only for the both-connected case.  Thus the remaining analytic work can be
produced independently as the explicit data terms below, with no hidden q62 case-split obligation. -/
theorem q62_independence_of_hDisc_hRigidData (φ : ℂ → M) (Disc : ℂ → Prop) (c₁ c₂ : ℂ)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hDisc : Disc c₁ → Disc c₂ →
      Transcendental K (φ c₂) ∧ φ c₁ ≠ 0 ∧
      ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (φ c₂) = φ c₂ ∧ σ ζ = ζ ∧ σ (φ c₁) = ζ * φ c₁)
    (hData1 : Disc c₁ → φ c₁ ≠ 0 ∧ Transcendental K (φ c₂) ∧
      ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (φ c₂) = φ c₂ ∧ σ ζ = ζ ∧ σ (φ c₁) = ζ * φ c₁)
    (hData2 : Disc c₂ → φ c₂ ≠ 0 ∧ Transcendental K (φ c₁) ∧
      ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (φ c₁) = φ c₁ ∧ σ ζ = ζ ∧ σ (φ c₂) = ζ * φ c₂)
    (hBoth : ¬ Disc c₁ → ¬ Disc c₂ →
      Transcendental K (φ c₂) ∧ TranscendentalOverAdjoin (K := K) (φ c₁) (φ c₂)) :
    NoRelation K (φ c₁) (φ c₂) :=
  q62_independence φ Disc c₁ c₂ hne hx₁ hx₂ hDisc
    (hRigid_assemble φ Disc c₁ c₂ hData1 hData2 hBoth)

end Bottcher
