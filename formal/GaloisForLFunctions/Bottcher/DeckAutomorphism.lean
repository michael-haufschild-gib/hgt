/-
# Böttcher tower — the deck automorphism (algebraic core of `σ_n`)

The monodromy `σ_n` of `DyadicMonodromyTower` is, on the fibre coordinate `W = φ_{c₁}`, the deck
transformation `W ↦ ζ·W` of the covering `w ↦ w^{2ⁿ}` (`isQuotientCoveringMap_npow`), with `ζ` a
`2ⁿ`-th root of unity. This file builds that scaling map as an honest **ℂ-algebra automorphism** of
the fibre coordinate ring `ℂ[W]`, with:

* `polyScaleEquiv_X`  : `σ(W) = ζ·W`        — the scaling property `σ_n F = ζ_n F`,
* `polyScaleHom_comp` : `σ_ζ ∘ σ_η = σ_{ζη}` — the `μ`-action homomorphism,
* `polyScaleHom_injective_param` : `ζ ↦ σ_ζ` faithful — giving `orderOf σ_ζ = orderOf ζ`.

This is the *algebraic core* of `σ_n` (real automorphism, correct scaling/order). The remaining
analytic input is the embedding of the actual `φ_c` germs into a cover field `M` extending this
`ℂ[W]`; the deck automorphism then lifts to that `M ≃ₐ[K] M` (field lift via `IsFractionRing`
functoriality is the next brick). NOT a stand-alone discharge of `hDisc`: the scaling/order are
exactly right, the embedding `M ⊇ ℂ(z)(φ_{c₁})` with the actual coordinates is what remains.
-/
import GaloisForLFunctions.Bottcher.MonodromyCovering
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

open Polynomial

namespace Bottcher

/-- The fibre-coordinate substitution `W ↦ ζ·W` as a ℂ-algebra endomorphism of `ℂ[W]`. -/
noncomputable def polyScaleHom (ζ : ℂ) : ℂ[X] →ₐ[ℂ] ℂ[X] := aeval (C ζ * X)

@[simp] lemma polyScaleHom_X (ζ : ℂ) : polyScaleHom ζ X = C ζ * X := by simp [polyScaleHom]

/-- The deck maps compose by multiplication of the roots of unity: `σ_ζ ∘ σ_η = σ_{ζη}`. The
`μ`-action homomorphism underlying the dyadic monodromy. -/
lemma polyScaleHom_comp (ζ η : ℂ) :
    (polyScaleHom ζ).comp (polyScaleHom η) = polyScaleHom (ζ * η) := by
  apply algHom_ext
  rw [AlgHom.comp_apply, polyScaleHom_X, map_mul, polyScaleHom_X,
      show polyScaleHom ζ (C η) = C η from by simp [polyScaleHom],
      polyScaleHom_X, C_mul]
  ring

@[simp] lemma polyScaleHom_one : polyScaleHom (1 : ℂ) = AlgHom.id ℂ ℂ[X] := by
  apply algHom_ext; simp

/-- `W ↦ ζ·W` as a ℂ-algebra **automorphism** of `ℂ[W]` (for `ζ ≠ 0`); inverse is `W ↦ ζ⁻¹·W`. -/
noncomputable def polyScaleEquiv (ζ : ℂ) (hζ : ζ ≠ 0) : ℂ[X] ≃ₐ[ℂ] ℂ[X] :=
  AlgEquiv.ofAlgHom (polyScaleHom ζ) (polyScaleHom ζ⁻¹)
    (by rw [polyScaleHom_comp, mul_inv_cancel₀ hζ, polyScaleHom_one])
    (by rw [polyScaleHom_comp, inv_mul_cancel₀ hζ, polyScaleHom_one])

@[simp] lemma polyScaleEquiv_X (ζ : ℂ) (hζ : ζ ≠ 0) : polyScaleEquiv ζ hζ X = C ζ * X := by
  simp [polyScaleEquiv]

/-- **Faithfulness in the parameter.** `ζ ↦ σ_ζ` is injective: distinct roots of unity give
distinct deck automorphisms. (Hence `orderOf (polyScaleEquiv ζ) = orderOf ζ` once lifted to the
group of automorphisms — the deck group `μ_{2ⁿ}` embeds.) -/
lemma polyScaleHom_injective_param {ζ η : ℂ} (h : polyScaleHom ζ = polyScaleHom η) : ζ = η := by
  have hX : C ζ * X = C η * X := by rw [← polyScaleHom_X, ← polyScaleHom_X, h]
  have : C ζ = C η := mul_right_cancel₀ X_ne_zero hX
  exact C_injective this

/-- **The deck automorphism on the fibre FIELD** `ℂ(W)` — `W ↦ ζ·W` lifted from `ℂ[W]` to its
fraction field via `IsFractionRing` functoriality. A genuine ℂ-algebra automorphism of the field
`RatFunc ℂ`. This is `σ_n` realized as a field automorphism (not merely a ring one). -/
noncomputable def deckRatEquiv (ζ : ℂ) (hζ : ζ ≠ 0) : RatFunc ℂ ≃ₐ[ℂ] RatFunc ℂ :=
  IsLocalization.algEquivOfAlgEquiv (RatFunc ℂ) (RatFunc ℂ) (polyScaleEquiv ζ hζ)
    (MulEquivClass.map_nonZeroDivisors (polyScaleEquiv ζ hζ))

/-- **Scaling on the field generator**: `σ(W) = ζ · W`, with `W = algebraMap ℂ[X] (RatFunc ℂ) X`
the fibre coordinate in the field. Exactly the `σ_n F = ζ_n F` clause of `DyadicMonodromyTower`. -/
theorem deckRatEquiv_smul_gen (ζ : ℂ) (hζ : ζ ≠ 0) :
    deckRatEquiv ζ hζ (algebraMap ℂ[X] (RatFunc ℂ) X)
      = ζ • (algebraMap ℂ[X] (RatFunc ℂ) X) := by
  rw [deckRatEquiv, IsLocalization.algEquivOfAlgEquiv_eq, polyScaleEquiv_X, map_mul,
      Algebra.smul_def, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-!
### Structural note (why the abstract `σ_n` cannot, alone, discharge `hDisc`)

`deckRatEquiv` is a genuine field automorphism with the exact scaling/order shape of `σ_n`. But a
`DyadicMonodromyTower` for the ACTUAL coordinates needs `σ_n` on a field `M ⊇ ℂ(z)` containing BOTH
`φ_{c₁}` (scaled) and `φ_{c₂}` (FIXED), with `φ_{c₂}` transcendental over `K = ℂ(z)`. Any element of
`ℂ(z)(φ_{c₁})` fixed by every `σ_n` lies in `ℂ(z)` (= `K`), so a `σ_n`-fixed transcendental `φ_{c₂}`
forces `φ_{c₂} ∉ ℂ(z)(φ_{c₁})` — i.e. the very independence to be proved. Hence the well-definedness
of `σ_n` (fixing `φ_{c₂}`) cannot be supplied by an abstract algebraic `M`; it must come from
ANALYTIC CONTINUATION on the actual germ/cover field, where "continue around the depth-`n` loop"
is an honest operation whose action on `φ_{c₂}` (trivial monodromy of the other basin's loop) is an
analytic fact, not an assumed one. This pins the remaining work to the analytic continuation layer.
-/

end Bottcher
