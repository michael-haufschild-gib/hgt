/-
# Böttcher tower — the continuation operator via Mathlib's covering monodromy

The circularity result (`DeckAutomorphism.lean`) shows `σ_n` cannot come from an abstract field —
it must be analytic continuation. The hardest part of building continuation by hand is the
**monodromy theorem** (homotopy-invariance: continuation along homotopic paths agrees). Mathlib
already provides it for covering maps: `IsCoveringMap.monodromy` is a homotopy-invariant fibre
bijection (`monodromy_bijective`, `monodromy_trans_apply` functoriality, `monodromyFunctor`).

By the conjugacy `φ_c ∘ f_c^[n] = (·)^{2ⁿ} ∘ φ_c`, the dyadic monodromy of `φ_{c₁}` is the
monodromy of the covering `w ↦ w^{2ⁿ}` of `ℂ∖{0}` (`isCoveringMap_npow`). This file instantiates
that covering and its monodromy operator — the topological continuation `σ`, well-defined by
Mathlib's monodromy theorem (no hand-built homotopy invariance needed).

Path to `σ_n` as a field automorphism (next bricks):
  topological monodromy (here)  →  it is a deck element `ζ ∈ μ_{2ⁿ}` of order `2ⁿ` (generator loop
  of `π₁(ℂ∖{0})=ℤ`, order from the winding/period theory)  →  induced field automorphism =
  `deckRatEquiv ζ` (built)  →  pulled back along `φ_{c₁}` to the basin, fixing `φ_{c₂}` (analytic
  fact: the loop is null-homotopic in the other basin).
-/
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import GaloisForLFunctions.Bottcher.DyadicMonodromy

open Complex

namespace Bottcher

/-- **The dyadic covering** `w ↦ w^(2ᵏ)` of `ℂ∖{0}` — `isCoveringMap_npow` at `n = 2ᵏ`. The
covering to which `φ_{c₁}^{2ᵏ}`-branching is conjugate; its deck group is `μ_{2ᵏ}`. -/
theorem isCoveringMap_dyadic (k : ℕ) :
    IsCoveringMap (fun x : {x : ℂ // x ≠ 0} =>
      (⟨x ^ (2 ^ k), pow_ne_zero _ x.2⟩ : {x : ℂ // x ≠ 0})) :=
  isCoveringMap_npow (2 ^ k) (by push_cast; exact pow_ne_zero k two_ne_zero)

/-- **The continuation operator**, realized topologically: the monodromy of the dyadic covering is
a bijection of fibres, depending only on the homotopy class of the loop (Mathlib's covering
monodromy theorem). This is `σ` before passing to the induced field automorphism — continuation of
a `2ᵏ`-th-root branch around a loop, well-defined with NO hand-built monodromy theorem. -/
theorem dyadic_monodromy_bijective (k : ℕ) {x y : {x : ℂ // x ≠ 0}}
    (γ : Path.Homotopic.Quotient x y) :
    ((isCoveringMap_dyadic k).monodromy γ).Bijective :=
  (isCoveringMap_dyadic k).monodromy_bijective γ

/-- Monodromy composes along concatenation of loops (functoriality of the fundamental groupoid
representation) — the homomorphism property `π₁ → Sym(fibre)` whose image is the deck group. -/
theorem dyadic_monodromy_trans (k : ℕ) {x y z : {x : ℂ // x ≠ 0}}
    (γ : Path.Homotopic.Quotient x y) (γ' : Path.Homotopic.Quotient y z) (e) :
    (isCoveringMap_dyadic k).monodromy (γ.trans γ') e
      = (isCoveringMap_dyadic k).monodromy γ' ((isCoveringMap_dyadic k).monodromy γ e) :=
  (isCoveringMap_dyadic k).monodromy_trans_apply γ γ' e

/-- **Generator-loop monodromy multiplier (step 2).** The explicit `2ᵏ`-th-root lift `Γ(t) =
exp(2πi t / 2ᵏ)` of the generator loop `t ↦ exp(2πi t)` of `π₁(ℂ∖{0}) = ℤ` lifts it
(`Γ(t)^{2ᵏ} = exp(2πi t)`) and returns multiplied by a primitive `2ᵏ`-th root of unity
(`Γ(1) = exp(2πi/2ᵏ)·Γ(0)`), of order exactly `2ᵏ`. This is the dyadic monodromy multiplier as the
covering monodromy of the generator — the order-`2ᵏ` scaling that `σ_n` realizes on `φ_{c₁}`,
matching the period-theory value `exp(2πi/2ⁿ)`. -/
theorem dyadic_generator_lift (k : ℕ) :
    ∃ Γ : ℝ → ℂ, Continuous Γ ∧
      (∀ t : ℝ, (Γ t) ^ (2 ^ k) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * t)) ∧
      Γ 1 = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ k : ℕ) : ℂ)) * Γ 0 ∧
      orderOf (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ k : ℕ) : ℂ))) = 2 ^ k := by
  refine ⟨fun t => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * t / ((2 ^ k : ℕ) : ℂ)),
    Complex.continuous_exp.comp (by fun_prop), ?_, ?_, orderOf_dyadicRoot k⟩
  · intro t
    have h2k : ((2 ^ k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero k two_ne_zero
    have harg : ((2 ^ k : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * t / ((2 ^ k : ℕ) : ℂ))
        = 2 * (Real.pi : ℂ) * Complex.I * t := by rw [mul_comm, div_mul_cancel₀ _ h2k]
    rw [← Complex.exp_nat_mul, harg]
  · simp

end Bottcher
