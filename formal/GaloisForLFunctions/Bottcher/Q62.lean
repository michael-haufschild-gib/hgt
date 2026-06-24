/-
# Böttcher tower — the q62 theorems (Nguyen Question 6.2, quadratic nonexceptional)

Top of the tower. The card `q62-bottcher-independence-n2-all-parameters.md` splits by
Mandelbrot placement of the two parameters; this file states the cases as named Lean
theorems and assembles them.

Algebraic independence of `φ_{c₁}, φ_{c₂}` over the base field `K = ℂ(z)` is rendered
as: no nonzero `P ∈ K[W][Y]` satisfies `P(φ_{c₁}, φ_{c₂}) = 0` (substitute `W ↦ φ_{c₂}`,
`Y ↦ φ_{c₁}`). This is exactly Nguyen's "algebraically independent over `C(z)`".

The DISCONNECTED case is proven outright from the verified machinery (the monodromy
input enters as the deep hypothesis `mono`, discharged by the exact-Prüfer tower).
The connected/mixed cases enter the top assembly through the Eremenko–van Strien
rigidity obstruction, supplied by the (still-being-built) T5 tower.
-/
import GaloisForLFunctions.Bottcher.AlgIndep
import GaloisForLFunctions.Bottcher.DyadicMonodromy

open Polynomial

namespace Bottcher

/-- Algebraic independence of the pair `(F, G)` over `K`, in the form used throughout:
no nonzero bivariate polynomial relation. `F` plays the role of `φ_{c₁}` (the one moved
by monodromy / blocked at the boundary), `G` the role of `φ_{c₂}`. -/
def NoRelation (K : Type*) {M : Type*} [Field K] [Field M] [Algebra K M] (F G : M) : Prop :=
  ∀ P : Polynomial (Polynomial K),
    (P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom).eval F = 0 → P = 0

/-- **q62 — disconnected/disconnected case (Nguyen Q6.2, both parameters outside `M`).**
For distinct disconnected nonexceptional parameters the two Böttcher coordinates are
algebraically independent over `K = ℂ(z)`.

Modelled abstractly: `G = φ_{c₂}` is transcendental over `K`, `F = φ_{c₁} ≠ 0`, and the
exact dyadic monodromy supplies, for every degree bound, a deck automorphism fixing `G`
and scaling `F` by a root of unity of larger order (`mono`). The conclusion is the full
algebraic-independence of `(F, G)`. Proven outright from `algIndep_of_unbounded_monodromy`. -/
theorem q62_disconnected
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    (F G : M) (hG : Transcendental K G) (hF : F ≠ 0)
    (mono : ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧ σ G = G ∧ σ ζ = ζ ∧ σ F = ζ * F) :
    NoRelation K F G :=
  fun P hrel => algIndep_of_unbounded_monodromy F G hG hF mono P hrel

/-- The analytic input to the disconnected case as an explicit structure: a tower of
monodromy automorphisms (deck transformations around depth-`n` Cantor cylinders), each
scaling `F = φ_{c₁}` by a multiplier `ζ n` of order `2^{n+1}` and fixing `G = φ_{c₂}`.
This is exactly what the germ-field / exact-Prüfer-monodromy construction must supply;
`multiplier_orderOf_of_mass` already verifies the multiplier orders from the period formula. -/
structure DyadicMonodromyTower (K : Type*) {M : Type*} [Field K] [Field M] [Algebra K M]
    (F G : M) where
  σ : ℕ → (M ≃ₐ[K] M)
  ζ : ℕ → M
  order : ∀ n, orderOf (ζ n) = 2 ^ (n + 1)
  fixG : ∀ n, σ n G = G
  fixζ : ∀ n, σ n (ζ n) = ζ n
  scaleF : ∀ n, σ n F = ζ n * F

/-- A dyadic monodromy tower yields the unbounded-order `mono` hypothesis. -/
theorem mono_of_tower {K M : Type*} [Field K] [Field M] [Algebra K M] {F G : M}
    (T : DyadicMonodromyTower K F G) :
    ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧ σ G = G ∧ σ ζ = ζ ∧ σ F = ζ * F := by
  intro d
  refine ⟨T.σ d, T.ζ d, 2 ^ (d + 1), ?_, T.order d, T.fixG d, T.fixζ d, T.scaleF d⟩
  calc d < 2 ^ d := Nat.lt_two_pow_self
    _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ d)

/-- **q62 disconnected case from the monodromy tower.** Algebraic independence of the
two Böttcher coordinates follows from transcendence of `G` and a dyadic monodromy tower. -/
theorem q62_disconnected_tower {K M : Type*} [Field K] [Field M] [Algebra K M]
    {F G : M} (hG : Transcendental K G) (hF : F ≠ 0) (T : DyadicMonodromyTower K F G) :
    NoRelation K F G :=
  q62_disconnected F G hG hF (mono_of_tower T)

/-- The exceptional quadratic parameters: monomial `c=0` and Chebyshev `c=-2`. -/
def Exceptional : Set ℂ := {0, -2}

/-- **q62 — all nonexceptional parameters (Nguyen Question 6.2, quadratic `n=2`).**
For `c₁ ≠ c₂` both outside `{0,-2}`, the inverse Böttcher coordinates `φ_{c₁}, φ_{c₂}`
are algebraically independent over `K = ℂ(z)`.

The proof is the card's Mandelbrot case-split (`Disc c ↔ c ∉ M`, "filled Julia set
disconnected"). The **disconnected/disconnected** subcase is discharged outright by
`q62_disconnected` — i.e. by the verified obstruction/monodromy machinery of this
tower, with the exact-Prüfer monodromy entering as `hDisc`. The **connected** and
**mixed** subcases enter through the Eremenko–van Strien smooth-piece rigidity
obstruction `hRigid` (arXiv:0810.2260), the deep analytic input the T5 sub-tower
discharges. -/
theorem q62_independence
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    (φ : ℂ → M) (Disc : ℂ → Prop) (c₁ c₂ : ℂ)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hDisc : Disc c₁ → Disc c₂ →
      Transcendental K (φ c₂) ∧ φ c₁ ≠ 0 ∧
      ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (φ c₂) = φ c₂ ∧ σ ζ = ζ ∧ σ (φ c₁) = ζ * φ c₁)
    (hRigid : (¬ Disc c₁ ∨ ¬ Disc c₂) → NoRelation K (φ c₁) (φ c₂)) :
    NoRelation K (φ c₁) (φ c₂) := by
  by_cases h1 : Disc c₁
  · by_cases h2 : Disc c₂
    · obtain ⟨hG, hF, mono⟩ := hDisc h1 h2
      exact q62_disconnected (φ c₁) (φ c₂) hG hF mono
    · exact hRigid (Or.inr h2)
  · exact hRigid (Or.inl h1)

/-- **q62 disconnected/disconnected from BOTH coordinates' monodromy** (strengthening of
`q62_disconnected`). In the disconnected/disconnected case both `φ_{c₁}` and `φ_{c₂}` carry their
own dyadic monodromy; the `Transcendental K G` hypothesis is then redundant — it follows from
`φ_{c₂}`'s own unbounded monodromy (`transcendental_of_monodromy`). So the algebraic independence
needs only `F ≠ 0`, `G ≠ 0`, and the two monodromy data — exactly what the geometric `deckMap₁`
construction supplies on the common cover (scaling one coordinate, fixing the other). -/
theorem q62_disconnected_both
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    (F G : M) (hF : F ≠ 0) (hG0 : G ≠ 0)
    (monoF : ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧ σ G = G ∧ σ ζ = ζ ∧ σ F = ζ * F)
    (monoG : ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M), d < orderOf ζ ∧ σ ζ = ζ ∧ σ G = ζ * G) :
    NoRelation K F G :=
  fun P hrel =>
    algIndep_of_unbounded_monodromy F G (transcendental_of_monodromy G hG0 monoG) hF monoF P hrel

end Bottcher
