/-
# Kummer descent, applied across proof programs: independence lifts to all finite roots

The abstract Kummer descent `U0MStepKummer.noRelation_pow_descent`
(`NoRelation K (F^n) G → NoRelation K F G`) is field-generic — it applies to ANY established
`NoRelation` in the codebase, not just the `u₀`/Böttcher window branch.  Combined with the committed
symmetry `Bottcher.noRelation_symm`, it descends on BOTH coordinates: from a single independence
statement `NoRelation K F G` it produces independence of every finite root of `F` from every finite
root of `G`.

Instantiated at the q62 Böttcher theorem `Bottcher.q62_independence` this yields: for distinct
nonexceptional parameters, not only are the two inverse Böttcher coordinates `φ_{c₁}, φ_{c₂}`
algebraically independent over `ℂ(z)`, but so is every `2^k`-power (indeed every `m`-th / `n`-th)
root of one from every root of the other — the full finite root tower of the q62 pair.  No new q62
input; the Böttcher lane's files are untouched.
-/
import GaloisForLFunctions.U0.U0MStepKummer
import GaloisForLFunctions.Bottcher.Q62
import GaloisForLFunctions.Bottcher.Rigidity

open Bottcher

namespace KummerRootApplications

/-- **Two-coordinate Kummer descent.**  If `F` and `G` are algebraically independent over `K`, then
so is any `m`-th root `χ` of `F` and any `n`-th root `η` of `G`.  Descends on the first coordinate,
flips with `noRelation_symm`, descends on the second, flips back. -/
theorem noRelation_pow_descent_both {K M : Type*} [Field K] [Field M] [Algebra K M]
    {F G χ η : M} {m n : ℕ} (hχ : χ ^ m = F) (hη : η ^ n = G) (h : NoRelation K F G) :
    NoRelation K χ η := by
  have h1 : NoRelation K χ G :=
    U0MStepKummer.noRelation_pow_descent χ G m (by rw [hχ]; exact h)
  have h2 : NoRelation K η χ :=
    U0MStepKummer.noRelation_pow_descent η χ n (by rw [hη]; exact noRelation_symm h1)
  exact noRelation_symm h2

/-- **q62 — independence of every finite root pair.**  Under the q62 hypotheses (distinct
nonexceptional parameters, the disconnected-case monodromy datum, the rigidity obstruction), for any
`m`-th root `χ` of `φ_{c₁}` and any `n`-th root `η` of `φ_{c₂}`, `χ` and `η` are algebraically
independent over `K = ℂ(z)`.  The base independence `NoRelation K (φ c₁) (φ c₂)` is
`Bottcher.q62_independence`; the lift is the two-coordinate Kummer descent.  In particular every
`2^k`-th root of one Böttcher coordinate is independent of every `2^j`-th root of the other. -/
theorem q62_roots_independence {K M : Type*} [Field K] [Field M] [Algebra K M]
    (φ : ℂ → M) (Disc : ℂ → Prop) (c₁ c₂ : ℂ)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hDisc : Disc c₁ → Disc c₂ →
      Transcendental K (φ c₂) ∧ φ c₁ ≠ 0 ∧
      ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (φ c₂) = φ c₂ ∧ σ ζ = ζ ∧ σ (φ c₁) = ζ * φ c₁)
    (hRigid : (¬ Disc c₁ ∨ ¬ Disc c₂) → NoRelation K (φ c₁) (φ c₂))
    {χ η : M} {m n : ℕ} (hχ : χ ^ m = φ c₁) (hη : η ^ n = φ c₂) :
    NoRelation K χ η :=
  noRelation_pow_descent_both hχ hη
    (q62_independence φ Disc c₁ c₂ hne hx₁ hx₂ hDisc hRigid)

/-- **q62 mixed case — root-tower independence.**  In the mixed connected/disconnected subcase
(`F ≠ 0`, `G` transcendental, one-coordinate unbounded monodromy scaling `F` and fixing `G`), not
only is `F ⟂ G` (`Bottcher.q62_mixed`), but every `p`-th root `χ` of `F` is independent of every
`q`-th root `η` of `G` over `K`. -/
theorem q62_mixed_roots_independence {K M : Type*} [Field K] [Field M] [Algebra K M]
    (F G : M) (hF : F ≠ 0) (hG : Transcendental K G)
    (mono : ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧ σ G = G ∧ σ ζ = ζ ∧ σ F = ζ * F)
    {χ η : M} {p q : ℕ} (hχ : χ ^ p = F) (hη : η ^ q = G) :
    NoRelation K χ η :=
  noRelation_pow_descent_both hχ hη (q62_mixed F G hF hG mono)

/-- **q62 both-disconnected case — root-tower independence.**  When BOTH coordinates carry their own
dyadic monodromy (`F ≠ 0`, `G ≠ 0`, one datum scaling `F` and fixing `G`, one scaling `G`), `F ⟂ G`
(`Bottcher.q62_disconnected_both`) lifts to independence of every `p`-th root of `F` from every
`q`-th root of `G` over `K` — the full finite root tower of the disconnected/disconnected pair,
needing no transcendence hypothesis (it follows from the monodromy). -/
theorem q62_disconnected_both_roots_independence {K M : Type*} [Field K] [Field M] [Algebra K M]
    (F G : M) (hF : F ≠ 0) (hG0 : G ≠ 0)
    (monoF : ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧ σ G = G ∧ σ ζ = ζ ∧ σ F = ζ * F)
    (monoG : ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M),
      d < orderOf ζ ∧ σ ζ = ζ ∧ σ G = ζ * G)
    {χ η : M} {p q : ℕ} (hχ : χ ^ p = F) (hη : η ^ q = G) :
    NoRelation K χ η :=
  noRelation_pow_descent_both hχ hη (q62_disconnected_both F G hF hG0 monoF monoG)

end KummerRootApplications
