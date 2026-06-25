/-
# q62 disconnected case via the Kummer route — genuine-carrier reduction

This file lands the abstract Kummer route (`KummerDeck.lean`) on the GENUINE meromorphic carrier
`meroField U` where the inverse Böttcher coordinates `φ_{c₁}, φ_{c₂}` live as honest germs. The
headline `q62_disconnected_kummer` reduces the disconnected/disconnected independence
`NoRelation ℂ(z) (φ_{c₁}, φ_{c₂})` to supplying, per degree `d`, the **per-depth Kummer input tuple**
`(B, i, a, GB, ζ, k)` — and that tuple is *mechanical* over machinery the project already proves:

  • base field `B = meroField(Ext)`, base map `i = restrictMeroHom` (`MeromorphicField.lean:681`,
    made a `RatFunc ℂ`-algebra hom by `restrictMeroHom_ratfuncToMero`);
  • radicand `a = φ_{c₁}∘f^[k]` germ, with the radical relation `φ_{c₁}^{2^k} = i(a)` from
    `bottcherCoord_iterate` (`BottcherCoord.lean:382`);
  • primitive root `ζ` from `exists_dyadic_primitive` (`BasinBranching.lean:472`); `−1 = i²` a square;
  • irreducibility `X^{2^k} − C a` from `kummer_irreducible` (Capelli `p=2`, `KummerDeck.lean`) once
    `a` is not a square in `meroField(Ext)` — the latter from the project's period `∮ d log φ_{c₁}`
    (`circleIntegral_dlog_bottcher`, `not_square_of_period_ftc`).
  • transcendence of `φ_{c₂}` from `transcendental_of_kummer_inputs` (its own dyadic monodromy).

**No geometric global section, no `commonPullback` connectedness, no E–vS, no circularity** — the deck
`σ : w ↦ ζw` fixes `φ_{c₂}` because it is a base element fixed by the *Galois* Kummer action.
-/
import GaloisForLFunctions.Bottcher.KummerDeck
import GaloisForLFunctions.Bottcher.MeromorphicField

open Polynomial

namespace Bottcher

/-- **q62 disconnected/disconnected via the Kummer route — the genuine-carrier reduction.** For the
genuine Böttcher coordinates `F = φ_{c₁}`, `G = φ_{c₂}` realized as germs `algebraMap a₁`, `algebraMap
a₂` in `meroField U` (the faithful carrier), algebraic independence over `ℂ(z) = RatFunc ℂ` follows
from: `F ≠ 0`, `G` transcendental, and the per-depth Kummer input tuple. This is the abstract Kummer
close (`noRelation_of_kummer_inputs`) instantiated at the genuine carrier — verified to type-check
against `meroField`. The remaining work to make it unconditional is the *mechanical* construction of
the `inputs` tuple (see the file header): all of its pieces reduce to lemmas the project already
proves, with no research-level gap and no circular dependence on the independence being proved. -/
theorem q62_disconnected_kummer {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) [Algebra (RatFunc ℂ) (meroField U)]
    (a₁ a₂ : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          (algebraMap (analyticSubring U) (meroField U) a₁) ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (inputs : haveI := isDomain_analyticSubring U hUo hUc hUne
      ∀ d : ℕ, ∃ (B : Type) (_ : Field B) (_ : Algebra (RatFunc ℂ) B)
      (i : B →ₐ[RatFunc ℂ] meroField U) (a GB ζ : B) (k : ℕ),
      d < 2 ^ k ∧ IsPrimitiveRoot ζ (2 ^ k) ∧ Irreducible (X ^ (2 ^ k) - C a) ∧
      (algebraMap (analyticSubring U) (meroField U) a₁) ^ (2 ^ k) = i a ∧
      i GB = (algebraMap (analyticSubring U) (meroField U) a₂)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  exact noRelation_of_kummer_inputs _ _ hF hGtr inputs

end Bottcher
