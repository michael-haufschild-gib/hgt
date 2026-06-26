/-
# Böttcher tower — the connected-case carrier bridge

The connected/connected case of `q62` (`hRigid`, Eremenko–van Strien rigidity) instantiated on the
**genuine carrier** `M = meroField U` (the meromorphic function field on a connected `U ⊆ escapeOpen`,
where both Böttcher germs `a₁ = φ_{c₁}`, `a₂ = φ_{c₂}` are single-valued analytic). Mirrors
`q62_independence_disconnected_of_lifts`, but with `Disc := fun _ => False`: the `hDisc` branch is
vacuous and `hRigid` fires, so the concrete independence `NoRelation ℂ(z) φ_{c₁} φ_{c₂}` reduces — over
the actual field — to exactly the two named analytic inputs of the connected case:
`Transcendental ℂ(z) φ_{c₂}` and `TranscendentalOverAdjoin φ_{c₁} φ_{c₂}` (the E–vS rigidity
obstruction). This is the connected analogue of the disconnected lane's lift bridge — the precise
point at which the abstract `q62_both_connected` meets the concrete `phiMero`.

New file (hRigid connected lane); consumes `Rigidity` (the abstract reduction) and `MeromorphicField`
(the carrier). Does not touch the unalterable `Q62.lean`.
-/
import GaloisForLFunctions.Bottcher.Rigidity
import GaloisForLFunctions.Bottcher.MeromorphicField

open Polynomial

namespace Bottcher

/-- **q62 connected/connected, on the genuine carrier.** With `Disc := fun _ => False` (both
parameters connected) the `q62_independence` case split sends everything through `hRigid`, discharged
by `q62_both_connected`. So over the meromorphic field `M = meroField U` the genuine independence
`NoRelation ℂ(z) φ_{c₁} φ_{c₂}` reduces to the two named analytic inputs of the connected case:
transcendence of `φ_{c₂}` over `ℂ(z)`, and `φ_{c₁}` transcendental over `ℂ(z)[φ_{c₂}]` (the E–vS
rigidity obstruction). The nonexceptional conditions `c₁,c₂ ∉ {0,-2}` and `c₁ ≠ c₂` ride in the
statement exactly as in `q62_independence`. -/
theorem q62_independence_connected_of_inputs {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    [Algebra (RatFunc ℂ) (meroField U)]
    (a₁ a₂ : analyticSubring U) (c₁ c₂ : ℂ) (hne : c₁ ≠ c₂)
    (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (hrig : haveI := isDomain_analyticSubring U hUo hUc hUne
            TranscendentalOverAdjoin (K := RatFunc ℂ)
              (algebraMap (analyticSubring U) (meroField U) a₁)
              (algebraMap (analyticSubring U) (meroField U) a₂)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  have key := q62_independence (K := RatFunc ℂ)
    (fun c => if c = c₂ then algebraMap (analyticSubring U) (meroField U) a₂
              else algebraMap (analyticSubring U) (meroField U) a₁)
    (fun _ => False) c₁ c₂ hne hx₁ hx₂
    (fun h1 _ => h1.elim)
    (fun _ => by
      simp only [if_neg hne]
      exact q62_both_connected _ _ hGtr hrig)
  simp only [if_neg hne] at key
  exact key

end Bottcher
