import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.BiScaleUncertainty.PrimePowerZeroPoleNodeCriticality

/-!
# Asymptotic node readings cannot resolve node positivity

The datum is a node set `𝒩 ⊆ ℕ`, the property is zero-pole positivity on `𝒩`, and the collapse is
the deletion of a single node. Node criticality
(`BiScaleUncertainty.not_zeroPoleBlindPositiveOn_diff_of_isPrimePow`) says the deletion of *any*
prime power is fatal on *every* node set, while the deletion of a non-prime-power is invisible to
the property itself (`invisible_zeroPoleBlindPositiveOn_deleteNode`).

A one-node deletion is a finite modification, so every *asymptotic* reading — a density, an
asymptotic counting function, a sieve level, any quantity unchanged by finitely many nodes — is
invisible to it. The collapse–resolution dichotomy then gives the gate in one step:

* `not_riemannHypothesis_of_resolves_of_invisible`: a reading blind to one prime-power deletion
  resolves node positivity only if RH fails;
* `not_resolves_of_asymptoticReading`: hence **no asymptotic reading resolves node positivity**,
  unless RH fails — density arguments are excluded wholesale, not case by case;
* `exists_deleteNode_reading_ne`: a resolving reading must move *every* prime-power deletion;
* `fatal_deleteNode_iff_isPrimePow`: and the fatal collapses are exactly the prime powers, so the
  gate is the incidence condition `log p^k`, never a density threshold.
-/

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

variable {O : Type*}

/-! ### 1. The node collapse -/

/-- The node collapse: delete the node `m`. -/
def deleteNode (m : ℕ) (𝒩 : Set ℕ) : Set ℕ := 𝒩 \ {m}

/-- Deleting one node is a finite modification of the node set. -/
theorem deleteNode_symmDiff_subset (m : ℕ) (𝒩 : Set ℕ) :
    deleteNode m 𝒩 \ 𝒩 ∪ 𝒩 \ deleteNode m 𝒩 ⊆ {m} := by
  intro x hx
  rcases hx with hx | hx
  · exact absurd hx.1.1 hx.2
  · by_contra hxm
    exact hx.2 ⟨hx.1, hxm⟩

/-- **Prime-power deletion is uniformly fatal**: on every node set, deleting one prime power
destroys zero-pole positivity. -/
theorem not_zeroPoleBlindPositiveOn_deleteNode {m : ℕ} (hm : IsPrimePow m) (𝒩 : Set ℕ) :
    ¬ ZeroPoleBlindPositiveOn (deleteNode m 𝒩) :=
  not_zeroPoleBlindPositiveOn_diff_of_isPrimePow 𝒩 hm

/-- **Non-prime-power deletion is invisible to the sharpest reading there is**, the property
itself: `log 6` and all composite nodes are redundant. -/
theorem invisible_zeroPoleBlindPositiveOn_deleteNode {n : ℕ} (hn : ¬ IsPrimePow n) :
    Invisible ZeroPoleBlindPositiveOn (deleteNode n) := fun 𝒩 =>
  propext (zeroPoleBlindPositiveOn_diff_iff_of_not_isPrimePow 𝒩 hn)

/-! ### 2. The node gate -/

/-- **The node gate.** A reading of node sets that is blind to the deletion of a single prime
power resolves zero-pole positivity only when RH fails. -/
theorem not_riemannHypothesis_of_resolves_of_invisible {r : Set ℕ → O} {m : ℕ}
    (hm : IsPrimePow m) (hres : Resolves r ZeroPoleBlindPositiveOn)
    (hinv : Invisible r (deleteNode m)) : ¬ RiemannHypothesis := fun hRH =>
  forall_not_of_resolves_of_invisible hres hinv (not_zeroPoleBlindPositiveOn_deleteNode hm)
    {n | IsPrimePow n} (riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers.mp hRH)

/-- A reading is *asymptotic* when finitely many nodes never change it: densities, asymptotic
counting functions, sieve levels, zero-density exponents. -/
def AsymptoticReading (r : Set ℕ → O) : Prop :=
  ∀ 𝒩 ℳ : Set ℕ, (𝒩 \ ℳ ∪ ℳ \ 𝒩).Finite → r 𝒩 = r ℳ

theorem invisible_deleteNode_of_asymptoticReading {r : Set ℕ → O} (h : AsymptoticReading r)
    (m : ℕ) : Invisible r (deleteNode m) := fun 𝒩 =>
  h _ _ ((Set.finite_singleton m).subset (deleteNode_symmDiff_subset m 𝒩))

/-- **No asymptotic reading resolves node positivity** (unless RH fails). Every density-level
argument about the node set is excluded in one step, because positivity is an incidence
condition on single prime powers. -/
theorem not_resolves_of_asymptoticReading {r : Set ℕ → O} (h : AsymptoticReading r)
    (hRH : RiemannHypothesis) : ¬ Resolves r ZeroPoleBlindPositiveOn := fun hres =>
  not_riemannHypothesis_of_resolves_of_invisible (by decide : IsPrimePow 4) hres
    (invisible_deleteNode_of_asymptoticReading h 4) hRH

/-- Under RH a resolving reading must move every prime-power deletion: the reading has to charge
the node `log p^k` itself. -/
theorem exists_deleteNode_reading_ne (hRH : RiemannHypothesis) {r : Set ℕ → O} {m : ℕ}
    (hm : IsPrimePow m) (hres : Resolves r ZeroPoleBlindPositiveOn) :
    ∃ 𝒩 : Set ℕ, r (deleteNode m 𝒩) ≠ r 𝒩 := by
  by_contra h
  push Not at h
  exact not_riemannHypothesis_of_resolves_of_invisible hm hres (fun 𝒩 => h 𝒩) hRH

/-! ### 3. The fatal collapses are exactly the prime powers -/

/-- **The gate is incidence, not density.** Deletion of `m` is fatal on every node set exactly
when `m` is a prime power. -/
theorem fatal_deleteNode_iff_isPrimePow (hRH : RiemannHypothesis) (m : ℕ) :
    (∀ 𝒩 : Set ℕ, ¬ ZeroPoleBlindPositiveOn (deleteNode m 𝒩)) ↔ IsPrimePow m := by
  refine ⟨fun h => ?_, fun hm => not_zeroPoleBlindPositiveOn_deleteNode hm⟩
  by_contra hm
  refine h {n | IsPrimePow n} ?_
  rw [invisible_zeroPoleBlindPositiveOn_deleteNode hm {n | IsPrimePow n}]
  exact riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers.mp hRH

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
