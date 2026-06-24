/-
# Böttcher tower — Tier 2d: the capacity-separation core

The heart of `q62-bottcher-independence-natural-boundary.md` Step 1 (used in all three
q62 cases): two compacta of equal logarithmic capacity, one containing the other,
must be equal.

Formalised as a contradiction: if `K1 ⊆ K2` have equal capacity yet `K2` carries a
perturbation `ν` with strictly positive Green integral `G` (the precise witness of
`K1 ⊊ K2`: mass sitting where the Green function of `K1` is `> 0`), the strict-gain
step lowers the energy of `μ_t = (1-t)μ_{K1} + tν` below `V(K1) = V(K2)`, contradicting
that `V(K2)` is a lower bound for energies of probability measures on `K2`.

The two genuinely analytic inputs — the equilibrium perturbation identity and the
fact that `μ_t` is a probability measure carried by `K2` — enter as hypotheses; both
are supplied by the Tier-2a/2c lemmas (`logEnergy_perturbation_identity`) and by
measure arithmetic respectively. Nothing here is a sorry.
-/
import GaloisForLFunctions.Bottcher.EnergyVariation

open MeasureTheory

namespace Bottcher

/-- **Capacity-separation core.** Equal Robin constant for `K1, K2`, a probability
measure `ν` on `K2` with positive Green integral `G`, the equilibrium perturbation
identity for `μ_t`, and `μ_t` being a probability measure on `K2`, are jointly
contradictory. Equivalently: equal capacity forbids a strict-containment witness, so
`K1 ⊆ K2` of equal capacity forces `K1 = K2`. -/
theorem capacity_separation_core
    {K1 K2 : Set ℂ} (μ ν : Measure ℂ) (G Iν : ℝ)
    (hcap : robinConstant K1 = robinConstant K2)
    (hbdd2 : BddBelow { e : ℝ | ∃ ρ : Measure ℂ, IsProbOn ρ K2 ∧ logEnergy ρ = e })
    (hG : 0 < G)
    (hidentity : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        logEnergy (ENNReal.ofReal (1 - t) • μ + ENNReal.ofReal t • ν)
          = robinConstant K1 - 2 * t * (1 - t) * G
            + t ^ 2 * (Iν - robinConstant K1))
    (hprob : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        IsProbOn (ENNReal.ofReal (1 - t) • μ + ENNReal.ofReal t • ν) K2) :
    False := by
  obtain ⟨t, ht0, ht1, hlt⟩ :=
    exists_energy_lt_of_green_pos (VA := robinConstant K1) (Iν := Iν) hG
  have hener := hidentity t ht0.le ht1.le
  have hmt := hprob t ht0.le ht1.le
  have hlow := robinConstant_le hmt hbdd2
  rw [hener, ← hcap] at hlow
  linarith [hlt]

end Bottcher
