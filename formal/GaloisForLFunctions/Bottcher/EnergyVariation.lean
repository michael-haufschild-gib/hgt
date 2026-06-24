/-
# Böttcher tower — Tier 2c: the equilibrium perturbation identity

Specialising the convex-combination energy expansion to `a = 1-t`, `b = t` and
feeding in the equilibrium facts (`I(μ)=V_A`, cross term `J(μ,ν)=V_A-G` via the
Green identity `Uᵘ = V_A - g`, and symmetry `J(μ,ν)=J(ν,μ)`) yields the card's
displayed formula

  `I(μ_t) = V_A - 2t(1-t)·G + t²·(I(ν) - V_A)`,    `μ_t = (1-t)μ + tν`,

from which `G ≥ δ > 0 ⟹ I(μ_t) < V_A` for small `t > 0` (capacity strictly
increases — the strict-gain step). Here `G = ∫ g dν` is the integral of the
Green's function of `K` against the perturbation.

The finite-energy integrability obligations ride as explicit hypotheses (faithful:
the equilibrium and perturbation measures have finite energy).
-/
import GaloisForLFunctions.Bottcher.Capacity

open MeasureTheory

namespace Bottcher

/-- **Equilibrium perturbation identity.** With `μ` an equilibrium measure
(`I(μ)=V_A`), cross term `J(μ,ν)=V_A-G`, symmetric mutual energy, and `I(ν)=Iν`,
the convex combination `μ_t=(1-t)μ+tν` has energy `V_A - 2t(1-t)G + t²(Iν-V_A)`. -/
theorem logEnergy_perturbation_identity (μ ν : Measure ℂ) (t VA G Iν : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hImu : logEnergy μ = VA)
    (hcross : logEnergyPair μ ν = VA - G)
    (hsymm : logEnergyPair ν μ = logEnergyPair μ ν)
    (hIν : logEnergy ν = Iν)
    (hA1 : Integrable (fun z => logPotential
            (ENNReal.ofReal (1 - t) • μ + ENNReal.ofReal t • ν) z) (ENNReal.ofReal (1 - t) • μ))
    (hA2 : Integrable (fun z => logPotential
            (ENNReal.ofReal (1 - t) • μ + ENNReal.ofReal t • ν) z) (ENNReal.ofReal t • ν))
    (hkaμ : ∀ z, Integrable (fun ζ => logKernel z ζ) (ENNReal.ofReal (1 - t) • μ))
    (hkbν : ∀ z, Integrable (fun ζ => logKernel z ζ) (ENNReal.ofReal t • ν))
    (hpμ_aμ : Integrable (fun z => logPotential (ENNReal.ofReal (1 - t) • μ) z) μ)
    (hpμ_bν : Integrable (fun z => logPotential (ENNReal.ofReal t • ν) z) μ)
    (hpν_aμ : Integrable (fun z => logPotential (ENNReal.ofReal (1 - t) • μ) z) ν)
    (hpν_bν : Integrable (fun z => logPotential (ENNReal.ofReal t • ν) z) ν) :
    logEnergy (ENNReal.ofReal (1 - t) • μ + ENNReal.ofReal t • ν)
      = VA - 2 * t * (1 - t) * G + t ^ 2 * (Iν - VA) := by
  rw [logEnergy_convexCombo μ ν (ENNReal.ofReal (1 - t)) (ENNReal.ofReal t)
        hA1 hA2 hkaμ hkbν hpμ_aμ hpμ_bν hpν_aμ hpν_bν,
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal ht0,
      hImu, hsymm, hcross, hIν]
  ring

/-- **Strict-gain step.** Under the perturbation identity, if the Green integral
`G` is positive then for all sufficiently small `t > 0` the perturbed energy drops
below `V_A`. (Pure sign analysis of `f(t) = -2t(1-t)G + t²(Iν-V_A)`: the linear
term `-2tG` dominates near `0`.) This is the inequality `I(μ_t) < V_A` that
contradicts minimality and forces strict capacity increase. -/
theorem exists_energy_lt_of_green_pos {VA G Iν : ℝ} (hG : 0 < G) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ VA - 2 * t * (1 - t) * G + t ^ 2 * (Iν - VA) < VA := by
  -- pick t small: t·[ -2(1-t)G + t(Iν-VA) ] < 0
  -- the bracket → -2G < 0 as t → 0⁺, so any small enough t works.
  set C := |Iν - VA| + 1 with hC
  have hCpos : 0 < C := by positivity
  -- choose t = min (1/2) (G / (G + C)); then 0 < t < 1 and the bracket is negative
  refine ⟨min (1/2) (G / (G + C)), ?_, ?_, ?_⟩
  · have : 0 < G / (G + C) := by positivity
    simp only [lt_min_iff]; exact ⟨by norm_num, this⟩
  · calc min (1/2) (G / (G + C)) ≤ (1:ℝ)/2 := min_le_left _ _
      _ < 1 := by norm_num
  · set t := min (1/2) (G / (G + C)) with ht
    have ht0 : 0 < t := by
      have : 0 < G / (G + C) := by positivity
      rw [ht]; simp only [lt_min_iff]; exact ⟨by norm_num, this⟩
    have htle : t ≤ G / (G + C) := min_le_right _ _
    have ht_half : t ≤ 1/2 := min_le_left _ _
    have h1t : (1:ℝ)/2 ≤ 1 - t := by linarith
    -- It suffices that  -2(1-t)G + t(Iν-VA) < 0.
    have hbracket : -2 * (1 - t) * G + t * (Iν - VA) < 0 := by
      have hIabs : Iν - VA ≤ C := by rw [hC]; nlinarith [abs_le.mp (le_refl |Iν - VA|), le_abs_self (Iν - VA)]
      have hpos_den : 0 < G + C := by positivity
      have htC : t * (G + C) ≤ G := by
        rw [ht] at htle ⊢
        calc min (1/2) (G / (G + C)) * (G + C) ≤ (G / (G + C)) * (G + C) := by
              apply mul_le_mul_of_nonneg_right (min_le_right _ _) (le_of_lt hpos_den)
          _ = G := by field_simp
      -- t·(Iν-VA) ≤ t·C, and -2(1-t)G ≤ -G since (1-t) ≥ 1/2; combine
      have hA : t * (Iν - VA) ≤ t * C := mul_le_mul_of_nonneg_left hIabs (le_of_lt ht0)
      have hB : -2 * (1 - t) * G ≤ -G := by nlinarith [hG]
      nlinarith [htC, hA, hB, ht0, hG]
    nlinarith [hbracket, ht0]

end Bottcher
