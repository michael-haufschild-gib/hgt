import GaloisForLFunctions.RHTower.DeningerCircleTopology
import GaloisForLFunctions.HTGeometry.PeriodicUniformComplete

/-!
# Sequential completeness of the smooth periodic space

A sequence Cauchy for every `C^r` sup-seminorm is uniformly Cauchy in every derivative, so its
limit exists, is smooth, and is periodic — that is, it lies in `C^∞(ℝ/Lℤ)` — and the convergence
holds in every seminorm.

* `deningerPeriodic_uniformCauchy` : the seminorm-Cauchy condition is uniform Cauchy per derivative.
* `deningerSmoothPeriodic_exists_limit` : **the limit exists in `C^∞(ℝ/Lℤ)`.**
-/

namespace RHTower

open Filter Topology GaloisForLFunctions
open scoped ContDiff

/-- A seminorm-Cauchy sequence is uniformly Cauchy in every derivative. -/
theorem deningerPeriodic_uniformCauchy {L : ℝ} (hL : 0 < L) (F : ℕ → DeningerSmoothPeriodic L)
    (hcauchy : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      deningerPeriodicSup r (F p - F q) < ε) (r : ℕ) :
    UniformCauchySeqOn
      (fun n => iteratedDeriv r (((F n : DeningerSmoothPeriodic L) : ℝ → ℂ))) atTop Set.univ := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hcauchy r ε hε
  refine ⟨N, fun p hp q hq x _ => ?_⟩
  have hsplit : iteratedFDeriv ℝ r (((F p - F q : DeningerSmoothPeriodic L) : ℝ → ℂ)) x
      = iteratedFDeriv ℝ r (((F p : DeningerSmoothPeriodic L) : ℝ → ℂ)) x
        - iteratedFDeriv ℝ r (((F q : DeningerSmoothPeriodic L) : ℝ → ℂ)) x := by
    have hsub : (((F p - F q : DeningerSmoothPeriodic L) : ℝ → ℂ))
        = (((F p : DeningerSmoothPeriodic L) : ℝ → ℂ))
          - (((F q : DeningerSmoothPeriodic L) : ℝ → ℂ)) := rfl
    rw [hsub]
    exact iteratedFDeriv_sub_apply
      ((deningerSmoothPeriodic_contDiff (F p)).of_le (by exact_mod_cast le_top)).contDiffAt
      ((deningerSmoothPeriodic_contDiff (F q)).of_le (by exact_mod_cast le_top)).contDiffAt
  have hbd := deningerPeriodicSup_le hL r (F p - F q) x
  rw [hsplit] at hbd
  have hlt : ‖iteratedFDeriv ℝ r (((F p : DeningerSmoothPeriodic L) : ℝ → ℂ)) x
      - iteratedFDeriv ℝ r (((F q : DeningerSmoothPeriodic L) : ℝ → ℂ)) x‖ < ε :=
    lt_of_le_of_lt hbd (hN p hp q hq)
  -- read the scalar derivative off the multilinear one
  have hval : iteratedDeriv r (((F p : DeningerSmoothPeriodic L) : ℝ → ℂ)) x
      - iteratedDeriv r (((F q : DeningerSmoothPeriodic L) : ℝ → ℂ)) x
      = (iteratedFDeriv ℝ r (((F p : DeningerSmoothPeriodic L) : ℝ → ℂ)) x
          - iteratedFDeriv ℝ r (((F q : DeningerSmoothPeriodic L) : ℝ → ℂ)) x) (fun _ => 1) := by
    rw [ContinuousMultilinearMap.sub_apply, ← iteratedDeriv_eq_iteratedFDeriv,
      ← iteratedDeriv_eq_iteratedFDeriv]
  rw [dist_eq_norm, hval]
  refine lt_of_le_of_lt ?_ hlt
  have hle := (iteratedFDeriv ℝ r (((F p : DeningerSmoothPeriodic L) : ℝ → ℂ)) x
      - iteratedFDeriv ℝ r (((F q : DeningerSmoothPeriodic L) : ℝ → ℂ)) x).le_opNorm
      (fun _ : Fin r => (1 : ℝ))
  simpa using hle

/-- **The limit of a seminorm-Cauchy sequence exists in `C^∞(ℝ/Lℤ)`.** -/
theorem deningerSmoothPeriodic_exists_limit {L : ℝ} (hL : 0 < L)
    (F : ℕ → DeningerSmoothPeriodic L)
    (hcauchy : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      deningerPeriodicSup r (F p - F q) < ε) :
    ∃ G : DeningerSmoothPeriodic L, ∀ r : ℕ,
      TendstoUniformly (fun n => iteratedDeriv r (((F n : DeningerSmoothPeriodic L) : ℝ → ℂ)))
        (iteratedDeriv r ((G : DeningerSmoothPeriodic L) : ℝ → ℂ)) atTop := by
  obtain ⟨G, hGsmooth, hGper, hGconv⟩ :=
    exists_smooth_limit_of_uniformCauchy
      (F := fun n => (((F n : DeningerSmoothPeriodic L) : ℝ → ℂ)))
      (fun n => deningerSmoothPeriodic_contDiff (F n))
      (deningerPeriodic_uniformCauchy hL F hcauchy)
      (L := L) (fun n => deningerSmoothPeriodic_periodic (F n))
  exact ⟨⟨G, hGsmooth, hGper⟩, hGconv⟩

end RHTower
