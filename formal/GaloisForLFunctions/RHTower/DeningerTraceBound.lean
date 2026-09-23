import GaloisForLFunctions.RHTower.DeningerEnergyIdentity
import GaloisForLFunctions.RHTower.DeningerTraceEnergy

/-!
# The trace bound and the Dirichlet principle

Completing the square splits the radial energy into the boundary term and the energy of the
deviation from the decaying exponential.  Since the deviation energy is nonnegative, the boundary
term is bounded by the energy: the trace has norm at most one.  Equality holds exactly when the
deviation vanishes, which is the Poisson profile, so the Poisson extension is the minimal-energy
filling of its boundary value.

* `deningerEnergy_completeSquare` : the energy splits as boundary term plus deviation energy.
* `deningerTrace_bound` : the boundary term is bounded by the energy.
* `deningerDirichlet_principle` : the Poisson profile attains the bound.
-/

namespace RHTower

open MeasureTheory Set Filter Topology

section TraceBound

variable {u v : ℝ → ℂ} {m : ℝ}

/-- **Completing the square.**  The radial energy is the boundary term plus the energy of the
deviation from the decaying exponential. -/
theorem deningerEnergy_completeSquare
    (hderiv : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt u (v r) r)
    (hcont : ContinuousWithinAt (fun r => ‖u r‖ ^ (2 : ℕ)) (Ici (0 : ℝ)) 0)
    (hlim : Tendsto (fun r => ‖u r‖ ^ (2 : ℕ)) atTop (𝓝 0))
    (hcross : IntegrableOn (fun r => 2 * ((starRingEnd ℂ) (u r) * v r).re) (Ioi (0 : ℝ)))
    (hv : IntegrableOn (fun r => ‖v r‖ ^ (2 : ℕ)) (Ioi (0 : ℝ)))
    (hu : IntegrableOn (fun r => ‖u r‖ ^ (2 : ℕ)) (Ioi (0 : ℝ))) :
    (∫ r in Ioi (0 : ℝ), (‖v r‖ ^ (2 : ℕ) + m ^ (2 : ℕ) * ‖u r‖ ^ (2 : ℕ)))
      = m * ‖u 0‖ ^ (2 : ℕ) + ∫ r in Ioi (0 : ℝ), ‖v r + (m : ℂ) * u r‖ ^ (2 : ℕ) := by
  have hexp : ∀ r : ℝ, ‖v r + (m : ℂ) * u r‖ ^ (2 : ℕ)
      = (‖v r‖ ^ (2 : ℕ) + m ^ (2 : ℕ) * ‖u r‖ ^ (2 : ℕ)) + 2 * m * ((starRingEnd ℂ) (u r) * v r).re := by
    intro r
    rw [deningerEnergy_expand]
    ring
  have hmcross : IntegrableOn (fun r => 2 * m * ((starRingEnd ℂ) (u r) * v r).re)
      (Ioi (0 : ℝ)) := by
    have hfun : (fun r => 2 * m * ((starRingEnd ℂ) (u r) * v r).re)
        = fun r => m * (2 * ((starRingEnd ℂ) (u r) * v r).re) := by
      funext r
      ring
    rw [hfun]
    exact hcross.const_mul m
  have hsum : IntegrableOn (fun r => ‖v r‖ ^ (2 : ℕ) + m ^ (2 : ℕ) * ‖u r‖ ^ (2 : ℕ)) (Ioi (0 : ℝ)) :=
    hv.add (hu.const_mul _)
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun r _ => hexp r,
    integral_add hsum hmcross, deningerEnergy_identity hderiv hcont hlim hcross]
  ring

/-- **The trace bound.**  The boundary term is at most the radial energy, because the deviation
energy is nonnegative. -/
theorem deningerTrace_bound
    (hderiv : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt u (v r) r)
    (hcont : ContinuousWithinAt (fun r => ‖u r‖ ^ (2 : ℕ)) (Ici (0 : ℝ)) 0)
    (hlim : Tendsto (fun r => ‖u r‖ ^ (2 : ℕ)) atTop (𝓝 0))
    (hcross : IntegrableOn (fun r => 2 * ((starRingEnd ℂ) (u r) * v r).re) (Ioi (0 : ℝ)))
    (hv : IntegrableOn (fun r => ‖v r‖ ^ (2 : ℕ)) (Ioi (0 : ℝ)))
    (hu : IntegrableOn (fun r => ‖u r‖ ^ (2 : ℕ)) (Ioi (0 : ℝ))) :
    m * ‖u 0‖ ^ (2 : ℕ) ≤ ∫ r in Ioi (0 : ℝ), (‖v r‖ ^ (2 : ℕ) + m ^ (2 : ℕ) * ‖u r‖ ^ (2 : ℕ)) := by
  rw [deningerEnergy_completeSquare hderiv hcont hlim hcross hv hu]
  have hnonneg : 0 ≤ ∫ r in Ioi (0 : ℝ), ‖v r + (m : ℂ) * u r‖ ^ (2 : ℕ) :=
    integral_nonneg fun r => by positivity
  linarith

/-- **The Dirichlet principle.**  The Poisson profile attains the trace bound: its energy is exactly
the boundary term, because its deviation vanishes identically. -/
theorem deningerDirichlet_principle {μ : ℝ} (hμ : μ ≠ 0) :
    (∫ r in Ioi (0 : ℝ), ((-|μ| * deningerModeProfile μ r) ^ (2 : ℕ)
        + μ ^ (2 : ℕ) * deningerModeProfile μ r ^ (2 : ℕ)))
      = |μ| * deningerModeProfile μ 0 ^ (2 : ℕ) := by
  rw [deningerPoisson_energy hμ, deningerPoissonProfile_zero]
  ring

end TraceBound

end RHTower
