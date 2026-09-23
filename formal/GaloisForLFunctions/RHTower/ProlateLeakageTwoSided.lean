import GaloisForLFunctions.RHTower.ProlateLeakageLowerSharp
import GaloisForLFunctions.RHTower.ProlateInteriorMassLower
import GaloisForLFunctions.RHTower.ProlateLeakageBarrierAssembly

/-!
# The leakage, two-sided, at the sharp action

Both bounds now carry the same exponential `exp(−2 c Xi_s(y₀))` at the standard matching point
`y₀ = 2 sqrt s`, so the Fuchs rate is pinned between two explicit polynomial prefactors:

```text
besselEnergyFloor/(864 c) / (2 · aperture-upper)   ≤  leakage  ≤   exterior-upper · barrier-lower⁻²
```

The upper bound consumes the interior mass *from below* on a band window — the flux bound
`(1 − t²)|Phi'/Phi| ≤ c b + 12` fed into the corpus's flux-driven mass estimate — and the barrier
ratio from below.  The lower bound consumes the exterior mass from below at the sharp order `1/c`
and the aperture mass from above through the amplitude envelope.  Nothing in either direction uses
a turning-point model function.
-/

noncomputable section

open Set MeasureTheory

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

open GaloisForLFunctions.HTGeometry

/-- **The leakage, two-sided.**  At `y₀ = 2 sqrt s` both directions are explicit and share the sharp
exponential. -/
theorem prolate_leakage_two_sided {c s α b : ℝ} {Φ DΦ R DR DDR : ℝ → ℝ} {value leakage : ℝ}
    (hc : 8 ≤ c) (hs0 : 0 < s) (hs8 : s ≤ 1 / 8) (hcs : 4 ≤ c * s)
    (hc0 : 1728 * radialProlateDensityTransferConstant / besselEnergyFloor ≤ c)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (heven : Function.Even Φ)
    (h2sα : 2 * Real.sqrt s ≤ α)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hcollar : 600 * (1 - α) ≤ 1 / 4)
    (hz : 1 ≤ c * bandEndpointPhase s α)
    (houter : ∀ t ∈ Icc α 1, c ^ (2 : ℕ) * (1 - 2 * t ^ (2 : ℕ)) ≤ -(s * c ^ (2 : ℕ)))
    (hposΦ : ∀ t ∈ Icc (2 * Real.sqrt s) 1, 0 < Φ t)
    (hΦd : ∀ t, HasDerivAt Φ (DΦ t) t)
    (hfluxd : ∀ t ∈ Icc (0 : ℝ) α, HasDerivAt (fun u => (1 - u ^ (2 : ℕ)) * DΦ u)
      (-(c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * Φ t)) t)
    (hb : 2 * Real.sqrt s < b) (hb1 : b < 1)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hIntR : IntegrableOn (fun x => R x ^ (2 : ℕ)) (Ioi (1 : ℝ)))
    (hvalue : 1 / 2 ≤ value ^ (2 : ℕ)) (hv2 : value ^ (2 : ℕ) ≤ 1) (hv : value ≠ 0) (hleak : 0 ≤ leakage)
    (hmass : (∫ x in Ioi (1 : ℝ), R x ^ (2 : ℕ))
      = (∫ y in (-1 : ℝ)..1, Φ y ^ (2 : ℕ)) * leakage / value ^ (2 : ℕ)) :
    besselEnergyFloor / 864 / c
          / (2 * (2 * (3 * (1 + (1 - α ^ (2 : ℕ)) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ (2 : ℕ)
                    / (c ^ (2 : ℕ) * (α ^ (2 : ℕ) - s))) + 1)
            * Real.exp (2 * c * (1 + s / 4 * Real.log s)
                + ((Real.log (α ^ (2 : ℕ) - s) - Real.log (3 * s))
                  + (Real.log (1 - 4 * s) - Real.log (1 - α ^ (2 : ℕ))))
                + 10 * (c * s))))
        ≤ leakage ∧
      leakage ≤ radialProlateExteriorMassConstant / c
        * ((6 * Real.pi * Real.sqrt (c * bandEndpointPhase s α)) ^ (2 : ℕ)
            * Real.exp (2 * ((c * b + 12) * (b - 2 * Real.sqrt s) / (1 - b ^ (2 : ℕ))))
            / (b - 2 * Real.sqrt s))
        * Real.exp (-(2 * (c * bandEndpointPhase s (2 * Real.sqrt s)
            + 6 * (Real.log (1 - α) - Real.log (1 - 2 * Real.sqrt s))))) := by
  have hcpos : (0 : ℝ) < c := by linarith
  have hsqrt : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hy00 : (0 : ℝ) < 2 * Real.sqrt s := by linarith
  have hsq : (2 * Real.sqrt s) ^ (2 : ℕ) = 4 * s := by
    rw [mul_pow, Real.sq_sqrt hs0.le]
    ring
  have hsy0 : s < (2 * Real.sqrt s) ^ (2 : ℕ) := by rw [hsq]; linarith
  refine ⟨prolate_leakage_ge_explicit hc hs0 hs8 hcs hc0 hsm heig hΦ1 heven h2sα hα1 houter
    hposΦ hΦd hfluxd hR1 hR hDR hode hIntR hvalue hleak hmass, ?_⟩
  -- the interior mass from below on the window `[2 sqrt s, b]`
  have hin := prolate_aperture_mass_lower (c := c) (s := s) (y₀ := 2 * Real.sqrt s) (b := b)
    hcpos hs0.le (by linarith) hcs hsm heig hΦ1 hy00 hsy0 hb.le hb1 hposΦ
  have hw : (0 : ℝ) < b - 2 * Real.sqrt s := by linarith
  exact prolate_leakage_le_exp_action (c := c) (s := s) (α := α) (y₀ := 2 * Real.sqrt s)
    (w := b - 2 * Real.sqrt s)
    (E := (c * b + 12) * (b - 2 * Real.sqrt s) / (1 - b ^ (2 : ℕ)))
    (inside := ∫ y in (-1 : ℝ)..1, Φ y ^ (2 : ℕ)) (value := value) (leakage := leakage)
    hs0.le hs8 (by linarith) hα hα1 hcollar hsm heig hΦ1 hy00.le h2sα hsy0 hposΦ hz
    hR1 hR hDR hode hw hin hv2 hv hleak hmass

end GaloisForLFunctions.RHTower

end
