import GaloisForLFunctions.RHTower.ProlateBandAmplitudeAnchor
import GaloisForLFunctions.RHTower.ProlateExteriorMassLower
import GaloisForLFunctions.RHTower.ProlateApertureMassSharp

/-!
# The leakage from below, at the sharp action

The two masses are now both sharp.  From below, the exterior mass of the radial mode is of order
`1/c`; from above, the aperture mass is `(c/sqrt s)` times the square of the turning amplitude, and
the turning amplitude carries the sharp exponent `c Xi_s(y₀)` rather than the crude clock `c(1−s)`.
The mass identity turns the sandwich into

```text
leakage  ≥  (besselEnergyFloor / (864 c))  /  (2 · aperture bound) .
```

Every constant is explicit and none is evaluated: `besselEnergyFloor` is the Wronskian-driven floor
of the Bessel energy and `radialProlateDensityTransferConstant` the density-transfer constant, and
the only condition on `c` is that it be past the point where the second-order term of the exterior
bound is absorbed.
-/

noncomputable section

open Set MeasureTheory

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

open GaloisForLFunctions.HTGeometry

/-- The exterior mass bound with the second-order term absorbed. -/
theorem integral_Ioi_radialProlate_sq_ge_half {c s : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 8 ≤ c)
    (hc0 : 1728 * radialProlateDensityTransferConstant / besselEnergyFloor ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    besselEnergyFloor / 864 / c ≤ ∫ x in Ioi (2 : ℝ), R x ^ (2 : ℕ) := by
  have hcpos : (0 : ℝ) < c := by linarith
  have hF : 0 < besselEnergyFloor := besselEnergyFloor_pos
  have hT : 0 ≤ radialProlateDensityTransferConstant := radialProlateDensityTransferConstant_nonneg
  have hmain := integral_Ioi_radialProlate_sq_ge hs0 hs1 hc hR1 hR hDR hode
  have hstep : besselEnergyFloor / 864 / c
      ≤ besselEnergyFloor / 432 / c - 2 * radialProlateDensityTransferConstant / c ^ (2 : ℕ) := by
    rw [div_le_iff₀ hF] at hc0
    have hsq : (0 : ℝ) < c ^ (2 : ℕ) := by positivity
    rw [div_div, div_div, ← sub_nonneg]
    have hval : besselEnergyFloor / (432 * c) - 2 * radialProlateDensityTransferConstant / c ^ (2 : ℕ)
        - besselEnergyFloor / (864 * c)
        = (besselEnergyFloor * c - 1728 * radialProlateDensityTransferConstant) / (864 * c ^ (2 : ℕ)) := by
      field_simp
      ring
    rw [hval]
    have hnum : 0 ≤ besselEnergyFloor * c - 1728 * radialProlateDensityTransferConstant := by
      nlinarith [hc0, hF]
    positivity
  linarith

/-- **The leakage lower bound at the sharp action.**  The exterior mass from below and the aperture
mass from above, both sharp, sandwich the leakage. -/
theorem prolate_leakage_ge_exp_sharp_action {c s y₀ α : ℝ} {Φ DΦ R DR DDR : ℝ → ℝ}
    {value leakage : ℝ}
    (hc : 8 ≤ c) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hcs : 4 ≤ c * s)
    (hc0 : 1728 * radialProlateDensityTransferConstant / besselEnergyFloor ≤ c)
    (hscale : 1 ≤ c * Real.sqrt s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (heven : Function.Even Φ)
    (hsy0 : s < y₀ ^ (2 : ℕ)) (hy00 : 0 < y₀) (hy0α : y₀ ≤ α) (hα1 : α < 1)
    (houter : ∀ y ∈ Icc α 1, c ^ (2 : ℕ) * (1 - 2 * y ^ (2 : ℕ)) ≤ -(s * c ^ (2 : ℕ)))
    (hposΦ : ∀ y ∈ Icc (Real.sqrt s) 1, 0 < Φ y)
    (hDΦ : ∀ y, HasDerivAt Φ (DΦ y) y)
    (hfluxd : ∀ y ∈ Icc y₀ α, HasDerivAt (fun t => (1 - t ^ (2 : ℕ)) * DΦ t)
      (-(c ^ (2 : ℕ) * (s - y ^ (2 : ℕ)) * Φ y)) y)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hIntR : IntegrableOn (fun x => R x ^ (2 : ℕ)) (Ioi (1 : ℝ)))
    (hvalue : 1 / 2 ≤ value ^ (2 : ℕ)) (hleak : 0 ≤ leakage)
    (hmass : (∫ x in Ioi (1 : ℝ), R x ^ (2 : ℕ))
      = (∫ y in (-1 : ℝ)..1, Φ y ^ (2 : ℕ)) * leakage / value ^ (2 : ℕ)) :
    besselEnergyFloor / 864 / c
        / (2 * (4 * Real.exp 1 * (c / Real.sqrt s)
          * ((1 + (1 - α ^ (2 : ℕ)) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ (2 : ℕ)
                / (c ^ (2 : ℕ) * (α ^ (2 : ℕ) - s)))
            * Real.exp (2 * c * bandEndpointPhase s y₀
                + ((Real.log (α ^ (2 : ℕ) - s) - Real.log (y₀ ^ (2 : ℕ) - s))
                  + (Real.log (1 - y₀ ^ (2 : ℕ)) - Real.log (1 - α ^ (2 : ℕ))))
                + 2 * (c * Real.sqrt (1 - s)
                    * (Real.sqrt (1 - s) - Real.sqrt (1 - y₀ ^ (2 : ℕ))))))))
      ≤ leakage := by
  have hcpos : (0 : ℝ) < c := by linarith
  have hs0' : 0 < s := by nlinarith
  have hsqrt : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 hs0'
  have hα0 : 0 < α := lt_of_lt_of_le hy00 hy0α
  have hsα : s < α ^ (2 : ℕ) := by nlinarith [hy0α, hy00]
  -- the exterior mass, transported from the ray past `2` to the whole ray
  have houtside : besselEnergyFloor / 864 / c ≤ ∫ x in Ioi (1 : ℝ), R x ^ (2 : ℕ) := by
    have h2 := integral_Ioi_radialProlate_sq_ge_half hs0 hs1 hc hc0 hR1 hR hDR hode
    have hsub : (Ioi (2 : ℝ)) ≤ᵐ[volume] (Ioi (1 : ℝ)) :=
      Filter.Eventually.of_forall fun x hx => lt_trans one_lt_two hx
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun x => R x ^ (2 : ℕ) :=
      Filter.Eventually.of_forall fun x => sq_nonneg _
    exact le_trans h2 (setIntegral_mono_set hIntR hnn hsub)
  -- the aperture mass
  have hinside := integral_sq_le_exp_sharp_action hcpos hs0 (by linarith) hcs hscale hsm heig hΦ1
    heven hsy0 hy00 hy0α hα1 houter hposΦ hDΦ hfluxd
  -- positivity of the aperture bound
  have hCpos : (0 : ℝ) < 1 + (1 - α ^ (2 : ℕ)) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ (2 : ℕ)
      / (c ^ (2 : ℕ) * (α ^ (2 : ℕ) - s)) := by
    have h1 : (0 : ℝ) < α ^ (2 : ℕ) - s := by linarith
    have h2 : (0 : ℝ) < 1 - α ^ (2 : ℕ) := by nlinarith
    positivity
  have hUin : (0 : ℝ) < 4 * Real.exp 1 * (c / Real.sqrt s)
      * ((1 + (1 - α ^ (2 : ℕ)) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ (2 : ℕ)
            / (c ^ (2 : ℕ) * (α ^ (2 : ℕ) - s)))
        * Real.exp (2 * c * bandEndpointPhase s y₀
            + ((Real.log (α ^ (2 : ℕ) - s) - Real.log (y₀ ^ (2 : ℕ) - s))
              + (Real.log (1 - y₀ ^ (2 : ℕ)) - Real.log (1 - α ^ (2 : ℕ))))
            + 2 * (c * Real.sqrt (1 - s)
                * (Real.sqrt (1 - s) - Real.sqrt (1 - y₀ ^ (2 : ℕ)))))) := by
    have hexp : (0 : ℝ) < Real.exp (2 * c * bandEndpointPhase s y₀
        + ((Real.log (α ^ (2 : ℕ) - s) - Real.log (y₀ ^ (2 : ℕ) - s))
          + (Real.log (1 - y₀ ^ (2 : ℕ)) - Real.log (1 - α ^ (2 : ℕ))))
        + 2 * (c * Real.sqrt (1 - s)
            * (Real.sqrt (1 - s) - Real.sqrt (1 - y₀ ^ (2 : ℕ))))) := Real.exp_pos _
    have he1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    positivity
  have hLnn : (0 : ℝ) ≤ besselEnergyFloor / 864 / c := by
    have := besselEnergyFloor_pos
    positivity
  exact leakage_lower_of_mass_bounds hLnn houtside hinside hUin hvalue hleak hmass

/-- **The leakage lower bound with no turning-layer prefactor.**  Replacing the corpus's aperture
envelope by the amplitude envelope removes the factor `c / sqrt s`: the only `c`-dependence in the
denominator is the sharp exponential, the scale ratio, and the `O(cs)` allowed-interval cost. -/
theorem prolate_leakage_ge_exp_sharp_amplitude {c s y₀ α : ℝ} {Φ DΦ R DR DDR : ℝ → ℝ}
    {value leakage : ℝ}
    (hc : 8 ≤ c) (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) (hcs : 4 ≤ c * s)
    (hc0 : 1728 * radialProlateDensityTransferConstant / besselEnergyFloor ≤ c)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (heven : Function.Even Φ)
    (hsy0 : s < y₀ ^ (2 : ℕ)) (hy00 : 0 < y₀) (hy04 : y₀ ^ (2 : ℕ) ≤ 4 * s) (hy0h : y₀ ^ (2 : ℕ) ≤ 1 / 2)
    (hratio : (y₀ ^ (2 : ℕ) - s) * (1 - y₀ ^ (2 : ℕ)) ≤ 3 * s)
    (hy0α : y₀ ≤ α) (hα1 : α < 1)
    (houter : ∀ t ∈ Icc α 1, c ^ (2 : ℕ) * (1 - 2 * t ^ (2 : ℕ)) ≤ -(s * c ^ (2 : ℕ)))
    (hposΦ : ∀ t ∈ Icc y₀ 1, 0 < Φ t)
    (hΦd : ∀ t, HasDerivAt Φ (DΦ t) t)
    (hfluxd : ∀ t ∈ Icc (0 : ℝ) α, HasDerivAt (fun u => (1 - u ^ (2 : ℕ)) * DΦ u)
      (-(c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * Φ t)) t)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hIntR : IntegrableOn (fun x => R x ^ (2 : ℕ)) (Ioi (1 : ℝ)))
    (hvalue : 1 / 2 ≤ value ^ (2 : ℕ)) (hleak : 0 ≤ leakage)
    (hmass : (∫ x in Ioi (1 : ℝ), R x ^ (2 : ℕ))
      = (∫ y in (-1 : ℝ)..1, Φ y ^ (2 : ℕ)) * leakage / value ^ (2 : ℕ)) :
    besselEnergyFloor / 864 / c
        / (2 * (2 * (3 * (1 + (1 - α ^ (2 : ℕ)) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ (2 : ℕ)
                  / (c ^ (2 : ℕ) * (α ^ (2 : ℕ) - s))) + 1)
          * Real.exp (2 * c * bandEndpointPhase s y₀ + prolateScaleLog s y₀ α
              + 5 * (c * Real.sqrt s) * y₀)))
      ≤ leakage := by
  have hcpos : (0 : ℝ) < c := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le hy00 hy0α
  have hsα : s < α ^ (2 : ℕ) := by nlinarith [hy0α, hy00]
  have houtside : besselEnergyFloor / 864 / c ≤ ∫ x in Ioi (1 : ℝ), R x ^ (2 : ℕ) := by
    have h2 := integral_Ioi_radialProlate_sq_ge_half hs0.le hs1 hc hc0 hR1 hR hDR hode
    have hsub : (Ioi (2 : ℝ)) ≤ᵐ[volume] (Ioi (1 : ℝ)) :=
      Filter.Eventually.of_forall fun x hx => lt_trans one_lt_two hx
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun x => R x ^ (2 : ℕ) :=
      Filter.Eventually.of_forall fun x => sq_nonneg _
    exact le_trans h2 (setIntegral_mono_set hIntR hnn hsub)
  have hinside := integral_sq_le_exp_sharp_action_amplitude hcpos hs0 (by linarith) hcs hsm heig
    hΦ1 heven hsy0 hy00 hy04 hy0h hratio hy0α hα1 houter hposΦ hΦd hfluxd
  have hCpos : (0 : ℝ) < 1 + (1 - α ^ (2 : ℕ)) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ (2 : ℕ)
      / (c ^ (2 : ℕ) * (α ^ (2 : ℕ) - s)) := by
    have h1 : (0 : ℝ) < α ^ (2 : ℕ) - s := by linarith
    have h2 : (0 : ℝ) < 1 - α ^ (2 : ℕ) := by nlinarith
    positivity
  have hUin : (0 : ℝ) < 2 * (3 * (1 + (1 - α ^ (2 : ℕ))
        * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ (2 : ℕ) / (c ^ (2 : ℕ) * (α ^ (2 : ℕ) - s))) + 1)
      * Real.exp (2 * c * bandEndpointPhase s y₀ + prolateScaleLog s y₀ α
          + 5 * (c * Real.sqrt s) * y₀) := by
    have hexp : (0 : ℝ) < Real.exp (2 * c * bandEndpointPhase s y₀ + prolateScaleLog s y₀ α
        + 5 * (c * Real.sqrt s) * y₀) := Real.exp_pos _
    positivity
  have hLnn : (0 : ℝ) ≤ besselEnergyFloor / 864 / c := by
    have := besselEnergyFloor_pos
    positivity
  exact leakage_lower_of_mass_bounds hLnn houtside hinside hUin hvalue hleak hmass

/-! ## The explicit form at the standard matching point -/

set_option maxHeartbeats 1000000 in
/-- **The leakage lower bound, explicitly.**  Matching at `y₀ = 2 sqrt s` makes every ingredient
elementary: the scale ratio is `(alpha² − s)(1 − 4s)/(3 s (1 − alpha²))`, the allowed-interval cost
is `exp(10 c s)`, and the action is the sharp `1 + (s/4) log s`. -/
theorem prolate_leakage_ge_explicit {c s α : ℝ} {Φ DΦ R DR DDR : ℝ → ℝ}
    {value leakage : ℝ}
    (hc : 8 ≤ c) (hs0 : 0 < s) (hs8 : s ≤ 1 / 8) (hcs : 4 ≤ c * s)
    (hc0 : 1728 * radialProlateDensityTransferConstant / besselEnergyFloor ≤ c)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (heven : Function.Even Φ)
    (h2sα : 2 * Real.sqrt s ≤ α) (hα1 : α < 1)
    (houter : ∀ t ∈ Icc α 1, c ^ (2 : ℕ) * (1 - 2 * t ^ (2 : ℕ)) ≤ -(s * c ^ (2 : ℕ)))
    (hposΦ : ∀ t ∈ Icc (2 * Real.sqrt s) 1, 0 < Φ t)
    (hΦd : ∀ t, HasDerivAt Φ (DΦ t) t)
    (hfluxd : ∀ t ∈ Icc (0 : ℝ) α, HasDerivAt (fun u => (1 - u ^ (2 : ℕ)) * DΦ u)
      (-(c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * Φ t)) t)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hIntR : IntegrableOn (fun x => R x ^ (2 : ℕ)) (Ioi (1 : ℝ)))
    (hvalue : 1 / 2 ≤ value ^ (2 : ℕ)) (hleak : 0 ≤ leakage)
    (hmass : (∫ x in Ioi (1 : ℝ), R x ^ (2 : ℕ))
      = (∫ y in (-1 : ℝ)..1, Φ y ^ (2 : ℕ)) * leakage / value ^ (2 : ℕ)) :
    besselEnergyFloor / 864 / c
        / (2 * (2 * (3 * (1 + (1 - α ^ (2 : ℕ)) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ (2 : ℕ)
                  / (c ^ (2 : ℕ) * (α ^ (2 : ℕ) - s))) + 1)
          * Real.exp (2 * c * (1 + s / 4 * Real.log s)
              + ((Real.log (α ^ (2 : ℕ) - s) - Real.log (3 * s))
                + (Real.log (1 - 4 * s) - Real.log (1 - α ^ (2 : ℕ))))
              + 10 * (c * s))))
      ≤ leakage := by
  have hcpos : (0 : ℝ) < c := by linarith
  have hsqrt : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hsq : (2 * Real.sqrt s) ^ (2 : ℕ) = 4 * s := by
    rw [mul_pow, Real.sq_sqrt hs0.le]
    ring
  have hy00 : (0 : ℝ) < 2 * Real.sqrt s := by linarith
  have hsy0 : s < (2 * Real.sqrt s) ^ (2 : ℕ) := by rw [hsq]; linarith
  have hy04 : (2 * Real.sqrt s) ^ (2 : ℕ) ≤ 4 * s := by rw [hsq]
  have hy0h : (2 * Real.sqrt s) ^ (2 : ℕ) ≤ 1 / 2 := by rw [hsq]; linarith
  have hratio : ((2 * Real.sqrt s) ^ (2 : ℕ) - s) * (1 - (2 * Real.sqrt s) ^ (2 : ℕ)) ≤ 3 * s := by
    rw [hsq]
    nlinarith [hs0]
  have hmain := prolate_leakage_ge_exp_sharp_amplitude (y₀ := 2 * Real.sqrt s) hc hs0
    (by linarith) hcs hc0 hsm heig hΦ1 heven hsy0 hy00 hy04 hy0h hratio h2sα hα1 houter hposΦ
    hΦd hfluxd hR1 hR hDR hode hIntR hvalue hleak hmass
  -- the exponent, explicitly
  have hphase : bandEndpointPhase s (2 * Real.sqrt s) ≤ 1 + s / 4 * Real.log s := by
    have h1 : bandEndpointPhase s (2 * Real.sqrt s) ≤ bandEndpointPhase s (Real.sqrt s) :=
      antitone_bandEndpointPhase s (by linarith)
    rw [bandEndpointPhase_sqrt_eq_prolateAngleAction] at h1
    have h2 := (prolateAngleAction_sub_bounds hs0 (by linarith)).1
    linarith
  have hscalelog : prolateScaleLog s (2 * Real.sqrt s) α
      = (Real.log (α ^ (2 : ℕ) - s) - Real.log (3 * s))
        + (Real.log (1 - 4 * s) - Real.log (1 - α ^ (2 : ℕ))) := by
    rw [prolateScaleLog, hsq]
    have h1 : (4 : ℝ) * s - s = 3 * s := by ring
    rw [h1]
  have hallowed : 5 * (c * Real.sqrt s) * (2 * Real.sqrt s) = 10 * (c * s) := by
    have h := Real.mul_self_sqrt hs0.le
    calc 5 * (c * Real.sqrt s) * (2 * Real.sqrt s)
        = 10 * c * (Real.sqrt s * Real.sqrt s) := by ring
      _ = 10 * (c * s) := by rw [h]; ring
  have hexpo : 2 * c * bandEndpointPhase s (2 * Real.sqrt s)
        + prolateScaleLog s (2 * Real.sqrt s) α + 5 * (c * Real.sqrt s) * (2 * Real.sqrt s)
      ≤ 2 * c * (1 + s / 4 * Real.log s)
        + ((Real.log (α ^ (2 : ℕ) - s) - Real.log (3 * s))
          + (Real.log (1 - 4 * s) - Real.log (1 - α ^ (2 : ℕ))))
        + 10 * (c * s) := by
    rw [hscalelog, hallowed]
    have hstep : 2 * c * bandEndpointPhase s (2 * Real.sqrt s)
        ≤ 2 * c * (1 + s / 4 * Real.log s) :=
      mul_le_mul_of_nonneg_left hphase (by linarith)
    linarith
  refine le_trans ?_ hmain
  set C : ℝ := 1 + (1 - α ^ (2 : ℕ)) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ (2 : ℕ)
      / (c ^ (2 : ℕ) * (α ^ (2 : ℕ) - s)) with hCdef
  have hα0 : (0 : ℝ) < α := lt_of_lt_of_le hy00 h2sα
  have hsα : s < α ^ (2 : ℕ) := by
    have h1 : (2 * Real.sqrt s) ^ (2 : ℕ) ≤ α ^ (2 : ℕ) := by nlinarith [h2sα, hy00]
    rw [hsq] at h1
    linarith
  have hCpos : (0 : ℝ) < C := by
    have h1 : (0 : ℝ) < α ^ (2 : ℕ) - s := by linarith
    have h2 : (0 : ℝ) < 1 - α ^ (2 : ℕ) := by nlinarith
    rw [hCdef]
    positivity
  have hnum : (0 : ℝ) ≤ besselEnergyFloor / 864 / c := by
    have := besselEnergyFloor_pos
    positivity
  have hden1 : (0 : ℝ) < 2 * (2 * (3 * C + 1)
      * Real.exp (2 * c * bandEndpointPhase s (2 * Real.sqrt s)
          + prolateScaleLog s (2 * Real.sqrt s) α
          + 5 * (c * Real.sqrt s) * (2 * Real.sqrt s))) := by
    have hexp : (0 : ℝ) < Real.exp (2 * c * bandEndpointPhase s (2 * Real.sqrt s)
        + prolateScaleLog s (2 * Real.sqrt s) α
        + 5 * (c * Real.sqrt s) * (2 * Real.sqrt s)) := Real.exp_pos _
    positivity
  refine div_le_div_of_nonneg_left hnum hden1 ?_
  have hfac : (0 : ℝ) ≤ 3 * C + 1 := by linarith
  gcongr

end GaloisForLFunctions.RHTower

end
