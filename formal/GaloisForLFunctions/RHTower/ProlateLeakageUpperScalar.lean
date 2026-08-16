import GaloisForLFunctions.RHTower.ProlateExteriorMassBound
import GaloisForLFunctions.RHTower.ProlateBandFluxEnergy

/-!
# The leakage from above, out of the exact mass balance

The exact mass balance of a fixed prolate mode is

```text
outside = inside · leakage / value² ,
```

with `outside` the exterior mass of the radial continuation, `inside` the aperture mass, and
`value` the concentration value.  The corpus extracts a *lower* bound for the leakage from an upper
bound on `inside` and a lower bound on `outside` (`leakage_lower_of_radial_mass_bounds`).  The
opposite extraction — the one an envelope needs — reads the balance the other way: an upper bound
on `outside` and a lower bound on `inside` cap the leakage, and the concentration value only helps,
since it is at most one.

Both inputs are now available at the sharp order: `integral_Ioi_one_radialProlate_sq_le` bounds the
exterior mass by `C/c` for an endpoint-normalized mode, and `mass_lower_of_fluxBound` bounds the
aperture mass below by the window length times the exponentially damped value at the window's left
end.
-/

noncomputable section

open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.RHTower

/-- **Scalar extraction of a leakage upper bound.**  Reading the mass balance against an upper
bound for the exterior mass and a lower bound for the interior one. -/
theorem leakage_upper_of_mass_bounds {inside outside value leakage U L : ℝ}
    (hL : 0 < L) (hin : L ≤ inside) (hout : outside ≤ U)
    (hvalue : value ^ 2 ≤ 1) (hv : value ≠ 0) (hU : 0 ≤ U)
    (hleak : 0 ≤ leakage)
    (hmass : outside = inside * leakage / value ^ 2) :
    leakage ≤ U / L := by
  have hv2 : 0 < value ^ 2 := by positivity
  have heq : outside * value ^ 2 = inside * leakage := by
    rw [hmass]
    field_simp
  have hstep : L * leakage ≤ inside * leakage := mul_le_mul_of_nonneg_right hin hleak
  have hup : outside * value ^ 2 ≤ U := by
    have h1 : outside * value ^ 2 ≤ U * value ^ 2 :=
      mul_le_mul_of_nonneg_right hout hv2.le
    have h2 : U * value ^ 2 ≤ U * 1 := mul_le_mul_of_nonneg_left hvalue hU
    linarith
  rw [le_div_iff₀ hL]
  calc leakage * L = L * leakage := by ring
    _ ≤ inside * leakage := hstep
    _ = outside * value ^ 2 := heq.symm
    _ ≤ U := hup

/-- **The leakage of a fixed mode, from above.**  With the exterior mass capped by the Dunster
transfer and the interior mass floored by the band flux energy, the mass balance caps the
leakage. -/
theorem leakage_upper_of_prolate_masses {s c : ℝ} {R DR DDR : ℝ → ℝ}
    {inside value leakage L : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hLpos : 0 < L) (hin : L ≤ inside)
    (hvalue : value ^ 2 ≤ 1) (hv : value ≠ 0) (hleak : 0 ≤ leakage)
    (hmass : (∫ x in Ioi (1 : ℝ), R x ^ 2) = inside * leakage / value ^ 2) :
    leakage ≤ radialProlateExteriorMassConstant / c / L := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  have hout := integral_Ioi_one_radialProlate_sq_le hs0 hs1 hc hR1 hR hDR hode
  have hU : (0 : ℝ) ≤ radialProlateExteriorMassConstant / c := by
    have := radialProlateExteriorMassConstant_nonneg
    positivity
  exact leakage_upper_of_mass_bounds hLpos hin hout hvalue hv hU hleak hmass

end GaloisForLFunctions.RHTower
