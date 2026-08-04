import GaloisForLFunctions.RHTower.Sieve.ChebyshevTruncatedSplit
import GaloisForLFunctions.RHTower.Sieve.CutoffMass
import GaloisForLFunctions.RHTower.Sieve.PoleBoundaryResidue

/-!
# The main term, explicitly

The middle piece of the split integrand is the only one contributing to the main term, and on the
truncated Perron line its integral is completely explicit:

    ∫_{-T}^{T} W(1)·((d+iy) - 1)⁻¹ dy  =  W(1)·2·arctan(T/(d-1)).

As `T → ∞` this is `π·W(1)`; the left edge contributes the other `π·W(1)`, and the Perron identity's
`2π` cancels both, leaving the mass of the cutoff — which lies between `N` and `N + H`.
-/

namespace RHTower.Sieve

open Complex GaloisForLFunctions.HTGeometry

/-- **The pole term on the truncated Perron line.** -/
theorem integral_pole_term_line {N H : ℝ} {d T : ℝ} (hd : 1 < d) :
    (∫ y : ℝ in (-T)..T, mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
        * (((d : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹)
      = mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
          * ((2 * Real.arctan (T / (d - 1)) : ℝ) : ℂ) := by
  have hd0 : (d - 1 : ℝ) ≠ 0 := by
    intro h
    apply absurd hd
    simp
    linarith
  have hrw : ∀ y : ℝ, ((d : ℂ) + (y : ℝ) * Complex.I) - 1
      = ((d - 1 : ℝ) : ℂ) + (y : ℝ) * Complex.I := by
    intro y; push_cast; ring
  have heq : (∫ y : ℝ in (-T)..T, (((d : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹)
      = ∫ y : ℝ in (-T)..T, (((d - 1 : ℝ) : ℂ) + (y : ℝ) * Complex.I)⁻¹ :=
    intervalIntegral.integral_congr (fun y _ => by rw [hrw y])
  rw [intervalIntegral.integral_const_mul, heq, integral_vertical_pole hd0]

/-- **The main term is the mass of the cutoff, in the limit.**  The truncated pole term tends to
`π·W(1)`. -/
theorem tendsto_integral_pole_term_line {N H : ℝ} {d : ℝ} (hd : 1 < d) :
    Filter.Tendsto (fun T : ℝ =>
        ∫ y : ℝ in (-T)..T, mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
          * (((d : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹)
      Filter.atTop
      (nhds (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1 * ((Real.pi : ℝ) : ℂ))) := by
  have harc : Filter.Tendsto (fun T : ℝ => ((2 * Real.arctan (T / (d - 1)) : ℝ) : ℂ))
      Filter.atTop (nhds ((Real.pi : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto Real.pi).comp (tendsto_two_arctan (by linarith))
  have hmul := harc.const_mul (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1)
  refine hmul.congr fun T => ?_
  exact (integral_pole_term_line hd).symm

end RHTower.Sieve
