import GaloisForLFunctions.RHTower.Sieve.ContourShiftIdentity
import GaloisForLFunctions.PNTPlus.ZetaBounds

/-!
# The residue of the Perron integrand at the pole of `ζ`

The integrand `(−ζ'/ζ)(s)·x^s/s` has a simple pole at `s = 1` with residue `x`: the logarithmic
derivative contributes `(s−1)^{-1}`, and the Perron kernel is analytic there with value `x`.
Splitting the difference into the `ζ` residue times a bounded factor plus a difference quotient,
both pieces are `O(1)` near the pole.
-/

namespace RHTower.Sieve

open Complex Filter Asymptotics Topology

noncomputable section

/-- The Perron kernel is analytic at the pole. -/
theorem differentiableAt_perronKernel {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) 1 := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by simpa using hx.ne'
  exact (differentiableAt_id.const_cpow (Or.inl hxne)).div differentiableAt_id one_ne_zero

theorem perronKernel_at_one (x : ℝ) : ((x : ℂ) ^ (1 : ℂ) / (1 : ℂ)) = (x : ℂ) := by
  rw [Complex.cpow_one, div_one]

/-- The difference quotient of the Perron kernel at the pole is bounded. -/
theorem perronKernel_slope_isBigO {x : ℝ} (hx : 0 < x) :
    (fun s : ℂ => ((x : ℂ) ^ s / s - (x : ℂ)) / (s - 1)) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  have htend := hasDerivAt_iff_tendsto_slope.1 (differentiableAt_perronKernel hx).hasDerivAt
  have heq : (fun s : ℂ => slope (fun s : ℂ => (x : ℂ) ^ s / s) 1 s)
      = fun s : ℂ => ((x : ℂ) ^ s / s - (x : ℂ)) / (s - 1) := by
    funext s
    rw [slope_def_field, perronKernel_at_one]
  rw [← heq]
  exact htend.isBigO_one ℂ

/-- The Perron kernel is bounded near the pole. -/
theorem perronKernel_isBigO_one {x : ℝ} (hx : 0 < x) :
    (fun s : ℂ => (x : ℂ) ^ s / s) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  have hcont := (differentiableAt_perronKernel hx).continuousAt
  have htend : Filter.Tendsto (fun s : ℂ => (x : ℂ) ^ s / s) (𝓝[≠] (1 : ℂ))
      (nhds ((x : ℂ) ^ (1 : ℂ) / (1 : ℂ))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact htend.isBigO_one ℂ

/-- **The residue of the Perron integrand at `s = 1` is `x`.** -/
theorem perron_integrand_residue {x : ℝ} (hx : 0 < x) :
    ((fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s))
        - fun s : ℂ => (x : ℂ) / (s - 1)) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  have hzeta := riemannZetaLogDerivResidueBigO
  have hprod : ((fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) - (s - 1)⁻¹)
      * fun s : ℂ => (x : ℂ) ^ s / s) =O[𝓝[≠] (1 : ℂ)] ((1 : ℂ → ℂ) * (1 : ℂ → ℂ)) := by
    refine Asymptotics.IsBigO.mul ?_ (perronKernel_isBigO_one hx)
    refine hzeta.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards with s
    simp [Pi.sub_apply, Pi.div_apply, Pi.neg_apply]
  have hslope := perronKernel_slope_isBigO hx
  have hprod' : ((fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) - (s - 1)⁻¹)
      * fun s : ℂ => (x : ℂ) ^ s / s) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
    refine hprod.trans ?_
    refine Asymptotics.isBigO_of_le _ fun s => ?_
    simp
  have hsum := hprod'.add hslope
  refine hsum.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    simp only [Pi.mul_apply, Pi.sub_apply]
    field_simp
    ring
  · filter_upwards with s
    simp

end

end RHTower.Sieve
