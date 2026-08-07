import GaloisForLFunctions.RHTower.HarmonicResidueAbscissaReader
import GaloisForLFunctions.RHTower.RouteRFirstWallScaleQuantification

/-!
# The Route R first trace wall, read at the abscissa

The oriented first-wall residue is `-1`, `0`, `+1` according to grade, and the analytic reader
computes exactly that residue.  So the first-wall criterion, previously a statement about cofinal
averages over deep prime stages, becomes a statement about the boundary behaviour of one explicit
prime Dirichlet series:

`(∑_p W_t(p) p^(-(s-1))) / (-log(s-1)) → -sign t`  as  `s → 1⁺`.

Frequently dropping below the harmonic quantum along `s → 1⁺` therefore forces neutral grade, and at
Xi divisor points that is exactly the Riemann hypothesis.
-/

open Filter Topology Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The analytic three-value law -/

theorem tendsto_primeAbscissa_criticalWall_neg_one_of_pos {t : ℝ} (ht : 0 < t) :
    Tendsto (fun s => primeAbscissaSeries (routeRPrimeGammaCriticalWallField t) s /
        ((abscissaLog s : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds (-1)) :=
  tendsto_primeAbscissaSeries_div_abscissaLog
    (hasReferenceResidue_criticalWall_neg_one_of_pos ht)

theorem tendsto_primeAbscissa_criticalWall_one_of_neg {t : ℝ} (ht : t < 0) :
    Tendsto (fun s => primeAbscissaSeries (routeRPrimeGammaCriticalWallField t) s /
        ((abscissaLog s : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) :=
  tendsto_primeAbscissaSeries_div_abscissaLog
    (hasReferenceResidue_criticalWall_one_of_neg ht)

/-- At neutral grade the first-wall field vanishes identically, so its series is
zero at every height. -/
theorem primeAbscissaSeries_criticalWall_zero (s : ℝ) :
    primeAbscissaSeries (routeRPrimeGammaCriticalWallField 0) s = 0 := by
  rw [primeAbscissaSeries]
  simp [routeRPrimeGammaCriticalWallField]

/-! ## The analytic gap criterion -/

/-- **Sub-quantum gap at the abscissa forces neutral grade.**  Only the real part
matters, and only frequently as `s → 1⁺`. -/
theorem eq_zero_of_frequently_abs_re_primeAbscissa_le {t r : ℝ} (hr : r < 1)
    (hfreq : ∃ᶠ s in nhdsWithin 1 (Ioi 1),
      |(primeAbscissaSeries (routeRPrimeGammaCriticalWallField t) s /
        ((abscissaLog s : ℝ) : ℂ)).re| ≤ r) :
    t = 0 := by
  by_contra ht
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · exact not_frequently_abs_re_le_of_unit_limit hr (by simp)
      (tendsto_primeAbscissa_criticalWall_one_of_neg htneg) hfreq
  · exact not_frequently_abs_re_le_of_unit_limit hr (by simp)
      (tendsto_primeAbscissa_criticalWall_neg_one_of_pos htpos) hfreq

/-! ## The Xi endpoint -/

theorem xiDivisorSupport_re_eq_half_of_frequently_abs_re_primeAbscissa_le
    (rho : XiDivisorSupport) {r : ℝ} (hr : r < 1)
    (hfreq : ∃ᶠ s in nhdsWithin 1 (Ioi 1),
      |(primeAbscissaSeries (routeRPrimeGammaXiCriticalWallField rho) s /
        ((abscissaLog s : ℝ) : ℂ)).re| ≤ r) :
    (rho : ℂ).re = 1 / 2 := by
  rw [← primeDepthBVWoldXiCenteredRate_eq_zero_iff]
  exact eq_zero_of_frequently_abs_re_primeAbscissa_le hr hfreq

/-- **RH as a boundary statement about one explicit prime Dirichlet series.**
The Riemann hypothesis holds if and only if, at every Xi divisor point, the
`log(1/(s-1))`-normalised real part of `∑_p W_{t_rho}(p) p^(-(s-1))` drops below
the harmonic quantum along some sequence approaching the abscissa. -/
theorem riemannHypothesis_iff_frequently_abs_re_primeAbscissa_lt_one :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport, ∃ r < 1, ∃ᶠ s in nhdsWithin 1 (Ioi 1),
        |(primeAbscissaSeries (routeRPrimeGammaXiCriticalWallField rho) s /
          ((abscissaLog s : ℝ) : ℂ)).re| ≤ r := by
  constructor
  · intro hRH rho
    refine ⟨1 / 2, by norm_num, ?_⟩
    have ht : primeDepthBVWoldXiCenteredRate rho = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mpr
        (xi_divisor_support_re_eq_half_of_rh hRH rho)
    have hfield : routeRPrimeGammaXiCriticalWallField rho =
        routeRPrimeGammaCriticalWallField 0 := by
      show routeRPrimeGammaCriticalWallField
        (primeDepthBVWoldXiCenteredRate rho) = _
      rw [ht]
    refine Filter.Eventually.frequently ?_
    filter_upwards with s
    rw [hfield, primeAbscissaSeries_criticalWall_zero]
    norm_num
  · intro h
    refine riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho => ?_
    obtain ⟨r, hr, hfreq⟩ := h rho
    exact xiDivisorSupport_re_eq_half_of_frequently_abs_re_primeAbscissa_le
      rho hr hfreq

end

end RHTower
