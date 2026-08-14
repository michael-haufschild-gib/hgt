import GaloisForLFunctions.RHTower.Sieve.InghamZetaSquareContourShift
import GaloisForLFunctions.RHTower.Sieve.InghamExponentialMellinInversion
import GaloisForLFunctions.RHTower.ZetaCarrier

/-!
# Functional-equation reflection of Ingham's left zeta-square contour

On left line `Re z = -3/4`, argument `s+z` has real part `-1/4`; zeta functional equation
reflects square to absolutely convergent half-plane `Re(1-s-z)=5/4`.  This is exact algebraic
bridge from left contour to divisor Dirichlet series, before analytic estimates/interchange.
-/

noncomputable section

open Complex

namespace RHTower.Sieve

/-- Functional-equation-reflected form of zeta-square Mellin integrand. -/
def inghamReflectedZetaSquareMellinIntegrand (s : ℂ) (x : ℝ) (z : ℂ) : ℂ :=
  (x : ℂ) ^ (-z) * Complex.Gamma z * zetaChi (s + z) ^ 2 *
    LSeries (fun n : ℕ => (n.divisors.card : ℂ)) (1 - s - z)

/-- Exact reflection whenever reflected zeta-square Dirichlet series converges absolutely. -/
theorem inghamZetaSquareMellinIntegrand_eq_reflected
    {s z : ℂ} {x : ℝ} (hw0 : s + z ≠ 0) (hw1 : s + z ≠ 1)
    (hreflect : 1 < (1 - s - z).re) :
    inghamZetaSquareMellinIntegrand s x z =
      inghamReflectedZetaSquareMellinIntegrand s x z := by
  have hpos : 0 < (1 - (s + z)).re := by
    have hre : (1 - (s + z)).re = (1 - s - z).re := by
      congr 1
      ring
    rw [hre]
    linarith
  have hGamma : Gammaℝ (1 - (s + z)) ≠ 0 := Gammaℝ_ne_zero_of_re_pos hpos
  have hFE : riemannZeta (s + z) =
      zetaChi (s + z) * riemannZeta (1 - (s + z)) :=
    zeta_eq_zetaChi_mul hw0 hw1 hGamma
  have harg : (1 : ℂ) - (s + z) = 1 - s - z := by ring
  have hDS := LSeries_card_divisors_eq_riemannZeta_sq hreflect
  unfold inghamZetaSquareMellinIntegrand inghamReflectedZetaSquareMellinIntegrand
  rw [hFE, harg, hDS]
  ring

/-- On fixed left line `Re z=-3/4`, reflection lands exactly on `Re=5/4`. -/
theorem inghamZetaSquareMellinIntegrand_left_threeQuarter_eq_reflected
    (tau x v : ℝ) :
    inghamZetaSquareMellinIntegrand (linePt tau) x
        ((-3 / 4 : ℂ) + (v : ℂ) * I) =
      inghamReflectedZetaSquareMellinIntegrand (linePt tau) x
        ((-3 / 4 : ℂ) + (v : ℂ) * I) := by
  apply inghamZetaSquareMellinIntegrand_eq_reflected
  · intro h
    have hre := congrArg Complex.re h
    rw [Complex.add_re, linePt_re] at hre
    norm_num at hre
  · intro h
    have hre := congrArg Complex.re h
    rw [Complex.add_re, linePt_re, Complex.one_re] at hre
    norm_num at hre
  · rw [Complex.sub_re, Complex.sub_re, Complex.one_re, linePt_re,
      Complex.add_re]
    norm_num

end RHTower.Sieve
