import GaloisForLFunctions.RHTower.CompletedChebyshevJet
import GaloisForLFunctions.RHTower.XiHypertranscendenceChain
import GaloisForLFunctions.RHTower.FarFieldAnchor

/-!
# The completed radial source polynomial

On the Euler ray `s > 1` the completed logarithmic derivative splits as

`xi'/xi = 1/s + 1/(s-1) - (log pi)/2 + (1/2) psi (s/2) + zeta'/zeta`,

so its alternating reverse-Bessel radial jet splits into the archimedean correction

`C_n s = radialJet n s (1/s - (log pi)/2 + (1/2) psi (s/2))`

and the radial jet of the pole-corrected logarithmic derivative, which is the common-kernel
discrepancy.  The completed source polynomial is therefore

`Q_n = C_n s + (∫_1^∞ f_{n,s} dx - ∫_[1,∞) f_{n,s} d psi)`,

one archimedean term plus one smoothed prime-counting discrepancy.  The split of the jet is
legitimate because both summands are real-smooth at `s`: `xi'/xi` is the real trace of a function
holomorphic on `Re z > 1`, where `xi` is analytic and does not vanish, and the archimedean
correction is then the difference of two smooth functions.
-/

open MeasureTheory Set Filter ArithmeticFunction

namespace RHTower

noncomputable section

/-- The real trace of the completed logarithmic derivative on the Euler ray. -/
def xiRayLogDeriv (s : ℝ) : ℝ := (xiLogDeriv (s : ℂ)).re

/-- The archimedean correction of equation `(5)`: the trivial-zero/archimedean part of `xi'/xi`. -/
def archimedeanRayLogDeriv (s : ℝ) : ℝ :=
  ((1 : ℂ) / (s : ℂ) - (Real.log Real.pi : ℂ) / 2
    + (1 / 2) * Complex.digamma ((s : ℂ) / 2)).re

/-- **Equation (5).**  On the Euler ray the completed logarithmic derivative is the archimedean
correction plus the pole-corrected logarithmic derivative of `zeta`. -/
theorem xiRayLogDeriv_split {s : ℝ} (hs : 1 < s) :
    xiRayLogDeriv s
      = archimedeanRayLogDeriv s
        + (1 / (s - 1) + deriv realZetaSeries s / realZetaSeries s) := by
  have hre : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  have h2 : ((1 : ℂ) / ((s : ℂ) - 1)).re = 1 / (s - 1) := by
    rw [show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring,
      show ((1 : ℂ) / ((s - 1 : ℝ) : ℂ)) = (((1 / (s - 1) : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  have h3 : (zetaLogDeriv (s : ℂ)).re = deriv realZetaSeries s / realZetaSeries s := by
    rw [zetaLogDeriv]
    exact (realZetaLogDeriv_eq hs).symm
  rw [xiRayLogDeriv, xiLogDeriv_split hre, archimedeanRayLogDeriv]
  simp only [Complex.add_re, Complex.sub_re]
  rw [h2, h3]
  ring

theorem contDiffAt_xiRayLogDeriv {s : ℝ} (hs : 1 < s) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n xiRayLogDeriv s := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ xiLogDeriv {z : ℂ | 1 < z.re} := by
    intro z hz
    have hxi : xi z ≠ 0 := xi_ne_zero_of_one_lt_re hz
    have hd : DifferentiableAt ℂ (deriv xi) z :=
      (xi_analyticOnNhd_univ z (Set.mem_univ z)).deriv.differentiableAt
    exact ((hd.div (xi_differentiable z) hxi)).differentiableWithinAt
  exact GaloisForLFunctions.HTGeometry.contDiffAt_re_comp_ofReal hopen hdiff
    (by simpa using hs) n

theorem contDiffAt_archimedeanRayLogDeriv {s : ℝ} (hs : 1 < s) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n archimedeanRayLogDeriv s := by
  have hsub : ContDiffAt ℝ n
      (fun b : ℝ => xiRayLogDeriv b
        - (1 / (b - 1) + deriv realZetaSeries b / realZetaSeries b)) s :=
    (contDiffAt_xiRayLogDeriv hs n).sub
      ((contDiffAt_poleTerm hs n).add (contDiffAt_realZetaLogDeriv hs n))
  refine hsub.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with y hy
  rw [xiRayLogDeriv_split hy]
  ring

/-- **Equation (6).**  The completed squared-Xi source polynomial is the archimedean correction
plus one smoothed prime-counting discrepancy: the alternating radial jet of `xi'/xi` equals the
archimedean jet `C_n s` plus the common-kernel discrepancy of the radial reverse-Bessel kernel. -/
theorem radialJet_xiRayLogDeriv {n : ℕ} {s : ℝ} (hs : 1 < s) :
    radialJet n s xiRayLogDeriv
      = radialJet n s archimedeanRayLogDeriv
        + ((∫ x in Ioi (1:ℝ), radialBesselKernel n s x)
            - ∫ x, radialBesselKernel n s x ∂chebyshevPsiStieltjes.measure) := by
  have hEq : xiRayLogDeriv =ᶠ[nhds s] fun b : ℝ =>
      archimedeanRayLogDeriv b + (1 / (b - 1) + deriv realZetaSeries b / realZetaSeries b) := by
    filter_upwards [Ioi_mem_nhds hs] with y hy using xiRayLogDeriv_split hy
  rw [radialJet_congr_of_eventuallyEq hEq,
    radialJet_add (fun k => contDiffAt_archimedeanRayLogDeriv hs (k : ℕ))
      (fun k => (contDiffAt_poleTerm hs (k : ℕ)).add (contDiffAt_realZetaLogDeriv hs (k : ℕ))),
    radialJet_poleCorrectedLogDeriv hs]

end

end RHTower
