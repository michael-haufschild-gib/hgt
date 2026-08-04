import GaloisForLFunctions.RHTower.DigammaQuarter
import GaloisForLFunctions.RHTower.CCMLocalRatioPlaces

/-!
# The archimedean local ratio on the critical line

The completed archimedean factor is `gamma_infinity(s) = pi^(-s/2) Gamma(s/2)` and the archimedean
local ratio is `rho_infinity(s) = gamma_infinity(s)/gamma_infinity(1-s)`.  Restricted to the critical
line it becomes

```text
u_infinity(t) = gamma_infinity(1/2 + it)/gamma_infinity(1/2 - it),
```

with `u_infinity(0) = 1` and `u_infinity'(0) = -i b_infinity`, `b_infinity = log pi - psi(1/4) > 0`.

* `gammaArch`, `gammaArch_eq_cpow` — the factor, written through `exp` so that differentiation is
  elementary, together with the bridge to the `pi^(-s/2)` form.
* `hasDerivAt_gammaArch_half` — the log-derivative at the seam is `(psi(1/4) - log pi)/2`, i.e.
  `-b_infinity/2`.  The factor `1/2` is the chain rule from `Gamma(s/2)`, and the two halves of
  `b_infinity` come from the two factors of `gamma_infinity`.
* `archRatio_zero`, `hasDerivAt_archRatio` — equation `(4)`.

Together with `hasDerivAt_primeRatio` this supplies the first jets of **all** places, so the generic
anomaly theorems of `CCMLocalRatioAnomaly.lean` apply to the completed family `V = {infinity} ∪ F`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Complex Filter Topology

theorem quarter_ne_negNatCast : ∀ m : ℕ, (1 / 4 : ℂ) ≠ -(m : ℂ) := by
  intro m hm
  have hre : ((1 / 4 : ℂ)).re = (-(m : ℂ)).re := by rw [hm]
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have h4 : ((1 / 4 : ℂ)).re = 1 / 4 := by norm_num
  rw [h4] at hre
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem gamma_quarter_ne_zero : Complex.Gamma (1 / 4 : ℂ) ≠ 0 :=
  Complex.Gamma_ne_zero quarter_ne_negNatCast

/-- The completed archimedean factor `pi^(-s/2) Gamma(s/2)`. -/
def gammaArch (s : ℂ) : ℂ :=
  Complex.exp (-(s / 2) * Complex.log (Real.pi : ℂ)) * Complex.Gamma (s / 2)

theorem gammaArch_eq_cpow (s : ℂ) :
    gammaArch s = ((Real.pi : ℝ) : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [gammaArch, Complex.cpow_def_of_ne_zero hpi]
  congr 2
  ring

theorem gammaArch_half_ne_zero : gammaArch (1 / 2 : ℂ) ≠ 0 := by
  rw [gammaArch]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  rw [show (1 / 2 : ℂ) / 2 = 1 / 4 from by norm_num]
  exact gamma_quarter_ne_zero

/-- The `Gamma` half of the archimedean factor, differentiated at the seam. -/
theorem hasDerivAt_gammaHalf :
    HasDerivAt (fun s : ℂ => Complex.Gamma (s / 2))
      (digamma (1 / 4 : ℂ) * Complex.Gamma (1 / 4 : ℂ) * (1 / 2)) (1 / 2 : ℂ) := by
  have hdG : DifferentiableAt ℂ Complex.Gamma (1 / 4 : ℂ) :=
    Complex.differentiableAt_Gamma _ quarter_ne_negNatCast
  have hderiv : deriv Complex.Gamma (1 / 4 : ℂ)
      = digamma (1 / 4 : ℂ) * Complex.Gamma (1 / 4 : ℂ) := by
    have h : digamma (1 / 4 : ℂ) = deriv Complex.Gamma (1 / 4 : ℂ) / Complex.Gamma (1 / 4 : ℂ) := by
      rw [show digamma (1 / 4 : ℂ) = logDeriv Complex.Gamma (1 / 4 : ℂ) from
        congrFun Complex.digamma_def (1 / 4 : ℂ), logDeriv_apply]
    rw [h, div_mul_cancel₀ _ gamma_quarter_ne_zero]
  have hinner : HasDerivAt (fun s : ℂ => s / 2) (1 / 2 : ℂ) (1 / 2 : ℂ) := by
    simpa using (hasDerivAt_id (1 / 2 : ℂ)).div_const 2
  have hGat : HasDerivAt Complex.Gamma
      (digamma (1 / 4 : ℂ) * Complex.Gamma (1 / 4 : ℂ)) ((fun s : ℂ => s / 2) (1 / 2 : ℂ)) := by
    rw [show ((fun s : ℂ => s / 2) (1 / 2 : ℂ)) = 1 / 4 from by norm_num, ← hderiv]
    exact hdG.hasDerivAt
  exact hGat.comp (1 / 2 : ℂ) hinner

/-- The exponential half of the archimedean factor, differentiated at the seam. -/
theorem hasDerivAt_expArch :
    HasDerivAt (fun s : ℂ => Complex.exp (-(s / 2) * Complex.log (Real.pi : ℂ)))
      (Complex.exp (-((1 : ℂ) / 2 / 2) * Complex.log (Real.pi : ℂ))
        * (-(1 / 2) * Complex.log (Real.pi : ℂ))) (1 / 2 : ℂ) := by
  have hinner : HasDerivAt (fun s : ℂ => -(s / 2) * Complex.log (Real.pi : ℂ))
      (-(1 / 2) * Complex.log (Real.pi : ℂ)) (1 / 2 : ℂ) := by
    have h1 : HasDerivAt (fun s : ℂ => -(s / 2)) (-(1 / 2) : ℂ) (1 / 2 : ℂ) := by
      have h0 : HasDerivAt (fun s : ℂ => s / 2) (1 / 2 : ℂ) (1 / 2 : ℂ) := by
        simpa using (hasDerivAt_id (1 / 2 : ℂ)).div_const 2
      exact h0.neg
    exact h1.mul_const _
  exact HasDerivAt.cexp hinner

/-- **The archimedean log-derivative at the seam.**  It is `-b_infinity/2`, with the two halves coming
from the two factors of `gamma_infinity`. -/
theorem hasDerivAt_gammaArch_half :
    HasDerivAt gammaArch (gammaArch (1 / 2 : ℂ) * (-((archRatioCharge : ℝ) : ℂ) / 2))
      (1 / 2 : ℂ) := by
  have hE := hasDerivAt_expArch
  have hG := hasDerivAt_gammaHalf
  have hmul := hE.mul hG
  have hEval : Complex.exp (-((1 : ℂ) / 2 / 2) * Complex.log (Real.pi : ℂ))
      = Complex.exp (-((1 : ℂ) / 2 / 2) * Complex.log (Real.pi : ℂ)) := rfl
  have hval : Complex.exp (-((1 : ℂ) / 2 / 2) * Complex.log (Real.pi : ℂ))
        * (-(1 / 2) * Complex.log (Real.pi : ℂ))
        * Complex.Gamma ((1 : ℂ) / 2 / 2)
      + Complex.exp (-((1 : ℂ) / 2 / 2) * Complex.log (Real.pi : ℂ))
        * (digamma (1 / 4 : ℂ) * Complex.Gamma (1 / 4 : ℂ) * (1 / 2))
      = gammaArch (1 / 2 : ℂ) * (-((archRatioCharge : ℝ) : ℂ) / 2) := by
    have hq : (1 : ℂ) / 2 / 2 = 1 / 4 := by norm_num
    have hlogpi : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) :=
      (Complex.ofReal_log Real.pi_pos.le).symm
    rw [hq, gammaArch, hq, ofReal_archRatioCharge, hlogpi]
    ring
  rw [hval] at hmul
  exact hmul

/-! ## The critical-line archimedean ratio -/

/-- The archimedean local ratio restricted to the critical line. -/
def archRatio (t : ℝ) : ℂ :=
  gammaArch (1 / 2 + (t : ℂ) * Complex.I) / gammaArch (1 / 2 - (t : ℂ) * Complex.I)

theorem archRatio_zero : archRatio 0 = 1 := by
  rw [archRatio]
  norm_num
  exact gammaArch_half_ne_zero

theorem hasDerivAt_linePlusC :
    HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) + z * Complex.I) Complex.I (0 : ℂ) := by
  have h1 : HasDerivAt (fun z : ℂ => z * Complex.I) (1 * Complex.I) (0 : ℂ) :=
    (hasDerivAt_id (0 : ℂ)).mul_const Complex.I
  have h2 := HasDerivAt.const_add (1 / 2 : ℂ) h1
  rw [one_mul] at h2
  exact h2

theorem hasDerivAt_lineMinusC :
    HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) - z * Complex.I) (-Complex.I) (0 : ℂ) := by
  have h1 : HasDerivAt (fun z : ℂ => z * Complex.I) (1 * Complex.I) (0 : ℂ) :=
    (hasDerivAt_id (0 : ℂ)).mul_const Complex.I
  have h2 := HasDerivAt.const_sub (1 / 2 : ℂ) h1
  rw [one_mul] at h2
  exact h2

/-- The numerator of the archimedean ratio, differentiated at the seam. -/
theorem hasDerivAt_archPlus :
    HasDerivAt (fun t : ℝ => gammaArch (1 / 2 + (t : ℂ) * Complex.I))
      (gammaArch (1 / 2 : ℂ) * (-((archRatioCharge : ℝ) : ℂ) / 2) * Complex.I) 0 := by
  have hGat : HasDerivAt gammaArch (gammaArch (1 / 2 : ℂ) * (-((archRatioCharge : ℝ) : ℂ) / 2))
      ((fun z : ℂ => (1 / 2 : ℂ) + z * Complex.I) 0) := by
    rw [show ((fun z : ℂ => (1 / 2 : ℂ) + z * Complex.I) 0) = 1 / 2 from by norm_num]
    exact hasDerivAt_gammaArch_half
  have hcomp : HasDerivAt (gammaArch ∘ fun z : ℂ => (1 / 2 : ℂ) + z * Complex.I)
      (gammaArch (1 / 2 : ℂ) * (-((archRatioCharge : ℝ) : ℂ) / 2) * Complex.I)
      (((0 : ℝ)) : ℂ) := by
    rw [show (((0 : ℝ)) : ℂ) = 0 from by norm_num]
    exact hGat.comp (0 : ℂ) hasDerivAt_linePlusC
  exact hcomp.comp_ofReal

/-- The denominator of the archimedean ratio, differentiated at the seam. -/
theorem hasDerivAt_archMinus :
    HasDerivAt (fun t : ℝ => gammaArch (1 / 2 - (t : ℂ) * Complex.I))
      (gammaArch (1 / 2 : ℂ) * (-((archRatioCharge : ℝ) : ℂ) / 2) * -Complex.I) 0 := by
  have hGat : HasDerivAt gammaArch (gammaArch (1 / 2 : ℂ) * (-((archRatioCharge : ℝ) : ℂ) / 2))
      ((fun z : ℂ => (1 / 2 : ℂ) - z * Complex.I) 0) := by
    rw [show ((fun z : ℂ => (1 / 2 : ℂ) - z * Complex.I) 0) = 1 / 2 from by norm_num]
    exact hasDerivAt_gammaArch_half
  have hcomp : HasDerivAt (gammaArch ∘ fun z : ℂ => (1 / 2 : ℂ) - z * Complex.I)
      (gammaArch (1 / 2 : ℂ) * (-((archRatioCharge : ℝ) : ℂ) / 2) * -Complex.I)
      (((0 : ℝ)) : ℂ) := by
    rw [show (((0 : ℝ)) : ℂ) = 0 from by norm_num]
    exact hGat.comp (0 : ℂ) hasDerivAt_lineMinusC
  exact hcomp.comp_ofReal

/-- **Equation (4).**  The first jet of the archimedean local ratio at the seam is purely imaginary,
with magnitude `b_infinity = log pi - psi(1/4) > 0`. -/
theorem hasDerivAt_archRatio :
    HasDerivAt archRatio (-Complex.I * ((archRatioCharge : ℝ) : ℂ)) 0 := by
  have hplus := hasDerivAt_archPlus
  have hminus := hasDerivAt_archMinus
  have hden : (fun t : ℝ => gammaArch (1 / 2 - (t : ℂ) * Complex.I)) 0 ≠ 0 := by
    have hz : (fun t : ℝ => gammaArch (1 / 2 - (t : ℂ) * Complex.I)) 0 = gammaArch (1 / 2 : ℂ) := by
      norm_num
    rw [hz]
    exact gammaArch_half_ne_zero
  have hdiv := HasDerivAt.div hplus hminus hden
  have hval : (gammaArch (1 / 2 : ℂ) * (-((archRatioCharge : ℝ) : ℂ) / 2) * Complex.I
        * gammaArch (1 / 2 - ((0 : ℝ) : ℂ) * Complex.I)
      - gammaArch (1 / 2 + ((0 : ℝ) : ℂ) * Complex.I)
        * (gammaArch (1 / 2 : ℂ) * (-((archRatioCharge : ℝ) : ℂ) / 2) * -Complex.I))
      / gammaArch (1 / 2 - ((0 : ℝ) : ℂ) * Complex.I) ^ 2
      = -Complex.I * ((archRatioCharge : ℝ) : ℂ) := by
    have hz : ((0 : ℝ) : ℂ) * Complex.I = 0 := by norm_num
    have hGne : gammaArch (1 / 2 : ℂ) ≠ 0 := gammaArch_half_ne_zero
    rw [hz, sub_zero, add_zero]
    field_simp
    ring
  rw [hval] at hdiv
  exact hdiv

theorem archRatioCharge_ne_zero : ((archRatioCharge : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt archRatioCharge_pos)

end GaloisForLFunctions.RHTower

end
