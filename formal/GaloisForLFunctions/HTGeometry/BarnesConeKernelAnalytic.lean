import GaloisForLFunctions.HTGeometry.BarnesKernelExpansion
import GaloisForLFunctions.HTGeometry.BarnesDoubleZetaSeries
import GaloisForLFunctions.HTGeometry.AnalyticSlopeFactor

/-!
# The Barnes cone kernel has a double pole and nothing worse

The cone kernel `F(t) = e^(-xt)/((1-e^(-ω₁t))(1-e^(-ω₂t)))` blows up like `t^(-2)` at the origin.
Multiplying by `t²` and filling in the removable singularities of the two factors `t/(1-e^(-ωt))`
gives a function analytic at the origin, whose second-order Taylor expansion

```text
t² F(t) = 1/(ω₁ω₂) + t A₁ + t² R(t)
```

isolates exactly the two singular contributions to the Mellin transform: the constant term produces
the pole at `s = 2` and the linear term the pole at `s = 1`, while the analytic remainder gives an
integral convergent for `Re s > 0`.
-/

open Complex Filter Metric
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Barnes cone kernel with its double pole removed: `t² F(t)`, extended across the origin. -/
def barnesConeKernelAnalytic (o1 o2 x : ℂ) (z : ℂ) : ℂ :=
  Complex.exp (-(x * z)) * cylKernelFactor o1 z * cylKernelFactor o2 z

@[simp] theorem barnesConeKernelAnalytic_zero (o1 o2 x : ℂ) :
    barnesConeKernelAnalytic o1 o2 x 0 = o1⁻¹ * o2⁻¹ := by
  simp [barnesConeKernelAnalytic]

/-- **The cone kernel has a double pole and nothing worse.**  Away from the origin the extended
kernel is `t²` times the cone kernel. -/
theorem barnesConeKernelAnalytic_ofReal (o1 o2 x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    barnesConeKernelAnalytic (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)
      = (t : ℂ) ^ 2 * barnesConeKernel o1 o2 x t := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hcast : ∀ o : ℝ, Complex.exp (-((o : ℂ) * (t : ℂ))) = ((Real.exp (-o * t) : ℝ) : ℂ) := by
    intro o
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have key : ∀ E T D1 D2 : ℂ, E * (T / D1) * (T / D2) = T ^ 2 * (E / (D1 * D2)) := by
    intro E T D1 D2
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [barnesConeKernelAnalytic, cylKernelFactor_of_ne htC, cylKernelFactor_of_ne htC,
    barnesConeKernel, hcast, hcast, hcast]
  exact key _ _ _ _

/-- **The extended cone kernel is analytic at the origin.** -/
theorem analyticAt_barnesConeKernelAnalytic {o1 o2 : ℂ} (h1 : o1 ≠ 0) (h2 : o2 ≠ 0) (x : ℂ) :
    AnalyticAt ℂ (barnesConeKernelAnalytic o1 o2 x) 0 := by
  have hexp : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-(x * z))) 0 :=
    ((analyticAt_const.mul analyticAt_id).neg).cexp'
  exact (hexp.mul (analyticAt_cylKernelFactor h1)).mul (analyticAt_cylKernelFactor h2)

/-- The analytic remainder in the second-order expansion of the extended cone kernel. -/
def barnesConeKernelRemainder (o1 o2 x : ℂ) : ℂ → ℂ :=
  analyticSlope (analyticSlope (barnesConeKernelAnalytic o1 o2 x) 0) 0

/-- **Second-order expansion of the extended cone kernel.**  The constant term `1/(ω₁ω₂)` and the
linear term carry the two poles of the Mellin transform, at `s = 2` and `s = 1`; the remainder is
analytic and contributes an integral convergent for `Re s > 0`. -/
theorem barnesConeKernelAnalytic_taylor (o1 o2 x z : ℂ) :
    barnesConeKernelAnalytic o1 o2 x z
      = o1⁻¹ * o2⁻¹ + z * deriv (barnesConeKernelAnalytic o1 o2 x) 0
        + z ^ 2 * barnesConeKernelRemainder o1 o2 x z := by
  have h := eq_taylor_two_add_sq_mul (barnesConeKernelAnalytic o1 o2 x) 0 z
  rw [barnesConeKernelAnalytic_zero, sub_zero] at h
  exact h

theorem analyticAt_barnesConeKernelRemainder {o1 o2 : ℂ} (h1 : o1 ≠ 0) (h2 : o2 ≠ 0) (x : ℂ) :
    AnalyticAt ℂ (barnesConeKernelRemainder o1 o2 x) 0 :=
  analyticAt_analyticSlope_two (analyticAt_barnesConeKernelAnalytic h1 h2 x)

end

end GaloisForLFunctions.HTGeometry
