import GaloisForLFunctions.HTGeometry.ArithmeticFunctionLSeriesDeterminant
import GaloisForLFunctions.RHTower.TwinRigidity

/-!
# Convolution-inverse analytic twins are zero-free

The report proposes arithmetic twins whose coefficient streams satisfy `a * d = 1`, while their
Mellin transforms continue holomorphically to the strict right half-plane and carry Xi zeros.
These requirements are incompatible.

In the common Euler chamber, multiplication of absolutely convergent `L`-series turns
`a * d = 1` into `A(s) D(s) = 1`. Both sides are analytic on the connected right half-plane, so
the identity theorem propagates this equality throughout that domain. Consequently neither
continued factor can vanish there.

The theorem is packaged as a closed existential no-go. No Xi divisor, RH premise, selected zero,
or extra axiom enters.
-/

open Complex Filter Topology
open ArithmeticFunction LSeries

noncomputable section

namespace RHTower

/-- Data asserted by the report's convolution-inverse twin proposal, including a zero in one
holomorphic continuation. -/
def AnalyticConvolutionInverseZeroPair : Prop :=
  ∃ a d : ArithmeticFunction ℂ, ∃ A D : ℂ → ℂ,
    a * d = 1 ∧
    AnalyticOnNhd ℂ A rightHalf ∧
    AnalyticOnNhd ℂ D rightHalf ∧
    (∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => a n) s) ∧
    (∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => d n) s) ∧
    (∀ s : ℂ, 1 < s.re → A s = LSeries (fun n => a n) s) ∧
    (∀ s : ℂ, 1 < s.re → D s = LSeries (fun n => d n) s) ∧
    ∃ ρ ∈ rightHalf, A ρ = 0 ∨ D ρ = 0

/-- No convolution-inverse coefficient pair can have two holomorphic right-half continuations if
either continuation has a right-half zero. -/
theorem not_analyticConvolutionInverseZeroPair :
    ¬ AnalyticConvolutionInverseZeroPair := by
  rintro ⟨a, d, A, D, hinv, hA, hD, hasum, hdsum, hAeq, hDeq,
    ρ, hρ, hzero⟩
  have hprod : AnalyticOnNhd ℂ (fun s => A s * D s) rightHalf := hA.mul hD
  have htwo : (2 : ℂ) ∈ rightHalf := by
    norm_num [rightHalf]
  have hevent : (fun s => A s * D s) =ᶠ[𝓝 (2 : ℂ)] fun _ => 1 := by
    have hsafe : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hsafe] with s hs
    rw [hAeq s hs, hDeq s hs,
      ← ArithmeticFunction.LSeries_mul' (hasum s hs) (hdsum s hs), hinv,
      (GaloisForLFunctions.arithmeticFunction_one_LSeries s).2]
  have hall := hprod.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected htwo hevent
  have hval := hall hρ
  rcases hzero with hzero | hzero <;> simp [hzero] at hval

end RHTower
