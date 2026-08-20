import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The second and third response of an exponential formation

For an exponential formation with log-partition `F`, first response `m = −F'`, second response
`V = −m'` and third response `κ₃ = −V'`, the symmetric Jeffreys work is integrated second response
while the directed information commutator is integrated **third** response:

`J(u) = u ∫₀ᵘ V`,  `χ(u) = ∫₀ᵘ (u − 2t) V(t) dt = ∫₀ᵘ t (u − t) κ₃(t) dt`.

The two directed costs are recovered from the pair `(J, χ)`.  Only the response chain and the
Fundamental Theorem of Calculus are used; the differentiation-under-the-integral step that produces
the response chain is the hypothesis of the source theorem.
-/

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

variable (F m : ℝ → ℝ) (u : ℝ)

/-- The forward directed formation cost `D(P₀‖P_u)`. -/
def directedForward : ℝ := F u - F 0 + u * m 0

/-- The reverse directed formation cost `D(P_u‖P₀)`. -/
def directedReverse : ℝ := F 0 - F u - u * m u

/-- The symmetric Jeffreys formation work. -/
def jeffreysWork : ℝ := directedForward F m u + directedReverse F m u

/-- The directed information commutator. -/
def formationChiralityAt : ℝ := directedForward F m u - directedReverse F m u

theorem jeffreysWork_eq : jeffreysWork F m u = u * (m 0 - m u) := by
  simp only [jeffreysWork, directedForward, directedReverse]
  ring

theorem formationChiralityAt_eq :
    formationChiralityAt F m u = 2 * (F u - F 0) + u * (m 0 + m u) := by
  simp only [formationChiralityAt, directedForward, directedReverse]
  ring

/-- **(FCRM.12)**  The two directed costs are reconstructed from the symmetric work and the
commutator. -/
theorem directed_reconstruction :
    directedForward F m u = (jeffreysWork F m u + formationChiralityAt F m u) / 2 ∧
      directedReverse F m u = (jeffreysWork F m u - formationChiralityAt F m u) / 2 := by
  constructor <;> · simp only [jeffreysWork, formationChiralityAt]; ring

variable {F m}

section Responses

variable {V κ₃ : ℝ → ℝ} {u}

/-- **(FCRM.10)**  Jeffreys work is integrated second response. -/
theorem jeffreysWork_eq_integral_secondResponse
    (hm : ∀ t ∈ Set.uIcc 0 u, HasDerivAt m (-(V t)) t)
    (hV : IntervalIntegrable V MeasureTheory.volume 0 u) :
    jeffreysWork F m u = u * ∫ t in (0 : ℝ)..u, V t := by
  have hFTC : ∫ t in (0 : ℝ)..u, -(V t) = m u - m 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hm hV.neg
  rw [jeffreysWork_eq]
  rw [intervalIntegral.integral_neg] at hFTC
  have : ∫ t in (0 : ℝ)..u, V t = m 0 - m u := by linarith
  rw [this]

/-- **(FCRM.11), first form.**  The commutator is the antisymmetrically weighted second response. -/
theorem formationChiralityAt_eq_integral_secondResponse
    (hF : ∀ t ∈ Set.uIcc 0 u, HasDerivAt F (-(m t)) t)
    (hm : ∀ t ∈ Set.uIcc 0 u, HasDerivAt m (-(V t)) t)
    (hmi : IntervalIntegrable m MeasureTheory.volume 0 u)
    (hVi : IntervalIntegrable V MeasureTheory.volume 0 u) :
    formationChiralityAt F m u = ∫ t in (0 : ℝ)..u, (u - 2 * t) * V t := by
  have hFTC : ∫ t in (0 : ℝ)..u, -(m t) = F u - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF hmi.neg
  rw [intervalIntegral.integral_neg] at hFTC
  have hw : ∀ t ∈ Set.uIcc (0 : ℝ) u, HasDerivAt (fun x : ℝ => u - 2 * x) (-2) t := by
    intro t _
    simpa using (((hasDerivAt_id t).const_mul (2 : ℝ)).const_sub u)
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hw hm
    (by simpa using (intervalIntegrable_const (c := (-2 : ℝ))))
    hVi.neg
  -- `∫ (u - 2t) * (-(V t)) = (u - 2u) * m u - (u - 0) * m 0 - ∫ (-2) * m t`
  have hleft : ∫ t in (0 : ℝ)..u, (u - 2 * t) * -(V t)
      = -∫ t in (0 : ℝ)..u, (u - 2 * t) * V t := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun t _ => by ring
  have hright : ∫ t in (0 : ℝ)..u, (-2 : ℝ) * m t = -2 * ∫ t in (0 : ℝ)..u, m t := by
    rw [intervalIntegral.integral_const_mul]
  rw [hleft, hright] at hIBP
  rw [formationChiralityAt_eq]
  have hFu : F u - F 0 = -∫ t in (0 : ℝ)..u, m t := by linarith [hFTC]
  rw [hFu]
  have hz : u - 2 * u = -u := by ring
  have hz0 : u - 2 * (0:ℝ) = u := by ring
  rw [hz, hz0] at hIBP
  linarith [hIBP]

/-- **(FCRM.11), boxed form.**  The commutator is integrated third response. -/
theorem formationChiralityAt_eq_integral_thirdResponse
    (hF : ∀ t ∈ Set.uIcc 0 u, HasDerivAt F (-(m t)) t)
    (hm : ∀ t ∈ Set.uIcc 0 u, HasDerivAt m (-(V t)) t)
    (hV : ∀ t ∈ Set.uIcc 0 u, HasDerivAt V (-(κ₃ t)) t)
    (hmi : IntervalIntegrable m MeasureTheory.volume 0 u)
    (hVi : IntervalIntegrable V MeasureTheory.volume 0 u)
    (hκi : IntervalIntegrable κ₃ MeasureTheory.volume 0 u) :
    formationChiralityAt F m u = ∫ t in (0 : ℝ)..u, t * (u - t) * κ₃ t := by
  rw [formationChiralityAt_eq_integral_secondResponse hF hm hmi hVi]
  have hg : ∀ t ∈ Set.uIcc (0 : ℝ) u, HasDerivAt (fun x : ℝ => x * (u - x)) (u - 2 * t) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => x * (u - x)) (1 * (u - t) + t * (-1)) t :=
      (hasDerivAt_id t).mul ((hasDerivAt_id t).const_sub u |>.congr_deriv (by ring))
    convert h1 using 1
    ring
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hg hV
    (by
      have : IntervalIntegrable (fun t : ℝ => u - 2 * t) MeasureTheory.volume 0 u :=
        (Continuous.intervalIntegrable (by fun_prop) _ _)
      exact this)
    hκi.neg
  have hleft : ∫ t in (0 : ℝ)..u, t * (u - t) * -(κ₃ t)
      = -∫ t in (0 : ℝ)..u, t * (u - t) * κ₃ t := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hleft] at hIBP
  simp only [sub_self, mul_zero, zero_mul, zero_sub, sub_zero] at hIBP
  linarith [hIBP]

end Responses

end GaloisForLFunctions.HTGeometry
