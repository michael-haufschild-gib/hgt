import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set intervalIntegral MeasureTheory

namespace GaloisForLFunctions.HTGeometry.NavierStokesCumulativeEnergyBound

noncomputable section

/-- Accumulated forcing magnitude from time zero. -/
def cumulativeForcing (q : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, q s

@[simp] theorem cumulativeForcing_zero (q : ℝ → ℝ) : cumulativeForcing q 0 = 0 := by
  simp [cumulativeForcing]

theorem hasDerivAt_cumulativeForcing {q : ℝ → ℝ} (hq : Continuous q) (t : ℝ) :
    HasDerivAt (cumulativeForcing q) (q t) t := by
  exact intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable 0 t)
    hq.aestronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt

theorem continuous_cumulativeForcing {q : ℝ → ℝ} (hq : Continuous q) :
    Continuous (cumulativeForcing q) :=
  (intervalIntegral.differentiable_integral_of_continuous (a := (0 : ℝ)) hq).continuous

/-- Exact chain-rule closure behind the last equality in Lemma 10.4:
`2 ∫₀ᵗ q(s) F(s) ds = F(t)²` for `F(t) = ∫₀ᵗ q(s) ds`. -/
theorem two_mul_integral_mul_cumulativeForcing (q : ℝ → ℝ) (hq : Continuous q) (t : ℝ) :
    2 * ∫ s in (0 : ℝ)..t, q s * cumulativeForcing q s = cumulativeForcing q t ^ (2 : ℕ) := by
  have hFcont : Continuous (cumulativeForcing q) := continuous_cumulativeForcing hq
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun x ↦ cumulativeForcing q x ^ (2 : ℕ))
        (2 * (q s * cumulativeForcing q s)) s := by
    intro s _
    exact ((hasDerivAt_cumulativeForcing hq s).pow 2).congr_deriv (by ring)
  have hint : IntervalIntegrable (fun s ↦ 2 * (q s * cumulativeForcing q s)) volume 0 t :=
    ((hq.mul hFcont).const_mul 2).intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hFTC
  simpa [cumulativeForcing_zero] using hFTC

/-- **Lemma 10.4, scalar energy closure.** If the velocity norm `N` is bounded by accumulated
forcing and the integrated energy identity has work `∫ qN`, then kinetic energy plus twice the
dissipation is bounded by the square of accumulated forcing. -/
theorem energy_add_dissipation_le_cumulativeForcing_sq
    {q N D : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hq : Continuous q) (hN : Continuous N)
    (hq_nonneg : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ q s)
    (hN_le : ∀ s ∈ Icc (0 : ℝ) t, N s ≤ cumulativeForcing q s)
    (henergy : N t ^ (2 : ℕ) + 2 * ∫ s in (0 : ℝ)..t, D s =
      2 * ∫ s in (0 : ℝ)..t, q s * N s) :
    N t ^ (2 : ℕ) + 2 * ∫ s in (0 : ℝ)..t, D s ≤ cumulativeForcing q t ^ (2 : ℕ) := by
  have hFcont : Continuous (cumulativeForcing q) := continuous_cumulativeForcing hq
  have hmono : (∫ s in (0 : ℝ)..t, q s * N s) ≤
      ∫ s in (0 : ℝ)..t, q s * cumulativeForcing q s := by
    exact intervalIntegral.integral_mono_on ht
      ((hq.mul hN).intervalIntegrable 0 t)
      ((hq.mul hFcont).intervalIntegrable 0 t)
      (fun s hs ↦ mul_le_mul_of_nonneg_left (hN_le s hs) (hq_nonneg s hs))
  calc
    N t ^ (2 : ℕ) + 2 * ∫ s in (0 : ℝ)..t, D s =
        2 * ∫ s in (0 : ℝ)..t, q s * N s := henergy
    _ ≤ 2 * ∫ s in (0 : ℝ)..t, q s * cumulativeForcing q s := by linarith
    _ = cumulativeForcing q t ^ (2 : ℕ) := two_mul_integral_mul_cumulativeForcing q hq t

end

end GaloisForLFunctions.HTGeometry.NavierStokesCumulativeEnergyBound
