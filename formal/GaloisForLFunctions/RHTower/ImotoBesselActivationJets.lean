import GaloisForLFunctions.RHTower.BesselJOneRecurrence

/-!
# All-order Bessel activation jets from arXiv:2609.03768
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set Filter Topology

def besselJ0HighJet (q : ℕ) (u : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ theta in (0 : ℝ)..Real.pi,
    Real.sin theta ^ q * Real.cos (u * Real.sin theta + (q : ℝ) * Real.pi / 2)

theorem besselJ0HighJet_zero (u : ℝ) : besselJ0HighJet 0 u = besselJ0 u := by
  simp [besselJ0HighJet, besselJ0]

theorem continuous_besselJ0HighJet_integrand (q : ℕ) (u : ℝ) :
    Continuous fun theta : ℝ => Real.sin theta ^ q *
      Real.cos (u * Real.sin theta + (q : ℝ) * Real.pi / 2) := by
  fun_prop

theorem hasDerivAt_besselJ0HighJet (q : ℕ) (u : ℝ) :
    HasDerivAt (besselJ0HighJet q) (besselJ0HighJet (q + 1) u) u := by
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := Real.pi) (bound := fun _ : ℝ => (1 : ℝ))
    (F := fun (x : ℝ) (theta : ℝ) => Real.sin theta ^ q *
      Real.cos (x * Real.sin theta + (q : ℝ) * Real.pi / 2))
    (F' := fun (x : ℝ) (theta : ℝ) => Real.sin theta ^ (q + 1) *
      Real.cos (x * Real.sin theta + ((q + 1 : ℕ) : ℝ) * Real.pi / 2))
    (x₀ := u) (s := Set.univ) (by simp)
    (Filter.Eventually.of_forall fun x =>
      ((continuous_besselJ0HighJet_integrand q x).aestronglyMeasurable).restrict)
    ((continuous_besselJ0HighJet_integrand q u).intervalIntegrable _ _)
    (((continuous_besselJ0HighJet_integrand (q + 1) u).aestronglyMeasurable).restrict)
    (Filter.Eventually.of_forall fun theta _ x _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      have hs : |Real.sin theta| ^ (q + 1) ≤ 1 := by
        simpa using pow_le_one₀ (abs_nonneg (Real.sin theta)) (Real.abs_sin_le_one theta)
      have hc : |Real.cos
          (x * Real.sin theta + ((q + 1 : ℕ) : ℝ) * Real.pi / 2)| ≤ 1 :=
        Real.abs_cos_le_one _
      nlinarith [abs_nonneg (Real.cos
        (x * Real.sin theta + ((q + 1 : ℕ) : ℝ) * Real.pi / 2))])
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun theta _ x _ => by
      have hinner : HasDerivAt
          (fun y : ℝ => y * Real.sin theta + (q : ℝ) * Real.pi / 2)
          (Real.sin theta) x := by
        simpa using ((hasDerivAt_id x).mul_const (Real.sin theta)).add_const
          ((q : ℝ) * Real.pi / 2)
      have h := ((Real.hasDerivAt_cos
        (x * Real.sin theta + (q : ℝ) * Real.pi / 2)).comp x hinner).const_mul
          (Real.sin theta ^ q)
      apply h.congr_deriv
      rw [show x * Real.sin theta + ((q + 1 : ℕ) : ℝ) * Real.pi / 2 =
          (x * Real.sin theta + (q : ℝ) * Real.pi / 2) + Real.pi / 2 by
            push_cast
            ring,
        Real.cos_add_pi_div_two, pow_succ]
      ring)
  have hderiv := hmain.2
  exact hderiv.const_mul (1 / Real.pi)

theorem abs_besselJ0HighJet_le_one (q : ℕ) (u : ℝ) :
    |besselJ0HighJet q u| ≤ 1 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hbd : ‖∫ theta in (0 : ℝ)..Real.pi,
      Real.sin theta ^ q * Real.cos (u * Real.sin theta + (q : ℝ) * Real.pi / 2)‖
      ≤ 1 * |Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun theta _ => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have hs : |Real.sin theta| ^ q ≤ 1 := by
      simpa using pow_le_one₀ (abs_nonneg (Real.sin theta)) (Real.abs_sin_le_one theta)
    have hc : |Real.cos (u * Real.sin theta + (q : ℝ) * Real.pi / 2)| ≤ 1 :=
      Real.abs_cos_le_one _
    nlinarith [abs_nonneg (Real.cos (u * Real.sin theta + (q : ℝ) * Real.pi / 2))]
  rw [Real.norm_eq_abs] at hbd
  rw [besselJ0HighJet, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.pi)]
  have hval : |Real.pi - 0| = Real.pi := by
    rw [sub_zero, abs_of_pos hpi]
  rw [hval, one_mul] at hbd
  calc
    1 / Real.pi * |∫ theta in (0 : ℝ)..Real.pi,
        Real.sin theta ^ q * Real.cos (u * Real.sin theta + (q : ℝ) * Real.pi / 2)|
        ≤ 1 / Real.pi * Real.pi := mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = 1 := by field_simp

def besselJ1HighJet (q : ℕ) (u : ℝ) : ℝ := -besselJ0HighJet (q + 1) u

theorem besselJ1HighJet_zero (u : ℝ) : besselJ1HighJet 0 u = besselJ1 u := by
  have hhigh := hasDerivAt_besselJ0HighJet 0 u
  have hfun : besselJ0HighJet 0 = besselJ0 := funext besselJ0HighJet_zero
  rw [hfun] at hhigh
  have hderiv : besselJ0HighJet 1 u = besselJ0Deriv u := by
    exact hhigh.unique (hasDerivAt_besselJ0 u)
  simp only [besselJ1HighJet, besselJ1, zero_add]
  rw [hderiv]

theorem hasDerivAt_besselJ1HighJet (q : ℕ) (u : ℝ) :
    HasDerivAt (besselJ1HighJet q) (besselJ1HighJet (q + 1) u) u := by
  have h := (hasDerivAt_besselJ0HighJet (q + 1) u).neg
  simp only [besselJ1HighJet, Nat.add_comm, Nat.add_left_comm]
  apply h.congr_of_eventuallyEq
  filter_upwards with y
  rfl

theorem abs_besselJ1HighJet_le_one (q : ℕ) (u : ℝ) :
    |besselJ1HighJet q u| ≤ 1 := by
  simpa [besselJ1HighJet] using abs_besselJ0HighJet_le_one (q + 1) u

end GaloisForLFunctions.RHTower

end
