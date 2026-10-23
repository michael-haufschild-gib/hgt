import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspModularCompactTube
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionGaussRiccatiSource

/-!
# A global barrier for the literal modular mass drift

The complete actual orbit rules out Riccati escape. Its exponentially damped
distance from the wall satisfies a strict square contraction on the full
positive ray, so the wall is never reached.
-/

namespace RHTower
noncomputable section
set_option maxHeartbeats 800000

/-- Nonnegative mass drift on the positive modular half-orbit. -/
def thetaCuspModularMassDrift (x : ℝ) : ℝ := -(thetaCuspModularDrift x).re

/-- Real Riccati equation retaining the positive discriminant gap. -/
theorem hasDerivAt_thetaCuspModularMassDrift (x : ℝ) :
    HasDerivAt thetaCuspModularMassDrift
      (-3 + thetaCuspModularMassDrift x^(2 : ℕ)/3 +
        3*thetaCuspModularGapAmplitude x/4) x := by
  convert (hasDerivAt_thetaCuspModularDrift_re x).neg using 1 <;>
    first | rfl | (dsimp [thetaCuspModularMassDrift, thetaCuspModularGapAmplitude]; ring)

@[simp] theorem thetaCuspModularMassDrift_zero : thetaCuspModularMassDrift 0 = 0 := by
  simp [thetaCuspModularMassDrift, thetaCuspModularDrift_re_zero]

/-- The actual mass drift is nonnegative on the nonnegative half-line. -/
theorem thetaCuspModularMassDrift_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thetaCuspModularMassDrift x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [thetaCuspModularMassDrift_zero]
  · exact (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)).le

private def dampedGap (x : ℝ) : ℝ :=
  Real.exp (-2*x) * (1-thetaCuspModularMassDrift x/3)

private theorem hasDerivAt_dampedGap (x : ℝ) :
    HasDerivAt dampedGap
      (-Real.exp (-2*x) * ((1-thetaCuspModularMassDrift x/3)^(2 : ℕ) +
        thetaCuspModularGapAmplitude x/4)) x := by
  have he := ((hasDerivAt_id x).const_mul (-2 : ℝ)).exp
  have hu := ((hasDerivAt_thetaCuspModularMassDrift x).div_const 3).const_sub 1
  convert he.mul hu using 1 <;> first | rfl | (simp only [id_eq]; ring)

private theorem dampedGap_contraction {x : ℝ} (hx : 0 < x) :
    deriv dampedGap x < -(dampedGap x)^(2 : ℕ) := by
  rw [(hasDerivAt_dampedGap x).deriv]
  have he := Real.exp_pos (-2*x)
  have he1 : Real.exp (-2*x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he2 : Real.exp (-2*x)^(2 : ℕ) ≤ Real.exp (-2*x) := pow_le_of_le_one he.le he1 two_ne_zero
  have hb := mul_le_mul_of_nonneg_right he2
    (sq_nonneg (1-thetaCuspModularMassDrift x/3))
  have ha := mul_pos he (thetaCuspModularGapAmplitude_pos x)
  unfold dampedGap
  nlinarith only [hb, ha]

/-- The full literal orbit remains strictly below the Riccati escape wall. -/
theorem thetaCuspModularMassDrift_lt_three {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspModularMassDrift x < 3 := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [thetaCuspModularMassDrift_zero]; norm_num
  have h := pos_of_deriv_lt_neg_sq_on_Ioi hx
    (fun t _ => (hasDerivAt_dampedGap t).differentiableAt)
    (fun t ht => dampedGap_contraction ht)
  unfold dampedGap at h
  have hgap := (mul_pos_iff.mp h).resolve_right
    (fun hn => (not_lt_of_gt (Real.exp_pos (-2*x))) hn.1)
  linarith [hgap.2]

/-- Global source bound, with no terminal estimate or numerical orbit premise. -/
theorem thetaCuspModularMassDrift_mem_Ico :
    ∀ x : ℝ, 0 ≤ x → thetaCuspModularMassDrift x ∈ Set.Ico (0 : ℝ) 3 := by
  intro x hx
  exact ⟨thetaCuspModularMassDrift_nonneg hx, thetaCuspModularMassDrift_lt_three hx⟩

end
end RHTower
