import Mathlib
import GaloisForLFunctions.HTGeometry.ConstitutiveStabilityWall
import GaloisForLFunctions.HTGeometry.ConstitutivePositiveResponse

/-!
# Antisymmetric intervention response across a stability wall

The A₂ wall family of central charges `z₁(θ) = exp(i(π/2 + θ))`, `z₂(θ) = exp(i(π/2 − θ))` has a
completely even passive positive packet `(1, 1, 4 cos²θ)`, so positivity cannot see which side of
the wall the law is on.  One fixed additive intervention, chosen before the wall is observed,
restores the side exactly: its antisymmetric component response is `4 sin θ`, and its sign is the
stability trichotomy of the extension.

The charges, their phase order and the stability classification are reused from
`ConstitutiveStabilityWall`; the intervention response and its derivative interpretation are reused
from `ConstitutivePositiveResponse`.
-/

namespace GaloisForLFunctions.HTGeometry

section RealParts

theorem wallCharge₁_re (θ : ℝ) : (wallCharge₁ θ).re = -Real.sin θ := by
  rw [wallCharge₁, Complex.exp_ofReal_mul_I_re]
  simp [Real.cos_add]

theorem wallCharge₂_re (θ : ℝ) : (wallCharge₂ θ).re = Real.sin θ := by
  rw [wallCharge₂, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_two_sub]

end RealParts

section PositivePacket

/-- The complete passive positive packet of the wall family, equation (3). -/
noncomputable def wallPositivePacket (θ : ℝ) : ℝ × ℝ × ℝ :=
  (constitutivePositiveDoctrine (wallCharge₁ θ),
    constitutivePositiveDoctrine (wallCharge₂ θ),
    constitutivePositiveDoctrine (wallCharge₁ θ + wallCharge₂ θ))

/-- **Equation (3).** -/
theorem wallPositivePacket_eq (θ : ℝ) :
    wallPositivePacket θ = (1, 1, 4 * Real.cos θ ^ 2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact constitutivePositiveDoctrine_unit_phase (Real.pi / 2 + θ)
  · exact constitutivePositiveDoctrine_unit_phase (Real.pi / 2 - θ)
  · show constitutivePositiveDoctrine (wallCharge₁ θ + wallCharge₂ θ) = 4 * Real.cos θ ^ 2
    rw [wallCharge_sum, constitutivePositiveDoctrine, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
    ring

/-- **Clause 1: the passive packet does not determine the chamber.** -/
theorem wallPositivePacket_even (θ : ℝ) : wallPositivePacket (-θ) = wallPositivePacket θ := by
  rw [wallPositivePacket_eq, wallPositivePacket_eq, Real.cos_neg]

end PositivePacket

section InterventionResponse

/-- Response of the first charge to the fixed real additive intervention `h = 1`. -/
noncomputable def wallResponse₁ (θ : ℝ) : ℝ := constitutiveAdditiveResponse 1 (wallCharge₁ θ)

/-- Response of the second charge to the same fixed intervention. -/
noncomputable def wallResponse₂ (θ : ℝ) : ℝ := constitutiveAdditiveResponse 1 (wallCharge₂ θ)

theorem constitutiveAdditiveResponse_one (z : ℂ) :
    constitutiveAdditiveResponse 1 z = 2 * z.re := by
  simp [constitutiveAdditiveResponse]

/-- **Equation (4) for the first charge:** the algebraic response really is the derivative of the
positive doctrine along the fixed intervention. -/
theorem wallResponse₁_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun ε : ℝ => constitutivePositiveDoctrine (wallCharge₁ θ + (ε : ℂ) * 1))
      (wallResponse₁ θ) 0 :=
  constitutivePositiveDoctrine_hasDerivAt_intervention 1 (wallCharge₁ θ)

/-- **Equation (4) for the second charge.** -/
theorem wallResponse₂_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun ε : ℝ => constitutivePositiveDoctrine (wallCharge₂ θ + (ε : ℂ) * 1))
      (wallResponse₂ θ) 0 :=
  constitutivePositiveDoctrine_hasDerivAt_intervention 1 (wallCharge₂ θ)

theorem wallResponse₁_eq (θ : ℝ) : wallResponse₁ θ = -(2 * Real.sin θ) := by
  rw [wallResponse₁, constitutiveAdditiveResponse_one, wallCharge₁_re]
  ring

theorem wallResponse₂_eq (θ : ℝ) : wallResponse₂ θ = 2 * Real.sin θ := by
  rw [wallResponse₂, constitutiveAdditiveResponse_one, wallCharge₂_re]

/-- The antisymmetric response `Δ = r₂ − r₁`. -/
noncomputable def antisymmetricWallResponse (θ : ℝ) : ℝ := wallResponse₂ θ - wallResponse₁ θ

/-- **Equation (5).** -/
theorem antisymmetricWallResponse_eq (θ : ℝ) :
    antisymmetricWallResponse θ = 4 * Real.sin θ := by
  rw [antisymmetricWallResponse, wallResponse₁_eq, wallResponse₂_eq]
  ring

end InterventionResponse

section SignTrichotomy

theorem sin_pos_iff_of_abs_lt {θ : ℝ} (h : |θ| < Real.pi / 2) :
    0 < Real.sin θ ↔ 0 < θ := by
  have hb := abs_lt.mp h
  have hpi := Real.pi_pos
  constructor
  · intro hsin
    rcases lt_trichotomy θ 0 with hlt | heq | hgt
    · exact absurd hsin (not_lt.mpr
        (le_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt hlt (by linarith))))
    · rw [heq, Real.sin_zero] at hsin; exact absurd hsin (lt_irrefl 0)
    · exact hgt
  · intro hpos
    exact Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)

theorem sin_neg_iff_of_abs_lt {θ : ℝ} (h : |θ| < Real.pi / 2) :
    Real.sin θ < 0 ↔ θ < 0 := by
  have hb := abs_lt.mp h
  have hpi := Real.pi_pos
  constructor
  · intro hsin
    rcases lt_trichotomy θ 0 with hlt | heq | hgt
    · exact hlt
    · rw [heq, Real.sin_zero] at hsin; exact absurd hsin (lt_irrefl 0)
    · exact absurd hsin (not_lt.mpr
        (le_of_lt (Real.sin_pos_of_pos_of_lt_pi hgt (by linarith))))
  · intro hneg
    exact Real.sin_neg_of_neg_of_neg_pi_lt hneg (by linarith)

theorem sin_eq_zero_iff_of_abs_lt {θ : ℝ} (h : |θ| < Real.pi / 2) :
    Real.sin θ = 0 ↔ θ = 0 := by
  have hb := abs_lt.mp h
  have hpi := Real.pi_pos
  constructor
  · intro hsin
    rcases lt_trichotomy θ 0 with hlt | heq | hgt
    · exact absurd hsin (ne_of_lt ((sin_neg_iff_of_abs_lt h).mpr hlt))
    · exact heq
    · exact absurd hsin (ne_of_gt ((sin_pos_iff_of_abs_lt h).mpr hgt))
  · intro hzero
    rw [hzero, Real.sin_zero]

end SignTrichotomy

section WallTrichotomy

theorem im_mul_conj_swap (z w : ℂ) :
    (w * (starRingEnd ℂ) z).im = -((z * (starRingEnd ℂ) w).im) := by
  simp [Complex.mul_im]
  ring

/-- **The wall family is unstable exactly on the negative side.** -/
theorem wallFamily_unstable_iff_neg {θ : ℝ} (h : |θ| < Real.pi / 2) :
    ((wallCharge₁ θ + wallCharge₂ θ).arg < (wallCharge₂ θ).arg) ↔ θ < 0 := by
  obtain ⟨h₁, h₂⟩ := wallCharge_im_pos h
  have hsum : 0 < (wallCharge₁ θ + wallCharge₂ θ).im := by
    rw [Complex.add_im]; linarith
  rw [arg_lt_arg_iff_cross_pos h₂ hsum]
  have hexp : (wallCharge₂ θ * (starRingEnd ℂ) (wallCharge₁ θ + wallCharge₂ θ)).im
      = (wallCharge₂ θ * (starRingEnd ℂ) (wallCharge₁ θ)).im := by
    rw [map_add, mul_add, Complex.add_im, Complex.mul_conj]
    simp
  rw [hexp, im_mul_conj_swap, wallCharge_cross]
  have hb := abs_lt.mp h
  constructor
  · intro hlt
    by_contra hcon
    rw [not_lt] at hcon
    have hnn : 0 ≤ Real.sin (2 * θ) := by
      rcases lt_or_eq_of_le hcon with hgt | heq
      · exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
      · rw [← heq]; simp
    linarith
  · intro hneg
    have : Real.sin (2 * θ) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    linarith

/-- **The wall family is strictly semistable exactly on the wall.** -/
theorem wallFamily_semistable_iff_zero {θ : ℝ} (h : |θ| < Real.pi / 2) :
    ((wallCharge₁ θ + wallCharge₂ θ).arg = (wallCharge₂ θ).arg) ↔ θ = 0 := by
  obtain ⟨h₁, h₂⟩ := wallCharge_im_pos h
  constructor
  · intro heq
    rcases lt_trichotomy θ 0 with hlt | hzero | hgt
    · exact absurd ((wallFamily_unstable_iff_neg h).mpr hlt) (by rw [heq]; exact lt_irrefl _)
    · exact hzero
    · exact absurd ((wallFamily_stable_iff_pos h).mpr hgt) (by rw [heq]; exact lt_irrefl _)
  · intro hzero
    subst hzero
    have hcharge : wallCharge₁ (0 : ℝ) = wallCharge₂ (0 : ℝ) := by
      rw [wallCharge₁, wallCharge₂]
      norm_num
    exact arg_eq_of_arg_eq h₁ h₂ (by rw [hcharge])

end WallTrichotomy

section Selection

/-- **Equation (6): stability is exactly a positive antisymmetric response.** -/
theorem stable_iff_response_pos {θ : ℝ} (h : |θ| < Real.pi / 2) :
    ((wallCharge₂ θ).arg < (wallCharge₁ θ + wallCharge₂ θ).arg)
      ↔ 0 < antisymmetricWallResponse θ := by
  rw [wallFamily_stable_iff_pos h, antisymmetricWallResponse_eq]
  constructor
  · intro hpos
    have := (sin_pos_iff_of_abs_lt h).mpr hpos
    linarith
  · intro hpos
    exact (sin_pos_iff_of_abs_lt h).mp (by linarith)

/-- **Equation (7): strict semistability is exactly a vanishing antisymmetric response.** -/
theorem semistable_iff_response_zero {θ : ℝ} (h : |θ| < Real.pi / 2) :
    ((wallCharge₁ θ + wallCharge₂ θ).arg = (wallCharge₂ θ).arg)
      ↔ antisymmetricWallResponse θ = 0 := by
  rw [wallFamily_semistable_iff_zero h, antisymmetricWallResponse_eq]
  constructor
  · intro hzero
    rw [hzero, Real.sin_zero]
    ring
  · intro hzero
    exact (sin_eq_zero_iff_of_abs_lt h).mp (by linarith)

/-- **Equation (8): instability is exactly a negative antisymmetric response.** -/
theorem unstable_iff_response_neg {θ : ℝ} (h : |θ| < Real.pi / 2) :
    ((wallCharge₁ θ + wallCharge₂ θ).arg < (wallCharge₂ θ).arg)
      ↔ antisymmetricWallResponse θ < 0 := by
  rw [wallFamily_unstable_iff_neg h, antisymmetricWallResponse_eq]
  constructor
  · intro hneg
    have := (sin_neg_iff_of_abs_lt h).mpr hneg
    linarith
  · intro hneg
    exact (sin_neg_iff_of_abs_lt h).mp (by linarith)

/-- **The theorem.**  The complete passive positive packet is even in `θ`, so it cannot determine
the chamber; the antisymmetric response of one intervention fixed before the wall is observed is
`4 sin θ`, and its sign is exactly the stability trichotomy of the extension. -/
theorem antisymmetric_response_selects_chamber {θ : ℝ} (h : |θ| < Real.pi / 2) :
    wallPositivePacket (-θ) = wallPositivePacket θ ∧
      antisymmetricWallResponse θ = 4 * Real.sin θ ∧
      (((wallCharge₂ θ).arg < (wallCharge₁ θ + wallCharge₂ θ).arg)
        ↔ 0 < antisymmetricWallResponse θ) ∧
      (((wallCharge₁ θ + wallCharge₂ θ).arg = (wallCharge₂ θ).arg)
        ↔ antisymmetricWallResponse θ = 0) ∧
      (((wallCharge₁ θ + wallCharge₂ θ).arg < (wallCharge₂ θ).arg)
        ↔ antisymmetricWallResponse θ < 0) :=
  ⟨wallPositivePacket_even θ, antisymmetricWallResponse_eq θ, stable_iff_response_pos h,
    semistable_iff_response_zero h, unstable_iff_response_neg h⟩

/-- **The response is transverse to the positive quotient.**  At `θ` and `−θ` the whole passive
packet agrees while the antisymmetric response changes sign; so the intervention response does not
factor through passive positivity. -/
theorem antisymmetric_response_not_factoring {θ : ℝ} (h : |θ| < Real.pi / 2) (hpos : 0 < θ) :
    wallPositivePacket (-θ) = wallPositivePacket θ ∧
      antisymmetricWallResponse (-θ) = -antisymmetricWallResponse θ ∧
      antisymmetricWallResponse (-θ) ≠ antisymmetricWallResponse θ := by
  have hsin : 0 < Real.sin θ := (sin_pos_iff_of_abs_lt h).mpr hpos
  refine ⟨wallPositivePacket_even θ, ?_, ?_⟩
  · rw [antisymmetricWallResponse_eq, antisymmetricWallResponse_eq, Real.sin_neg]
    ring
  · rw [antisymmetricWallResponse_eq, antisymmetricWallResponse_eq, Real.sin_neg]
    intro hcon
    linarith

end Selection

end GaloisForLFunctions.HTGeometry
