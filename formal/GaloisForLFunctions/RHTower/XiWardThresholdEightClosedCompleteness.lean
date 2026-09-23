import GaloisForLFunctions.RHTower.XiWardThresholdEightCompleteness

/-!
# Closed threshold-eight completeness for the Xi Ward corner

The paired strict-right Xi response has Cauchy energy strictly larger than
eight.  Consequently the endpoint budget `c = 8` is still RH-complete: no
strict loss below eight is required.

This closes the endpoint left open by the strict-budget theorem and is the
form needed by a joint two-quantum source transport whose total source
energy is exactly eight.
-/

open Complex
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Endpoint budget-violation core.  A budget at most eight is strictly
smaller than the paired Cauchy energy of every point in the open strip. -/
theorem xiWardCornerBudget_violation_core_of_le_eight
    {c : ℝ} {lam r1 r2 : ℂ}
    (ha : 0 < lam.re) (hhalf : lam.re < 1 / 2) (hc : c ≤ 8)
    (hfloor : xiWardPairEnergy lam ≤ 2 * (r1.re + r2.re))
    (hQ : (0 : ℝ) ≤ ((4 : ℂ) * ((c : ℂ) *
        ((lam + (starRingEnd ℂ) lam)⁻¹ + (lam + lam)⁻¹ +
          ((starRingEnd ℂ) lam + (starRingEnd ℂ) lam)⁻¹ +
          ((starRingEnd ℂ) lam + lam)⁻¹) -
        (r1 + r2) * ((starRingEnd ℂ) r1 + (starRingEnd ℂ) r2))).re) :
    False := by
  have hD : 0 < 2 * lam.re * (2 * lam.re) +
      2 * lam.im * (2 * lam.im) := by
    nlinarith [mul_pos ha ha, mul_self_nonneg lam.im]
  have hN : 0 < lam.re ^ (2 : ℕ) + lam.im ^ (2 : ℕ) := by
    nlinarith [pow_pos ha 2, sq_nonneg lam.im]
  have h4re : ∀ z : ℂ, ((4 : ℂ) * z).re = 4 * z.re := fun z => by
    norm_num [Complex.mul_re]
  rw [h4re, Complex.sub_re, Complex.re_ofReal_mul, Complex.add_re,
    Complex.add_re, Complex.add_re, re_inv_self_add_conj,
    re_inv_self_add_self, re_inv_conj_add_conj,
    re_inv_conj_add_self, ← map_add, Complex.mul_conj,
    Complex.ofReal_re] at hQ
  have hgsum : (2 * lam.re)⁻¹ +
      2 * lam.re /
          (2 * lam.re * (2 * lam.re) + 2 * lam.im * (2 * lam.im)) +
      2 * lam.re /
          (2 * lam.re * (2 * lam.re) + 2 * lam.im * (2 * lam.im)) +
      (2 * lam.re)⁻¹ = xiWardPairEnergy lam / 4 := by
    rw [xiWardPairEnergy]
    field_simp
    ring
  rw [hgsum] at hQ
  have hE := eight_lt_xiWardPairEnergy ha hhalf
  have hsq : (r1 + r2).re * (r1 + r2).re ≤
      Complex.normSq (r1 + r2) :=
    Complex.re_sq_le_normSq (r1 + r2)
  rw [Complex.add_re] at hsq
  have hcE : c < xiWardPairEnergy lam := lt_of_le_of_lt hc hE
  nlinarith [mul_self_le_mul_self
      (by linarith : (0 : ℝ) ≤ xiWardPairEnergy lam / 2)
      (by linarith : xiWardPairEnergy lam / 2 ≤ r1.re + r2.re),
    mul_lt_mul_of_pos_right hcE
      (by linarith : (0 : ℝ) < xiWardPairEnergy lam)]

/-- A strict-right Xi Schwarz pair defeats the closed budget `c ≤ 8`. -/
theorem continuedXiWardCornerDefect_conjPair_not_posSemidef_of_le_eight
    (q : XiRightUpperZeroCopy) {c : ℝ} (hc : c ≤ 8) :
    ¬ (continuedXiWardCornerDefect c
        ![xiRightCenteredZero q.1,
          (starRingEnd ℂ) (xiRightCenteredZero q.1)]).PosSemidef := by
  intro h
  have hquad := h.dotProduct_mulVec_nonneg ![2, 2]
  rw [Complex.le_def] at hquad
  have hQ0 := hquad.1
  rw [Complex.zero_re] at hQ0
  have hexpand : star (![2, 2] : Fin 2 → ℂ) ⬝ᵥ
      (continuedXiWardCornerDefect c
        ![xiRightCenteredZero q.1,
          (starRingEnd ℂ) (xiRightCenteredZero q.1)]).mulVec ![2, 2] =
      (4 : ℂ) * ((c : ℂ) *
        ((xiRightCenteredZero q.1 +
            (starRingEnd ℂ) (xiRightCenteredZero q.1))⁻¹ +
          (xiRightCenteredZero q.1 + xiRightCenteredZero q.1)⁻¹ +
          ((starRingEnd ℂ) (xiRightCenteredZero q.1) +
            (starRingEnd ℂ) (xiRightCenteredZero q.1))⁻¹ +
          ((starRingEnd ℂ) (xiRightCenteredZero q.1) +
            xiRightCenteredZero q.1)⁻¹) -
        (continuedXiAntiCausalWardResponse
              (xiRightCenteredZero q.1) +
            continuedXiAntiCausalWardResponse
              ((starRingEnd ℂ) (xiRightCenteredZero q.1))) *
          ((starRingEnd ℂ)
              (continuedXiAntiCausalWardResponse
                (xiRightCenteredZero q.1)) +
            (starRingEnd ℂ)
              (continuedXiAntiCausalWardResponse
                ((starRingEnd ℂ) (xiRightCenteredZero q.1))))) := by
    simp only [continuedXiWardCornerDefect,
      rightHalfPlaneHardyCauchyGram, dotProduct, Matrix.mulVec,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.star_apply, RCLike.star_def, Complex.conj_conj, map_ofNat,
      one_div]
    ring
  rw [hexpand] at hQ0
  exact xiWardCornerBudget_violation_core_of_le_eight
    (xiRightCenteredZero_re_pos q.1)
    ((abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2) hc
    (xiWardPairEnergy_le_two_mul_re_continuedResponses q) hQ0

/-- Closed threshold-eight implication: positivity with any nonnegative
budget at most eight forces RH. -/
theorem riemannHypothesis_of_continuedXiWardCornerLiftLaw_of_le_eight
    {c : ℝ} (hc : c ≤ 8) (hlaw : ContinuedXiWardCornerLiftLaw c) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  have hnode : ∀ i : Fin 2, 0 <
      ((![xiRightCenteredZero q.1,
        (starRingEnd ℂ) (xiRightCenteredZero q.1)] :
          Fin 2 → ℂ) i).re := by
    intro i
    fin_cases i
    · simpa using xiRightCenteredZero_re_pos q.1
    · simpa using xiRightCenteredZero_re_pos q.1
  exact
    continuedXiWardCornerDefect_conjPair_not_posSemidef_of_le_eight
      q hc (hlaw _ hnode)

/-- **Closed threshold-eight corner completeness law.**  Every fixed budget
`0 ≤ c ≤ 8`, including the exact doubled-source endpoint `c = 8`, is
equivalent to RH. -/
theorem riemannHypothesis_iff_continuedXiWardCornerLiftLaw_of_le_eight
    {c : ℝ} (hc0 : 0 ≤ c) (hc8 : c ≤ 8) :
    RiemannHypothesis ↔ ContinuedXiWardCornerLiftLaw c :=
  ⟨continuedXiWardCornerLiftLaw_of_riemannHypothesis hc0,
    riemannHypothesis_of_continuedXiWardCornerLiftLaw_of_le_eight hc8⟩

/-- Exact endpoint specialization used by an eight-unit joint source
transport. -/
theorem riemannHypothesis_iff_continuedXiWardCornerLiftLaw_eight :
    RiemannHypothesis ↔ ContinuedXiWardCornerLiftLaw 8 :=
  riemannHypothesis_iff_continuedXiWardCornerLiftLaw_of_le_eight
    (by norm_num) (by norm_num)

/-- **Native-eight-to-four connector.**  Positivity of the joint
eight-unit corner on every finite packet is equivalent, unconditionally, to
positivity of the requested augmented Gram
`[[G_P, r_P], [r_Pᴴ, 4]]` on every finite packet.  Thus a source transport
may spend the full native two-channel budget eight; no separate strict
contraction back to four is required. -/
theorem continuedXiWardCornerLiftLaw_eight_iff_fourUnitBoundaryGramLaw :
    ContinuedXiWardCornerLiftLaw 8 ↔
      ContinuedXiWardFourUnitBoundaryGramLaw :=
  riemannHypothesis_iff_continuedXiWardCornerLiftLaw_eight.symm.trans
    riemannHypothesis_iff_continuedXiWardFourUnitBoundaryGramLaw

end

end RHTower
