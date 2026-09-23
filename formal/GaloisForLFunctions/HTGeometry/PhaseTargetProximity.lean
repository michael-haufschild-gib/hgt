import GaloisForLFunctions.HTGeometry.TorsionCapCount

/-!
# Two states close to one target are close to each other

If two unit vectors both have fidelity at least `1 - δ²` with a common unit target, their own
overlap is at least `1 - 2δ²`: split each along the target, use Pythagoras on the transverse parts,
and bound the transverse pairing by Cauchy--Schwarz.

For the uniform phase ray of a torsion vector this is the geometric input of a torsion cap: the
overlap of two captured rays is the normalized coordinate sum of their relative phases, so a
captured class forces that sum to have modulus at least `(1 - 2δ²)D`.
-/

open scoped ComplexOrder

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Proximity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Two states close to one target are close to each other.** -/
theorem norm_inner_ge_of_common_target {u v y : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hy : ‖y‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h1 : 1 - δ ^ (2 : ℕ) ≤ ‖(inner ℂ y u : ℂ)‖ ^ (2 : ℕ)) (h2 : 1 - δ ^ (2 : ℕ) ≤ ‖(inner ℂ y v : ℂ)‖ ^ (2 : ℕ)) :
    1 - 2 * δ ^ (2 : ℕ) ≤ ‖(inner ℂ u v : ℂ)‖ := by
  set a : ℂ := inner ℂ y u with ha
  set b : ℂ := inner ℂ y v with hb
  set u' : E := u - a • y with hu'
  set v' : E := v - b • y with hv'
  have hyy : (inner ℂ y y : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hy]
    norm_num
  have hyu' : (inner ℂ y u' : ℂ) = 0 := by
    rw [hu', inner_sub_right, inner_smul_right, hyy, mul_one, ha, sub_self]
  have hyv' : (inner ℂ y v' : ℂ) = 0 := by
    rw [hv', inner_sub_right, inner_smul_right, hyy, mul_one, hb, sub_self]
  have hdecu : u = a • y + u' := by
    rw [hu']
    abel
  have hdecv : v = b • y + v' := by
    rw [hv']
    abel
  have hnormu : ‖u‖ ^ (2 : ℕ) = ‖a‖ ^ (2 : ℕ) + ‖u'‖ ^ (2 : ℕ) := by
    have hortho : (inner ℂ (a • y) u' : ℂ) = 0 := by
      rw [inner_smul_left, hyu', mul_zero]
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a • y) u' hortho
    rw [← hdecu, norm_smul, hy, mul_one] at hpy
    rw [pow_two, pow_two, pow_two, hpy]
  have hnormv : ‖v‖ ^ (2 : ℕ) = ‖b‖ ^ (2 : ℕ) + ‖v'‖ ^ (2 : ℕ) := by
    have hortho : (inner ℂ (b • y) v' : ℂ) = 0 := by
      rw [inner_smul_left, hyv', mul_zero]
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b • y) v' hortho
    rw [← hdecv, norm_smul, hy, mul_one] at hpy
    rw [pow_two, pow_two, pow_two, hpy]
  have hu'sq : ‖u'‖ ^ (2 : ℕ) ≤ δ ^ (2 : ℕ) := by
    rw [hu, one_pow] at hnormu
    linarith
  have hv'sq : ‖v'‖ ^ (2 : ℕ) ≤ δ ^ (2 : ℕ) := by
    rw [hv, one_pow] at hnormv
    linarith
  have hu'le : ‖u'‖ ≤ δ := by
    nlinarith [norm_nonneg u']
  have hv'le : ‖v'‖ ≤ δ := by
    nlinarith [norm_nonneg v']
  have hinner : (inner ℂ u v : ℂ) = (starRingEnd ℂ) a * b + (inner ℂ u' v' : ℂ) := by
    have hzero : (inner ℂ u' y : ℂ) = 0 := by
      rw [← inner_conj_symm, hyu', map_zero]
    conv_lhs => rw [hdecu, hdecv]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hyy, hyv',
      hzero]
    ring
  have hcross : ‖(inner ℂ u' v' : ℂ)‖ ≤ δ ^ (2 : ℕ) := by
    calc ‖(inner ℂ u' v' : ℂ)‖ ≤ ‖u'‖ * ‖v'‖ := norm_inner_le_norm u' v'
      _ ≤ δ * δ := mul_le_mul hu'le hv'le (norm_nonneg v') hδ
      _ = δ ^ (2 : ℕ) := by ring
  have hab : (1 : ℝ) - δ ^ (2 : ℕ) ≤ ‖a‖ * ‖b‖ := by
    rcases le_or_gt (1 - δ ^ (2 : ℕ)) 0 with hneg | hpos
    · exact le_trans hneg (by positivity)
    · have hprod : (1 - δ ^ (2 : ℕ)) * (1 - δ ^ (2 : ℕ)) ≤ ‖a‖ ^ (2 : ℕ) * ‖b‖ ^ (2 : ℕ) :=
        mul_le_mul h1 h2 (le_of_lt hpos) (by positivity)
      have hsq : (1 - δ ^ (2 : ℕ)) ^ (2 : ℕ) ≤ (‖a‖ * ‖b‖) ^ (2 : ℕ) := by nlinarith [hprod]
      have hrw1 : (1 : ℝ) - δ ^ (2 : ℕ) = Real.sqrt ((1 - δ ^ (2 : ℕ)) ^ (2 : ℕ)) :=
        (Real.sqrt_sq (le_of_lt hpos)).symm
      have hrw2 : ‖a‖ * ‖b‖ = Real.sqrt ((‖a‖ * ‖b‖) ^ (2 : ℕ)) :=
        (Real.sqrt_sq (by positivity)).symm
      rw [hrw1, hrw2]
      exact Real.sqrt_le_sqrt hsq
  calc (1 : ℝ) - 2 * δ ^ (2 : ℕ) = (1 - δ ^ (2 : ℕ)) - δ ^ (2 : ℕ) := by ring
    _ ≤ ‖a‖ * ‖b‖ - ‖(inner ℂ u' v' : ℂ)‖ := by linarith
    _ = ‖(starRingEnd ℂ) a * b‖ - ‖(inner ℂ u' v' : ℂ)‖ := by
        rw [norm_mul, RCLike.norm_conj]
    _ ≤ ‖(starRingEnd ℂ) a * b + (inner ℂ u' v' : ℂ)‖ := by
        have htri := norm_sub_le ((starRingEnd ℂ) a * b + (inner ℂ u' v' : ℂ))
          (inner ℂ u' v' : ℂ)
        simp only [add_sub_cancel_right] at htri
        linarith
    _ = ‖(inner ℂ u v : ℂ)‖ := by rw [← hinner]

end Proximity

section PhaseRay

variable {D : ℕ}

/-- The uniform phase ray of a unimodular coordinate vector. -/
def phaseRay (q : Fin D → ℂ) : EuclideanSpace ℂ (Fin D) :=
  WithLp.toLp 2 fun a => ((Real.sqrt (D : ℝ))⁻¹ : ℂ) * q a

theorem norm_phaseRay {q : Fin D → ℂ} (hq : ∀ a, ‖q a‖ = 1) (hD : 0 < D) :
    ‖phaseRay q‖ = 1 := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [EuclideanSpace.norm_eq]
  have hterm : ∀ a : Fin D, ‖(phaseRay q).ofLp a‖ ^ (2 : ℕ) = ((D : ℝ))⁻¹ := by
    intro a
    show ‖((Real.sqrt (D : ℝ))⁻¹ : ℂ) * q a‖ ^ (2 : ℕ) = ((D : ℝ))⁻¹
    rw [norm_mul, hq a, mul_one, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (le_of_lt hDR)]
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [mul_inv_cancel₀ (ne_of_gt hDR), Real.sqrt_one]

theorem inner_phaseRay (q r : Fin D → ℂ) (hD : 0 < D) :
    (inner ℂ (phaseRay q) (phaseRay r) : ℂ)
      = ((D : ℝ) : ℂ)⁻¹ * ∑ a, (starRingEnd ℂ) (q a) * r a := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [PiLp.inner_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [RCLike.inner_apply]
  show (((Real.sqrt (D : ℝ))⁻¹ : ℂ) * r a) *
      (starRingEnd ℂ) (((Real.sqrt (D : ℝ))⁻¹ : ℂ) * q a)
      = ((D : ℝ) : ℂ)⁻¹ * ((starRingEnd ℂ) (q a) * r a)
  rw [map_mul, map_inv₀, Complex.conj_ofReal]
  have hsq : ((Real.sqrt (D : ℝ) : ℂ))⁻¹ * ((Real.sqrt (D : ℝ) : ℂ))⁻¹ = ((D : ℝ) : ℂ)⁻¹ := by
    rw [← mul_inv]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hDR)]
  calc (((Real.sqrt (D : ℝ) : ℂ))⁻¹ * r a) *
        (((Real.sqrt (D : ℝ) : ℂ))⁻¹ * (starRingEnd ℂ) (q a))
      = (((Real.sqrt (D : ℝ) : ℂ))⁻¹ * ((Real.sqrt (D : ℝ) : ℂ))⁻¹) *
          ((starRingEnd ℂ) (q a) * r a) := by ring
    _ = ((D : ℝ) : ℂ)⁻¹ * ((starRingEnd ℂ) (q a) * r a) := by rw [hsq]

/-- **The geometric input of a torsion cap.**  Two phase vectors whose rays both have fidelity at
least `1 - δ²` with a common target have relative-phase sum of modulus at least `(1-2δ²)D`. -/
theorem norm_sum_relative_phase_ge {q r : Fin D → ℂ} (hq : ∀ a, ‖q a‖ = 1) (hr : ∀ a, ‖r a‖ = 1)
    (hD : 0 < D) {y : EuclideanSpace ℂ (Fin D)} (hy : ‖y‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (h1 : 1 - δ ^ (2 : ℕ) ≤ ‖(inner ℂ y (phaseRay q) : ℂ)‖ ^ (2 : ℕ))
    (h2 : 1 - δ ^ (2 : ℕ) ≤ ‖(inner ℂ y (phaseRay r) : ℂ)‖ ^ (2 : ℕ)) :
    (1 - 2 * δ ^ (2 : ℕ)) * (D : ℝ) ≤ ‖∑ a, (starRingEnd ℂ) (q a) * r a‖ := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hmain := norm_inner_ge_of_common_target (norm_phaseRay hq hD) (norm_phaseRay hr hD) hy hδ
    h1 h2
  rw [inner_phaseRay q r hD, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (le_of_lt hDR)] at hmain
  rw [← le_div_iff₀ hDR] at *
  calc (1 : ℝ) - 2 * δ ^ (2 : ℕ) ≤ ((D : ℝ))⁻¹ * ‖∑ a, (starRingEnd ℂ) (q a) * r a‖ := hmain
    _ = ‖∑ a, (starRingEnd ℂ) (q a) * r a‖ / (D : ℝ) := by
        rw [inv_mul_eq_div]

end PhaseRay

end

end GaloisForLFunctions.HTGeometry
