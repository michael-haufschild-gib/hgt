import GaloisForLFunctions.ArithmeticPositiveDuality.TwoQuartetEndpointInterpolation
import GaloisForLFunctions.ArithmeticPositiveDuality.EndpointNormalizationForcesANegativeQuartetTrace
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem

/-!
# Two off-line quartets preserve both endpoint values and derivatives

Four critical-line donor pairs can be replaced by two distinct quartets on
the lines `1/4` and `3/4`. The monic rational multiplier has value one and
derivative zero at both real endpoints. A single off-line quartet cannot
preserve this jet.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- Off-line target whose endpoint parameter is `u`. -/
def quartetParameterTarget (u : ℝ) : ℂ :=
  3 / 4 + (Real.sqrt (u - 5 / 16) : ℂ) * I

/-- Two quartet relocations sharing one endpoint normalization. -/
def twoQuartetFactor (u v γ₁ γ₂ γ₃ γ₄ : ℝ) (s : ℂ) : ℂ :=
  zeroRelocationFactor (quartetParameterTarget u) γ₁ γ₂ s *
    zeroRelocationFactor (quartetParameterTarget v) γ₃ γ₄ s

@[simp] theorem quartetParameterTarget_re (u : ℝ) :
    (quartetParameterTarget u).re = 3 / 4 := by
  norm_num [quartetParameterTarget]

@[simp] theorem quartetParameterTarget_im (u : ℝ) :
    (quartetParameterTarget u).im = Real.sqrt (u - 5 / 16) := by
  norm_num [quartetParameterTarget]

private theorem numerator_centered (η : ℝ) (s : ℂ) :
    zeroRelocationNum (3 / 4 + (η : ℂ) * I) s =
      ((s - 1 / 2) ^ 2 + (η : ℂ) ^ 2 - 1 / 16) ^ 2 + (η : ℂ) ^ 2 / 4 := by
  simp only [zeroRelocationNum, map_add, map_mul, map_div₀, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I]
  apply Complex.ext <;>
    norm_num [pow_two, Complex.mul_re, Complex.mul_im] <;> ring

private theorem numerator_parameter {u : ℝ} (hu : 5 / 16 ≤ u) (s : ℂ) :
    zeroRelocationNum (quartetParameterTarget u) s =
      ((s - 1 / 2) ^ 2 + (u : ℂ) - 3 / 8) ^ 2 + ((u : ℂ) - 5 / 16) / 4 := by
  rw [quartetParameterTarget, numerator_centered, ← Complex.ofReal_pow,
    Real.sq_sqrt (sub_nonneg.mpr hu)]
  push_cast
  ring

private theorem numerator_at_one {u : ℝ} (hu : 5 / 16 ≤ u) :
    zeroRelocationNum (quartetParameterTarget u) 1 = (quartetEndpointMass u : ℂ) := by
  rw [numerator_parameter hu]
  unfold quartetEndpointMass
  push_cast
  ring

private theorem numerator_derivative {u : ℝ} (hu : 5 / 16 ≤ u) :
    HasDerivAt (zeroRelocationNum (quartetParameterTarget u)) ((2 * (u - 1 / 8) : ℝ) : ℂ) 1 := by
  have hf := (((((hasDerivAt_id (1 : ℂ)).sub_const (1 / 2)).pow 2).add_const
    (u : ℂ)).sub_const (3 / 8)).pow 2
  have hg := hf.add_const (((u : ℂ) - 5 / 16) / 4)
  refine (hg.congr_of_eventuallyEq (Eventually.of_forall
    (fun s => numerator_parameter hu s))).congr_deriv ?_
  push_cast
  dsimp only [id, Pi.sub_apply, Pi.pow_apply, Pi.add_apply]
  ring

private theorem denominator_centered (γ₁ γ₂ : ℝ) (s : ℂ) :
    zeroRelocationDen γ₁ γ₂ s =
      ((s - 1 / 2) ^ 2 + (γ₁ : ℂ) ^ 2) * ((s - 1 / 2) ^ 2 + (γ₂ : ℂ) ^ 2) := by
  apply Complex.ext <;>
    norm_num [zeroRelocationDen, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

private theorem denominator_at_one (γ₁ γ₂ : ℝ) :
    zeroRelocationDen γ₁ γ₂ 1 = (((γ₁ ^ 2 + 1 / 4) * (γ₂ ^ 2 + 1 / 4) : ℝ) : ℂ) := by
  rw [denominator_centered]
  push_cast
  ring

private theorem denominator_derivative (γ₁ γ₂ : ℝ) :
    HasDerivAt (zeroRelocationDen γ₁ γ₂)
      (((γ₁ ^ 2 + 1 / 4) + (γ₂ ^ 2 + 1 / 4) : ℝ) : ℂ) 1 := by
  have hf := ((((hasDerivAt_id (1 : ℂ)).sub_const (1 / 2)).pow 2).add_const
    ((γ₁ : ℂ) ^ 2)).mul
    ((((hasDerivAt_id (1 : ℂ)).sub_const (1 / 2)).pow 2).add_const ((γ₂ : ℂ) ^ 2))
  refine (hf.congr_of_eventuallyEq (Eventually.of_forall
    (fun s => denominator_centered γ₁ γ₂ s))).congr_deriv ?_
  push_cast
  dsimp only [id, Pi.sub_apply, Pi.pow_apply, Pi.add_apply]
  ring

theorem twoQuartetFactor_one_sub (u v γ₁ γ₂ γ₃ γ₄ : ℝ) (s : ℂ) :
    twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ (1 - s) = twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ s := by
  simp only [twoQuartetFactor, zeroRelocationFactor_one_sub]

theorem twoQuartetFactor_conj (u v γ₁ γ₂ γ₃ γ₄ : ℝ) (s : ℂ) :
    twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ (starRingEnd ℂ s) =
      starRingEnd ℂ (twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ s) := by
  simp only [twoQuartetFactor, zeroRelocationFactor_conj, map_mul]

private theorem factor_jet {u v γ₁ γ₂ γ₃ γ₄ : ℝ}
    (hu : 5 / 16 < u) (hv : 5 / 16 < v)
    (hmass : quartetEndpointMass u * quartetEndpointMass v =
      (γ₁ ^ 2 + 1 / 4) * (γ₂ ^ 2 + 1 / 4) * (γ₃ ^ 2 + 1 / 4) * (γ₄ ^ 2 + 1 / 4))
    (hslope : quartetEndpointSlope u + quartetEndpointSlope v =
      1 / (γ₁ ^ 2 + 1 / 4) + 1 / (γ₂ ^ 2 + 1 / 4) +
        1 / (γ₃ ^ 2 + 1 / 4) + 1 / (γ₄ ^ 2 + 1 / 4)) :
    twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ 1 = 1 ∧
      HasDerivAt (twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄) 0 1 := by
  let N := fun s => zeroRelocationNum (quartetParameterTarget u) s *
    zeroRelocationNum (quartetParameterTarget v) s
  let D := fun s => zeroRelocationDen γ₁ γ₂ s * zeroRelocationDen γ₃ γ₄ s
  have hD0 : D 1 ≠ 0 := mul_ne_zero
    (zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ (by norm_num))
    (zeroRelocationDen_ne_zero_of_re_ne_half γ₃ γ₄ (by norm_num))
  have hN0 : N 1 = D 1 := by
    dsimp only [N, D]
    rw [numerator_at_one hu.le, numerator_at_one hv.le,
      denominator_at_one, denominator_at_one, ← Complex.ofReal_mul, hmass]
    push_cast
    ring
  have hmu : quartetEndpointMass u ≠ 0 := by
    unfold quartetEndpointMass
    nlinarith only [hu, sq_nonneg (u - 5 / 16)]
  have hmv : quartetEndpointMass v ≠ 0 := by
    unfold quartetEndpointMass
    nlinarith only [hv, sq_nonneg (v - 5 / 16)]
  have he : 2 * (u - 1 / 8) * quartetEndpointMass v +
      quartetEndpointMass u * (2 * (v - 1 / 8)) =
      ((γ₁ ^ 2 + 1 / 4) + (γ₂ ^ 2 + 1 / 4)) *
        ((γ₃ ^ 2 + 1 / 4) * (γ₄ ^ 2 + 1 / 4)) +
      ((γ₁ ^ 2 + 1 / 4) * (γ₂ ^ 2 + 1 / 4)) *
        ((γ₃ ^ 2 + 1 / 4) + (γ₄ ^ 2 + 1 / 4)) := by
    calc
      _ = (quartetEndpointMass u * quartetEndpointMass v) *
          (quartetEndpointSlope u + quartetEndpointSlope v) := by
        unfold quartetEndpointSlope
        field_simp [hmu, hmv]
      _ = _ := by
        rw [hmass, hslope]
        have h₁ : γ₁ ^ 2 + 1 / 4 ≠ 0 := by positivity
        have h₂ : γ₂ ^ 2 + 1 / 4 ≠ 0 := by positivity
        have h₃ : γ₃ ^ 2 + 1 / 4 ≠ 0 := by positivity
        have h₄ : γ₄ ^ 2 + 1 / 4 ≠ 0 := by positivity
        field_simp [h₁, h₂, h₃, h₄]
        ring
  have hN := (numerator_derivative hu.le).mul (numerator_derivative hv.le)
  have hD := (denominator_derivative γ₁ γ₂).mul (denominator_derivative γ₃ γ₄)
  rw [numerator_at_one hu.le, numerator_at_one hv.le] at hN
  rw [denominator_at_one, denominator_at_one] at hD
  have heC := congrArg Complex.ofReal he
  push_cast at heC hN hD
  rw [heC] at hN
  have hquot := hN.div hD hD0
  have hfun : twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ = fun s => N s / D s := by
    funext s
    exact div_mul_div_comm _ _ _ _
  constructor
  · rw [hfun]
    change N 1 / D 1 = 1
    rw [hN0, div_self hD0]
  · rw [hfun]
    refine hquot.congr_deriv ?_
    change (_ * D 1 - N 1 * _) / D 1 ^ 2 = (0 : ℂ)
    rw [hN0]
    ring

/-- Any four donor pairs above height one admit a two-quartet multiplier preserving the endpoint jet. -/
theorem exists_two_quartet_factor_jet {γ₁ γ₂ γ₃ γ₄ : ℝ}
    (h₁ : 1 < γ₁) (h₂ : 1 < γ₂) (h₃ : 1 < γ₃) (h₄ : 1 < γ₄) :
    ∃ u v : ℝ, 5 / 16 < v ∧ v < u ∧
      twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ 1 = 1 ∧
      HasDerivAt (twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄) 0 1 := by
  obtain ⟨u, v, hv, hvu, hm, hs⟩ := exists_two_quartet_endpoint_parameters
    (show 1 < γ₁ ^ 2 + 1 / 4 by nlinarith only [h₁])
    (show 1 < γ₂ ^ 2 + 1 / 4 by nlinarith only [h₂])
    (show 1 < γ₃ ^ 2 + 1 / 4 by nlinarith only [h₃])
    (show 1 < γ₄ ^ 2 + 1 / 4 by nlinarith only [h₄])
  exact ⟨u, v, hv, hvu, factor_jet (hv.trans hvu) hv hm hs⟩

/-- Reflection transfers the preserved jet to zero. -/
theorem twoQuartetFactor_jet_zero {u v γ₁ γ₂ γ₃ γ₄ : ℝ}
    (hval : twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ 1 = 1)
    (hjet : HasDerivAt (twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄) 0 1) :
    twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ 0 = 1 ∧
      HasDerivAt (twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄) 0 0 := by
  constructor
  · have he := twoQuartetFactor_one_sub u v γ₁ γ₂ γ₃ γ₄ 0
    simp only [sub_zero] at he
    exact he.symm.trans hval
  · have hneg : HasDerivAt (fun s : ℂ => 1 - s) (-1) 0 := by
      exact (hasDerivAt_id (0 : ℂ)).const_sub 1
    have hjet' : HasDerivAt (twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄) 0 (1 - 0) := by
      simpa only [sub_zero] using hjet
    simpa only [Function.comp_def, zero_mul, twoQuartetFactor_one_sub] using hjet'.comp 0 hneg

/-- The two prescribed conjugate pairs are the entire right-hand zero set of the multiplier. -/
theorem twoQuartetFactor_eq_zero_iff {s : ℂ} (hs : 1 / 2 < s.re)
    (u v γ₁ γ₂ γ₃ γ₄ : ℝ) :
    twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ s = 0 ↔
      s = quartetParameterTarget u ∨ s = starRingEnd ℂ (quartetParameterTarget u) ∨
      s = quartetParameterTarget v ∨ s = starRingEnd ℂ (quartetParameterTarget v) := by
  rw [twoQuartetFactor, mul_eq_zero,
    zeroRelocationFactor_eq_zero_iff_of_half_lt_re (by norm_num) γ₁ γ₂ hs,
    zeroRelocationFactor_eq_zero_iff_of_half_lt_re (by norm_num) γ₃ γ₄ hs, or_assoc]

/-- Monicity retains the vertical normalization at every abscissa. -/
theorem tendsto_twoQuartetFactor_vertical (u v γ₁ γ₂ γ₃ γ₄ σ : ℝ) :
    Tendsto (fun t : ℝ => twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ ((σ : ℂ) + (t : ℂ) * I))
      atTop (𝓝 1) := by
  simpa only [one_mul, twoQuartetFactor] using
    (tendsto_zeroRelocationFactor_vertical_atTop (quartetParameterTarget u) γ₁ γ₂ σ).mul
      (tendsto_zeroRelocationFactor_vertical_atTop (quartetParameterTarget v) γ₃ γ₄ σ)

/-- Four distinct actual critical-line donor pairs exist without a simplicity assumption. -/
theorem exists_four_critical_donor_ordinates :
    ∃ γ₁ γ₂ γ₃ γ₄ : ℝ, 1 < γ₁ ∧ γ₁ < γ₂ ∧ γ₂ < γ₃ ∧ γ₃ < γ₄ ∧
      riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0 ∧
      riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0 ∧
      riemannZeta (1 / 2 + (γ₃ : ℂ) * I) = 0 ∧
      riemannZeta (1 / 2 + (γ₄ : ℂ) * I) = 0 := by
  obtain ⟨T₀, _, hT⟩ := RHTower.exists_riemannZeta_line_zero_dyadic
  let T := max T₀ 2
  have hT₂ : (2 : ℝ) ≤ T := le_max_right _ _
  have hT₀T : T₀ ≤ T := le_max_left _ _
  obtain ⟨γ₁, hγ₁, hz₁⟩ := hT T hT₀T
  obtain ⟨γ₂, hγ₂, hz₂⟩ := hT (4 * T) (by linarith only [hT₀T, hT₂])
  obtain ⟨γ₃, hγ₃, hz₃⟩ := hT (16 * T) (by linarith only [hT₀T, hT₂])
  obtain ⟨γ₄, hγ₄, hz₄⟩ := hT (64 * T) (by linarith only [hT₀T, hT₂])
  refine ⟨γ₁, γ₂, γ₃, γ₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hγ₁.1, hT₂]
  · linarith only [hγ₁.2, hγ₂.1, hT₂]
  · linarith only [hγ₂.2, hγ₃.1, hT₂]
  · linarith only [hγ₃.2, hγ₄.1, hT₂]
  · simpa [RHTower.linePt] using hz₁
  · simpa [RHTower.linePt] using hz₂
  · simpa [RHTower.linePt] using hz₃
  · simpa [RHTower.linePt] using hz₄

/-- Actual donor zeros permit two off-line quartets with unchanged endpoint values and derivatives. -/
theorem exists_actual_two_quartet_endpoint_jet :
    ∃ γ₁ γ₂ γ₃ γ₄ u v : ℝ,
      1 < γ₁ ∧ γ₁ < γ₂ ∧ γ₂ < γ₃ ∧ γ₃ < γ₄ ∧
      riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0 ∧
      riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0 ∧
      riemannZeta (1 / 2 + (γ₃ : ℂ) * I) = 0 ∧
      riemannZeta (1 / 2 + (γ₄ : ℂ) * I) = 0 ∧
      5 / 16 < v ∧ v < u ∧
      twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ 0 = 1 ∧
      twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ 1 = 1 ∧
      HasDerivAt (twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄) 0 0 ∧
      HasDerivAt (twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄) 0 1 := by
  obtain ⟨γ₁, γ₂, γ₃, γ₄, h₁, h₁₂, h₂₃, h₃₄, hz₁, hz₂, hz₃, hz₄⟩ :=
    exists_four_critical_donor_ordinates
  obtain ⟨u, v, hv, hvu, hval, hjet⟩ := exists_two_quartet_factor_jet h₁
    (h₁.trans h₁₂) ((h₁.trans h₁₂).trans h₂₃) (((h₁.trans h₁₂).trans h₂₃).trans h₃₄)
  obtain ⟨hval0, hjet0⟩ := twoQuartetFactor_jet_zero hval hjet
  exact ⟨γ₁, γ₂, γ₃, γ₄, u, v, h₁, h₁₂, h₂₃, h₃₄, hz₁, hz₂, hz₃, hz₄,
    hv, hvu, hval0, hval, hjet0, hjet⟩

end GaloisForLFunctions.ArithmeticPositiveDuality

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.exists_two_quartet_factor_jet
#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.exists_actual_two_quartet_endpoint_jet
#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.tendsto_twoQuartetFactor_vertical
