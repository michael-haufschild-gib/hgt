import GaloisForLFunctions.BlackHoleRingdown.TheVerticalBoundsOfTheEisensteinTail
import GaloisForLFunctions.BlackHoleRingdown.TheInverseXiContour
import GaloisForLFunctions.RHTower.EisensteinLineZeroMean
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralSourceReflection

/-!
# The normalized Eisenstein function

`E(z, ½ + u)` is written without junk values at the poles of the completed zeta function:

`E(u; x, Y) = Y^{½+u} + ψ(u) Y^{½-u} + χ(u) T(u; x, Y)`,

where `ψ(u) = ((1+2u)/(2u-1)) ξ(2u)/ξ(1+2u)` is the scattering coefficient `φ(½+u)`, the factor
`χ(u) = (1+2u)(2u)/ξ(1+2u)`, and `T` is the Whittaker tail. Off the real axis this is the completed
Fourier model divided by `Λ(1+2u)`. It is meromorphic with poles only at zeros of `ξ(1+2u)` and at
`u = ½`, so it stays regular at `u = 0` and `u = -½`.

On the line `u = iξ` this module proves the eigen-equation `Δ E = -(ξ²+¼) E`, modular invariance, the
constant term, `|ψ(iξ)| = 1`, measurability, and Gaussian-dominated bounds for every jet that a wave
packet needs.
-/

open Complex MeasureTheory Set Filter Topology
open scoped UpperHalfPlane MatrixGroups

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-! ### Definitions -/

/-- The two-sided Whittaker tail and its jets. -/
def eisTail (u : ℂ) (x Y : ℝ) : ℂ := weightedTail u false x Y + weightedTail u true x Y
def eisTailX (u : ℂ) (x Y : ℝ) : ℂ := weightedTailX u false x Y + weightedTailX u true x Y
def eisTailXX (u : ℂ) (x Y : ℝ) : ℂ := weightedTailXX u false x Y + weightedTailXX u true x Y
def eisTailY (u : ℂ) (x Y : ℝ) : ℂ := weightedTailY u false x Y + weightedTailY u true x Y
def eisTailYY (u : ℂ) (x Y : ℝ) : ℂ := weightedTailYY u false x Y + weightedTailYY u true x Y

/-- The scattering coefficient `φ(½+u) = ((1+2u)/(2u-1)) ξ(2u)/ξ(1+2u)`. -/
def scatteringPhase (u : ℂ) : ℂ := (1 + 2 * u) / (2 * u - 1) * (xi (2 * u) / xi (1 + 2 * u))

/-- The weight `(1+2u)(2u)/ξ(1+2u)` of the tail. -/
def tailWeight (u : ℂ) : ℂ := (1 + 2 * u) * (2 * u) / xi (1 + 2 * u)

/-- The normalized Eisenstein function `E(x + iY, ½ + u)`. -/
def normalizedEisenstein (u : ℂ) (x Y : ℝ) : ℂ :=
  (Y : ℂ) ^ (1 / 2 + u) + scatteringPhase u * (Y : ℂ) ^ (1 / 2 - u) + tailWeight u * eisTail u x Y

def eisensteinX (u : ℂ) (x Y : ℝ) : ℂ := tailWeight u * eisTailX u x Y
def eisensteinXX (u : ℂ) (x Y : ℝ) : ℂ := tailWeight u * eisTailXX u x Y

def eisensteinY (u : ℂ) (x Y : ℝ) : ℂ :=
  (1 / 2 + u) * (Y : ℂ) ^ (1 / 2 + u - 1) + scatteringPhase u * ((1 / 2 - u) * (Y : ℂ) ^ (1 / 2 - u - 1)) +
    tailWeight u * eisTailY u x Y

def eisensteinYY (u : ℂ) (x Y : ℝ) : ℂ :=
  (1 / 2 + u) * ((1 / 2 + u - 1) * (Y : ℂ) ^ (1 / 2 + u - 1 - 1)) +
    scatteringPhase u * ((1 / 2 - u) * ((1 / 2 - u - 1) * (Y : ℂ) ^ (1 / 2 - u - 1 - 1))) +
    tailWeight u * eisTailYY u x Y

/-! ### Jets and the eigen-equation -/

section Jets

variable (u : ℂ) (x : ℝ) {Y : ℝ}

theorem hasDerivAt_eisenstein_x (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => normalizedEisenstein u q Y) (eisensteinX u x Y) x := by
  have h := (((hasDerivAt_weightedTail_x u false x hY).add
    (hasDerivAt_weightedTail_x u true x hY)).const_mul (tailWeight u)).const_add
    ((Y : ℂ) ^ (1 / 2 + u) + scatteringPhase u * (Y : ℂ) ^ (1 / 2 - u))
  exact h

theorem hasDerivAt_eisensteinX_x (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => eisensteinX u q Y) (eisensteinXX u x Y) x :=
  ((hasDerivAt_weightedTailX_x u false x hY).add
    (hasDerivAt_weightedTailX_x u true x hY)).const_mul (tailWeight u)

theorem hasDerivAt_eisenstein_y (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => normalizedEisenstein u x q) (eisensteinY u x Y) Y := by
  have h1 := hasDerivAt_ofReal_cpow_const_thetaCuspHawkingBMEisensteinLineEigenEquation (1 / 2 + u) hY
  have h2 := (hasDerivAt_ofReal_cpow_const_thetaCuspHawkingBMEisensteinLineEigenEquation
    (1 / 2 - u) hY).const_mul (scatteringPhase u)
  have h3 := ((hasDerivAt_weightedTail_y u false x hY).add
    (hasDerivAt_weightedTail_y u true x hY)).const_mul (tailWeight u)
  exact (h1.add h2).add h3

theorem hasDerivAt_eisensteinY_y (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => eisensteinY u x q) (eisensteinYY u x Y) Y := by
  have h1 := (hasDerivAt_ofReal_cpow_const_thetaCuspHawkingBMEisensteinLineEigenEquation
    (1 / 2 + u - 1) hY).const_mul (1 / 2 + u)
  have h2 := ((hasDerivAt_ofReal_cpow_const_thetaCuspHawkingBMEisensteinLineEigenEquation
    (1 / 2 - u - 1) hY).const_mul (1 / 2 - u)).const_mul (scatteringPhase u)
  have h3 := ((hasDerivAt_weightedTailY_y u false x hY).add
    (hasDerivAt_weightedTailY_y u true x hY)).const_mul (tailWeight u)
  exact (h1.add h2).add h3

theorem sq_mul_cpow_sub_two (w : ℂ) (hY : 0 < Y) :
    (Y : ℂ) ^ 2 * (Y : ℂ) ^ (w - 1 - 1) = (Y : ℂ) ^ w := by
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hsplit : w = (w - 1 - 1) + 2 := by ring
  conv_rhs => rw [hsplit, Complex.cpow_add _ _ hYC]
  rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  ring

/-- **The eigen-equation** `Y²(∂ₓ² + ∂_Y²) E = (u² - ¼) E`. -/
theorem eisenstein_eigen (hY : 0 < Y) :
    (Y : ℂ) ^ 2 * (eisensteinXX u x Y + eisensteinYY u x Y) =
      (u ^ 2 - 1 / 4) * normalizedEisenstein u x Y := by
  have h1 := sq_mul_cpow_sub_two (1 / 2 + u) hY
  have h2 := sq_mul_cpow_sub_two (1 / 2 - u) hY
  have h3 := weightedTail_eigen u false x hY
  have h4 := weightedTail_eigen u true x hY
  simp only [eisensteinXX, eisensteinYY, normalizedEisenstein, eisTailXX, eisTailYY, eisTail]
  linear_combination (1 / 2 + u) * (1 / 2 + u - 1) * h1 +
    scatteringPhase u * (1 / 2 - u) * (1 / 2 - u - 1) * h2 + tailWeight u * h3 + tailWeight u * h4

end Jets

/-! ### The completed model -/

theorem constantPart_scalar_eq (u : ℂ) (Y : ℝ) :
    d4BMCompletedEisensteinCuspConstantPart .scalar u Y =
      reflectedCompletedLambda (2 * u) * (Y : ℂ) ^ (1 / 2 - u) +
        reflectedCompletedLambda (1 + 2 * u) * (Y : ℂ) ^ (1 / 2 + u) := by
  simp only [d4BMCompletedEisensteinCuspConstantPart, d4BMCompletedEisensteinCuspConstantTerm,
    d4BMCompletedEisensteinCuspConstantCoefficient, d4BMCompletedEisensteinCuspConstantMaassFactor,
    d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign]
  simp only [if_true, if_false, Bool.false_eq_true, mul_one]
  push_cast
  rw [show (1 / 2 + -1 * u : ℂ) = 1 / 2 - u by ring, show (1 / 2 + 1 * u : ℂ) = 1 / 2 + u by ring]

theorem xi_eq_reflectedCompletedLambda {s : ℂ} (him : s.im ≠ 0) :
    xi s = s * (s - 1) / 2 * reflectedCompletedLambda s := by
  rw [reflectedCompletedLambda]
  exact xi_eq_factor him

theorem lineModel_eq (u : ℂ) (x Y : ℝ) :
    lineModel u x Y = reflectedCompletedLambda (2 * u) * (Y : ℂ) ^ (1 / 2 - u) +
      reflectedCompletedLambda (1 + 2 * u) * (Y : ℂ) ^ (1 / 2 + u) + 2 * eisTail u x Y := by
  rw [lineModel, constantPart_scalar_eq, eisTail]

/-- **Off the real axis, `E` is the completed Fourier model divided by `Λ(1+2u)`.** -/
theorem normalizedEisenstein_eq_lineModel_div {u : ℂ} (him : u.im ≠ 0)
    (h0 : xi (1 + 2 * u) ≠ 0) (x Y : ℝ) :
    normalizedEisenstein u x Y = lineModel u x Y / reflectedCompletedLambda (1 + 2 * u) := by
  have him1 : (1 + 2 * u).im ≠ 0 := by simpa using him
  have him2 : (2 * u).im ≠ 0 := by simpa using him
  have hu0 : u ≠ 0 := fun h => him (by rw [h]; simp)
  have h2u : (2 : ℂ) * u ≠ 0 := mul_ne_zero two_ne_zero hu0
  have h1 : (1 : ℂ) + 2 * u ≠ 0 := fun h => him1 (by rw [h]; simp)
  have h2 : (2 : ℂ) * u - 1 ≠ 0 := fun h => by
    have h' : (2 : ℂ) * u = 1 := sub_eq_zero.mp h
    exact him2 (by rw [h']; simp)
  have hx1 := xi_eq_reflectedCompletedLambda him1
  have hx2 := xi_eq_reflectedCompletedLambda him2
  have hsub : (1 : ℂ) + 2 * u - 1 = 2 * u := by ring
  rw [hsub] at hx1
  set L₁ := reflectedCompletedLambda (1 + 2 * u) with hL₁
  set L₂ := reflectedCompletedLambda (2 * u) with hL₂
  have hL₁ne : L₁ ≠ 0 := by
    intro h
    rw [hx1, h, mul_zero] at h0
    exact h0 rfl
  rw [normalizedEisenstein, lineModel_eq, scatteringPhase, tailWeight, hx1, hx2]
  field_simp
  ring

/-- The constant term of `E`. -/
theorem setIntegral_normalizedEisenstein (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    ∫ x in Ioc (0 : ℝ) 1, normalizedEisenstein u x Y =
      (Y : ℂ) ^ (1 / 2 + u) + scatteringPhase u * (Y : ℂ) ^ (1 / 2 - u) := by
  have hT : ∀ negative : Bool, IntegrableOn (fun x => weightedTail u negative x Y) (Ioc 0 1) := by
    intro negative
    simp_rw [weightedTail_eq_signedSqrtWhittakerTail]
    exact (continuous_signedSqrtWhittakerTail_x negative hY u).integrableOn_Ioc
  have hZ : ∀ negative : Bool, ∫ x in Ioc (0 : ℝ) 1, weightedTail u negative x Y = 0 := by
    intro negative
    simp_rw [weightedTail_eq_signedSqrtWhittakerTail]
    exact setIntegral_Ioc_signedSqrtWhittakerTail negative hY u
  have hfin : volume (Ioc (0 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hconst : IntegrableOn (fun _ : ℝ => (Y : ℂ) ^ (1 / 2 + u) +
      scatteringPhase u * (Y : ℂ) ^ (1 / 2 - u)) (Ioc 0 1) := integrableOn_const hfin
  have hsum : IntegrableOn (fun x => eisTail u x Y) (Ioc 0 1) := (hT false).add (hT true)
  have hval : (∫ x in Ioc (0 : ℝ) 1, eisTail u x Y) = 0 := by
    have : (∫ x in Ioc (0 : ℝ) 1, eisTail u x Y) =
        (∫ x in Ioc (0 : ℝ) 1, weightedTail u false x Y) +
          ∫ x in Ioc (0 : ℝ) 1, weightedTail u true x Y := integral_add (hT false) (hT true)
    rw [this, hZ, hZ, add_zero]
  have hsplit : (∫ x in Ioc (0 : ℝ) 1, normalizedEisenstein u x Y) =
      (∫ _x in Ioc (0 : ℝ) 1, (Y : ℂ) ^ (1 / 2 + u) + scatteringPhase u * (Y : ℂ) ^ (1 / 2 - u)) +
        ∫ x in Ioc (0 : ℝ) 1, tailWeight u * eisTail u x Y :=
    integral_add hconst (hsum.const_mul _)
  rw [hsplit, integral_const_mul, hval, mul_zero, add_zero, setIntegral_const]
  simp [Measure.real, Real.volume_Ioc]

/-! ### Modular invariance on the line -/

theorem reflectedCompletedLambda_eq_completed {s : ℂ} (hs : s.im ≠ 0) :
    reflectedCompletedLambda s = completedRiemannZeta s := by
  have hs0 : s ≠ 0 := fun h => hs (by rw [h]; rfl)
  have hG : Complex.Gammaℝ s ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    refine mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_ne_zero))) ?_
    refine Complex.Gamma_ne_zero fun m hm => hs ?_
    have := congrArg Complex.im hm
    simp at this
    linarith
  rw [reflectedCompletedLambda, riemannZeta_def_of_ne_zero hs0]
  field_simp

/-- The completed Fourier model is even in the parameter. -/
theorem cuspLeg_neg {u : ℂ} (him : u.im ≠ 0) (x Y : ℝ) :
    d4BMCompletedEisensteinCuspLeg .scalar (-u) x Y = d4BMCompletedEisensteinCuspLeg .scalar u x Y := by
  have h1 : (2 * u).im ≠ 0 := by simpa using him
  have h2 : (1 + 2 * u).im ≠ 0 := by simpa using him
  have h3 : (2 * -u).im ≠ 0 := by simpa using him
  have h4 : (1 + 2 * -u).im ≠ 0 := by simpa using him
  have hL1 : reflectedCompletedLambda (2 * -u) = reflectedCompletedLambda (1 + 2 * u) := by
    rw [reflectedCompletedLambda_eq_completed h3, reflectedCompletedLambda_eq_completed h2,
      ← completedRiemannZeta_one_sub]
    congr 1
    ring
  have hL2 : reflectedCompletedLambda (1 + 2 * -u) = reflectedCompletedLambda (2 * u) := by
    rw [reflectedCompletedLambda_eq_completed h4, reflectedCompletedLambda_eq_completed h1,
      ← completedRiemannZeta_one_sub]
    congr 1
    ring
  unfold d4BMCompletedEisensteinCuspLeg
  rw [constantPart_scalar_eq, constantPart_scalar_eq, hL1, hL2]
  have htail : d4BMCompletedEisensteinCuspTailPart .scalar (-u) x Y =
      d4BMCompletedEisensteinCuspTailPart .scalar u x Y := by
    unfold d4BMCompletedEisensteinCuspTailPart
    simp only
    rw [d4BMCompletedEisensteinFullSignedZeroWord_neg]
  rw [htail]
  rw [show (1 / 2 - -u : ℂ) = 1 / 2 + u by ring, show (1 / 2 + -u : ℂ) = 1 / 2 - u by ring]
  ring

theorem xi_line_ne_zero (ξ : ℝ) : xi (1 + 2 * ((ξ : ℂ) * I)) ≠ 0 :=
  xi_ne_zero_of_one_le_re (by simp)

/-- **Modular invariance.**  For `ξ ≠ 0`, the function `E(·, ½ + iξ)` is `SL₂(ℤ)`-invariant. -/
theorem normalizedEisenstein_smul {ξ : ℝ} (hξ : ξ ≠ 0) (γ : SL(2, ℤ)) (z : ℍ) :
    normalizedEisenstein ((ξ : ℂ) * I) (γ • z : ℍ).re (γ • z : ℍ).im =
      normalizedEisenstein ((ξ : ℂ) * I) z.re z.im := by
  have him : ((ξ : ℂ) * I).im ≠ 0 := by simpa using hξ
  rw [normalizedEisenstein_eq_lineModel_div him (xi_line_ne_zero ξ),
    normalizedEisenstein_eq_lineModel_div him (xi_line_ne_zero ξ), lineModel_eq_cuspLeg,
    lineModel_eq_cuspLeg]
  congr 1
  rcases lt_or_gt_of_ne hξ with h | h
  · have hpos : 0 < -ξ := by linarith
    have hinv := eisensteinLineModel_I_mul_smul hpos γ z
    simp only [eisensteinLineModel] at hinv
    have hneg : (((-ξ : ℝ) : ℂ) * I) = -((ξ : ℂ) * I) := by
      push_cast
      ring
    rw [hneg, cuspLeg_neg him, cuspLeg_neg him] at hinv
    exact hinv
  · have hinv := eisensteinLineModel_I_mul_smul h γ z
    simpa only [eisensteinLineModel] using hinv

/-! ### Bounds on the line -/

/-- On the critical line the scattering coefficient is unimodular. -/
theorem norm_scatteringPhase_line (ξ : ℝ) : ‖scatteringPhase ((ξ : ℂ) * I)‖ = 1 := by
  set s : ℂ := 1 + 2 * ((ξ : ℂ) * I) with hs
  have hconj : 2 * ((ξ : ℂ) * I) = 1 - (starRingEnd ℂ) s := by
    rw [hs]
    simp only [map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  have hxi : ‖xi (2 * ((ξ : ℂ) * I))‖ = ‖xi s‖ := by
    rw [hconj, xi_one_sub, xi_conj, RCLike.norm_conj]
  have hne : xi s ≠ 0 := xi_line_ne_zero ξ
  have hden : ‖2 * ((ξ : ℂ) * I) - 1‖ = ‖1 + 2 * ((ξ : ℂ) * I)‖ := by
    have h : 2 * ((ξ : ℂ) * I) - 1 = -(starRingEnd ℂ) s := by
      rw [hconj]
      ring
    rw [h, norm_neg, RCLike.norm_conj]
  have hdne : ‖1 + 2 * ((ξ : ℂ) * I)‖ ≠ 0 := by
    have : (1 + 2 * ((ξ : ℂ) * I)).re = 1 := by simp
    intro h0
    rw [norm_eq_zero] at h0
    rw [h0] at this
    simp at this
  have hdne' : ‖s‖ ≠ 0 := by
    rw [hs]
    exact hdne
  rw [scatteringPhase, norm_mul, norm_div, norm_div, hden, hxi, ← hs, div_self hdne',
    div_self (norm_ne_zero_iff.mpr hne), one_mul]

/-- `1/ξ` on the line `Re s = 1` is dominated by any Gaussian. -/
theorem exists_norm_inv_xi_line_le_gaussian {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, ‖(xi (1 + 2 * ((ξ : ℂ) * I)))⁻¹‖ ≤ C * Real.exp (c * ξ ^ 2) := by
  obtain ⟨C₂, N₂, hC₂, hxi⟩ := exists_norm_inv_xi_le 1 1
  obtain ⟨K, hK, hzeta⟩ := exists_norm_inv_zeta_one_line
  obtain ⟨C₄, hC₄, hcmp⟩ := exists_one_add_pow_mul_exp_le_gaussian (N₂ + 11)
    (b := Real.pi / 4) (c := c / 4) (by positivity)
  have hcont : Continuous fun ξ : ℝ => (xi (1 + 2 * ((ξ : ℂ) * I)))⁻¹ := by
    refine Continuous.inv₀ ?_ xi_line_ne_zero
    exact xi_differentiable.continuous.comp (by fun_prop)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨C₂ * K * C₄ + max M 0, by positivity, fun ξ => ?_⟩
  have hE : 1 ≤ Real.exp (c * ξ ^ 2) := Real.one_le_exp (by positivity)
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  rcases le_or_gt |ξ| 1 with h | h
  · have h1 := (hM ξ (abs_le.mp h)).trans (le_max_left M 0)
    have h2 : 0 ≤ C₂ * K * C₄ * Real.exp (c * ξ ^ 2) := by positivity
    nlinarith
  · have hξ0 : ξ ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      linarith
    have hre : (1 + 2 * ((ξ : ℂ) * I)).re = 1 := by simp
    have him : (1 + 2 * ((ξ : ℂ) * I)).im = 2 * ξ := by simp
    have habs : |(1 + 2 * ((ξ : ℂ) * I)).im| = 2 * |ξ| := by
      rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hX := hxi (1 + 2 * ((ξ : ℂ) * I)) (by rw [hre]) (by rw [hre]) (by rw [habs]; linarith)
    rw [habs] at hX
    have hline : (1 + 2 * ((ξ : ℂ) * I)) = 1 + ((2 * ξ : ℝ) : ℂ) * I := by
      push_cast
      ring
    have hZ := hzeta (2 * ξ) (by simpa using hξ0)
    rw [← hline] at hZ
    have habs2 : |2 * ξ| = 2 * |ξ| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [habs2] at hZ
    set x := 2 * |ξ| with hx
    have hx0 : 0 ≤ x := by positivity
    have hcm := hcmp x hx0
    have hexpEq : Real.pi * x / 4 = Real.pi / 4 * x := by ring
    rw [hexpEq] at hX
    have hxsq : c / 4 * x ^ 2 = c * ξ ^ 2 := by
      rw [hx, mul_pow, sq_abs]
      ring
    rw [hxsq] at hcm
    have hbound : ‖(xi (1 + 2 * ((ξ : ℂ) * I)))⁻¹‖ ≤
        C₂ * K * ((1 + x) ^ (N₂ + 11) * Real.exp (Real.pi / 4 * x)) := by
      refine hX.trans ?_
      calc C₂ * (1 + x) ^ N₂ * Real.exp (Real.pi / 4 * x) * ‖(riemannZeta (1 + 2 * ((ξ : ℂ) * I)))⁻¹‖
          ≤ C₂ * (1 + x) ^ N₂ * Real.exp (Real.pi / 4 * x) * (K * (1 + x) ^ 11) :=
            mul_le_mul_of_nonneg_left hZ (by positivity)
        _ = C₂ * K * ((1 + x) ^ (N₂ + 11) * Real.exp (Real.pi / 4 * x)) := by
            rw [pow_add]
            ring
    have h3 := hbound.trans (mul_le_mul_of_nonneg_left hcm (by positivity))
    have h4 : 0 ≤ max M 0 * Real.exp (c * ξ ^ 2) := by positivity
    calc _ ≤ C₂ * K * (C₄ * Real.exp (c * ξ ^ 2)) := h3
      _ ≤ (C₂ * K * C₄ + max M 0) * Real.exp (c * ξ ^ 2) := by nlinarith

theorem exists_norm_tailWeight_line_le_gaussian {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, ‖tailWeight ((ξ : ℂ) * I)‖ ≤ C * Real.exp (c * ξ ^ 2) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_inv_xi_line_le_gaussian (c := c / 2) (by positivity)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_one_add_pow_mul_exp_le_gaussian 2 (b := 0) (c := c / 8) (by positivity)
  refine ⟨4 * C₂ * C₁, by positivity, fun ξ => ?_⟩
  have hn1 : ‖(1 : ℂ) + 2 * ((ξ : ℂ) * I)‖ ≤ 1 + 2 * |ξ| := by
    refine (norm_add_le _ _).trans ?_
    simp [Complex.norm_real]
  have hn2 : ‖(2 : ℂ) * ((ξ : ℂ) * I)‖ ≤ 1 + 2 * |ξ| := by
    simp [Complex.norm_real]
  set x := 2 * |ξ| with hx
  have hx0 : 0 ≤ x := by positivity
  have hcm := h₂ x hx0
  simp only [zero_mul, Real.exp_zero, mul_one] at hcm
  have hxsq : c / 8 * x ^ 2 = c / 2 * ξ ^ 2 := by
    rw [hx, mul_pow, sq_abs]
    ring
  rw [hxsq] at hcm
  rw [tailWeight, div_eq_mul_inv, norm_mul, norm_mul]
  have hpoly : ‖(1 : ℂ) + 2 * ((ξ : ℂ) * I)‖ * ‖(2 : ℂ) * ((ξ : ℂ) * I)‖ ≤ (1 + x) ^ 2 := by
    rw [sq]
    exact mul_le_mul hn1 hn2 (norm_nonneg _) (by positivity)
  have hprod : Real.exp (c / 2 * ξ ^ 2) * Real.exp (c / 2 * ξ ^ 2) = Real.exp (c * ξ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hC2pos : 0 < C₂ := h₂ 0 le_rfl |> fun h => by
    simp at h
    nlinarith [Real.exp_pos (c / 8 * 0 ^ 2), hC₂]
  calc ‖(1 : ℂ) + 2 * ((ξ : ℂ) * I)‖ * ‖(2 : ℂ) * ((ξ : ℂ) * I)‖ * ‖(xi (1 + 2 * ((ξ : ℂ) * I)))⁻¹‖
      ≤ (C₂ * Real.exp (c / 2 * ξ ^ 2)) * (C₁ * Real.exp (c / 2 * ξ ^ 2)) :=
        mul_le_mul (hpoly.trans hcm) (h₁ ξ) (norm_nonneg _) (by positivity)
    _ = C₂ * C₁ * Real.exp (c * ξ ^ 2) := by
        rw [← hprod]
        ring
    _ ≤ 4 * C₂ * C₁ * Real.exp (c * ξ ^ 2) := by
        have : 0 ≤ C₂ * C₁ * Real.exp (c * ξ ^ 2) := by positivity
        nlinarith

/-! ### Jets of `E` on the line -/

/-- A constant dominating the three powers of `Y` that occur on a height window. -/
def windowPowerBound (Y₀ : ℝ) : ℝ :=
  (2 * Y₀) ^ (1 / 2 : ℝ) + (Y₀ / 2) ^ (-(1 / 2) : ℝ) + (Y₀ / 2) ^ (-(3 / 2) : ℝ)

theorem windowPowerBound_nonneg {Y₀ : ℝ} (hY₀ : 0 < Y₀) : 0 ≤ windowPowerBound Y₀ := by
  unfold windowPowerBound
  positivity

theorem window_powers_le {Y₀ Y : ℝ} (hY₀ : 0 < Y₀) (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀)) :
    Y ^ (1 / 2 : ℝ) ≤ windowPowerBound Y₀ ∧ Y ^ (-(1 / 2) : ℝ) ≤ windowPowerBound Y₀ ∧
      Y ^ (-(3 / 2) : ℝ) ≤ windowPowerBound Y₀ := by
  have hA : 0 < Y₀ / 2 := by positivity
  have hYpos : 0 < Y := window_pos hY₀ hY
  have ha : 0 ≤ (2 * Y₀) ^ (1 / 2 : ℝ) := by positivity
  have hb : 0 ≤ (Y₀ / 2) ^ (-(1 / 2) : ℝ) := by positivity
  have hc : 0 ≤ (Y₀ / 2) ^ (-(3 / 2) : ℝ) := by positivity
  have h1 : Y ^ (1 / 2 : ℝ) ≤ (2 * Y₀) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hYpos.le hY.2 (by norm_num)
  have h2 : Y ^ (-(1 / 2) : ℝ) ≤ (Y₀ / 2) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hA hY.1 (by norm_num)
  have h3 : Y ^ (-(3 / 2) : ℝ) ≤ (Y₀ / 2) ^ (-(3 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hA hY.1 (by norm_num)
  unfold windowPowerBound
  exact ⟨by linarith, by linarith, by linarith⟩

theorem norm_line (ξ : ℝ) : ‖(ξ : ℂ) * I‖ = |ξ| := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem norm_half_add_line_le (ξ : ℝ) : ‖(1 / 2 + (ξ : ℂ) * I : ℂ)‖ ≤ 1 + |ξ| := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_line]
  have h : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h]
  linarith

theorem norm_half_sub_line_le (ξ : ℝ) : ‖(1 / 2 - (ξ : ℂ) * I : ℂ)‖ ≤ 1 + |ξ| := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_line]
  have h : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h]
  linarith

/-- Absorbing a sum into the common shape `K p² (1 + W)`. -/
theorem jet_shape_le {A B K p2 W : ℝ} (hA : A ≤ K) (hB : B ≤ K) (hp : 0 ≤ p2) (hW : 0 ≤ W) :
    A * p2 + B * (p2 * W) ≤ K * p2 * (1 + W) := by
  have h1 : A * p2 ≤ K * p2 := mul_le_mul_of_nonneg_right hA hp
  have h2 : B * (p2 * W) ≤ K * (p2 * W) := mul_le_mul_of_nonneg_right hB (mul_nonneg hp hW)
  calc A * p2 + B * (p2 * W) ≤ K * p2 + K * (p2 * W) := add_le_add h1 h2
    _ = K * p2 * (1 + W) := by ring

/-- The bound for `∂_Y²` of a one-sided tail on the line. -/
theorem norm_weightedTailYY_line_le {Y₀ Y C₀ : ℝ} (hY₀ : 0 < Y₀) (hC₀ : 0 ≤ C₀)
    (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀)) (ξ : ℝ) (negative : Bool) (x : ℝ)
    (hT : ‖weightedTail ((ξ : ℂ) * I) negative x Y‖ ≤ C₀)
    (hXX : ‖weightedTailXX ((ξ : ℂ) * I) negative x Y‖ ≤ C₀) :
    ‖weightedTailYY ((ξ : ℂ) * I) negative x Y‖ ≤ C₀ * (4 / Y₀ ^ 2 + 1) * (1 + |ξ|) ^ 2 := by
  have hYpos : 0 < Y := window_pos hY₀ hY
  rw [weightedTailYY_eq _ negative x hYpos]
  have hYsq : 1 / Y ^ 2 ≤ 4 / Y₀ ^ 2 := window_inv_sq_le hY₀ hY
  set p2 := (1 + |ξ|) ^ 2 with hp2
  have hξ := abs_nonneg ξ
  have hp2one : 1 ≤ p2 := by
    rw [hp2]
    exact one_le_pow₀ (by linarith)
  have huNorm : ‖(((ξ : ℂ) * I) ^ 2 - 1 / 4 : ℂ)‖ ≤ p2 := by
    refine (norm_sub_le _ _).trans ?_
    have h2 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
    rw [norm_pow, norm_line, h2, hp2]
    nlinarith
  have hquot : ‖(((ξ : ℂ) * I) ^ 2 - 1 / 4) * weightedTail ((ξ : ℂ) * I) negative x Y / (Y : ℂ) ^ 2‖ ≤
      p2 * C₀ * (4 / Y₀ ^ 2) := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hYpos,
      div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul huNorm hT (norm_nonneg _) (by positivity)) hYsq (by positivity)
      (by positivity)
  refine (norm_sub_le _ _).trans ?_
  have hC : C₀ ≤ C₀ * p2 := le_mul_of_one_le_right hC₀ hp2one
  calc _ ≤ p2 * C₀ * (4 / Y₀ ^ 2) + C₀ := add_le_add hquot hXX
    _ ≤ p2 * C₀ * (4 / Y₀ ^ 2) + C₀ * p2 := by linarith
    _ = C₀ * (4 / Y₀ ^ 2 + 1) * p2 := by ring

/-- The polynomial `(1+|ξ|)²(1 + ‖χ‖)` is dominated by any Gaussian. -/
theorem exists_jet_shape_le_gaussian {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ,
      (1 + |ξ|) ^ 2 * (1 + ‖tailWeight ((ξ : ℂ) * I)‖) ≤ C * Real.exp (c * ξ ^ 2) := by
  obtain ⟨C₁, hC₁, hχ⟩ := exists_norm_tailWeight_line_le_gaussian (c := c / 2) (by positivity)
  obtain ⟨C₂, hC₂, hcmp⟩ := exists_one_add_pow_mul_exp_le_gaussian 2 (b := 0) (c := c / 2)
    (by positivity)
  refine ⟨(1 + C₁) * C₂, by positivity, fun ξ => ?_⟩
  have hE1 : 1 ≤ Real.exp (c / 2 * ξ ^ 2) := Real.one_le_exp (by positivity)
  have hW : 1 + ‖tailWeight ((ξ : ℂ) * I)‖ ≤ (1 + C₁) * Real.exp (c / 2 * ξ ^ 2) := by
    have := hχ ξ
    rw [add_mul, one_mul]
    linarith
  have hp := hcmp |ξ| (abs_nonneg ξ)
  simp only [zero_mul, Real.exp_zero, mul_one, sq_abs] at hp
  have hprod : Real.exp (c / 2 * ξ ^ 2) * Real.exp (c / 2 * ξ ^ 2) = Real.exp (c * ξ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (1 + |ξ|) ^ 2 * (1 + ‖tailWeight ((ξ : ℂ) * I)‖)
      ≤ (C₂ * Real.exp (c / 2 * ξ ^ 2)) * ((1 + C₁) * Real.exp (c / 2 * ξ ^ 2)) :=
        mul_le_mul hp hW (by positivity) (by positivity)
    _ = (1 + C₁) * C₂ * (Real.exp (c / 2 * ξ ^ 2) * Real.exp (c / 2 * ξ ^ 2)) := by ring
    _ = _ := by rw [hprod]

section JetShapes

variable {Y₀ Y C₀ : ℝ} (hY₀ : 0 < Y₀) (hC₀ : 0 ≤ C₀) (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀)) (ξ x : ℝ)

/-- Abbreviation: the common constant of the jet shapes. -/
def jetShapeConstant (Y₀ C₀ : ℝ) : ℝ :=
  2 * windowPowerBound Y₀ + 2 * C₀ * (4 / Y₀ ^ 2 + 1) + 2 * C₀

theorem le_jetShapeConstant_left (hY₀ : 0 < Y₀) (hC₀ : 0 ≤ C₀) :
    2 * windowPowerBound Y₀ ≤ jetShapeConstant Y₀ C₀ := by
  have : 0 ≤ 2 * C₀ * (4 / Y₀ ^ 2 + 1) := by positivity
  unfold jetShapeConstant
  linarith

theorem le_jetShapeConstant_mid (hY₀ : 0 < Y₀) (hC₀ : 0 ≤ C₀) :
    2 * C₀ * (4 / Y₀ ^ 2 + 1) ≤ jetShapeConstant Y₀ C₀ := by
  have := windowPowerBound_nonneg hY₀
  unfold jetShapeConstant
  linarith

theorem le_jetShapeConstant_right (hY₀ : 0 < Y₀) (hC₀ : 0 ≤ C₀) :
    2 * C₀ ≤ jetShapeConstant Y₀ C₀ := by
  have := windowPowerBound_nonneg hY₀
  have : 0 ≤ 2 * C₀ * (4 / Y₀ ^ 2 + 1) := by positivity
  unfold jetShapeConstant
  linarith

include hY₀ hC₀ hY

theorem norm_eisenstein_shape (hT : ‖eisTail ((ξ : ℂ) * I) x Y‖ ≤ 2 * C₀) :
    ‖normalizedEisenstein ((ξ : ℂ) * I) x Y‖ ≤
      jetShapeConstant Y₀ C₀ * (1 + |ξ|) ^ 2 * (1 + ‖tailWeight ((ξ : ℂ) * I)‖) := by
  have hYpos := window_pos hY₀ hY
  obtain ⟨hP, -, -⟩ := window_powers_le hY₀ hY
  set W := ‖tailWeight ((ξ : ℂ) * I)‖ with hW
  have hWnn : 0 ≤ W := norm_nonneg _
  set p2 := (1 + |ξ|) ^ 2 with hp2
  have hp2one : 1 ≤ p2 := one_le_pow₀ (by linarith [abs_nonneg ξ])
  have hreA : (1 / 2 + (ξ : ℂ) * I).re = 1 / 2 := by simp
  have hreB : (1 / 2 - (ξ : ℂ) * I).re = 1 / 2 := by simp
  have h1 : ‖(Y : ℂ) ^ (1 / 2 + (ξ : ℂ) * I)‖ ≤ windowPowerBound Y₀ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos, hreA]
    exact hP
  have h2 : ‖scatteringPhase ((ξ : ℂ) * I) * (Y : ℂ) ^ (1 / 2 - (ξ : ℂ) * I)‖ ≤ windowPowerBound Y₀ := by
    rw [norm_mul, norm_scatteringPhase_line, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hYpos, hreB]
    exact hP
  have h3 : ‖tailWeight ((ξ : ℂ) * I) * eisTail ((ξ : ℂ) * I) x Y‖ ≤ 2 * C₀ * W := by
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hT hWnn
  have hM := windowPowerBound_nonneg hY₀
  have hshape := jet_shape_le (le_jetShapeConstant_left (C₀ := C₀) hY₀ hC₀)
    (le_jetShapeConstant_right (C₀ := C₀) hY₀ hC₀) (by linarith : 0 ≤ p2) hWnn
  refine le_trans ?_ hshape
  rw [normalizedEisenstein]
  refine (norm_add₃_le).trans ?_
  have hA : 2 * windowPowerBound Y₀ ≤ 2 * windowPowerBound Y₀ * p2 :=
    le_mul_of_one_le_right (by linarith) hp2one
  have hB : 2 * C₀ * W ≤ 2 * C₀ * (p2 * W) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact le_mul_of_one_le_left hWnn hp2one
  linarith

omit hY in
theorem norm_eisensteinX_shape (hT : ‖eisTailX ((ξ : ℂ) * I) x Y‖ ≤ 2 * C₀) :
    ‖eisensteinX ((ξ : ℂ) * I) x Y‖ ≤
      jetShapeConstant Y₀ C₀ * (1 + |ξ|) ^ 2 * (1 + ‖tailWeight ((ξ : ℂ) * I)‖) := by
  set W := ‖tailWeight ((ξ : ℂ) * I)‖ with hW
  have hWnn : 0 ≤ W := norm_nonneg _
  set p2 := (1 + |ξ|) ^ 2 with hp2
  have hp2one : 1 ≤ p2 := one_le_pow₀ (by linarith [abs_nonneg ξ])
  have hM := windowPowerBound_nonneg hY₀
  have hshape := jet_shape_le (le_jetShapeConstant_left (C₀ := C₀) hY₀ hC₀)
    (le_jetShapeConstant_right (C₀ := C₀) hY₀ hC₀) (by linarith : 0 ≤ p2) hWnn
  refine le_trans ?_ hshape
  rw [eisensteinX, norm_mul, mul_comm]
  have h1 : ‖eisTailX ((ξ : ℂ) * I) x Y‖ * W ≤ 2 * C₀ * W := mul_le_mul_of_nonneg_right hT hWnn
  have hB : 2 * C₀ * W ≤ 2 * C₀ * (p2 * W) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact le_mul_of_one_le_left hWnn hp2one
  have hA : 0 ≤ 2 * windowPowerBound Y₀ * p2 := by positivity
  linarith

omit hY in
theorem norm_eisensteinXX_shape (hT : ‖eisTailXX ((ξ : ℂ) * I) x Y‖ ≤ 2 * C₀) :
    ‖eisensteinXX ((ξ : ℂ) * I) x Y‖ ≤
      jetShapeConstant Y₀ C₀ * (1 + |ξ|) ^ 2 * (1 + ‖tailWeight ((ξ : ℂ) * I)‖) := by
  set W := ‖tailWeight ((ξ : ℂ) * I)‖ with hW
  have hWnn : 0 ≤ W := norm_nonneg _
  set p2 := (1 + |ξ|) ^ 2 with hp2
  have hp2one : 1 ≤ p2 := one_le_pow₀ (by linarith [abs_nonneg ξ])
  have hM := windowPowerBound_nonneg hY₀
  have hshape := jet_shape_le (le_jetShapeConstant_left (C₀ := C₀) hY₀ hC₀)
    (le_jetShapeConstant_right (C₀ := C₀) hY₀ hC₀) (by linarith : 0 ≤ p2) hWnn
  refine le_trans ?_ hshape
  rw [eisensteinXX, norm_mul, mul_comm]
  have h1 : ‖eisTailXX ((ξ : ℂ) * I) x Y‖ * W ≤ 2 * C₀ * W := mul_le_mul_of_nonneg_right hT hWnn
  have hB : 2 * C₀ * W ≤ 2 * C₀ * (p2 * W) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact le_mul_of_one_le_left hWnn hp2one
  have hA : 0 ≤ 2 * windowPowerBound Y₀ * p2 := by positivity
  linarith

theorem norm_eisensteinY_shape (hT : ‖eisTailY ((ξ : ℂ) * I) x Y‖ ≤ 2 * C₀) :
    ‖eisensteinY ((ξ : ℂ) * I) x Y‖ ≤
      jetShapeConstant Y₀ C₀ * (1 + |ξ|) ^ 2 * (1 + ‖tailWeight ((ξ : ℂ) * I)‖) := by
  have hYpos := window_pos hY₀ hY
  obtain ⟨-, hP, -⟩ := window_powers_le hY₀ hY
  set W := ‖tailWeight ((ξ : ℂ) * I)‖ with hW
  have hWnn : 0 ≤ W := norm_nonneg _
  set p := 1 + |ξ| with hp
  have hp1 : 1 ≤ p := by linarith [abs_nonneg ξ]
  have hp2one : 1 ≤ p ^ 2 := one_le_pow₀ hp1
  have hpp : p ≤ p ^ 2 := by nlinarith
  have hreA : (1 / 2 + (ξ : ℂ) * I - 1).re = -(1 / 2) := by
    simp
    norm_num
  have hreB : (1 / 2 - (ξ : ℂ) * I - 1).re = -(1 / 2) := by
    simp
    norm_num
  have hM := windowPowerBound_nonneg hY₀
  have h1 : ‖(1 / 2 + (ξ : ℂ) * I) * (Y : ℂ) ^ (1 / 2 + (ξ : ℂ) * I - 1)‖ ≤ p * windowPowerBound Y₀ := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hYpos, hreA]
    exact mul_le_mul (norm_half_add_line_le ξ) hP (by positivity) (by linarith)
  have h2 : ‖scatteringPhase ((ξ : ℂ) * I) *
      ((1 / 2 - (ξ : ℂ) * I) * (Y : ℂ) ^ (1 / 2 - (ξ : ℂ) * I - 1))‖ ≤ p * windowPowerBound Y₀ := by
    rw [norm_mul, norm_scatteringPhase_line, one_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hYpos, hreB]
    exact mul_le_mul (norm_half_sub_line_le ξ) hP (by positivity) (by linarith)
  have h3 : ‖tailWeight ((ξ : ℂ) * I) * eisTailY ((ξ : ℂ) * I) x Y‖ ≤ 2 * C₀ * W := by
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hT hWnn
  have hshape := jet_shape_le (le_jetShapeConstant_left (C₀ := C₀) hY₀ hC₀)
    (le_jetShapeConstant_right (C₀ := C₀) hY₀ hC₀) (by linarith : 0 ≤ p ^ 2) hWnn
  refine le_trans ?_ hshape
  rw [eisensteinY]
  refine (norm_add₃_le).trans ?_
  have hA : p * windowPowerBound Y₀ ≤ p ^ 2 * windowPowerBound Y₀ :=
    mul_le_mul_of_nonneg_right hpp hM
  have hB : 2 * C₀ * W ≤ 2 * C₀ * (p ^ 2 * W) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact le_mul_of_one_le_left hWnn hp2one
  have hexp : 2 * windowPowerBound Y₀ * p ^ 2 = p ^ 2 * windowPowerBound Y₀ + p ^ 2 * windowPowerBound Y₀ := by
    ring
  linarith

theorem norm_eisensteinYY_shape
    (hT : ‖eisTailYY ((ξ : ℂ) * I) x Y‖ ≤ 2 * C₀ * (4 / Y₀ ^ 2 + 1) * (1 + |ξ|) ^ 2) :
    ‖eisensteinYY ((ξ : ℂ) * I) x Y‖ ≤
      jetShapeConstant Y₀ C₀ * (1 + |ξ|) ^ 2 * (1 + ‖tailWeight ((ξ : ℂ) * I)‖) := by
  have hYpos := window_pos hY₀ hY
  obtain ⟨-, -, hP⟩ := window_powers_le hY₀ hY
  set W := ‖tailWeight ((ξ : ℂ) * I)‖ with hW
  have hWnn : 0 ≤ W := norm_nonneg _
  set p := 1 + |ξ| with hp
  have hp1 : 1 ≤ p := by linarith [abs_nonneg ξ]
  have hreA : (1 / 2 + (ξ : ℂ) * I - 1 - 1).re = -(3 / 2) := by
    simp
    norm_num
  have hreB : (1 / 2 - (ξ : ℂ) * I - 1 - 1).re = -(3 / 2) := by
    simp
    norm_num
  have hM := windowPowerBound_nonneg hY₀
  have hplus1 : ‖(1 / 2 + (ξ : ℂ) * I - 1 : ℂ)‖ ≤ p := by
    have h : (1 / 2 + (ξ : ℂ) * I - 1 : ℂ) = -(1 / 2 - (ξ : ℂ) * I) := by ring
    rw [h, norm_neg]
    exact norm_half_sub_line_le ξ
  have hminus1 : ‖(1 / 2 - (ξ : ℂ) * I - 1 : ℂ)‖ ≤ p := by
    have h : (1 / 2 - (ξ : ℂ) * I - 1 : ℂ) = -(1 / 2 + (ξ : ℂ) * I) := by ring
    rw [h, norm_neg]
    exact norm_half_add_line_le ξ
  have h1 : ‖(1 / 2 + (ξ : ℂ) * I) * ((1 / 2 + (ξ : ℂ) * I - 1) *
      (Y : ℂ) ^ (1 / 2 + (ξ : ℂ) * I - 1 - 1))‖ ≤ p ^ 2 * windowPowerBound Y₀ := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hYpos, hreA, sq, mul_assoc]
    exact mul_le_mul (norm_half_add_line_le ξ) (mul_le_mul hplus1 hP (by positivity) (by linarith))
      (by positivity) (by linarith)
  have h2 : ‖scatteringPhase ((ξ : ℂ) * I) * ((1 / 2 - (ξ : ℂ) * I) * ((1 / 2 - (ξ : ℂ) * I - 1) *
      (Y : ℂ) ^ (1 / 2 - (ξ : ℂ) * I - 1 - 1)))‖ ≤ p ^ 2 * windowPowerBound Y₀ := by
    rw [norm_mul, norm_scatteringPhase_line, one_mul, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hYpos, hreB, sq, mul_assoc]
    exact mul_le_mul (norm_half_sub_line_le ξ) (mul_le_mul hminus1 hP (by positivity) (by linarith))
      (by positivity) (by linarith)
  have h3 : ‖tailWeight ((ξ : ℂ) * I) * eisTailYY ((ξ : ℂ) * I) x Y‖ ≤
      2 * C₀ * (4 / Y₀ ^ 2 + 1) * (p ^ 2 * W) := by
    rw [norm_mul, mul_comm]
    calc _ ≤ (2 * C₀ * (4 / Y₀ ^ 2 + 1) * p ^ 2) * W := mul_le_mul_of_nonneg_right hT hWnn
      _ = _ := by ring
  have hshape := jet_shape_le (le_jetShapeConstant_left (C₀ := C₀) hY₀ hC₀)
    (le_jetShapeConstant_mid (C₀ := C₀) hY₀ hC₀) (by positivity : 0 ≤ p ^ 2) hWnn
  refine le_trans ?_ hshape
  rw [eisensteinYY]
  refine (norm_add₃_le).trans ?_
  have hexp : 2 * windowPowerBound Y₀ * p ^ 2 = p ^ 2 * windowPowerBound Y₀ + p ^ 2 * windowPowerBound Y₀ := by
    ring
  linarith

end JetShapes

/-- **All jets of `E` on the line are dominated by any Gaussian**, uniformly in `x` and on a height
window. -/
theorem exists_eisenstein_jets_le_gaussian {Y₀ : ℝ} (hY₀ : 0 < Y₀) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ξ x Y : ℝ), Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
      ‖normalizedEisenstein ((ξ : ℂ) * I) x Y‖ ≤ C * Real.exp (c * ξ ^ 2) ∧
      ‖eisensteinX ((ξ : ℂ) * I) x Y‖ ≤ C * Real.exp (c * ξ ^ 2) ∧
      ‖eisensteinXX ((ξ : ℂ) * I) x Y‖ ≤ C * Real.exp (c * ξ ^ 2) ∧
      ‖eisensteinY ((ξ : ℂ) * I) x Y‖ ≤ C * Real.exp (c * ξ ^ 2) ∧
      ‖eisensteinYY ((ξ : ℂ) * I) x Y‖ ≤ C * Real.exp (c * ξ ^ 2) := by
  obtain ⟨C₀, hC₀, htail⟩ := exists_weightedTail_jets_le hY₀ (le_refl (0 : ℝ))
  obtain ⟨C₁, hC₁, hshape⟩ := exists_jet_shape_le_gaussian hc
  have hK : 0 ≤ jetShapeConstant Y₀ C₀ := by
    have := windowPowerBound_nonneg hY₀
    unfold jetShapeConstant
    positivity
  refine ⟨jetShapeConstant Y₀ C₀ * C₁, by positivity, fun ξ x Y hY => ?_⟩
  have hu : |((ξ : ℂ) * I).re| ≤ 0 := by simp
  obtain ⟨hT1, hX1, hXX1, hY1⟩ := htail ((ξ : ℂ) * I) false x Y hu hY
  obtain ⟨hT2, hX2, hXX2, hY2⟩ := htail ((ξ : ℂ) * I) true x Y hu hY
  have hsum : ∀ {a b : ℂ}, ‖a‖ ≤ C₀ → ‖b‖ ≤ C₀ → ‖a + b‖ ≤ 2 * C₀ := fun ha hb =>
    (norm_add_le _ _).trans (by linarith)
  have hYY : ‖eisTailYY ((ξ : ℂ) * I) x Y‖ ≤ 2 * C₀ * (4 / Y₀ ^ 2 + 1) * (1 + |ξ|) ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_weightedTailYY_line_le hY₀ hC₀ hY ξ false x hT1 hXX1
    have h2 := norm_weightedTailYY_line_le hY₀ hC₀ hY ξ true x hT2 hXX2
    linarith
  have hfinal : ∀ J : ℝ,
      J ≤ jetShapeConstant Y₀ C₀ * (1 + |ξ|) ^ 2 * (1 + ‖tailWeight ((ξ : ℂ) * I)‖) →
      J ≤ jetShapeConstant Y₀ C₀ * C₁ * Real.exp (c * ξ ^ 2) := by
    intro J hJ
    refine hJ.trans ?_
    calc jetShapeConstant Y₀ C₀ * (1 + |ξ|) ^ 2 * (1 + ‖tailWeight ((ξ : ℂ) * I)‖)
        = jetShapeConstant Y₀ C₀ * ((1 + |ξ|) ^ 2 * (1 + ‖tailWeight ((ξ : ℂ) * I)‖)) := by ring
      _ ≤ jetShapeConstant Y₀ C₀ * (C₁ * Real.exp (c * ξ ^ 2)) :=
          mul_le_mul_of_nonneg_left (hshape ξ) hK
      _ = _ := by ring
  exact ⟨hfinal _ (norm_eisenstein_shape hY₀ hC₀ hY ξ x (hsum hT1 hT2)),
    hfinal _ (norm_eisensteinX_shape hY₀ hC₀ ξ x (hsum hX1 hX2)),
    hfinal _ (norm_eisensteinXX_shape hY₀ hC₀ ξ x (hsum hXX1 hXX2)),
    hfinal _ (norm_eisensteinY_shape hY₀ hC₀ hY ξ x (hsum hY1 hY2)),
    hfinal _ (norm_eisensteinYY_shape hY₀ hC₀ hY ξ x hYY)⟩

/-! ### Measurability on the line -/

theorem continuous_scatteringPhase_line : Continuous fun ξ : ℝ => scatteringPhase ((ξ : ℂ) * I) := by
  have hne : ∀ ξ : ℝ, (2 : ℂ) * ((ξ : ℂ) * I) - 1 ≠ 0 := fun ξ h => by
    have := congrArg Complex.re h
    simp at this
  have hline : Continuous fun ξ : ℝ => (ξ : ℂ) * I := by fun_prop
  unfold scatteringPhase
  refine Continuous.mul (Continuous.div (by fun_prop) (by fun_prop) hne) ?_
  refine Continuous.div ?_ ?_ xi_line_ne_zero
  · exact xi_differentiable.continuous.comp (by fun_prop)
  · exact xi_differentiable.continuous.comp (by fun_prop)

theorem continuous_tailWeight_line : Continuous fun ξ : ℝ => tailWeight ((ξ : ℂ) * I) := by
  unfold tailWeight
  refine Continuous.div (by fun_prop) ?_ xi_line_ne_zero
  exact xi_differentiable.continuous.comp (by fun_prop)

section LineMeasurability

variable {Y : ℝ}

theorem continuous_cpow_line (hY : 0 < Y) {c₀ c₁ : ℂ} :
    Continuous fun ξ : ℝ => (Y : ℂ) ^ (c₀ + c₁ * ((ξ : ℂ) * I)) := by
  refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
  exact_mod_cast hY.ne'

theorem measurable_eisTail_line (hY : 0 < Y) (x : ℝ) :
    Measurable fun ξ : ℝ => eisTail ((ξ : ℂ) * I) x Y :=
  (measurable_weightedTail_line hY false x).add (measurable_weightedTail_line hY true x)

theorem measurable_normalizedEisenstein_line (hY : 0 < Y) (x : ℝ) :
    Measurable fun ξ : ℝ => normalizedEisenstein ((ξ : ℂ) * I) x Y := by
  have h1 : Continuous fun ξ : ℝ => (Y : ℂ) ^ (1 / 2 + ((ξ : ℂ) * I)) := by
    simpa using continuous_cpow_line hY (c₀ := 1 / 2) (c₁ := 1)
  have h2 : Continuous fun ξ : ℝ => (Y : ℂ) ^ (1 / 2 - ((ξ : ℂ) * I)) := by
    have := continuous_cpow_line hY (c₀ := 1 / 2) (c₁ := -1)
    simpa [sub_eq_add_neg] using this
  unfold normalizedEisenstein
  exact (h1.measurable.add (continuous_scatteringPhase_line.mul h2).measurable).add
    (continuous_tailWeight_line.measurable.mul (measurable_eisTail_line hY x))

theorem measurable_eisensteinX_line (hY : 0 < Y) (x : ℝ) :
    Measurable fun ξ : ℝ => eisensteinX ((ξ : ℂ) * I) x Y :=
  continuous_tailWeight_line.measurable.mul
    ((measurable_weightedTailX_line hY false x).add (measurable_weightedTailX_line hY true x))

theorem measurable_eisensteinXX_line (hY : 0 < Y) (x : ℝ) :
    Measurable fun ξ : ℝ => eisensteinXX ((ξ : ℂ) * I) x Y :=
  continuous_tailWeight_line.measurable.mul
    ((measurable_weightedTailXX_line hY false x).add (measurable_weightedTailXX_line hY true x))

theorem measurable_eisensteinY_line (hY : 0 < Y) (x : ℝ) :
    Measurable fun ξ : ℝ => eisensteinY ((ξ : ℂ) * I) x Y := by
  have h1 : Continuous fun ξ : ℝ => (Y : ℂ) ^ (1 / 2 + ((ξ : ℂ) * I) - 1) := by
    have := continuous_cpow_line hY (c₀ := -(1 / 2)) (c₁ := 1)
    refine this.congr fun ξ => ?_
    congr 1
    ring
  have h2 : Continuous fun ξ : ℝ => (Y : ℂ) ^ (1 / 2 - ((ξ : ℂ) * I) - 1) := by
    have := continuous_cpow_line hY (c₀ := -(1 / 2)) (c₁ := -1)
    refine this.congr fun ξ => ?_
    congr 1
    ring
  have hl : Continuous fun ξ : ℝ => (ξ : ℂ) * I := by fun_prop
  unfold eisensteinY
  refine ((Continuous.mul (by fun_prop) h1).measurable.add
    (continuous_scatteringPhase_line.mul (Continuous.mul (by fun_prop) h2)).measurable).add ?_
  exact continuous_tailWeight_line.measurable.mul
    ((measurable_weightedTailY_line hY false x).add (measurable_weightedTailY_line hY true x))

theorem measurable_eisensteinYY_line (hY : 0 < Y) (x : ℝ) :
    Measurable fun ξ : ℝ => eisensteinYY ((ξ : ℂ) * I) x Y := by
  have h1 : Continuous fun ξ : ℝ => (Y : ℂ) ^ (1 / 2 + ((ξ : ℂ) * I) - 1 - 1) := by
    have := continuous_cpow_line hY (c₀ := -(3 / 2)) (c₁ := 1)
    refine this.congr fun ξ => ?_
    congr 1
    ring
  have h2 : Continuous fun ξ : ℝ => (Y : ℂ) ^ (1 / 2 - ((ξ : ℂ) * I) - 1 - 1) := by
    have := continuous_cpow_line hY (c₀ := -(3 / 2)) (c₁ := -1)
    refine this.congr fun ξ => ?_
    congr 1
    ring
  unfold eisensteinYY
  refine ((Continuous.mul (by fun_prop) (Continuous.mul (by fun_prop) h1)).measurable.add
    (continuous_scatteringPhase_line.mul
      (Continuous.mul (by fun_prop) (Continuous.mul (by fun_prop) h2))).measurable).add ?_
  exact continuous_tailWeight_line.measurable.mul
    ((measurable_weightedTailYY_line hY false x).add (measurable_weightedTailYY_line hY true x))

end LineMeasurability

end GaloisForLFunctions.BlackHoleRingdown

end
