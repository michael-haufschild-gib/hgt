import GaloisForLFunctions.ExclusionOfTheCriticalState.TheGammaPairingInLevyForm

/-!
# The energy domain is stable under bounded Lipschitz multipliers

For every profile of `L¹ ∩ L²` the Gamma energy is a mass term plus the Lévy jump energy
`∫_{x>0} ω(x) ∫ (G(u) - G(u+x))² du dx`, as an identity in `[0, ∞]`. A profile with finite jump
energy therefore has finite Gamma energy.

For a bounded Lipschitz multiplier `ψ`,

  `(ψF)(u) - (ψF)(u+x) = ψ(u) (F(u) - F(u+x)) + (ψ(u) - ψ(u+x)) F(u+x)`,

and `ω(x) min(Λx, M)² ≤ (3Λ² + 2M²) e^{-x/2}`: a Lipschitz jump is paid near the origin, a bounded
one far out. Hence `ψF` lies in the energy domain together with `F`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology
open scoped FourierTransform

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Finite jump energy gives finite Gamma energy -/

theorem memLp_cx_of_sq {G : ℝ → ℝ} (hG1 : Integrable G) (hG2 : Integrable fun u => G u ^ 2) :
    MemLp (cx G) 2 volume := by
  have hGc : Integrable (cx G) := hG1.ofReal (𝕜 := ℂ)
  apply (memLp_two_iff_integrable_sq_norm hGc.aestronglyMeasurable).mpr
  simpa only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hG2

/-- **Finite jump energy gives finite Gamma energy.** The Lévy–Plancherel identity holds in
`[0, ∞]` on `L¹ ∩ L²`; the mass term is paid by Plancherel. -/
theorem integrable_gamma_of_lintegral_levy_ne_top {G : ℝ → ℝ} (hG1 : Integrable G)
    (hG2 : Integrable fun u => G u ^ 2)
    (h : ∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal (archLevyDensity x * ∫ u, (G u - G (u + x)) ^ 2) ≠ ⊤) :
    Integrable fun r : ℝ => ‖paperFT (cx G) r‖ ^ 2 * EF.gammaBracket r := by
  have hg1 : Integrable (cx G) := hG1.ofReal (𝕜 := ℂ)
  have hg2 := memLp_cx_of_sq hG1 hG2
  have hL := lintegral_archSymbol_mul_normSq_fourier hg1 hg2
  have hL' : (∫⁻ ξ : ℝ, ENNReal.ofReal (2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) -
      gammaHardyPhaseRate 0) * ‖𝓕 (cx G) ξ‖ ^ 2)) ≠ ⊤ := by
    rw [hL]
    exact ne_of_eq_of_ne (lintegral_levy_eq G) h
  have hcont : Continuous (𝓕 (cx G)) :=
    GaloisForLFunctions.RHTower.continuous_fourier_of_integrable hg1
  have hθc : Continuous fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) :=
    continuous_gammaHardyPhaseRate.comp (continuous_const.mul continuous_id)
  have hSnn : ∀ ξ : ℝ, 0 ≤ 2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0) *
      ‖𝓕 (cx G) ξ‖ ^ 2 := fun ξ =>
    mul_nonneg (mul_nonneg two_pos.le (sub_nonneg.mpr (gammaHardyPhaseRate_zero_le_levy _)))
      (sq_nonneg _)
  have hSint : Integrable fun ξ : ℝ => 2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) -
      gammaHardyPhaseRate 0) * ‖𝓕 (cx G) ξ‖ ^ 2 := by
    refine ⟨((continuous_const.mul (hθc.sub continuous_const)).mul
      (hcont.norm.pow 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hSnn)]
    exact lt_top_iff_ne_top.mpr hL'
  have hP := GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hg1 hg2
  have hθ : Integrable fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 (cx G) ξ‖ ^ 2 := by
    refine ((hSint.div_const 2).add (hP.const_mul (gammaHardyPhaseRate 0))).congr
      (Eventually.of_forall fun ξ => ?_)
    simp only [Pi.add_apply]
    ring
  have hπ : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have h2 := (hθ.comp_div (neg_ne_zero.mpr hπ)).const_mul 2
  refine h2.congr (Eventually.of_forall fun r => ?_)
  have e1 : 2 * Real.pi * (r / -(2 * Real.pi)) = -r := by field_simp
  have e2 : -(2 * Real.pi * (r / -(2 * Real.pi))) = r := by rw [e1, neg_neg]
  show 2 * (gammaHardyPhaseRate (2 * Real.pi * (r / -(2 * Real.pi))) *
    ‖𝓕 (cx G) (r / -(2 * Real.pi))‖ ^ 2) = ‖paperFT (cx G) r‖ ^ 2 * EF.gammaBracket r
  rw [fourier_eq_paperFT_neg_two_pi_mul, e2, e1, gammaHardyPhaseRate_neg,
    WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate]
  ring

/-! ### The price of a jump of the multiplier -/

theorem integrableOn_exp_neg_half : IntegrableOn (fun x : ℝ => Real.exp (-(x / 2))) (Ioi 0) := by
  refine (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).congr_fun
    (fun x _ => ?_) measurableSet_Ioi
  show Real.exp (-(1 / 2) * x) = Real.exp (-(x / 2))
  congr 1
  ring

/-- `ω(x) min(Λx, M)² ≤ (3Λ² + 2M²) e^{-x/2}`. -/
theorem archLevyDensity_mul_min_sq_le {Λ M x : ℝ} (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) (hx : 0 < x) :
    archLevyDensity x * min (Λ * x) M ^ 2 ≤ (3 * Λ ^ 2 + 2 * M ^ 2) * Real.exp (-(x / 2)) := by
  have hm0 : 0 ≤ min (Λ * x) M := le_min (mul_nonneg hΛ hx.le) hM
  have he := Real.exp_pos (-(x / 2))
  rcases le_total x 1 with h1 | h1
  · have h2 := archLevyDensity_le_near hx h1
    have hmin : min (Λ * x) M ^ 2 ≤ (Λ * x) ^ 2 := pow_le_pow_left₀ hm0 (min_le_left _ _) 2
    have hexp : (1 : ℝ) / 2 ≤ Real.exp (-(x / 2)) := by
      have := Real.add_one_le_exp (-(x / 2))
      linarith
    have hΛx : Λ ^ 2 * x ≤ Λ ^ 2 := by nlinarith [sq_nonneg Λ]
    calc archLevyDensity x * min (Λ * x) M ^ 2 ≤ 3 / (2 * x) * (Λ * x) ^ 2 :=
          mul_le_mul h2 hmin (sq_nonneg _) (by positivity)
      _ = 3 / 2 * (Λ ^ 2 * x) := by field_simp
      _ ≤ (3 * Λ ^ 2 + 2 * M ^ 2) * Real.exp (-(x / 2)) := by
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 3 * Λ ^ 2 + 2 * M ^ 2)
            (sub_nonneg.mpr hexp), sq_nonneg M]
  · have h2 := archLevyDensity_le_far h1
    have hmin : min (Λ * x) M ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hm0 (min_le_right _ _) 2
    calc archLevyDensity x * min (Λ * x) M ^ 2 ≤ 2 * Real.exp (-(x / 2)) * M ^ 2 :=
          mul_le_mul h2 hmin (sq_nonneg _) (by positivity)
      _ ≤ (3 * Λ ^ 2 + 2 * M ^ 2) * Real.exp (-(x / 2)) := by
          nlinarith [mul_nonneg (sq_nonneg Λ) he.le]

/-! ### The mixed jump integrand -/

/-- The mixed jump integrand of two profiles of the domain is integrable (polarization). -/
theorem integrableOn_levyMixedIntegrand {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) :
    IntegrableOn (fun x : ℝ => archLevyDensity x *
      ∫ u, (F u - F (u + x)) * (G u - G (u + x))) (Ioi 0) := by
  have hdp := hF.add_const_mul hG 1
  have hdm := hF.add_const_mul hG (-1)
  have hFm := hF.memLp_real
  have hGm := hG.memLp_real
  refine ((hdp.integrableOn_levyIntegrand.sub hdm.integrableOn_levyIntegrand).div_const 4).congr
    (Eventually.of_forall fun x => ?_)
  have hΔF : MemLp (fun u => F u - F (u + x)) 2 volume := hFm.sub (memLp_two_shift hFm x)
  have hΔG : MemLp (fun u => G u - G (u + x)) 2 volume := hGm.sub (memLp_two_shift hGm x)
  have iP : Integrable fun u => (F u + 1 * G u - (F (u + x) + 1 * G (u + x))) ^ 2 :=
    (integrable_sq_of_memLp (hΔF.add hΔG)).congr (Eventually.of_forall fun u => by
      simp only [Pi.add_apply]; ring)
  have iM : Integrable fun u => (F u + -1 * G u - (F (u + x) + -1 * G (u + x))) ^ 2 :=
    (integrable_sq_of_memLp (hΔF.sub hΔG)).congr (Eventually.of_forall fun u => by
      simp only [Pi.sub_apply]; ring)
  have key : (∫ u, (F u + 1 * G u - (F (u + x) + 1 * G (u + x))) ^ 2) -
      (∫ u, (F u + -1 * G u - (F (u + x) + -1 * G (u + x))) ^ 2) =
        4 * ∫ u, (F u - F (u + x)) * (G u - G (u + x)) := by
    rw [← integral_sub iP iM, ← integral_const_mul]
    congr 1
    funext u
    ring
  show (archLevyDensity x * (∫ u, (F u + 1 * G u - (F (u + x) + 1 * G (u + x))) ^ 2) -
    archLevyDensity x * (∫ u, (F u + -1 * G u - (F (u + x) + -1 * G (u + x))) ^ 2)) / 4 =
      archLevyDensity x * ∫ u, (F u - F (u + x)) * (G u - G (u + x))
  rw [← mul_sub, key]
  ring

/-! ### Multipliers -/

/-- **Bounded Lipschitz multipliers preserve the energy domain.** -/
theorem criticalHalfLineEnergyDomain_lipschitz_mul {F ψ : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hψ : Measurable ψ) {M Λ : ℝ}
    (hM : ∀ u, |ψ u| ≤ M) (hΛ : ∀ u v, |ψ u - ψ v| ≤ Λ * |u - v|) :
    CriticalHalfLineEnergyDomain (fun u => ψ u * F u) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hΛ0 : 0 ≤ Λ := by
    have h := (abs_nonneg _).trans (hΛ 0 1)
    rwa [zero_sub, abs_neg, abs_one, mul_one] at h
  have hmeas : Measurable fun u => ψ u * F u := hψ.mul hF.meas
  have hψ2 : ∀ u, ψ u ^ 2 ≤ M ^ 2 := fun u =>
    sq_le_sq' (by linarith [(abs_le.mp (hM u)).1]) (abs_le.mp (hM u)).2
  have hsqle : ∀ u, (ψ u * F u) ^ 2 ≤ M ^ 2 * F u ^ 2 := fun u => by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (hψ2 u) (sq_nonneg _)
  have hint : Integrable fun u => ψ u * F u := by
    refine (hF.integrable.norm.const_mul M).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM u) (norm_nonneg _)
  have hsq : Integrable fun u => (ψ u * F u) ^ 2 := by
    refine (hF.sq.const_mul (M ^ 2)).mono' (hmeas.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsqle u
  have hexp : Integrable fun u => (ψ u * F u) ^ 2 * Real.exp (-(8 * u)) := by
    refine (hF.exponential.const_mul (M ^ 2)).mono'
      ((hmeas.pow_const 2).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    calc (ψ u * F u) ^ 2 * Real.exp (-(8 * u)) ≤ M ^ 2 * F u ^ 2 * Real.exp (-(8 * u)) :=
          mul_le_mul_of_nonneg_right (hsqle u) (Real.exp_pos _).le
      _ = M ^ 2 * (F u ^ 2 * Real.exp (-(8 * u))) := by ring
  refine ⟨hmeas, hint, hsq, hexp, fun u hu => by rw [hF.support u hu, mul_zero], ?_⟩
  apply integrable_gamma_of_lintegral_levy_ne_top hint hsq
  have hFm := hF.memLp_real
  have hGm : MemLp (fun u => ψ u * F u) 2 volume :=
    (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr hsq
  have hF2 : 0 ≤ ∫ u, F u ^ 2 := integral_nonneg fun u => sq_nonneg _
  -- the dominating integrand
  have hD : IntegrableOn (fun x : ℝ => 2 * M ^ 2 *
      (archLevyDensity x * ∫ u, (F u - F (u + x)) ^ 2) + 2 * (∫ u, F u ^ 2) *
        ((3 * Λ ^ 2 + 2 * (2 * M) ^ 2) * Real.exp (-(x / 2)))) (Ioi 0) :=
    (hF.integrableOn_levyIntegrand.const_mul (2 * M ^ 2)).add
      ((integrableOn_exp_neg_half.const_mul (3 * Λ ^ 2 + 2 * (2 * M) ^ 2)).const_mul
        (2 * ∫ u, F u ^ 2))
  have hle : ∀ x ∈ Ioi (0 : ℝ),
      archLevyDensity x * (∫ u, (ψ u * F u - ψ (u + x) * F (u + x)) ^ 2) ≤
        2 * M ^ 2 * (archLevyDensity x * ∫ u, (F u - F (u + x)) ^ 2) + 2 * (∫ u, F u ^ 2) *
          ((3 * Λ ^ 2 + 2 * (2 * M) ^ 2) * Real.exp (-(x / 2))) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hω := (archLevyDensity_pos hx0).le
    have hΔF : MemLp (fun u => F u - F (u + x)) 2 volume := hFm.sub (memLp_two_shift hFm x)
    have hΔG : MemLp (fun u => ψ u * F u - ψ (u + x) * F (u + x)) 2 volume :=
      hGm.sub (memLp_two_shift hGm x)
    have iL : Integrable fun u => (ψ u * F u - ψ (u + x) * F (u + x)) ^ 2 :=
      integrable_sq_of_memLp hΔG
    have iF : Integrable fun u => (F u - F (u + x)) ^ 2 := integrable_sq_of_memLp hΔF
    have iS : Integrable fun u => F (u + x) ^ 2 := integrable_sq_of_memLp (memLp_two_shift hFm x)
    have hshift : (∫ u, F (u + x) ^ 2) = ∫ u, F u ^ 2 :=
      integral_add_right_eq_self (fun v => F v ^ 2) x
    have hpt : ∀ u, (ψ u * F u - ψ (u + x) * F (u + x)) ^ 2 ≤
        2 * M ^ 2 * (F u - F (u + x)) ^ 2 + 2 * min (Λ * x) (2 * M) ^ 2 * F (u + x) ^ 2 := by
      intro u
      have h1 : |ψ u - ψ (u + x)| ≤ min (Λ * x) (2 * M) := by
        refine le_min ?_ ?_
        · have h := hΛ u (u + x)
          rwa [show u - (u + x) = -x by ring, abs_neg, abs_of_pos hx0] at h
        · have h := abs_sub (ψ u) (ψ (u + x))
          linarith [hM u, hM (u + x)]
      have h2 : (ψ u - ψ (u + x)) ^ 2 ≤ min (Λ * x) (2 * M) ^ 2 :=
        sq_le_sq' (by linarith [(abs_le.mp h1).1]) (abs_le.mp h1).2
      have e : ψ u * F u - ψ (u + x) * F (u + x) =
          ψ u * (F u - F (u + x)) + (ψ u - ψ (u + x)) * F (u + x) := by ring
      rw [e]
      nlinarith [sq_nonneg (ψ u * (F u - F (u + x)) - (ψ u - ψ (u + x)) * F (u + x)),
        mul_le_mul_of_nonneg_right (hψ2 u) (sq_nonneg (F u - F (u + x))),
        mul_le_mul_of_nonneg_right h2 (sq_nonneg (F (u + x)))]
    have hinner : (∫ u, (ψ u * F u - ψ (u + x) * F (u + x)) ^ 2) ≤
        2 * M ^ 2 * (∫ u, (F u - F (u + x)) ^ 2) +
          2 * min (Λ * x) (2 * M) ^ 2 * ∫ u, F u ^ 2 := by
      calc (∫ u, (ψ u * F u - ψ (u + x) * F (u + x)) ^ 2)
          ≤ ∫ u, (2 * M ^ 2 * (F u - F (u + x)) ^ 2 +
              2 * min (Λ * x) (2 * M) ^ 2 * F (u + x) ^ 2) :=
            integral_mono iL ((iF.const_mul _).add (iS.const_mul _)) hpt
        _ = 2 * M ^ 2 * (∫ u, (F u - F (u + x)) ^ 2) +
              2 * min (Λ * x) (2 * M) ^ 2 * ∫ u, F u ^ 2 := by
            rw [integral_add (iF.const_mul _) (iS.const_mul _), integral_const_mul,
              integral_const_mul, hshift]
    have hmin := archLevyDensity_mul_min_sq_le hΛ0 (by positivity : (0 : ℝ) ≤ 2 * M) hx0
    have hmin' := mul_le_mul_of_nonneg_left hmin (mul_nonneg two_pos.le hF2)
    calc archLevyDensity x * (∫ u, (ψ u * F u - ψ (u + x) * F (u + x)) ^ 2)
        ≤ archLevyDensity x * (2 * M ^ 2 * (∫ u, (F u - F (u + x)) ^ 2) +
            2 * min (Λ * x) (2 * M) ^ 2 * ∫ u, F u ^ 2) := mul_le_mul_of_nonneg_left hinner hω
      _ = 2 * M ^ 2 * (archLevyDensity x * ∫ u, (F u - F (u + x)) ^ 2) +
            2 * (∫ u, F u ^ 2) * (archLevyDensity x * min (Λ * x) (2 * M) ^ 2) := by ring
      _ ≤ _ := by linarith
  have hDnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun x : ℝ => 2 * M ^ 2 *
      (archLevyDensity x * ∫ u, (F u - F (u + x)) ^ 2) + 2 * (∫ u, F u ^ 2) *
        ((3 * Λ ^ 2 + 2 * (2 * M) ^ 2) * Real.exp (-(x / 2))) :=
    (ae_restrict_mem measurableSet_Ioi).mono fun x hx =>
      (mul_nonneg (archLevyDensity_pos hx).le (integral_nonneg fun u => sq_nonneg _)).trans
        (hle x hx)
  refine (lt_of_le_of_lt (lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono
    fun x hx => ENNReal.ofReal_le_ofReal (hle x hx))) ?_).ne
  rw [← ofReal_integral_eq_lintegral_ofReal hD hDnn]
  exact ENNReal.ofReal_lt_top

end GaloisForLFunctions.ExclusionOfTheCriticalState
