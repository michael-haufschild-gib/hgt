import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineEnergyGap

/-!
# The variational floor and its critical tangent

The parameter changes only the exponential confinement. The transverse
gap controls the error of replacing a nearby minimizing profile by the
critical-state line.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory WindowTowerOfSpecZ

/-- The unit-mass variational floor of the literal full half-line form. -/
def criticalHalfLineGroundEnergy (R : ℝ) : ℝ :=
  sInf {e : ℝ | ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧
    (∫ u, G u ^ 2) = 1 ∧ criticalHalfLineFullEnergy R G = e}

/-- Changing the ratio changes only the coefficient of the exponential mass. -/
theorem criticalHalfLineFullEnergy_change_ratio (R S : ℝ) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineFullEnergy R G = criticalHalfLineFullEnergy S G +
      (criticalAliasCoefficient R - criticalAliasCoefficient S) *
        (∫ u, G u ^ 2 * Real.exp (-(8 * u))) := by
  unfold criticalHalfLineFullEnergy
  rw [halfLineExpMass_eq_full hG.support]
  ring

/-- Positive confinement gives a finite lower bound on the normalized energy range. -/
theorem criticalHalfLine_energyRange_bddBelow {R : ℝ} (hR : 0 < R) :
    BddBelow {e : ℝ | ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧
      (∫ u, G u ^ 2) = 1 ∧ criticalHalfLineFullEnergy R G = e} := by
  obtain ⟨B, _, hbound⟩ := criticalHalfLineFullEnergy_coercive_remainder hR
  refine ⟨-B, ?_⟩
  rintro e ⟨G, hG, hm, rfl⟩
  have h := hbound hG
  rw [hm, mul_one] at h
  have hw : 0 ≤ (criticalAliasCoefficient R / 2) *
      (∫ u, G u ^ 2 * Real.exp (-(8 * u))) :=
    mul_nonneg (half_pos (criticalAliasCoefficient_positive hR)).le
      (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  linarith only [h, hw]

theorem criticalHalfLineGroundEnergy_le {R : ℝ} (hR : 0 < R) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (hm : (∫ u, G u ^ 2) = 1) :
    criticalHalfLineGroundEnergy R ≤ criticalHalfLineFullEnergy R G :=
  csInf_le (criticalHalfLine_energyRange_bddBelow hR) ⟨G, hG, hm, rfl⟩

/-- Homogeneity extends the unit-mass floor to every profile of positive mass. -/
theorem criticalHalfLineGroundEnergy_mul_mass_le {R : ℝ} (hR : 0 < R) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (hm : 0 < ∫ u, G u ^ 2) :
    criticalHalfLineGroundEnergy R * (∫ u, G u ^ 2) ≤ criticalHalfLineFullEnergy R G := by
  let m : ℝ := ∫ u, G u ^ 2
  let c : ℝ := (Real.sqrt m)⁻¹
  have hcm : c ^ 2 * m = 1 := by
    calc
      _ = c ^ 2 * (Real.sqrt m) ^ 2 := by rw [Real.sq_sqrt hm.le]
      _ = 1 := by
        dsimp only [c]
        rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 (Real.sqrt_pos.mpr hm).ne')]
  have hnorm : (∫ u, (c * G u) ^ 2) = 1 := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact hcm
  have h := criticalHalfLineGroundEnergy_le hR (hG.const_mul c) hnorm
  rw [criticalHalfLineFullEnergy_const_mul] at h
  have hmul := mul_le_mul_of_nonneg_right h hm.le
  have he : c ^ 2 * criticalHalfLineFullEnergy R G * m = criticalHalfLineFullEnergy R G := by
    calc
      _ = (c ^ 2 * m) * criticalHalfLineFullEnergy R G := by ring
      _ = _ := by rw [hcm, one_mul]
  exact hmul.trans_eq he

/-- Coercivity extends the homogeneous variational bound to zero-mass profiles. -/
theorem criticalHalfLineGroundEnergy_mul_mass_le_all
    {R : ℝ} (hR : 0 < R)
    {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineGroundEnergy R * (∫ u, G u ^ 2) ≤ criticalHalfLineFullEnergy R G := by
  by_cases hm : 0 < ∫ u, G u ^ 2
  · exact criticalHalfLineGroundEnergy_mul_mass_le hR hG hm
  have hm0 : (∫ u, G u ^ 2) = 0 :=
    le_antisymm (le_of_not_gt hm) (integral_nonneg fun u => sq_nonneg _)
  obtain ⟨B, _, hbound⟩ := criticalHalfLineFullEnergy_coercive_remainder hR
  have h := hbound hG
  rw [hm0, mul_zero, add_zero] at h
  rw [hm0, mul_zero]
  exact (mul_nonneg (half_pos (criticalAliasCoefficient_positive hR)).le
    (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)).trans h

/-- The critical state gives the linear upper tangent of the variational floor. -/
theorem criticalHalfLineGroundEnergy_le_critical_tangent
    {W₀ R : ℝ} (hW : 0 < W₀) (hR : 0 < R)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    criticalHalfLineGroundEnergy R ≤
      (criticalAliasCoefficient R - criticalAliasCoefficient W₀) *
        (∫ u, F u ^ 2 * Real.exp (-(8 * u))) := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have h := criticalHalfLineGroundEnergy_le hR hdF hF.2.2.2.1
  rwa [criticalHalfLineFullEnergy_change_ratio R W₀ hdF,
    criticalHalfLineFullEnergy_groundState_eq_zero hW ht hF, zero_add] at h

theorem CriticalHalfLineEnergyDomain.square_mass_le_exponential_mass {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) :
    (∫ u, G u ^ 2) ≤ ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
  apply integral_mono hG.sq hG.exponential
  intro u
  change G u ^ 2 ≤ G u ^ 2 * Real.exp (-(8 * u))
  by_cases hu : 0 ≤ u
  · rw [hG.support u hu, zero_pow two_ne_zero, zero_mul]
  · have he : 1 ≤ Real.exp (-(8 * u)) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
        (show 0 ≤ -(8 * u) by linarith only [lt_of_not_ge hu])
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (sq_nonneg (G u))

/-- Ordinary square mass expands along every full-domain variation. -/
theorem criticalHalfLine_square_mass_add_const_mul {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) (c : ℝ) :
    (∫ u, (F u + c * G u) ^ 2) = (∫ u, F u ^ 2) +
      2 * c * (∫ u, F u * G u) + c ^ 2 * (∫ u, G u ^ 2) := by
  have hcG := hG.const_mul c
  have h := HTGeometry.integral_sq_add hF.meas.aestronglyMeasurable
    hcG.meas.aestronglyMeasurable hF.sq hcG.sq
  have hcross : (∫ u, F u * (c * G u)) = c * ∫ u, F u * G u := by
    have heq : (fun u => F u * (c * G u)) = fun u => c * (F u * G u) :=
      funext fun u => by ring
    rw [heq, integral_const_mul]
  rw [hcross, HTGeometry.integral_sq_const_mul] at h
  exact h.trans (by ring)

/-- Weighted polarization uses the literal exponential cross integral. -/
theorem criticalHalfLine_exponential_mass_add_const_mul {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) (c : ℝ) :
    (∫ u, (F u + c * G u) ^ 2 * Real.exp (-(8 * u))) =
      (∫ u, F u ^ 2 * Real.exp (-(8 * u))) +
        2 * c * criticalHalfLineExponentialPair F G +
        c ^ 2 * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) := by
  have heq : (fun u => (F u + c * G u) ^ 2 * Real.exp (-(8 * u))) =
      fun u => (F u ^ 2 * Real.exp (-(8 * u)) +
        (2 * c) * (F u * G u * Real.exp (-(8 * u)))) +
          c ^ 2 * (G u ^ 2 * Real.exp (-(8 * u))) := by
    funext u
    ring
  have hsum : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)) +
      (2 * c) * (F u * G u * Real.exp (-(8 * u)))) :=
    hF.exponential.add ((hF.integrable_exponentialCross hG).const_mul (2 * c))
  rw [heq, integral_add hsum
    (hG.exponential.const_mul (c ^ 2)),
    integral_add hF.exponential ((hF.integrable_exponentialCross hG).const_mul (2 * c)),
    integral_const_mul, integral_const_mul]
  rfl

/-- The weighted square of a sum is bounded by twice the two diagonal masses. -/
theorem criticalHalfLine_exponential_mass_add_const_mul_le {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) (c : ℝ) :
    (∫ u, (F u + c * G u) ^ 2 * Real.exp (-(8 * u))) ≤
      2 * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) +
        2 * c ^ 2 * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) := by
  have hpos : 0 ≤ ∫ u, (F u + (-c) * G u) ^ 2 * Real.exp (-(8 * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  rw [criticalHalfLine_exponential_mass_add_const_mul hF hG] at hpos ⊢
  nlinarith only [hpos]

/-- Ordinary orthogonal projection splits unit mass into a scalar square and the neutral mass. -/
theorem criticalHalfLineNeutralPart_square_mass {W₀ : ℝ} {F G : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hG : CriticalHalfLineEnergyDomain G)
    (hm : (∫ u, G u ^ 2) = 1) :
    (∫ u, criticalHalfLineNeutralPart F G u ^ 2) = 1 - (∫ u, F u * G u) ^ 2 := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have hpair : Integrable (fun u => F u * G u) := HTGeometry.integrable_mul_of_sq_integrable
    hdF.meas.aestronglyMeasurable hG.meas.aestronglyMeasurable hdF.sq hG.sq
  have heq : (fun u => criticalHalfLineNeutralPart F G u ^ 2) =
      fun u => (G u ^ 2 - (2 * (∫ v, F v * G v)) * (F u * G u)) +
        (∫ v, F v * G v) ^ 2 * F u ^ 2 := by
    funext u
    dsimp only [criticalHalfLineNeutralPart]
    ring
  have hdiff : Integrable (fun u => G u ^ 2 -
      (2 * (∫ v, F v * G v)) * (F u * G u)) := hG.sq.sub (hpair.const_mul _)
  rw [heq, integral_add hdiff (hdF.sq.const_mul _),
    integral_sub hG.sq (hpair.const_mul _), integral_const_mul, integral_const_mul,
    hm, hF.2.2.2.1]
  ring

theorem criticalHalfLine_exponential_mass_neutral_decomposition {W₀ : ℝ} {F G : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hG : CriticalHalfLineEnergyDomain G) :
    (∫ u, G u ^ 2 * Real.exp (-(8 * u))) =
      (∫ u, criticalHalfLineNeutralPart F G u ^ 2 * Real.exp (-(8 * u))) +
        2 * (∫ v, F v * G v) * criticalHalfLineExponentialPair (criticalHalfLineNeutralPart F G) F +
        (∫ v, F v * G v) ^ 2 * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have h := criticalHalfLine_exponential_mass_add_const_mul (hdF.neutralPart hG) hdF
    (∫ v, F v * G v)
  have heq (u : ℝ) : criticalHalfLineNeutralPart F G u + (∫ v, F v * G v) * F u = G u :=
    sub_add_cancel _ _
  simpa only [heq] using h

private theorem tangent_lower_algebra {E E₀ η w m n q c γ : ℝ}
    (hγ : 0 < γ) (hw : 0 ≤ w) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hmn : m ≤ n) (hmass : m = 1 - c ^ 2)
    (he₀ : γ * n ≤ E₀) (he : E = E₀ + η * (n + 2 * c * q + (1 - m) * w))
    (hsmall : |η| * (1 + w) ≤ γ / 2)
    (hpos : 0 ≤ n + 2 * (2 * η * c / γ) * q + (2 * η * c / γ) ^ 2 * w) :
    η * w - (2 * w / γ) * η ^ 2 ≤ E := by
  have hc : c ^ 2 ≤ 1 := by linarith only [hmass, hm]
  have hC : 0 ≤ 2 * w / γ := by positivity
  have hy := mul_nonneg (half_pos hγ).le hpos
  have hid : γ / 2 * (n + 2 * (2 * η * c / γ) * q + (2 * η * c / γ) ^ 2 * w) =
      γ / 2 * n + 2 * η * c * q + (2 * w / γ) * η ^ 2 * c ^ 2 := by
    field_simp [hγ.ne']
  rw [hid] at hy
  have h1 := mul_le_mul_of_nonneg_right (neg_abs_le η) hn
  have h2 := mul_le_mul_of_nonneg_right (le_abs_self η) (mul_nonneg hw hm)
  have h3 := mul_le_mul_of_nonneg_left hmn (mul_nonneg (abs_nonneg η) hw)
  have h4 := mul_le_mul_of_nonneg_right hsmall hn
  have h5 := mul_le_mul_of_nonneg_left hc (mul_nonneg hC (sq_nonneg η))
  nlinarith only [he, he₀, hy, h1, h2, h3, h4, h5]

/-- The transverse gap bounds the loss below the critical tangent by a quadratic error. -/
theorem criticalHalfLineFullEnergy_ge_critical_tangent
    {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ (R : ℝ) (G : ℝ → ℝ),
      CriticalHalfLineEnergyDomain G → (∫ u, G u ^ 2) = 1 →
      |criticalAliasCoefficient R - criticalAliasCoefficient W₀| ≤ δ →
      (criticalAliasCoefficient R - criticalAliasCoefficient W₀) *
        (∫ u, F u ^ 2 * Real.exp (-(8 * u))) -
          C * (criticalAliasCoefficient R - criticalAliasCoefficient W₀) ^ 2 ≤
            criticalHalfLineFullEnergy R G := by
  obtain ⟨γ, hγ, hgap⟩ := criticalHalfLineFullEnergy_controls_neutralPart hW ht hF
  let w : ℝ := ∫ u, F u ^ 2 * Real.exp (-(8 * u))
  have hw : 0 ≤ w := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hC : 0 ≤ 2 * w / γ := div_nonneg (mul_nonneg (by norm_num) hw) hγ.le
  refine ⟨γ / (2 * (1 + w)), 2 * w / γ, by positivity, hC, ?_⟩
  intro R G hG hm hsmall
  let η : ℝ := criticalAliasCoefficient R - criticalAliasCoefficient W₀
  let c : ℝ := ∫ u, F u * G u
  let N : ℝ → ℝ := criticalHalfLineNeutralPart F G
  let m : ℝ := ∫ u, N u ^ 2
  let n : ℝ := ∫ u, N u ^ 2 * Real.exp (-(8 * u))
  let q : ℝ := criticalHalfLineExponentialPair N F
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have hdN : CriticalHalfLineEnergyDomain N := hdF.neutralPart hG
  have hm0 : 0 ≤ m := integral_nonneg fun u => sq_nonneg _
  have hn0 : 0 ≤ n := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hmn : m ≤ n := hdN.square_mass_le_exponential_mass
  have hmass : m = 1 - c ^ 2 := criticalHalfLineNeutralPart_square_mass hF hG hm
  have hc' : c ^ 2 = 1 - m := by linarith only [hmass]
  have he0 : γ * n ≤ criticalHalfLineFullEnergy W₀ G := hgap hG
  have hdecomp : (∫ u, G u ^ 2 * Real.exp (-(8 * u))) = n + 2 * c * q + c ^ 2 * w :=
    criticalHalfLine_exponential_mass_neutral_decomposition hF hG
  have he := criticalHalfLineFullEnergy_change_ratio R W₀ hG
  rw [hdecomp, hc'] at he
  change |η| ≤ γ / (2 * (1 + w)) at hsmall
  have hsmall' : |η| * (1 + w) ≤ γ / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (1 + w))).mp hsmall
    linarith only [h]
  -- Positivity of a weighted square supplies Young's inequality with the gap coefficient.
  have hpos : 0 ≤ ∫ u, (N u + (2 * η * c / γ) * F u) ^ 2 * Real.exp (-(8 * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  rw [criticalHalfLine_exponential_mass_add_const_mul hdN hdF] at hpos
  change 0 ≤ n + 2 * (2 * η * c / γ) * q + (2 * η * c / γ) ^ 2 * w at hpos
  change η * w - (2 * w / γ) * η ^ 2 ≤ criticalHalfLineFullEnergy R G
  change criticalHalfLineFullEnergy R G =
    criticalHalfLineFullEnergy W₀ G + η * (n + 2 * c * q + (1 - m) * w) at he
  exact tangent_lower_algebra hγ hw hm0 hn0 hmn hmass he0 he hsmall' hpos

/-- The variational floor has a quadratic remainder in the confinement coefficient. -/
theorem criticalHalfLineGroundEnergy_quadratic_tangent
    {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      |criticalAliasCoefficient R - criticalAliasCoefficient W₀| ≤ δ →
      |criticalHalfLineGroundEnergy R -
        (criticalAliasCoefficient R - criticalAliasCoefficient W₀) *
          (∫ u, F u ^ 2 * Real.exp (-(8 * u)))| ≤
            C * (criticalAliasCoefficient R - criticalAliasCoefficient W₀) ^ 2 := by
  obtain ⟨δ, C, hδ, hC, hbound⟩ := criticalHalfLineFullEnergy_ge_critical_tangent hW ht hF
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro R hR hsmall
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have hnonempty : ({e : ℝ | ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧
      (∫ u, G u ^ 2) = 1 ∧ criticalHalfLineFullEnergy R G = e} : Set ℝ).Nonempty :=
    ⟨criticalHalfLineFullEnergy R F, F, hdF, hF.2.2.2.1, rfl⟩
  have hlower : (criticalAliasCoefficient R - criticalAliasCoefficient W₀) *
      (∫ u, F u ^ 2 * Real.exp (-(8 * u))) -
        C * (criticalAliasCoefficient R - criticalAliasCoefficient W₀) ^ 2 ≤
          criticalHalfLineGroundEnergy R := by
    apply le_csInf hnonempty
    rintro e ⟨G, hG, hm, rfl⟩
    exact hbound R G hG hm hsmall
  have hupper := criticalHalfLineGroundEnergy_le_critical_tangent hW hR ht hF
  have herr := mul_nonneg hC (sq_nonneg (criticalAliasCoefficient R - criticalAliasCoefficient W₀))
  exact abs_le.mpr ⟨by linarith only [hlower], by linarith only [hupper, herr]⟩

#print axioms criticalHalfLineGroundEnergy_quadratic_tangent

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
