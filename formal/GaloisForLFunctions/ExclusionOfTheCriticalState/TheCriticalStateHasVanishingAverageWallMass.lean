import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineGroundEnergy
import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.ExactBregmanBoundaryBalance
import GaloisForLFunctions.HTGeometry.Analysis.VanishingCumulativeLaplaceBound

/-!
# Vanishing average square mass at the critical wall

The reversed residual of a causal translate agrees with the state in its
terminal interval. The spectral gap bounds its square mass, and the exact
translation identity bounds its full energy. Exponential coercivity then
controls its Lévy energy. The logarithmic boundary inequality gives
`log(2/h) ∫(-h,0) F² ≤ C h`.

Thus the average square mass vanishes at the wall. Truncation and weighted
Cauchy–Schwarz imply `σ |LF(σ+iy)| → 0`, uniformly in the height `y`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower WeilLevyPoleGauss

private theorem levyEnergy_le_fullEnergy_add_mass {R : ℝ} (hR : 0 < R) :
    ∃ L M : ℝ, 0 < L ∧ 0 ≤ M ∧ ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
      levyEnergy G ≤ L * criticalHalfLineFullEnergy R G + M * (∫ u, G u ^ 2) := by
  obtain ⟨B, hB, hco⟩ := criticalHalfLineFullEnergy_coercive_remainder hR
  let C : ℝ := 2 * vonMangoldtThreeHalvesMass + 2 * (∫ u : ℝ, Real.exp (-|u|))
  have hC : 0 ≤ C := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) vonMangoldtThreeHalvesMass_nonneg
    · exact mul_nonneg (by norm_num) (integral_nonneg fun u => (Real.exp_pos _).le)
  let a : ℝ := criticalAliasCoefficient R / 2
  have ha : 0 < a := half_pos (criticalAliasCoefficient_positive hR)
  refine ⟨1+C/a, C+2*|gammaHardyPhaseRate 0|+C/a*B, by positivity, by positivity, ?_⟩
  intro G hG
  have hm : 0 ≤ ∫ u, G u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hw : 0 ≤ ∫ u, G u ^ 2 * Real.exp (-(8*u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hs : exponentialSourceMass G ≤ (∫ u, G u ^ 2) +
      ∫ u, G u ^ 2 * Real.exp (-(8*u)) := by
    have h := (exponentialSourceMass_le_of_support (Y := 0) (by norm_num)
      hG.meas.aestronglyMeasurable hG.sq hG.exponential
      (Eventually.of_forall fun u hu => hG.support u hu.le)).2
    simpa only [mul_zero, neg_zero, Real.exp_zero, one_mul] using h
  have hweight : (∫ u, G u ^ 2 * Real.exp (-(8*u))) ≤
      (criticalHalfLineFullEnergy R G + B * (∫ u, G u ^ 2)) / a := by
    apply (le_div_iff₀ ha).mpr
    simpa only [a, mul_comm] using hco hG
  have hp := (le_abs_self (primeSum G)).trans hG.prime_bound
  have hsin := hG.sinh_bound
  have hγ := mul_le_mul_of_nonneg_right (neg_abs_le (gammaHardyPhaseRate 0)) hm
  have hconf := mul_nonneg (criticalAliasCoefficient_positive hR).le hw
  have he : criticalHalfLineFullEnergy R G =
      2*gammaHardyPhaseRate 0*(∫ u, G u^2) + levyEnergy G +
        2*coshHalfMoment G^2 - 2*sinhHalfMoment G^2 - primeSum G +
          criticalAliasCoefficient R*(∫ u,G u^2*Real.exp (-(8*u))) := by
    unfold criticalHalfLineFullEnergy
    rw [halfLineExpMass_eq_full hG.support, hG.archForm_eq_levyEnergy]
    ring
  have hb : levyEnergy G ≤ criticalHalfLineFullEnergy R G +
      C * exponentialSourceMass G + 2*|gammaHardyPhaseRate 0| * (∫ u,G u^2) := by
    dsimp only [C]
    nlinarith only [he, hp, hsin, hγ, hconf, sq_nonneg (coshHalfMoment G)]
  have hsw := hs.trans (add_le_add (le_refl (∫ u, G u^2)) hweight)
  calc
    levyEnergy G ≤ criticalHalfLineFullEnergy R G + C * exponentialSourceMass G +
        2*|gammaHardyPhaseRate 0| * (∫ u,G u^2) := hb
    _ ≤ criticalHalfLineFullEnergy R G + C * ((∫ u,G u^2) +
        (criticalHalfLineFullEnergy R G+B*(∫ u,G u^2))/a) +
          2*|gammaHardyPhaseRate 0| * (∫ u,G u^2) :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsw hC)) le_rfl
    _ = _ := by ring

private theorem reversed_translate_levy_bound {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ K : ℝ, 0 < K ∧ ∀ h : ℝ, 0 ≤ h →
      levyEnergy (fun u => F u + (-(∫ v, F v*F (v+h)))*F (u+h)) ≤
        K * (Real.exp (8*h)-1) := by
  obtain ⟨δ, hδ, hgap⟩ := criticalHalfLineFullEnergy_transverse_L2_gap hW ht hF
  obtain ⟨L, M, hL, hM, hlevy⟩ := levyEnergy_le_fullEnergy_add_mass hW
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  let A : ℝ := criticalAliasCoefficient W₀ * criticalHalfLineExponentialPair F F
  have hA : 0 ≤ A := by
    apply mul_nonneg (criticalAliasCoefficient_positive hW).le
    rw [criticalHalfLineExponentialPair_self]
    exact integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  refine ⟨1+(L+M/δ)*A, by positivity, fun h hh => ?_⟩
  have hT := hd.causalTranslate hh
  have hTmass : (∫ u, F (u+h)^2) = 1 := by
    rw [integral_add_right_eq_self (fun u => F u^2) h, hF.2.2.2.1]
  let c : ℝ := ∫ v, F v*F (v+h)
  let J : ℝ → ℝ := fun u => F u+(-c)*F (u+h)
  have hJ : CriticalHalfLineEnergyDomain J := hd.add_const_mul hT (-c)
  have hmass : (∫ u,J u^2) = 1-c^2 := by
    rw [criticalHalfLine_square_mass_add_const_mul hd hT, hF.2.2.2.1, hTmass]
    change 1+2*(-c)*c+(-c)^2*1 = 1-c^2
    ring
  have hc : c^2 ≤ 1 := by
    have hm : 0 ≤ ∫ u, J u^2 := integral_nonneg (fun u => sq_nonneg (J u))
    rw [hmass] at hm
    linarith only [hm]
  have hE : criticalHalfLineFullEnergy W₀ (fun u => F (u+h)) =
      A*(Real.exp (8*h)-1) := by
    have he := criticalHalfLineFullEnergy_causal_ground_shear hW ht hF hd hh 0
    simp only [zero_mul, add_zero, criticalHalfLineFullEnergy_groundState_eq_zero hW ht hF,
      zero_add] at he
    rw [he]
    dsimp only [A]
    ring
  have hneutral := hgap (hd.neutralPart hT) (criticalHalfLineNeutralPart_orthogonal hF hT)
  rw [criticalHalfLineNeutralPart_square_mass hF hT hTmass,
    criticalHalfLineFullEnergy_neutralPart hW ht hF hT, hE] at hneutral
  have hmb : (∫ u,J u^2) ≤ A*(Real.exp (8*h)-1)/δ := by
    rw [hmass]
    exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hneutral)
  have hJE : criticalHalfLineFullEnergy W₀ J = c^2*(A*(Real.exp (8*h)-1)) := by
    rw [criticalHalfLineFullEnergy_add_const_mul W₀ hd hT,
      criticalHalfLineFullEnergy_groundState_eq_zero hW ht hF,
      criticalHalfLineMixedEnergy_groundState_eq_zero hW ht hF hT, hE]
    ring
  have hexp : 0 ≤ Real.exp (8*h)-1 := sub_nonneg.mpr
    (Real.one_le_exp_iff.mpr (by positivity))
  have hjb : criticalHalfLineFullEnergy W₀ J ≤ A*(Real.exp (8*h)-1) := by
    rw [hJE]
    exact mul_le_of_le_one_left (mul_nonneg hA hexp) hc
  have hb := (hlevy hJ).trans (add_le_add
    (mul_le_mul_of_nonneg_left hjb hL.le) (mul_le_mul_of_nonneg_left hmb hM))
  change levyEnergy J ≤ _
  calc
    _ ≤ L*(A*(Real.exp (8*h)-1))+M*(A*(Real.exp (8*h)-1)/δ) := hb
    _ = ((L+M/δ)*A)*(Real.exp (8*h)-1) := by ring
    _ ≤ (Real.exp (8*h)-1)+((L+M/δ)*A)*(Real.exp (8*h)-1) :=
      le_add_of_nonneg_left hexp
    _ = _ := by ring

/-- The critical state's terminal mass gains a logarithm over the linear bound. -/
theorem criticalState_terminal_square_mass_logarithmic_gain {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      Real.log (2/h)*(∫ u in Ioo (-h) 0,F u^2) ≤ C*h := by
  obtain ⟨K,hK,hbound⟩ := reversed_translate_levy_bound hW ht hF
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  refine ⟨2*K*(8*Real.exp 8),by positivity,fun h hh h1 => ?_⟩
  let c : ℝ := ∫ v, F v*F (v+h)
  have hJ := hd.add_const_mul (hd.causalTranslate hh.le) (-c)
  have he : (∫ u in Ioo (-h) 0,(F u+(-c)*F (u+h))^2) =
      ∫ u in Ioo (-h) 0,F u^2 := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    change (F u+(-c)*F (u+h))^2 = F u^2
    rw [hd.support (u+h) (by linarith only [hu.1]),mul_zero,add_zero]
  have hb := terminal_square_logarithmic_boundary_bound hJ hh h1
  rw [he] at hb
  have hlevy := hbound h hh.le
  have hx := Real.add_one_le_exp (-(8*h))
  have hm := mul_le_mul_of_nonneg_right hx (Real.exp_pos (8*h)).le
  have hinv : Real.exp (-(8*h))*Real.exp (8*h)=1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  rw [hinv] at hm
  have hex := Real.exp_le_exp.mpr (show 8*h ≤ (8:ℝ) by linarith only [h1])
  have hx' := mul_le_mul_of_nonneg_left hex (show 0 ≤ 8*h by positivity)
  have hlin : Real.exp (8*h)-1 ≤ (8*Real.exp 8)*h := by nlinarith only [hm,hx']
  have hk := mul_le_mul_of_nonneg_left hlin hK.le
  change levyEnergy (fun u => F u+(-c)*F (u+h)) ≤ _ at hlevy
  nlinarith only [hb,hlevy,hk]

/-- The critical state has zero terminal trace in the average-square sense. -/
theorem criticalState_terminal_average_tendsto_zero {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun h : ℝ => (∫ u in Ioo (-h) 0,F u^2)/h) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C,_,hb⟩ := criticalState_terminal_square_mass_logarithmic_gain hW ht hF
  exact terminal_average_tendsto_zero_of_log_bound
    (fun h _ => integral_nonneg fun u => sq_nonneg (F u)) hb

private theorem norm_laplace_le_absolute_real_integral (F : ℝ → ℝ) (z : ℂ) :
    ‖negativeHalfLineLaplace (cx F) z‖ ≤ ∫ u,|F u| *Real.exp (z.re*u) := by
  change ‖∫ u : ℝ,Complex.exp (z*(u:ℂ))*(F u:ℂ)‖ ≤ _
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    change ‖Complex.exp (z*(u:ℂ))*(F u:ℂ)‖ = |F u| *Real.exp (z.re*u)
    rw [norm_mul,Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs]
    have hre : (z*(u:ℂ)).re = z.re*u := by
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    rw [hre,mul_comm]

/-- The inverse-linear Laplace scale vanishes uniformly throughout far-right half-planes. -/
theorem criticalState_uniform_right_laplace_o_inv {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, T ≤ z.re →
      z.re * ‖negativeHalfLineLaplace (cx F) z‖ < ε := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hmean : Tendsto (fun h : ℝ => (∫ u in Ioo (-h) 0,|F u| ^2)/h)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [sq_abs] using criticalState_terminal_average_tendsto_zero hW ht hF
  have hdecay := tendsto_mul_laplace_of_vanishing_terminal_square_average
    hd.meas.abs hd.integrable.abs (by simpa only [sq_abs] using hd.sq)
    (fun u hu => by rw [hd.support u hu,abs_zero]) hmean
  have hn (t : ℝ) : 0 ≤ ∫ u,|F u| *Real.exp (t*u) :=
    integral_nonneg fun u => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have he : (fun t : ℝ => t*|∫ u,|F u| *Real.exp (t*u)|) =
      fun t : ℝ => t*(∫ u,|F u| *Real.exp (t*u)) := by
    funext t
    rw [abs_of_nonneg (hn t)]
  rw [he] at hdecay
  intro ε hε
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hdecay.eventually_lt_const hε)
  refine ⟨max 1 T,lt_of_lt_of_le zero_lt_one (le_max_left _ _),fun z hz => ?_⟩
  have hz0 : 0 < z.re := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hz)
  exact (mul_le_mul_of_nonneg_left (norm_laplace_le_absolute_real_integral F z) hz0.le).trans_lt
    (hT z.re ((le_max_right _ _).trans hz))

/-- The unconditional critical-state alternative includes zero mean-square wall trace
and uniform little-o inverse-linear decay of the transform. -/
theorem riemannHypothesis_or_criticalState_vanishing_wall_trace :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      (∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
        Real.log (2/h)*(∫ u in Ioo (-h) 0,F u^2) ≤ C*h) ∧
      Tendsto (fun h : ℝ => (∫ u in Ioo (-h) 0,F u^2)/h) (𝓝[>] 0) (𝓝 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, T ≤ z.re →
        z.re * ‖negativeHalfLineLaplace (cx F) z‖ < ε) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl h
  · exact Or.inr ⟨W₀,F,hW,ht,hF,criticalState_terminal_square_mass_logarithmic_gain hW ht hF,
      criticalState_terminal_average_tendsto_zero hW ht hF,
      criticalState_uniform_right_laplace_o_inv hW ht hF⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
