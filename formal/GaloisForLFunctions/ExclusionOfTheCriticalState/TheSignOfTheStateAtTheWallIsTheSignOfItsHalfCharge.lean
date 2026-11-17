import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateAndThePrimeSideHaveExactLogarithmicLawsAtTheWall
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLevyHeadResolvesTheWallCharges

/-!
# The sign of the state at the wall is the sign of its half-charge

Let `F` be the critical state and `𝓛F(σ) = ∫ F(u) e^{σu} du`. The samples `𝓛F(σ)`, `σ ≥ ½`, all
have the sign of the half-charge `𝓛F(½)`. The sign at the wall is that sign:

* `𝓛F(½) · ∫_{−k}^0 F > 0` and `𝓛F(½) · ∫_{v>k} F(−v)/v dv > 0` for every small `k > 0`
  (`criticalState_eventually_halfCharge_mul_terminalMass_pos`);
* `𝓛F(½) · Re F⁺(x) < 0` for almost every small `x > 0`
  (`criticalState_exists_ae_halfCharge_mul_beyondWall_neg`): at the wall the prime side is
  anti-oriented to the half-charge.

Mechanism. Fubini on `v < h` writes the transform as a Laplace average of the terminal mass,
`𝓛F(σ) = σ ∫_{h>0} (∫_{−h}^0 F) e^{−σh} dh`. The terminal mass has the sign `s` of the wall on
`(0, δ)`, is bounded below on `[δ/4, δ/2]` and bounded by `∫|F|` everywhere, so
`s 𝓛F(σ) ≥ σ e^{−σδ/2} (c δ/4 − σ⁻¹ ∫|F|) > 0` for large `σ`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The transform as a Laplace average of the terminal mass -/

theorem integral_Ioi_exp_neg_mul {σ : ℝ} (hσ : 0 < σ) (v : ℝ) :
    ∫ h in Ioi v, Real.exp (-(σ * h)) = Real.exp (-(σ * v)) / σ := by
  have h := integral_exp_mul_Ioi (neg_lt_zero.mpr hσ) v
  simp only [neg_mul] at h
  rw [h, neg_div_neg_eq]

theorem integrableOn_Ioi_exp_neg_mul {σ : ℝ} (hσ : 0 < σ) (v : ℝ) :
    IntegrableOn (fun h : ℝ => Real.exp (-(σ * h))) (Ioi v) := by
  have h := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hσ) v
  simpa only [neg_mul] using h

/-- **The transform is a Laplace average of the terminal mass.** For a profile carried by `u < 0`
and `σ > 0`, `∫ F(u) e^{σu} du = σ ∫_{h>0} (∫_{−h}^0 F) e^{−σh} dh`. -/
theorem integral_mul_exp_eq_laplace_terminalMass {F : ℝ → ℝ} (hFi : Integrable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {σ : ℝ} (hσ : 0 < σ) :
    ∫ u, F u * Real.exp (σ * u) =
      σ * ∫ h in Ioi (0 : ℝ), (∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h)) := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hfi : Integrable fun v : ℝ => F (-v) := hFi.comp_neg
  have hswap := integral_Ioi_mul_integral_Ioi_eq (f := fun v => F (-v))
    (w := fun h => Real.exp (-(σ * h))) (k := 0) hfi.integrableOn
    (integrableOn_Ioi_exp_neg_mul hσ 0)
  have h1 : ∫ u, F u * Real.exp (σ * u) = ∫ v in Ioi (0 : ℝ), F (-v) * Real.exp (-(σ * v)) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => by
      have hv' : v ≤ 0 := not_lt.mp (show ¬ (0 : ℝ) < v from hv)
      rw [hsupp (-v) (by linarith), zero_mul]]
    rw [← integral_neg_eq_self (fun u : ℝ => F u * Real.exp (σ * u)) volume]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    show F (-v) * Real.exp (σ * -v) = F (-v) * Real.exp (-(σ * v))
    rw [mul_neg]
  have h2 : ∫ v in Ioi (0 : ℝ), F (-v) * (∫ h in Ioi v, Real.exp (-(σ * h))) =
      (∫ v in Ioi (0 : ℝ), F (-v) * Real.exp (-(σ * v))) / σ := by
    rw [← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    show F (-v) * (∫ h in Ioi v, Real.exp (-(σ * h))) = F (-v) * Real.exp (-(σ * v)) / σ
    rw [integral_Ioi_exp_neg_mul hσ v, mul_div_assoc]
  have h3 : ∫ h in Ioi (0 : ℝ), (∫ v in Ioo 0 h, F (-v)) * Real.exp (-(σ * h)) =
      ∫ h in Ioi (0 : ℝ), (∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
    show (∫ v in Ioo 0 h, F (-v)) * Real.exp (-(σ * h)) =
      (∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h))
    rw [setIntegral_Ioo_neg F 0 h, neg_zero]
  have e : ∀ X : ℝ, σ * (X / σ) = X := fun X => by field_simp
  rw [h1, ← h3, ← hswap, h2, e]

/-- **A one-signed terminal mass orients the transform at large real points.** If
`s ∫_{−h}^0 F > 0` on `0 < h < δ`, then `s ∫ F(u) e^{σu} du > 0` for all large `σ`. -/
theorem exists_forall_pos_mul_integral_mul_exp {F : ℝ → ℝ} (hFi : Integrable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {s δ : ℝ} (hs : s = 1 ∨ s = -1) (hδ : 0 < δ)
    (hpos : ∀ h ∈ Ioo (0 : ℝ) δ, 0 < s * ∫ u in Ioo (-h) 0, F u) :
    ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ → 0 < s * ∫ u, F u * Real.exp (σ * u) := by
  have habs : |s| = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hcont : ContinuousOn (fun h : ℝ => s * ∫ u in Ioo (-h) 0, F u) (Icc (δ / 4) (δ / 2)) :=
    (continuousOn_const.mul (continuousOn_terminalMass hFi)).mono fun h hh =>
      show (0 : ℝ) ≤ h by linarith [hh.1]
  obtain ⟨h₀, hh₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by linarith)) hcont
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : ℝ, c₁ = s * ∫ u in Ioo (-h₀) 0, F u := ⟨_, rfl⟩
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    exact hpos h₀ ⟨by linarith [hh₀.1], by linarith [hh₀.2]⟩
  have hmin' : ∀ h ∈ Icc (δ / 4) (δ / 2), c₁ ≤ s * ∫ u in Ioo (-h) 0, F u := by
    intro h hh
    rw [hc₁def]
    exact isMinOn_iff.mp hmin h hh
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∫ u, |F u| := ⟨_, rfl⟩
  have hA : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg fun u => abs_nonneg _
  have hbd : ∀ h : ℝ, |s * ∫ u in Ioo (-h) 0, F u| ≤ A := by
    intro h
    rw [abs_mul, habs, one_mul, hAdef]
    exact abs_terminalMass_le hFi h
  have hden : 0 < c₁ * (δ / 4) := by positivity
  refine ⟨A / (c₁ * (δ / 4)) + 1, fun σ hσ => ?_⟩
  have hσ0 : 0 < σ := lt_of_lt_of_le (by positivity) hσ
  have hσA : A < σ * (c₁ * (δ / 4)) := (div_lt_iff₀ hden).mp (by linarith)
  have hE := Real.exp_pos (-(σ * (δ / 2)))
  -- the integrand `s (∫_{−h}^0 F) e^{−σh}` on `h > 0`
  have hGi : IntegrableOn
      (fun h : ℝ => s * ((∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h)))) (Ioi 0) := by
    have hGc : ContinuousOn
        (fun h : ℝ => s * ((∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h)))) (Ioi 0) :=
      continuousOn_const.mul (((continuousOn_terminalMass hFi).mono Ioi_subset_Ici_self).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn)
    refine Integrable.mono' ((integrableOn_Ioi_exp_neg_mul hσ0 0).const_mul A)
      (hGc.aestronglyMeasurable measurableSet_Ioi) (Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs, ← mul_assoc, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hbd h) (Real.exp_pos _).le
  have hsub : Ioc (δ / 4) (δ / 2) ⊆ Ioi (0 : ℝ) := fun x hx =>
    lt_of_le_of_lt (by positivity) hx.1
  have e1 : ∫ h in Ioi (0 : ℝ), s * ((∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h))) =
      (∫ h in Ioc (0 : ℝ) (δ / 2), s * ((∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h)))) +
        ∫ h in Ioi (δ / 2), s * ((∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h))) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ δ / 2 by positivity),
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hGi.mono_set Ioc_subset_Ioi_self) (hGi.mono_set (Ioi_subset_Ioi (by positivity)))]
  have e2 : ∫ h in Ioc (0 : ℝ) (δ / 2), s * ((∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h))) =
      (∫ h in Ioc (0 : ℝ) (δ / 4), s * ((∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h)))) +
        ∫ h in Ioc (δ / 4) (δ / 2), s * ((∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h))) := by
    rw [← Ioc_union_Ioc_eq_Ioc (show (0 : ℝ) ≤ δ / 4 by positivity)
        (show δ / 4 ≤ δ / 2 by linarith),
      setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => not_lt.mpr hx.2 hx'.1)
        measurableSet_Ioc (hGi.mono_set Ioc_subset_Ioi_self) (hGi.mono_set hsub)]
  -- near the wall the integrand is nonnegative
  have b1 : 0 ≤ ∫ h in Ioc (0 : ℝ) (δ / 4),
      s * ((∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h))) := by
    refine setIntegral_nonneg measurableSet_Ioc fun h hh => ?_
    have hp := hpos h ⟨hh.1, by linarith [hh.2]⟩
    rw [← mul_assoc]
    exact mul_nonneg hp.le (Real.exp_pos _).le
  -- on `(δ/4, δ/2]` it is bounded below
  have b2 : c₁ * Real.exp (-(σ * (δ / 2))) * (δ / 4) ≤ ∫ h in Ioc (δ / 4) (δ / 2),
      s * ((∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h))) := by
    have hconst : ∫ _h in Ioc (δ / 4) (δ / 2), c₁ * Real.exp (-(σ * (δ / 2))) =
        c₁ * Real.exp (-(σ * (δ / 2))) * (δ / 4) := by
      rw [← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const,
        smul_eq_mul]
      ring
    rw [← hconst]
    refine setIntegral_mono_on (integrable_const _) (hGi.mono_set hsub) measurableSet_Ioc
      fun h hh => ?_
    have h1 := hmin' h ⟨hh.1.le, hh.2⟩
    have h2 : Real.exp (-(σ * (δ / 2))) ≤ Real.exp (-(σ * h)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hh.2 hσ0.le))
    rw [← mul_assoc]
    exact mul_le_mul h1 h2 hE.le (hc₁.le.trans h1)
  -- beyond `δ/2` it is bounded by `∫|F|`
  have b3 : -(A * (Real.exp (-(σ * (δ / 2))) / σ)) ≤ ∫ h in Ioi (δ / 2),
      s * ((∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h))) := by
    have hconst : ∫ h in Ioi (δ / 2), -(A * Real.exp (-(σ * h))) =
        -(A * (Real.exp (-(σ * (δ / 2))) / σ)) := by
      rw [integral_neg, integral_const_mul, integral_Ioi_exp_neg_mul hσ0 (δ / 2)]
    rw [← hconst]
    refine setIntegral_mono_on ((integrableOn_Ioi_exp_neg_mul hσ0 (δ / 2)).const_mul A).neg
      (hGi.mono_set (Ioi_subset_Ioi (by positivity))) measurableSet_Ioi fun h _ => ?_
    have h1 := hbd h
    have h2 := neg_abs_le (s * ∫ u in Ioo (-h) 0, F u)
    have h3 := mul_nonneg (show 0 ≤ s * (∫ u in Ioo (-h) 0, F u) + A by linarith)
      (Real.exp_pos (-(σ * h))).le
    show -(A * Real.exp (-(σ * h))) ≤ s * ((∫ u in Ioo (-h) 0, F u) * Real.exp (-(σ * h)))
    rw [← mul_assoc]
    linarith
  have h4 : A / σ < c₁ * (δ / 4) := by
    rw [div_lt_iff₀ hσ0]
    linarith
  have key : 0 < c₁ * Real.exp (-(σ * (δ / 2))) * (δ / 4) -
      A * (Real.exp (-(σ * (δ / 2))) / σ) := by
    have e : c₁ * Real.exp (-(σ * (δ / 2))) * (δ / 4) - A * (Real.exp (-(σ * (δ / 2))) / σ) =
        Real.exp (-(σ * (δ / 2))) * (c₁ * (δ / 4) - A / σ) := by ring
    rw [e]
    exact mul_pos hE (by linarith)
  rw [integral_mul_exp_eq_laplace_terminalMass hFi hsupp hσ0, ← mul_assoc, mul_comm s σ, mul_assoc,
    ← integral_const_mul]
  refine mul_pos hσ0 ?_
  rw [e1, e2]
  linarith

/-! ### The critical state -/

/-- **The sign of the state at the wall is the sign of its half-charge.** For every small
`k > 0`, `𝓛F(½) ∫_{−k}^0 F > 0` and `𝓛F(½) ∫_{v>k} F(−v)/v dv > 0`. -/
theorem criticalState_eventually_halfCharge_mul_terminalMass_pos {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∀ᶠ k : ℝ in 𝓝[>] 0,
      0 < (negativeHalfLineLaplace (cx F) (1 / 2)).re * ∫ u in Ioo (-k) 0, F u ∧
        0 < (negativeHalfLineLaplace (cx F) (1 / 2)).re * wallLogMoment F k := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨s, hs, hev⟩ := criticalState_exists_sign_at_wall hW hthreshold hF
  have hss : s * s = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  have hpos : ∀ h ∈ Ioo (0 : ℝ) δ,
      0 < s * ∫ u in Ioo (-h) 0, F u ∧ 0 < s * wallLogMoment F h := fun h hh =>
    hδP (by rw [Real.dist_eq, sub_zero, abs_of_pos hh.1]; exact hh.2) hh.1
  obtain ⟨σ₀, hσ₀⟩ := exists_forall_pos_mul_integral_mul_exp hd.integrable hd.support hs hδ
    fun h hh => (hpos h hh).1
  have hσpos := hσ₀ (max σ₀ (1 / 2)) (le_max_left _ _)
  have hch := criticalState_laplace_half_mul_pos hW hthreshold hF (s := max σ₀ (1 / 2))
    (le_max_right _ _)
  rw [negativeHalfLineLaplace_ofReal, Complex.ofReal_re] at hch
  have hcs : 0 < (negativeHalfLineLaplace (cx F) (1 / 2)).re * s := by
    have hI : (∫ u, F u * Real.exp (max σ₀ (1 / 2) * u)) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hσpos
      exact lt_irrefl _ hσpos
    have hprod : 0 < (negativeHalfLineLaplace (cx F) (1 / 2)).re * s *
        ((∫ u, F u * Real.exp (max σ₀ (1 / 2) * u)) *
          ∫ u, F u * Real.exp (max σ₀ (1 / 2) * u)) := by
      have h := mul_pos hch hσpos
      calc (0 : ℝ) < (negativeHalfLineLaplace (cx F) (1 / 2)).re *
            (∫ u, F u * Real.exp (max σ₀ (1 / 2) * u)) *
              (s * ∫ u, F u * Real.exp (max σ₀ (1 / 2) * u)) := h
        _ = _ := by ring
    exact (pos_iff_pos_of_mul_pos hprod).mpr (mul_self_pos.mpr hI)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)]
    with k hk hkδ
  obtain ⟨h1, h2⟩ := hpos k ⟨hk, hkδ⟩
  constructor
  · have e : (negativeHalfLineLaplace (cx F) (1 / 2)).re * (∫ u in Ioo (-k) 0, F u) =
        (negativeHalfLineLaplace (cx F) (1 / 2)).re * s * (s * ∫ u in Ioo (-k) 0, F u) := by
      linear_combination
        (-((negativeHalfLineLaplace (cx F) (1 / 2)).re * ∫ u in Ioo (-k) 0, F u)) * hss
    rw [e]
    exact mul_pos hcs h1
  · have e : (negativeHalfLineLaplace (cx F) (1 / 2)).re * wallLogMoment F k =
        (negativeHalfLineLaplace (cx F) (1 / 2)).re * s * (s * wallLogMoment F k) := by
      linear_combination (-((negativeHalfLineLaplace (cx F) (1 / 2)).re * wallLogMoment F k)) * hss
    rw [e]
    exact mul_pos hcs h2

/-- **At the wall the prime side is anti-oriented to the half-charge.** For almost every small
`x > 0`, `𝓛F(½) · Re F⁺(x) < 0`. -/
theorem criticalState_exists_ae_halfCharge_mul_beyondWall_neg {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) δ)),
      (negativeHalfLineLaplace (cx F) (1 / 2)).re *
        (beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x).re < 0 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := criticalAliasCoefficient_positive hW
  have hM := criticalState_exponentialMass_pos hW hF
  obtain ⟨s, hs, hev, -, -, hprime⟩ := criticalState_wall_laws hW hthreshold hF
  have hss : s * s = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  -- the sign of the wall is the sign of the half-charge
  obtain ⟨k, hk1, hk2⟩ := (hev.and
    (criticalState_eventually_halfCharge_mul_terminalMass_pos hW hthreshold hF)).exists
  have hcs : 0 < (negativeHalfLineLaplace (cx F) (1 / 2)).re * s := by
    have hμ : (∫ u in Ioo (-k) 0, F u) ≠ 0 := fun h0 => by
      have h := hk1.1
      rw [h0, mul_zero] at h
      exact lt_irrefl _ h
    have hprod : 0 < (negativeHalfLineLaplace (cx F) (1 / 2)).re * s *
        ((∫ u in Ioo (-k) 0, F u) * ∫ u in Ioo (-k) 0, F u) := by
      have h := mul_pos hk2.1 hk1.1
      calc (0 : ℝ) < (negativeHalfLineLaplace (cx F) (1 / 2)).re * (∫ u in Ioo (-k) 0, F u) *
            (s * ∫ u in Ioo (-k) 0, F u) := h
        _ = _ := by ring
    exact (pos_iff_pos_of_mul_pos hprod).mpr (mul_self_pos.mpr hμ)
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Real.sqrt (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) := ⟨_, rfl⟩
  have ht : 0 < t := by
    rw [htdef]
    exact Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) ha) hM)
  rw [← htdef] at hprime
  obtain ⟨δ, hδ, hae⟩ := hprime (t / 2) (half_pos ht)
  refine ⟨min δ 1, lt_min hδ one_pos, ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo le_rfl (min_le_left δ 1)) hae,
    ae_restrict_mem measurableSet_Ioo] with x hx hmem
  have hw : 0 < Real.sqrt (Real.log (1 / x)) :=
    Real.sqrt_pos.mpr (Real.log_pos (one_lt_one_div hmem.1 (hmem.2.trans_le (min_le_right _ _))))
  have hre := (Complex.abs_re_le_norm _).trans_lt hx
  rw [Complex.add_re, Complex.ofReal_re, Complex.div_ofReal_re, Complex.re_ofReal_mul] at hre
  have h6 := abs_lt.mp hre
  have h5 : s * (criticalAliasCoefficient W₀ * (beyondWallProfile W₀ hd x).re /
      Real.sqrt (Real.log (1 / x))) < 0 := by
    rcases hs with h | h <;> rw [h] at h6 ⊢ <;> linarith [h6.1, h6.2]
  have h7 : s * (beyondWallProfile W₀ hd x).re < 0 := by
    by_contra hcon
    have e : s * (criticalAliasCoefficient W₀ * (beyondWallProfile W₀ hd x).re /
        Real.sqrt (Real.log (1 / x))) =
        s * (beyondWallProfile W₀ hd x).re *
          (criticalAliasCoefficient W₀ / Real.sqrt (Real.log (1 / x))) := by ring
    rw [e] at h5
    exact absurd h5 (not_lt.mpr (mul_nonneg (not_lt.mp hcon) (div_pos ha hw).le))
  have e : (negativeHalfLineLaplace (cx F) (1 / 2)).re * (beyondWallProfile W₀ hd x).re =
      (negativeHalfLineLaplace (cx F) (1 / 2)).re * s * (s * (beyondWallProfile W₀ hd x).re) := by
    linear_combination (-((negativeHalfLineLaplace (cx F) (1 / 2)).re * (beyondWallProfile W₀ hd x).re)) * hss
  show (negativeHalfLineLaplace (cx F) (1 / 2)).re * (beyondWallProfile W₀ hd x).re < 0
  rw [e]
  exact mul_neg_of_pos_of_neg hcs h7

end GaloisForLFunctions.ExclusionOfTheCriticalState
