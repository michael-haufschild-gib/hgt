/-
# The uniform-flank quiet-crossing producer

The carrier-mass interface of `PerronCarrierFlankMass` is discharged here from the two classical
contour hypotheses: a uniform supremum bound `‖F s‖ ≤ H M` on every left region `-M ≤ Re s ≤ 1-c`,
and a height exhaustion `T k → ∞` on which the carrier is quiet in the strip `1-c ≤ Re s ≤ c` at
order `o(T k ²)`.

The Cauchy weight `(1+y²)⁻¹` contributes exactly `π` on the left line, so a uniform flank envelope
`H` produces the normalized carrier mass of envelope `2H`; on the horizontal edges the entire
Perron regularization decays quadratically in the height, so the quiet bound makes both edges
vanish.  Composing with the carrier-mass support theorem gives the exact growth-to-support
inequality: a geometric flank envelope of radius `R` forces every nonzero Dirichlet coefficient
index to satisfy `n ≤ R`.
-/
import GaloisForLFunctions.RHTower.PerronCarrierFlankMass

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Asymptotics intervalIntegral Set
open scoped Topology Interval

/-- A uniform supremum bound on the left flank line gives the weighted carrier mass, with the
Cauchy weight contributing exactly `π`. -/
theorem hasPerronCarrierFlankMassAt_of_uniform_flank
    {F : ℂ → ℂ} {M : ℕ} {A : ℝ} (hF : Continuous F)
    (hbd : ∀ y : ℝ, ‖F (↑(-(M : ℝ)) + ↑y * I)‖ ≤ A) :
    HasPerronCarrierFlankMassAt F M (Real.pi * A) := by
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hbd 0)
  have hmeas : Continuous (perronCarrierFlankWeight F M) := by
    unfold perronCarrierFlankWeight
    have hnum : Continuous fun y : ℝ => ‖F (↑(-(M : ℝ)) + ↑y * I)‖ :=
      (hF.comp (by fun_prop)).norm
    exact hnum.div (by fun_prop) (fun y => by positivity)
  have hdom : ∀ y : ℝ, ‖perronCarrierFlankWeight F M y‖ ≤ A * (1 + y ^ (2 : ℕ))⁻¹ := by
    intro y
    have hpos : (0 : ℝ) < 1 + y ^ (2 : ℕ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold perronCarrierFlankWeight; positivity)]
    unfold perronCarrierFlankWeight
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hbd y) (by positivity)
  have hint : Integrable (perronCarrierFlankWeight F M) :=
    (integrable_inv_one_add_sq.const_mul A).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall hdom)
  refine ⟨hint, ?_⟩
  calc (∫ y : ℝ, perronCarrierFlankWeight F M y)
      ≤ ∫ y : ℝ, A * (1 + y ^ (2 : ℕ))⁻¹ := by
        refine integral_mono hint (integrable_inv_one_add_sq.const_mul A) ?_
        intro y
        have := hdom y
        rw [Real.norm_eq_abs, abs_of_nonneg (by unfold perronCarrierFlankWeight; positivity)] at this
        exact this
    _ = Real.pi * A := by
        rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
        ring

/-- Eventually uniform left-flank bounds give the normalized carrier flank mass with envelope
`2 H`. -/
theorem hasPerronCarrierFlankMass_of_uniform_flank
    {F : ℂ → ℂ} {H : ℕ → ℝ} (hF : Continuous F)
    (hbd : ∀ᶠ M : ℕ in atTop, ∀ y : ℝ, ‖F (↑(-(M : ℝ)) + ↑y * I)‖ ≤ H M) :
    HasPerronCarrierFlankMass F (fun M => 2 * H M) := by
  filter_upwards [hbd] with M hM
  have := hasPerronCarrierFlankMassAt_of_uniform_flank hF hM
  rwa [show Real.pi / 2 * (2 * H M) = Real.pi * H M by ring]

/-- **Quiet horizontal escape.**  A height exhaustion on which the carrier is uniformly bounded
across the whole contour width by a quantity of smaller order than the squared height makes both
horizontal Perron edges vanish. -/
theorem hasPerronHorizontalEscapeAt_of_quiet_heights
    {F : ℂ → ℂ} {c δ : ℝ} {n M : ℕ} {T Q : ℕ → ℝ}
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ))
    (hc0 : 0 < c)
    (hT : Tendsto T atTop atTop)
    (hbd : ∀ k, ∀ x : ℝ, -(M : ℝ) ≤ x → x ≤ c →
      ‖F (↑x + ↑(T k) * I)‖ ≤ Q k ∧ ‖F (↑x + ↑(-(T k)) * I)‖ ≤ Q k)
    (hQ0 : ∀ k, 0 ≤ Q k)
    (hQ : Tendsto (fun k => Q k / (1 + (T k) ^ (2 : ℕ))) atTop (𝓝 0)) :
    HasPerronHorizontalEscapeAt F c n δ M := by
  classical
  obtain ⟨k₀, hk₀⟩ := (hT.eventually_ge_atTop (1 : ℝ)).exists_forall_of_atTop
  set T' : ℕ → ℝ := fun k => T (k + k₀) with hT'
  have hT'ge : ∀ k, (1 : ℝ) ≤ T' k := fun k => hk₀ (k + k₀) (Nat.le_add_left _ _)
  have hT'top : Tendsto T' atTop atTop := hT.comp (tendsto_add_atTop_nat k₀)
  have hshift : Tendsto (fun k : ℕ => k + k₀) atTop atTop := tendsto_add_atTop_nat k₀
  have hQ' : Tendsto (fun k => Q (k + k₀) / (1 + (T' k) ^ (2 : ℕ))) atTop (𝓝 0) := hQ.comp hshift
  set K : ℝ := perronStripKernelEnvelope n M δ c with hK
  have hK0 : 0 ≤ K := by
    dsimp [K, perronStripKernelEnvelope]
    positivity
  have hMc : -(M : ℝ) ≤ c := by
    have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hbound : ∀ (k : ℕ) (ε : ℝ), ε = 1 ∨ ε = -1 →
      ‖∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑(ε * T' k) * I)‖
        ≤ (K * (c + (M : ℝ))) * (Q (k + k₀) / (1 + (T' k) ^ (2 : ℕ))) := by
    intro k ε hε
    have habs : |ε * T' k| = T' k := by
      rcases hε with rfl | rfl
      · rw [one_mul, abs_of_nonneg (by linarith [hT'ge k])]
      · rw [neg_one_mul, abs_neg, abs_of_nonneg (by linarith [hT'ge k])]
    have hsq : (ε * T' k) ^ (2 : ℕ) = (T' k) ^ (2 : ℕ) := by
      rcases hε with rfl | rfl <;> ring
    have hstep : ∀ x ∈ Set.uIoc (-(M : ℝ)) c,
        ‖perronContourIntegrand F n δ (↑x + ↑(ε * T' k) * I)‖
          ≤ K * (Q (k + k₀) / (1 + (T' k) ^ (2 : ℕ))) := by
      intro x hx
      rw [Set.uIoc_of_le hMc] at hx
      have hxlo : -(M : ℝ) ≤ x := le_of_lt hx.1
      have hxhi : x ≤ c := hx.2
      have hEbd : ‖perronEAt n δ (↑x + ↑(ε * T' k) * I)‖ ≤ K / (1 + (ε * T' k) ^ (2 : ℕ)) :=
        perronEAt_strip_high_norm_le hn hδ0 hδn hxlo hxhi (by rw [habs]; exact hT'ge k)
      have hFbd : ‖F (↑x + ↑(ε * T' k) * I)‖ ≤ Q (k + k₀) := by
        rcases hε with rfl | rfl
        · rw [one_mul]; exact (hbd (k + k₀) x hxlo hxhi).1
        · rw [neg_one_mul]; exact (hbd (k + k₀) x hxlo hxhi).2
      unfold perronContourIntegrand
      rw [norm_mul]
      calc ‖F (↑x + ↑(ε * T' k) * I)‖ * ‖perronEAt n δ (↑x + ↑(ε * T' k) * I)‖
          ≤ Q (k + k₀) * (K / (1 + (ε * T' k) ^ (2 : ℕ))) := by
            refine mul_le_mul hFbd hEbd (norm_nonneg _) (hQ0 _)
        _ = K * (Q (k + k₀) / (1 + (T' k) ^ (2 : ℕ))) := by rw [hsq]; ring
    have hlen : |c - -(M : ℝ)| = c + (M : ℝ) := by
      rw [abs_of_nonneg (by linarith)]
      ring
    calc ‖∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑(ε * T' k) * I)‖
        ≤ (K * (Q (k + k₀) / (1 + (T' k) ^ (2 : ℕ)))) * |c - -(M : ℝ)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hstep
      _ = (K * (c + (M : ℝ))) * (Q (k + k₀) / (1 + (T' k) ^ (2 : ℕ))) := by rw [hlen]; ring
  have hlim : Tendsto (fun k => (K * (c + (M : ℝ))) * (Q (k + k₀) / (1 + (T' k) ^ (2 : ℕ))))
      atTop (𝓝 0) := by simpa using hQ'.const_mul (K * (c + (M : ℝ)))
  refine ⟨T', hT'top, fun k => by linarith [hT'ge k], ?_, ?_⟩
  · refine squeeze_zero_norm (fun k => ?_) hlim
    simpa using hbound k 1 (Or.inl rfl)
  · refine squeeze_zero_norm (fun k => ?_) hlim
    have := hbound k (-1) (Or.inr rfl)
    simpa using this

/-- **Quiet heights plus a uniform flank envelope give horizontal escape at every knot width and
every sufficiently deep contour.** -/
theorem hasVariablePerronHorizontalEscape_of_quiet_uniform_flank
    {F : ℂ → ℂ} {c : ℝ} {H q T : ℕ → ℝ} {n : ℕ}
    (hc : 1 / 2 ≤ c) (hn : 1 ≤ n)
    (hT : Tendsto T atTop atTop)
    (hquiet : ∀ k, ∀ σ : ℝ, 1 - c ≤ σ → σ ≤ c →
      ‖F (↑σ + ↑(T k) * I)‖ ≤ q k ∧ ‖F (↑σ + ↑(-(T k)) * I)‖ ≤ q k)
    (hq : Tendsto (fun k => q k / T k ^ (2 : ℕ)) atTop (𝓝 0))
    (hflank : ∀ M : ℕ, ∀ s : ℂ, -(M : ℝ) ≤ s.re → s.re ≤ 1 - c → ‖F s‖ ≤ H M) :
    HasVariablePerronHorizontalEscape F c n := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hcc : 1 - c ≤ c := by linarith
  have hq0 : ∀ k, 0 ≤ q k := fun k =>
    le_trans (norm_nonneg _) ((hquiet k c hcc le_rfl)).1
  have hTpos : ∀ᶠ k : ℕ in atTop, (0 : ℝ) < T k := hT.eventually_gt_atTop 0
  have hqw : Tendsto (fun k => q k / (1 + T k ^ (2 : ℕ))) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun k => div_nonneg (hq0 k) (by positivity)) ?_ hq
    filter_upwards [hTpos] with k hk
    refine div_le_div_of_nonneg_left (hq0 k) (by positivity) ?_
    nlinarith
  have hTsq : Tendsto (fun k => 1 + T k ^ (2 : ℕ)) atTop atTop := by
    have h1 : Tendsto (fun k => T k ^ (2 : ℕ)) atTop atTop := by
      simpa [pow_two] using (hT.atTop_mul_atTop₀ hT)
    exact tendsto_atTop_add_const_left _ 1 h1
  intro δ hδ0 hδ1 hδn
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop c] with M hMc
  have hMle : -(M : ℝ) ≤ 1 - c := by linarith
  have hH0 : 0 ≤ H M := le_trans (norm_nonneg (F (↑(-(M : ℝ)) + ↑(0 : ℝ) * I)))
    (hflank M _ (by simp) (by simpa using hMle))
  refine hasPerronHorizontalEscapeAt_of_quiet_heights (Q := fun k => H M + q k)
    hn hδ0 hδn hc0 hT ?_ (fun k => by linarith [hq0 k]) ?_
  · intro k x hxlo hxhi
    rcases le_total x (1 - c) with hx | hx
    · constructor
      · exact le_trans (hflank M _ (by simpa using hxlo) (by simpa using hx))
          (by linarith [hq0 k])
      · exact le_trans (hflank M _ (by simpa using hxlo) (by simpa using hx))
          (by linarith [hq0 k])
    · exact ⟨le_trans (hquiet k x hx hxhi).1 (by linarith),
        le_trans (hquiet k x hx hxhi).2 (by linarith)⟩
  · have hHlim : Tendsto (fun k => H M / (1 + T k ^ (2 : ℕ))) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hTsq
    have := hHlim.add hqw
    simpa [add_div] using this

/-- **Uniform quiet-flank support theorem.**  An entire carrier which agrees with an absolutely
convergent Dirichlet series on `Re s ≥ c ≥ 1/2`, is quiet on a height exhaustion at order below the
squared height, and obeys a geometric uniform flank envelope `H(M) ≤ C R^M` on every left region
`-M ≤ Re s ≤ 1-c`, has all its nonzero Dirichlet coefficients supported in `n ≤ R`. -/
theorem coefficient_index_le_exact_flank_radius_of_quiet_uniform_flank
    {F : ℂ → ℂ} {a : ℕ → ℂ} {c : ℝ} {H q T : ℕ → ℝ} {n : ℕ} {C R : ℝ}
    (hc : 1 / 2 ≤ c)
    (hF : Differentiable ℂ F) (hsum : LSeriesSummable a c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s) (hn : 1 ≤ n)
    (hT : Tendsto T atTop atTop)
    (hquiet : ∀ k, ∀ σ : ℝ, 1 - c ≤ σ → σ ≤ c →
      ‖F (↑σ + ↑(T k) * I)‖ ≤ q k ∧ ‖F (↑σ + ↑(-(T k)) * I)‖ ≤ q k)
    (hq : Tendsto (fun k => q k / T k ^ (2 : ℕ)) atTop (𝓝 0))
    (hflank : ∀ M : ℕ, ∀ s : ℂ, -(M : ℝ) ≤ s.re → s.re ≤ 1 - c → ‖F s‖ ≤ H M)
    (hR : 0 ≤ R) (hH : ∀ᶠ M : ℕ in atTop, H M ≤ C * R ^ M)
    (han : a n ≠ 0) :
    (n : ℝ) ≤ R := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hdeep : ∀ᶠ M : ℕ in atTop, c ≤ (M : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop c
  have hflankline : ∀ᶠ M : ℕ in atTop, ∀ y : ℝ, ‖F (↑(-(M : ℝ)) + ↑y * I)‖ ≤ H M := by
    filter_upwards [hdeep] with M hMc y
    exact hflank M _ (by simp) (by simp; linarith)
  have hH0 : ∀ᶠ M : ℕ in atTop, 0 ≤ H M := by
    filter_upwards [hflankline] with M hM
    exact le_trans (norm_nonneg _) (hM 0)
  refine coefficient_index_le_exact_flank_radius_of_carrierFlankMass_horizontalEscape
    (H := fun M => 2 * H M) (C := 2 * C)
    (hasPerronCarrierFlankMass_of_uniform_flank hF.continuous hflankline)
    (hasVariablePerronHorizontalEscape_of_quiet_uniform_flank hc hn hT hquiet hq hflank)
    hc0 hsum hF hFeq hn hR ?_ ?_ han
  · filter_upwards [hH0] with M hM using by linarith
  · filter_upwards [hH] with M hM using by linarith

end RHTower
