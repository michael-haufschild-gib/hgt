import GaloisForLFunctions.BlackHoleRingdown.TheRingdownExpansion

/-!
# The ringdown expansion is uniform at late times

The partial sums of the ringdown expansion converge uniformly on `τ ≥ 0`. So at every precision, finitely
many damped modes and the remainder approximate the packet at all late times at once.

On a finite rectangle the partial sum differs from `𝓕 - R` by the tails of the two line integrals and by
the two horizontal edges. On `τ ≥ 0` the factor `e^{uτ}` has modulus at most one on `Re u ≤ 0`, so each
of these is dominated by the same quantity at `τ = 0`, which does not depend on `τ`.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-- The tail of an integral is dominated by the tail of a majorant. -/
theorem norm_integral_sub_interval_le {f : ℝ → ℂ} {n : ℝ → ℝ} (hf : Integrable f) (hn : Integrable n)
    (h : ∀ y, ‖f y‖ ≤ n y) {L : ℝ} (hL : 0 ≤ L) :
    ‖(∫ y, f y) - ∫ y in (-L)..L, f y‖ ≤ (∫ y, n y) - ∫ y in (-L)..L, n y := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle]
  have h1 := integral_add_compl (measurableSet_Ioc (a := -L) (b := L)) hf
  have h2 := integral_add_compl (measurableSet_Ioc (a := -L) (b := L)) hn
  have e1 : (∫ y, f y) - ∫ y in Ioc (-L) L, f y = ∫ y in (Ioc (-L) L)ᶜ, f y := by
    rw [← h1]
    ring
  have e2 : (∫ y, n y) - ∫ y in Ioc (-L) L, n y = ∫ y in (Ioc (-L) L)ᶜ, n y := by
    rw [← h2]
    ring
  rw [e1, e2]
  exact norm_integral_le_of_norm_le hn.integrableOn (Eventually.of_forall h)

/-- The tail of an integrable function tends to zero. -/
theorem tendsto_integral_sub_interval {n : ℝ → ℝ} (hn : Integrable n) :
    Tendsto (fun L : ℝ => (∫ y, n y) - ∫ y in (-L)..L, n y) atTop (𝓝 0) := by
  have h := intervalIntegral_tendsto_integral hn tendsto_neg_atTop_atBot tendsto_id
  have h2 : Tendsto (fun L : ℝ => (∫ y, n y) - ∫ y in (-L)..L, n y) atTop
      (𝓝 ((∫ y, n y) - ∫ y, n y)) := tendsto_const_nhds.sub h
  rwa [sub_self] at h2

section Uniform

variable {ε : ℝ} (hε : 0 < ε) (ξ₀ x : ℝ) {Y : ℝ} (hY : 0 < Y)

/-- On `Re u ≤ 0` and `τ ≥ 0`, the quotient at time `τ` is dominated by the quotient at time zero. -/
theorem norm_inverseXiQuotient_packet_le (τ : ℝ) (hτ : 0 ≤ τ) {u : ℂ} (hu : u.re ≤ 0) :
    ‖inverseXiQuotient (packetNumerator ε ξ₀ τ x Y) u‖ ≤
      ‖inverseXiQuotient (packetNumerator ε ξ₀ 0 x Y) u‖ := by
  rw [inverseXiQuotient_packet_time, norm_mul, Complex.norm_exp]
  have hre : (u * (τ : ℂ)).re = u.re * τ := by simp
  rw [hre]
  have h1 : Real.exp (u.re * τ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hu hτ
  exact mul_le_of_le_one_left (norm_nonneg _) h1

include hε hY

/-- The finite rectangle: the partial sum in terms of the edges and of the truncated lines. -/
theorem ringdownPartialSum_eq (τ : ℝ) {A : ℝ} (hA : 1 ≤ A) (k : ℕ) :
    ringdownPartialSum ε ξ₀ τ x Y k =
      (HIntegral (inverseXiQuotient (packetNumerator ε ξ₀ τ x Y)) (-A) 0 (-(goodHeight k / 2)) -
          HIntegral (inverseXiQuotient (packetNumerator ε ξ₀ τ x Y)) (-A) 0 (goodHeight k / 2)) / I +
        (∫ y in (-(goodHeight k / 2))..(goodHeight k / 2),
          inverseXiQuotient (packetNumerator ε ξ₀ τ x Y) ((y : ℂ) * I)) -
        ∫ y in (-(goodHeight k / 2))..(goodHeight k / 2),
          inverseXiQuotient (packetNumerator ε ξ₀ τ x Y) (((-A : ℝ) : ℂ) + (y : ℂ) * I) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [ringdownPartialSum, ← rectangleIntegral'_inverseXiQuotient hA
    (gaussianNumerator_packet hε ξ₀ τ x hY (by linarith)) k]
  simp only [RectangleIntegral', RectangleIntegral, VIntegral, smul_eq_mul]
  simp only [Complex.ofReal_zero, zero_add]
  field_simp

/-- **Uniform bound.**  The distance from the partial sum to `𝓕 - R` on `τ ≥ 0` is at most a sequence
that does not depend on `τ` and tends to zero. -/
theorem exists_uniform_bound {A : ℝ} (hA : 1 ≤ A) :
    ∃ B : ℕ → ℝ, Tendsto B atTop (𝓝 0) ∧ ∀ᶠ k in atTop, ∀ τ : ℝ, 0 ≤ τ →
      ‖(wavePacket ε ξ₀ τ x Y - ringdownRemainder A ε ξ₀ τ x Y) -
        ringdownPartialSum ε ξ₀ τ x Y k‖ ≤ B k := by
  have hAnn : 0 ≤ A := by linarith
  have hP₀ := gaussianNumerator_packet hε ξ₀ 0 x hY hAnn
  obtain ⟨C, c, k₀, hC, hc, hedge⟩ := exists_norm_inverseXiQuotient_edge_le hA hP₀
  have hint₁ := integrable_inverseXiQuotient_right hA hP₀
  have hint₂ := integrable_inverseXiQuotient_left hA hP₀
  set n₁ : ℝ → ℝ := fun y => ‖inverseXiQuotient (packetNumerator ε ξ₀ 0 x Y) ((y : ℂ) * I)‖ with hn₁
  set n₂ : ℝ → ℝ := fun y =>
    ‖inverseXiQuotient (packetNumerator ε ξ₀ 0 x Y) (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ with hn₂
  have hTat := tendsto_goodHeight
  have hLat : Tendsto (fun k => goodHeight k / 2) atTop atTop := hTat.atTop_div_const (by norm_num)
  refine ⟨fun k => ((∫ y, n₁ y) - ∫ y in (-(goodHeight k / 2))..(goodHeight k / 2), n₁ y) +
      ((∫ y, n₂ y) - ∫ y in (-(goodHeight k / 2))..(goodHeight k / 2), n₂ y) +
      2 * (C * Real.exp (-c * goodHeight k ^ 2) * A), ?_, ?_⟩
  · have ht₁ := (tendsto_integral_sub_interval hint₁.norm).comp hLat
    have ht₂ := (tendsto_integral_sub_interval hint₂.norm).comp hLat
    have hsq : Tendsto (fun k => c * goodHeight k ^ 2) atTop atTop :=
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hTat).const_mul_atTop hc
    have hexp : Tendsto (fun k => Real.exp (-c * goodHeight k ^ 2)) atTop (𝓝 0) := by
      refine (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsq)).congr fun k => ?_
      simp only [Function.comp_def]
      congr 1
      ring
    have hedges : Tendsto (fun k => 2 * (C * Real.exp (-c * goodHeight k ^ 2) * A)) atTop (𝓝 0) := by
      simpa using ((hexp.const_mul C).mul_const A).const_mul 2
    have hsum := (ht₁.add ht₂).add hedges
    rw [add_zero, add_zero] at hsum
    exact hsum
  · filter_upwards [eventually_ge_atTop k₀, hTat.eventually_ge_atTop 2] with k hk hT2 τ hτ
    set L := goodHeight k / 2 with hL
    have hL0 : 0 ≤ L := by rw [hL]; linarith
    have hP := gaussianNumerator_packet hε ξ₀ τ x hY hAnn
    have hline₁ := norm_integral_sub_interval_le (integrable_inverseXiQuotient_right hA hP)
      hint₁.norm (fun y => norm_inverseXiQuotient_packet_le ξ₀ x τ hτ (u := (y : ℂ) * I) (by simp))
      hL0
    have hline₂ := norm_integral_sub_interval_le (integrable_inverseXiQuotient_left hA hP)
      hint₂.norm (fun y => norm_inverseXiQuotient_packet_le ξ₀ x τ hτ
        (u := ((-A : ℝ) : ℂ) + (y : ℂ) * I) (by simp; linarith)) hL0
    have hEdge : ∀ s : ℝ, |s| = L →
        ‖HIntegral (inverseXiQuotient (packetNumerator ε ξ₀ τ x Y)) (-A) 0 s‖ ≤
          C * Real.exp (-c * goodHeight k ^ 2) * A := by
      intro s hs
      rw [HIntegral]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -A) (b := 0)
        (f := fun q : ℝ => inverseXiQuotient (packetNumerator ε ξ₀ τ x Y) ((q : ℂ) + (s : ℂ) * I))
        (C := C * Real.exp (-c * goodHeight k ^ 2)) (fun q hq => by
          rw [uIoc_of_le (by linarith)] at hq
          have hre : ((q : ℂ) + (s : ℂ) * I).re = q := by simp
          have him : ((q : ℂ) + (s : ℂ) * I).im = s := by simp
          refine (norm_inverseXiQuotient_packet_le ξ₀ x τ hτ (by rw [hre]; exact hq.2)).trans ?_
          exact hedge k hk hT2 _ (by rw [hre]; exact hq.1.le) (by rw [hre]; exact hq.2)
            (by rw [him, hs]))
      refine hb.trans (le_of_eq ?_)
      rw [sub_neg_eq_add, zero_add, abs_of_nonneg hAnn]
    have hE₁ := hEdge (-L) (by rw [abs_neg, abs_of_nonneg hL0])
    have hE₂ := hEdge L (abs_of_nonneg hL0)
    rw [ringdownPartialSum_eq hε ξ₀ x hY τ hA k, ← hL, wavePacket_eq_lineIntegral, ringdownRemainder]
    set H₁ := HIntegral (inverseXiQuotient (packetNumerator ε ξ₀ τ x Y)) (-A) 0 (-L)
    set H₂ := HIntegral (inverseXiQuotient (packetNumerator ε ξ₀ τ x Y)) (-A) 0 L
    set J₁ := ∫ y : ℝ, inverseXiQuotient (packetNumerator ε ξ₀ τ x Y) ((y : ℂ) * I)
    set J₂ := ∫ y : ℝ, inverseXiQuotient (packetNumerator ε ξ₀ τ x Y) (((-A : ℝ) : ℂ) + (y : ℂ) * I)
    set K₁ := ∫ y in (-L)..L, inverseXiQuotient (packetNumerator ε ξ₀ τ x Y) ((y : ℂ) * I)
    set K₂ := ∫ y in (-L)..L,
      inverseXiQuotient (packetNumerator ε ξ₀ τ x Y) (((-A : ℝ) : ℂ) + (y : ℂ) * I)
    have hsplit : J₁ - J₂ - ((H₁ - H₂) / I + K₁ - K₂) = (J₁ - K₁) - (J₂ - K₂) - (H₁ - H₂) / I := by
      ring
    have hIn : ‖(H₁ - H₂) / I‖ ≤ ‖H₁‖ + ‖H₂‖ := by
      rw [norm_div, Complex.norm_I, div_one]
      exact norm_sub_le _ _
    rw [hsplit]
    calc ‖(J₁ - K₁) - (J₂ - K₂) - (H₁ - H₂) / I‖
        ≤ ‖J₁ - K₁‖ + ‖J₂ - K₂‖ + ‖(H₁ - H₂) / I‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ _ := by linarith

/-- **The expansion is uniform at late times.**  On `τ ≥ 0`, the partial sums over the zeros up to the good
heights converge uniformly to `𝓕 - R`, and `R` decays faster than every exponential. -/
theorem ringdown_expansion_uniform :
    ∃ R : ℝ → ℂ, (∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖R τ‖ ≤ C * Real.exp (-A * τ)) ∧
      TendstoUniformlyOn (fun k τ => ringdownPartialSum ε ξ₀ τ x Y k)
        (fun τ => wavePacket ε ξ₀ τ x Y - R τ) atTop (Ici 0) := by
  refine ⟨fun τ => ringdownRemainder 1 ε ξ₀ τ x Y, fun A hA => ?_, ?_⟩
  · obtain ⟨C, hC, hb⟩ := exists_norm_ringdownRemainder_le hε ξ₀ x hY hA
    refine ⟨C, hC, fun τ => ?_⟩
    simp only
    rw [ringdownRemainder_eq hε ξ₀ x hY τ le_rfl hA]
    exact hb τ
  · obtain ⟨B, hB, hbound⟩ := exists_uniform_bound hε ξ₀ x hY (A := 1) le_rfl
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [hbound, hB.eventually (gt_mem_nhds hδ)] with k hk hBk τ hτ
    rw [dist_eq_norm]
    exact (hk τ hτ).trans_lt hBk

end Uniform

end GaloisForLFunctions.BlackHoleRingdown

end
