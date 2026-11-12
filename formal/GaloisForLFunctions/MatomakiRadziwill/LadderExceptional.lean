import GaloisForLFunctions.MatomakiRadziwill.LadderScaleBounds

/-!
# The exceptional set of the ladder

* **Pure moments** (`integral_normSq_blockQ_pow_le`): for `S = e^{u/H'} ≥ H' ≥ 3`, `k ≥ 1`, `S^k ≥ W`,
  `∫_{|w|≤W} |Q_u(w)|^{2k} ≤ 144 (18k/H')^k` (the coincidence count with the trivial cofactor).
* **Markov** (`volume_large_le`): `|{|w| ≤ W : |Q(w)| > c}| ≤ c^{-2k} ∫_{|w|≤W} |Q|^{2k}`; summed over the
  blocks of a scale, `|[−W,W] ∖ smallAt Q V c| ≤ Σ_v c_v^{-2k_v} ∫ |Q_v|^{2k_v}`
  (`volume_not_small_le`).
* **The exceptional integral** (`setIntegral_not_small_le`): if `|Q*_v| ≤ ρ` on `[−W,W]` for every block
  `v` of the top scale, then `∫_{E} |Σ_v Q*_v R*_v|² ≤ #V ρ² Σ_v ∫_E |R*_v|²`, `E` the exceptional set.
-/

open Finset MeasureTheory Set RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

theorem unitLogPhase_one (w : ℝ) : unitLogPhase w 1 = 1 := by
  simp [unitLogPhase]

/-- **Pure moments of a normalised prime block.** -/
theorem integral_normSq_blockQ_pow_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {Pr' : Finset ℕ} (hPr' : ∀ q ∈ Pr', q.Prime) {H' : ℝ} (hH' : 3 ≤ H') (u k : ℕ) (hk : 1 ≤ k)
    (hS : H' ≤ Real.exp ((u : ℝ) / H')) {W : ℝ} (hW : 1 ≤ W)
    (hlen : W ≤ Real.exp ((u : ℝ) / H') ^ k) :
    (∫ w in Icc (-W) W, ‖blockQ f Pr' H' u w ^ k‖ ^ (2 : ℕ)) ≤ 144 * (18 * k / H') ^ k := by
  classical
  have hH0 : 0 < H' := by linarith
  set S := Real.exp ((u : ℝ) / H') with hSdef
  set E := Real.exp (1 / H') with hEdef
  set B := Pr'.filter fun p => blk H' p = u with hBdef
  have hS0 : 0 < S := Real.exp_pos _
  have hE2 : E ≤ 2 := exp_inv_le_two (by linarith)
  have hE1 : E - 1 ≤ 2 / H' := exp_inv_sub_one_le (by linarith)
  set a' : ℕ → ℂ := fun p => if p ∈ B then (S : ℂ) * coefA f p else 0 with ha'
  set c' : ℕ → ℂ := fun m => if m = 1 then 1 else 0 with hc'
  have ha'1 : ∀ p, ‖a' p‖ ≤ 1 := by
    intro p
    simp only [ha']
    split_ifs with hp
    · obtain ⟨h1, -⟩ := mem_block_bounds hPr' hH0 hp
      have hp0 : (0 : ℝ) < p := lt_of_lt_of_le hS0 h1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS0]
      calc S * ‖coefA f p‖ ≤ S * (1 / p) := mul_le_mul_of_nonneg_left (norm_coefA_le hf p) hS0.le
        _ ≤ 1 := by rw [mul_one_div, div_le_one hp0]; exact h1
    · rw [norm_zero]; exact zero_le_one
  have hc'1 : ∀ m, ‖c' m‖ ≤ 1 := by
    intro m; simp only [hc']; split_ifs <;> simp
  have hone : ∀ w, logPoly c' {1} w = 1 := by
    intro w
    rw [logPoly_eq_sum_mul_unitLogPhase, sum_singleton, unitLogPhase_one]
    simp [hc']
  have hQ : ∀ w, blockQ f Pr' H' u w = (S : ℂ)⁻¹ * logPoly a' B w := by
    intro w
    rw [blockQ, ← hBdef, logPoly_congr (b := fun p => (S : ℂ)⁻¹ * a' p) (fun p hp => by
      simp only [ha', if_pos hp]
      have : (S : ℂ) ≠ 0 := by exact_mod_cast hS0.ne'
      field_simp) w, logPoly_const_mul]
  have hnorm : ∀ w, ‖blockQ f Pr' H' u w ^ k‖ ^ (2 : ℕ)
      = (S ^ k)⁻¹ ^ 2 * ‖logPoly a' B w ^ k * logPoly c' {1} w‖ ^ (2 : ℕ) := by
    intro w
    rw [hone, mul_one, hQ, mul_pow, show (S : ℂ)⁻¹ ^ k * logPoly a' B w ^ k
        = (((S ^ k)⁻¹ : ℝ) : ℂ) * logPoly a' B w ^ k by push_cast; ring, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  simp_rw [hnorm]
  rw [integral_const_mul]
  set Bmax : ℕ := ⌊S * E⌋₊ with hBmax
  have hBbounds : ∀ p ∈ B, S ≤ p ∧ p ≤ Bmax := fun p hp => by
    obtain ⟨h1, h2⟩ := mem_block_bounds hPr' hH0 hp
    exact ⟨h1, Nat.le_floor h2.le⟩
  have hcore := integral_normSq_logPoly_pow_mul_logPoly_le (B := B) (D := {1}) (X := 1)
    (fun p hp => hPr' p (mem_filter.mp hp).1) ha'1 hc'1 (fun m hm => by
      rw [Finset.mem_singleton] at hm; omega) hS0
    (fun p hp => (hBbounds p hp).1) (fun p hp => (hBbounds p hp).2) k hW
  have hBmaxle : (Bmax : ℝ) ≤ 2 * S := le_trans (Nat.floor_le (by positivity)) (by nlinarith)
  have hcardB : (B.card : ℝ) ≤ 3 * S / H' := by
    have h := card_block_le hPr' hH0 u
    rw [← hSdef, ← hEdef, ← hBdef] at h
    have h1 : S * (E - 1) ≤ 2 * S / H' := by
      calc S * (E - 1) ≤ S * (2 / H') := mul_le_mul_of_nonneg_left hE1 hS0.le
        _ = 2 * S / H' := by ring
    have h2 : (1 : ℝ) ≤ S / H' := by rw [le_div_iff₀ hH0]; linarith
    calc (B.card : ℝ) ≤ S * (E - 1) + 1 := h
      _ ≤ 2 * S / H' + S / H' := add_le_add h1 h2
      _ = 3 * S / H' := by ring
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcardB2 : (B.card : ℝ) + k * Bmax ≤ 3 * k * S := by
    have h1 : 3 * S / H' ≤ S := by rw [div_le_iff₀ hH0]; nlinarith
    have h2 : (k : ℝ) * Bmax ≤ k * (2 * S) := mul_le_mul_of_nonneg_left hBmaxle (by linarith)
    nlinarith
  have hB0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hprod : (B.card : ℝ) ^ k * ((1 : ℕ) : ℝ) * ((B.card : ℝ) + k * Bmax) ^ k / S ^ k
      ≤ (9 * k * S / H') ^ k := by
    have h1 : (B.card : ℝ) ^ k ≤ (3 * S / H') ^ k := pow_le_pow_left₀ hB0 hcardB k
    have h2 : ((B.card : ℝ) + k * Bmax) ^ k ≤ (3 * k * S) ^ k :=
      pow_le_pow_left₀ (by positivity) hcardB2 k
    have hSk : 0 < S ^ k := pow_pos hS0 k
    rw [div_le_iff₀ hSk, Nat.cast_one, mul_one]
    calc (B.card : ℝ) ^ k * ((B.card : ℝ) + k * Bmax) ^ k ≤ (3 * S / H') ^ k * (3 * k * S) ^ k :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (9 * k * S / H') ^ k * S ^ k := by rw [← mul_pow, ← mul_pow]; congr 1; ring
  have hfirst : 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((Bmax ^ k * 1 : ℕ) : ℝ)
      ≤ 16 * 2 ^ k * S ^ k := by
    have hpi : Real.pi ≤ 16 / 5 := by linarith [Real.pi_lt_d2]
    have he : Real.exp 1 ≤ 14 / 5 := by linarith [Real.exp_one_lt_d9]
    have hBk : ((Bmax ^ k * 1 : ℕ) : ℝ) ≤ (2 * S) ^ k := by
      push_cast; rw [mul_one]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hBmaxle k
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hSk : 0 < S ^ k := pow_pos hS0 k
    have h1 : 5 * Real.pi / 2 * W ≤ 8 * S ^ k := by nlinarith
    have h3 : 5 * Real.exp 1 / 2 * ((Bmax ^ k * 1 : ℕ) : ℝ) ≤ 7 * (2 * S) ^ k := by
      have : 0 ≤ ((Bmax ^ k * 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h4 : (2 * S) ^ k = 2 ^ k * S ^ k := mul_pow 2 S k
    nlinarith
  have hfirst0 : 0 ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((Bmax ^ k * 1 : ℕ) : ℝ) := by
    have := Real.pi_pos; have := (Real.exp_pos 1).le; have : (0 : ℝ) ≤ W := by linarith
    positivity
  have hscale : 0 ≤ (S ^ k)⁻¹ ^ 2 := by positivity
  calc (S ^ k)⁻¹ ^ 2 * ∫ w in Icc (-W) W, ‖logPoly a' B w ^ k * logPoly c' {1} w‖ ^ (2 : ℕ)
      ≤ (S ^ k)⁻¹ ^ 2 * ((16 * 2 ^ k * S ^ k) * (9 * k * S / H') ^ k) := by
        refine mul_le_mul_of_nonneg_left (hcore.trans ?_) hscale
        exact mul_le_mul hfirst hprod (by positivity) (by positivity)
    _ = 16 * (2 ^ k * (9 * k * S / H') ^ k / S ^ k) := by
        field_simp
    _ = 16 * (18 * k / H') ^ k := by
        congr 1
        rw [← mul_pow, ← div_pow]
        congr 1
        field_simp
        ring
    _ ≤ 144 * (18 * k / H') ^ k := by
        have : 0 ≤ (18 * (k : ℝ) / H') ^ k := by positivity
        linarith

/-- **Markov's inequality for a large value of `Q`.** -/
theorem volume_large_le {Q : ℝ → ℂ} (hQ : Continuous Q) {c : ℝ} (hc : 0 < c) (k : ℕ) (W : ℝ) :
    volume.real (Icc (-W) W ∩ {w | c < ‖Q w‖})
      ≤ (c ^ (2 * k))⁻¹ * ∫ w in Icc (-W) W, ‖Q w ^ k‖ ^ (2 : ℕ) := by
  set μ := volume.restrict (Icc (-W) W) with hμ
  have hcont : Continuous fun w => ‖Q w ^ k‖ ^ (2 : ℕ) := ((hQ.pow k).norm).pow 2
  have hint : Integrable (fun w => ‖Q w ^ k‖ ^ (2 : ℕ)) μ :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall fun w => by positivity) hint (c ^ (2 * k))
  have hmeas : MeasurableSet {w | c ^ (2 * k) ≤ ‖Q w ^ k‖ ^ (2 : ℕ)} :=
    (isClosed_le continuous_const hcont).measurableSet
  rw [hμ, measureReal_restrict_apply hmeas] at hmark
  have hsub : Icc (-W) W ∩ {w | c < ‖Q w‖}
      ⊆ {w | c ^ (2 * k) ≤ ‖Q w ^ k‖ ^ (2 : ℕ)} ∩ Icc (-W) W := by
    intro w ⟨hw1, hw2⟩
    refine ⟨?_, hw1⟩
    simp only [mem_setOf_eq] at hw2 ⊢
    rw [norm_pow, ← pow_mul, mul_comm k 2]
    exact pow_le_pow_left₀ hc.le hw2.le _
  have hfin : volume ({w | c ^ (2 * k) ≤ ‖Q w ^ k‖ ^ (2 : ℕ)} ∩ Icc (-W) W) ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_Icc_lt_top (a := -W) (b := W)).ne (measure_mono inter_subset_right)
  have hmono := measureReal_mono hsub hfin
  have hck : 0 < c ^ (2 * k) := pow_pos hc _
  rw [inv_mul_eq_div, le_div_iff₀ hck]
  calc volume.real (Icc (-W) W ∩ {w | c < ‖Q w‖}) * c ^ (2 * k)
      ≤ volume.real ({w | c ^ (2 * k) ≤ ‖Q w ^ k‖ ^ (2 : ℕ)} ∩ Icc (-W) W) * c ^ (2 * k) :=
        mul_le_mul_of_nonneg_right hmono hck.le
    _ = c ^ (2 * k) * volume.real ({w | c ^ (2 * k) ≤ ‖Q w ^ k‖ ^ (2 : ℕ)} ∩ Icc (-W) W) := by
        ring
    _ ≤ ∫ w in Icc (-W) W, ‖Q w ^ k‖ ^ (2 : ℕ) := hmark

/-- **The measure of the exceptional set.** -/
theorem volume_not_small_le {Q : ℕ → ℝ → ℂ} (hQ : ∀ v, Continuous (Q v)) (V : Finset ℕ)
    {c : ℕ → ℝ} (hc : ∀ v ∈ V, 0 < c v) (k : ℕ → ℕ) (W : ℝ) :
    volume.real (Icc (-W) W ∩ (smallAt Q V c)ᶜ)
      ≤ ∑ v ∈ V, (c v ^ (2 * k v))⁻¹ * ∫ w in Icc (-W) W, ‖Q v w ^ k v‖ ^ (2 : ℕ) := by
  have hsub : Icc (-W) W ∩ (smallAt Q V c)ᶜ ⊆ ⋃ v ∈ V, Icc (-W) W ∩ {w | c v < ‖Q v w‖} := by
    intro w ⟨hw1, hw2⟩
    simp only [smallAt, mem_compl_iff, mem_setOf_eq, not_forall, not_le] at hw2
    obtain ⟨v, hv, hlt⟩ := hw2
    exact mem_biUnion hv ⟨hw1, hlt⟩
  have hfin : volume (⋃ v ∈ V, Icc (-W) W ∩ {w | c v < ‖Q v w‖}) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_Icc_lt_top (a := -W) (b := W)).ne (measure_mono ?_)
    exact iUnion₂_subset fun v _ => inter_subset_left
  calc volume.real (Icc (-W) W ∩ (smallAt Q V c)ᶜ)
      ≤ volume.real (⋃ v ∈ V, Icc (-W) W ∩ {w | c v < ‖Q v w‖}) := measureReal_mono hsub hfin
    _ ≤ ∑ v ∈ V, volume.real (Icc (-W) W ∩ {w | c v < ‖Q v w‖}) :=
        measureReal_biUnion_finset_le V _
    _ ≤ ∑ v ∈ V, (c v ^ (2 * k v))⁻¹ * ∫ w in Icc (-W) W, ‖Q v w ^ k v‖ ^ (2 : ℕ) :=
        sum_le_sum fun v hv => volume_large_le (hQ v) (hc v hv) (k v) W

/-- **The exceptional integral.**  If every top-scale block is at most `ρ` on `[−W, W]`, then on
any measurable `E ⊆ [−W, W]`: `∫_E |Σ_v Q_v R_v|² ≤ #V ρ² Σ_v ∫_E |R_v|²`. -/
theorem setIntegral_sum_blocks_le_of_bound {Q R : ℕ → ℝ → ℂ} (hR : ∀ v, Continuous (R v))
    (V : Finset ℕ) {ρ : ℝ} {E : Set ℝ} (hEm : MeasurableSet E) {W : ℝ} (hEs : E ⊆ Icc (-W) W)
    (hρ : ∀ v ∈ V, ∀ w ∈ Icc (-W) W, ‖Q v w‖ ≤ ρ) :
    (∫ w in E, ‖∑ v ∈ V, Q v w * R v w‖ ^ 2)
      ≤ (V.card : ℝ) * ρ ^ 2 * ∑ v ∈ V, ∫ w in E, ‖R v w‖ ^ 2 := by
  have hint : ∀ v, IntegrableOn (fun w => ‖R v w‖ ^ 2) E := fun v =>
    (((hR v).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set hEs
  have hmaj : IntegrableOn (fun w => (V.card : ℝ) * ρ ^ 2 * ∑ v ∈ V, ‖R v w‖ ^ 2) E :=
    (integrable_finsetSum V fun v _ => hint v).const_mul _
  have hpt : ∀ w ∈ E, ‖∑ v ∈ V, Q v w * R v w‖ ^ 2
      ≤ (V.card : ℝ) * ρ ^ 2 * ∑ v ∈ V, ‖R v w‖ ^ 2 := by
    intro w hw
    calc ‖∑ v ∈ V, Q v w * R v w‖ ^ 2
        ≤ (V.card : ℝ) * ∑ v ∈ V, ‖Q v w‖ ^ 2 * ‖R v w‖ ^ 2 :=
          normSq_sum_blocks_le (fun v => Q v w) (fun v => R v w)
      _ ≤ (V.card : ℝ) * ∑ v ∈ V, ρ ^ 2 * ‖R v w‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun v hv => ?_) (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (hρ v hv w (hEs hw)) 2) (by positivity)
      _ = (V.card : ℝ) * ρ ^ 2 * ∑ v ∈ V, ‖R v w‖ ^ 2 := by rw [← mul_sum]; ring
  calc (∫ w in E, ‖∑ v ∈ V, Q v w * R v w‖ ^ 2)
      ≤ ∫ w in E, (V.card : ℝ) * ρ ^ 2 * ∑ v ∈ V, ‖R v w‖ ^ 2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => by positivity) hmaj
          ((ae_restrict_iff' hEm).mpr (Filter.Eventually.of_forall hpt))
    _ = (V.card : ℝ) * ρ ^ 2 * ∑ v ∈ V, ∫ w in E, ‖R v w‖ ^ 2 := by
        rw [integral_const_mul, integral_finsetSum V fun v _ => hint v]

end

end GaloisForLFunctions.MatomakiRadziwill
