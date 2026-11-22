import Zeta23.WeilEF.Landau

/-! Restrict the local partial fraction to the inner third of the disk. -/

open Finset Metric Complex

noncomputable section

namespace QH.PrimeProgressions

/-- The logarithmic derivative after removing the inner zeros is uniformly bounded on
the sixth-radius disk. Zeros in the discarded annulus contribute a bounded sum. -/
theorem disk_log_derivative_expansion :
    ∃ A : ℝ, 0 < A ∧ ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r B : ℝ), 0 < r → 2 ≤ B →
      DifferentiableOn ℂ f (closedBall z₀ r) → f z₀ ≠ 0 →
      (∀ z ∈ closedBall z₀ r, ‖f z‖ ≤ B * ‖f z₀‖) →
      ∃ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ ρ ∈ closedBall z₀ (r / 3) ∧ f ρ = 0) ∧
        (∀ ρ ∈ Z, 1 ≤ analyticOrderNatAt f ρ) ∧
        (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ A * Real.log B ∧
        ∀ s ∈ closedBall z₀ (r / 6), f s ≠ 0 →
          ‖deriv f s / f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤ A * Real.log B / r := by
  classical
  let J := 1 / Real.log ((24 / 25 : ℝ) / (22 / 25))
  have hJ : 0 < J := one_div_pos.mpr (Real.log_pos (by norm_num))
  let A := 4 * 44795000 / 3 + 6 * J
  have hA : 0 < A := by dsimp only [A]; positivity
  have hJA : J ≤ A := by dsimp only [A]; linarith
  refine ⟨A, hA, ?_⟩
  intro f z₀ r B hr hB hf hf₀ hg
  let R := 3 * r / 4
  have hR : 0 < R := by dsimp only [R]; positivity
  have hlo : r / 3 ≤ 22 / 25 * R := by dsimp only [R]; linarith
  have hhi : 24 / 25 * R ≤ r := by dsimp only [R]; linarith
  have hfan : AnalyticOnNhd ℂ f (ball z₀ r) := fun z hz =>
    (hf.mono ball_subset_closedBall).analyticAt (isOpen_ball.mem_nhds hz)
  have hfa : AnalyticOnNhd ℂ f (closedBall z₀ R) := hfan.mono (closedBall_subset_ball (by dsimp only [R]; linarith))
  obtain ⟨W, hW, hmass, hpf⟩ := Zeta23.WeilEF.logDeriv_partial_fraction_disk hR hfa hf₀ hB
    (fun s hs => hg s (closedBall_subset_closedBall hhi hs))
  let Z := W.filter (fun ρ => ρ ∈ closedBall z₀ (r / 3))
  have hzeros (ρ : ℂ) : ρ ∈ Z ↔ ρ ∈ closedBall z₀ (r / 3) ∧ f ρ = 0 := by
    simp only [Z, mem_filter]
    have hw : ρ ∈ W ↔ ρ ∈ closedBall z₀ (22 / 25 * R) ∧ f ρ = 0 := by
      change ρ ∈ (W : Set ℂ) ↔ _
      rw [hW]
      rfl
    rw [hw]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨closedBall_subset_closedBall hlo h.1, h.2⟩, h.1⟩⟩
  have hsub : Z ⊆ W := filter_subset _ _
  have hJB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  refine ⟨Z, hzeros, ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨hρb, hρz⟩ := (hzeros ρ).mp hρ
    have hρu := closedBall_subset_ball (by linarith : r / 3 < r) hρb
    have hs₀ := mem_ball_self (x := z₀) hr
    have h₀ := (hfan _ hs₀).analyticOrderAt_eq_zero.mpr hf₀
    have hne := hfan.analyticOrderAt_ne_top_of_isPreconnected (convex_ball z₀ r).isPreconnected hs₀ hρu
      (by rw [h₀]; exact WithTop.zero_ne_top)
    rw [Nat.one_le_iff_ne_zero]
    intro h
    have hh := Nat.cast_analyticOrderNatAt hne
    rw [h, Nat.cast_zero] at hh
    exact ((hfan _ hρu).analyticOrderAt_ne_zero.mpr hρz) hh.symm
  · exact (sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ => Nat.cast_nonneg _)).trans
      (hmass.trans (mul_le_mul_of_nonneg_right hJA hJB))
  · intro s hs hfs
    have hfraction := hpf s (closedBall_subset_closedBall (by dsimp only [R]; linarith) hs) hfs
    let m := analyticOrderNatAt f
    let zterm (ρ : ℂ) := (m ρ : ℂ) / (s - ρ)
    have hdiff : ‖∑ ρ ∈ W \ Z, zterm ρ‖ ≤ 6 * (J * Real.log B) / r := by
      calc ‖∑ ρ ∈ W \ Z, zterm ρ‖ ≤ ∑ ρ ∈ W \ Z, ‖zterm ρ‖ := norm_sum_le _ _
        _ ≤ ∑ ρ ∈ W \ Z, (6 / r) * (m ρ : ℝ) := by
            apply sum_le_sum
            intro ρ hρ
            obtain ⟨hρW, hρZ⟩ := mem_sdiff.mp hρ
            have hρfar := fun hρb => hρZ (mem_filter.mpr ⟨hρW, hρb⟩)
            rw [mem_closedBall] at hs
            have hd : r / 6 ≤ ‖s - ρ‖ := by
              have hx : r / 3 < dist ρ z₀ := lt_of_not_ge fun h => hρfar (mem_closedBall.mpr h)
              have hd := dist_triangle ρ s z₀
              rw [dist_comm ρ s, Complex.dist_eq s ρ] at hd
              linarith only [hd, hx, hs]
            dsimp only [zterm]
            rw [norm_div, Complex.norm_natCast, div_le_iff₀ (lt_of_lt_of_le (by positivity) hd)]
            have h := mul_le_mul_of_nonneg_left hd (show 0 ≤ 6 / r * (m ρ : ℝ) by positivity)
            have he : 6 / r * (m ρ : ℝ) * (r / 6) = (m ρ : ℝ) := by field_simp
            rwa [he] at h
        _ ≤ _ := by
            rw [← mul_sum, show 6 * (J * Real.log B) / r = (6 / r) * (J * Real.log B) by ring]
            exact mul_le_mul_of_nonneg_left
              ((sum_le_sum_of_subset_of_nonneg sdiff_subset (fun ρ _ _ => Nat.cast_nonneg (m ρ))).trans hmass)
              (by positivity)
    have hsum : (∑ ρ ∈ W \ Z, zterm ρ) + ∑ ρ ∈ Z, zterm ρ = ∑ ρ ∈ W, zterm ρ := sum_sdiff hsub
    have he : deriv f s / f s - ∑ ρ ∈ Z, zterm ρ =
        (logDeriv f s - ∑ ρ ∈ W, zterm ρ) + ∑ ρ ∈ W \ Z, zterm ρ := by
      rw [← hsum, logDeriv_apply]
      ring
    change ‖deriv f s / f s - ∑ ρ ∈ Z, zterm ρ‖ ≤ _
    rw [he]
    refine (norm_add_le _ _).trans ((add_le_add hfraction hdiff).trans_eq ?_)
    dsimp only [R, A]
    field_simp [hr.ne']

end QH.PrimeProgressions
