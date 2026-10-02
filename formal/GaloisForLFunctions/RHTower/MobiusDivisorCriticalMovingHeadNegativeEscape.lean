import GaloisForLFunctions.RHTower.MobiusDivisorCriticalMovingHeadMellin

/-!
# Negative escape of the complete moving prime head

The centered Mellin jet forces negative linear excursions even after the
actual old-prime head is subtracted. The boundary constant is retained in
the compensated-transform comparison. No pointwise Tauberian converse or
sign premise is used.
-/

noncomputable section
open Filter Topology MeasureTheory Set
namespace RHTower

private theorem moving_compensated_integral (C δ : ℝ) (hδ : 0 < δ)
    (hi : IntegrableOn
      (fun x : ℝ => x ^ (-(5 / 2 : ℝ) - δ) * criticalMovingPrimeHead x) (Ioi (1 : ℝ))) :
    IntegrableOn (fun x : ℝ => x ^ (-(5 / 2 : ℝ) - δ) *
      (criticalMovingPrimeHead x + C * x)) (Ioi (1 : ℝ)) ∧
    (∫ x in Ioi (1 : ℝ), x ^ (-(5 / 2 : ℝ) - δ) *
      (criticalMovingPrimeHead x + C * x)) =
        criticalSourceRealMellin criticalMovingPrimeHead δ + C / (1 / 2 + δ) := by
  have hp := (integrableOn_Ioi_rpow_of_lt
    (a := -(3 / 2 : ℝ) - δ) (by linarith) zero_lt_one).const_mul C
  have heq : ∀ x ∈ Ioi (1 : ℝ),
      x ^ (-(5 / 2 : ℝ) - δ) * (criticalMovingPrimeHead x + C * x) =
        x ^ (-(5 / 2 : ℝ) - δ) * criticalMovingPrimeHead x +
          C * x ^ (-(3 / 2 : ℝ) - δ) := by
    intro x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hr : x ^ (-(5 / 2 : ℝ) - δ) * x = x ^ (-(3 / 2 : ℝ) - δ) := by
      calc
        _ = x ^ (-(5 / 2 : ℝ) - δ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
    linear_combination C * hr
  constructor
  · exact (hi.add hp).congr_fun (fun x hx => (heq x hx).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_add hi hp,
      integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    simp only [Real.one_rpow]
    change criticalSourceRealMellin criticalMovingPrimeHead δ +
      C * (-1 / (-(3 / 2 : ℝ) - δ + 1)) = _
    congr 1
    rw [show -(3 / 2 : ℝ) - δ + 1 = -(1 / 2 + δ) by ring]
    rw [div_neg, neg_div, neg_neg]
    ring

/-- The complete moving head admits no global linear lower bound. The
actual retained-prime cutoff is included in this unconditional statement. -/
theorem criticalMovingPrimeHead_negative_linear_escape (C : ℝ) :
    ∃ x : ℝ, 1 < x ∧ criticalMovingPrimeHead x < -C * x := by
  suffices h : ∀ K : ℝ, 0 ≤ K →
      ∃ x : ℝ, 1 < x ∧ criticalMovingPrimeHead x < -K * x by
    obtain ⟨x, hx, hb⟩ := h (max C 0) (le_max_right _ _)
    refine ⟨x, hx, hb.trans_le ?_⟩
    exact mul_le_mul_of_nonneg_right (neg_le_neg (le_max_left _ _)) (by linarith)
  intro K hK
  by_contra! hbound
  have hlim : Tendsto (fun δ : ℝ =>
      criticalSourceRealMellin criticalMovingPrimeHead δ + K / (1 / 2 + δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (-criticalRetainedPrimeBoundaryTransform 0 + 2 * K)) := by
    have hd : Tendsto (fun δ : ℝ => (1 / 2 : ℝ) + δ)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
      simpa using (tendsto_const_nhds.add
        (tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0)))
    have hk : Tendsto (fun δ : ℝ => K / (1 / 2 + δ))
        (𝓝[>] (0 : ℝ)) (𝓝 (2 * K)) := by
      convert (tendsto_const_nhds (x := K)).div hd (by norm_num) using 1 <;> first | rfl | ring
    exact criticalMovingPrimeHead_mellin_boundary.add hk
  have hevent := (criticalMovingPrimeHead_mellin_admission.and
    (criticalMovingPrimeHead_centered_slope_atTop.eventually
      (eventually_gt_atTop (4 * K)))).and self_mem_nhdsWithin
  obtain ⟨ε, ⟨hiε, hlarge⟩, hε⟩ := hevent.exists
  change 0 < ε at hε
  have hle : criticalSourceRealMellin criticalMovingPrimeHead ε + K / (1 / 2 + ε) ≤
      -criticalRetainedPrimeBoundaryTransform 0 + 2 * K := by
    apply ge_of_tendsto hlim
    filter_upwards [criticalMovingPrimeHead_mellin_admission, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hε)] with δ hiδ hδ hδε
    change 0 < δ at hδ
    change δ < ε at hδε
    obtain ⟨hie, he⟩ := moving_compensated_integral K ε hε hiε.1
    obtain ⟨hid, hd⟩ := moving_compensated_integral K δ hδ hiδ.1
    rw [← he, ← hd]
    apply integral_mono_ae hie hid
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
    have hb := hbound x hx
    linarith
  have hbig : 4 * K * ε < criticalSourceRealMellin criticalMovingPrimeHead ε +
      criticalRetainedPrimeBoundaryTransform 0 := (lt_div_iff₀ hε).mp hlarge
  have hden : 0 < (1 / 2 : ℝ) + ε := by linarith
  have hmul := mul_le_mul_of_nonneg_right hle hden.le
  have hquot : K / (1 / 2 + ε) * (1 / 2 + ε) = K := div_mul_cancel₀ _ hden.ne'
  have hstrict := mul_lt_mul_of_pos_right hbig hden
  nlinarith [mul_nonneg hK (sq_nonneg ε)]

private theorem moving_Abel_locally_bounded (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, x ≤ R → |criticalContinuousAbel x| ≤ B := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max R 1)
  let b : ℕ → ℝ := fun k => |criticalContinuousAbel k| +
    (Real.sqrt N + Real.sqrt k) * |psiDefect k|
  have hb : ∀ k, 0 ≤ b k := fun k => by dsimp [b]; positivity
  refine ⟨∑ k ∈ Finset.range (N + 1), b k, Finset.sum_nonneg (fun k _ => hb k), ?_⟩
  intro x hx
  by_cases hx1 : x ≤ 1
  · rw [criticalContinuousAbel_eq_zero_le_one hx1, abs_zero]
    exact Finset.sum_nonneg (fun k _ => hb k)
  have hx0 : 0 < x := by linarith
  have hxN : x ≤ N := hx.trans ((le_max_left _ _).trans hN)
  have hk : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0.le).mpr (by simpa using (lt_of_not_ge hx1).le)
  have hkx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxk : x ≤ (⌊x⌋₊ + 1 : ℕ) := by exact_mod_cast (Nat.lt_floor_add_one x).le
  have hkN : ⌊x⌋₊ ≤ N := by exact_mod_cast hkx.trans hxN
  have he := congrArg Complex.re
    (squareRootSummatoryPrimitive_between criticalSourceCoeff hk hkx hxk)
  rw [criticalSourceCoeff_cumulative _ hk] at he
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at he
  change criticalContinuousAbel x = criticalContinuousAbel ⌊x⌋₊ +
    (Real.sqrt x - Real.sqrt ⌊x⌋₊) * psiDefect ⌊x⌋₊ at he
  have hs : |Real.sqrt x - Real.sqrt ⌊x⌋₊| ≤ Real.sqrt N + Real.sqrt ⌊x⌋₊ :=
    (abs_sub _ _).trans (by
      rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
      gcongr)
  calc
    |criticalContinuousAbel x| ≤ b ⌊x⌋₊ := by
      rw [he]
      exact (abs_add_le _ _).trans (by
        rw [abs_mul]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hs (abs_nonneg _)))
    _ ≤ ∑ k ∈ Finset.range (N + 1), b k :=
      Finset.single_le_sum (fun k _ => hb k) (Finset.mem_range.mpr (by omega))

private theorem movingHead_locally_bounded (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 < x → x ≤ R → |criticalMovingPrimeHead x| ≤ B := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max R 1)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  obtain ⟨B, hB, hb⟩ := moving_Abel_locally_bounded N
  let S := (Finset.range N).subtype Nat.Prime
  let BF : ℝ := ∑ p ∈ S, Real.sqrt (p : ℝ) * B
  let BG : ℝ := ∑ p ∈ Finset.range (N + 1), Real.sqrt (p : ℝ) * B
  have hBF : 0 ≤ BF := Finset.sum_nonneg (fun _ _ => by positivity)
  have hBG : 0 ≤ BG := Finset.sum_nonneg (fun _ _ => by positivity)
  refine ⟨B + BF + BG, by positivity, ?_⟩
  intro x hx1 hxR
  have hxN : x ≤ N := hxR.trans ((le_max_left _ _).trans hN)
  have hAb : |criticalContinuousAbel x| ≤ B := hb x hxN
  have hFb : |(criticalPrimeAbelHead x).re| ≤ BF := by
    rw [criticalPrimeAbelHead_eq_finite x N hxN, Complex.re_sum]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro p _
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply mul_le_mul_of_nonneg_left (hb _ ?_) (Real.sqrt_nonneg _)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
    apply (div_le_iff₀ hp0).mpr
    exact hxN.trans (le_mul_of_one_le_right hN0 hp1)
  have hGb : |criticalRetainedPrimeHead x| ≤ BG := by
    rw [criticalRetainedPrimeHead_eq_finite hx1]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ p ∈ retainedPrimeCutoff x, Real.sqrt (p : ℝ) * B := by
        apply Finset.sum_le_sum
        intro p hp
        have hpp := (Finset.mem_filter.mp hp).2
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
        unfold criticalRetainedPrimeHeadAtom
        split_ifs
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          apply mul_le_mul_of_nonneg_left (hb _ ?_) (Real.sqrt_nonneg _)
          apply (div_le_iff₀ hp0).mpr
          exact hxN.trans (le_mul_of_one_le_right hN0 hp1)
        · simp only [abs_zero]
          positivity
      _ ≤ BG := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
        intro p hp
        have hpF := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
        have hFN : ⌊x⌋₊ ≤ N := by
          exact_mod_cast (Nat.floor_le (le_of_lt (lt_trans zero_lt_one hx1))).trans hxN
        exact Finset.mem_range.mpr (by omega)
  unfold criticalMovingPrimeHead
  calc
    |criticalContinuousAbel x + (criticalPrimeAbelHead x).re - criticalRetainedPrimeHead x| ≤
        |criticalContinuousAbel x + (criticalPrimeAbelHead x).re| + |criticalRetainedPrimeHead x| :=
      abs_sub _ _
    _ ≤ (|criticalContinuousAbel x| + |(criticalPrimeAbelHead x).re|) +
        |criticalRetainedPrimeHead x| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ B + BF + BG := add_le_add (add_le_add hAb hFb) hGb

/-- Negative linear excursions of the complete moving head occur beyond
every cutoff, with the old-prime contribution retained exactly. -/
theorem criticalMovingPrimeHead_cofinal_negative_linear_escape (C X : ℝ) :
    ∃ x : ℝ, X < x ∧ 1 < x ∧ criticalMovingPrimeHead x < -C * x := by
  obtain ⟨B, hB, hb⟩ := movingHead_locally_bounded X
  obtain ⟨x, hx1, hxneg⟩ := criticalMovingPrimeHead_negative_linear_escape (max C B)
  have hxX : X < x := by
    by_contra! hle
    have hlow := (abs_le.mp (hb x hx1 hle)).1
    have hKB : B ≤ max C B := le_max_right _ _
    have hK0 : 0 ≤ max C B := hB.trans hKB
    have hmul : B ≤ max C B * x := hKB.trans (le_mul_of_one_le_right hK0 hx1.le)
    nlinarith
  refine ⟨x, hxX, hx1, hxneg.trans_le ?_⟩
  exact mul_le_mul_of_nonneg_right (neg_le_neg (le_max_left _ _)) (by linarith)

end RHTower
