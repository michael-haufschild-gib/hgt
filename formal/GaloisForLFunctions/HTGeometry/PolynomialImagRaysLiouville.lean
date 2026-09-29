import GaloisForLFunctions.HTGeometry.SectorPhragmenLindelof
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# A polynomial Liouville theorem on the imaginary axis and four rays

An entire function `f` with an order-one envelope `|f(z)| ≤ exp(K(1+|z|)log(2+|z|))`, with
`|f(iy)| ≤ C(1+|y|)^N` on the imaginary axis, and with `|f| ≤ A(1+r)^N e^{ηr cos α}` on the four rays
`±r e^{±iα}` (for every `η > 0`, some `α ∈ (0, π/2)`) is a polynomial of degree at most `N`.

The remainder `h` in `f(z) = Σ_{i≤N} c_i z^i + z^{N+1} h(z)` (iterated difference quotients at `0`)
satisfies the hypotheses of the constant case `eq_const_of_imag_of_rays`, so it is constant, and the
imaginary-axis bound forces the constant to vanish.
-/
open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Iterated difference quotients at the origin. -/
def dslopeIter (f : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => f
  | n + 1 => dslope (dslopeIter f n) 0

theorem differentiable_dslopeIter {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    Differentiable ℂ (dslopeIter f n) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [← differentiableOn_univ] at ih ⊢
    exact (Complex.differentiableOn_dslope univ_mem).2 ih

/-- Taylor expansion with an entire remainder: `f z = Σ_{i<n} c_i z^i + z^n f_n(z)`. -/
theorem eq_sum_add_dslopeIter (f : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    f z = ∑ i ∈ Finset.range n, dslopeIter f i 0 * z ^ i + z ^ n * dslopeIter f n z := by
  induction n with
  | zero => simp [dslopeIter]
  | succ n ih =>
    have h := sub_smul_dslope (dslopeIter f n) 0 z
    simp only [sub_zero, smul_eq_mul] at h
    have hstep : dslopeIter f n z = dslopeIter f n 0 + z * dslopeIter f (n + 1) z := by
      show _ = _ + z * dslope (dslopeIter f n) 0 z
      linear_combination -h
    rw [ih, Finset.sum_range_succ, hstep]
    ring

theorem norm_sum_mul_pow_le (c : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    ‖∑ i ∈ Finset.range (N + 1), c i * z ^ i‖ ≤
      (∑ i ∈ Finset.range (N + 1), ‖c i‖) * (1 + ‖z‖) ^ N := by
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hi' : i ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  calc ‖z‖ ^ i ≤ (1 + ‖z‖) ^ i := pow_le_pow_left₀ (norm_nonneg _) (by linarith) i
    _ ≤ (1 + ‖z‖) ^ N := pow_le_pow_right₀ (by linarith [norm_nonneg z]) hi'

theorem one_add_pow_div_pow_succ_le {t : ℝ} (ht : 1 ≤ t) (N : ℕ) :
    (1 + t) ^ N / t ^ (N + 1) ≤ 2 ^ N := by
  have ht0 : 0 < t := by linarith
  rw [div_le_iff₀ (by positivity)]
  calc (1 + t) ^ N ≤ (2 * t) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    _ = 2 ^ N * t ^ N := mul_pow _ _ _
    _ ≤ 2 ^ N * t ^ (N + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) (by positivity)

/-- **Polynomial Liouville theorem on the imaginary axis and four rays.**  An entire function of
order one whose growth is at most `(1 + |y|)^N` on the imaginary axis and at most
`(1 + r)^N e^{η r cos α}` on four rays near it, for every `η > 0`, is a polynomial of degree at most
`N`: it equals its Taylor polynomial of degree `N`. -/
theorem eq_taylor_of_imag_of_rays {f : ℂ → ℂ} (hf : Differentiable ℂ f) {K C : ℝ} (N : ℕ)
    (hK : 0 ≤ K) (hgrowth : ∀ z, ‖f z‖ ≤ Real.exp (K * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (him : ∀ y : ℝ, ‖f (y * I)‖ ≤ C * (1 + |y|) ^ N)
    (hrays : ∀ η > 0, ∃ α ∈ Ioo 0 (Real.pi / 2), ∃ A : ℝ, ∀ r : ℝ, 0 ≤ r →
      ‖f (r * cexp (α * I))‖ ≤ A * (1 + r) ^ N * Real.exp (η * r * Real.cos α) ∧
        ‖f (r * cexp (-α * I))‖ ≤ A * (1 + r) ^ N * Real.exp (η * r * Real.cos α) ∧
        ‖f (-(r * cexp (α * I)))‖ ≤ A * (1 + r) ^ N * Real.exp (η * r * Real.cos α) ∧
        ‖f (-(r * cexp (-α * I)))‖ ≤ A * (1 + r) ^ N * Real.exp (η * r * Real.cos α))
    (z : ℂ) : f z = ∑ i ∈ Finset.range (N + 1), dslopeIter f i 0 * z ^ i := by
  set c : ℕ → ℂ := fun i => dslopeIter f i 0
  set h := dslopeIter f (N + 1)
  have hh : Differentiable ℂ h := differentiable_dslopeIter hf (N + 1)
  set B := ∑ i ∈ Finset.range (N + 1), ‖c i‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hdec : ∀ w, f w = ∑ i ∈ Finset.range (N + 1), c i * w ^ i + w ^ (N + 1) * h w :=
    fun w => eq_sum_add_dslopeIter f (N + 1) w
  have hT : ∀ w, ‖∑ i ∈ Finset.range (N + 1), c i * w ^ i‖ ≤ B * (1 + ‖w‖) ^ N :=
    norm_sum_mul_pow_le c N
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hh.continuous.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Metric.mem_closedBall_self zero_le_one))
  have hsmall : ∀ w, ‖w‖ ≤ 1 → ‖h w‖ ≤ M := fun w hw => hM w (mem_closedBall_zero_iff.2 hw)
  have hlarge : ∀ w, 1 ≤ ‖w‖ → ‖h w‖ ≤ (‖f w‖ + B * (1 + ‖w‖) ^ N) / ‖w‖ ^ (N + 1) := by
    intro w hw
    have hw0 : 0 < ‖w‖ ^ (N + 1) := by positivity
    rw [le_div_iff₀ hw0]
    have h1 : w ^ (N + 1) * h w = f w - ∑ i ∈ Finset.range (N + 1), c i * w ^ i := by
      rw [hdec w]; ring
    calc ‖h w‖ * ‖w‖ ^ (N + 1) = ‖w ^ (N + 1) * h w‖ := by rw [norm_mul, norm_pow, mul_comm]
      _ = ‖f w - ∑ i ∈ Finset.range (N + 1), c i * w ^ i‖ := by rw [h1]
      _ ≤ ‖f w‖ + ‖∑ i ∈ Finset.range (N + 1), c i * w ^ i‖ := norm_sub_le _ _
      _ ≤ ‖f w‖ + B * (1 + ‖w‖) ^ N := by linarith [hT w]
  -- growth of `h` along the imaginary axis
  set C' := max C 0
  have him' : ∀ y : ℝ, ‖h (y * I)‖ ≤ max M ((C' + B) * 2 ^ N) := by
    intro y
    have hn : ‖(y : ℂ) * I‖ = |y| := by simp
    rcases le_or_gt |y| 1 with hy | hy
    · exact (hsmall _ (by rw [hn]; exact hy)).trans (le_max_left _ _)
    · have h1 := hlarge _ (by rw [hn]; exact hy.le)
      rw [hn] at h1
      have hf1 : ‖f (y * I)‖ ≤ C' * (1 + |y|) ^ N :=
        (him y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      refine h1.trans (le_trans ?_ (le_max_right _ _))
      calc (‖f (y * I)‖ + B * (1 + |y|) ^ N) / |y| ^ (N + 1)
          ≤ (C' + B) * ((1 + |y|) ^ N / |y| ^ (N + 1)) := by
            rw [mul_div_assoc']
            gcongr
            linarith
        _ ≤ (C' + B) * 2 ^ N :=
            mul_le_mul_of_nonneg_left (one_add_pow_div_pow_succ_le hy.le N)
              (add_nonneg (le_max_right _ _) hB)
  -- growth of `h` on the rays
  have hrays' : ∀ η > 0, ∃ α ∈ Ioo 0 (Real.pi / 2), ∃ A : ℝ, ∀ r : ℝ, 0 ≤ r →
      ‖h (r * cexp (α * I))‖ ≤ A * Real.exp (η * r * Real.cos α) ∧
        ‖h (r * cexp (-α * I))‖ ≤ A * Real.exp (η * r * Real.cos α) ∧
        ‖h (-(r * cexp (α * I)))‖ ≤ A * Real.exp (η * r * Real.cos α) ∧
        ‖h (-(r * cexp (-α * I)))‖ ≤ A * Real.exp (η * r * Real.cos α) := by
    intro η hη
    obtain ⟨α, hα, A, hA⟩ := hrays η hη
    have hcos : 0 < Real.cos α :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
    refine ⟨α, hα, max M ((|A| + B) * 2 ^ N), fun r hr => ?_⟩
    have hexp1 : 1 ≤ Real.exp (η * r * Real.cos α) := Real.one_le_exp (by positivity)
    have hpt : ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ A * (1 + r) ^ N * Real.exp (η * r * Real.cos α) →
        ‖h w‖ ≤ max M ((|A| + B) * 2 ^ N) * Real.exp (η * r * Real.cos α) := by
      intro w hw hfw
      have hA0 : 0 ≤ max M ((|A| + B) * 2 ^ N) := le_max_of_le_left hM0
      rcases le_or_gt r 1 with hr1 | hr1
      · calc ‖h w‖ ≤ M := hsmall w (by rw [hw]; exact hr1)
          _ ≤ max M ((|A| + B) * 2 ^ N) := le_max_left _ _
          _ ≤ _ := le_mul_of_one_le_right hA0 hexp1
      · have h1 := hlarge w (by rw [hw]; exact hr1.le)
        rw [hw] at h1
        have hfw' : ‖f w‖ ≤ |A| * (1 + r) ^ N * Real.exp (η * r * Real.cos α) :=
          hfw.trans (by gcongr; exact le_abs_self A)
        refine h1.trans ?_
        calc (‖f w‖ + B * (1 + r) ^ N) / r ^ (N + 1)
            ≤ ((|A| + B) * Real.exp (η * r * Real.cos α)) * ((1 + r) ^ N / r ^ (N + 1)) := by
              rw [mul_div_assoc']
              gcongr
              nlinarith [mul_le_mul_of_nonneg_left hexp1 (mul_nonneg hB
                (by positivity : (0 : ℝ) ≤ (1 + r) ^ N))]
          _ ≤ ((|A| + B) * Real.exp (η * r * Real.cos α)) * 2 ^ N :=
              mul_le_mul_of_nonneg_left (one_add_pow_div_pow_succ_le hr1.le N) (by positivity)
          _ = (|A| + B) * 2 ^ N * Real.exp (η * r * Real.cos α) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
    have hn1 : ‖(r : ℂ) * cexp (α * I)‖ = r := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hr]
    have hn2 : ‖(r : ℂ) * cexp (-α * I)‖ = r := by
      rw [show (-(α : ℂ)) = ((-α : ℝ) : ℂ) by push_cast; ring, norm_mul,
        Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hr]
    obtain ⟨h1, h2, h3, h4⟩ := hA r hr
    exact ⟨hpt _ hn1 h1, hpt _ hn2 h2, hpt _ (by rw [norm_neg, hn1]) h3,
      hpt _ (by rw [norm_neg, hn2]) h4⟩
  -- order-one growth of `h`
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K' := K + N + (Real.log (1 + B) + Real.log (max M 1)) / Real.log 2
  have hK' : 0 ≤ K' := by
    have h1 : 0 ≤ Real.log (1 + B) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log (max M 1) := Real.log_nonneg (le_max_right _ _)
    positivity
  have hgrowth' : ∀ w, ‖h w‖ ≤ Real.exp (K' * (1 + ‖w‖) * Real.log (2 + ‖w‖)) := by
    intro w
    set s := (1 + ‖w‖) * Real.log (2 + ‖w‖) with hs
    have hs2 : Real.log 2 ≤ s := by
      have h1 : Real.log 2 ≤ Real.log (2 + ‖w‖) :=
        Real.log_le_log (by norm_num) (by linarith [norm_nonneg w])
      have h2 : 0 ≤ Real.log (2 + ‖w‖) := Real.log_nonneg (by linarith [norm_nonneg w])
      nlinarith [norm_nonneg w]
    have hs0 : 0 ≤ s := hl2.le.trans hs2
    have hK's : K' * (1 + ‖w‖) * Real.log (2 + ‖w‖) = K' * s := by rw [hs]; ring
    rw [hK's]
    have hdiv : ∀ a : ℝ, 0 ≤ a → a / Real.log 2 * s ≥ a := fun a ha => by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hs2 ha
    rcases le_or_gt ‖w‖ 1 with hw | hw
    · have hlM := hdiv _ (Real.log_nonneg (le_max_right M 1))
      calc ‖h w‖ ≤ max M 1 := (hsmall w hw).trans (le_max_left _ _)
        _ = Real.exp (Real.log (max M 1)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp (K' * s) := by
            refine Real.exp_le_exp.2 ?_
            have h1 : 0 ≤ Real.log (1 + B) / Real.log 2 * s :=
              mul_nonneg (div_nonneg (Real.log_nonneg (by linarith)) hl2.le) hs0
            have h2 : 0 ≤ (K + N) * s := mul_nonneg (by positivity) hs0
            have : K' * s = (K + N) * s + Real.log (1 + B) / Real.log 2 * s +
                Real.log (max M 1) / Real.log 2 * s := by
              simp only [K']; ring
            linarith
    · have h1 := hlarge w hw.le
      have hpow : 1 ≤ ‖w‖ ^ (N + 1) := one_le_pow₀ hw.le
      have hnum : 0 ≤ ‖f w‖ + B * (1 + ‖w‖) ^ N := by positivity
      have h2 : ‖h w‖ ≤ ‖f w‖ + B * (1 + ‖w‖) ^ N :=
        h1.trans (div_le_self hnum hpow)
      have hpowexp : (1 + ‖w‖) ^ N ≤ Real.exp (N * s) := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < (1 + ‖w‖) ^ N), Real.log_pow]
        refine Real.exp_le_exp.2 ?_
        have hl1 : Real.log (1 + ‖w‖) ≤ Real.log (2 + ‖w‖) :=
          Real.log_le_log (by positivity) (by linarith)
        have hl0 : 0 ≤ Real.log (2 + ‖w‖) := Real.log_nonneg (by linarith [norm_nonneg w])
        have : Real.log (2 + ‖w‖) ≤ s := by
          rw [hs]; nlinarith [norm_nonneg w]
        have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith
      have hfexp : ‖f w‖ ≤ Real.exp (K * s) := by
        have := hgrowth w; rwa [show K * (1 + ‖w‖) * Real.log (2 + ‖w‖) = K * s by rw [hs]; ring]
          at this
      have hKN1 : Real.exp (K * s) ≤ Real.exp ((K + N) * s) :=
        Real.exp_le_exp.2 (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
      have hKN2 : Real.exp (N * s) ≤ Real.exp ((K + N) * s) :=
        Real.exp_le_exp.2 (by nlinarith)
      calc ‖h w‖ ≤ ‖f w‖ + B * (1 + ‖w‖) ^ N := h2
        _ ≤ Real.exp ((K + N) * s) + B * Real.exp ((K + N) * s) := by
            gcongr
            · exact hfexp.trans hKN1
            · exact hpowexp.trans hKN2
        _ = Real.exp (Real.log (1 + B)) * Real.exp ((K + N) * s) := by
            rw [Real.exp_log (by linarith)]; ring
        _ ≤ Real.exp (K' * s) := by
            rw [← Real.exp_add]
            refine Real.exp_le_exp.2 ?_
            have h1 := hdiv _ (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + B))
            have h3 : 0 ≤ Real.log (max M 1) / Real.log 2 * s :=
              mul_nonneg (div_nonneg (Real.log_nonneg (le_max_right _ _)) hl2.le) hs0
            have : K' * s = (K + N) * s + Real.log (1 + B) / Real.log 2 * s +
                Real.log (max M 1) / Real.log 2 * s := by
              simp only [K']; ring
            linarith
  have hconst := _root_.HTGeometry.eq_const_of_imag_of_rays hh hK' hgrowth' him' hrays'
  -- the remainder constant vanishes by the imaginary-axis bound
  have hc0 : h 0 = 0 := by
    by_contra hne
    have hpos : 0 < ‖h 0‖ := norm_pos_iff.2 hne
    set y : ℝ := (C' + B) * 2 ^ N / ‖h 0‖ + 1
    have hy1 : 1 ≤ y := by
      have : 0 ≤ (C' + B) * 2 ^ N / ‖h 0‖ :=
        div_nonneg (mul_nonneg (add_nonneg (le_max_right _ _) hB) (by positivity)) hpos.le
      linarith
    have hn : ‖(y : ℂ) * I‖ = y := by simp [abs_of_pos (by linarith : (0 : ℝ) < y)]
    have h1 := hlarge _ (by rw [hn]; exact hy1)
    rw [hconst, hn] at h1
    have hf1 : ‖f (y * I)‖ ≤ C' * (1 + y) ^ N := by
      have := him y
      rw [abs_of_pos (by linarith : (0 : ℝ) < y)] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have h2 : ‖h 0‖ ≤ (C' + B) * 2 ^ N / y := by
      refine h1.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc (‖f (y * I)‖ + B * (1 + y) ^ N) * y ≤ ((C' + B) * (1 + y) ^ N) * y := by
            gcongr; linarith
        _ ≤ ((C' + B) * (2 ^ N * y ^ N)) * y := by
            have hpy : (1 + y) ^ N ≤ 2 ^ N * y ^ N :=
              calc (1 + y) ^ N ≤ (2 * y) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
                _ = 2 ^ N * y ^ N := mul_pow _ _ _
            have hCB : 0 ≤ C' + B := add_nonneg (le_max_right _ _) hB
            gcongr
        _ = (C' + B) * 2 ^ N * y ^ (N + 1) := by ring
    rw [le_div_iff₀ (by linarith)] at h2
    have : ‖h 0‖ * y = (C' + B) * 2 ^ N + ‖h 0‖ := by
      simp only [y]; field_simp
    linarith
  rw [hdec z, hconst, hc0, mul_zero, add_zero]

end

end GaloisForLFunctions.HTGeometry
