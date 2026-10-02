import GaloisForLFunctions.RHTower.ZetaChiIntegerStationaryPackets
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Coherent fourth-grade root packets

The literal fourth-root saddle phase is quadratically close to an integer
linear phase on a common box. Complete nonnegative weighted packets therefore
retain their mass. An explicit family of boxes disproves extension of the
degree-two square-root/log operator scale to arbitrary fourth-grade families.
The logarithmic saddle identity and the full packet are retained throughout.
-/

noncomputable section
open Complex Set
open scoped BigOperators
namespace RHTower

private theorem sqrt_pair_mem_box {N H x y : ℝ} (hN : 0 < N) (hH : 0 ≤ H)
    (hx : x ∈ Icc N (N + H)) (hy : y ∈ Icc N (N + H)) :
    Real.sqrt (x * y) ∈ Icc N (N + H) := by
  have hx0 := hN.le.trans hx.1
  have hy0 := hN.le.trans hy.1
  constructor
  · apply Real.le_sqrt_of_sq_le
    simpa only [pow_two] using mul_le_mul hx.1 hy.1 hN.le hx0
  · apply (Real.sqrt_le_left (by positivity : 0 ≤ N + H)).mpr
    simpa only [pow_two] using mul_le_mul hx.2 hy.2 hy0 (by positivity : 0 ≤ N + H)

private theorem sqrt_pair_defect_box {N H x y : ℝ} (hN : 0 < N) (hH : 0 ≤ H)
    (hx : x ∈ Icc N (N + H)) (hy : y ∈ Icc N (N + H)) :
    0 ≤ x + y - 2 * Real.sqrt (x * y) ∧
      x + y - 2 * Real.sqrt (x * y) ≤ H ^ 2 / (4 * N) := by
  have hx0 := hN.le.trans hx.1
  have hy0 := hN.le.trans hy.1
  have hs := Real.sq_sqrt (mul_nonneg hx0 hy0)
  have hg := sqrt_pair_mem_box hN hH hx hy
  have hn : 0 ≤ x + y - 2 * Real.sqrt (x * y) := by
    have hh : (2 * Real.sqrt (x * y)) ^ 2 ≤ (x + y) ^ 2 := by
      nlinarith [sq_nonneg (x - y)]
    have hh' := (sq_le_sq₀ (by positivity : 0 ≤ 2 * Real.sqrt (x * y)) (by positivity : 0 ≤ x + y)).mp hh
    linarith only [hh']
  refine ⟨hn, ?_⟩
  have hab : |x - y| ≤ H := abs_le.mpr ⟨by linarith only [hx.1, hy.2], by linarith only [hx.2, hy.1]⟩
  have hsq : (x - y) ^ 2 ≤ H ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2
  have he : (x + y - 2 * Real.sqrt (x * y)) * (x + y + 2 * Real.sqrt (x * y)) = (x - y) ^ 2 := by
    nlinarith only [hs]
  have hmul := mul_nonneg hn (show 0 ≤ x + y + 2 * Real.sqrt (x * y) - 4 * N by linarith only [hx.1, hy.1, hg.1])
  apply (le_div_iff₀ (by positivity : 0 < 4 * N)).mpr
  nlinarith only [hmul, he, hsq]

/-- The literal fourth-root saddle radius. -/
def chiDegreeFourRoot (p q r s : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (p * q) * Real.sqrt (r * s))

/-- The entire fourth-root phase differs from its integer linear phase only
quadratically across a common box. -/
theorem chiDegreeFourRoot_box_defect {N H p q r s : ℝ} (hN : 0 < N) (hH : 0 ≤ H)
    (hp : p ∈ Icc N (N + H)) (hq : q ∈ Icc N (N + H))
    (hr : r ∈ Icc N (N + H)) (hs : s ∈ Icc N (N + H)) :
    0 ≤ p + q + r + s - 4 * chiDegreeFourRoot p q r s ∧
      p + q + r + s - 4 * chiDegreeFourRoot p q r s ≤ H ^ 2 / N := by
  have h1 := sqrt_pair_defect_box hN hH hp hq
  have h2 := sqrt_pair_defect_box hN hH hr hs
  have h3 := sqrt_pair_defect_box hN hH (sqrt_pair_mem_box hN hH hp hq) (sqrt_pair_mem_box hN hH hr hs)
  have he : H ^ 2 / N = 4 * (H ^ 2 / (4 * N)) := by ring
  dsimp only [chiDegreeFourRoot]
  constructor
  · linarith only [h1.1, h2.1, h3.1]
  · rw [he]
    linarith only [h1.2, h2.2, h3.2]

/-- Every integer quadruple in a common square-root-width box has the same
fourth-grade orientation. No averaging or primality premise is used. -/
theorem norm_chiDegreeFourRoot_phase_sub_one_le {N H : ℝ} (hN : 0 < N) (hH : 0 ≤ H)
    (p q r s : ℕ) (hp : (p : ℝ) ∈ Icc N (N + H)) (hq : (q : ℝ) ∈ Icc N (N + H))
    (hr : (r : ℝ) ∈ Icc N (N + H)) (hs : (s : ℝ) ∈ Icc N (N + H)) :
    ‖bourgainOscillation (8 * Real.pi * chiDegreeFourRoot p q r s) - 1‖ ≤
      2 * Real.pi * H ^ 2 / N := by
  have hgap := chiDegreeFourRoot_box_defect hN hH hp hq hr hs
  have hint : bourgainOscillation (2 * Real.pi * ((p : ℝ) + q + r + s)) = 1 := by
    unfold bourgainOscillation
    have he : I * ((2 * Real.pi * ((p : ℝ) + q + r + s) : ℝ) : ℂ) =
        ((p + q + r + s : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by push_cast; ring
    rw [he, Complex.exp_nat_mul_two_pi_mul_I]
  rw [← hint]
  apply (norm_bourgainOscillation_sub_le _ _).trans
  have he : |8 * Real.pi * chiDegreeFourRoot p q r s -
      2 * Real.pi * ((p : ℝ) + q + r + s)| =
      2 * Real.pi * ((p : ℝ) + q + r + s - 4 * chiDegreeFourRoot p q r s) := by
    rw [show 8 * Real.pi * chiDegreeFourRoot p q r s -
        2 * Real.pi * ((p : ℝ) + q + r + s) =
        -(2 * Real.pi * ((p : ℝ) + q + r + s - 4 * chiDegreeFourRoot p q r s)) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (by positivity) hgap.1)]
  rw [he]
  calc
    _ ≤ 2 * Real.pi * (H ^ 2 / N) := mul_le_mul_of_nonneg_left hgap.2 (by positivity)
    _ = _ := by ring

/-- Complete positive fourfold packets retain their coefficient mass. Their
relative phase error is quadratic in the common packet width. -/
theorem norm_chiDegreeFourRoot_packet_error_le {N H : ℝ} (hN : 0 < N) (hH : 0 ≤ H)
    (S : Finset ℕ) (hS : ∀ p ∈ S, (p : ℝ) ∈ Icc N (N + H))
    (a b c d : ℕ → ℝ) (ha : ∀ p ∈ S, 0 ≤ a p) (hb : ∀ p ∈ S, 0 ≤ b p)
    (hc : ∀ p ∈ S, 0 ≤ c p) (hd : ∀ p ∈ S, 0 ≤ d p) :
    ‖∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, ∑ s ∈ S,
      ((a p * b q * c r * d s : ℝ) : ℂ) *
        (bourgainOscillation (8 * Real.pi * chiDegreeFourRoot p q r s) - 1)‖ ≤
      (2 * Real.pi * H ^ 2 / N) * (∑ p ∈ S, a p) * (∑ q ∈ S, b q) *
        (∑ r ∈ S, c r) * (∑ s ∈ S, d s) := by
  calc
    _ ≤ ∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, ∑ s ∈ S,
        ‖((a p * b q * c r * d s : ℝ) : ℂ) *
          (bourgainOscillation (8 * Real.pi * chiDegreeFourRoot p q r s) - 1)‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r _
      exact norm_sum_le _ _
    _ ≤ ∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, ∑ s ∈ S,
        (a p * b q * c r * d s) * (2 * Real.pi * H ^ 2 / N) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      have hn : 0 ≤ a p * b q * c r * d s :=
        mul_nonneg (mul_nonneg (mul_nonneg (ha p hp) (hb q hq)) (hc r hr)) (hd s hs)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
      exact mul_le_mul_of_nonneg_left
        (norm_chiDegreeFourRoot_phase_sub_one_le hN hH p q r s (hS p hp) (hS q hq) (hS r hr) (hS s hs)) hn
    _ = (2 * Real.pi * H ^ 2 / N) * (∑ s ∈ S, d s) * (∑ r ∈ S, c r) *
        (∑ q ∈ S, b q) * (∑ p ∈ S, a p) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by ring

/-- Exact fourth-root identification of the physical grade-four saddle. -/
theorem chiDegreeFourRoot_pow_four {p q r s : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    chiDegreeFourRoot p q r s ^ 4 = p * q * (r * s) := by
  unfold chiDegreeFourRoot
  calc
    _ = (Real.sqrt (Real.sqrt (p * q) * Real.sqrt (r * s)) ^ 2) ^ 2 := by ring
    _ = (Real.sqrt (p * q) * Real.sqrt (r * s)) ^ 2 := by rw [Real.sq_sqrt (by positivity)]
    _ = _ := by rw [mul_pow, Real.sq_sqrt (mul_nonneg hp hq), Real.sq_sqrt (mul_nonneg hr hs)]

/-- The fourth-root parameter has exactly the product logarithmic frequency. -/
theorem four_mul_log_chiDegreeFourRoot {p q r s : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s) :
    4 * Real.log (chiDegreeFourRoot p q r s) = Real.log p + Real.log q + Real.log r + Real.log s := by
  have he := Real.log_pow (chiDegreeFourRoot p q r s) 4
  rw [chiDegreeFourRoot_pow_four hp.le hq.le hr.le hs.le,
    Real.log_mul (mul_ne_zero hp.ne' hq.ne') (mul_ne_zero hr.ne' hs.ne'),
    Real.log_mul hp.ne' hq.ne', Real.log_mul hr.ne' hs.ne'] at he
  norm_num only [Nat.cast_ofNat] at he
  linarith only [he]

/-- Full integer quartic root packet, with no term deleted. -/
def chiDegreeFourRootPacket (S : Finset ℕ) : ℂ :=
  ∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, ∑ s ∈ S,
    bourgainOscillation (8 * Real.pi * chiDegreeFourRoot p q r s)

/-- The complete packet stays close to its full cardinality mass. -/
theorem norm_chiDegreeFourRootPacket_sub_mass_le {N H : ℝ} (hN : 0 < N) (hH : 0 ≤ H)
    (S : Finset ℕ) (hS : ∀ p ∈ S, (p : ℝ) ∈ Icc N (N + H)) :
    ‖chiDegreeFourRootPacket S - ((S.card : ℝ) ^ 4 : ℂ)‖ ≤
      (2 * Real.pi * H ^ 2 / N) * (S.card : ℝ) ^ 4 := by
  have hb := norm_chiDegreeFourRoot_packet_error_le hN hH S hS
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ _ => zero_le_one) (fun _ _ => zero_le_one)
    (fun _ _ => zero_le_one) (fun _ _ => zero_le_one)
  simp only [one_mul, Complex.ofReal_one, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, mul_one] at hb
  have he : (S.card : ℂ) * ((S.card : ℂ) * ((S.card : ℂ) * (S.card : ℂ))) =
      ((S.card : ℝ) ^ 4 : ℂ) := by push_cast; ring
  have he' : (2 * Real.pi * H ^ 2 / N) * (S.card : ℝ) * (S.card : ℝ) * (S.card : ℝ) * (S.card : ℝ) =
      (2 * Real.pi * H ^ 2 / N) * (S.card : ℝ) ^ 4 := by ring
  rw [he, he'] at hb
  exact hb

/-- A coherent quartic box carries at least half its full fourfold mass. -/
theorem chiDegreeFourRootPacket_norm_lower {N H : ℝ} (hN : 0 < N) (hH : 0 ≤ H)
    (hwidth : 2 * Real.pi * H ^ 2 / N ≤ 1 / 2)
    (S : Finset ℕ) (hS : ∀ p ∈ S, (p : ℝ) ∈ Icc N (N + H)) :
    (S.card : ℝ) ^ 4 / 2 ≤ ‖chiDegreeFourRootPacket S‖ := by
  have he := norm_chiDegreeFourRootPacket_sub_mass_le hN hH S hS
  have hmass : ‖((S.card : ℝ) ^ 4 : ℂ)‖ = (S.card : ℝ) ^ 4 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg S.card)]
  have ht : (S.card : ℝ) ^ 4 ≤
      ‖chiDegreeFourRootPacket S - ((S.card : ℝ) ^ 4 : ℂ)‖ + ‖chiDegreeFourRootPacket S‖ := by
    have hh := norm_add_le (((S.card : ℝ) ^ 4 : ℂ) - chiDegreeFourRootPacket S) (chiDegreeFourRootPacket S)
    rw [sub_add_cancel, hmass, norm_sub_rev] at hh
    exact hh
  have hh := mul_le_mul_of_nonneg_right hwidth (by positivity : 0 ≤ (S.card : ℝ) ^ 4)
  linarith only [he, ht, hh]

/-- The degree-two square-root/log operator scale cannot hold for all fourth-
grade coefficient families: complete positive integer boxes give counterexamples. -/
theorem exists_chiDegreeFourRootPacket_exceeds_sqrt_log (C : ℝ) :
    ∃ N : ℕ, 0 < N ∧ ∃ S : Finset ℕ, S ⊆ Finset.Icc N (2 * N) ∧
      C * Real.sqrt ((N : ℝ) * (1 + Real.log ((N : ℝ) + 1))) * (S.card : ℝ) ^ 2 <
        ‖chiDegreeFourRootPacket S‖ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (16 * |C| + 4)
  have hm4 : (4 : ℝ) < m := by linarith [abs_nonneg C]
  have hm0 : (0 : ℝ) < m := by linarith
  have hmNat : 0 < m := by exact_mod_cast hm0
  let N : ℕ := 16 * m ^ 4
  let S : Finset ℕ := Finset.Icc N (N + m ^ 2)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hNR : (N : ℝ) = 16 * (m : ℝ) ^ 4 := by dsimp only [N]; push_cast; rfl
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hm2 : 1 ≤ m ^ 2 := by have := pow_pos hmNat 2; omega
  have hH : m ^ 2 ≤ N := by
    have hh := Nat.mul_le_mul_left (m ^ 2) hm2
    have he : m ^ 2 * m ^ 2 = m ^ 4 := by ring
    rw [mul_one, he] at hh
    exact hh.trans (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 16))
  have hsub : S ⊆ Finset.Icc N (2 * N) := by
    intro p hp
    have hh := Finset.mem_Icc.mp hp
    exact Finset.mem_Icc.mpr ⟨hh.1, by omega⟩
  have hbox (p : ℕ) (hp : p ∈ S) : (p : ℝ) ∈ Icc (N : ℝ) ((N : ℝ) + (m : ℝ) ^ 2) := by
    have hh := Finset.mem_Icc.mp hp
    constructor
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2
  have hw : 2 * Real.pi * ((m : ℝ) ^ 2) ^ 2 / N ≤ 1 / 2 := by
    rw [div_le_iff₀ hN0, hNR]
    have hh := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (by positivity : 0 ≤ (m : ℝ) ^ 4)
    nlinarith only [hh]
  have hb := chiDegreeFourRootPacket_norm_lower hN0 (sq_nonneg (m : ℝ)) hw S hbox
  have hcard : S.card = m ^ 2 + 1 := by dsimp only [S]; rw [Nat.card_Icc]; omega
  have hc : (S.card : ℝ) = (m : ℝ) ^ 2 + 1 := by exact_mod_cast hcard
  have hc0 : 0 < (S.card : ℝ) := by rw [hc]; positivity
  have hsqrt : Real.sqrt (N : ℝ) = 4 * (m : ℝ) ^ 2 := by
    apply (Real.sqrt_eq_iff_eq_sq hN0.le (by positivity)).mpr
    rw [hNR]
    ring
  have hsqrt2 : Real.sqrt (Real.sqrt (N : ℝ)) = 2 * (m : ℝ) := by
    apply (Real.sqrt_eq_iff_eq_sq (Real.sqrt_nonneg _) (by positivity)).mpr
    rw [hsqrt]
    ring
  have hlog : 1 + Real.log ((N : ℝ) + 1) ≤ Real.sqrt N := by
    have hp : (N : ℝ) + 1 ≤ 32 * (m : ℝ) ^ 4 := by
      rw [hNR]
      have hh : (1 : ℝ) ≤ (m : ℝ) ^ 4 := by
        have hx : (1 : ℝ) ≤ m := by linarith
        simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hx 4
      linarith only [hh]
    have hl := Real.log_le_log (by positivity : 0 < (N : ℝ) + 1) hp
    rw [Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) (pow_ne_zero 4 hm0.ne'), Real.log_pow] at hl
    have hl32 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 32)
    have hlm := Real.log_le_sub_one_of_pos hm0
    have hquad := mul_nonneg (sub_nonneg.mpr hm4.le) (show 0 ≤ (m : ℝ) + 3 by positivity)
    rw [hsqrt]
    norm_num only [Nat.cast_ofNat] at hl
    nlinarith only [hl, hl32, hlm, hquad]
  have hscale : Real.sqrt ((N : ℝ) * (1 + Real.log ((N : ℝ) + 1))) ≤
      Real.sqrt (N : ℝ) * Real.sqrt (Real.sqrt (N : ℝ)) := by
    calc
      _ ≤ Real.sqrt ((N : ℝ) * Real.sqrt N) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog hN0.le)
      _ = _ := Real.sqrt_mul hN0.le _
  have hCm : 16 * |C| < (m : ℝ) := by linarith only [hm]
  have hpow := mul_lt_mul_of_pos_right hCm (pow_pos hm0 3)
  have hcardpow : (m : ℝ) ^ 4 < (S.card : ℝ) ^ 2 := by rw [hc]; nlinarith [sq_nonneg (m : ℝ)]
  have hstep : 16 * |C| * (m : ℝ) ^ 3 < (S.card : ℝ) ^ 2 := by nlinarith only [hpow, hcardpow]
  have hmul := mul_lt_mul_of_pos_right hstep (sq_pos_of_pos hc0)
  refine ⟨N, hN, S, hsub, ?_⟩
  apply lt_of_lt_of_le _ hb
  calc
    _ ≤ |C| * Real.sqrt ((N : ℝ) * (1 + Real.log ((N : ℝ) + 1))) * (S.card : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)) (sq_nonneg _)
    _ ≤ |C| * (Real.sqrt N * Real.sqrt (Real.sqrt N)) * (S.card : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (abs_nonneg C)) (sq_nonneg _)
    _ < (S.card : ℝ) ^ 4 / 2 := by
      rw [hsqrt2, hsqrt]
      nlinarith only [hmul]

end RHTower
