import GaloisForLFunctions.RHTower.XiWindowQuotient
import GaloisForLFunctions.RHTower.XiFourthTraceExtendedCriticalLineBand
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion
import GaloisForLFunctions.HTGeometry.InverseDistanceBoxIntegral
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# `ξ'/ξ` is integrable against `1/(1 + x²)` on almost every vertical line of the right half-strip

For `½ < σ < 1` the vertical line `Re s = σ` may pass arbitrarily close to zeros of `ξ`, where
`ξ'/ξ` is large.  Averaging over `σ` controls this.  On a window of heights around `n ≥ 8`,

  `|ξ'/ξ(s)| ≤ C log n + Σ_{|Im ρ − n| < 2} 1/|s − ρ|`   (`norm_logDeriv_xi_le_window`),

the window has `O(log n)` zeros, and each singularity `1/|s − ρ|` is integrable over the box
`[½, 1] × [Im ρ − 3, Im ρ + 3]` with integral `≤ 16√3` (`lintegral_box_inv_norm_sub_le`).  Summing
against `1/(1 + n²)` gives a finite double integral.

**Theorem** (`ae_lintegral_xiLineMass_lt_top`).  For almost every `σ ∈ (½, 1)`,

  `∫_ℝ |ξ'/ξ(σ + ix)| / (1 + x²) dx < ∞`.

Low heights are handled by the critical-line band (zeros with `|Im ρ| < 12.16` lie on `Re s = ½`).
Negative heights are handled by the reflection `ξ'/ξ(s̄) = conj(ξ'/ξ(s))`.
-/

open Complex MeasureTheory Set Filter

namespace RHTower

noncomputable section

/-- The weighted modulus of `ξ'/ξ` on the vertical line `Re s = σ`. -/
def xiLineMass (σ x : ℝ) : ENNReal :=
  ENNReal.ofReal (‖logDeriv xi ((σ : ℂ) + x * I)‖ / (1 + x ^ 2))

/-- **Window majorant.** -/
theorem norm_logDeriv_xi_le_window {n : ℕ} (hn : 8 ≤ n) {σ x : ℝ} (hσ : σ ∈ Icc (1 / 2 : ℝ) 1)
    (hx : |x - n| ≤ 1) :
    ‖logDeriv xi ((σ : ℂ) + x * I)‖ ≤ windowLogConst * Real.log n +
      ∑ q ∈ windowCopySet n, 1 / ‖(σ : ℂ) + x * I - (q.1 : ℂ)‖ := by
  set s : ℂ := (σ : ℂ) + x * I with hs
  have hsum0 : 0 ≤ ∑ q ∈ windowCopySet n, 1 / ‖s - (q.1 : ℂ)‖ :=
    Finset.sum_nonneg fun q _ => by positivity
  have hlog0 : 0 ≤ windowLogConst * Real.log n :=
    mul_nonneg windowLogConst_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
  by_cases hxi : xi s = 0
  · rw [logDeriv_apply, hxi, div_zero, norm_zero]; linarith
  · have hre : s.re = σ := by simp [hs]
    have him : s.im = x := by simp [hs]
    have h := norm_logDeriv_xi_sub_window_le (s := s) (t₀ := n) (by exact_mod_cast hn)
      (by rw [hre]; exact hσ.1) (by rw [hre]; linarith [hσ.2]) (by rw [him]; exact hx) hxi
    have htri : ‖∑ q ∈ windowCopySet n, (s - (q.1 : ℂ))⁻¹‖ ≤
        ∑ q ∈ windowCopySet n, 1 / ‖s - (q.1 : ℂ)‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun q _ => ?_))
      rw [norm_inv, one_div]
    calc ‖logDeriv xi s‖ ≤ ‖logDeriv xi s - ∑ q ∈ windowCopySet n, (s - (q.1 : ℂ))⁻¹‖ +
          ‖∑ q ∈ windowCopySet n, (s - (q.1 : ℂ))⁻¹‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := add_le_add h htri

/-- **Reflection.**  `ξ'/ξ(s̄) = conj(ξ'/ξ(s))`. -/
theorem logDeriv_xi_starRingEnd (s : ℂ) : logDeriv xi (starRingEnd ℂ s) = starRingEnd ℂ (logDeriv xi s) := by
  have hcomp : (⇑(starRingEnd ℂ) ∘ xi ∘ ⇑(starRingEnd ℂ)) = xi := by
    funext z; simp only [Function.comp_apply, xi_conj, Complex.conj_conj]
  have hd : HasDerivAt xi (starRingEnd ℂ (deriv xi s)) (starRingEnd ℂ s) := by
    have h := (xi_differentiable s).hasDerivAt.conj_conj
    rw [hcomp] at h
    exact h
  rw [logDeriv_apply, logDeriv_apply, hd.deriv, xi_conj, map_div₀]

theorem xiLineMass_neg (σ x : ℝ) : xiLineMass σ (-x) = xiLineMass σ x := by
  unfold xiLineMass
  have e : (σ : ℂ) + ((-x : ℝ) : ℂ) * I = starRingEnd ℂ ((σ : ℂ) + x * I) := by
    apply Complex.ext <;> simp
  rw [e, logDeriv_xi_starRingEnd, Complex.norm_conj, neg_sq]

/-- **Low heights.**  For `½ < σ < 1`, the line meets no zero of `ξ` below height `8`. -/
theorem xi_ne_zero_of_low_height {σ x : ℝ} (hσ : 1 / 2 < σ) (hx : |x| ≤ 8) :
    xi ((σ : ℂ) + x * I) ≠ 0 := by
  intro h
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h
  have him : (q.1 : ℂ).im ^ 2 < 2365 / 16 := by
    rw [hq]; simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, zero_add,
      mul_one]
    nlinarith [sq_abs x, abs_nonneg x]
  have hre := xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q him
  rw [hq] at hre
  simp at hre
  linarith

theorem lintegral_xiLineMass_low_lt_top {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∫⁻ x in Icc (-8 : ℝ) 8, xiLineMass σ x < ⊤ := by
  have hcont : ContinuousOn (fun x : ℝ => ‖logDeriv xi ((σ : ℂ) + x * I)‖ / (1 + x ^ 2))
      (Icc (-8 : ℝ) 8) := by
    intro x hx
    have hne := xi_ne_zero_of_low_height hσ (abs_le.mpr hx)
    have hpath : ContinuousAt (fun x : ℝ => (σ : ℂ) + x * I) x := by fun_prop
    have hlog : ContinuousAt (logDeriv xi) ((σ : ℂ) + x * I) := by
      have h1 : ContinuousAt (deriv xi) ((σ : ℂ) + x * I) :=
        (xi_differentiable.deriv.continuous).continuousAt
      have h2 : ContinuousAt xi ((σ : ℂ) + x * I) := xi_differentiable.continuous.continuousAt
      have := h1.div h2 hne
      simpa [logDeriv] using this
    have hc := (hlog.comp (f := fun x : ℝ => (σ : ℂ) + (x : ℂ) * I) hpath).norm
    have hden : ContinuousAt (fun x : ℝ => 1 + x ^ 2) x := by fun_prop
    exact (hc.div hden (by positivity)).continuousWithinAt
  exact (hcont.integrableOn_compact isCompact_Icc).lintegral_lt_top

/-! ## The window decomposition -/

/-- The box integral of the singularity of one zero copy. -/
def windowBoxMass (q : XiZeroCopy) (σ : ℝ) : ENNReal :=
  ∫⁻ x in Icc ((q.1 : ℂ).im - 3) ((q.1 : ℂ).im + 3),
    ENNReal.ofReal (1 / ‖(σ : ℂ) + x * I - (q.1 : ℂ)‖)

/-- The weight `1/(1 + (n − ½)²)` of the height window `[n − ½, n + ½]`. -/
def pieceWeight (n : ℕ) : ℝ := 1 / (1 + ((n : ℝ) - 1 / 2) ^ 2)

theorem pieceWeight_nonneg (n : ℕ) : 0 ≤ pieceWeight n := by unfold pieceWeight; positivity

theorem measurable_inv_dist (ρ : ℂ) :
    Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / ‖(p.1 : ℂ) + p.2 * I - ρ‖) :=
  (measurable_const.div (by fun_prop : Continuous fun p : ℝ × ℝ =>
    ‖(p.1 : ℂ) + p.2 * I - ρ‖).measurable).ennreal_ofReal

theorem measurable_windowBoxMass (q : XiZeroCopy) : Measurable (windowBoxMass q) :=
  (measurable_inv_dist (q.1 : ℂ)).lintegral_prod_right'

/-- **One window.** -/
theorem lintegral_xiLineMass_piece_le {n : ℕ} (hn : 8 ≤ n) {σ : ℝ} (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) :
    ∫⁻ x in Icc ((n : ℝ) - 1 / 2) (n + 1 / 2), xiLineMass σ x ≤
      ENNReal.ofReal (pieceWeight n) * (ENNReal.ofReal (windowLogConst * Real.log n) +
        ∑ q ∈ windowCopySet n, windowBoxMass q σ) := by
  set J := Icc ((n : ℝ) - 1 / 2) (n + 1 / 2) with hJ
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ windowLogConst * Real.log n :=
    mul_nonneg windowLogConst_nonneg (Real.log_nonneg (by linarith))
  have hpt : ∀ x ∈ J, xiLineMass σ x ≤ ENNReal.ofReal (pieceWeight n) *
      (ENNReal.ofReal (windowLogConst * Real.log n) +
        ∑ q ∈ windowCopySet n, ENNReal.ofReal (1 / ‖(σ : ℂ) + x * I - (q.1 : ℂ)‖)) := by
    intro x hx
    have hxn : |x - n| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    have hmaj := norm_logDeriv_xi_le_window hn hσ hxn
    have hw : 1 / (1 + x ^ 2) ≤ pieceWeight n := by
      unfold pieceWeight
      apply one_div_le_one_div_of_le (by positivity)
      have : (n : ℝ) - 1 / 2 ≤ x := hx.1
      nlinarith
    rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => by positivity),
      ← ENNReal.ofReal_add hlog0 (Finset.sum_nonneg fun q _ => by positivity),
      ← ENNReal.ofReal_mul (pieceWeight_nonneg n)]
    unfold xiLineMass
    apply ENNReal.ofReal_le_ofReal
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul hw hmaj (norm_nonneg _) (pieceWeight_nonneg n)
  have hsub : ∀ q ∈ windowCopySet n, J ⊆ Icc ((q.1 : ℂ).im - 3) ((q.1 : ℂ).im + 3) := by
    intro q hq x hx
    have h := mem_windowCopySet.mp hq
    rw [abs_lt] at h
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmeasq : ∀ q ∈ windowCopySet n,
      Measurable fun x : ℝ => ENNReal.ofReal (1 / ‖(σ : ℂ) + x * I - (q.1 : ℂ)‖) :=
    fun q _ => (measurable_const.div (by fun_prop : Continuous fun x : ℝ =>
      ‖(σ : ℂ) + x * I - (q.1 : ℂ)‖).measurable).ennreal_ofReal
  calc ∫⁻ x in J, xiLineMass σ x
      ≤ ∫⁻ x in J, ENNReal.ofReal (pieceWeight n) *
          (ENNReal.ofReal (windowLogConst * Real.log n) +
            ∑ q ∈ windowCopySet n, ENNReal.ofReal (1 / ‖(σ : ℂ) + x * I - (q.1 : ℂ)‖)) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal (pieceWeight n) * (ENNReal.ofReal (windowLogConst * Real.log n) * volume J +
          ∑ q ∈ windowCopySet n,
            ∫⁻ x in J, ENNReal.ofReal (1 / ‖(σ : ℂ) + x * I - (q.1 : ℂ)‖)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
          setLIntegral_const, lintegral_finsetSum _ hmeasq]
    _ ≤ _ := by
        have hJvol : volume J = 1 := by
          rw [hJ, Real.volume_Icc]; norm_num
        rw [hJvol, mul_one]
        gcongr with q hq
        exact lintegral_mono_set (hsub q hq)

/-- The majorant of the upper half-line integral. -/
def lineMajorant (σ : ℝ) : ENNReal :=
  ∑' n : ℕ, if 8 ≤ n then ENNReal.ofReal (pieceWeight n) *
    (ENNReal.ofReal (windowLogConst * Real.log n) + ∑ q ∈ windowCopySet n, windowBoxMass q σ) else 0

theorem measurable_lineMajorant : Measurable lineMajorant := by
  refine Measurable.tsum fun n => ?_
  split_ifs
  · exact measurable_const.mul (measurable_const.add
      (Finset.measurable_sum _ fun q _ => measurable_windowBoxMass q))
  · exact measurable_const

/-- **The upper half-line.** -/
theorem lintegral_xiLineMass_upper_le {σ : ℝ} (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) :
    ∫⁻ x in Ici (15 / 2 : ℝ), xiLineMass σ x ≤ lineMajorant σ := by
  set U : ℕ → Set ℝ := fun n => if 8 ≤ n then Icc ((n : ℝ) - 1 / 2) (n + 1 / 2) else ∅ with hU
  have hcover : Ici (15 / 2 : ℝ) ⊆ ⋃ n, U n := by
    intro x hx
    have hx' : (15 / 2 : ℝ) ≤ x := hx
    set n := ⌊x + 1 / 2⌋₊ with hn
    have h0 : 0 ≤ x + 1 / 2 := by linarith
    have hle : (n : ℝ) ≤ x + 1 / 2 := Nat.floor_le h0
    have hlt : x + 1 / 2 < n + 1 := Nat.lt_floor_add_one _
    have h8 : 8 ≤ n := by
      rw [hn]; apply Nat.le_floor; push_cast; linarith
    refine mem_iUnion.mpr ⟨n, ?_⟩
    simp only [hU, if_pos h8]
    exact ⟨by linarith, by linarith⟩
  calc ∫⁻ x in Ici (15 / 2 : ℝ), xiLineMass σ x ≤ ∫⁻ x in ⋃ n, U n, xiLineMass σ x :=
        lintegral_mono_set hcover
    _ ≤ ∑' n, ∫⁻ x in U n, xiLineMass σ x := lintegral_iUnion_le _ _
    _ ≤ lineMajorant σ := by
        unfold lineMajorant
        refine ENNReal.tsum_le_tsum fun n => ?_
        by_cases h8 : 8 ≤ n
        · simp only [hU, if_pos h8]
          exact lintegral_xiLineMass_piece_le h8 hσ
        · simp [hU, h8]

/-! ## Averaging over the abscissa -/

theorem log_le_two_mul_sqrt_of_pos_windowAverage {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h
  linarith

theorem pieceWeight_le (n : ℕ) : pieceWeight n ≤ 16 / ((n : ℝ) + 2) ^ 2 := by
  unfold pieceWeight
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ((n : ℝ) - 2 / 3)]

theorem summable_pieceWeight_mul_log {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Summable fun n : ℕ => pieceWeight n * (A * Real.log (180 * ((n : ℝ) + 2)) + B) := by
  have hbase : Summable fun n : ℕ => (((n : ℝ) + 2) ^ (3 / 2 : ℝ))⁻¹ := by
    have h := (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2))
    simpa using h
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (pieceWeight_nonneg n)
    (add_nonneg (mul_nonneg hA (Real.log_nonneg (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))) hB))
    (fun n => ?_) (hbase.mul_left (16 * (27 * A + B)))
  set m : ℝ := (n : ℝ) + 2 with hm
  have hm1 : 1 ≤ m := by rw [hm]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hsq : 1 ≤ Real.sqrt m := by rw [Real.one_le_sqrt]; exact hm1
  have hlog : Real.log (180 * m) ≤ 27 * Real.sqrt m := by
    have h := log_le_two_mul_sqrt_of_pos_windowAverage (show (0 : ℝ) < 180 * m by positivity)
    rw [Real.sqrt_mul (by norm_num)] at h
    have h180 : Real.sqrt 180 ≤ 27 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg m]
  have hrpow : (m ^ (3 / 2 : ℝ))⁻¹ = Real.sqrt m / m ^ 2 := by
    rw [show (3 / 2 : ℝ) = 2 - 1 / 2 by norm_num, Real.rpow_sub (by linarith), Real.rpow_two,
      ← Real.sqrt_eq_rpow, inv_div]
  rw [hrpow]
  calc pieceWeight n * (A * Real.log (180 * m) + B)
      ≤ 16 / m ^ 2 * (A * (27 * Real.sqrt m) + B * Real.sqrt m) := by
        have hl0 : 0 ≤ Real.log (180 * m) := Real.log_nonneg (by linarith)
        apply mul_le_mul (pieceWeight_le n) _ (add_nonneg (mul_nonneg hA hl0) hB) (by positivity)
        nlinarith
    _ = 16 * (27 * A + B) * (Real.sqrt m / m ^ 2) := by
        field_simp

/-- The real majorant of the averaged window sums. -/
def windowAverageBound (n : ℕ) : ℝ :=
  if 8 ≤ n then pieceWeight n * (windowLogConst * Real.log n +
    2 * (80 * Real.log (180 * ((n : ℝ) + 2)) + smallHeightCount) * (16 * Real.sqrt 3)) else 0

theorem summable_windowAverageBound : Summable windowAverageBound := by
  have hshc : 0 ≤ (smallHeightCount : ℝ) := Nat.cast_nonneg _
  have hA0 : 0 ≤ windowLogConst + 2 * 80 * (16 * Real.sqrt 3) :=
    add_nonneg windowLogConst_nonneg (by positivity)
  have hmaj := summable_pieceWeight_mul_log (A := windowLogConst + 2 * 80 * (16 * Real.sqrt 3))
    (B := 2 * smallHeightCount * (16 * Real.sqrt 3)) hA0 (by positivity)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · unfold windowAverageBound
    split_ifs with h8
    · have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      exact mul_nonneg (pieceWeight_nonneg n) (add_nonneg
        (mul_nonneg windowLogConst_nonneg (Real.log_nonneg hn))
        (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (by norm_num)
          (Real.log_nonneg (by nlinarith))) hshc)) (by positivity)))
    · exact le_rfl
  · unfold windowAverageBound
    split_ifs with h8
    · have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have hlogle : Real.log n ≤ Real.log (180 * ((n : ℝ) + 2)) :=
        Real.log_le_log (by linarith) (by nlinarith)
      have hl0 : 0 ≤ Real.log (180 * ((n : ℝ) + 2)) := Real.log_nonneg (by nlinarith)
      apply mul_le_mul_of_nonneg_left _ (pieceWeight_nonneg n)
      nlinarith [windowLogConst_nonneg, Real.sqrt_nonneg 3]
    · exact mul_nonneg (pieceWeight_nonneg n) (add_nonneg (mul_nonneg hA0
        (Real.log_nonneg (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))) (by positivity))

/-- **The averaged majorant is finite.** -/
theorem lintegral_lineMajorant_lt_top : ∫⁻ σ in Icc (1 / 2 : ℝ) 1, lineMajorant σ < ⊤ := by
  have hterm : ∀ n : ℕ, ∫⁻ σ in Icc (1 / 2 : ℝ) 1,
      (if 8 ≤ n then ENNReal.ofReal (pieceWeight n) *
        (ENNReal.ofReal (windowLogConst * Real.log n) +
          ∑ q ∈ windowCopySet n, windowBoxMass q σ) else 0) ≤
      ENNReal.ofReal (windowAverageBound n) := by
    intro n
    unfold windowAverageBound
    by_cases h8 : 8 ≤ n
    · simp only [if_pos h8]
      have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast (by omega : 4 ≤ n)
      have hcard := card_windowCopySet_le hn4
      have hlog0 : 0 ≤ windowLogConst * Real.log n :=
        mul_nonneg windowLogConst_nonneg (Real.log_nonneg (by linarith))
      have hbox : ∀ q ∈ windowCopySet n, ∫⁻ σ in Icc (1 / 2 : ℝ) 1, windowBoxMass q σ ≤
          ENNReal.ofReal (16 * Real.sqrt 3) := fun q _ =>
        GaloisForLFunctions.HTGeometry.lintegral_box_inv_norm_sub_le (q.1 : ℂ) (xiZeroCopy_re_pos q).le
          (xiZeroCopy_re_lt_one q).le (by norm_num)
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
        setLIntegral_const, lintegral_finsetSum _ fun q _ => measurable_windowBoxMass q,
        Real.volume_Icc]
      calc ENNReal.ofReal (pieceWeight n) * (ENNReal.ofReal (windowLogConst * Real.log n) *
            ENNReal.ofReal (1 - 1 / 2) +
            ∑ q ∈ windowCopySet n, ∫⁻ σ in Icc (1 / 2 : ℝ) 1, windowBoxMass q σ)
          ≤ ENNReal.ofReal (pieceWeight n) * (ENNReal.ofReal (windowLogConst * Real.log n) +
            ∑ q ∈ windowCopySet n, ENNReal.ofReal (16 * Real.sqrt 3)) := by
            gcongr with q hq
            · calc ENNReal.ofReal (windowLogConst * Real.log n) * ENNReal.ofReal (1 - 1 / 2)
                  ≤ ENNReal.ofReal (windowLogConst * Real.log n) * 1 := by
                    gcongr; exact ENNReal.ofReal_le_one.mpr (by norm_num)
                _ = _ := mul_one _
            · exact hbox q hq
        _ = ENNReal.ofReal (pieceWeight n * (windowLogConst * Real.log n +
              (windowCopySet n).card * (16 * Real.sqrt 3))) := by
            rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (pieceWeight_nonneg n),
              ENNReal.ofReal_add hlog0 (by positivity),
              ENNReal.ofReal_mul (Nat.cast_nonneg (windowCopySet n).card : (0 : ℝ) ≤ _),
              ENNReal.ofReal_natCast]
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            apply mul_le_mul_of_nonneg_left _ (pieceWeight_nonneg n)
            nlinarith [Real.sqrt_nonneg 3]
    · simp [h8]
  have hmeas : ∀ n : ℕ, AEMeasurable (fun σ => if 8 ≤ n then ENNReal.ofReal (pieceWeight n) *
      (ENNReal.ofReal (windowLogConst * Real.log n) +
        ∑ q ∈ windowCopySet n, windowBoxMass q σ) else 0) (volume.restrict (Icc (1 / 2 : ℝ) 1)) := by
    intro n
    split_ifs
    · exact (measurable_const.mul (measurable_const.add
        (Finset.measurable_sum _ fun q _ => measurable_windowBoxMass q))).aemeasurable
    · exact aemeasurable_const
  unfold lineMajorant
  rw [lintegral_tsum hmeas]
  calc _ ≤ ∑' n, ENNReal.ofReal (windowAverageBound n) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' n, windowAverageBound n) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun n => ?_) summable_windowAverageBound]
        unfold windowAverageBound
        split_ifs with h8
        · have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
          exact mul_nonneg (pieceWeight_nonneg n) (add_nonneg
            (mul_nonneg windowLogConst_nonneg (Real.log_nonneg hn))
            (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (by norm_num)
              (Real.log_nonneg (by nlinarith))) (Nat.cast_nonneg _))) (by positivity)))
        · exact le_rfl
    _ < ⊤ := ENNReal.ofReal_lt_top

/-! ## Assembly -/

theorem lintegral_xiLineMass_lower_eq (σ : ℝ) :
    ∫⁻ x in Iic (-(15 / 2) : ℝ), xiLineMass σ x = ∫⁻ x in Ici (15 / 2 : ℝ), xiLineMass σ x := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
    measurableEmbedding_neg (fun x => xiLineMass σ x) (Ici (15 / 2 : ℝ))
  have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ici (15 / 2) = Iic (-(15 / 2)) := by
    ext x; simp only [mem_preimage, mem_Ici, mem_Iic]; constructor <;> intro h <;> linarith
  rw [hpre] at h
  simpa only [xiLineMass_neg] using h

theorem measurable_norm_logDeriv_xi_line (σ : ℝ) :
    Measurable fun x : ℝ => ‖logDeriv xi ((σ : ℂ) + x * I)‖ / (1 + x ^ 2) := by
  have hl : Measurable (logDeriv xi) := by
    have h1 : Measurable (deriv xi) := xi_differentiable.deriv.continuous.measurable
    have h2 : Measurable xi := xi_differentiable.continuous.measurable
    simpa [logDeriv] using h1.div h2
  have hp : Measurable fun x : ℝ => (σ : ℂ) + x * I := by fun_prop
  exact (hl.comp hp).norm.div (by fun_prop)

/-- **Almost every vertical line.**  For almost every `σ ∈ (½, 1)`,
`∫_ℝ |ξ'/ξ(σ + ix)| / (1 + x²) dx < ∞`. -/
theorem ae_lintegral_xiLineMass_lt_top :
    ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (1 / 2 : ℝ) 1 → ∫⁻ x, xiLineMass σ x < ⊤ := by
  have hfin := ae_lt_top measurable_lineMajorant lintegral_lineMajorant_lt_top.ne
  rw [ae_restrict_iff' measurableSet_Icc] at hfin
  filter_upwards [hfin] with σ hσ hσIoo
  have hσIcc : σ ∈ Icc (1 / 2 : ℝ) 1 := Ioo_subset_Icc_self hσIoo
  have hup := (lintegral_xiLineMass_upper_le hσIcc).trans_lt (hσ hσIcc)
  have hmid := lintegral_xiLineMass_low_lt_top hσIoo.1
  set A : Set ℝ := Iic (-(15 / 2 : ℝ)) with hA
  set B : Set ℝ := Icc (-8 : ℝ) 8 with hB
  set C : Set ℝ := Ici (15 / 2 : ℝ) with hC
  have hlow : ∫⁻ x in A, xiLineMass σ x < ⊤ := by
    rw [hA, lintegral_xiLineMass_lower_eq]; exact hup
  have hcover : (univ : Set ℝ) ⊆ (A ∪ B) ∪ C := by
    intro x _
    by_cases h1 : x ≤ -(15 / 2)
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : 15 / 2 ≤ x
      · exact Or.inr h2
      · exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
  rw [← setLIntegral_univ]
  calc ∫⁻ x in univ, xiLineMass σ x ≤ ∫⁻ x in (A ∪ B) ∪ C, xiLineMass σ x :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ x in A ∪ B, xiLineMass σ x) + ∫⁻ x in C, xiLineMass σ x := lintegral_union_le _ _ _
    _ ≤ ((∫⁻ x in A, xiLineMass σ x) + ∫⁻ x in B, xiLineMass σ x) + ∫⁻ x in C, xiLineMass σ x :=
        add_le_add (lintegral_union_le _ _ _) le_rfl
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hlow, hmid⟩, hup⟩

/-- **Integrability form.** -/
theorem ae_integrable_norm_logDeriv_xi_line :
    ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (1 / 2 : ℝ) 1 →
      Integrable fun x : ℝ => ‖logDeriv xi ((σ : ℂ) + x * I)‖ / (1 + x ^ 2) := by
  filter_upwards [ae_lintegral_xiLineMass_lt_top] with σ hσ hσIoo
  refine ⟨(measurable_norm_logDeriv_xi_line σ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => by positivity)]
  exact hσ hσIoo

end

end RHTower
