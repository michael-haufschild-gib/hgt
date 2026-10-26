import GaloisForLFunctions.TransHorizonIncidenceMechanics.APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic

/-!
# Mellin residues pin power-like solutions to the translated zeros

Let `0 < ε < 1/2`, `α = 1 − ε`, and `S_ε v(n) = Σ_{j≤n} j^{-ε} v(⌊n/j⌋)`. Suppose a complex row is a finite
power sum plus a row of bounded pronic energy, `v = Σ_{s∈F} c_s n^s + r`, with `1/2 < Re s ≤ 1`,
`s ≠ α`, and satisfies the renormalized inversion law `S_ε v = c' n^α + r'` with `r'` of bounded
energy. Then `ζ(s + ε) = 0` for every `s` with `c_s ≠ 0`
(`riemannZeta_add_eq_zero_of_powerLike_solution`).

The finite-horizon symbol calculus cannot see this: `S_ε` is unbounded on rows of bounded energy,
and nothing excludes `S_ε r` cancelling the power terms at every horizon. The Mellin transform does.
With `𝓜v(w) = Σ v(n)(n^{-w} − (n+1)^{-w})`:

* `𝓜(S_ε v)(w) = ζ(w + ε) 𝓜v(w)` for `Re w > 2` (`rowMellin_cTotalCofactorSum`);
* `𝓜(n^s)(w) = s ζ(w − s + 1) + E_s(w)` with `E_s` holomorphic on `Re w > Re s − 1`
  (`rowMellin_cpow_eq`, `differentiableOn_powerCorrection`);
* `𝓜r` is holomorphic on `Re w > 1/2` for `r` of bounded energy (`differentiableOn_rowMellin`).

So `ζ(w+ε)(Σ c_s(sζ(w−s+1) + E_s) + 𝓜r) − c'(αζ(w−α+1) + E_α) − 𝓜r'` is meromorphic on
`Re w > 1/2` and vanishes on `Re w > 2`, hence near every point; its residue at `s` is
`c_s s ζ(s + ε)`.
-/

open Finset Filter Topology Complex
open GaloisForLFunctions.TransHorizonIncidenceMechanics (complexMellinCell complexMellinPairing
  norm_complexMellinCell_le summable_abs_mul_rpow_of_energy differentiableOn_complexMellinPairing)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The complex Mellin transform of a complex row. -/
def rowMellin (v : ℕ → ℂ) (w : ℂ) : ℂ := ∑' n : ℕ, v n * complexMellinCell w n

/-- Bounded pronic energy of a complex row. -/
def EnergyBounded (v : ℕ → ℂ) : Prop :=
  ∃ E : ℝ, ∀ T : ℕ, ∑ n ∈ Icc 1 T, ‖v n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E

/-! ### Rows of bounded energy -/

/-- A row of bounded energy grows at most linearly: `‖r(n)‖ ≤ √E (n + 1)`. -/
theorem norm_le_of_energyBounded {r : ℕ → ℂ} {E : ℝ}
    (hE : ∀ T : ℕ, ∑ n ∈ Icc 1 T, ‖r n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E) {n : ℕ} (hn : 1 ≤ n) :
    ‖r n‖ ≤ Real.sqrt E * ((n : ℝ) + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ‖r n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E := by
    refine le_trans ?_ (hE n)
    exact single_le_sum (f := fun k => ‖r k‖ ^ 2 / ((k : ℝ) * ((k : ℝ) + 1)))
      (fun k _ => by positivity) (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
  have hsq : ‖r n‖ ^ 2 ≤ E * ((n : ℝ) + 1) ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hterm
    nlinarith [sq_nonneg ‖r n‖]
  have hE0 : 0 ≤ E := le_trans (by positivity) hterm
  calc ‖r n‖ = Real.sqrt (‖r n‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (E * ((n : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt E * ((n : ℝ) + 1) := by
        rw [Real.sqrt_mul hE0, Real.sqrt_sq (by positivity)]

/-- **The Mellin transform of a row of bounded energy is holomorphic on `Re w > 1/2`.** -/
theorem differentiableOn_rowMellin {r : ℕ → ℂ} (hr0 : r 0 = 0) {E : ℝ}
    (hE : ∀ T : ℕ, ∑ n ∈ Icc 1 T, ‖r n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E) :
    DifferentiableOn ℂ (rowMellin r) {w : ℂ | 1 / 2 < w.re} := by
  have hEre : ∀ T : ℕ, ∑ n ∈ Icc 1 T, (r n).re ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E := fun T =>
    le_trans (sum_le_sum fun n _ => div_le_div_of_nonneg_right
      (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2)
      (by positivity)) (hE T)
  have hEim : ∀ T : ℕ, ∑ n ∈ Icc 1 T, (r n).im ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E := fun T =>
    le_trans (sum_le_sum fun n _ => div_le_div_of_nonneg_right
      (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2)
      (by positivity)) (hE T)
  have hre0 : (fun n => (r n).re) 0 = 0 := by simp [hr0]
  have him0 : (fun n => (r n).im) 0 = 0 := by simp [hr0]
  have hD := (differentiableOn_complexMellinPairing hre0 hEre).add
    ((differentiableOn_complexMellinPairing him0 hEim).const_mul I)
  refine hD.congr fun w hw => ?_
  have hw' : (1 : ℝ) / 2 < w.re := hw
  -- summability of the real and imaginary parts
  have hsumm : ∀ f : ℕ → ℝ, f 0 = 0 →
      (∀ T : ℕ, ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E) →
      Summable fun n => (f n : ℂ) * complexMellinCell w n := by
    intro f hf0 hfE
    refine Summable.of_norm_bounded ((summable_abs_mul_rpow_of_energy hw' hf0 hfE).mul_left ‖w‖)
      fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf0]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |f n| * ‖complexMellinCell w n‖ ≤ |f n| * (‖w‖ * (n : ℝ) ^ (-w.re - 1)) :=
          mul_le_mul_of_nonneg_left (norm_complexMellinCell_le (by linarith) hn) (abs_nonneg _)
      _ = ‖w‖ * (|f n| * (n : ℝ) ^ (-w.re - 1)) := by ring
  have h1 := hsumm _ hre0 hEre
  have h2 := hsumm _ him0 hEim
  simp only [Pi.add_apply, rowMellin, complexMellinPairing]
  rw [← tsum_mul_left, ← h1.tsum_add (h2.mul_left I)]
  refine tsum_congr fun n => ?_
  conv_lhs => rw [← Complex.re_add_im (r n)]
  ring

/-! ### The Mellin transform of a power row -/

theorem hasDerivAt_ofReal_cpow_const (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ s) (s * ((x : ℝ) : ℂ) ^ (s - 1)) x := by
  have h := (hasDerivAt_id' (x := (x : ℂ))).cpow_const (c := s)
    (Complex.ofReal_mem_slitPlane.mpr hx)
  simpa using h.comp_ofReal

/-- Mean value bound `‖b^z − u^z‖ ≤ ‖z‖ a^{Re z − 1} (b − u)` for `0 < a ≤ u ≤ b`, `Re z ≤ 1`. -/
theorem norm_ofReal_cpow_sub_le' {z : ℂ} (hz : z.re ≤ 1) {a u b : ℝ} (ha : 0 < a) (hau : a ≤ u)
    (hub : u ≤ b) :
    ‖((b : ℝ) : ℂ) ^ z - ((u : ℝ) : ℂ) ^ z‖ ≤ ‖z‖ * a ^ (z.re - 1) * (b - u) := by
  have hu0 : 0 < u := lt_of_lt_of_le ha hau
  refine norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun y : ℝ => ((y : ℝ) : ℂ) ^ z) (f' := fun y => z * ((y : ℝ) : ℂ) ^ (z - 1))
    (fun y hy => (hasDerivAt_ofReal_cpow_const z (lt_of_lt_of_le hu0 hy.1)).hasDerivWithinAt)
    (fun y hy => ?_) b ⟨hub, le_rfl⟩
  have hy0 : 0 < y := lt_of_lt_of_le hu0 hy.1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hre : (z - 1).re = z.re - 1 := by simp
  rw [hre]
  exact Real.rpow_le_rpow_of_nonpos ha (hau.trans hy.1) (by linarith)

/-- The second-order defect `e_s(k) = (k+1)^s − k^s − s (k+1)^{s−1}`. -/
def powerDefect (s : ℂ) (k : ℕ) : ℂ :=
  (((k : ℝ) + 1 : ℝ) : ℂ) ^ s - ((k : ℝ) : ℂ) ^ s - s * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1)

/-- `‖e_s(k)‖ ≤ ‖s‖ ‖s − 1‖ k^{Re s − 2}` for `k ≥ 1` and `Re s ≤ 2`. -/
theorem norm_powerDefect_le {s : ℂ} (hs : s.re ≤ 2) {k : ℕ} (hk : 1 ≤ k) :
    ‖powerDefect s k‖ ≤ ‖s‖ * ‖s - 1‖ * (k : ℝ) ^ (s.re - 2) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set g : ℝ → ℂ := fun x => ((x : ℝ) : ℂ) ^ s - s * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) * (x : ℂ)
    with hg
  have hderiv : ∀ x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1), HasDerivWithinAt g
      (s * ((x : ℝ) : ℂ) ^ (s - 1) - s * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1))
        (Set.Icc (k : ℝ) ((k : ℝ) + 1)) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hk0 hx.1
    have h1 := hasDerivAt_ofReal_cpow_const s hx0
    have h2 : HasDerivAt (fun y : ℝ => s * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) * (y : ℂ))
        (s * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) * 1) x :=
      (Complex.ofRealCLM.hasDerivAt.const_mul _)
    have h3 := (h1.sub h2).hasDerivWithinAt (s := Set.Icc (k : ℝ) ((k : ℝ) + 1))
    rw [mul_one] at h3
    exact h3
  have hbound : ∀ x ∈ Set.Ico (k : ℝ) ((k : ℝ) + 1),
      ‖s * ((x : ℝ) : ℂ) ^ (s - 1) - s * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1)‖ ≤
        ‖s‖ * ‖s - 1‖ * (k : ℝ) ^ (s.re - 2) := by
    intro x hx
    have hmv := norm_ofReal_cpow_sub_le' (z := s - 1) (by simp; linarith) hk0 hx.1 hx.2.le
    rw [← mul_sub, norm_mul, norm_sub_rev, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hre : (s - 1).re - 1 = s.re - 2 := by simp; ring
    rw [hre] at hmv
    calc _ ≤ ‖s - 1‖ * (k : ℝ) ^ (s.re - 2) * ((k : ℝ) + 1 - x) := hmv
      _ ≤ ‖s - 1‖ * (k : ℝ) ^ (s.re - 2) * 1 := by
          refine mul_le_mul_of_nonneg_left (by linarith [hx.1]) (by positivity)
      _ = _ := mul_one _
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound ((k : ℝ) + 1)
    ⟨by linarith, le_rfl⟩
  rw [show (k : ℝ) + 1 - k = 1 by ring, mul_one] at h
  have hid : g ((k : ℝ) + 1) - g k = powerDefect s k := by
    simp only [hg, powerDefect]
    push_cast
    ring
  rw [← hid]
  exact h

/-- A uniform form: `‖e_s(k)‖ ≤ (4‖s‖‖s − 1‖ + ‖s − 1‖)(k + 1)^{Re s − 2}` for `0 ≤ Re s ≤ 2`. -/
theorem norm_powerDefect_le_uniform {s : ℂ} (hs0 : 0 ≤ s.re) (hs : s.re ≤ 2) (k : ℕ) :
    ‖powerDefect s k‖ ≤ (4 * ‖s‖ * ‖s - 1‖ + ‖s - 1‖) * ((k : ℝ) + 1) ^ (s.re - 2) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : ‖powerDefect s 0‖ ≤ ‖s - 1‖ := by
      by_cases hs' : s = 0
      · subst hs'; simp [powerDefect]
      · simp only [powerDefect, Nat.cast_zero, zero_add, Complex.ofReal_one, Complex.one_cpow,
          Complex.ofReal_zero, Complex.zero_cpow hs', sub_zero, mul_one]
        rw [norm_sub_rev]
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one]
    nlinarith [norm_nonneg s, norm_nonneg (s - 1)]
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    have hpow : (k : ℝ) ^ (s.re - 2) ≤ 4 * ((k : ℝ) + 1) ^ (s.re - 2) := by
      have h2k : (k : ℝ) + 1 ≤ 2 * k := by linarith
      have h1 : (2 * (k : ℝ)) ^ (s.re - 2) ≤ ((k : ℝ) + 1) ^ (s.re - 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h2k (by linarith)
      rw [Real.mul_rpow (by norm_num) hk0.le] at h1
      have h22 : (2 : ℝ) ^ (s.re - 2) * 4 ≥ 1 := by
        have : (2 : ℝ) ^ (s.re - 2) ≥ (2 : ℝ) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        have h4 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
          rw [Real.rpow_neg (by norm_num)]; norm_num
        rw [h4] at this; linarith
      have hkpos : 0 < (k : ℝ) ^ (s.re - 2) := Real.rpow_pos_of_pos hk0 _
      nlinarith
    calc ‖powerDefect s k‖ ≤ ‖s‖ * ‖s - 1‖ * (k : ℝ) ^ (s.re - 2) := norm_powerDefect_le hs hk
      _ ≤ ‖s‖ * ‖s - 1‖ * (4 * ((k : ℝ) + 1) ^ (s.re - 2)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (4 * ‖s‖ * ‖s - 1‖ + ‖s - 1‖) * ((k : ℝ) + 1) ^ (s.re - 2) := by
          have : 0 ≤ ‖s - 1‖ * ((k : ℝ) + 1) ^ (s.re - 2) := by positivity
          nlinarith

/-- The holomorphic correction `E_s(w) = Σ_k e_s(k) (k+1)^{-w}`. -/
def powerCorrection (s w : ℂ) : ℂ :=
  ∑' k : ℕ, powerDefect s k * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-w)

theorem norm_powerDefect_mul_le {s w : ℂ} (hs0 : 0 ≤ s.re) (hs : s.re ≤ 2) {b : ℝ}
    (hb : b ≤ w.re) (k : ℕ) :
    ‖powerDefect s k * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-w)‖ ≤
      (4 * ‖s‖ * ‖s - 1‖ + ‖s - 1‖) * ((k : ℝ) + 1) ^ (s.re - 2 - b) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hk, Complex.neg_re]
  calc ‖powerDefect s k‖ * ((k : ℝ) + 1) ^ (-w.re)
      ≤ (4 * ‖s‖ * ‖s - 1‖ + ‖s - 1‖) * ((k : ℝ) + 1) ^ (s.re - 2) * ((k : ℝ) + 1) ^ (-b) := by
        refine mul_le_mul (norm_powerDefect_le_uniform hs0 hs k)
          (Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by linarith))
          (by positivity) (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hk]; ring_nf

/-- **The correction is holomorphic on `Re w > Re s − 1`.** -/
theorem differentiableOn_powerCorrection {s : ℂ} (hs0 : 0 ≤ s.re) (hs : s.re ≤ 2) :
    DifferentiableOn ℂ (powerCorrection s) {w : ℂ | s.re - 1 < w.re} := by
  intro w₀ hw₀
  have hw₀' : s.re - 1 < w₀.re := hw₀
  obtain ⟨b, hb, hbw⟩ : ∃ b : ℝ, s.re - 1 < b ∧ b < w₀.re :=
    ⟨(s.re - 1 + w₀.re) / 2, by linarith, by linarith⟩
  set U : Set ℂ := {w | b < w.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsum : Summable fun k : ℕ =>
      (4 * ‖s‖ * ‖s - 1‖ + ‖s - 1‖) * ((k : ℝ) + 1) ^ (s.re - 2 - b) := by
    refine Summable.mul_left _ ?_
    have := (Real.summable_nat_rpow.mpr (by linarith : s.re - 2 - b < -1))
    exact_mod_cast (summable_nat_add_iff 1).mpr this
  have hdiff : DifferentiableOn ℂ (fun w => ∑' k : ℕ, powerDefect s k *
      (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-w)) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm hsum (fun k w _ => ?_) hU
      (fun k w hw => norm_powerDefect_mul_le hs0 hs (le_of_lt hw) k)
    have hbase : (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show ((k : ℝ) + 1) ≠ 0 by positivity)
    exact ((differentiableAt_const _).mul
      (differentiableAt_id.neg.const_cpow (Or.inl hbase))).differentiableWithinAt
  exact (hdiff.differentiableAt (hU.mem_nhds hbw)).differentiableWithinAt

/-- **The Mellin transform of `n^s`.** For `Re w > Re s + 1`:
`𝓜(n^s)(w) = s ζ(w − s + 1) + E_s(w)`. -/
theorem rowMellin_cpow_eq {s w : ℂ} (hs : s ≠ 0) (hs0 : 0 ≤ s.re) (hs2 : s.re ≤ 2)
    (hsw : s.re + 1 < w.re) :
    rowMellin (fun n => ((n : ℝ) : ℂ) ^ s) w = s * riemannZeta (w - s + 1) + powerCorrection s w := by
  have hw0 : 0 < w.re := by linarith
  set a : ℕ → ℂ := fun n => ((n : ℝ) : ℂ) ^ s * ((n : ℝ) : ℂ) ^ (-w) with ha
  set b : ℕ → ℂ := fun n => ((n : ℝ) : ℂ) ^ s * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-w) with hb
  have ha0 : a 0 = 0 := by simp [ha, Complex.zero_cpow hs]
  have hsa : Summable fun k : ℕ => a (k + 1) := by
    refine Summable.of_norm_bounded (g := fun k : ℕ => ((k : ℝ) + 1) ^ (s.re - w.re)) ?_
      fun k => ?_
    · have := Real.summable_nat_rpow.mpr (by linarith : s.re - w.re < -1)
      exact_mod_cast (summable_nat_add_iff 1).mpr this
    · have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      simp only [ha, Nat.cast_add, Nat.cast_one]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hk,
        Complex.norm_cpow_eq_rpow_re_of_pos hk, Complex.neg_re, ← Real.rpow_add hk]
      exact le_of_eq (by ring_nf)
  have hsa' : Summable a := (summable_nat_add_iff 1).mp hsa
  have hsb : Summable b := by
    refine Summable.of_norm_bounded (g := fun k : ℕ => ((k : ℝ) + 1) ^ (s.re - w.re)) ?_
      fun k => ?_
    · have := Real.summable_nat_rpow.mpr (by linarith : s.re - w.re < -1)
      exact_mod_cast (summable_nat_add_iff 1).mpr this
    · have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      simp only [hb]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hk, Complex.neg_re]
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simp [Complex.zero_cpow hs]
      · have hk0 : (0 : ℝ) < k := by exact_mod_cast hkpos
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hk0]
        calc (k : ℝ) ^ s.re * ((k : ℝ) + 1) ^ (-w.re)
            ≤ ((k : ℝ) + 1) ^ s.re * ((k : ℝ) + 1) ^ (-w.re) :=
              mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hk0.le (by linarith) hs0)
                (by positivity)
          _ = ((k : ℝ) + 1) ^ (s.re - w.re) := by rw [← Real.rpow_add hk]; ring_nf
  set x : ℕ → ℂ := fun k => s * (1 / ((k : ℂ) + 1) ^ (w - s + 1)) with hx
  set y : ℕ → ℂ := fun k => powerDefect s k * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-w) with hy
  have hzeta : riemannZeta (w - s + 1) = ∑' k : ℕ, 1 / ((k : ℂ) + 1) ^ (w - s + 1) :=
    zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; linarith)
  have hsx : Summable x := by
    refine Summable.mul_left _ ?_
    have h1 : Summable fun n : ℕ => 1 / (n : ℂ) ^ (w - s + 1) :=
      Complex.summable_one_div_nat_cpow.mpr (by simp; linarith)
    have h2 := (summable_nat_add_iff 1).mpr h1
    refine h2.congr fun k => ?_
    push_cast
    rfl
  have hsy : Summable y := by
    have hg : Summable fun k : ℕ =>
        (4 * ‖s‖ * ‖s - 1‖ + ‖s - 1‖) * ((k : ℝ) + 1) ^ (s.re - 2 - w.re) := by
      refine Summable.mul_left _ ?_
      have := Real.summable_nat_rpow.mpr (by linarith : s.re - 2 - w.re < -1)
      exact_mod_cast (summable_nat_add_iff 1).mpr this
    exact Summable.of_norm_bounded hg fun k => norm_powerDefect_mul_le hs0 hs2 le_rfl k
  have hstep : ∀ k : ℕ, a (k + 1) - b k = x k + y k := by
    intro k
    have hk : (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show ((k : ℝ) + 1) ≠ 0 by positivity)
    have hpow : (((k : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-w) =
        1 / ((k : ℂ) + 1) ^ (w - s + 1) := by
      rw [← Complex.cpow_add _ _ hk, one_div, ← Complex.cpow_neg]
      push_cast; ring_nf
    simp only [ha, hb, hx, hy, powerDefect]
    push_cast
    rw [← hpow]
    push_cast
    ring
  have hmain : rowMellin (fun n => ((n : ℝ) : ℂ) ^ s) w = ∑' n, (a n - b n) := by
    refine tsum_congr fun n => ?_
    simp only [ha, hb, complexMellinCell]
    ring
  rw [hmain, hsa'.tsum_sub hsb, hsa'.tsum_eq_zero_add, ha0, zero_add, ← hsa.tsum_sub hsb]
  rw [tsum_congr hstep, hsx.tsum_add hsy, hzeta, ← tsum_mul_left]
  rfl

/-! ### The cofactor sum is multiplication by `ζ(w + ε)` -/

/-- The complex total cofactor sum `S_ε v(n) = Σ_{j≤n} j^{-ε} v(⌊n/j⌋)`. -/
def cTotalCofactorSum (ε : ℝ) (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Icc 1 n, (((j : ℝ) ^ (-ε) : ℝ) : ℂ) * v (n / j)

/-- Rows of at most linear growth. -/
def LinearGrowth (v : ℕ → ℂ) : Prop := ∃ C : ℝ, ∀ n : ℕ, ‖v n‖ ≤ C * ((n : ℝ) + 1)

theorem norm_mul_cell_le {v : ℕ → ℂ} (hv0 : v 0 = 0) {C : ℝ} (hC : ∀ n : ℕ, ‖v n‖ ≤ C * ((n : ℝ) + 1))
    {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    ‖v n * complexMellinCell w n‖ ≤ 2 * C * ‖w‖ * (n : ℝ) ^ (-w.re) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hv0, Real.zero_rpow (by linarith : -w.re ≠ 0)]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0); simp at this; linarith
  rw [norm_mul]
  calc ‖v n‖ * ‖complexMellinCell w n‖ ≤ (C * ((n : ℝ) + 1)) * (‖w‖ * (n : ℝ) ^ (-w.re - 1)) :=
        mul_le_mul (hC n) (norm_complexMellinCell_le hw hn) (norm_nonneg _) (by positivity)
    _ ≤ (C * (2 * n)) * (‖w‖ * (n : ℝ) ^ (-w.re - 1)) := by
        gcongr; linarith
    _ = 2 * C * ‖w‖ * ((n : ℝ) * (n : ℝ) ^ (-w.re - 1)) := by ring
    _ = 2 * C * ‖w‖ * (n : ℝ) ^ (-w.re) := by
        have h := Real.rpow_add hn0 1 (-w.re - 1)
        rw [Real.rpow_one, show (1 : ℝ) + (-w.re - 1) = -w.re by ring] at h
        rw [h]

theorem summable_rowMellin {v : ℕ → ℂ} (hv0 : v 0 = 0) {C : ℝ}
    (hC : ∀ n : ℕ, ‖v n‖ ≤ C * ((n : ℝ) + 1)) {w : ℂ} (hw : 1 < w.re) :
    Summable fun n => v n * complexMellinCell w n :=
  Summable.of_norm_bounded ((Real.summable_nat_rpow.mpr (by linarith : -w.re < -1)).mul_left
    (2 * C * ‖w‖)) fun n => norm_mul_cell_le hv0 hC (by linarith) n

/-- Block telescoping: `Σ_{t<d} Δ_{md+t}(w) = d^{-w} Δ_m(w)`. -/
theorem sum_range_complexMellinCell_block (w : ℂ) (d m : ℕ) :
    ∑ t ∈ range d, complexMellinCell w (m * d + t) =
      ((d : ℝ) : ℂ) ^ (-w) * complexMellinCell w m := by
  have htel : ∀ k, ∑ t ∈ range k, complexMellinCell w (m * d + t) =
      (((m * d : ℕ) : ℝ) : ℂ) ^ (-w) - (((m * d + k : ℕ) : ℝ) : ℂ) ^ (-w) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, complexMellinCell]
      push_cast; ring_nf
  rw [htel d, complexMellinCell]
  have h1 : (((m * d : ℕ) : ℝ) : ℂ) ^ (-w) = ((m : ℝ) : ℂ) ^ (-w) * ((d : ℝ) : ℂ) ^ (-w) := by
    push_cast
    exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg d) (-w)
  have h2 : (((m * d + d : ℕ) : ℝ) : ℂ) ^ (-w) =
      (((m : ℝ) + 1 : ℝ) : ℂ) ^ (-w) * ((d : ℝ) : ℂ) ^ (-w) := by
    rw [show ((m * d + d : ℕ) : ℝ) = ((m : ℝ) + 1) * (d : ℝ) by push_cast; ring, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (by positivity) (Nat.cast_nonneg d) (-w)
  rw [h1, h2]
  ring

/-- **Mellin intertwining of floor dilations.** -/
theorem hasSum_dil_mul_complexMellinCell {v : ℕ → ℂ} (hv0 : v 0 = 0) {C : ℝ}
    (hC : ∀ n : ℕ, ‖v n‖ ≤ C * ((n : ℝ) + 1)) {w : ℂ} (hw : 1 < w.re) {d : ℕ} (hd : 1 ≤ d) :
    HasSum (fun n => v (n / d) * complexMellinCell w n) (((d : ℝ) : ℂ) ^ (-w) * rowMellin v w) := by
  have hCd : ∀ n : ℕ, ‖v (n / d)‖ ≤ C * ((n : ℝ) + 1) := by
    intro n
    have hC0 : 0 ≤ C := by
      have := (norm_nonneg _).trans (hC 0); simp at this; linarith
    refine (hC (n / d)).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    have : ((n / d : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n d
    linarith
  have hsumm := summable_rowMellin (v := fun n => v (n / d)) (by simp [hv0]) hCd hw
  have hpart : ∀ N : ℕ, ∑ n ∈ range (N * d), v (n / d) * complexMellinCell w n =
      ((d : ℝ) : ℂ) ^ (-w) * ∑ m ∈ range N, v m * complexMellinCell w m := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show (N + 1) * d = N * d + d by ring, Finset.sum_range_add, ih, Finset.sum_range_succ,
        mul_add]
      congr 1
      have hdiv : ∀ t ∈ range d, (N * d + t) / d = N := fun t ht => by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (mem_range.mp ht),
          zero_add]
      rw [sum_congr rfl fun t ht => by rw [hdiv t ht], ← mul_sum,
        sum_range_complexMellinCell_block]
      ring
  have hmul : Tendsto (fun N : ℕ => N * d) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => ha.trans (Nat.le_mul_of_pos_right a hd)⟩
  have hlim1 := hsumm.hasSum.tendsto_sum_nat.comp hmul
  have hlim2 : Tendsto (fun N => ∑ n ∈ range (N * d), v (n / d) * complexMellinCell w n) atTop
      (𝓝 (((d : ℝ) : ℂ) ^ (-w) * rowMellin v w)) := by
    simp_rw [hpart]
    exact (summable_rowMellin hv0 hC hw).hasSum.tendsto_sum_nat.const_mul _
  rw [← tendsto_nhds_unique hlim1 hlim2]
  exact hsumm.hasSum

/-- **`𝓜(S_ε v)(w) = ζ(w + ε) 𝓜v(w)` for `Re w > 2`.** -/
theorem hasSum_cTotalCofactorSum_mul_cell {ε : ℝ} (hε : 0 < ε) {v : ℕ → ℂ} (hv0 : v 0 = 0) {C : ℝ}
    (hC : ∀ n : ℕ, ‖v n‖ ≤ C * ((n : ℝ) + 1)) {w : ℂ} (hw : 2 < w.re) :
    HasSum (fun n => cTotalCofactorSum ε v n * complexMellinCell w n)
      (riemannZeta (w + ε) * rowMellin v w) := by
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0); simp at this; linarith
  set F : ℕ → ℕ → ℂ := fun j n => (((j : ℝ) ^ (-ε) : ℝ) : ℂ) * v (n / j) * complexMellinCell w n
    with hF
  have hvanish : ∀ n j, j ∉ Icc 1 n → F j n = 0 := by
    intro n j hj
    simp only [Finset.mem_Icc, not_and_or, not_le] at hj
    rcases hj with hj | hj
    · have : j = 0 := by omega
      subst this; simp [hF, Real.zero_rpow (by linarith : -ε ≠ 0)]
    · simp [hF, Nat.div_eq_of_lt hj, hv0]
  -- absolute summability on pairs
  have hbound : ∀ j n, ‖F j n‖ ≤ (2 * C * ‖w‖) * ((j : ℝ) ^ (-1 - ε) * (n : ℝ) ^ (-w.re)) := by
    intro j n
    by_cases hjn : j ∈ Icc 1 n
    · obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.mp hjn
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hj1 hjn)
      have hn1 : 1 ≤ n := le_trans hj1 hjn
      have hvj : ‖v (n / j)‖ ≤ C * (2 * n / j) := by
        refine (hC _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
        have h1 : ((n / j : ℕ) : ℝ) ≤ n / j := Nat.cast_div_le
        have h2 : (1 : ℝ) ≤ n / j := by rw [le_div_iff₀ hj0, one_mul]; exact_mod_cast hjn
        have h3 : (n : ℝ) / j + n / j = 2 * n / j := by ring
        linarith
      rw [hF, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hj0 _)]
      calc (j : ℝ) ^ (-ε) * ‖v (n / j)‖ * ‖complexMellinCell w n‖
          ≤ (j : ℝ) ^ (-ε) * (C * (2 * n / j)) * (‖w‖ * (n : ℝ) ^ (-w.re - 1)) := by
            gcongr
            · exact norm_complexMellinCell_le (by linarith) hn1
        _ = (2 * C * ‖w‖) * (((j : ℝ) ^ (-ε) / j) * ((n : ℝ) * (n : ℝ) ^ (-w.re - 1))) := by
            ring
        _ = _ := by
            congr 2
            · rw [show (-1 - ε) = -ε + -1 by ring, Real.rpow_add hj0, Real.rpow_neg_one, div_eq_mul_inv]
            · have h := Real.rpow_add hn0 1 (-w.re - 1)
              rw [Real.rpow_one, show (1 : ℝ) + (-w.re - 1) = -w.re by ring] at h
              rw [h]
    · rw [hvanish n j hjn, norm_zero]
      positivity
  have hsj : Summable fun j : ℕ => (j : ℝ) ^ (-1 - ε) := Real.summable_nat_rpow.mpr (by linarith)
  have hsn : Summable fun n : ℕ => (n : ℝ) ^ (-w.re) := Real.summable_nat_rpow.mpr (by linarith)
  have hprod : Summable fun x : ℕ × ℕ =>
      (2 * C * ‖w‖) * ((x.1 : ℝ) ^ (-1 - ε) * (x.2 : ℝ) ^ (-w.re)) :=
    (hsj.mul_of_nonneg hsn (fun j => by positivity) (fun n => by positivity)).mul_left _
  have hS : Summable (Function.uncurry F) := hprod.of_norm_bounded fun x => hbound x.1 x.2
  -- column sums: dilated Mellin transforms
  set col : ℕ → ℂ := fun j =>
    (((j : ℝ) ^ (-ε) : ℝ) : ℂ) * (((j : ℝ) : ℂ) ^ (-w) * rowMellin v w) with hcoldef
  have hcol : ∀ j, HasSum (fun n => F j n) (col j) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have h0 : ((((0 : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) = 0 := by
        simp [Real.zero_rpow (by linarith : -ε ≠ 0)]
      simp only [hF, hcoldef, h0, zero_mul]
      exact hasSum_zero
    · have h := (hasSum_dil_mul_complexMellinCell hv0 hC (by linarith : 1 < w.re) hj).mul_left
        ((((j : ℝ) ^ (-ε) : ℝ) : ℂ))
      simp only [hF, hcoldef, mul_assoc]
      exact h
  -- row sums: the cofactor sum
  have hrow : ∀ n, HasSum (fun j => F j n) (cTotalCofactorSum ε v n * complexMellinCell w n) := by
    intro n
    rw [cTotalCofactorSum, sum_mul]
    exact hasSum_sum_of_ne_finset_zero fun j hj => hvanish n j hj
  have h1 := hS.hasSum.prod_fiberwise hcol
  have hS' : HasSum (Function.uncurry F ∘ Equiv.prodComm ℕ ℕ) (∑' x, Function.uncurry F x) :=
    (Equiv.hasSum_iff (Equiv.prodComm ℕ ℕ)).mpr hS.hasSum
  have h2 := hS'.prod_fiberwise fun n => hrow n
  have hval : ∑' j, col j = riemannZeta (w + ε) * rowMellin v w := by
    have hz : riemannZeta (w + ε) = ∑' j : ℕ, 1 / (j : ℂ) ^ (w + ε) :=
      zeta_eq_tsum_one_div_nat_cpow (by simp; linarith)
    rw [hz, ← tsum_mul_right]
    refine tsum_congr fun j => ?_
    simp only [hcoldef]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hwe : w + (ε : ℂ) ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      simp [Real.zero_rpow (by linarith : -ε ≠ 0), Complex.zero_cpow hwe]
    · have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
      have hjne : ((j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hj0.ne'
      rw [Complex.ofReal_cpow hj0.le, ← mul_assoc, ← Complex.cpow_add _ _ hjne, one_div,
        ← Complex.cpow_neg, Complex.ofReal_natCast]
      congr 2
      push_cast; ring
  rw [← hval, h1.tsum_eq]
  exact h2

/-! ### Residues -/

theorem isConnected_halfPlane (x : ℝ) : IsConnected {s : ℂ | x < s.re} :=
  ⟨⟨((x + 1 : ℝ) : ℂ), by simp⟩,
    (convex_halfSpace_gt ⟨fun _ _ => rfl, fun _ _ => by simp⟩ x).isPreconnected⟩

theorem meromorphicAt_riemannZeta_comp {g : ℂ → ℂ} {u : ℂ} (hg : AnalyticAt ℂ g u) :
    MeromorphicAt (fun z => riemannZeta (g z)) u :=
  (HTGeometry.meromorphicOn_riemannZeta (g u) (Set.mem_univ _)).comp_analyticAt hg

theorem continuousAt_riemannZeta_comp {g : ℂ → ℂ} {u : ℂ} (hg : ContinuousAt g u)
    (h1 : g u ≠ 1) : ContinuousAt (fun z => riemannZeta (g z)) u :=
  (differentiableAt_riemannZeta h1).continuousAt.comp hg

/-- `(w − s₀) ζ(w − s₀ + 1) → 1` as `w → s₀`. -/
theorem tendsto_sub_mul_riemannZeta_shift (s₀ : ℂ) :
    Tendsto (fun w => (w - s₀) * riemannZeta (w - s₀ + 1)) (𝓝[≠] s₀) (𝓝 1) := by
  have hmap : Tendsto (fun w : ℂ => w - s₀ + 1) (𝓝[≠] s₀) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun w : ℂ => w - s₀ + 1) (𝓝 s₀) (𝓝 (s₀ - s₀ + 1)) :=
        ((continuous_id.sub continuous_const).add continuous_const).tendsto s₀
      rw [sub_self, zero_add] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro h
      apply hw
      have h1 : w - s₀ + 1 = 1 := h
      exact (by linear_combination h1 : w = s₀)
  refine (riemannZeta_residue_one.comp hmap).congr fun w => ?_
  simp only [Function.comp]
  ring_nf

theorem norm_cpow_le_add_one {s : ℂ} (hs : s ≠ 0) (hs1 : s.re ≤ 1) (n : ℕ) :
    ‖((n : ℝ) : ℂ) ^ s‖ ≤ 1 * ((n : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Complex.zero_cpow hs]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0, one_mul]
  calc (n : ℝ) ^ s.re ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hs1
    _ = n := Real.rpow_one _
    _ ≤ (n : ℝ) + 1 := by linarith

theorem linearGrowth_of_energy {r : ℕ → ℂ} (hr0 : r 0 = 0) {E : ℝ}
    (hE : ∀ T : ℕ, ∑ n ∈ Icc 1 T, ‖r n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E) (n : ℕ) :
    ‖r n‖ ≤ Real.sqrt E * ((n : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hr0]
  · exact norm_le_of_energyBounded hE hn

/-- **Mellin residues pin power-like solutions to the translated zeros.** Let `0 < ε < 1/2` and
`v = Σ_{s∈F} c_s n^s + r` with `1/2 < Re s ≤ 1`, `s ≠ 1 − ε`, and `r` of bounded pronic energy. If
`S_ε v = c' n^{1−ε} + r'` with `r'` of bounded pronic energy, then `ζ(s + ε) = 0` whenever
`c_s ≠ 0`. -/
theorem riemannZeta_add_eq_zero_of_powerLike_solution {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2)
    (F : Finset ℂ) (hF : ∀ s ∈ F, 1 / 2 < s.re ∧ s.re ≤ 1 ∧ s ≠ ((1 - ε : ℝ) : ℂ))
    (c : ℂ → ℂ) {r r' : ℕ → ℂ} (hr0 : r 0 = 0) (hr : EnergyBounded r) (hr'0 : r' 0 = 0)
    (hr' : EnergyBounded r') (c' : ℂ)
    (hlaw : ∀ n, cTotalCofactorSum ε (fun m => ∑ s ∈ F, c s * ((m : ℝ) : ℂ) ^ s + r m) n =
      c' * ((n : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ) + r' n) :
    ∀ s ∈ F, c s ≠ 0 → riemannZeta (s + ε) = 0 := by
  intro s₀ hs₀ hc₀
  obtain ⟨E, hE⟩ := hr
  obtain ⟨E', hE'⟩ := hr'
  set α : ℂ := ((1 - ε : ℝ) : ℂ) with hαdef
  have hαre : α.re = 1 - ε := by simp [hαdef]
  have hα0 : α ≠ 0 := fun h => by
    have := congrArg Complex.re h; rw [hαre] at this; simp at this; linarith
  have hsne : ∀ s ∈ F, s ≠ 0 := fun s hs h => by
    have := (hF s hs).1; rw [h] at this; simp at this; linarith
  set v : ℕ → ℂ := fun m => ∑ s ∈ F, c s * ((m : ℝ) : ℂ) ^ s + r m with hvdef
  have hv0 : v 0 = 0 := by
    simp only [hvdef, hr0, add_zero, Nat.cast_zero, Complex.ofReal_zero]
    exact Finset.sum_eq_zero fun s hs => by rw [Complex.zero_cpow (hsne s hs), mul_zero]
  set Cv := ∑ s ∈ F, ‖c s‖ + Real.sqrt E
  have hCv : ∀ n : ℕ, ‖v n‖ ≤ Cv * ((n : ℝ) + 1) := by
    intro n
    have h1 : ‖∑ s ∈ F, c s * ((n : ℝ) : ℂ) ^ s‖ ≤ (∑ s ∈ F, ‖c s‖) * ((n : ℝ) + 1) := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun s hs => ?_
      rw [norm_mul]
      have := norm_cpow_le_add_one (hsne s hs) (hF s hs).2.1 n
      rw [one_mul] at this
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
    have h2 := linearGrowth_of_energy hr0 hE n
    calc ‖v n‖ ≤ ‖∑ s ∈ F, c s * ((n : ℝ) : ℂ) ^ s‖ + ‖r n‖ := norm_add_le _ _
      _ ≤ _ := by simp only [Cv]; nlinarith
  have hCr : ∀ n : ℕ, ‖r n‖ ≤ Real.sqrt E * ((n : ℝ) + 1) := linearGrowth_of_energy hr0 hE
  have hCr' : ∀ n : ℕ, ‖r' n‖ ≤ Real.sqrt E' * ((n : ℝ) + 1) := linearGrowth_of_energy hr'0 hE'
  -- the meromorphic comparison function
  set G : ℂ → ℂ := fun w => riemannZeta (w + ε) *
      (∑ s ∈ F, c s * (s * riemannZeta (w - s + 1) + powerCorrection s w) + rowMellin r w) -
      (c' * (α * riemannZeta (w - α + 1) + powerCorrection α w) + rowMellin r' w) with hGdef
  -- it vanishes on `Re w > 2`
  have hαle : α.re ≤ 1 := by rw [hαre]; linarith
  have hαge : 0 ≤ α.re := by rw [hαre]; linarith
  have hGzero : ∀ w : ℂ, 2 < w.re → G w = 0 := by
    intro w hw
    have hw1 : 1 < w.re := by linarith
    have hpow : ∀ s : ℂ, s ≠ 0 → s.re ≤ 1 →
        Summable fun n : ℕ => ((n : ℝ) : ℂ) ^ s * complexMellinCell w n := fun s hs hs1 =>
      summable_rowMellin (v := fun n : ℕ => ((n : ℝ) : ℂ) ^ s) (by simp [Complex.zero_cpow hs])
        (C := 1) (norm_cpow_le_add_one hs hs1) hw1
    have hSr : Summable fun n => r n * complexMellinCell w n := summable_rowMellin hr0 hCr hw1
    have hSr' : Summable fun n => r' n * complexMellinCell w n := summable_rowMellin hr'0 hCr' hw1
    have hsF : ∀ s ∈ F, Summable fun n : ℕ => c s * (((n : ℝ) : ℂ) ^ s * complexMellinCell w n) :=
      fun s hs => (hpow s (hsne s hs) (hF s hs).2.1).mul_left (c s)
    have hMv : rowMellin v w =
        ∑ s ∈ F, c s * (s * riemannZeta (w - s + 1) + powerCorrection s w) + rowMellin r w := by
      have hexp : (fun n => v n * complexMellinCell w n) = fun n : ℕ =>
          (∑ s ∈ F, c s * (((n : ℝ) : ℂ) ^ s * complexMellinCell w n)) +
            r n * complexMellinCell w n := by
        funext n
        simp only [hvdef]
        rw [add_mul, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [rowMellin, hexp, (summable_sum hsF).tsum_add hSr, Summable.tsum_finsetSum hsF]
      congr 1
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [tsum_mul_left]
      congr 1
      have h := rowMellin_cpow_eq (hsne s hs) (by linarith [(hF s hs).1]) (by linarith [(hF s hs).2.1])
        (by linarith [(hF s hs).2.1] : s.re + 1 < w.re)
      rw [rowMellin] at h
      exact h
    have hMS : rowMellin (cTotalCofactorSum ε v) w =
        c' * (α * riemannZeta (w - α + 1) + powerCorrection α w) + rowMellin r' w := by
      have hexp : (fun n => cTotalCofactorSum ε v n * complexMellinCell w n) = fun n : ℕ =>
          c' * (((n : ℝ) : ℂ) ^ α * complexMellinCell w n) + r' n * complexMellinCell w n := by
        funext n
        rw [hlaw n]
        ring
      have h := rowMellin_cpow_eq hα0 hαge (by linarith) (by linarith : α.re + 1 < w.re)
      rw [rowMellin] at h
      rw [rowMellin, hexp, ((hpow α hα0 hαle).mul_left c').tsum_add hSr', tsum_mul_left, h]
      rfl
    have hfub := (hasSum_cTotalCofactorSum_mul_cell hε0 hv0 hCv hw).tsum_eq
    simp only [hGdef]
    rw [← hMv, ← hMS]
    have hfub' : rowMellin (cTotalCofactorSum ε v) w = riemannZeta (w + ε) * rowMellin v w := hfub
    rw [hfub', sub_self]
  -- `G` is meromorphic on `Re w > 1/2`
  set U : Set ℂ := {w : ℂ | 1 / 2 < w.re} with hUdef
  have hDr := differentiableOn_rowMellin hr0 hE
  have hDr' := differentiableOn_rowMellin hr'0 hE'
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hcorr : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → ∀ u ∈ U, AnalyticAt ℂ (powerCorrection s) u := by
    intro s hs0 hs1 u hu
    refine (differentiableOn_powerCorrection hs0 (by linarith)).analyticAt ?_
    have hu' : (1 : ℝ) / 2 < u.re := hu
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show s.re - 1 < u.re by linarith)
  have hanR : ∀ u ∈ U, AnalyticAt ℂ (rowMellin r) u := fun u hu => hDr.analyticAt (hUo.mem_nhds hu)
  have hanR' : ∀ u ∈ U, AnalyticAt ℂ (rowMellin r') u := fun u hu =>
    hDr'.analyticAt (hUo.mem_nhds hu)
  have hmero : MeromorphicOn G U := by
    intro u hu
    have hzs : ∀ a : ℂ, MeromorphicAt (fun z => riemannZeta (z - a + 1)) u := fun a =>
      meromorphicAt_riemannZeta_comp ((analyticAt_id.sub analyticAt_const).add analyticAt_const)
    have hz1 : MeromorphicAt (fun z => riemannZeta (z + ε)) u :=
      meromorphicAt_riemannZeta_comp (analyticAt_id.add analyticAt_const)
    have hsum : MeromorphicAt (fun z => ∑ s ∈ F, c s * (s * riemannZeta (z - s + 1) +
        powerCorrection s z)) u :=
      MeromorphicAt.fun_sum fun s hs => (MeromorphicAt.const (c s) u).mul
        (((MeromorphicAt.const s u).mul (hzs s)).add
          (hcorr s (by linarith [(hF s hs).1]) (hF s hs).2.1 u hu).meromorphicAt)
    have hP : MeromorphicAt (fun z => c' * (α * riemannZeta (z - α + 1) + powerCorrection α z) +
        rowMellin r' z) u :=
      ((MeromorphicAt.const c' u).mul (((MeromorphicAt.const α u).mul (hzs α)).add
        (hcorr α hαge hαle u hu).meromorphicAt)).add (hanR' u hu).meromorphicAt
    exact (hz1.mul (hsum.add (hanR u hu).meromorphicAt)).sub hP
  -- the identity theorem: `G` vanishes near every point of `Re w > 1/2`
  have h3U : (3 : ℂ) ∈ U := by simp only [hUdef, Set.mem_setOf_eq]; norm_num
  have hG3 : meromorphicOrderAt G 3 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hnbhd : {w : ℂ | 2 < w.re} ∈ 𝓝 (3 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp only [Set.mem_setOf_eq]; norm_num)
    filter_upwards [nhdsWithin_le_nhds hnbhd] with w hw
    exact hGzero w hw
  have hs₀U : s₀ ∈ U := (hF s₀ hs₀).1
  have hs₀top : meromorphicOrderAt G s₀ = ⊤ := by
    by_contra hne
    exact ((hmero.exists_meromorphicOrderAt_ne_top_iff_forall_mem
      (isConnected_halfPlane _)).mp ⟨s₀, hs₀U, hne⟩ 3 h3U) hG3
  have hev := meromorphicOrderAt_eq_top_iff.mp hs₀top
  -- the residue at `s₀`
  have hs₀α : s₀ ≠ α := (hF s₀ hs₀).2.2
  set R : ℂ → ℂ := fun w => ∑ s ∈ F.erase s₀, c s * (s * riemannZeta (w - s + 1) +
      powerCorrection s w) + c s₀ * powerCorrection s₀ w + rowMellin r w with hRdef
  set P : ℂ → ℂ := fun w => c' * (α * riemannZeta (w - α + 1) + powerCorrection α w) +
      rowMellin r' w with hPdef
  have hid : ∀ w, (w - s₀) * G w = riemannZeta (w + ε) *
      (c s₀ * s₀ * ((w - s₀) * riemannZeta (w - s₀ + 1)) + (w - s₀) * R w) - (w - s₀) * P w := by
    intro w
    simp only [hGdef, hRdef, hPdef]
    rw [← Finset.add_sum_erase F _ hs₀]
    ring
  have hcz : ∀ a : ℂ, s₀ - a + 1 ≠ 1 → ContinuousAt (fun z => riemannZeta (z - a + 1)) s₀ :=
    fun a ha => continuousAt_riemannZeta_comp
      ((continuous_id.sub continuous_const).add continuous_const).continuousAt ha
  have hRc : ContinuousAt R s₀ := by
    have h1 : ContinuousAt (fun w => ∑ s ∈ F.erase s₀, c s * (s * riemannZeta (w - s + 1) +
        powerCorrection s w)) s₀ := by
      refine tendsto_finsetSum _ fun s hs => ?_
      have hss : s ≠ s₀ := Finset.ne_of_mem_erase hs
      have hsF : s ∈ F := Finset.mem_of_mem_erase hs
      have hne : s₀ - s + 1 ≠ 1 := fun h => hss (by linear_combination -h)
      exact (continuousAt_const.mul (continuousAt_const.mul (hcz s hne) |>.add
        (hcorr s (by linarith [(hF s hsF).1]) (hF s hsF).2.1 s₀ hs₀U).continuousAt)).tendsto
    exact (h1.add (continuousAt_const.mul
      (hcorr s₀ (by linarith [(hF s₀ hs₀).1]) (hF s₀ hs₀).2.1 s₀ hs₀U).continuousAt)).add
      (hanR s₀ hs₀U).continuousAt
  have hPc : ContinuousAt P s₀ := by
    have hne : s₀ - α + 1 ≠ 1 := fun h => hs₀α (by linear_combination h)
    exact (continuousAt_const.mul ((continuousAt_const.mul (hcz α hne)).add
      (hcorr α hαge hαle s₀ hs₀U).continuousAt)).add (hanR' s₀ hs₀U).continuousAt
  have hε1 : s₀ + (ε : ℂ) ≠ 1 := fun h => hs₀α (by
    rw [hαdef]; push_cast; linear_combination h)
  have hT1 : Tendsto (fun w => riemannZeta (w + ε)) (𝓝[≠] s₀) (𝓝 (riemannZeta (s₀ + ε))) :=
    (continuousAt_riemannZeta_comp (continuous_id.add continuous_const).continuousAt hε1).tendsto.mono_left
      nhdsWithin_le_nhds
  have hlin : Tendsto (fun w : ℂ => w - s₀) (𝓝[≠] s₀) (𝓝 0) := by
    have h : Tendsto (fun w : ℂ => w - s₀) (𝓝 s₀) (𝓝 (s₀ - s₀)) :=
      (continuous_id.sub continuous_const).tendsto s₀
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hT3 : Tendsto (fun w => (w - s₀) * R w) (𝓝[≠] s₀) (𝓝 0) := by
    have := hlin.mul (hRc.tendsto.mono_left nhdsWithin_le_nhds)
    rwa [zero_mul] at this
  have hT4 : Tendsto (fun w => (w - s₀) * P w) (𝓝[≠] s₀) (𝓝 0) := by
    have := hlin.mul (hPc.tendsto.mono_left nhdsWithin_le_nhds)
    rwa [zero_mul] at this
  have hlim : Tendsto (fun w => (w - s₀) * G w) (𝓝[≠] s₀)
      (𝓝 (riemannZeta (s₀ + ε) * (c s₀ * s₀ * 1 + 0) - 0)) := by
    refine Tendsto.congr (fun w => (hid w).symm) ?_
    exact (hT1.mul (((tendsto_sub_mul_riemannZeta_shift s₀).const_mul (c s₀ * s₀)).add hT3)).sub hT4
  have hzero : Tendsto (fun w => (w - s₀) * G w) (𝓝[≠] s₀) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with w hw
    rw [hw, mul_zero]
  have heq := tendsto_nhds_unique hlim hzero
  simp only [mul_one, add_zero, sub_zero] at heq
  rcases mul_eq_zero.mp heq with h | h
  · exact h
  · exact absurd h (mul_ne_zero hc₀ (hsne s₀ hs₀))

end GaloisForLFunctions.ArithmeticDefectRigidity
