import Mathlib
import GaloisForLFunctions.WindowedLandauTheory.CesaroIncrementBounds

/-!
# Increments of the class Cesàro functionals

For a host character `ψ` with Cesàro functional `G_ψ` (`G_ζ` for `ψ = 0`):

* `w G_ψ(A/w) = Σ_{n ≤ A/w} Λ(n) ψ(n) (A/n - w) + (A ℓ(ψ), or A log w - A log A + (1+γ)A)`
  (`mul_classCesaro_eq`);
* `‖w G_ψ(A/w) - w' G_ψ(A/w')‖ ≤ 7A/w · (w' - w)` for `0 < w ≤ w'`
  (`norm_mul_classCesaro_sub_le`), from Chebyshev's bound;
* `‖G_ψ(y) - G_ψ(x)‖ ≤ log(x+1) + log 4 + 4 + ‖ℓ(ψ)‖` for `ψ ≠ 0` and `|y - x| ≤ 1`
  (`norm_classCesaro_sub_le`), and `|G_ζ(y) - G_ζ(x)| ≤ log 4 + 7`
  (`abs_zetaCesaroFunctional_sub_le`), from Mertens' bound.
-/

open Finset ArithmeticFunction

namespace WindowedLandauTheory

noncomputable section

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
/-- The weighted Cesàro functional as a weighted ramp. -/
theorem mul_classCesaro_eq (D : FrobeniusData H) (ℓ : AddChar (SignPair × H) ℂ → ℂ)
    (ψ : AddChar (SignPair × H) ℂ) {A w : ℝ} (hA : 0 < A) (hw : 0 < w) :
    (w : ℂ) * classCesaro D ℓ ψ (A / w) =
      ∑ n ∈ Icc 1 ⌊A / w⌋₊, (vonMangoldt n : ℂ) * classValue D ψ n * ((A / n - w : ℝ) : ℂ) +
        (if ψ = 0 then ((A * Real.log w - A * Real.log A +
          (1 + Real.eulerMascheroniConstant) * A : ℝ) : ℂ) else (A : ℂ) * ℓ ψ) := by
  have hwa : w * (A / w) = A := by field_simp
  have hterm : ∀ n : ℕ, ((A / n - w : ℝ) : ℂ) = (w : ℂ) * ((A / w / n - 1 : ℝ) : ℂ) := by
    intro n
    rw [← Complex.ofReal_mul]
    congr 1
    rw [mul_sub, mul_one, mul_div_assoc', hwa]
  simp_rw [hterm]
  by_cases h0 : ψ = 0
  · subst h0
    rw [if_pos rfl, classCesaro, if_pos rfl, zetaCesaroFunctional]
    simp_rw [classValue_zero, mul_one]
    rw [Real.log_div hA.ne' hw.ne']
    have hs : ∑ n ∈ Icc 1 ⌊A / w⌋₊, (vonMangoldt n : ℂ) * ((w : ℂ) * ((A / w / n - 1 : ℝ) : ℂ)) =
        (w : ℂ) * ((∑ n ∈ Icc 1 ⌊A / w⌋₊, vonMangoldt n * (A / w / n - 1) : ℝ) : ℂ) := by
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hs]
    generalize (∑ n ∈ Icc 1 ⌊A / w⌋₊, vonMangoldt n * (A / w / n - 1)) = S
    have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
    push_cast
    field_simp
    ring
  · rw [if_neg h0, classCesaro, if_neg h0]
    have hwa' : (w : ℂ) * ((A / w : ℝ) : ℂ) = A := by rw [← Complex.ofReal_mul, hwa]
    rw [mul_add, Finset.mul_sum, ← mul_assoc, hwa']
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring

omit [DecidableEq H] in
theorem norm_vonMangoldt_mul_classValue_le (D : FrobeniusData H) (ψ : AddChar (SignPair × H) ℂ)
    (n : ℕ) : ‖(vonMangoldt n : ℂ) * classValue D ψ n‖ ≤ vonMangoldt n := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
  exact mul_le_of_le_one_right vonMangoldt_nonneg (norm_classValue_le D ψ n)

omit [DecidableEq H] in
/-- **Lipschitz in the weight:** `‖w G_ψ(A/w) - w' G_ψ(A/w')‖ ≤ 7A/w · (w' - w)`. -/
theorem norm_mul_classCesaro_sub_le (D : FrobeniusData H) (ℓ : AddChar (SignPair × H) ℂ → ℂ)
    (ψ : AddChar (SignPair × H) ℂ) {A w w' : ℝ} (hA : 0 < A) (hw : 0 < w) (hww : w ≤ w') :
    ‖(w : ℂ) * classCesaro D ℓ ψ (A / w) - (w' : ℂ) * classCesaro D ℓ ψ (A / w')‖ ≤
      7 * A / w * (w' - w) := by
  have hw' : 0 < w' := hw.trans_le hww
  rw [mul_classCesaro_eq D ℓ ψ hA hw, mul_classCesaro_eq D ℓ ψ hA hw']
  have hramp := norm_weightRamp_sub_le (fun n => (vonMangoldt n : ℂ) * classValue D ψ n)
    (norm_vonMangoldt_mul_classValue_le D ψ) hA.le hw hww
  have hcheb := sum_Icc_vonMangoldt_le (div_nonneg hA.le hw.le)
  have hR : (w' - w) * ∑ n ∈ Icc 1 ⌊A / w⌋₊, vonMangoldt n ≤ (w' - w) * (6 * (A / w)) :=
    mul_le_mul_of_nonneg_left hcheb (by linarith)
  have h67 : (w' - w) * (6 * (A / w)) + A * (w' - w) / w = 7 * A / w * (w' - w) := by
    field_simp
    ring
  have hAw : 0 ≤ A * (w' - w) / w := div_nonneg (mul_nonneg hA.le (by linarith)) hw.le
  by_cases h0 : ψ = 0
  · rw [if_pos h0, if_pos h0]
    set R := ∑ n ∈ Icc 1 ⌊A / w⌋₊, (vonMangoldt n : ℂ) * classValue D ψ n * ((A / n - w : ℝ) : ℂ)
    set R' := ∑ n ∈ Icc 1 ⌊A / w'⌋₊, (vonMangoldt n : ℂ) * classValue D ψ n *
      ((A / n - w' : ℝ) : ℂ)
    have e : R + ((A * Real.log w - A * Real.log A + (1 + Real.eulerMascheroniConstant) * A : ℝ) : ℂ) -
        (R' + ((A * Real.log w' - A * Real.log A + (1 + Real.eulerMascheroniConstant) * A : ℝ) :
          ℂ)) = (R - R') + ((A * (Real.log w - Real.log w') : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e]
    have hlog : Real.log w' - Real.log w ≤ (w' - w) / w := by
      rw [← Real.log_div hw'.ne' hw.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hw' hw)
      rw [div_sub_one hw.ne'] at this
      exact this
    have hlog0 : 0 ≤ Real.log w' - Real.log w := by
      have := Real.log_le_log hw hww
      linarith
    have hc : ‖((A * (Real.log w - Real.log w') : ℝ) : ℂ)‖ ≤ A * (w' - w) / w := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by nlinarith)]
      have := mul_le_mul_of_nonneg_left hlog hA.le
      rw [mul_div_assoc]
      linarith
    calc ‖(R - R') + ((A * (Real.log w - Real.log w') : ℝ) : ℂ)‖
        ≤ ‖R - R'‖ + ‖((A * (Real.log w - Real.log w') : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ (w' - w) * (6 * (A / w)) + A * (w' - w) / w := add_le_add (hramp.trans hR) hc
      _ = 7 * A / w * (w' - w) := h67
  · rw [if_neg h0, if_neg h0, add_sub_add_right_eq_sub]
    linarith [hramp.trans hR]

omit [DecidableEq H] in
/-- **Lipschitz in the point** for `ψ ≠ 0` and `|y - x| ≤ 1`. -/
theorem norm_classCesaro_sub_le (D : FrobeniusData H) (ℓ : AddChar (SignPair × H) ℂ → ℂ)
    {ψ : AddChar (SignPair × H) ℂ} (hψ : ψ ≠ 0) {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxy : |y - x| ≤ 1) :
    ‖classCesaro D ℓ ψ y - classCesaro D ℓ ψ x‖ ≤
      Real.log (x + 1) + (Real.log 4 + 4) + ‖ℓ ψ‖ := by
  obtain ⟨hl, hu⟩ := abs_le.1 hxy
  have hc := norm_vonMangoldt_mul_classValue_le D ψ
  rw [classCesaro, if_neg hψ, classCesaro, if_neg hψ]
  set c : ℕ → ℂ := fun n => (vonMangoldt n : ℂ) * classValue D ψ n with hcdef
  -- the ramp increment, ordered
  have hramp : ‖∑ n ∈ Icc 1 ⌊y⌋₊, (vonMangoldt n : ℂ) * classValue D ψ n * ((y / n - 1 : ℝ) : ℂ) -
      ∑ n ∈ Icc 1 ⌊x⌋₊, (vonMangoldt n : ℂ) * classValue D ψ n * ((x / n - 1 : ℝ) : ℂ)‖ ≤
      Real.log (x + 1) + (Real.log 4 + 4) := by
    have hM : ∀ z : ℝ, 1 ≤ z → z ≤ x + 1 →
        ∑ n ∈ Icc 1 ⌊z⌋₊, vonMangoldt n / n ≤ Real.log (x + 1) + (Real.log 4 + 4) := by
      intro z hz hzx
      have h1 := sum_Icc_vonMangoldt_div_le hz
      have h2 : Real.log z ≤ Real.log (x + 1) := Real.log_le_log (by linarith) hzx
      linarith
    have hpos : ∀ z : ℝ, 0 ≤ ∑ n ∈ Icc 1 ⌊z⌋₊, vonMangoldt n / n := fun z =>
      Finset.sum_nonneg fun n _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
    rcases le_total x y with hxy' | hyx
    · have h := norm_ramp_sub_le c hc (by linarith) hxy'
      have h2 : (y - x) * ∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n / n ≤
          1 * (Real.log (x + 1) + (Real.log 4 + 4)) :=
        mul_le_mul (by linarith) (hM y hy (by linarith)) (hpos y) (by
          have := Real.log_nonneg (show (1 : ℝ) ≤ x + 1 by linarith)
          have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          linarith)
      simpa using h.trans h2
    · have h := norm_ramp_sub_le c hc (by linarith) hyx
      rw [norm_sub_rev] at h
      have h2 : (x - y) * ∑ n ∈ Icc 1 ⌊x⌋₊, vonMangoldt n / n ≤
          1 * (Real.log (x + 1) + (Real.log 4 + 4)) :=
        mul_le_mul (by linarith) (hM x hx (by linarith)) (hpos x) (by
          have := Real.log_nonneg (show (1 : ℝ) ≤ x + 1 by linarith)
          have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          linarith)
      simpa using h.trans h2
  have e : (∑ n ∈ Icc 1 ⌊y⌋₊, (vonMangoldt n : ℂ) * classValue D ψ n * ((y / n - 1 : ℝ) : ℂ) +
      (y : ℂ) * ℓ ψ) -
      (∑ n ∈ Icc 1 ⌊x⌋₊, (vonMangoldt n : ℂ) * classValue D ψ n * ((x / n - 1 : ℝ) : ℂ) +
      (x : ℂ) * ℓ ψ) =
      (∑ n ∈ Icc 1 ⌊y⌋₊, (vonMangoldt n : ℂ) * classValue D ψ n * ((y / n - 1 : ℝ) : ℂ) -
        ∑ n ∈ Icc 1 ⌊x⌋₊, (vonMangoldt n : ℂ) * classValue D ψ n * ((x / n - 1 : ℝ) : ℂ)) +
      ((y - x : ℝ) : ℂ) * ℓ ψ := by
    push_cast
    ring
  rw [e]
  have hl2 : ‖((y - x : ℝ) : ℂ) * ℓ ψ‖ ≤ ‖ℓ ψ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) hxy
  exact (norm_add_le _ _).trans (add_le_add hramp hl2)

end

/-- The ordered increment of `G_ζ` over a step of length at most one. -/
theorem abs_zetaCesaroFunctional_sub_le_of_le {z y : ℝ} (hz : 1 ≤ z) (hzy : z ≤ y)
    (hyz : y ≤ z + 1) :
    |zetaCesaroFunctional y - zetaCesaroFunctional z| ≤ Real.log 4 + 7 := by
  set d := y - z with hd
  have hd0 : 0 ≤ d := by linarith
  have hd1 : d ≤ 1 := by linarith
  have hy : 1 ≤ y := by linarith
  set M := Real.log 4 + 4 with hMdef
  have hM0 : 0 ≤ M := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  -- the ramp increment
  have hSup : ∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n * (y / n - 1) -
      ∑ n ∈ Icc 1 ⌊z⌋₊, vonMangoldt n * (z / n - 1) ≤ d * (Real.log y + M) := by
    have h := norm_ramp_sub_le (fun n => (vonMangoldt n : ℂ))
      (fun n => by rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]) (by linarith) hzy
    have e : ∑ n ∈ Icc 1 ⌊y⌋₊, (vonMangoldt n : ℂ) * ((y / n - 1 : ℝ) : ℂ) -
        ∑ n ∈ Icc 1 ⌊z⌋₊, (vonMangoldt n : ℂ) * ((z / n - 1 : ℝ) : ℂ) =
        ((∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n * (y / n - 1) -
          ∑ n ∈ Icc 1 ⌊z⌋₊, vonMangoldt n * (z / n - 1) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [e, Complex.norm_real, Real.norm_eq_abs] at h
    have h2 := mul_le_mul_of_nonneg_left (sum_Icc_vonMangoldt_div_le hy) hd0
    linarith [le_abs_self (∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n * (y / n - 1) -
      ∑ n ∈ Icc 1 ⌊z⌋₊, vonMangoldt n * (z / n - 1))]
  have hSlo : d * (Real.log z - Real.log 2 - M) ≤ ∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n * (y / n - 1) -
      ∑ n ∈ Icc 1 ⌊z⌋₊, vonMangoldt n * (z / n - 1) := by
    have h := le_vonMangoldtRamp_sub (by linarith) hzy
    have h2 := mul_le_mul_of_nonneg_left (le_sum_Icc_vonMangoldt_div hz) hd0
    linarith
  -- the logarithmic term
  have hz0 : 0 < z := by linarith
  have hy0 : 0 < y := by linarith
  have hL1 : d / y ≤ Real.log y - Real.log z := by
    rw [← Real.log_div hy0.ne' hz0.ne']
    have := Real.one_sub_inv_le_log_of_pos (div_pos hy0 hz0)
    rw [inv_div] at this
    have e : 1 - z / y = d / y := by
      field_simp
      ring
    linarith
  have hL2 : Real.log y - Real.log z ≤ d / z := by
    rw [← Real.log_div hy0.ne' hz0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hy0 hz0)
    have e : y / z - 1 = d / z := by
      field_simp
      ring
    linarith
  have hdz : d / z ≤ d := div_le_self hd0 hz
  have hT : y * Real.log y - z * Real.log z = y * (Real.log y - Real.log z) + d * Real.log z := by
    ring
  have hyL : d ≤ y * (Real.log y - Real.log z) := by
    have := mul_le_mul_of_nonneg_left hL1 hy0.le
    rwa [mul_div_cancel₀ _ hy0.ne'] at this
  have hyU : y * (Real.log y - Real.log z) ≤ 2 * d := by
    have h1 := mul_le_mul_of_nonneg_left hL2 hy0.le
    have h2 : y * (d / z) = d + d * (d / z) := by
      field_simp
      ring
    have h3 : d * (d / z) ≤ d * 1 := mul_le_mul_of_nonneg_left
      (by rw [div_le_one hz0]; linarith) hd0
    linarith
  have hγ1 := Real.eulerMascheroniConstant_lt_two_thirds
  have hγ0 := Real.one_half_lt_eulerMascheroniConstant
  have hl2 := Real.log_two_lt_d9
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hdiff : Real.log y - Real.log z ≤ 1 := hL2.trans (hdz.trans hd1)
  -- assemble
  have hG : zetaCesaroFunctional y - zetaCesaroFunctional z =
      (∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n * (y / n - 1) -
        ∑ n ∈ Icc 1 ⌊z⌋₊, vonMangoldt n * (z / n - 1)) -
      (y * (Real.log y - Real.log z) + d * Real.log z) +
      (1 + Real.eulerMascheroniConstant) * d := by
    rw [← hT]
    unfold zetaCesaroFunctional
    ring
  rw [hG, abs_le]
  have p1 : d * (Real.log y - Real.log z) ≤ d * 1 := mul_le_mul_of_nonneg_left hdiff hd0
  have p2 : d * (M + Real.eulerMascheroniConstant) ≤ 1 * (M + Real.eulerMascheroniConstant) :=
    mul_le_mul_of_nonneg_right hd1 (by linarith)
  have p3 : d * (Real.log 2 + M + 1) ≤ 1 * (Real.log 2 + M + 1) :=
    mul_le_mul_of_nonneg_right hd1 (by linarith)
  have p4 : 0 ≤ d * Real.eulerMascheroniConstant := mul_nonneg hd0 (by linarith)
  constructor
  · nlinarith
  · nlinarith

/-- **Lipschitz in the point for `G_ζ`:** `|G_ζ(y) - G_ζ(x)| ≤ log 4 + 7` for `|y - x| ≤ 1`. -/
theorem abs_zetaCesaroFunctional_sub_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxy : |y - x| ≤ 1) :
    |zetaCesaroFunctional y - zetaCesaroFunctional x| ≤ Real.log 4 + 7 := by
  obtain ⟨hl, hu⟩ := abs_le.1 hxy
  rcases le_total x y with h | h
  · exact abs_zetaCesaroFunctional_sub_le_of_le hx h (by linarith)
  · rw [abs_sub_comm]
    exact abs_zetaCesaroFunctional_sub_le_of_le hy h (by linarith)

end

end WindowedLandauTheory
