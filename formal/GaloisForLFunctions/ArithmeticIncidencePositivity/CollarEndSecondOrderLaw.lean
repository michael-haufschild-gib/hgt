import GaloisForLFunctions.ArithmeticIncidencePositivity.QuarterPointClassification
import GaloisForLFunctions.HTGeometry.HyperbolicBounds

/-!
# The collar end to second order

On the anti-diagonal of sum `s` the collar is the set where the polar weight
`P_s(a) = cosh(s/2) − cosh(s/2 − a)` is below the archimedean density `ω(s)`. For `s ≥ 4 log 2`
it is exactly two axis intervals `(0, c) ∪ (s − c, s)`, where the **collar end** `c = c(s)` is the
root of `P_s(c) = ω(s)` in `(0, s/2]` (`antiDiagonalCollar_eq_collarEnd`), and with the inner end
`ℓ = ω(s)/sinh(s/2)` and `a = coth(s/2)/2`,

`|c − ℓ − a ℓ²| ≤ 14 ℓ³`        (`abs_collarEnd_sub_second_order_le`).

The second-order coefficient is exact in `q = e^{−s}`: `a ℓ = q/(1 − q)³`
(`half_coth_mul_collarInnerEnd`), so `c(s) = ℓ(s) (1 + e^{−s}/(1 − e^{−s})³ + O(e^{−2s}))` and
`c(s)/ℓ(s) = 1 + e^{−s} + O(e^{−2s})`.

Mechanism: `P_s(x) = sinh(s/2) (sinh x − 2a (cosh x − 1))`, and on `[0, 1]`
`x ≤ sinh x ≤ x(1 + x²)`, `x²/2 ≤ cosh x − 1 ≤ (x²/2)(1 + x²)`, so the normalized weight is
`x − a x² + O(x³)`; the root lies in `[ℓ, 2ℓ]` and the quadratic is inverted to second order.
-/

open RHTower Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### Hyperbolic bounds on `[0, 1]` -/

theorem sq_half_le_cosh_sub_one {x : ℝ} (hx : 0 ≤ x) : x ^ 2 / 2 ≤ Real.cosh x - 1 := by
  have h := HTGeometry.sinh_half_sq x
  have hs := HTGeometry.self_le_sinh_of_nonneg (show 0 ≤ x / 2 by linarith)
  nlinarith [pow_le_pow_left₀ (by linarith : 0 ≤ x / 2) hs 2]

theorem cosh_le_one_add_sq {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : Real.cosh x ≤ 1 + x ^ 2 := by
  have h := HTGeometry.cosh_sub_one_le hx
  have hc := Real.one_le_cosh x
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hx2 (show 0 ≤ x ^ 2 * (Real.cosh x - 1) by
    have : 0 ≤ Real.cosh x - 1 := by linarith
    positivity)]

/-! ### The normalized polar weight -/

/-- `P_s(x) = sinh(s/2) sinh x − cosh(s/2) (cosh x − 1)`. -/
theorem crossingPolarWeight_eq_sinh_cosh (s x : ℝ) :
    crossingPolarWeight s x = Real.sinh (s / 2) * Real.sinh x - Real.cosh (s / 2) * (Real.cosh x - 1) := by
  rw [crossingPolarWeight_eq, Real.cosh_sub]
  ring

/-- Upper bound `P_s(x) ≤ sinh(s/2)(x + x³) − cosh(s/2) x²/2` on `[0, 1]`. -/
theorem crossingPolarWeight_le_cubic {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    crossingPolarWeight s x ≤
      Real.sinh (s / 2) * (x + x ^ 3) - Real.cosh (s / 2) * (x ^ 2 / 2) := by
  rw [crossingPolarWeight_eq_sinh_cosh]
  have hsh : 0 ≤ Real.sinh (s / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  have hch : 0 ≤ Real.cosh (s / 2) := (Real.cosh_pos _).le
  have h1 : Real.sinh x ≤ x + x ^ 3 := by
    have := HTGeometry.sinh_le_self_mul_cosh hx
    nlinarith [cosh_le_one_add_sq hx hx1]
  have h2 := sq_half_le_cosh_sub_one hx
  nlinarith [mul_le_mul_of_nonneg_left h1 hsh, mul_le_mul_of_nonneg_left h2 hch]

/-- Lower bound `P_s(x) ≥ sinh(s/2) x − cosh(s/2)(x²/2)(1 + x²)` on `[0, 1]`. -/
theorem le_crossingPolarWeight_quartic {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sinh (s / 2) * x - Real.cosh (s / 2) * (x ^ 2 / 2 * (1 + x ^ 2)) ≤
      crossingPolarWeight s x := by
  rw [crossingPolarWeight_eq_sinh_cosh]
  have hsh : 0 ≤ Real.sinh (s / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  have hch : 0 ≤ Real.cosh (s / 2) := (Real.cosh_pos _).le
  have h1 := HTGeometry.self_le_sinh_of_nonneg hx
  have h2 : Real.cosh x - 1 ≤ x ^ 2 / 2 * (1 + x ^ 2) := by
    have := HTGeometry.cosh_sub_one_le hx
    have hc := cosh_le_one_add_sq hx hx1
    nlinarith [mul_le_mul_of_nonneg_left hc (show 0 ≤ x ^ 2 / 2 by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hsh, mul_le_mul_of_nonneg_left h2 hch]


/-! ### Scale bounds for `s ≥ 4 log 2` -/

theorem exp_neg_le_sixteenth {s : ℝ} (hs : 4 * Real.log 2 ≤ s) : Real.exp (-s) ≤ 1 / 16 := by
  have h := exp_neg_half_le_of_four_log_two_le hs
  have e : Real.exp (-s) = Real.exp (-s / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e]
  nlinarith [Real.exp_pos (-s / 2)]

theorem collarInnerEnd_le_small {s : ℝ} (hs : 4 * Real.log 2 ≤ s) : collarInnerEnd s ≤ 0.134 := by
  have h1 := collarInnerEnd_le hs
  have h2 := exp_neg_le_sixteenth hs
  nlinarith

theorem collarInnerEnd_pos {s : ℝ} (hs : 0 < s) : 0 < collarInnerEnd s :=
  div_pos (archLevyDensity_pos hs) (Real.sinh_pos_iff.mpr (by linarith))

/-- `coth(s/2) ≤ 17/15` for `s ≥ 4 log 2`. -/
theorem cosh_half_le_mul_sinh_half {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    15 * Real.cosh (s / 2) ≤ 17 * Real.sinh (s / 2) := by
  have h := exp_neg_half_le_of_four_log_two_le hs
  have hq := Real.exp_pos (-s / 2)
  have hE : Real.exp (s / 2) * Real.exp (-s / 2) = 1 := by rw [← Real.exp_add]; ring_nf; simp
  rw [Real.cosh_eq, Real.sinh_eq, show -(s / 2) = -s / 2 by ring]
  nlinarith [Real.exp_pos (s / 2)]

/-- **Inverting `x − a x² + O(x³)` to second order.** If `ℓ ≤ c ≤ 2ℓ`, `ℓ ≤ 0.134`,
`0 ≤ a ≤ 17/30` and `c − a c²(1 + c²) ≤ ℓ ≤ c + c³ − a c²`, then `|c − ℓ − a ℓ²| ≤ 8ℓ³`. -/
theorem second_order_inversion {a ℓ c : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 17 / 30) (hℓ0 : 0 < ℓ)
    (hℓs : ℓ ≤ 0.134) (hlow : ℓ ≤ c) (hup : c ≤ 2 * ℓ) (hU' : ℓ ≤ c + c ^ 3 - a * c ^ 2)
    (hL' : c - a * c ^ 2 * (1 + c ^ 2) ≤ ℓ) :
    |c - ℓ - a * ℓ ^ 2| ≤ 8 * ℓ ^ 3 := by
  have hc0 : 0 < c := by linarith
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hcc : c ^ 3 ≤ 8 * ℓ ^ 3 := by
      have := pow_le_pow_left₀ hc0.le hup 3
      nlinarith
    have hsq : ℓ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hℓ0.le hlow 2
    nlinarith [mul_le_mul_of_nonneg_left hsq ha0]
  · have hdiff : c - ℓ ≤ a * c ^ 2 * (1 + c ^ 2) := by linarith
    have hc2 : c ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
    have hcl : c + ℓ ≤ 3 * ℓ := by linarith
    have h1 : a * (c ^ 2 - ℓ ^ 2) ≤ a * (a * (4 * ℓ ^ 2) * (1 + 4 * ℓ ^ 2) * (3 * ℓ)) := by
      apply mul_le_mul_of_nonneg_left _ ha0
      have e : c ^ 2 - ℓ ^ 2 = (c - ℓ) * (c + ℓ) := by ring
      rw [e]
      have hd0 : 0 ≤ c - ℓ := by linarith
      calc (c - ℓ) * (c + ℓ) ≤ (a * c ^ 2 * (1 + c ^ 2)) * (3 * ℓ) :=
            mul_le_mul hdiff hcl (by linarith) (by positivity)
        _ ≤ (a * (4 * ℓ ^ 2) * (1 + 4 * ℓ ^ 2)) * (3 * ℓ) := by
            gcongr
    have h2 : c - ℓ - a * c ^ 2 ≤ a * c ^ 4 := by
      have e : a * c ^ 2 * (1 + c ^ 2) = a * c ^ 2 + a * c ^ 4 := by ring
      linarith
    have hc4 : c ^ 4 ≤ 16 * ℓ ^ 4 :=
      (pow_le_pow_left₀ hc0.le hup 4).trans_eq (by ring)
    have hℓ2 : ℓ ^ 2 ≤ 0.018 := by
      have := mul_le_mul hℓs hℓs hℓ0.le (by norm_num)
      nlinarith
    have hfin : a * (a * (4 * ℓ ^ 2) * (1 + 4 * ℓ ^ 2) * (3 * ℓ)) + a * (16 * ℓ ^ 4) ≤ 8 * ℓ ^ 3 := by
      have hA : a * a ≤ 0.322 := by nlinarith
      have e : a * (a * (4 * ℓ ^ 2) * (1 + 4 * ℓ ^ 2) * (3 * ℓ)) + a * (16 * ℓ ^ 4) =
          ℓ ^ 3 * (12 * (a * a) * (1 + 4 * ℓ ^ 2) + 16 * a * ℓ) := by ring
      rw [e]
      have hb1 : 12 * (a * a) * (1 + 4 * ℓ ^ 2) ≤ 12 * 0.322 * (1 + 4 * 0.018) := by
        have : 1 + 4 * ℓ ^ 2 ≤ 1 + 4 * 0.018 := by linarith
        have h0 : 0 ≤ a * a := by positivity
        nlinarith [mul_le_mul hA this (by positivity) (by norm_num)]
      have hb2 : 16 * a * ℓ ≤ 16 * (17 / 30) * 0.134 := by
        have := mul_le_mul ha1 hℓs hℓ0.le (by norm_num)
        linarith
      have hb : 12 * (a * a) * (1 + 4 * ℓ ^ 2) + 16 * a * ℓ ≤ 8 := by
        norm_num at hb1 hb2 ⊢; linarith
      have hl3 : 0 ≤ ℓ ^ 3 := by positivity
      have := mul_le_mul_of_nonneg_left hb hl3
      linarith
    have : c - ℓ - a * ℓ ^ 2 = a * (c ^ 2 - ℓ ^ 2) + (c - ℓ - a * c ^ 2) := by ring
    nlinarith [mul_le_mul_of_nonneg_left hc4 ha0]


/-! ### The collar end -/

/-- **Second-order law of the collar end.** For `s ≥ 4 log 2` the collar of the anti-diagonal of
sum `s` is `(0, c) ∪ (s − c, s)` with `P_s(c) = ω(s)`, `ℓ ≤ c ≤ 2ℓ` and
`|c − ℓ − (coth(s/2)/2) ℓ²| ≤ 8ℓ³`, `ℓ = ω(s)/sinh(s/2)`. -/
theorem collarEnd_second_order {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    ∃ c, 0 < c ∧ c ≤ s / 2 ∧ crossingPolarWeight s c = archLevyDensity s ∧
      antiDiagonalCollar s = Ioo 0 c ∪ Ioo (s - c) s ∧
      collarInnerEnd s ≤ c ∧ c ≤ 2 * collarInnerEnd s ∧
      |c - collarInnerEnd s - Real.cosh (s / 2) / (2 * Real.sinh (s / 2)) * collarInnerEnd s ^ 2| ≤
        8 * collarInnerEnd s ^ 3 := by
  have hs0 := pos_of_four_log_two_le hs
  have hl2 := Real.log_two_gt_d9
  have hωℓ : archLevyDensity s = Real.sinh (s / 2) * collarInnerEnd s := by
    have : Real.sinh (s / 2) ≠ 0 := (Real.sinh_pos_iff.mpr (by linarith)).ne'
    rw [collarInnerEnd]; field_simp
  set Sh := Real.sinh (s / 2) with hSh
  set Ch := Real.cosh (s / 2) with hCh
  set ω := archLevyDensity s with hω
  set ℓ := collarInnerEnd s with hℓ
  have hSh0 : 0 < Sh := Real.sinh_pos_iff.mpr (by linarith)
  have hCh0 : 0 < Ch := Real.cosh_pos _
  have hω0 : 0 < ω := archLevyDensity_pos hs0
  have hℓ0 : 0 < ℓ := collarInnerEnd_pos hs0
  have hℓs : ℓ ≤ 0.134 := collarInnerEnd_le_small hs
  have hcoth := cosh_half_le_mul_sinh_half hs
  -- the midpoint is paid
  have hmid : ω ≤ crossingPolarWeight s (s / 2) := by
    rw [crossingPolarWeight_eq, sub_self, Real.cosh_zero]
    have h1 := sq_half_le_cosh_sub_one (show 0 ≤ s / 2 by linarith)
    have h2 : ω ≤ 1 / 3 := by
      rw [hω, archLevyDensity]
      have hh := exp_neg_half_le_of_four_log_two_le hs
      have hq2 : Real.exp (-2 * s) ≤ 1 / 16 := by
        have := exp_neg_le_sixteenth hs
        calc Real.exp (-2 * s) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
          _ ≤ 1 / 16 := this
      rw [div_le_iff₀ (by linarith)]
      linarith
    nlinarith
  obtain ⟨c, hc0, hcs, hcE, hset⟩ := unpaidSet_eq_of_le_midpoint hs0 hω0 hmid
  have hcollar : antiDiagonalCollar s = Ioo 0 c ∪ Ioo (s - c) s := by
    rw [antiDiagonalCollar_eq hs0, ← hset]
    ext a; simp only [unpaidSet, mem_inter_iff, mem_Ioo, mem_setOf_eq, and_assoc]; exact Iff.rfl
  -- first order: `ℓ ≤ c ≤ 2ℓ`
  have hlow : ℓ ≤ c := by
    have h := crossingPolarWeight_le hs0.le hc0.le
    rw [hcE, ← hSh, hωℓ] at h
    nlinarith
  have hup : c ≤ 2 * ℓ := by
    by_contra hlt
    rw [not_le] at hlt
    have h2l : 2 * ℓ ≤ 1 := by linarith
    have hq := le_crossingPolarWeight_quartic (x := 2 * ℓ) hs0.le (by linarith) h2l
    rw [← hSh, ← hCh] at hq
    have hlt' := crossingPolarWeight_lt (s := s) hlt hcs
    rw [hcE] at hlt'
    -- `P_s(2ℓ) ≥ ω` because `4 a ℓ (1 + 4ℓ²) ≤ 1`
    have key : Ch * ((2 * ℓ) ^ 2 / 2 * (1 + (2 * ℓ) ^ 2)) ≤ Sh * ℓ := by
      have h4 : (2 * ℓ) ^ 2 / 2 * (1 + (2 * ℓ) ^ 2) ≤ ℓ * (0.268 * 1.072) := by
        have : (2 * ℓ) ^ 2 ≤ 0.072 := by nlinarith
        nlinarith
      have h5 : Ch * (ℓ * (0.268 * 1.072)) ≤ Sh * ℓ := by nlinarith
      exact (mul_le_mul_of_nonneg_left h4 hCh0.le).trans h5
    nlinarith
  have hc1 : c ≤ 1 := by linarith
  -- second order
  have hU := crossingPolarWeight_le_cubic hs0.le hc0.le hc1
  have hL := le_crossingPolarWeight_quartic hs0.le hc0.le hc1
  rw [hcE, ← hSh, ← hCh, hωℓ] at hU hL
  set a := Ch / (2 * Sh) with ha
  have hCha : Ch = 2 * a * Sh := by rw [ha]; field_simp
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 17 / 30 := by
    rw [ha, div_le_iff₀ (by positivity)]; linarith
  rw [hCha] at hU hL
  -- `c − ℓ ∈ [a c² − c³, a c² + a c⁴]`
  have hU' : ℓ ≤ c + c ^ 3 - a * c ^ 2 := by nlinarith
  have hL' : c - a * c ^ 2 * (1 + c ^ 2) ≤ ℓ := by nlinarith
  exact ⟨c, hc0, hcs, hcE, hcollar, hlow, hup,
    second_order_inversion ha0 ha1 hℓ0 hℓs hlow hup hU' hL'⟩

/-- **The exact second-order coefficient.** `(coth(s/2)/2) ℓ(s) = e^{−s}/(1 − e^{−s})³`. -/
theorem half_coth_mul_collarInnerEnd {s : ℝ} (hs : 0 < s) :
    Real.cosh (s / 2) / (2 * Real.sinh (s / 2)) * collarInnerEnd s =
      Real.exp (-s) / (1 - Real.exp (-s)) ^ 3 := by
  rw [collarInnerEnd_eq hs]
  set q := Real.exp (-s) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have e2 : Real.exp (-2 * s) = q ^ 2 := by rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hcoth : Real.cosh (s / 2) / Real.sinh (s / 2) = (1 + q) / (1 - q) := by
    rw [Real.cosh_eq, Real.sinh_eq]
    have hx := Real.exp_pos (s / 2)
    have hneg : Real.exp (-(s / 2)) = Real.exp (s / 2) * q := by
      rw [hq, ← Real.exp_add]; congr 1; ring
    rw [hneg]
    have h1 : Real.exp (s / 2) - Real.exp (s / 2) * q ≠ 0 := by
      have : 0 < Real.exp (s / 2) * (1 - q) := mul_pos hx (by linarith)
      linarith
    field_simp
  rw [e2, show Real.cosh (s / 2) / (2 * Real.sinh (s / 2)) =
    (Real.cosh (s / 2) / Real.sinh (s / 2)) / 2 by ring, hcoth]
  have h1 : (1 : ℝ) - q ≠ 0 := by linarith
  have h2 : (1 : ℝ) - q ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring


/-- **The collar ratio.** For `s ≥ 4 log 2` the collar end satisfies
`|c(s)/ℓ(s) − 1 − e^{−s}/(1 − e^{−s})³| ≤ 37 e^{−2s}`: `c(s)/ℓ(s) = 1 + e^{−s} + O(e^{−2s})`. -/
theorem collarEnd_ratio {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    ∃ c, antiDiagonalCollar s = Ioo 0 c ∪ Ioo (s - c) s ∧
      |c / collarInnerEnd s - 1 - Real.exp (-s) / (1 - Real.exp (-s)) ^ 3| ≤
        37 * Real.exp (-s) ^ 2 := by
  have hs0 := pos_of_four_log_two_le hs
  obtain ⟨c, -, -, -, hcollar, -, -, hbound⟩ := collarEnd_second_order hs
  refine ⟨c, hcollar, ?_⟩
  have hℓ0 := collarInnerEnd_pos hs0
  have hcoef := half_coth_mul_collarInnerEnd hs0
  set ℓ := collarInnerEnd s with hℓ
  set a := Real.cosh (s / 2) / (2 * Real.sinh (s / 2)) with ha
  have e : c / ℓ - 1 - a * ℓ = (c - ℓ - a * ℓ ^ 2) / ℓ := by field_simp
  rw [← hcoef, e, abs_div, abs_of_pos hℓ0, div_le_iff₀ hℓ0]
  have hℓu : ℓ ≤ 256 / 239 * (2 * Real.exp (-s)) := collarInnerEnd_le hs
  have hq0 := Real.exp_pos (-s)
  have hsq : ℓ ^ 2 ≤ (256 / 239 * (2 * Real.exp (-s))) ^ 2 := pow_le_pow_left₀ hℓ0.le hℓu 2
  have h8 : 8 * ℓ ^ 3 ≤ 37 * Real.exp (-s) ^ 2 * ℓ := by
    have : 8 * ℓ ^ 2 ≤ 37 * Real.exp (-s) ^ 2 := by nlinarith
    nlinarith
  linarith

end GaloisForLFunctions.ArithmeticIncidencePositivity
