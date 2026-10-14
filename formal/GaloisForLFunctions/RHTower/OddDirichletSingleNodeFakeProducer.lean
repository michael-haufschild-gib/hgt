import GaloisForLFunctions.RHTower.DirichletArchimedeanSymbolPositivity
import GaloisForLFunctions.RHTower.DigammaVerticalMinimum

/-!
# Single-node Weil-positive weights for odd Dirichlet data of conductor at least 7

For an odd primitive character of conductor `q` the explicit formula has no pole term, and its
archimedean symbol is `S_q(τ) = Re ψ(¾ + iτ/2) + log(q/π)`.  For `q ≥ 4π` it is nonnegative
(`oddDirichletArchSymbol_nonneg`), so the zero weight is Weil-positive.  Below that threshold `S_q`
is negative near `τ = 0`, with deficit `c_q = −S_q(0) = γ + 3 log 2 − π/2 + log π − log q`.

**Theorem** (`oddDirichletSingleNodeSymbol_nonneg_of_bounds`).  Let `m ≥ 2` and give the single node
`m` the weight `λ(m) = −c_q √m / 2` (`oddSingleNodeWeight`).  If `c_q ≤ c₀` and `(log m)² ≤ B` for
admissible constants `(c₀, B)`, then the weighted symbol `S_q(τ) + c_q cos(τ log m)` is
nonnegative for every `τ`.  Admissible pairs include `(½, ½)` for `m = 2` and `(⅓, 5/4)` for
`m = 3`.

**Corollaries.**
* `oddDirichletSingleNodeSymbol_nonneg_two` (`q ≥ 7`, node `2`).
* `oddDirichletSingleNodeSymbol_nonneg_eight_three` (`q = 8`, node `3`).
* `integral_oddDirichletSingleNode_nonneg`: the corresponding Weil forms are nonnegative on every
  test.

So for every odd conductor `q ≥ 7` the Weil cone of the odd archimedean data contains a weight
supported on one prime.  This extends the zero-weight result from `q ≥ 4π ≈ 12.6` to `q ≥ 7`.
Prime-blind positivity for such data is therefore unconditional and carries no information about
the zeros, and blindness at that single prime already suffices.  Cone uniqueness for `ζ` rests on
the pole term together with the deficit `ψ(¼) − log π ≈ −5.37`.

Proof.  The Gauss series gives `Re ψ(¾ + iy) − ψ(¾) ≥ y²/(¾(9/16 + y²))` (first term), so
`S_q(τ) ≥ −c_q + 16τ²/(27 + 12τ²)`.  For small `τ`, `1 − cos(τ log m) ≤ τ²(log m)²/2` is
dominated by the quadratic growth.  For large `τ`, `16τ²/(27 + 12τ²) ≥ 2c₀ ≥ c_q(1 − cos)`.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- The first Gauss term bounds the vertical growth of digamma:
`Re ψ(a + iy) − ψ(a) ≥ y²/(a(a² + y²))` for `a > 0`. -/
theorem re_digamma_add_mul_I_sub_ge {a : ℝ} (ha : 0 < a) (y : ℝ) :
    y ^ 2 / (a * (a ^ 2 + y ^ 2)) ≤
      (Complex.digamma ((a : ℂ) + (y : ℂ) * Complex.I)).re - (Complex.digamma ((a : ℂ))).re := by
  have hreR : ((a : ℂ)).re = a := Complex.ofReal_re a
  have hreC : ((a : ℂ) + (y : ℂ) * Complex.I).re = a := by
    simp [Complex.add_re, Complex.mul_re]
  have hsR := digamma_eq_neg_euler_add_tsum_gauss (s := (a : ℂ)) (by rw [hreR]; exact ha)
  have hsC := digamma_eq_neg_euler_add_tsum_gauss
    (s := (a : ℂ) + (y : ℂ) * Complex.I) (by rw [hreC]; exact ha)
  have hsumR : Summable (fun n : ℕ => gaussDigammaSeriesTerm ((a : ℂ)) n) :=
    summable_norm_iff.mp
      (GaloisForLFunctions.HTGeometry.summable_norm_gaussDigammaSeriesTerm_all _)
  have hsumC : Summable (fun n : ℕ => gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n) :=
    summable_norm_iff.mp
      (GaloisForLFunctions.HTGeometry.summable_norm_gaussDigammaSeriesTerm_all _)
  have hR' := (Complex.hasSum_re hsumR.hasSum).summable
  have hC' := (Complex.hasSum_re hsumC.hasSum).summable
  rw [hsR, hsC, Complex.add_re, Complex.add_re, Complex.re_tsum hsumR, Complex.re_tsum hsumC]
  set d : ℕ → ℝ := fun n => (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n).re -
    (gaussDigammaSeriesTerm ((a : ℂ)) n).re with hd
  have hdsum : Summable d := hC'.sub hR'
  have hdnn : ∀ n, 0 ≤ d n := fun n => sub_nonneg.mpr (re_gaussDigammaSeriesTerm_real_le ha y n)
  have hd0 : d 0 = y ^ 2 / (a * (a ^ 2 + y ^ 2)) := by
    simp only [hd, gaussDigammaSeriesTerm, Nat.cast_zero, add_zero, zero_add, Complex.sub_re]
    have hC0 : (1 / ((a : ℂ) + (y : ℂ) * Complex.I)).re = a / (a ^ 2 + y ^ 2) := by
      rw [one_div, Complex.inv_re, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring_nf
    have hR0 : (1 / (a : ℂ)).re = 1 / a := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [hC0, hR0]
    have ha2 : 0 < a ^ 2 + y ^ 2 := by positivity
    field_simp
    ring
  have hle : d 0 ≤ ∑' n, d n := hdsum.le_tsum 0 fun n _ => hdnn n
  have htsub : ∑' n, d n =
      ∑' n : ℕ, (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n).re -
        ∑' n : ℕ, (gaussDigammaSeriesTerm ((a : ℂ)) n).re := hC'.tsum_sub hR'
  rw [hd0] at hle
  linarith

/-- The odd deficit `c_q = −(ψ(¾) − log π + log q)`. -/
def oddDeficit (q : ℝ) : ℝ := -((Complex.digamma ((3 / 4 : ℝ) : ℂ)).re - Real.log π + Real.log q)

theorem oddDeficit_eq (q : ℝ) :
    oddDeficit q = Real.eulerMascheroniConstant + 3 * Real.log 2 - π / 2 + Real.log π -
      Real.log q := by
  have h34 : (Complex.digamma (((3 / 4 : ℝ) : ℂ))).re =
      -Real.eulerMascheroniConstant - 3 * Real.log 2 + π / 2 := by
    rw [show (((3 / 4 : ℝ) : ℂ)) = (3 / 4 : ℂ) by push_cast; ring, re_digamma_three_quarters_eq,
      re_digamma_one_quarter]
    ring
  rw [oddDeficit, h34]
  ring

/-- The weight `−c_q √m / 2` at the node `m`, zero elsewhere. -/
def oddSingleNodeWeight (q : ℝ) (m : ℕ) (n : ℕ) : ℝ :=
  if n = m then -(oddDeficit q) * Real.sqrt m / 2 else 0

/-- The weighted symbol is the odd symbol plus `c_q cos(τ log m)`. -/
theorem weilAtomSymbol_oddSingleNodeWeight {q : ℝ} {m : ℕ} (hm : 2 ≤ m) (τ : ℝ) :
    weilAtomSymbol (oddSingleNodeWeight q m) m (τ / (2 * π)) + Real.log q +
        π / Real.cosh (π * τ) =
      (Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)).re - Real.log π +
        Real.log q + oddDeficit q * Real.cos (τ * Real.log m) := by
  have hsum : ∑ n ∈ Finset.Icc 2 m, oddSingleNodeWeight q m n * (1 / Real.sqrt n) *
      (2 * Real.cos (2 * π * Real.log n * (τ / (2 * π)))) =
      -(oddDeficit q) * Real.cos (τ * Real.log m) := by
    rw [Finset.sum_eq_single m]
    · have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < m))
      simp only [oddSingleNodeWeight, if_true]
      rw [show 2 * π * Real.log m * (τ / (2 * π)) = τ * Real.log m by field_simp]
      field_simp
    · intro n _ hn
      simp [oddSingleNodeWeight, hn]
    · intro h
      exact absurd (Finset.mem_Icc.mpr ⟨hm, le_rfl⟩) h
  rw [weilAtomSymbol, hsum, ← archimedeanWeilSymbol_add_sech τ]
  ring

/-- **The single-node weighted odd symbol is nonnegative**, given admissible constants. -/
theorem oddDirichletSingleNodeSymbol_nonneg_of_bounds {q c₀ B T₀ : ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hc : oddDeficit q ≤ c₀) (hB : Real.log m ^ 2 ≤ B) (hT₀ : 0 ≤ T₀)
    (hT : 16 * T₀ = 2 * c₀ * (27 + 12 * T₀)) (hadm : c₀ * B * (27 + 12 * T₀) ≤ 32) (τ : ℝ) :
    0 ≤ weilAtomSymbol (oddSingleNodeWeight q m) m (τ / (2 * π)) + Real.log q +
      π / Real.cosh (π * τ) := by
  rw [weilAtomSymbol_oddSingleNodeWeight hm τ]
  set c := oddDeficit q with hc_def
  set x := τ * Real.log m with hx
  have hgrow := re_digamma_add_mul_I_sub_ge (a := 3 / 4) (by norm_num) (τ / 2)
  have hS0 : (Complex.digamma (((3 / 4 : ℝ) : ℂ))).re - Real.log π + Real.log q = -c := by
    rw [hc_def, oddDeficit]; ring
  have hg : (τ / 2) ^ 2 / (3 / 4 * ((3 / 4) ^ 2 + (τ / 2) ^ 2)) =
      16 * τ ^ 2 / (27 + 12 * τ ^ 2) := by
    field_simp
    ring
  rw [hg] at hgrow
  have hcos1 : Real.cos x ≤ 1 := Real.cos_le_one x
  rcases le_or_gt c 0 with hc0 | hc0
  · have h1 : 0 ≤ 16 * τ ^ 2 / (27 + 12 * τ ^ 2) := by positivity
    nlinarith
  · have hc0' : c ≤ c₀ := hc
    have hcos2 : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
    have hcosm : -1 ≤ Real.cos x := Real.neg_one_le_cos x
    have hden : 0 < 27 + 12 * τ ^ 2 := by positivity
    have hgoal : c * (1 - Real.cos x) ≤ 16 * τ ^ 2 / (27 + 12 * τ ^ 2) := by
      rcases le_or_gt (τ ^ 2) T₀ with hτ | hτ
      · have hx2 : x ^ 2 ≤ τ ^ 2 * B := by
          rw [hx, mul_pow]
          exact mul_le_mul_of_nonneg_left hB (sq_nonneg τ)
        have h1 : c * (1 - Real.cos x) ≤ c₀ * (τ ^ 2 * B / 2) := by
          have : 1 - Real.cos x ≤ τ ^ 2 * B / 2 := by linarith
          calc c * (1 - Real.cos x) ≤ c * (τ ^ 2 * B / 2) :=
                mul_le_mul_of_nonneg_left this hc0.le
            _ ≤ c₀ * (τ ^ 2 * B / 2) :=
                mul_le_mul_of_nonneg_right hc0' (by nlinarith [sq_nonneg τ, sq_nonneg (Real.log m)])
        have h2 : c₀ * (τ ^ 2 * B / 2) ≤ 16 * τ ^ 2 / (27 + 12 * τ ^ 2) := by
          rw [le_div_iff₀ hden]
          have hB0 : 0 ≤ B := le_trans (sq_nonneg _) hB
          have hc00 : 0 ≤ c₀ := le_trans hc0.le hc0'
          have : c₀ * B * (27 + 12 * τ ^ 2) ≤ 32 := by
            calc c₀ * B * (27 + 12 * τ ^ 2) ≤ c₀ * B * (27 + 12 * T₀) := by
                  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc00 hB0); linarith
              _ ≤ 32 := hadm
          nlinarith [sq_nonneg τ]
        linarith
      · have h1 : c * (1 - Real.cos x) ≤ 2 * c₀ := by nlinarith
        have h2 : 2 * c₀ ≤ 16 * τ ^ 2 / (27 + 12 * τ ^ 2) := by
          rw [le_div_iff₀ hden]
          nlinarith
        linarith
    nlinarith

theorem log_three_le : Real.log 3 ≤ (3 * Real.log 2 + 1 / 8) / 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 / 8 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
    show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

theorem log_pi_le : Real.log π ≤ (3 * Real.log 2 + 1 / 8) / 2 + (π / 3 - 1) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < π / 3 by positivity)
  rw [Real.log_div Real.pi_pos.ne' (by norm_num)] at h
  linarith [log_three_le]

theorem log_seven_ge : 3 * Real.log 2 - 1 / 7 ≤ Real.log 7 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 / 7 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num,
    Real.log_pow] at h
  push_cast at h
  linarith

/-- **Node `2` for every odd conductor `q ≥ 7`.** -/
theorem oddDirichletSingleNodeSymbol_nonneg_two {q : ℝ} (hq : 7 ≤ q) (τ : ℝ) :
    0 ≤ weilAtomSymbol (oddSingleNodeWeight q 2) 2 (τ / (2 * π)) + Real.log q +
      π / Real.cosh (π * τ) := by
  have hlogq : Real.log 7 ≤ Real.log q := Real.log_le_log (by norm_num) hq
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hπ := Real.pi_gt_d4
  have hπ' := Real.pi_lt_d4
  have hc : oddDeficit q ≤ 1 / 2 := by
    rw [oddDeficit_eq]
    linarith [log_pi_le, log_seven_ge]
  refine oddDirichletSingleNodeSymbol_nonneg_of_bounds (c₀ := 1 / 2) (B := 1 / 2) (T₀ := 27 / 4)
    (by norm_num) hc ?_ (by norm_num) (by norm_num) (by norm_num) τ
  push_cast
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- **Node `3` for conductor `8`.** -/
theorem oddDirichletSingleNodeSymbol_nonneg_eight_three (τ : ℝ) :
    0 ≤ weilAtomSymbol (oddSingleNodeWeight 8 3) 3 (τ / (2 * π)) + Real.log 8 +
      π / Real.cosh (π * τ) := by
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hl2 := Real.log_two_lt_d9
  have hπ := Real.pi_gt_d4
  have hπ' := Real.pi_lt_d4
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  have hc : oddDeficit 8 ≤ 1 / 3 := by
    rw [oddDeficit_eq, h8]
    linarith [log_pi_le]
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  refine oddDirichletSingleNodeSymbol_nonneg_of_bounds (c₀ := 1 / 3) (B := 5 / 4) (T₀ := 9 / 4)
    (by norm_num) hc ?_ (by norm_num) (by norm_num) (by norm_num) τ
  push_cast
  nlinarith [log_three_le]

/-- **The single-node odd Weil forms are nonnegative on every test.** -/
theorem integral_oddDirichletSingleNode_nonneg {q : ℝ} (hq : 7 ≤ q) (f : ℝ → ℂ) :
    0 ≤ ∫ τ : ℝ, ‖Zeta23.paperFT f τ‖ ^ 2 *
      (weilAtomSymbol (oddSingleNodeWeight q 2) 2 (τ / (2 * π)) + Real.log q +
        π / Real.cosh (π * τ)) :=
  MeasureTheory.integral_nonneg fun τ =>
    mul_nonneg (by positivity) (oddDirichletSingleNodeSymbol_nonneg_two hq τ)

end

end RHTower
