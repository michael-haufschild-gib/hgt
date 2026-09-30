import GaloisForLFunctions.RHTower.SelbergNearLineTailLength
import GaloisForLFunctions.RHTower.SelbergNearLineZeroDensity

/-!
# Exponential zero density at the critical scale

There are absolute constants `A, K > 0` such that for all large `U`, with `L = log U`, admissible
heights `T₁ ∈ (U/4, U/4 + 1)` and `T₂ ∈ (U/2 − 1, U/2)` exist with

`2π (a/L) · #{ρ : ζ(ρ) = 0, Re ρ ≥ 1/2 + 2a/L, T₁ ≤ Im ρ ≤ T₂} ≤ (T₂ − T₁) A e^{−a/1200} + K L`

for every `1 ≤ a ≤ (L − 2)/2` simultaneously (`exists_selberg_exponential_nearLine_zeroDensity`),
zeros counted with multiplicity. The proportion of zeros at distance `2a/L` right of the line decays
exponentially in `a`, uniformly in `U`.

The mollifier combines two Barban–Vehov lengths `Y < X`:
`M = (log X · Ψ_X − log Y · Ψ_Y)/log(X/Y)`, with coefficients `μ(n)` for `n ≤ Y` and
`μ(n) log(X/n)/log(X/Y)` for `Y < n ≤ X` (`twoLengthCoeff`). Since `log Z · (ζΨ_Z − 1 − f_Z)` is the
von Mangoldt polynomial `Σ_{n ≤ Z} Λ(n) n^{−s}`, the heads cancel below `Y`:

`ζM = 1 + H + g`, `H = Σ_{Y < n ≤ X} Λ(n)/log(X/Y) · n^{−s}`,
`g = (log X · f_X − log Y · f_Y)/log(X/Y)` (`zeta_mul_twoLength_eq`).

With `X = ⌊U^{1/100}⌋`, `Y = ⌊U^{1/200}⌋` the mean-value theorem gives `∫|H|² ≪ T e^{−a/100}`
(every frequency exceeds `Y`), and the three-lines tail estimate for both lengths gives
`∫|g|² ≪ T e^{−a/600}`. Littlewood's lemma for the mollified detector converts the mean square
`T(1 + O(e^{−a/1200}))` into the count.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-! ## The two-length mollifier -/

/-- Two-length Barban–Vehov coefficients `(b_X(n) − b_Y(n))/(log X − log Y)`,
`b_Z(n) = μ(n) log(Z/n)` for `n ≤ Z`. -/
def twoLengthCoeff (X Y n : ℕ) : ℂ :=
  (((Sieve.barbanVehovWeight X n - Sieve.barbanVehovWeight Y n) /
    (Real.log X - Real.log Y) : ℝ) : ℂ)

/-- Head coefficients of the two-length mollified zeta function: `Λ(n)/(log X − log Y)` for
`n > Y`. -/
def twoLengthHeadCoeff (X Y n : ℕ) : ℂ :=
  ((if Y < n then ArithmeticFunction.vonMangoldt n / (Real.log X - Real.log Y) else 0 : ℝ) : ℂ)

theorem twoLength_log_gap_pos {X Y : ℕ} (hY : 1 ≤ Y) (hYX : Y < X) :
    0 < Real.log X - Real.log Y := by
  have : Real.log Y < Real.log X :=
    Real.log_lt_log (by exact_mod_cast hY) (by exact_mod_cast hYX)
  linarith

theorem twoLengthCoeff_one {X Y : ℕ} (hY : 1 ≤ Y) (hYX : Y < X) : twoLengthCoeff X Y 1 = 1 := by
  have hgap := twoLength_log_gap_pos hY hYX
  unfold twoLengthCoeff Sieve.barbanVehovWeight
  rw [if_pos (by omega), if_pos hY, ArithmeticFunction.moebius_apply_one]
  simp only [Int.cast_one, one_mul, Nat.cast_one, div_one]
  rw [div_self hgap.ne', Complex.ofReal_one]

theorem norm_twoLengthCoeff_le {X Y n : ℕ} (hY : 1 ≤ Y) (hYX : Y < X)
    (hn : n ∈ Finset.Icc 1 X) : ‖twoLengthCoeff X Y n‖ ≤ 1 := by
  obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hn
  have hgap := twoLength_log_gap_pos hY hYX
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  set m : ℝ := ((ArithmeticFunction.moebius n : ℤ) : ℝ) with hm
  have hμ : |m| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := n)
    rw [hm]
    exact_mod_cast this
  unfold twoLengthCoeff Sieve.barbanVehovWeight
  rw [if_pos hnX, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hgap, div_le_one hgap]
  by_cases hnY : n ≤ Y
  · rw [if_pos hnY]
    have e : m * Real.log ((X : ℝ) / n) - m * Real.log ((Y : ℝ) / n) =
        m * (Real.log X - Real.log Y) := by
      rw [Real.log_div hX0.ne' hn0.ne', Real.log_div hY0.ne' hn0.ne']
      ring
    rw [← hm, e, abs_mul, abs_of_pos hgap]
    calc |m| * (Real.log X - Real.log Y) ≤ 1 * (Real.log X - Real.log Y) :=
          mul_le_mul_of_nonneg_right hμ hgap.le
      _ = Real.log X - Real.log Y := one_mul _
  · rw [if_neg hnY, sub_zero, ← hm, abs_mul]
    have hYn : (Y : ℝ) < n := by exact_mod_cast (not_le.mp hnY)
    have hnX' : (n : ℝ) ≤ X := by exact_mod_cast hnX
    have hlog0 : 0 ≤ Real.log ((X : ℝ) / n) := Real.log_nonneg (by rw [le_div_iff₀ hn0]; linarith)
    have hlogle : Real.log ((X : ℝ) / n) ≤ Real.log X - Real.log Y := by
      rw [Real.log_div hX0.ne' hn0.ne']
      linarith [Real.log_lt_log hY0 hYn]
    rw [abs_of_nonneg hlog0]
    calc |m| * Real.log ((X : ℝ) / n) ≤ 1 * (Real.log X - Real.log Y) :=
          mul_le_mul hμ hlogle hlog0 zero_le_one
      _ = Real.log X - Real.log Y := one_mul _

theorem conj_twoLengthCoeff (X Y n : ℕ) :
    (starRingEnd ℂ) (twoLengthCoeff X Y n) = twoLengthCoeff X Y n :=
  Complex.conj_ofReal _

theorem sum_norm_twoLengthCoeff_mul_rpow_le {X Y : ℕ} (hY : 1 ≤ Y) (hYX : Y < X) :
    (∑ n ∈ Finset.Icc 1 X, ‖twoLengthCoeff X Y n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ (X : ℝ) ^ (5 : ℕ) := by
  have hterm : ∀ n ∈ Finset.Icc 1 X,
      ‖twoLengthCoeff X Y n‖ * ((n : ℝ) ^ (4 : ℝ)) ≤ (X : ℝ) ^ (4 : ℕ) := by
    intro n hn
    have hnX : (n : ℝ) ≤ X := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc ‖twoLengthCoeff X Y n‖ * ((n : ℝ) ^ (4 : ℝ)) ≤ 1 * ((X : ℝ) ^ (4 : ℝ)) :=
          mul_le_mul (norm_twoLengthCoeff_le hY hYX hn)
            (Real.rpow_le_rpow hn0 hnX (by norm_num)) (by positivity) zero_le_one
      _ = (X : ℝ) ^ (4 : ℕ) := by rw [one_mul, Real.rpow_ofNat]
  calc (∑ n ∈ Finset.Icc 1 X, ‖twoLengthCoeff X Y n‖ * ((n : ℝ) ^ (4 : ℝ)))
      ≤ ∑ _n ∈ Finset.Icc 1 X, (X : ℝ) ^ (4 : ℕ) := Finset.sum_le_sum hterm
    _ = (X : ℝ) * (X : ℝ) ^ (4 : ℕ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp
    _ = (X : ℝ) ^ (5 : ℕ) := by ring

theorem ofReal_log_mul_hbCoeff {Z : ℕ} (hZ : 2 ≤ Z) (n : ℕ) :
    ((Real.log Z : ℝ) : ℂ) * hbCoeff Z n = ((Sieve.barbanVehovWeight Z n : ℝ) : ℂ) := by
  have hlog : Real.log Z ≠ 0 := (Real.log_pos (by exact_mod_cast hZ)).ne'
  unfold hbCoeff
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp

theorem ofReal_log_mul_hbVonMangoldtCoeff {Z : ℕ} (hZ : 2 ≤ Z) (n : ℕ) :
    ((Real.log Z : ℝ) : ℂ) * hbVonMangoldtCoeff Z n =
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) := by
  have hlog : Real.log Z ≠ 0 := (Real.log_pos (by exact_mod_cast hZ)).ne'
  unfold hbVonMangoldtCoeff
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp

/-- **The two-length mollifier** is `(log X · Ψ_X − log Y · Ψ_Y)/(log X − log Y)`. -/
theorem edPoly_twoLengthCoeff {X Y : ℕ} (hY : 2 ≤ Y) (hYX : Y < X) (z : ℂ) :
    edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) z =
      (((Real.log X : ℝ) : ℂ) * edPoly (hbCoeff X) (Finset.Icc 1 X) z -
        ((Real.log Y : ℝ) : ℂ) * edPoly (hbCoeff Y) (Finset.Icc 1 Y) z) /
          ((Real.log X - Real.log Y : ℝ) : ℂ) := by
  have hgap := twoLength_log_gap_pos (by omega) hYX
  have hne : ((Real.log X - Real.log Y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hgap.ne'
  have hext : edPoly (hbCoeff Y) (Finset.Icc 1 Y) z = edPoly (hbCoeff Y) (Finset.Icc 1 X) z := by
    unfold edPoly
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hYX.le) ?_
    intro n hnX hnY
    have : Y < n := by
      simp only [Finset.mem_Icc] at hnX hnY
      omega
    rw [hbCoeff_eq_zero_of_lt this, zero_mul]
  rw [hext, eq_div_iff hne]
  unfold edPoly
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hc : twoLengthCoeff X Y n * ((Real.log X - Real.log Y : ℝ) : ℂ) =
      ((Real.log X : ℝ) : ℂ) * hbCoeff X n - ((Real.log Y : ℝ) : ℂ) * hbCoeff Y n := by
    rw [ofReal_log_mul_hbCoeff (by omega) n, ofReal_log_mul_hbCoeff hY n]
    unfold twoLengthCoeff
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hgap.ne']
    push_cast
    ring
  calc twoLengthCoeff X Y n * ((n : ℝ) : ℂ) ^ (-z) * ((Real.log X - Real.log Y : ℝ) : ℂ)
      = (twoLengthCoeff X Y n * ((Real.log X - Real.log Y : ℝ) : ℂ)) * ((n : ℝ) : ℂ) ^ (-z) := by
        ring
    _ = _ := by rw [hc]; ring

/-- **The two-length head** is `(log X · P_X − log Y · P_Y)/(log X − log Y)`. -/
theorem edPoly_twoLengthHeadCoeff {X Y : ℕ} (hY : 2 ≤ Y) (hYX : Y < X) (z : ℂ) :
    edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X) z =
      (((Real.log X : ℝ) : ℂ) * edPoly (hbVonMangoldtCoeff X) (Finset.Icc 1 X) z -
        ((Real.log Y : ℝ) : ℂ) * edPoly (hbVonMangoldtCoeff Y) (Finset.Icc 1 Y) z) /
          ((Real.log X - Real.log Y : ℝ) : ℂ) := by
  have hgap := twoLength_log_gap_pos (by omega) hYX
  have hne : ((Real.log X - Real.log Y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hgap.ne'
  have hext : edPoly (hbVonMangoldtCoeff Y) (Finset.Icc 1 Y) z =
      ∑ n ∈ Finset.Icc 1 X,
        (if n ≤ Y then hbVonMangoldtCoeff Y n else 0) * ((n : ℝ) : ℂ) ^ (-z) := by
    unfold edPoly
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hYX.le)
      (f := fun n => (if n ≤ Y then hbVonMangoldtCoeff Y n else 0) * ((n : ℝ) : ℂ) ^ (-z)) ?_]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [if_pos (Finset.mem_Icc.mp hn).2]
    · intro n hnX hnY
      have : ¬ n ≤ Y := by
        simp only [Finset.mem_Icc] at hnX hnY
        omega
      rw [if_neg this, zero_mul]
  rw [hext, eq_div_iff hne]
  unfold edPoly
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hc : twoLengthHeadCoeff X Y n * ((Real.log X - Real.log Y : ℝ) : ℂ) =
      ((Real.log X : ℝ) : ℂ) * hbVonMangoldtCoeff X n -
        ((Real.log Y : ℝ) : ℂ) * (if n ≤ Y then hbVonMangoldtCoeff Y n else 0) := by
    rw [ofReal_log_mul_hbVonMangoldtCoeff (by omega) n]
    unfold twoLengthHeadCoeff
    by_cases hnY : n ≤ Y
    · rw [if_neg (by omega), if_pos hnY, ofReal_log_mul_hbVonMangoldtCoeff hY n]
      simp
    · rw [if_pos (by omega), if_neg hnY, ← Complex.ofReal_mul, div_mul_cancel₀ _ hgap.ne']
      simp
  calc twoLengthHeadCoeff X Y n * ((n : ℝ) : ℂ) ^ (-z) * ((Real.log X - Real.log Y : ℝ) : ℂ)
      = (twoLengthHeadCoeff X Y n * ((Real.log X - Real.log Y : ℝ) : ℂ)) *
          ((n : ℝ) : ℂ) ^ (-z) := by ring
    _ = _ := by rw [hc]; ring

/-- **The two-length mollified zeta function**: `ζM = 1 + H + (log X · f_X − log Y · f_Y)/log(X/Y)`,
with `f_Z = ζΨ_Z − 1 − P_Z` the Barban–Vehov tails. -/
theorem zeta_mul_twoLength_eq {X Y : ℕ} (hY : 2 ≤ Y) (hYX : Y < X) (z : ℂ) :
    riemannZeta z * edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) z =
      1 + (edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X) z +
        (((Real.log X : ℝ) : ℂ) * hbMollifiedTail X z -
          ((Real.log Y : ℝ) : ℂ) * hbMollifiedTail Y z) /
            ((Real.log X - Real.log Y : ℝ) : ℂ)) := by
  have hgap := twoLength_log_gap_pos (by omega) hYX
  have hne : ((Real.log X : ℝ) : ℂ) - ((Real.log Y : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact_mod_cast hgap.ne'
  rw [edPoly_twoLengthCoeff hY hYX, edPoly_twoLengthHeadCoeff hY hYX, Complex.ofReal_sub]
  unfold hbMollifiedTail
  set lX : ℂ := ((Real.log X : ℝ) : ℂ)
  set lY : ℂ := ((Real.log Y : ℝ) : ℂ)
  field_simp
  ring

/-! ## Mean squares on the right-shifted line -/

/-- The head has every frequency beyond `Y`: its mean square on `Re s = 1/2 + δ` carries `Y^{−2δ}`. -/
theorem integral_normSq_twoLengthHead_le {X Y : ℕ} (hY : 1 ≤ Y) (hYX : Y < X) {δ CM : ℝ}
    (hδ : 0 ≤ δ)
    (hCM : ∑ k ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log X * (Real.log X + CM)) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    (∫ τ in T₁..T₂,
        ‖edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X) (displacedLinePt (-δ) τ)‖ ^ 2) ≤
      (T₂ - T₁ + 8 * X * (1 + Real.log X)) *
        ((Y : ℝ) ^ (-(2 * δ)) * (Real.log X * (Real.log X + CM)) /
          (Real.log X - Real.log Y) ^ 2) := by
  have hgap := twoLength_log_gap_pos hY hYX
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  refine (integral_normSq_edPoly_displaced_le (-δ) _ X T₁ T₂).trans ?_
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hfac : 0 ≤ T₂ - T₁ + 8 * X * (1 + Real.log X) := by
    have := Real.log_nonneg hX1
    nlinarith
  refine mul_le_mul_of_nonneg_left ?_ hfac
  set c : ℝ := (Y : ℝ) ^ (-(2 * δ)) / (Real.log X - Real.log Y) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hterm : ∀ n ∈ Finset.Icc 1 X,
      ‖twoLengthHeadCoeff X Y n‖ ^ 2 * (n : ℝ) ^ (2 * -δ - 1) ≤
        c * (ArithmeticFunction.vonMangoldt n ^ (2 : ℕ) / (n : ℝ)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    unfold twoLengthHeadCoeff
    by_cases hYn : Y < n
    · rw [if_pos hYn, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
      have hYn' : (Y : ℝ) ≤ n := by exact_mod_cast hYn.le
      have hpow : (n : ℝ) ^ (2 * -δ - 1) = (n : ℝ) ^ (-(2 * δ)) / n := by
        rw [Real.rpow_sub hn0, Real.rpow_one]
        ring_nf
      have hmono : (n : ℝ) ^ (-(2 * δ)) ≤ (Y : ℝ) ^ (-(2 * δ)) :=
        Real.rpow_le_rpow_of_nonpos hY0 hYn' (by linarith)
      rw [hpow, hc]
      have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n ^ 2 := by positivity
      calc ArithmeticFunction.vonMangoldt n ^ 2 / (Real.log X - Real.log Y) ^ 2 *
            ((n : ℝ) ^ (-(2 * δ)) / n)
          ≤ ArithmeticFunction.vonMangoldt n ^ 2 / (Real.log X - Real.log Y) ^ 2 *
            ((Y : ℝ) ^ (-(2 * δ)) / n) := by gcongr
        _ = (Y : ℝ) ^ (-(2 * δ)) / (Real.log X - Real.log Y) ^ 2 *
            (ArithmeticFunction.vonMangoldt n ^ (2 : ℕ) / (n : ℝ)) := by ring
    · rw [if_neg hYn]
      simp only [Complex.ofReal_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_mul]
      positivity
  calc ∑ n ∈ Finset.Icc 1 X, ‖twoLengthHeadCoeff X Y n‖ ^ 2 * (n : ℝ) ^ (2 * -δ - 1)
      ≤ ∑ n ∈ Finset.Icc 1 X, c * (ArithmeticFunction.vonMangoldt n ^ (2 : ℕ) / (n : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = c * ∑ n ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt n ^ (2 : ℕ) / (n : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ c * (Real.log X * (Real.log X + CM)) := mul_le_mul_of_nonneg_left hCM hc0
    _ = (Y : ℝ) ^ (-(2 * δ)) * (Real.log X * (Real.log X + CM)) /
          (Real.log X - Real.log Y) ^ 2 := by rw [hc]; ring

/-- Size facts for the two lengths `X ≈ e^{L/100}`, `Y ≈ e^{L/200}`. -/
theorem twoLength_scale_facts {X Y : ℕ} {L : ℝ} (hL : 1000 ≤ L)
    (hXle : (X : ℝ) ≤ Real.exp (L / 100)) (hXgt : Real.exp (L / 100) - 1 < X)
    (hYle : (Y : ℝ) ≤ Real.exp (L / 200)) (hYgt : Real.exp (L / 200) - 1 < Y) :
    2 ≤ Y ∧ Y < X ∧ Real.exp (L / 200) / 2 ≤ Y ∧ Real.exp (L / 200) / 2 ≤ X ∧
      Real.log X ≤ L / 100 ∧ 0 ≤ Real.log Y ∧ Real.log Y ≤ L / 200 ∧
      L / 400 ≤ Real.log X - Real.log Y := by
  have he5 := hundred_le_exp_five
  have hE5 : Real.exp 5 ≤ Real.exp (L / 200) := Real.exp_le_exp.mpr (by linarith)
  have hsq : Real.exp (L / 100) = Real.exp (L / 200) * Real.exp (L / 200) := by
    rw [← Real.exp_add]; ring_nf
  have hXbig : 100 * Real.exp (L / 200) ≤ Real.exp (L / 100) := by
    rw [hsq]; nlinarith [Real.exp_pos (L / 200)]
  have hY2 : (2 : ℝ) ≤ Y := by linarith
  have hYX : (Y : ℝ) < X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hXhalf : Real.exp (L / 100) / 2 ≤ X := by linarith
  refine ⟨by exact_mod_cast hY2, by exact_mod_cast hYX, by linarith, by linarith, ?_,
    Real.log_nonneg (by linarith), ?_, ?_⟩
  · have := Real.log_le_log hX0 hXle
    rwa [Real.log_exp] at this
  · have := Real.log_le_log hY0 hYle
    rwa [Real.log_exp] at this
  · have h1 := Real.log_le_log (by positivity) hXhalf
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h1
    have h2 : Real.log Y ≤ L / 200 := by
      have := Real.log_le_log hY0 hYle
      rwa [Real.log_exp] at this
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith

/-- `Y^{−2a/L} ≤ 2e^{−a/100}` for `Y ≥ e^{L/200}/2` and `2a ≤ L`. -/
theorem rpow_neg_twoLength_le {Y : ℕ} {L a : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (haL : 2 * a ≤ L)
    (hY : Real.exp (L / 200) / 2 ≤ Y) :
    (Y : ℝ) ^ (-(2 * (a / L))) ≤ 2 * Real.exp (-(a / 100)) := by
  have hb0 : 0 < Real.exp (L / 200) / 2 := by positivity
  have hstep : (Y : ℝ) ^ (-(2 * (a / L))) ≤ (Real.exp (L / 200) / 2) ^ (-(2 * (a / L))) :=
    Real.rpow_le_rpow_of_nonpos hb0 hY (by have h0 : 0 ≤ a / L := div_nonneg ha hL.le; linarith)
  refine hstep.trans ?_
  rw [Real.rpow_def_of_pos hb0, Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have haL' : a / L ≤ 1 / 2 := by rw [div_le_iff₀ hL]; linarith
  have hexp : (L / 200 - Real.log 2) * -(2 * (a / L)) ≤ -(a / 100) + Real.log 2 := by
    have e : (L / 200) * (2 * (a / L)) = a / 100 := by field_simp; ring
    have h1 : Real.log 2 * (2 * (a / L)) ≤ Real.log 2 := by
      have : 2 * (a / L) ≤ 1 := by linarith
      nlinarith
    nlinarith
  calc Real.exp ((L / 200 - Real.log 2) * -(2 * (a / L)))
      ≤ Real.exp (-(a / 100) + Real.log 2) := Real.exp_le_exp.mpr hexp
    _ = 2 * Real.exp (-(a / 100)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]; ring

/-- **The head mean square at the scale `U = e^L`**: `∫|H|² ≤ 128 (T₂ − T₁) e^{−a/100}`. -/
theorem integral_normSq_twoLengthHead_rightShift_le {X Y : ℕ} {L a CM T₁ T₂ : ℝ}
    (hL : 1000 ≤ L) (hLCM : 100 * |CM| ≤ L)
    (hXle : (X : ℝ) ≤ Real.exp (L / 100)) (hXgt : Real.exp (L / 100) - 1 < X)
    (hYle : (Y : ℝ) ≤ Real.exp (L / 200)) (hYgt : Real.exp (L / 200) - 1 < Y)
    (hCM : ∑ k ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log X * (Real.log X + CM))
    (ha : 0 ≤ a) (haL : 2 * a ≤ L) (hT : T₁ ≤ T₂) (hlen : Real.exp (99 / 100 * L) ≤ T₂ - T₁) :
    ∫ τ in T₁..T₂, ‖edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X)
        (((1 / 2 + a / L : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤
      (T₂ - T₁) * (128 * Real.exp (-(a / 100))) := by
  obtain ⟨hY2, hYX, hYhalf, -, hlogX, hlogY0, hlogY, hgap⟩ :=
    twoLength_scale_facts hL hXle hXgt hYle hYgt
  obtain ⟨-, -, hMVT, -⟩ := nearLine_length_facts (by linarith) hXle hXgt
  have hL0 : 0 < L := by linarith
  have hpt : ∀ τ : ℝ, displacedLinePt (-(a / L)) τ = ((1 / 2 + a / L : ℝ) : ℂ) + (τ : ℂ) * I := by
    intro τ
    unfold displacedLinePt
    congr 2
    ring
  have h := integral_normSq_twoLengthHead_le (by omega) hYX (δ := a / L) (by positivity) hCM hT
  simp only [hpt] at h
  refine h.trans ?_
  have h1 : T₂ - T₁ + 8 * X * (1 + Real.log X) ≤ 2 * (T₂ - T₁) := by linarith
  have hYp := rpow_neg_twoLength_le hL0 ha haL hYhalf
  have hgap0 : 0 < Real.log X - Real.log Y := by linarith
  have hlogX0 : 0 ≤ Real.log X := by linarith
  have hprod : Real.log X * (Real.log X + CM) ≤ (L / 100) * (2 * (L / 100)) := by
    have hCMa : CM ≤ L / 100 := by
      have := le_abs_self CM
      linarith
    rcases le_or_gt (Real.log X + CM) 0 with hneg | hpos
    · have : Real.log X * (Real.log X + CM) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlogX0 hneg
      nlinarith
    · exact mul_le_mul hlogX (by linarith) hpos.le (by positivity)
  have h2 : (Y : ℝ) ^ (-(2 * (a / L))) * (Real.log X * (Real.log X + CM)) /
      (Real.log X - Real.log Y) ^ 2 ≤ 64 * Real.exp (-(a / 100)) := by
    rw [div_le_iff₀ (by positivity)]
    have hsq : (L / 400) ^ 2 ≤ (Real.log X - Real.log Y) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hgap 2
    have hY0 : 0 ≤ (Y : ℝ) ^ (-(2 * (a / L))) := by positivity
    have hE0 : 0 ≤ Real.exp (-(a / 100)) := (Real.exp_pos _).le
    calc (Y : ℝ) ^ (-(2 * (a / L))) * (Real.log X * (Real.log X + CM))
        ≤ (2 * Real.exp (-(a / 100))) * ((L / 100) * (2 * (L / 100))) := by
          rcases le_or_gt (Real.log X * (Real.log X + CM)) 0 with hneg | hpos
          · have : (Y : ℝ) ^ (-(2 * (a / L))) * (Real.log X * (Real.log X + CM)) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos hY0 hneg
            have : 0 ≤ (2 * Real.exp (-(a / 100))) * ((L / 100) * (2 * (L / 100))) := by
              positivity
            linarith
          · exact mul_le_mul hYp hprod hpos.le (by positivity)
      _ = 64 * Real.exp (-(a / 100)) * (L / 400) ^ 2 := by ring
      _ ≤ 64 * Real.exp (-(a / 100)) * (Real.log X - Real.log Y) ^ 2 := by gcongr
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  calc (T₂ - T₁ + 8 * X * (1 + Real.log X)) *
        ((Y : ℝ) ^ (-(2 * (a / L))) * (Real.log X * (Real.log X + CM)) /
          (Real.log X - Real.log Y) ^ 2)
      ≤ (T₂ - T₁ + 8 * X * (1 + Real.log X)) * (64 * Real.exp (-(a / 100))) := by
        refine mul_le_mul_of_nonneg_left h2 ?_
        have := Real.log_nonneg hX1
        nlinarith
    _ ≤ (2 * (T₂ - T₁)) * (64 * Real.exp (-(a / 100))) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (T₂ - T₁) * (128 * Real.exp (-(a / 100))) := by ring

/-- Pointwise: `‖(p u − q v)/r‖² ≤ 32‖u‖² + 8‖v‖²` for `0 ≤ p ≤ 4r`, `0 ≤ q ≤ 2r`. -/
theorem normSq_twoLength_tail_le {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 < r)
    (hpr : p ≤ 4 * r) (hqr : q ≤ 2 * r) (u v : ℂ) :
    ‖((p : ℂ) * u - (q : ℂ) * v) / (r : ℂ)‖ ^ 2 ≤ 32 * ‖u‖ ^ 2 + 8 * ‖v‖ ^ 2 := by
  have hnorm : ‖((p : ℂ) * u - (q : ℂ) * v) / (r : ℂ)‖ ≤ 4 * ‖u‖ + 2 * ‖v‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_le_iff₀ hr]
    have h1 : ‖(p : ℂ) * u - (q : ℂ) * v‖ ≤ p * ‖u‖ + q * ‖v‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg hq]
    have h2 : p * ‖u‖ ≤ 4 * r * ‖u‖ := mul_le_mul_of_nonneg_right hpr (norm_nonneg _)
    have h3 : q * ‖v‖ ≤ 2 * r * ‖v‖ := mul_le_mul_of_nonneg_right hqr (norm_nonneg _)
    nlinarith
  have h0 : 0 ≤ ‖((p : ℂ) * u - (q : ℂ) * v) / (r : ℂ)‖ := norm_nonneg _
  have hsq := pow_le_pow_left₀ h0 hnorm 2
  nlinarith [sq_nonneg (2 * ‖u‖ - ‖v‖), norm_nonneg u, norm_nonneg v]

/-- Littlewood count from a mean square `Msq ≤ (T₂ − T₁)(1 + r)`. -/
theorem count_le_of_meanSquare_rate {L a r C K₀ T₁ T₂ Mb Msq count : ℝ}
    (hK₀ : 0 ≤ K₀) (hT12 : T₁ < T₂) (hT₂L : Real.log T₂ ≤ L) (hMb : Real.log Mb ≤ L)
    (hMsq0 : 0 < Msq) (hMsq : Msq ≤ (T₂ - T₁) * (1 + r))
    (hmain : 2 * Real.pi * (a / L * count) ≤
      (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁)) + C + K₀ * (Real.log T₂ + Real.log Mb)) :
    2 * Real.pi * (a / L * count) ≤ (T₂ - T₁) / 2 * r + (C + 2 * K₀ * L) := by
  refine hmain.trans ?_
  have hT0 : 0 < T₂ - T₁ := by linarith
  have hlog1 : Real.log (Msq / (T₂ - T₁)) ≤ r := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hMsq0 hT0)
    have h2 : Msq / (T₂ - T₁) ≤ 1 + r := by rw [div_le_iff₀ hT0]; linarith
    linarith
  have h1 : (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁)) ≤ (T₂ - T₁) / 2 * r :=
    mul_le_mul_of_nonneg_left hlog1 (by linarith)
  have h2 : K₀ * (Real.log T₂ + Real.log Mb) ≤ K₀ * (2 * L) :=
    mul_le_mul_of_nonneg_left (by linarith) hK₀
  linarith

/-- The rate `3√η + 2η`, `η = A₀ e^{−a/600}`, is at most `(3√A₀ + 2A₀) e^{−a/1200}`. -/
theorem twoLength_rate_le {A₀ a : ℝ} (hA₀ : 0 ≤ A₀) (ha : 0 ≤ a) :
    3 * Real.sqrt (A₀ * Real.exp (-(a / 600))) + 2 * (A₀ * Real.exp (-(a / 600))) ≤
      (3 * Real.sqrt A₀ + 2 * A₀) * Real.exp (-(a / 1200)) := by
  have hsq : Real.sqrt (A₀ * Real.exp (-(a / 600))) = Real.sqrt A₀ * Real.exp (-(a / 1200)) := by
    rw [Real.sqrt_mul hA₀, ← Real.exp_half]
    congr 2
    ring
  have he : A₀ * Real.exp (-(a / 600)) ≤ A₀ * Real.exp (-(a / 1200)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hA₀
  rw [hsq]
  nlinarith

/-- The final count at one scale, from the consumer inequality for the two-length mollifier. -/
theorem twoLength_final_count {L a C K₀ A₀ T₁ T₂ Mb count : ℝ} (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hK₀ : 0 ≤ K₀) (hA₀ : 0 ≤ A₀) (ha : 0 ≤ a) (hT12 : T₁ < T₂) (hlogT₂ : Real.log T₂ ≤ L)
    (hlogMb : Real.log Mb ≤ L)
    (hmain : 2 * Real.pi * (a / L * count) ≤
      (T₂ - T₁) / 2 * Real.log ((T₂ - T₁) * (1 + 3 * Real.sqrt (A₀ * Real.exp (-(a / 600))) +
        2 * (A₀ * Real.exp (-(a / 600)))) / (T₂ - T₁)) + C +
        K₀ * (Real.log T₂ + Real.log Mb)) :
    2 * Real.pi * (a / L * count) ≤
      (T₂ - T₁) * ((3 * Real.sqrt A₀ + 2 * A₀) / 2 * Real.exp (-(a / 1200))) + (C + 2 * K₀) * L := by
  set r : ℝ := 3 * Real.sqrt (A₀ * Real.exp (-(a / 600))) + 2 * (A₀ * Real.exp (-(a / 600)))
    with hr
  have hT0 : 0 < T₂ - T₁ := by linarith
  have hMsq0 : 0 < (T₂ - T₁) * (1 + 3 * Real.sqrt (A₀ * Real.exp (-(a / 600))) +
      2 * (A₀ * Real.exp (-(a / 600)))) := by positivity
  have hcount := count_le_of_meanSquare_rate (r := r) hK₀ hT12 hlogT₂ hlogMb hMsq0
    (le_of_eq (by rw [hr]; ring)) hmain
  have hrate := twoLength_rate_le hA₀ ha
  rw [← hr] at hrate
  have h1 : (T₂ - T₁) / 2 * r ≤
      (T₂ - T₁) * ((3 * Real.sqrt A₀ + 2 * A₀) / 2 * Real.exp (-(a / 1200))) := by
    calc (T₂ - T₁) / 2 * r
        ≤ (T₂ - T₁) / 2 * ((3 * Real.sqrt A₀ + 2 * A₀) * Real.exp (-(a / 1200))) :=
          mul_le_mul_of_nonneg_left hrate (by linarith)
      _ = _ := by ring
  have h2 : C + 2 * K₀ * L ≤ (C + 2 * K₀) * L := by nlinarith
  calc 2 * Real.pi * (a / L * count) ≤ (T₂ - T₁) / 2 * r + (C + 2 * K₀ * L) := hcount
    _ ≤ _ := add_le_add h1 h2

/-- Admissible heights for a mollifier with leading coefficient `1` and coefficients of norm
`≤ 1`: horizontal segments over `[1/4, 15/2]` free of zeros of `ζ` and of the mollifier. -/
theorem exists_admissible_heights_of_mollifier {b : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (hb1 : b 1 = 1)
    (hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) {A₁ B₁ A₂ B₂ : ℝ}
    (h20 : 20 ≤ A₁) (h1 : A₁ < B₁) (h2 : B₁ < A₂) (h3 : A₂ < B₂) :
    ∃ T₁ ∈ Ioo A₁ B₁, ∃ T₂ ∈ Ioo A₂ B₂,
      (∀ x ∈ Icc (1 / 4 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 ∧
        edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Icc (1 / 4 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 ∧
        edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) := by
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  set F : ℂ → ℂ := fun z => zetaEntire z * edPoly b (Finset.Icc 1 N) z with hF
  have hFd : Differentiable ℂ F := differentiable_zetaEntire.mul (differentiable_edPoly _ hs)
  have hFan : AnalyticOnNhd ℂ F Set.univ := hFd.differentiableOn.analyticOnNhd isOpen_univ
  have hFne : ∃ z : ℂ, F z ≠ 0 := by
    refine ⟨((15 / 2 : ℝ) : ℂ), mul_ne_zero ?_ ?_⟩
    · rw [zetaEntire_eq (by intro h; have := congrArg Complex.re h; simp at this; norm_num at this)]
      refine mul_ne_zero
        (by intro h; have := congrArg Complex.re h; simp at this; norm_num at this) ?_
      exact riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num)
    · intro h0
      have h := norm_edPoly_sub_one_le_half_of_six_le b hs
        (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩) hb1 hbn (z := ((15 / 2 : ℝ) : ℂ)) (by simp; norm_num)
      rw [h0] at h
      norm_num at h
  obtain ⟨T₁, hT₁, T₂, hT₂, hF1, hF2⟩ :=
    exists_horizontal_slices_avoiding_entire_zeros hFan hFne (c := (1 / 4 : ℝ)) (d := 15 / 2)
      (by norm_num) h1 h2 h3
  have hedge : ∀ T : ℝ, 20 ≤ T →
      (∀ x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2), F ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      ∀ x ∈ Icc (1 / 4 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 ∧
        edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
    intro T hT hFT x hx
    have hx' : x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2) := by
      rw [Set.uIcc_of_le (by norm_num)]; exact hx
    have hne1 : ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hFx := hFT x hx'
    simp only [hF] at hFx
    rw [zetaEntire_eq hne1] at hFx
    refine ⟨fun h0 => hFx (by rw [h0]; ring), fun h0 => hFx (by rw [h0]; ring)⟩
  exact ⟨T₁, hT₁, T₂, hT₂, hedge T₁ (by linarith [hT₁.1]) hF1,
    hedge T₂ (by linarith [hT₂.1, hT₁.2]) hF2⟩

/-- The Barban–Vehov tail is continuous along a vertical line above height zero. -/
theorem continuousOn_hbMollifiedTail_line (Z : ℕ) (σ₀ : ℝ) {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) :
    ContinuousOn (fun t : ℝ => hbMollifiedTail Z ((σ₀ : ℂ) + (t : ℂ) * I)) (Icc T₁ T₂) := by
  intro t ht
  have hne : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith [ht.1]
  exact (ContinuousAt.comp (g := hbMollifiedTail Z) (f := fun t : ℝ => ((σ₀ : ℂ) + (t : ℂ) * I))
    (continuousAt_hbMollifiedTail hne) (by fun_prop)).continuousWithinAt

/-- **The combined tail** `(log X · f_X − log Y · f_Y)/log(X/Y)` has mean square
`≤ 120 C_f (T₂ − T₁) e^{−a/600}` once both tails obey the three-lines bound. -/
theorem integral_normSq_twoLengthTail_le {X Y : ℕ} {L a Cf T₁ T₂ : ℝ} (σ₀ : ℝ)
    (hCf : 0 < Cf) (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂) (hlen : Real.exp (99 / 100 * L) ≤ T₂ - T₁)
    (hlogY0 : 0 ≤ Real.log Y) (hlogY : Real.log Y ≤ L / 200)
    (hgap : L / 400 ≤ Real.log X - Real.log Y) (hL : 0 < L)
    (hfX : ∫ t in T₁..T₂, ‖hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Cf * Real.exp (-((a + 1) / 600)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L)))
    (hfY : ∫ t in T₁..T₂, ‖hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Cf * Real.exp (-((a + 1) / 600)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L))) :
    ∫ t in T₁..T₂, ‖(((Real.log X : ℝ) : ℂ) * hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I) -
        ((Real.log Y : ℝ) : ℂ) * hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)) /
          ((Real.log X - Real.log Y : ℝ) : ℂ)‖ ^ 2 ≤
      (T₂ - T₁) * (120 * Cf * Real.exp (-(a / 600))) := by
  have hgap0 : 0 < Real.log X - Real.log Y := by
    have : 0 < L / 400 := by positivity
    linarith
  have hcX := continuousOn_hbMollifiedTail_line X σ₀ (T₂ := T₂) hT₁
  have hcY := continuousOn_hbMollifiedTail_line Y σ₀ (T₂ := T₂) hT₁
  have hiX : IntervalIntegrable (fun t : ℝ => ‖hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume T₁ T₂ := (hcX.norm.pow 2).intervalIntegrable_of_Icc hT
  have hiY : IntervalIntegrable (fun t : ℝ => ‖hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume T₁ T₂ := (hcY.norm.pow 2).intervalIntegrable_of_Icc hT
  have hcg : ContinuousOn (fun t : ℝ =>
      (((Real.log X : ℝ) : ℂ) * hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I) -
        ((Real.log Y : ℝ) : ℂ) * hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)) /
          ((Real.log X - Real.log Y : ℝ) : ℂ)) (Icc T₁ T₂) :=
    ((continuousOn_const.mul hcX).sub (continuousOn_const.mul hcY)).div_const _
  have hig : IntervalIntegrable (fun t : ℝ =>
      ‖(((Real.log X : ℝ) : ℂ) * hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I) -
        ((Real.log Y : ℝ) : ℂ) * hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)) /
          ((Real.log X - Real.log Y : ℝ) : ℂ)‖ ^ 2) volume T₁ T₂ :=
    (hcg.norm.pow 2).intervalIntegrable_of_Icc hT
  have hpt : ∀ t ∈ Icc T₁ T₂,
      ‖(((Real.log X : ℝ) : ℂ) * hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I) -
        ((Real.log Y : ℝ) : ℂ) * hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)) /
          ((Real.log X - Real.log Y : ℝ) : ℂ)‖ ^ 2 ≤
        32 * ‖hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 +
          8 * ‖hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    fun t _ => normSq_twoLength_tail_le (by linarith) hlogY0 hgap0 (by linarith) (by linarith) _ _
  have hmono := intervalIntegral.integral_mono_on hT hig
    ((hiX.const_mul 32).add (hiY.const_mul 8)) hpt
  rw [intervalIntegral.integral_add (hiX.const_mul 32) (hiY.const_mul 8),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  refine hmono.trans ?_
  have he : Real.exp (-((a + 1) / 600)) ≤ Real.exp (-(a / 600)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : T₂ - T₁ + 2 * Real.exp (99 / 100 * L) ≤ 3 * (T₂ - T₁) := by linarith
  have hB : Cf * Real.exp (-((a + 1) / 600)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L)) ≤
      Cf * Real.exp (-(a / 600)) * (3 * (T₂ - T₁)) := by
    have : 0 ≤ T₂ - T₁ + 2 * Real.exp (99 / 100 * L) := by positivity
    gcongr
  have := add_le_add (mul_le_mul_of_nonneg_left (hfX.trans hB) (by norm_num : (0 : ℝ) ≤ 32))
    (mul_le_mul_of_nonneg_left (hfY.trans hB) (by norm_num : (0 : ℝ) ≤ 8))
  linarith

/-- **The two-length mollified mean square on `Re s = 1/2 + a/L`** is
`(T₂ − T₁)(1 + 3√η + 2η)`, `η = (128 + 120 C_f) e^{−a/600}`. -/
theorem integral_normSq_zetaTwoLength_rightShift_le {X Y : ℕ} {L a CM Cf T₁ T₂ : ℝ}
    (hL : 1000 ≤ L) (hLCM : 100 * |CM| ≤ L) (hCf : 0 < Cf)
    (hXle : (X : ℝ) ≤ Real.exp (L / 100)) (hXgt : Real.exp (L / 100) - 1 < X)
    (hYle : (Y : ℝ) ≤ Real.exp (L / 200)) (hYgt : Real.exp (L / 200) - 1 < Y)
    (hCM : ∑ k ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log X * (Real.log X + CM))
    (ha : 0 ≤ a) (haL : 2 * a ≤ L) (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂)
    (hlen : Real.exp (99 / 100 * L) ≤ T₂ - T₁)
    (hfX : ∫ t in T₁..T₂, ‖hbMollifiedTail X (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Cf * Real.exp (-((a + 1) / 600)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L)))
    (hfY : ∫ t in T₁..T₂, ‖hbMollifiedTail Y (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Cf * Real.exp (-((a + 1) / 600)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L))) :
    ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (T₂ - T₁) * (1 + 3 * Real.sqrt ((128 + 120 * Cf) * Real.exp (-(a / 600))) +
        2 * ((128 + 120 * Cf) * Real.exp (-(a / 600)))) := by
  obtain ⟨hY2, hYX, -, -, -, hlogY0, hlogY, hgap⟩ :=
    twoLength_scale_facts hL hXle hXgt hYle hYgt
  have hL0 : 0 < L := by linarith
  set σ₀ : ℝ := 1 / 2 + a / L with hσ₀
  have hP := integral_normSq_twoLengthHead_rightShift_le hL hLCM hXle hXgt hYle hYgt hCM ha haL
    hT hlen
  have hg := integral_normSq_twoLengthTail_le σ₀ hCf hT₁ hT hlen hlogY0 hlogY hgap hL0
    hfX hfY
  set η : ℝ := (128 + 120 * Cf) * Real.exp (-(a / 600)) with hη
  have hη0 : 0 < η := by positivity
  have he : Real.exp (-(a / 100)) ≤ Real.exp (-(a / 600)) := Real.exp_le_exp.mpr (by linarith)
  have hsum : (∫ t in T₁..T₂, ‖edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X)
        (((σ₀ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) +
      (∫ t in T₁..T₂, ‖(((Real.log X : ℝ) : ℂ) * hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I) -
        ((Real.log Y : ℝ) : ℂ) * hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)) /
          ((Real.log X - Real.log Y : ℝ) : ℂ)‖ ^ 2) ≤ (T₂ - T₁) * η := by
    have hT0 : 0 ≤ T₂ - T₁ := by linarith
    have h1 : (T₂ - T₁) * (128 * Real.exp (-(a / 100))) ≤
        (T₂ - T₁) * (128 * Real.exp (-(a / 600))) := by gcongr
    rw [hη]
    nlinarith
  have hs : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hPc : ContinuousOn (fun t : ℝ => edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X)
      (((σ₀ : ℝ) : ℂ) + (t : ℂ) * I)) (Icc T₁ T₂) :=
    ((differentiable_edPoly _ hs).continuous.comp (by fun_prop)).continuousOn
  have hgc : ContinuousOn (fun t : ℝ =>
      (((Real.log X : ℝ) : ℂ) * hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I) -
        ((Real.log Y : ℝ) : ℂ) * hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)) /
          ((Real.log X - Real.log Y : ℝ) : ℂ)) (Icc T₁ T₂) :=
    ((continuousOn_const.mul (continuousOn_hbMollifiedTail_line X σ₀ hT₁)).sub
      (continuousOn_const.mul (continuousOn_hbMollifiedTail_line Y σ₀ hT₁))).div_const _
  have hMsq := integral_normSq_one_add_add_le hT hη0 hPc hgc hsum
  simp only [zeta_mul_twoLength_eq hY2 hYX]
  exact hMsq

/-- **Exponential zero density at the critical scale.** For all large `U`, with `L = log U`,
admissible heights `T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)` exist such that for every
`1 ≤ a` with `2a + 2 ≤ L` the zeros with `Re ρ ≥ 1/2 + 2a/L` between them satisfy
`2π (a/L) · #zeros ≤ (T₂ − T₁) A e^{−a/1200} + K L`. -/
theorem exists_selberg_exponential_nearLine_zeroDensity :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ a : ℝ, 1 ≤ a → 2 * a + 2 ≤ Real.log U →
        ∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
          2 * Real.pi * ((a / Real.log U) *
            ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / Real.log U ≤ w.re),
              ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
            (T₂ - T₁) * (A * Real.exp (-(a / 1200))) + K * Real.log U := by
  obtain ⟨C, K₀, hC, hK₀, hcons⟩ := exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide
  obtain ⟨Cf, hCf, htail⟩ := exists_eventually_integral_hbMollifiedTail_rightShift_le_len
  obtain ⟨CM, hCM⟩ := exists_sum_vonMangoldt_sq_div_le
  have hA₀0 : 0 < 128 + 120 * Cf := by positivity
  refine ⟨(3 * Real.sqrt (128 + 120 * Cf) + 2 * (128 + 120 * Cf)) / 2, C + 2 * K₀, by positivity,
    by positivity, ?_⟩
  filter_upwards [htail, eventually_ge_atTop (Real.exp (max 1000 (100 * |CM|)))]
    with U htailU hUL₀
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos _) hUL₀
  have hL := Real.log_le_log (Real.exp_pos _) hUL₀
  rw [Real.log_exp] at hL
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log U := ⟨_, rfl⟩
  have hUexp : U = Real.exp L := by rw [hLdef, Real.exp_log hU0]
  rw [← hLdef] at hL
  subst hUexp
  simp only [Real.log_exp] at htailU ⊢
  have hL1000 : 1000 ≤ L := le_trans (le_max_left _ _) hL
  have hLCM : 100 * |CM| ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := by linarith
  have hU100 : Real.exp L ^ ((1 : ℝ) / 100) = Real.exp (L / 100) := by
    rw [← Real.exp_mul]; ring_nf
  have hU200 : Real.exp L ^ ((1 : ℝ) / 200) = Real.exp (L / 200) := by
    rw [← Real.exp_mul]; ring_nf
  have hU99 : Real.exp L ^ ((99 : ℝ) / 100) = Real.exp (99 / 100 * L) := by
    rw [← Real.exp_mul]; ring_nf
  set X : ℕ := ZetaGateProductAFE.mollN (Real.exp L) with hXdef
  set Y : ℕ := ⌊Real.exp (L / 200)⌋₊ with hYdef
  have hXle : (X : ℝ) ≤ Real.exp (L / 100) := by
    rw [← hU100]; exact ZetaGateProductAFE.mollN_le (Real.exp_pos L).le
  have hXgt : Real.exp (L / 100) - 1 < X := by
    rw [← hU100]; exact ZetaGateProductAFE.mollN_gt (Real.exp L)
  have hYle : (Y : ℝ) ≤ Real.exp (L / 200) := Nat.floor_le (Real.exp_pos _).le
  have hYgt : Real.exp (L / 200) - 1 < Y := by
    have := Nat.lt_floor_add_one (Real.exp (L / 200))
    linarith
  obtain ⟨hY2, hYX, hYhalf, hXhalf, -, -, -, -⟩ := twoLength_scale_facts hL1000 hXle hXgt hYle hYgt
  obtain ⟨-, hHU, -, -, hU160, -⟩ := nearLine_scale_facts (by linarith : (500 : ℝ) ≤ L)
  have hbn : ∀ n ∈ Finset.Icc 1 X, ‖twoLengthCoeff X Y n‖ ≤ 1 :=
    fun n hn => norm_twoLengthCoeff_le (by omega) hYX hn
  obtain ⟨T₁, hT₁, T₂, hT₂, hE1, hE2⟩ := exists_admissible_heights_of_mollifier
    (b := twoLengthCoeff X Y) (N := X) (by omega) (twoLengthCoeff_one (by omega) hYX) hbn
    (A₁ := Real.exp L / 4) (B₁ := Real.exp L / 4 + 1) (A₂ := Real.exp L / 2 - 1)
    (B₂ := Real.exp L / 2) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨T₁, hT₁, T₂, hT₂, fun a ha haL Z hZ => ?_⟩
  have hT₁₂ : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  have hlen : Real.exp (99 / 100 * L) ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1]
  have hfX := htailU X (by rw [hU100]; exact hXle) (by rw [hU200]; exact hXhalf) a (by linarith)
    haL T₁ T₂ hT₁.1.le hT₁₂ hT₂.2.le
  have hexp12 : Real.exp (L / 200) ≤ Real.exp (L / 100) := Real.exp_le_exp.mpr (by linarith)
  have hfY := htailU Y (by rw [hU100]; linarith) (by rw [hU200]; exact hYhalf) a (by linarith)
    haL T₁ T₂ hT₁.1.le hT₁₂ hT₂.2.le
  rw [hU99] at hfX hfY
  have hMsq := integral_normSq_zetaTwoLength_rightShift_le hL1000 hLCM hCf hXle hXgt hYle hYgt
    (hCM X (by omega)) (by linarith) (by linarith) (by linarith [hT₁.1]) hT₁₂ hlen hfX hfY
  have hσ₀a : 1 / 4 ≤ 1 / 2 + a / L := by
    have : 0 < a / L := div_pos (by linarith) hL0
    linarith
  have hσ₀b : 1 / 2 + a / L < 2 := by
    have : a / L ≤ 1 := by rw [div_le_one hL0]; linarith
    linarith
  have hmem : ∀ x ∈ Icc (1 / 2 + a / L) (15 / 2 : ℝ), x ∈ Icc (1 / 4 : ℝ) (15 / 2) :=
    fun x hx => ⟨le_trans hσ₀a hx.1, hx.2⟩
  have hXX : (1 : ℝ) ≤ (X : ℝ) ^ (5 : ℕ) :=
    one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ X))
  have hmain := hcons (twoLengthCoeff X Y) X (by omega) (twoLengthCoeff_one (by omega) hYX) hbn
    (fun n _ => conj_twoLengthCoeff X Y n) _ hXX
    (sum_norm_twoLengthCoeff_mul_rpow_le (by omega) hYX) (1 / 2 + a / L) T₁ T₂ _
    hσ₀a hσ₀b (by linarith [hT₁.1]) hT12
    (fun x hx => (hE1 x (hmem x hx)).1) (fun x hx => (hE2 x (hmem x hx)).1)
    (fun x hx => (hE1 x (hmem x hx)).2) (fun x hx => (hE2 x (hmem x hx)).2)
    hMsq Z hZ (a / L) (div_pos (by linarith) hL0).le
  have hfilter : Z.filter (fun w => 1 / 2 + a / L + a / L ≤ w.re) =
      Z.filter (fun w => 1 / 2 + 2 * a / L ≤ w.re) := by
    refine Finset.filter_congr fun w _ => ?_
    rw [show 1 / 2 + a / L + a / L = 1 / 2 + 2 * a / L by ring]
  rw [hfilter] at hmain
  have hlogT₂ : Real.log T₂ ≤ L := by
    have h1 : T₂ ≤ Real.exp L := le_trans hT₂.2.le (by linarith [Real.exp_pos L])
    have := Real.log_le_log (by linarith [hT₁.1, hT₁.2, hT₂.1]) h1
    rwa [Real.log_exp] at this
  have hlogMb : Real.log ((X : ℝ) ^ (5 : ℕ)) ≤ L := by
    rw [Real.log_pow]
    have h1 := Real.log_le_log (by exact_mod_cast (by omega : 0 < X)) hXle
    rw [Real.log_exp] at h1
    push_cast
    linarith
  exact twoLength_final_count (by linarith) hC.le hK₀.le hA₀0.le (by linarith) hT12 hlogT₂
    hlogMb hmain

end RHTower
