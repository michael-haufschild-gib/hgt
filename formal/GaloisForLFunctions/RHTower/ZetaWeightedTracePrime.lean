import GaloisForLFunctions.RHTower.ZetaJacksonFourier
import Zeta23.PrimeSideA.Basic

/-!
# The prime part of the weighted trace

For grid weights `W_k` the prime part of the weighted trace of the zeta Gram matrix is, by Zeta23's per-point identity
`P_part_eq`,

`Σ_{k<d} W_k ∫ φ̂(r)² P_X(τ_k + r) dr = −2 Σ_{n≤X} a_n A_φ(y_n) Σ_{k<d} W_k cos(τ_k y_n)`   (`weighted_P_part_eq`).

If the full-lattice character sum `Σ_{k∈ℤ} W(τ_k) e^{iτ_k y}` vanishes, the finite sum is bounded by the mass of the
weights outside the grid (`abs_sum_range_cos_le_of_hasSum_zero`).  For the Jackson window this holds for every prime
frequency `2b ≤ y_n ≤ L − 2b` (`jackson_grid_char_eq_zero_of_band`); the remaining frequencies `y_n > L − 2b` carry
`A_φ(y_n) ≤ L − y_n < 2b`.  Altogether (`abs_weighted_P_part_le`)

`|Σ_k W_k G^P_kk| ≤ 2 (Σ_{n≤X} a_n) (L·E + 2b·d)`,   `E = Σ_{k∉[0,d)} W(τ_k)`.
-/

open Complex MeasureTheory Real Set Filter Finset
open GaloisForLFunctions.HTGeometry Zeta23 Zeta23.PrimeSide

noncomputable section

namespace RHTower

/-- A finite part of a lattice sum with total `0` is bounded by the complementary mass. -/
theorem norm_sum_le_tsum_compl_of_hasSum_zero {c : ℤ → ℂ} (hc : HasSum c 0)
    (hs : Summable fun k => ‖c k‖) (S : Finset ℤ) :
    ‖∑ k ∈ S, c k‖ ≤ ∑' k : {k : ℤ // k ∉ S}, ‖c k‖ := by
  have h := hc.summable.sum_add_tsum_subtype_compl S
  rw [hc.tsum_eq] at h
  have e : ∑ k ∈ S, c k = -∑' k : {k : ℤ // k ∉ S}, c k := by linear_combination h
  rw [e, norm_neg]
  exact norm_tsum_le_tsum_norm (hs.subtype _)

/-- **The cosine sum over the finite grid.**  If `Σ_{k∈ℤ} W(τ_k) e^{iτ_k y} = 0` with `W ≥ 0` summable on the lattice,
then `|Σ_{k<d} W(τ_k) cos(τ_k y)| ≤ Σ_{k∉[0,d)} W(τ_k)`. -/
theorem abs_sum_range_cos_le_of_hasSum_zero {W : ℝ → ℝ} (hW0 : ∀ s, 0 ≤ W s) {τ : ℤ → ℝ} {y : ℝ}
    (hc : HasSum (fun k : ℤ => ((W (τ k) : ℝ) : ℂ) * cexp (I * y * ((τ k : ℝ) : ℂ))) 0)
    (hs : Summable fun k : ℤ => W (τ k)) (d : ℕ) :
    |∑ k ∈ Finset.range d, W (τ k) * Real.cos (τ k * y)|
      ≤ ∑' k : {k : ℤ // k ∉ (Finset.range d).image (fun k : ℕ => (k : ℤ))}, W (τ k) := by
  set S : Finset ℤ := (Finset.range d).image (fun k : ℕ => (k : ℤ)) with hS
  have hnorm : ∀ k : ℤ, ‖((W (τ k) : ℝ) : ℂ) * cexp (I * y * ((τ k : ℝ) : ℂ))‖ = W (τ k) := by
    intro k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW0 _),
      show I * (y : ℂ) * ((τ k : ℝ) : ℂ) = ((y * τ k : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hb := norm_sum_le_tsum_compl_of_hasSum_zero hc (by simp_rw [hnorm]; exact hs) S
  simp_rw [hnorm] at hb
  have hre : ∑ k ∈ Finset.range d, W (τ k) * Real.cos (τ k * y)
      = (∑ k ∈ S, ((W (τ k) : ℝ) : ℂ) * cexp (I * y * ((τ k : ℝ) : ℂ))).re := by
    rw [hS, Finset.sum_image (fun a _ b _ h => by exact_mod_cast h), Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show I * (y : ℂ) * ((τ k : ℝ) : ℂ) = ((y * τ k : ℝ) : ℂ) * I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, mul_comm y]
  rw [hre]
  exact (Complex.abs_re_le_norm _).trans hb

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- **The weighted prime part of the trace.** -/
theorem weighted_P_part_eq (hF : LocalHypsCore cϱ p F) (W : ℕ → ℝ) :
    ∑ k ∈ Finset.range p.d, W k * ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)
      = -2 * ∑ n ∈ primeRange p.X, acoef n * F.Aphi (ycoef n)
          * ∑ k ∈ Finset.range p.d, W k * Real.cos (p.tau k * ycoef n) := by
  simp_rw [P_part_eq hF]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Bound for the weighted prime part.**  Suppose `0 ≤ W_k ≤ 1` and, for every prime power `n ≤ X` with
`log 2 ≤ y_n ≤ L − B`, the finite cosine sum is at most `E`.  Then
`|Σ_k W_k G^P_kk| ≤ 2 (Σ_{n≤X} a_n)(L E + B d)`. -/
theorem abs_weighted_P_part_le (hF : LocalHypsCore cϱ p F) {W : ℕ → ℝ} (hW0 : ∀ k, 0 ≤ W k)
    (hW1 : ∀ k, W k ≤ 1) {B E : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hcos : ∀ n ∈ primeRange p.X, Real.log 2 ≤ ycoef n → ycoef n ≤ p.L - B →
      |∑ k ∈ Finset.range p.d, W k * Real.cos (p.tau k * ycoef n)| ≤ E) :
    |∑ k ∈ Finset.range p.d, W k * ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)|
      ≤ 2 * (∑ n ∈ primeRange p.X, acoef n) * (p.L * E + B * p.d) := by
  rw [weighted_P_part_eq hF, abs_mul, abs_neg, abs_two, mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun n hn => ?_)) (by norm_num)
  have ha : 0 ≤ acoef n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hA0 := hF.Aphi_nonneg (ycoef n)
  have htriv : |∑ k ∈ Finset.range p.d, W k * Real.cos (p.tau k * ycoef n)| ≤ p.d := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range p.d, |W k * Real.cos (p.tau k * ycoef n)|
        ≤ ∑ k ∈ Finset.range p.d, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
          rw [abs_mul, abs_of_nonneg (hW0 k)]
          exact (mul_le_mul (hW1 k) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one).trans
            (le_of_eq (one_mul 1))
      _ = p.d := by simp
  have hRHS : 0 ≤ p.L * E + B * p.d := by
    have := mul_nonneg hF.L_pos.le hE; have : 0 ≤ B * p.d := by positivity
    linarith
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- n = 1: the coefficient `a_1 = Λ(1)/1` vanishes
    have hn1 : n = 1 := by have := (Finset.mem_Ioc.1 hn).1; omega
    subst hn1
    simp only [acoef, ArithmeticFunction.vonMangoldt_apply_one, Nat.cast_one, Real.sqrt_one, div_one,
      zero_mul, abs_zero]
    positivity
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hA0, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ ha
  have hy2 : Real.log 2 ≤ ycoef n := Real.log_le_log two_pos (by exact_mod_cast hn2)
  have hy0 : 0 ≤ ycoef n := le_trans (Real.log_nonneg one_le_two) hy2
  rcases le_or_gt (ycoef n) (p.L - B) with hyL | hyL
  · have hAle : F.Aphi (ycoef n) ≤ p.L := (hF.Aphi_le _).trans (by
      apply max_le _ hF.L_pos.le; rw [abs_of_nonneg hy0]; linarith)
    have h1 : F.Aphi (ycoef n) * |∑ k ∈ Finset.range p.d, W k * Real.cos (p.tau k * ycoef n)|
        ≤ p.L * E := mul_le_mul hAle (hcos n hn hy2 hyL) (abs_nonneg _) hF.L_pos.le
    have h2 : 0 ≤ B * p.d := by positivity
    linarith
  · have hAle : F.Aphi (ycoef n) ≤ B := (hF.Aphi_le _).trans (by
      apply max_le _ hB; rw [abs_of_nonneg hy0]; linarith)
    have h1 : F.Aphi (ycoef n) * |∑ k ∈ Finset.range p.d, W k * Real.cos (p.tau k * ycoef n)|
        ≤ B * p.d := mul_le_mul hAle htriv (abs_nonneg _) hB
    have h2 : 0 ≤ p.L * E := mul_nonneg hF.L_pos.le hE
    linarith

/-- **Sharper bound for the weighted prime part:** the trivial grid bound `B·d` is paid only on the alias band
`y_n > L − B`, so `|Σ_k W_k G^P_kk| ≤ 2(L E Σ_{n≤X} a_n + B d Σ_{n≤X, y_n > L−B} a_n)`. -/
theorem abs_weighted_P_part_le_band (hF : LocalHypsCore cϱ p F) {W : ℕ → ℝ} (hW0 : ∀ k, 0 ≤ W k)
    (hW1 : ∀ k, W k ≤ 1) {B E : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hcos : ∀ n ∈ primeRange p.X, Real.log 2 ≤ ycoef n → ycoef n ≤ p.L - B →
      |∑ k ∈ Finset.range p.d, W k * Real.cos (p.tau k * ycoef n)| ≤ E) :
    |∑ k ∈ Finset.range p.d, W k * ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)|
      ≤ 2 * (p.L * E * ∑ n ∈ primeRange p.X, acoef n
        + B * p.d * ∑ n ∈ (primeRange p.X).filter (fun n => p.L - B < ycoef n), acoef n) := by
  rw [weighted_P_part_eq hF, abs_mul, abs_neg, abs_two]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hsplit : p.L * E * ∑ n ∈ primeRange p.X, acoef n
      + B * p.d * ∑ n ∈ (primeRange p.X).filter (fun n => p.L - B < ycoef n), acoef n
      = ∑ n ∈ primeRange p.X, (p.L * E * acoef n
          + if p.L - B < ycoef n then B * p.d * acoef n else 0) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      ← Finset.mul_sum]
  rw [hsplit]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have ha : 0 ≤ acoef n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hA0 := hF.Aphi_nonneg (ycoef n)
  have htriv : |∑ k ∈ Finset.range p.d, W k * Real.cos (p.tau k * ycoef n)| ≤ p.d := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range p.d, |W k * Real.cos (p.tau k * ycoef n)|
        ≤ ∑ k ∈ Finset.range p.d, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
          rw [abs_mul, abs_of_nonneg (hW0 k)]
          exact (mul_le_mul (hW1 k) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one).trans
            (le_of_eq (one_mul 1))
      _ = p.d := by simp
  have hLE : 0 ≤ p.L * E * acoef n := mul_nonneg (mul_nonneg hF.L_pos.le hE) ha
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hn1 : n = 1 := by have := (Finset.mem_Ioc.1 hn).1; omega
    subst hn1
    have h0 : acoef 1 = 0 := by
      simp only [acoef, ArithmeticFunction.vonMangoldt_apply_one, Nat.cast_one, Real.sqrt_one, div_one]
    simp only [h0, zero_mul, abs_zero, mul_zero]
    split_ifs <;> simp
  have hy2 : Real.log 2 ≤ ycoef n := Real.log_le_log two_pos (by exact_mod_cast hn2)
  have hy0 : 0 ≤ ycoef n := le_trans (Real.log_nonneg one_le_two) hy2
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hA0]
  split_ifs with hyL
  · have hAle : F.Aphi (ycoef n) ≤ B := (hF.Aphi_le _).trans (by
      apply max_le _ hB; rw [abs_of_nonneg hy0]; linarith)
    have h1 : F.Aphi (ycoef n) * |∑ k ∈ Finset.range p.d, W k * Real.cos (p.tau k * ycoef n)|
        ≤ B * p.d := mul_le_mul hAle htriv (abs_nonneg _) hB
    have h2 := mul_le_mul_of_nonneg_left h1 ha
    nlinarith
  · push Not at hyL
    have hAle : F.Aphi (ycoef n) ≤ p.L := (hF.Aphi_le _).trans (by
      apply max_le _ hF.L_pos.le; rw [abs_of_nonneg hy0]; linarith)
    have h1 : F.Aphi (ycoef n) * |∑ k ∈ Finset.range p.d, W k * Real.cos (p.tau k * ycoef n)|
        ≤ p.L * E := mul_le_mul hAle (hcos n hn hy2 hyL) (abs_nonneg _) hF.L_pos.le
    have h2 := mul_le_mul_of_nonneg_left h1 ha
    nlinarith

namespace FejerWeight

/-- A window with quadratic decay, sampled along the grid, is `O(|x|⁻²)`. -/
theorem window_grid_isBigO {W : ℝ → ℝ} {C R L : ℝ} (hC : 0 ≤ C)
    (hWdec : ∀ s, R ≤ |s| → |W s| ≤ C / s ^ 2) (hL : 0 < L) (T : ℝ) :
    (fun x : ℝ => W (T + x * (2 * π / L))) =O[cocompact ℝ] fun x => |x| ^ (-2 : ℝ) := by
  set h : ℝ := 2 * π / L with hh
  have hh0 : 0 < h := by positivity
  refine Asymptotics.IsBigO.of_bound (4 * C / h ^ 2) ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually
    (eventually_ge_atTop (2 * (|T| + |R| + 1) / h))] with x hx
  rw [Real.norm_eq_abs, div_le_iff₀ hh0] at hx
  have hT := abs_nonneg T
  have hRa := abs_nonneg R
  have hxh : |x * h| = |x| * h := by rw [abs_mul, abs_of_pos hh0]
  have h2 : |x * h| ≤ |T + x * h| + |T| := by
    have := abs_sub (T + x * h) T
    rwa [add_sub_cancel_left] at this
  have hs : |x| * h / 2 ≤ |T + x * h| := by linarith
  have hRs : R ≤ |T + x * h| := by linarith [le_abs_self R]
  have hpos : 0 < |x| * h / 2 := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) (-2)),
    Real.rpow_neg (abs_nonneg x), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine (hWdec (T + x * h) hRs).trans ?_
  have hsq : (|x| * h / 2) ^ 2 ≤ (T + x * h) ^ 2 := by
    rw [← sq_abs (T + x * h)]; exact pow_le_pow_left₀ hpos.le hs 2
  calc C / (T + x * h) ^ 2 ≤ C / (|x| * h / 2) ^ 2 :=
        div_le_div_of_nonneg_left hC (by positivity) hsq
    _ = 4 * C / h ^ 2 * (|x| ^ 2)⁻¹ := by field_simp; ring

variable {b s₀ s₁ : ℝ}

theorem summable_jacksonWindow_grid (hb : 0 < b) (h01 : s₀ ≤ s₁) {L : ℝ} (hL : 0 < L) (T : ℝ) :
    Summable fun k : ℤ => jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) :=
  summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    ((window_grid_isBigO (by have := (jacksonMass_pos hb).le; positivity)
      (fun s hs => abs_jacksonWindow_le_inv_sq hb h01 hs) hL T).comp_tendsto Int.tendsto_coe_cofinite)

/-- Inside the band `2b ≤ y ≤ L − 2b` every alias `jL − y` is at distance `≥ 2b` (for `4b ≤ L`). -/
theorem two_mul_le_abs_alias {L y : ℝ} (hb : 0 < b) (hL : 4 * b ≤ L) (hy : 2 * b ≤ y)
    (hy' : y ≤ L - 2 * b) (j : ℤ) : 2 * b ≤ |j * L - y| := by
  rcases lt_trichotomy j 0 with hj | hj | hj
  · have hj' : (j : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hj
    rw [abs_of_neg (by nlinarith)]; nlinarith
  · subst hj; simp only [Int.cast_zero, zero_mul, zero_sub, abs_neg]; rw [abs_of_pos (by linarith)]
    exact hy
  · have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    rw [abs_of_nonneg (by nlinarith)]; nlinarith

/-- **The Jackson cosine sums on the finite grid** are bounded by the outer mass of the window. -/
theorem abs_sum_range_jackson_cos_le (hb : 0 < b) (h01 : s₀ ≤ s₁) {L : ℝ} (hL : 4 * b ≤ L)
    (T : ℝ) {y : ℝ} (hy : 2 * b ≤ y) (hy' : y ≤ L - 2 * b) (d : ℕ) :
    |∑ k ∈ Finset.range d, jacksonWindow b s₀ s₁ (T + (k : ℤ) * (2 * π / L))
        * Real.cos ((T + (k : ℤ) * (2 * π / L)) * y)|
      ≤ ∑' k : {k : ℤ // k ∉ (Finset.range d).image (fun k : ℕ => (k : ℤ))},
          jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) := by
  have hL0 : 0 < L := by linarith
  exact abs_sum_range_cos_le_of_hasSum_zero (W := jacksonWindow b s₀ s₁)
    (τ := fun k : ℤ => T + k * (2 * π / L)) (jacksonWindow_nonneg hb h01)
    (hasSum_jackson_grid_char_eq_zero hb h01 hL0 T y (two_mul_le_abs_alias hb hL hy hy'))
    (summable_jacksonWindow_grid hb h01 hL0 T) d

/-- Telescoping: `Σ_{m≥0} (M + (m+1)h)⁻² ≤ 1/(hM)`. -/
theorem tsum_inv_sq_grid_shift_le {M h : ℝ} (hM : 0 < M) (hh : 0 < h) :
    Summable (fun m : ℕ => 1 / (M + (m + 1) * h) ^ 2) ∧
      ∑' m : ℕ, 1 / (M + (m + 1) * h) ^ 2 ≤ 1 / (h * M) := by
  have hnn : ∀ m : ℕ, 0 ≤ 1 / (M + (m + 1) * h) ^ 2 := fun m => by positivity
  have hstep : ∀ m : ℕ, 1 / (M + (m + 1) * h) ^ 2
      ≤ (1 / h) * (1 / (M + m * h) - 1 / (M + (m + 1) * h)) := by
    intro m
    have h1 : 0 < M + m * h := by positivity
    have h2 : 0 < M + (m + 1) * h := by positivity
    rw [div_sub_div _ _ h1.ne' h2.ne', one_mul, mul_one,
      show M + (m + 1) * h - (M + m * h) = h by ring, div_mul_div_comm, one_mul,
      show h / (h * ((M + m * h) * (M + (m + 1) * h))) = 1 / ((M + m * h) * (M + (m + 1) * h)) by
        field_simp]
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]
    exact mul_le_mul_of_nonneg_right (by nlinarith) h2.le
  have hpart : ∀ n : ℕ, ∑ m ∈ Finset.range n, 1 / (M + (m + 1) * h) ^ 2 ≤ 1 / (h * M) := by
    intro n
    calc ∑ m ∈ Finset.range n, 1 / (M + (m + 1) * h) ^ 2
        ≤ ∑ m ∈ Finset.range n, (1 / h) * (1 / (M + m * h) - 1 / (M + (m + 1) * h)) :=
          Finset.sum_le_sum fun m _ => hstep m
      _ = (1 / h) * (1 / M - 1 / (M + n * h)) := by
          rw [← Finset.mul_sum]
          congr 1
          have := Finset.sum_range_sub' (fun m : ℕ => 1 / (M + m * h)) n
          simp only [Nat.cast_add, Nat.cast_one] at this
          rw [this]
          simp
      _ ≤ 1 / (h * M) := by
          have : 0 ≤ 1 / (M + n * h) := by positivity
          rw [mul_sub, show 1 / h * (1 / M) = 1 / (h * M) by field_simp]
          have : 0 ≤ 1 / h * (1 / (M + n * h)) := by positivity
          linarith
  exact ⟨summable_of_sum_range_le hnn hpart, Real.tsum_le_of_sum_range_le hnn hpart⟩

/-- `c/D³ ≤ (c/M)·D⁻²` for `D ≥ M > 0`. -/
theorem div_cube_le_div_mul_inv_sq {c M D : ℝ} (hc : 0 ≤ c) (hM : 0 < M) (hMD : M ≤ D) :
    c / D ^ 3 ≤ c / M * (1 / D ^ 2) := by
  have hD : 0 < D := lt_of_lt_of_le hM hMD
  rw [div_mul_div_comm, mul_one]
  apply div_le_div_of_nonneg_left hc (by positivity)
  rw [show D ^ 3 = D * D ^ 2 by ring]
  exact mul_le_mul_of_nonneg_right hMD (by positivity)

/-- **The mass of the Jackson window outside the grid.**  If the window interval sits at distance `M` inside the
grid range `[T, T + d·h]` (`h = 2π/L`), then `Σ_{k∉[0,d)} W(τ_k) ≤ κ₂⁻¹·(16/(3b²))·(1/M³ + 2/(hM²))`. -/
theorem tsum_compl_jacksonWindow_le (hb : 0 < b) (h01 : s₀ ≤ s₁) {L T M : ℝ} (hL : 0 < L) (hM : 0 < M)
    (d : ℕ) (hs₀ : T + M ≤ s₀) (hs₁ : s₁ + M ≤ T + d * (2 * π / L)) :
    ∑' k : {k : ℤ // k ∉ (Finset.range d).image (fun k : ℕ => (k : ℤ))},
        jacksonWindow b s₀ s₁ (T + k * (2 * π / L))
      ≤ (jacksonMass b)⁻¹ * (16 / (3 * b ^ 2)) * (1 / M ^ 3 + 2 / (2 * π / L * M ^ 2)) := by
  set h : ℝ := 2 * π / L with hh
  have hh0 : 0 < h := by positivity
  set S : Finset ℤ := (Finset.range d).image (fun k : ℕ => (k : ℤ)) with hS
  set F : ℤ → ℝ := fun k => jacksonWindow b s₀ s₁ (T + k * h) with hF
  set c : ℝ := (jacksonMass b)⁻¹ * (16 / (3 * b ^ 2)) with hc
  have hc0 : 0 ≤ c := by have := (jacksonMass_pos hb).le; positivity
  have hF0 : ∀ k, 0 ≤ F k := fun k => jacksonWindow_nonneg hb h01 _
  have hFs : Summable F := summable_jacksonWindow_grid hb h01 hL T
  have hcube : ∀ D, 0 < D → c / D ^ 3 = (jacksonMass b)⁻¹ * (16 / (3 * b ^ 2 * D ^ 3)) := by
    intro D hD; rw [hc]; field_simp
  -- pointwise bounds outside the grid
  have hright : ∀ m : ℕ, F ((d + m : ℕ) : ℤ) ≤ c / M * (1 / (M + m * h) ^ 2) := by
    intro m
    have hD : 0 < M + m * h := by positivity
    have hW := jacksonWindow_le_right hb (s₀ := s₀) (s₁ := s₁) (s := T + ((d + m : ℕ) : ℤ) * h)
      (D := M + m * h) hD (by push_cast; nlinarith)
    rw [← hcube _ hD] at hW
    exact hW.trans (div_cube_le_div_mul_inv_sq hc0 hM (by nlinarith))
  have hleft : ∀ n : ℕ, F (-((n : ℤ) + 1)) ≤ c / M * (1 / (M + (n + 1) * h) ^ 2) := by
    intro n
    have hD : 0 < M + (n + 1) * h := by positivity
    have hW := jacksonWindow_le_left hb (s₀ := s₀) (s₁ := s₁) (s := T + (-((n : ℤ) + 1) : ℤ) * h)
      (D := M + (n + 1) * h) hD (by push_cast; nlinarith)
    rw [← hcube _ hD] at hW
    exact hW.trans (div_cube_le_div_mul_inv_sq hc0 hM (by nlinarith))
  -- the complement as an indicator sum
  set G : ℤ → ℝ := (((S : Set ℤ))ᶜ).indicator F with hG
  have hGs : Summable G := hFs.indicator _
  have hsub : ∑' k : {k : ℤ // k ∉ S}, F k = ∑' k, G k := by
    rw [hG, ← _root_.tsum_subtype]
    rfl
  rw [hsub]
  have hG0 : ∀ k, 0 ≤ G k := fun k => Set.indicator_nonneg (fun k _ => hF0 k) k
  have hGnat : Summable fun n : ℕ => G n := hGs.comp_injective Nat.cast_injective
  have hGneg : Summable fun n : ℕ => G (-((n : ℤ) + 1)) :=
    hGs.comp_injective (fun a b hab => by simpa using hab)
  rw [tsum_of_nat_of_neg_add_one hGnat hGneg]
  -- the nonnegative indices: only `n ≥ d` survive
  have hpos : ∑' n : ℕ, G n ≤ c / M * (1 / M ^ 2 + 1 / (h * M)) := by
    have hsplit := hGnat.sum_add_tsum_nat_add d
    have hzero : ∑ i ∈ Finset.range d, G i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [hG, Set.indicator_of_notMem]
      simp only [Set.mem_compl_iff, Finset.mem_coe, not_not, hS, Finset.mem_image]
      exact ⟨i, hi, rfl⟩
    rw [hzero, zero_add] at hsplit
    rw [← hsplit]
    have hle : ∀ m : ℕ, G ((m + d : ℕ) : ℤ) ≤ c / M * (1 / (M + m * h) ^ 2) := by
      intro m
      refine (Set.indicator_le_self' (fun k _ => hF0 k) _).trans ?_
      rw [add_comm m d]
      exact hright m
    have hT := tsum_inv_sq_grid_shift_le hM hh0
    have hs1 : Summable fun n : ℕ => (fun m : ℕ => 1 / (M + (m : ℝ) * h) ^ 2) (n + 1) :=
      hT.1.congr fun n => by push_cast; ring
    have hs : Summable fun m : ℕ => 1 / (M + (m : ℝ) * h) ^ 2 := (summable_nat_add_iff 1).mp hs1
    have hmaj : Summable fun m : ℕ => c / M * (1 / (M + m * h) ^ 2) := hs.mul_left (c / M)
    calc ∑' m : ℕ, G ((m + d : ℕ) : ℤ) ≤ ∑' m : ℕ, c / M * (1 / (M + m * h) ^ 2) :=
          (hGnat.comp_injective (add_left_injective d)).tsum_le_tsum hle hmaj
      _ = c / M * ∑' m : ℕ, 1 / (M + m * h) ^ 2 := tsum_mul_left
      _ ≤ c / M * (1 / M ^ 2 + 1 / (h * M)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hs.tsum_eq_zero_add]
          simp only [Nat.cast_zero, zero_mul, add_zero]
          have e : ∑' m : ℕ, 1 / (M + ((m + 1 : ℕ) : ℝ) * h) ^ 2
              = ∑' m : ℕ, 1 / (M + ((m : ℝ) + 1) * h) ^ 2 := by
            congr 1 with m; push_cast; ring
          rw [e]
          linarith [hT.2]
  have hneg : ∑' n : ℕ, G (-((n : ℤ) + 1)) ≤ c / M * (1 / (h * M)) := by
    have hle : ∀ n : ℕ, G (-((n : ℤ) + 1)) ≤ c / M * (1 / (M + (n + 1) * h) ^ 2) :=
      fun n => (Set.indicator_le_self' (fun k _ => hF0 k) _).trans (hleft n)
    have hT := tsum_inv_sq_grid_shift_le hM hh0
    calc ∑' n : ℕ, G (-((n : ℤ) + 1)) ≤ ∑' n : ℕ, c / M * (1 / (M + (n + 1) * h) ^ 2) :=
          hGneg.tsum_le_tsum hle (hT.1.mul_left _)
      _ = c / M * ∑' n : ℕ, 1 / (M + (n + 1) * h) ^ 2 := tsum_mul_left
      _ ≤ c / M * (1 / (h * M)) := mul_le_mul_of_nonneg_left hT.2 (by positivity)
  calc ∑' n : ℕ, G n + ∑' n : ℕ, G (-((n : ℤ) + 1))
      ≤ c / M * (1 / M ^ 2 + 1 / (h * M)) + c / M * (1 / (h * M)) := add_le_add hpos hneg
    _ = c * (1 / M ^ 3 + 2 / (h * M ^ 2)) := by field_simp; ring

end FejerWeight

end RHTower
