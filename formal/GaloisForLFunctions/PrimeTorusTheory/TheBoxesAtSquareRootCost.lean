import GaloisForLFunctions.PrimeTorusTheory.TheBoxesOfTheTorus
import Mathlib.NumberTheory.Chebyshev

/-!
# Boxes at square-root cost

The box theorem `exists_mem_box` bounds every nonzero frequency of the concentrated kernel by the largest integer of the kernel. That costs `exp(2m θ(y))` with `m ≍ log y/δ`, so `log T_mix ≲ y log y/δ`.

Most of the kernel's mass is at small frequencies. The frequency of a multi-index `κ` is `log(a/b)` with `ab = Π_p p^{|e_p − κ_p|}` (`gapOf`), so its window integral is at most `min(L, 2 ab)`, and `min(L, M) ≤ L^{1−λ} M^λ`. The binomial kernel has moment generating function `cosh(u/2)^{2e} ≤ exp(e u²/4)` (`sum_choose_div_exp_le`). So the error has the Chernoff form

`2 L^{1−λ} Π_p 2 exp(e_p λ² log² p/4)` (`abs_integral_boxWeight_sub_le_gap`),

and a window enters every box as soon as `log 8 + r log 8m + m λ² Σ_p log² p/2 < λ log L` (`exists_mem_box_gap`). With `r ≍ y/log y` (Chebyshev), `Σ_p log² p ≤ 1.4 y log y`, and the optimal `λ = √(δ log log y)/(log y)^{3/2}`:

**Theorem** (`eventually_exists_mem_box_sharp`). Every window of length `exp(10 y √(log y · log log y/δ))` enters every `δ`-box on the primes up to `y`.

The exponent drops from `y log y/δ` to `y √(log y log log y/δ)`. The bracket for the mixing time becomes `π(y) log 2 ≲ log T_mix ≲ 10 y √(log y log log y/δ)`, with a gap of `(log y)^{3/2} √(log log y)` instead of `(log y)²`. The remaining factor comes from the union bound `m ≍ log y/δ` and from `log 8m`, the cost of normalizing the kernel.
-/

open Complex Finset Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- Interpolation: `u ≤ A`, `u ≤ B` give `u ≤ A^{1−λ} B^λ`. -/
theorem le_rpow_mul_rpow {u A B l : ℝ} (hu : 0 ≤ u) (hA : u ≤ A) (hB : u ≤ B) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) : u ≤ A ^ (1 - l) * B ^ l := by
  have h : u ^ (1 - l) * u ^ l = u := by
    rw [← Real.rpow_add_of_nonneg hu (by linarith) hl0, sub_add_cancel, Real.rpow_one]
  calc u = u ^ (1 - l) * u ^ l := h.symm
    _ ≤ A ^ (1 - l) * B ^ l :=
      mul_le_mul (Real.rpow_le_rpow hu hA (by linarith)) (Real.rpow_le_rpow hu hB hl0)
        (Real.rpow_nonneg hu _) (Real.rpow_nonneg (hu.trans hA) _)

/-! ### The moment generating function of the kernel -/

theorem sum_choose_exp_eq (e : ℕ) (v : ℝ) :
    ∑ k ∈ range (2 * e + 1), ((2 * e).choose k : ℝ) * Real.exp (v * ((e : ℝ) - k)) =
      (Real.exp (-(v / 2)) + Real.exp (v / 2)) ^ (2 * e) := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ 2 * e := by
    have := Finset.mem_range.mp hk
    omega
  have e1 : Real.exp (-(v / 2)) ^ k * Real.exp (v / 2) ^ (2 * e - k) = Real.exp (v * ((e : ℝ) - k)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [Nat.cast_sub hk']
    push_cast
    ring
  rw [e1]
  ring

/-- The binomial kernel is sub-Gaussian: `Σ_k C(2e,k) 4^{−e} e^{v(e−k)} = cosh(v/2)^{2e} ≤ e^{e v²/4}`. -/
theorem sum_choose_div_exp_le (e : ℕ) (v : ℝ) :
    ∑ k ∈ range (2 * e + 1), ((2 * e).choose k : ℝ) / 4 ^ e * Real.exp (v * ((e : ℝ) - k)) ≤
      Real.exp (e * v ^ 2 / 4) := by
  have h1 : ∑ k ∈ range (2 * e + 1), ((2 * e).choose k : ℝ) / 4 ^ e * Real.exp (v * ((e : ℝ) - k)) =
      (∑ k ∈ range (2 * e + 1), ((2 * e).choose k : ℝ) * Real.exp (v * ((e : ℝ) - k))) / 4 ^ e := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h2 : (Real.exp (-(v / 2)) + Real.exp (v / 2)) ^ (2 * e) / 4 ^ e = Real.cosh (v / 2) ^ (2 * e) := by
    rw [Real.cosh_eq, div_pow, add_comm, pow_mul, pow_mul]
    norm_num
  rw [h1, sum_choose_exp_eq, h2]
  calc Real.cosh (v / 2) ^ (2 * e) ≤ Real.exp ((v / 2) ^ 2 / 2) ^ (2 * e) :=
        pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) _
    _ = Real.exp (e * v ^ 2 / 4) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-- The same with `|e − k|`: at most `2 e^{e u²/4}`. -/
theorem sum_choose_div_exp_abs_le (e : ℕ) (u : ℝ) :
    ∑ k ∈ range (2 * e + 1), ((2 * e).choose k : ℝ) / 4 ^ e *
      Real.exp (u * ((((e - k) + (k - e) : ℕ)) : ℝ)) ≤ 2 * Real.exp (e * u ^ 2 / 4) := by
  have hterm : ∀ k ∈ range (2 * e + 1), ((2 * e).choose k : ℝ) / 4 ^ e *
      Real.exp (u * ((((e - k) + (k - e) : ℕ)) : ℝ)) ≤
      ((2 * e).choose k : ℝ) / 4 ^ e * Real.exp (u * ((e : ℝ) - k)) +
        ((2 * e).choose k : ℝ) / 4 ^ e * Real.exp ((-u) * ((e : ℝ) - k)) := by
    intro k _
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rcases le_total k e with h | h
    · rw [show (e - k) + (k - e) = e - k by omega, Nat.cast_sub h]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [show (e - k) + (k - e) = k - e by omega, Nat.cast_sub h,
        show u * ((k : ℝ) - e) = (-u) * ((e : ℝ) - k) by ring]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib]
  have h1 := sum_choose_div_exp_le e u
  have h2 := sum_choose_div_exp_le e (-u)
  rw [neg_sq] at h2
  linarith

/-! ### The reduced integer gap -/

section Gap

variable {Y : Finset ℕ} (e : ℕ → ℕ)

/-- The modulus `Π_p p^{|e_p − κ_p|}` of a multi-index: the product of the two reduced integers whose ratio is its frequency. -/
def gapOf (e : ℕ → ℕ) (κ : Y → ℕ) : ℕ := ∏ i : Y, (i : ℕ) ^ ((e i - κ i) + (κ i - e i))

theorem log_prod_pow (hY : ∀ p ∈ Y, p.Prime) (f : Y → ℕ) :
    Real.log ((∏ i : Y, (i : ℕ) ^ f i : ℕ) : ℝ) = ∑ i : Y, (f i : ℝ) * Real.log (i : ℕ) := by
  push_cast
  rw [Real.log_prod fun i _ => pow_ne_zero _ (by exact_mod_cast (hY i i.2).ne_zero)]
  exact Finset.sum_congr rfl fun i _ => Real.log_pow _ _

/-- **The reduced gap.** Away from the exponent vector, the window integral of a frequency is at most `2 gapOf`. -/
theorem norm_integral_le_gap (hY : ∀ p ∈ Y, p.Prime) {κ : Y → ℕ} (hne : κ ≠ fun i : Y => e i)
    (T L : ℝ) :
    ‖∫ t in T..T + L, cexp (I * ((freqOf e κ : ℝ) * (t : ℝ)))‖ ≤ 2 * (gapOf e κ : ℝ) := by
  classical
  set a : ℕ := ∏ i : Y, (i : ℕ) ^ (e i - κ i) with ha
  set b : ℕ := ∏ i : Y, (i : ℕ) ^ (κ i - e i) with hb
  have hgap' : gapOf e κ = a * b := by
    unfold gapOf
    rw [ha, hb, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => pow_add _ _ _
  have hapos : 0 < a := Finset.prod_pos fun i _ => pow_pos (hY i i.2).pos _
  have hbpos : 0 < b := Finset.prod_pos fun i _ => pow_pos (hY i i.2).pos _
  have hneq : a ≠ b := by
    intro h
    refine hne (funext fun q => ?_)
    have h1 : a.factorization q = e q - κ q := factorization_prod_pow hY (fun i => e i - κ i) q
    have h2 : b.factorization q = κ q - e q := factorization_prod_pow hY (fun i => κ i - e i) q
    rw [h] at h1
    rw [h1] at h2
    show κ q = e q
    omega
  have hfreq : freqOf e κ = Real.log (a : ℝ) - Real.log (b : ℝ) := by
    rw [ha, hb, log_prod_pow hY, log_prod_pow hY]
    unfold freqOf
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases le_total (e i) (κ i) with h | h
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]
      push_cast
      ring
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]
      push_cast
      ring
  have hgap := HTGeometry.inv_max_le_abs_log_sub_log hapos hbpos hneq
  rw [← hfreq] at hgap
  have hmaxpos : (0 : ℝ) < ((max a b : ℕ) : ℝ) := by
    have : 0 < max a b := lt_max_of_lt_left hapos
    exact_mod_cast this
  have hγ : freqOf e κ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hgap
    exact absurd hgap (not_le.mpr (by positivity))
  have hI := TrigSum.norm_integral_exp_I_mul_le _ hγ T L
  refine hI.trans ?_
  have hmax : ((max a b : ℕ) : ℝ) ≤ gapOf e κ := by
    rw [hgap']
    exact_mod_cast max_le (Nat.le_mul_of_pos_right a hbpos) (Nat.le_mul_of_pos_left b hapos)
  have hpos : 0 < |freqOf e κ| := abs_pos.mpr hγ
  rw [div_le_iff₀ hpos]
  have h3 : (1 : ℝ) ≤ ((max a b : ℕ) : ℝ) * |freqOf e κ| := by
    have := mul_le_mul_of_nonneg_left hgap hmaxpos.le
    rwa [mul_inv_cancel₀ hmaxpos.ne'] at this
  nlinarith [abs_nonneg (freqOf e κ)]

/-- **The Chernoff sum.** `Σ_κ coeff(κ) gapOf(κ)^λ ≤ Π_p 2 exp(e_p λ² log² p/4)`. -/
theorem sum_coeffOf_mul_gap_rpow_le (hY : ∀ p ∈ Y, p.Prime) {l : ℝ} (hl : 0 ≤ l) :
    ∑ κ ∈ boxIndex Y e, coeffOf e κ * (gapOf e κ : ℝ) ^ l ≤
      ∏ p ∈ Y, 2 * Real.exp (e p * (l * Real.log p) ^ 2 / 4) := by
  classical
  have hterm : ∀ κ : Y → ℕ, coeffOf e κ * (gapOf e κ : ℝ) ^ l = ∏ i : Y,
      (((2 * e i).choose (κ i) : ℝ) / 4 ^ e i *
        Real.exp ((l * Real.log (i : ℕ)) * ((((e i - κ i) + (κ i - e i) : ℕ)) : ℝ))) := by
    intro κ
    have hg : (0 : ℝ) < gapOf e κ := by
      have : 0 < gapOf e κ := Finset.prod_pos fun i _ => pow_pos (hY i i.2).pos _
      exact_mod_cast this
    rw [Real.rpow_def_of_pos hg]
    unfold gapOf
    rw [log_prod_pow hY (fun i : Y => (e i - κ i) + (κ i - e i)), Finset.sum_mul, Real.exp_sum]
    unfold coeffOf
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 2
    ring
  rw [Finset.sum_congr rfl fun κ _ => hterm κ]
  unfold boxIndex
  rw [← Finset.prod_univ_sum (fun i : Y => range (2 * e i + 1))
    (fun i k => ((2 * e i).choose k : ℝ) / 4 ^ e i *
      Real.exp ((l * Real.log (i : ℕ)) * ((((e i - k) + (k - e i) : ℕ)) : ℝ))),
    ← Finset.prod_coe_sort Y (fun p => 2 * Real.exp (e p * (l * Real.log p) ^ 2 / 4))]
  refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun k _ => by positivity) fun i _ => ?_
  exact sum_choose_div_exp_abs_le (e i) (l * Real.log (i : ℕ))

/-- **The window integral at Chernoff cost.** -/
theorem abs_integral_boxWeight_sub_le_gap (hY : ∀ p ∈ Y, p.Prime) (θ : ℕ → ℝ) (T : ℝ) {L : ℝ}
    (hL : 0 < L) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    |(∫ t in T..T + L, boxWeight Y e θ t) - L * ∏ p ∈ Y, binomMean (e p)| ≤
      2 * (L ^ (1 - l) * ∏ p ∈ Y, 2 * Real.exp (e p * (l * Real.log p) ^ 2 / 4)) := by
  have h := abs_integral_boxWeight_sub_le_sum (Y := Y) e θ T L
    (fun κ => 2 * (L ^ (1 - l) * (gapOf e κ : ℝ) ^ l)) (fun κ => by positivity) fun κ _ hne => ?_
  · refine h.trans ?_
    have h1 : ∑ κ ∈ boxIndex Y e, coeffOf e κ * (2 * (L ^ (1 - l) * (gapOf e κ : ℝ) ^ l)) =
        2 * (L ^ (1 - l) * ∑ κ ∈ boxIndex Y e, coeffOf e κ * (gapOf e κ : ℝ) ^ l) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun κ _ => by ring
    rw [h1]
    have h2 := sum_coeffOf_mul_gap_rpow_le e hY hl0
    have h3 : 0 ≤ L ^ (1 - l) := Real.rpow_nonneg hL.le _
    nlinarith
  · have hA : ‖∫ t in T..T + L, cexp (I * ((freqOf e κ : ℝ) * (t : ℝ)))‖ ≤ L := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (a := T) (b := T + L)
        (f := fun t : ℝ => cexp (I * ((freqOf e κ : ℝ) * (t : ℝ)))) fun t _ => by
          rw [show I * ((freqOf e κ : ℂ) * (t : ℂ)) = ((freqOf e κ * t : ℝ) : ℂ) * I by push_cast; ring]
          exact (Complex.norm_exp_ofReal_mul_I _).le
      rwa [one_mul, add_sub_cancel_left, abs_of_pos hL] at h1
    have hB := norm_integral_le_gap e hY hne T L
    have h2 := le_rpow_mul_rpow (norm_nonneg _) hA hB hl0 hl1
    have h3 : (2 * (gapOf e κ : ℝ)) ^ l ≤ 2 * (gapOf e κ : ℝ) ^ l := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      have h4 : (2 : ℝ) ^ l ≤ 2 := by
        have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hl1
        rwa [Real.rpow_one] at this
      exact mul_le_mul_of_nonneg_right h4 (by positivity)
    calc ‖∫ t in T..T + L, cexp (I * ((freqOf e κ : ℝ) * (t : ℝ)))‖
        ≤ L ^ (1 - l) * (2 * (gapOf e κ : ℝ)) ^ l := h2
      _ ≤ L ^ (1 - l) * (2 * (gapOf e κ : ℝ) ^ l) := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hL.le _)
      _ = 2 * (L ^ (1 - l) * (gapOf e κ : ℝ) ^ l) := by ring

end Gap

/-! ### The box theorem at Chernoff cost -/

/-- **The box theorem at Chernoff cost.** A window of length `L` enters every `δ`-box on `Y` as soon as `log 8 + r log 8m + m λ² Σ_p log² p/2 < λ log L`. -/
theorem exists_mem_box_gap {Y : Finset ℕ} (hY : ∀ p ∈ Y, p.Prime) (θ : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m)
    {δ : ℝ} (hδ1 : δ < 1) (hc : 8 * (m : ℝ) * ((Y.card : ℝ) * (1 - δ) ^ m) ≤ 1) (T : ℝ)
    {L l : ℝ} (hL : 0 < L) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hlen : Real.log 8 + Y.card * Real.log (8 * m) + m * l ^ 2 * (∑ p ∈ Y, Real.log p ^ 2) / 2 <
      l * Real.log L) :
    ∃ t ∈ Set.Icc T (T + L), ∀ q ∈ Y, 1 - δ < bump (t * Real.log q - θ q) := by
  by_contra hcon
  push Not at hcon
  set P : ℝ := ∏ p ∈ Y, 2 * Real.exp (((2 * m : ℕ) : ℝ) * (l * Real.log p) ^ 2 / 4) with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun _ _ => by positivity
  have h1 := box_core θ hm hδ1 hc T hL (D := L ^ (1 - l) * P)
    (mul_nonneg (Real.rpow_nonneg hL.le _) hP0) (fun e he => ?_) hcon
  · have hsplit : L ^ (1 - l) * L ^ l = L := by
      rw [← Real.rpow_add hL, sub_add_cancel, Real.rpow_one]
    have hpos : 0 < L ^ (1 - l) := Real.rpow_pos_of_pos hL _
    have h2 : L ^ l ≤ 8 * (4 * (m : ℝ)) ^ Y.card * P := by
      have : L ^ (1 - l) * L ^ l ≤ L ^ (1 - l) * (8 * (4 * (m : ℝ)) ^ Y.card * P) := by
        rw [hsplit]
        calc L ≤ 8 * (4 * (m : ℝ)) ^ Y.card * (L ^ (1 - l) * P) := h1
          _ = L ^ (1 - l) * (8 * (4 * (m : ℝ)) ^ Y.card * P) := by ring
      exact le_of_mul_le_mul_left this hpos
    have hPe : P = 2 ^ Y.card * Real.exp (m * l ^ 2 * (∑ p ∈ Y, Real.log p ^ 2) / 2) := by
      rw [hP, Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
      congr 2
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun p _ => ?_
      push_cast
      ring
    have hm8 : (0 : ℝ) < 8 * m := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have h3 : 8 * (4 * (m : ℝ)) ^ Y.card * P = Real.exp (Real.log 8 + Y.card * Real.log (8 * m) +
        m * l ^ 2 * (∑ p ∈ Y, Real.log p ^ 2) / 2) := by
      have e1 : Real.exp (Y.card * Real.log (8 * m)) = (8 * (m : ℝ)) ^ Y.card := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hm8, mul_comm]
      rw [hPe, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), e1,
        show (8 * (m : ℝ)) ^ Y.card = 2 ^ Y.card * (4 * (m : ℝ)) ^ Y.card by rw [← mul_pow]; ring]
      ring
    have h4 : L ^ l = Real.exp (l * Real.log L) := by
      rw [Real.rpow_def_of_pos hL, mul_comm]
    rw [h3, h4] at h2
    exact absurd (Real.exp_le_exp.mp h2) (not_le.mpr hlen)
  · refine (abs_integral_boxWeight_sub_le_gap e hY θ T hL hl0 hl1).trans ?_
    rw [hP]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.prod_le_prod
      (fun p _ => by positivity) fun p _ => ?_) (Real.rpow_nonneg hL.le _)) (by norm_num)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    have h5 : (e p : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast he p
    have h6 := mul_le_mul_of_nonneg_right h5 (sq_nonneg (l * Real.log p))
    linarith

/-! ### The scale -/

theorem card_primesUpTo_eq (y : ℕ) : (primesUpTo y).card = Nat.primeCounting y := by
  unfold primesUpTo Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]

/-- `Σ_{p ≤ y} log² p ≤ 1.4 y log y`. -/
theorem sum_log_sq_le (y : ℕ) :
    ∑ p ∈ primesUpTo y, Real.log p ^ 2 ≤ 1.4 * y * Real.log y := by
  have hθ : ∑ p ∈ primesUpTo y, Real.log p ≤ y * Real.log 4 := by
    have h := boxModulus_primesUpTo_le y 1
    have e : Real.log (boxModulus (primesUpTo y) 1 : ℝ) = ∑ p ∈ primesUpTo y, Real.log p := by
      unfold boxModulus
      push_cast
      rw [Real.log_prod fun p hp => pow_ne_zero _ (by exact_mod_cast (prime_of_mem_primesUpTo hp).ne_zero)]
      simp
    rw [← e]
    have hpos : (0 : ℝ) < boxModulus (primesUpTo y) 1 := by
      exact_mod_cast Finset.prod_pos fun p hp => pow_pos (prime_of_mem_primesUpTo hp).pos _
    have h2 : (boxModulus (primesUpTo y) 1 : ℝ) ≤ (4 : ℝ) ^ (1 * y) := by exact_mod_cast h
    refine (Real.log_le_log hpos h2).trans (le_of_eq ?_)
    rw [Real.log_pow]
    push_cast
    ring
  have h4 : Real.log 4 ≤ 1.4 := by
    have e : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [e, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have hℓ : 0 ≤ Real.log y := Real.log_natCast_nonneg y
  have hterm : ∀ p ∈ primesUpTo y, Real.log p ^ 2 ≤ Real.log y * Real.log p := by
    intro p hp
    have hp0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hpy : Real.log p ≤ Real.log y := Real.log_le_log
      (by exact_mod_cast (prime_of_mem_primesUpTo hp).pos) (by exact_mod_cast le_of_mem_primesUpTo hp)
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have h5 : Real.log y * ∑ p ∈ primesUpTo y, Real.log p ≤ Real.log y * (y * Real.log 4) :=
    mul_le_mul_of_nonneg_left hθ hℓ
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have h6 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hℓ hy0)
  linarith

/-- The arithmetic of the length at `λ = √(δ ℓ'/ℓ³)`: the three terms cost `2.1 + 6w + 2.8w < 10w`, `w = y ℓ'/ℓ ≥ 12`. -/
theorem sharp_length_algebra {δ ℓ ℓ' y r m S l a : ℝ} (hδ0 : 0 < δ) (hℓ0 : 0 < ℓ) (hℓ'1 : 1 ≤ ℓ')
    (hy : 12 * ℓ ≤ y) (hr : r ≤ 3 * y / ℓ) (ha0 : 0 ≤ a) (ha : a ≤ 2 * ℓ') (hm : m ≤ 4 * ℓ / δ)
    (hS0 : 0 ≤ S) (hS : S ≤ 1.4 * y * ℓ) (hl2 : l ^ 2 = δ * ℓ' / ℓ ^ 3) :
    Real.log 8 + r * a + m * l ^ 2 * S / 2 < 10 * (y * ℓ' / ℓ) := by
  set w : ℝ := y * ℓ' / ℓ with hw
  have hy0 : 0 ≤ y := by linarith
  have h8 : Real.log 8 ≤ 2.1 := by
    have e : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [e, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have hT2 : r * a ≤ 6 * w := by
    calc r * a ≤ (3 * y / ℓ) * a := mul_le_mul_of_nonneg_right hr ha0
      _ ≤ (3 * y / ℓ) * (2 * ℓ') := mul_le_mul_of_nonneg_left ha (by positivity)
      _ = 6 * w := by rw [hw]; ring
  have hT3 : m * l ^ 2 * S / 2 ≤ 2.8 * w := by
    have hmS : m * S ≤ (4 * ℓ / δ) * (1.4 * y * ℓ) := by
      calc m * S ≤ (4 * ℓ / δ) * S := mul_le_mul_of_nonneg_right hm hS0
        _ ≤ (4 * ℓ / δ) * (1.4 * y * ℓ) := mul_le_mul_of_nonneg_left hS (by positivity)
    have h1 := mul_le_mul_of_nonneg_right hmS (sq_nonneg l)
    have e : (4 * ℓ / δ) * (1.4 * y * ℓ) * l ^ 2 / 2 = 2.8 * w := by
      rw [hl2, hw]
      field_simp
      ring
    calc m * l ^ 2 * S / 2 = m * S * l ^ 2 / 2 := by ring
      _ ≤ (4 * ℓ / δ) * (1.4 * y * ℓ) * l ^ 2 / 2 := by linarith
      _ = 2.8 * w := e
  have hw12 : 12 ≤ w := by
    rw [hw, le_div_iff₀ hℓ0]
    have := mul_le_mul_of_nonneg_left hℓ'1 hy0
    linarith
  linarith

/-- **The scale of the boxes at square-root cost.** Every window of length `exp(10 y √(log y · log log y/δ))` enters every `δ`-box on the primes up to `y`. -/
theorem eventually_exists_mem_box_sharp {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y → ∀ (θ : ℕ → ℝ) (T : ℝ),
      ∃ t ∈ Set.Icc T (T + Real.exp (10 * y * √(Real.log y * Real.log (Real.log y) / δ))),
        ∀ q ∈ primesUpTo y, 1 - δ < bump (t * Real.log q - θ q) := by
  have hev : ∀ᶠ Y : ℝ in atTop, (4 ≤ Real.log Y ∧ 4 * (3 * Real.log Y / δ + 1) ≤ Y ∧
      8 * (3 * Real.log Y / δ + 1) ≤ Y ^ 2 ∧ 1 ≤ Y) ∧
      (Nat.primeCounting ⌊Y⌋₊ : ℝ) ≤ (Real.log 4 + 1) * Y / Real.log Y ∧
      24 / δ + 8 ≤ Real.log Y ∧ Real.exp 1 ≤ Real.log Y :=
    (eventually_box_conditions hδ0).and ((Chebyshev.eventually_primeCounting_le one_pos).and
      ((Real.tendsto_log_atTop.eventually_ge_atTop _).and
        (Real.tendsto_log_atTop.eventually_ge_atTop _)))
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨y₀, fun y hy θ T => ?_⟩
  obtain ⟨⟨hℓ4, hY4, hY8, hY1⟩, hπ, hℓδ, hℓe⟩ := hy₀ y hy
  rw [Nat.floor_natCast] at hπ
  obtain ⟨m, hmpos, hm2, hc⟩ := box_tail_condition hδ0 hδ1 hℓ4 hY8 hY1
  set ℓ : ℝ := Real.log y with hℓdef
  set ℓ' : ℝ := Real.log ℓ with hℓ'def
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ'1 : 1 ≤ ℓ' := by
    have := Real.log_le_log (Real.exp_pos 1) hℓe
    rwa [Real.log_exp] at this
  have hℓ'ℓ : ℓ' ≤ ℓ := Real.log_le_self hℓ0.le
  have hy1 : 1 ≤ y := by exact_mod_cast hY1
  have hYpos : (0 : ℝ) < y := by linarith
  -- The parameter `λ = √(δ ℓ'/ℓ³)`.
  set l : ℝ := √(δ * ℓ' / ℓ ^ 3) with hl
  have hq0 : 0 ≤ δ * ℓ' / ℓ ^ 3 := by positivity
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  have hl1 : l ≤ 1 := by
    have h1 : δ * ℓ' / ℓ ^ 3 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have h2 : δ * ℓ' ≤ ℓ := by
        have := mul_le_mul_of_nonneg_right hδ1.le (show (0 : ℝ) ≤ ℓ' by linarith)
        linarith
      have h3 : ℓ ≤ ℓ ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
      linarith
    exact (Real.sqrt_le_sqrt h1).trans_eq Real.sqrt_one
  have hl2 : l ^ 2 = δ * ℓ' / ℓ ^ 3 := Real.sq_sqrt hq0
  set L : ℝ := Real.exp (10 * y * √(ℓ * ℓ' / δ)) with hLdef
  have hL : 0 < L := Real.exp_pos _
  have hcard : ((primesUpTo y).card : ℝ) ≤ y := by exact_mod_cast card_primesUpTo_le y
  refine exists_mem_box_gap (fun p hp => prime_of_mem_primesUpTo hp) θ hmpos hδ1 ?_ T hL hl0 hl1 ?_
  · refine le_trans ?_ hc
    have h0 : 0 ≤ (1 - δ) ^ m := pow_nonneg (by linarith) _
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard h0) (by positivity)
  · -- `λ log L = 10 y ℓ'/ℓ`.
    have hlogL : l * Real.log L = 10 * (y * ℓ' / ℓ) := by
      rw [hLdef, Real.log_exp, hl]
      have h1 : √(δ * ℓ' / ℓ ^ 3) * √(ℓ * ℓ' / δ) = ℓ' / ℓ := by
        rw [← Real.sqrt_mul hq0]
        have e : δ * ℓ' / ℓ ^ 3 * (ℓ * ℓ' / δ) = (ℓ' / ℓ) ^ 2 := by
          field_simp
        rw [e, Real.sqrt_sq (by positivity)]
      calc √(δ * ℓ' / ℓ ^ 3) * (10 * y * √(ℓ * ℓ' / δ))
          = 10 * y * (√(δ * ℓ' / ℓ ^ 3) * √(ℓ * ℓ' / δ)) := by ring
        _ = 10 * (y * ℓ' / ℓ) := by rw [h1]; ring
    rw [hlogL]
    have h4 : Real.log 4 ≤ 1.4 := by
      have e : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [e, Real.log_pow]
      have := Real.log_two_lt_d9
      push_cast
      linarith
    have hr : ((primesUpTo y).card : ℝ) ≤ 3 * y / ℓ := by
      rw [card_primesUpTo_eq]
      refine hπ.trans ?_
      rw [div_le_div_iff_of_pos_right hℓ0]
      have := mul_le_mul_of_nonneg_right (show Real.log 4 + 1 ≤ 3 by linarith) hYpos.le
      linarith
    have hℓδ1 : 1 ≤ ℓ / δ := by
      rw [le_div_iff₀ hδ0]
      linarith
    have hm4 : (m : ℝ) ≤ 4 * ℓ / δ := by
      have e : 4 * ℓ / δ = 3 * ℓ / δ + ℓ / δ := by ring
      linarith
    have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
    have hlog8m : Real.log (8 * m) ≤ 2 * ℓ' := by
      have h1 : 8 * (m : ℝ) ≤ ℓ ^ 2 := by
        have h3 : 24 * ℓ / δ + 8 ≤ ℓ ^ 2 := by
          have h5 : 24 * ℓ / δ = (24 / δ) * ℓ := by ring
          have h6 := mul_le_mul_of_nonneg_right hℓδ hℓ0.le
          have h7 : 8 ≤ 8 * ℓ := by linarith
          rw [h5]
          nlinarith
        have e : 8 * (3 * ℓ / δ + 1) = 24 * ℓ / δ + 8 := by ring
        linarith
      have := Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at this
      push_cast at this
      exact this
    have hlog8m0 : 0 ≤ Real.log (8 * m) := Real.log_nonneg (by linarith)
    have h12 : 12 * ℓ ≤ y := by
      have h1 : 12 * ℓ / δ ≤ y := by
        have : 4 * (3 * ℓ / δ + 1) = 12 * ℓ / δ + 4 := by ring
        linarith
      have h2 : 12 * ℓ ≤ 12 * ℓ / δ := by
        rw [le_div_iff₀ hδ0]
        have := mul_le_mul_of_nonneg_left hδ1.le (show (0 : ℝ) ≤ 12 * ℓ by linarith)
        linarith
      linarith
    exact sharp_length_algebra hδ0 hℓ0 hℓ'1 h12 hr hlog8m0 hlog8m hm4
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sum_log_sq_le y) hl2

end

end GaloisForLFunctions.PrimeTorusTheory
