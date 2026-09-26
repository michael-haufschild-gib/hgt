import GaloisForLFunctions.RHTower.SelbergNearLineGaussianField

/-!
# The Möbius-mollified zeta function beyond its constant term

Let `M_X(s) = Σ_{n ≤ X} μ(n) n^{-s}`. On `Re s > 1` the Dirichlet coefficients of `ζ M_X` are
`Σ_{d ∣ n, d ≤ X} μ(d)`, which equal `[n = 1]` for `n ≤ X` (every divisor of `n ≤ X` is `≤ X`) and
are at most `d(n) ≤ n` in size. So `ζ M_X − 1` has no Dirichlet coefficients below `X` at all:

`‖ζ M_X − 1‖ ≤ 2/X` on `Re s ≥ 3` (`norm_mobMollifiedError_le`).

The pole-cleared field `((z−1)/z)(ζ M_X − 1)` (`mobField`) is holomorphic on `Re z > 0` and grows
at most linearly on `1/4 ≤ Re z ≤ 3`: `‖mobField X z‖ ≤ C X (1 + |Im z|)`
(`exists_norm_mobField_le`).
-/

noncomputable section

open Complex

namespace RHTower

/-- The Möbius coefficients as complex numbers. -/
def mobCoeff (n : ℕ) : ℂ := ((ArithmeticFunction.moebius n : ℤ) : ℂ)

theorem norm_mobCoeff_le (n : ℕ) : ‖mobCoeff n‖ ≤ 1 := by
  unfold mobCoeff
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

theorem mobCoeff_one : mobCoeff 1 = 1 := by
  simp [mobCoeff]

theorem conj_mobCoeff (n : ℕ) : (starRingEnd ℂ) (mobCoeff n) = mobCoeff n := by
  simp [mobCoeff]

theorem sum_divisors_mobCoeff (n : ℕ) :
    ∑ d ∈ n.divisors, mobCoeff d = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (f := (ArithmeticFunction.moebius : ArithmeticFunction ℤ))
    (x := n)
  rw [ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply] at h
  unfold mobCoeff
  rw [← Int.cast_sum, ← h]
  split_ifs <;> simp

theorem norm_cutIcc_mobCoeff_le (X n : ℕ) : ‖cutIcc X mobCoeff n‖ ≤ 1 := by
  unfold cutIcc
  split_ifs
  · exact norm_mobCoeff_le n
  · simp

theorem convolution_one_cutIcc_mobCoeff_of_le {X n : ℕ} (hn : n ≤ X) :
    LSeries.convolution 1 (cutIcc X mobCoeff) n = if n = 1 then 1 else 0 := by
  simp only [LSeries.convolution_def]
  rw [Nat.sum_divisorsAntidiagonal' (fun x y => (1 : ℕ → ℂ) x * cutIcc X mobCoeff y)]
  simp only [Pi.one_apply, one_mul]
  rw [← sum_divisors_mobCoeff]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  have hdn : d ≤ n := Nat.divisor_le hd
  unfold cutIcc
  rw [if_pos (Finset.mem_Icc.mpr ⟨hd1, hdn.trans hn⟩)]

theorem norm_convolution_one_cutIcc_mobCoeff_le (X n : ℕ) :
    ‖LSeries.convolution 1 (cutIcc X mobCoeff) n‖ ≤ n := by
  simp only [LSeries.convolution_def]
  rw [Nat.sum_divisorsAntidiagonal' (fun x y => (1 : ℕ → ℂ) x * cutIcc X mobCoeff y)]
  simp only [Pi.one_apply, one_mul]
  calc ‖∑ d ∈ n.divisors, cutIcc X mobCoeff d‖
      ≤ ∑ d ∈ n.divisors, ‖cutIcc X mobCoeff d‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := Finset.sum_le_sum fun d _ => norm_cutIcc_mobCoeff_le X d
    _ = n.divisors.card := by simp
    _ ≤ n := by exact_mod_cast Nat.card_divisors_le_self n

/-- The coefficients of `ζ M_X − 1`. -/
def mobTailCoeff (X : ℕ) : ℕ → ℂ :=
  LSeries.convolution 1 (cutIcc X mobCoeff) - LSeries.delta

theorem mobTailCoeff_eq_zero_of_le {X n : ℕ} (hn : n ≤ X) : mobTailCoeff X n = 0 := by
  unfold mobTailCoeff
  simp only [Pi.sub_apply]
  rw [convolution_one_cutIcc_mobCoeff_of_le hn]
  simp [LSeries.delta]

theorem norm_mobTailCoeff_le {X n : ℕ} (hX : 1 ≤ X) (hn : X < n) : ‖mobTailCoeff X n‖ ≤ n := by
  unfold mobTailCoeff
  simp only [Pi.sub_apply]
  have h1 : LSeries.delta n = 0 := by
    simp only [LSeries.delta]
    rw [if_neg (by omega)]
  rw [h1, sub_zero]
  exact norm_convolution_one_cutIcc_mobCoeff_le X n

/-- **A Dirichlet series without coefficients up to `N`**, with `|c_n| ≤ n`, is at most `2/N` on
`Re s ≥ 3`. -/
theorem norm_LSeries_le_of_vanishing_head {c : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hzero : ∀ n, n ≤ N → c n = 0) (hbound : ∀ n, N < n → ‖c n‖ ≤ n) {s : ℂ} (hs : 3 ≤ s.re) :
    ‖LSeries c s‖ ≤ 2 / N := by
  set g : ℕ → ℝ := fun n => if N < n then (((n : ℝ) ^ 2)⁻¹) else 0 with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [hg]; split_ifs <;> positivity
  have hterm : ∀ n : ℕ, ‖LSeries.term c s n‖ ≤ g n := by
    intro n
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [if_pos h0]
      exact hg0 n
    · rw [if_neg hpos.ne']
      by_cases hNn : N < n
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        have hc := hbound n hNn
        have hpow : (n : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) ^ s.re :=
          Real.rpow_le_rpow_of_exponent_le hn1 hs
        have hpow3 : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ 3 := by
          exact_mod_cast Real.rpow_natCast (n : ℝ) 3
        have hgn : g n = ((n : ℝ) ^ 2)⁻¹ := by simp only [hg, if_pos hNn]
        rw [hgn, div_le_iff₀ (by positivity)]
        calc ‖c n‖ ≤ n := hc
          _ = ((n : ℝ) ^ 2)⁻¹ * (n : ℝ) ^ 3 := by field_simp
          _ ≤ ((n : ℝ) ^ 2)⁻¹ * (n : ℝ) ^ s.re := by
              rw [← hpow3]
              exact mul_le_mul_of_nonneg_left hpow (by positivity)
      · rw [hzero n (not_lt.mp hNn), norm_zero, zero_div]
        exact hg0 n
  have hgsum : Summable g := by
    refine Summable.of_nonneg_of_le hg0 (fun n => ?_)
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simp only [hg]
    split_ifs
    · rw [one_div]
    · positivity
  have htsum : ∑' n, g n ≤ 2 / N := by
    refine hgsum.tsum_le_of_sum_le fun S => ?_
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n ∈ S, n < M := ⟨S.sup id + 1, fun n hn =>
      Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
    calc ∑ n ∈ S, g n ≤ ∑ n ∈ Finset.range M, g n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => Finset.mem_range.mpr (hM n hn))
            fun n _ _ => hg0 n
      _ = ∑ n ∈ Finset.Ioo N M, ((n : ℝ) ^ 2)⁻¹ := by
          rw [← Finset.sum_filter_add_sum_filter_not (Finset.range M) (fun n => N < n)]
          have h1 : ∑ n ∈ (Finset.range M).filter (fun n => ¬ N < n), g n = 0 :=
            Finset.sum_eq_zero fun n hn => by
              simp only [hg, if_neg (Finset.mem_filter.mp hn).2]
          rw [h1, add_zero]
          have hset : (Finset.range M).filter (fun n => N < n) = Finset.Ioo N M := by
            ext n
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
            tauto
          rw [hset]
          refine Finset.sum_congr rfl fun n hn => ?_
          simp only [hg, if_pos (Finset.mem_Ioo.mp hn).1]
      _ ≤ 2 / ((N : ℝ) + 1) := sum_Ioo_inv_sq_le N M
      _ ≤ 2 / N := by
          have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
          exact div_le_div_of_nonneg_left (by norm_num) hN0 (by linarith)
  have hsumnorm : Summable fun n => ‖LSeries.term c s n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hgsum
  calc ‖LSeries c s‖ ≤ ∑' n, ‖LSeries.term c s n‖ := norm_tsum_le_tsum_norm hsumnorm
    _ ≤ ∑' n, g n := hsumnorm.tsum_le_tsum hterm hgsum
    _ ≤ 2 / N := htsum

/-- The mollified error `ζ M_X − 1`. -/
def mobMollifiedError (X : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * edPoly mobCoeff (Finset.Icc 1 X) s - 1

theorem mobMollifiedError_eq_LSeries (X : ℕ) {s : ℂ} (hs : 1 < s.re) :
    mobMollifiedError X s = LSeries (mobTailCoeff X) s := by
  have hsum1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  have hsumM : LSeriesSummable (cutIcc X mobCoeff) s :=
    Sieve.LSeriesSummable_of_support (fun k hk => cutIcc_support hk) s
  have hsumδ : LSeriesSummable LSeries.delta s :=
    Sieve.LSeriesSummable_of_support (s := {1}) (fun k hk => by
      simp only [LSeries.delta] at hk
      split_ifs at hk with h
      · simp [h]
      · exact absurd rfl hk) s
  have hconv : LSeriesSummable (LSeries.convolution 1 (cutIcc X mobCoeff)) s :=
    hsum1.convolution hsumM
  unfold mobMollifiedError mobTailCoeff
  rw [LSeries_sub hconv hsumδ, LSeries_convolution' hsum1 hsumM, LSeries_one_eq_riemannZeta hs,
    LSeries_delta, edPoly_Icc_eq_LSeries]
  rfl

/-- **`ζ M_X − 1` is `O(1/X)` on `Re s ≥ 3`.** -/
theorem norm_mobMollifiedError_le {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 3 ≤ s.re) :
    ‖mobMollifiedError X s‖ ≤ 2 / X := by
  rw [mobMollifiedError_eq_LSeries X (by linarith)]
  exact norm_LSeries_le_of_vanishing_head hX (fun n hn => mobTailCoeff_eq_zero_of_le hn)
    (fun n hn => norm_mobTailCoeff_le hX hn) hs

/-- `‖M_X(s)‖ ≤ X` on `Re s ≥ 0`. -/
theorem norm_edPoly_mobCoeff_le (X : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖edPoly mobCoeff (Finset.Icc 1 X) s‖ ≤ X := by
  unfold edPoly
  calc ‖∑ n ∈ Finset.Icc 1 X, mobCoeff n * ((n : ℝ) : ℂ) ^ (-s)‖
      ≤ ∑ n ∈ Finset.Icc 1 X, ‖mobCoeff n * ((n : ℝ) : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
        have h1 : (n : ℝ) ^ (-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
        calc ‖mobCoeff n‖ * (n : ℝ) ^ (-s.re) ≤ 1 * 1 :=
              mul_le_mul (norm_mobCoeff_le n) h1 (by positivity) zero_le_one
          _ = 1 := one_mul 1
    _ = X := by simp

/-- The pole-cleared mollified error `((z−1)/z)(ζ M_X − 1)`. -/
def mobField (X : ℕ) (z : ℂ) : ℂ :=
  (zetaEntire z * edPoly mobCoeff (Finset.Icc 1 X) z - (z - 1)) / z

theorem mobField_eq {X : ℕ} {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    mobField X z = (z - 1) / z * mobMollifiedError X z := by
  unfold mobField mobMollifiedError
  rw [zetaEntire_eq hz1]
  field_simp

theorem differentiableOn_mobField (X : ℕ) :
    DifferentiableOn ℂ (mobField X) {z | 0 < z.re} := by
  intro z hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hs : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.div _ differentiableAt_id hz0
  exact ((differentiable_zetaEntire z).mul (differentiable_edPoly _ hs z)).sub
    (differentiableAt_id.sub_const 1)

/-- `|z/(z−1)|² ≤ 2` on `1/2 ≤ Re z ≤ 1`, `|Im z| ≥ 1`: the error is controlled by the field. -/
theorem norm_mobMollifiedError_sq_le_two_mul {X : ℕ} {z : ℂ} (hz : 1 / 2 ≤ z.re) (hz' : z.re ≤ 1)
    (him : 1 ≤ |z.im|) :
    ‖mobMollifiedError X z‖ ^ 2 ≤ 2 * ‖mobField X z‖ ^ 2 := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz; linarith
  have hz1 : z ≠ 1 := fun h => by simp [h] at him; linarith
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [mobField_eq hz0 hz1, norm_mul, mul_pow, norm_div]
  have h1 : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have h2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hpos1 : 0 < ‖z - 1‖ := norm_pos_iff.mpr hsub
  have hpos0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have him2 : 1 ≤ z.im ^ 2 := by
    have := sq_abs z.im
    nlinarith [abs_nonneg z.im]
  have hratio : ‖z‖ ^ 2 ≤ 2 * ‖z - 1‖ ^ 2 := by
    rw [h1, h2]
    nlinarith
  rw [div_pow]
  have hT := sq_nonneg ‖mobMollifiedError X z‖
  rw [show 2 * (‖z - 1‖ ^ 2 / ‖z‖ ^ 2 * ‖mobMollifiedError X z‖ ^ 2) =
      (2 * ‖z - 1‖ ^ 2) / ‖z‖ ^ 2 * ‖mobMollifiedError X z‖ ^ 2 by ring]
  have hge : 1 ≤ (2 * ‖z - 1‖ ^ 2) / ‖z‖ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  nlinarith

/-- **Linear growth of the pole-cleared error on the strip `1/4 ≤ Re z ≤ 3`.** -/
theorem exists_norm_mobField_le :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X → ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 →
      ‖mobField X z‖ ≤ C * X * (1 + |z.im|) := by
  set K : Set ℂ := (Set.Icc (1 / 4 : ℝ) 3) ×ℂ (Set.Icc (-2 : ℝ) 2) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨CZ, hCZ⟩ := hKc.exists_bound_of_continuousOn
    (differentiable_zetaEntire.continuous.continuousOn (s := K))
  set CZ' : ℝ := max CZ 0 with hCZ'
  refine ⟨max 16 (4 * (CZ' + 8)), by positivity, fun X hX z hz hz' => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hΨ := norm_edPoly_mobCoeff_le X (s := z) (by linarith)
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz; linarith
  have habs : 0 ≤ |z.im| := abs_nonneg _
  rcases le_or_gt 2 |z.im| with him | him
  · have hz1 : z ≠ 1 := fun h => by simp [h] at him; linarith
    rw [mobField_eq hz0 hz1, norm_mul]
    have hfac : ‖(z - 1) / z‖ ≤ 2 := by
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hz0)]
      have h1 : ‖z - 1‖ ≤ ‖z‖ + 1 := by
        have := norm_sub_le z 1
        simpa using this
      have h2 : 2 ≤ ‖z‖ := le_trans him (Complex.abs_im_le_norm z)
      linarith
    have hζ := norm_riemannZeta_le_quarter hz him
    have hf : ‖mobMollifiedError X z‖ ≤ 8 * X * (1 + |z.im|) := by
      unfold mobMollifiedError
      calc ‖riemannZeta z * edPoly mobCoeff (Finset.Icc 1 X) z - 1‖
          ≤ ‖riemannZeta z‖ * ‖edPoly mobCoeff (Finset.Icc 1 X) z‖ + 1 := by
            have h2 := norm_sub_le (riemannZeta z * edPoly mobCoeff (Finset.Icc 1 X) z) 1
            rw [norm_mul, norm_one] at h2
            linarith
        _ ≤ (2 + 8 * |z.im|) * X + 1 := by
            have := mul_le_mul hζ hΨ (norm_nonneg _) (by positivity)
            linarith
        _ ≤ 8 * X * (1 + |z.im|) := by nlinarith
    calc ‖(z - 1) / z‖ * ‖mobMollifiedError X z‖ ≤ 2 * (8 * X * (1 + |z.im|)) :=
          mul_le_mul hfac hf (norm_nonneg _) (by norm_num)
      _ = 16 * X * (1 + |z.im|) := by ring
      _ ≤ max 16 (4 * (CZ' + 8)) * X * (1 + |z.im|) := by
          gcongr
          exact le_max_left _ _
  · have hmem : z ∈ K := by
      rw [hK]
      refine ⟨⟨hz, hz'⟩, ?_⟩
      have := abs_lt.mp him
      exact ⟨by linarith, by linarith⟩
    have hZ : ‖zetaEntire z‖ ≤ CZ' := (hCZ z hmem).trans (le_max_left _ _)
    have hz1n : ‖z - 1‖ ≤ 4 := by
      have h := norm_le_abs_re_add_abs_im (z - 1)
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h
      have : |z.re - 1| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have hzn : 1 / 4 ≤ ‖z‖ := le_trans hz (Complex.re_le_norm z)
    unfold mobField
    rw [norm_div, div_le_iff₀ (by linarith)]
    calc ‖zetaEntire z * edPoly mobCoeff (Finset.Icc 1 X) z - (z - 1)‖
        ≤ ‖zetaEntire z‖ * ‖edPoly mobCoeff (Finset.Icc 1 X) z‖ + ‖z - 1‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ CZ' * X + 4 := by
          have hCZ0 : 0 ≤ CZ' := le_max_right _ _
          have h1 := mul_le_mul hZ hΨ (norm_nonneg _) hCZ0
          linarith
      _ ≤ (CZ' + 8) * X := by nlinarith
      _ ≤ max 16 (4 * (CZ' + 8)) * X * (1 + |z.im|) * ‖z‖ := by
          have hmax : 4 * (CZ' + 8) ≤ max 16 (4 * (CZ' + 8)) := le_max_right _ _
          have hCZ0 : 0 ≤ CZ' := le_max_right _ _
          have hX0 : (0 : ℝ) ≤ X := by linarith
          have e1 : (CZ' + 8) * X = (4 * (CZ' + 8)) * X * 1 * (1 / 4) := by ring
          rw [e1]
          gcongr
          linarith

/-- The pole-cleared error on the edge `Re z = 3` is at most `2/X`. -/
theorem norm_mobField_three_le {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    ‖mobField X ((3 : ℂ) + (t : ℂ) * I)‖ ≤ 2 / X := by
  set z : ℂ := (3 : ℂ) + (t : ℂ) * I with hzdef
  have hre : z.re = 3 := by simp [hzdef]
  have hz0 : z ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hz1 : z ≠ 1 := fun h => by rw [h] at hre; simp at hre
  rw [mobField_eq hz0 hz1, norm_mul]
  have h1 := norm_sub_one_div_le_one (z := z) (by rw [hre]; norm_num)
  have h2 := norm_mobMollifiedError_le hX (s := z) (by rw [hre])
  calc ‖(z - 1) / z‖ * ‖mobMollifiedError X z‖ ≤ 1 * (2 / X) :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 2 / X := one_mul _

end RHTower
