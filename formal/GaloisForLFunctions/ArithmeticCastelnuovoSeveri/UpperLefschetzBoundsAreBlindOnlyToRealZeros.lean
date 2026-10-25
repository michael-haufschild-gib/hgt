import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFirstNegativeLagOfACurve
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhichArithmeticDataForceTheSign

/-!
# Upper Lefschetz bounds are blind only to real zeros

Bombieri's proof of the Riemann hypothesis for curves needs an *upper* bound for point counts at
square-root precision. On a curve datum the two one-sided Lefschetz bounds behave differently:

* the lower bound `N_k ≥ q^k + 1 − C q^{k/2}`, i.e. `trace k ≤ C`, forces unitarity
  (`CurveDatum.unitary_of_trace_le`);
* the upper bound `N_k ≤ q^k + 1 + C q^{k/2}`, i.e. `trace k ≥ −C`, forces unitarity unless some
  outer eigenvalue is a positive real number, i.e. the datum has a real zero right of the line
  (`CurveDatum.unitary_of_neg_le_trace`, `CurveDatum.oneSided_forcing_tfae`).

Both come from one statement on finite exponential sums. If the members of maximal modulus `A`
are `A w_i` with `|w_i| = 1`, the window mean of `Re Σ w_i^k` is `#{w_i = 1}` and its mean square
is at least `#J/2`; so `Re Σ w_i^k > 1/8` infinitely often, and `< −1/8` infinitely often when no
`w_i` equals `1` (`exists_lt_re_powerSum`, `exists_re_powerSum_lt`).

The golden fake curve satisfies the upper bound with `C = 0`; its outer eigenvalue `φ` is real
(`goldenDatum_upper_lefschetz_bound_and_real_zero`). On the scaling surface of a curve the lag
tests `g ∓ g(· − n log q)` read the two sides separately: difference tests are all Weil-nonnegative
iff the curve is pure; sum tests detect every impure curve without a real outer eigenvalue and
are all nonnegative on the golden curve (`CurveDatum.differenceLagTests_nonneg_iff_unitary`,
`CurveDatum.sumLagTests_nonneg_iff_unitary`, `goldenDatum_sumLagTests_nonneg`).
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

noncomputable section

/-! ### 1. Window sums of unimodular powers -/

/-- The error constant `2/‖u − 1‖` of a window sum of powers of `u`; `0` at `u = 1`. -/
def windowConst (u : ℂ) : ℝ := if u = 1 then 0 else 2 / ‖u - 1‖

theorem windowConst_nonneg (u : ℂ) : 0 ≤ windowConst u := by
  unfold windowConst; split_ifs <;> positivity

/-- A window sum of `Re u^k`, `‖u‖ = 1`, equals `N` if `u = 1` and `0` otherwise, up to
`windowConst u` (geometric summation). -/
theorem abs_sum_re_pow_sub_le {u : ℂ} (hu : ‖u‖ = 1) (K N : ℕ) :
    |∑ j ∈ range N, (u ^ (K + j)).re - (if u = 1 then (N : ℝ) else 0)| ≤ windowConst u := by
  by_cases h1 : u = 1
  · subst h1; simp [windowConst]
  · have hgeom : ∑ j ∈ range N, u ^ (K + j) = u ^ K * ((u ^ N - 1) / (u - 1)) := by
      rw [← geom_sum_eq h1, mul_sum]; simp_rw [pow_add]
    simp only [h1, if_false, sub_zero, windowConst]
    rw [← Complex.re_sum, hgeom]
    refine (abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow, hu, one_pow, one_mul, norm_div]
    gcongr
    calc ‖u ^ N - 1‖ ≤ ‖u ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hu, one_pow, norm_one]; norm_num

/-! ### 2. Unimodular power sums change sign -/

section Unimodular

variable {ι : Type*} (J : Finset ι) (w : ι → ℂ)

theorem abs_re_powerSum_le (hw : ∀ i ∈ J, ‖w i‖ = 1) (k : ℕ) :
    |(∑ i ∈ J, w i ^ k).re| ≤ (J.card : ℝ) := by
  calc |(∑ i ∈ J, w i ^ k).re| ≤ ‖∑ i ∈ J, w i ^ k‖ := abs_re_le_norm _
    _ ≤ ∑ i ∈ J, ‖w i ^ k‖ := norm_sum_le _ _
    _ = ∑ _i ∈ J, (1 : ℝ) := sum_congr rfl fun i hi => by rw [norm_pow, hw i hi, one_pow]
    _ = (J.card : ℝ) := by simp

/-- **First moment.** The window sum of `Re Σ_{i∈J} w_i^k` is `N · #{i ∈ J : w_i = 1}` up to
`Σ_i windowConst (w_i)`. -/
theorem abs_window_sum_re_powerSum_sub_le (hw : ∀ i ∈ J, ‖w i‖ = 1) (K N : ℕ) :
    |∑ j ∈ range N, (∑ i ∈ J, w i ^ (K + j)).re - N * (J.filter (fun i => w i = 1)).card| ≤
      ∑ i ∈ J, windowConst (w i) := by
  have hswap : ∑ j ∈ range N, (∑ i ∈ J, w i ^ (K + j)).re =
      ∑ i ∈ J, ∑ j ∈ range N, (w i ^ (K + j)).re := by
    simp_rw [Complex.re_sum]; exact sum_comm
  have hcard : (N : ℝ) * (J.filter (fun i => w i = 1)).card =
      ∑ i ∈ J, (if w i = 1 then (N : ℝ) else 0) := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_comm]
  rw [hswap, hcard, ← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => abs_sum_re_pow_sub_le (hw i hi) K N)

theorem two_mul_re_sq (z : ℂ) : 2 * z.re ^ 2 = (z * conj z).re + (z * z).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

/-- **Second moment.** `2 Σ_window (Re Σ_{i∈J} w_i^k)² ≥ N · #J` up to a constant: the diagonal
pairs of `|Σ w_i^k|²` contribute `N` each. -/
theorem window_sum_sq_re_powerSum_ge (hw : ∀ i ∈ J, ‖w i‖ = 1) (K N : ℕ) :
    N * J.card - ∑ i ∈ J, ∑ l ∈ J, (windowConst (w i * conj (w l)) + windowConst (w i * w l)) ≤
      2 * ∑ j ∈ range N, ((∑ i ∈ J, w i ^ (K + j)).re) ^ 2 := by
  have hpt : ∀ k : ℕ, 2 * ((∑ i ∈ J, w i ^ k).re) ^ 2 =
      ∑ i ∈ J, ∑ l ∈ J, (((w i * conj (w l)) ^ k).re + ((w i * w l) ^ k).re) := by
    intro k
    rw [two_mul_re_sq, map_sum, sum_mul_sum, sum_mul_sum]
    simp_rw [map_pow, ← mul_pow, Complex.re_sum, ← sum_add_distrib]
  have hunit : ∀ i ∈ J, ∀ l ∈ J, ‖w i * conj (w l)‖ = 1 ∧ ‖w i * w l‖ = 1 := by
    intro i hi l hl
    simp [hw i hi, hw l hl]
  have hRHS : 2 * ∑ j ∈ range N, ((∑ i ∈ J, w i ^ (K + j)).re) ^ 2 =
      ∑ i ∈ J, ∑ l ∈ J, ∑ j ∈ range N,
        (((w i * conj (w l)) ^ (K + j)).re + ((w i * w l) ^ (K + j)).re) := by
    rw [mul_sum]
    simp_rw [hpt]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_comm
  rw [hRHS]
  have hterm : ∀ i ∈ J, ∀ l ∈ J,
      (if w i * conj (w l) = 1 then (N : ℝ) else 0) -
          (windowConst (w i * conj (w l)) + windowConst (w i * w l)) ≤
        ∑ j ∈ range N, (((w i * conj (w l)) ^ (K + j)).re + ((w i * w l) ^ (K + j)).re) := by
    intro i hi l hl
    obtain ⟨h1, h2⟩ := hunit i hi l hl
    have e1 := (abs_le.mp (abs_sum_re_pow_sub_le h1 K N)).1
    have e2 := (abs_le.mp (abs_sum_re_pow_sub_le h2 K N)).1
    have hite : (0 : ℝ) ≤ if w i * w l = 1 then (N : ℝ) else 0 := by split_ifs <;> positivity
    rw [sum_add_distrib]
    linarith
  have hdiag : ∀ i ∈ J, (N : ℝ) ≤ ∑ l ∈ J, (if w i * conj (w l) = 1 then (N : ℝ) else 0) := by
    intro i hi
    have hself : w i * conj (w i) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw i hi]; simp
    have := single_le_sum (f := fun l => if w i * conj (w l) = 1 then (N : ℝ) else 0)
      (fun l _ => by split_ifs <;> positivity) hi
    simpa [hself] using this
  calc (N : ℝ) * J.card - ∑ i ∈ J, ∑ l ∈ J,
        (windowConst (w i * conj (w l)) + windowConst (w i * w l))
      = ∑ _i ∈ J, (N : ℝ) - ∑ i ∈ J, ∑ l ∈ J,
          (windowConst (w i * conj (w l)) + windowConst (w i * w l)) := by
        rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ J, ∑ l ∈ J, ((if w i * conj (w l) = 1 then (N : ℝ) else 0) -
          (windowConst (w i * conj (w l)) + windowConst (w i * w l))) := by
        simp_rw [sum_sub_distrib]
        exact sub_le_sub_right (sum_le_sum hdiag) _
    _ ≤ _ := sum_le_sum fun i hi => sum_le_sum fun l hl => hterm i hi l hl

/-- **Unimodular power sums are positive infinitely often**: `Re Σ_{i∈J} w_i^k > 1/8` for some
`k ≥ K`. -/
theorem exists_lt_re_powerSum (hJ : J.Nonempty) (hw : ∀ i ∈ J, ‖w i‖ = 1) (K : ℕ) :
    ∃ k, K ≤ k ∧ 1 / 8 < (∑ i ∈ J, w i ^ k).re := by
  by_contra hcon
  push Not at hcon
  set n : ℝ := (J.card : ℝ) with hn_def
  set B := ∑ i ∈ J, windowConst (w i)
  set B₂ := ∑ i ∈ J, ∑ l ∈ J, (windowConst (w i * conj (w l)) + windowConst (w i * w l))
  have hn : 1 ≤ n := by rw [hn_def]; exact_mod_cast hJ.card_pos
  have hB₂ : 0 ≤ B₂ := sum_nonneg fun i _ => sum_nonneg fun l _ =>
    add_nonneg (windowConst_nonneg _) (windowConst_nonneg _)
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * B + 2 * B₂)
  have hmean := abs_window_sum_re_powerSum_sub_le J w hw K N
  have hsq := window_sum_sq_re_powerSum_ge J w hw K N
  have hbound : ∀ j ∈ range N, ((∑ i ∈ J, w i ^ (K + j)).re) ^ 2 ≤
      n * (1 / 4 - (∑ i ∈ J, w i ^ (K + j)).re) := by
    intro j _
    have hx := hcon (K + j) (Nat.le_add_right K j)
    have hxn := abs_re_powerSum_le J w hw (K + j)
    have habs : |(∑ i ∈ J, w i ^ (K + j)).re| ≤ 1 / 4 - (∑ i ∈ J, w i ^ (K + j)).re :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    rw [← sq_abs, sq]
    exact mul_le_mul hxn habs (abs_nonneg _) (by linarith)
  have hsum := sum_le_sum hbound
  rw [← mul_sum, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at hsum
  have hm0 : (0 : ℝ) ≤ N * (J.filter (fun i => w i = 1)).card := by positivity
  have hS := (abs_le.mp hmean).1
  have h1 : 0 ≤ n * ((∑ j ∈ range N, (∑ i ∈ J, w i ^ (K + j)).re) + B) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 < n * (N - 4 * B - 2 * B₂) := mul_pos (by linarith) (by linarith)
  have h3 : 0 ≤ (n - 1) * B₂ := mul_nonneg (by linarith) hB₂
  linarith

/-- **Unimodular power sums with no member equal to `1` are negative infinitely often**:
`Re Σ_{i∈J} w_i^k < −1/8` for some `k ≥ K`. -/
theorem exists_re_powerSum_lt (hJ : J.Nonempty) (hw : ∀ i ∈ J, ‖w i‖ = 1)
    (h1 : ∀ i ∈ J, w i ≠ 1) (K : ℕ) :
    ∃ k, K ≤ k ∧ (∑ i ∈ J, w i ^ k).re < -(1 / 8) := by
  by_contra hcon
  push Not at hcon
  set n : ℝ := (J.card : ℝ) with hn_def
  set B := ∑ i ∈ J, windowConst (w i)
  set B₂ := ∑ i ∈ J, ∑ l ∈ J, (windowConst (w i * conj (w l)) + windowConst (w i * w l))
  have hn : 1 ≤ n := by rw [hn_def]; exact_mod_cast hJ.card_pos
  have hB₂ : 0 ≤ B₂ := sum_nonneg fun i _ => sum_nonneg fun l _ =>
    add_nonneg (windowConst_nonneg _) (windowConst_nonneg _)
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * B + 2 * B₂)
  have hmean := abs_window_sum_re_powerSum_sub_le J w hw K N
  have hfilter : J.filter (fun i => w i = 1) = ∅ := filter_eq_empty_iff.mpr fun i hi => h1 i hi
  rw [hfilter, card_empty, Nat.cast_zero, mul_zero, sub_zero] at hmean
  have hsq := window_sum_sq_re_powerSum_ge J w hw K N
  have hbound : ∀ j ∈ range N, ((∑ i ∈ J, w i ^ (K + j)).re) ^ 2 ≤
      n * ((∑ i ∈ J, w i ^ (K + j)).re + 1 / 4) := by
    intro j _
    have hx := hcon (K + j) (Nat.le_add_right K j)
    have hxn := abs_re_powerSum_le J w hw (K + j)
    have habs : |(∑ i ∈ J, w i ^ (K + j)).re| ≤ (∑ i ∈ J, w i ^ (K + j)).re + 1 / 4 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    rw [← sq_abs, sq]
    exact mul_le_mul hxn habs (abs_nonneg _) (by linarith)
  have hsum := sum_le_sum hbound
  rw [← mul_sum, sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at hsum
  have hS := (abs_le.mp hmean).2
  have h1 : 0 ≤ n * (B - ∑ j ∈ range N, (∑ i ∈ J, w i ^ (K + j)).re) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 < n * (N - 4 * B - 2 * B₂) := mul_pos (by linarith) (by linarith)
  have h3 : 0 ≤ (n - 1) * B₂ := mul_nonneg (by linarith) hB₂
  linarith

end Unimodular

/-! ### 3. One-sided power-sum bounds bound the moduli -/

section Transfer

variable {ι : Type*} [Fintype ι] (z : ι → ℂ)

/-- Below the maximal modulus `A` the power sum is the top block `A^k Σ_{‖z_i‖ = A} (z_i/A)^k`
up to `ε A^k`, for all large `k`. -/
theorem exists_abs_re_sum_pow_sub_top_le {A : ℝ} (hA : 0 < A) (hmax : ∀ i, ‖z i‖ ≤ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K, ∀ k, K ≤ k → |(∑ i, z i ^ k).re -
      A ^ k * (∑ i ∈ univ.filter (fun i => ‖z i‖ = A), (z i / A) ^ k).re| ≤ ε * A ^ k := by
  have hlim : Tendsto (fun k : ℕ => ∑ i ∈ univ.filter (fun i => ¬ ‖z i‖ = A), (‖z i‖ / A) ^ k)
      atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ _i ∈ univ.filter (fun i => ¬ ‖z i‖ = A), (0 : ℝ) by simp]
    refine tendsto_finsetSum _ fun i hi => tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg (norm_nonneg _) hA.le) ((div_lt_one hA).mpr ?_)
    exact lt_of_le_of_ne (hmax i) (mem_filter.mp hi).2
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨K, fun k hk => ?_⟩
  have htop : ∑ i ∈ univ.filter (fun i => ‖z i‖ = A), z i ^ k =
      ((A ^ k : ℝ) : ℂ) * ∑ i ∈ univ.filter (fun i => ‖z i‖ = A), (z i / A) ^ k := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
    rw [div_pow, Complex.ofReal_pow, mul_div_cancel₀ _ (pow_ne_zero k hA0)]
  rw [← sum_filter_add_sum_filter_not univ (fun i => ‖z i‖ = A), Complex.add_re, htop,
    Complex.re_ofReal_mul, add_sub_cancel_left]
  calc |(∑ i ∈ univ.filter (fun i => ¬ ‖z i‖ = A), z i ^ k).re|
      ≤ ∑ i ∈ univ.filter (fun i => ¬ ‖z i‖ = A), ‖z i ^ k‖ :=
        (abs_re_le_norm _).trans (norm_sum_le _ _)
    _ = A ^ k * ∑ i ∈ univ.filter (fun i => ¬ ‖z i‖ = A), (‖z i‖ / A) ^ k := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [norm_pow, div_pow, mul_div_cancel₀ _ (pow_ne_zero k hA.ne')]
    _ ≤ A ^ k * ε := mul_le_mul_of_nonneg_left (hK k hk).le (pow_nonneg hA.le k)
    _ = ε * A ^ k := mul_comm _ _

/-- The maximal modulus of a family with a member above `ρ`, its top block, and the decay of
`C (ρ/A)^k`. -/
private theorem top_data {ρ : ℝ} (hρ : 0 < ρ) {i₁ : ι} (hi₁ : ρ < ‖z i₁‖) (C : ℝ) :
    ∃ A : ℝ, ρ < A ∧ (∀ i, ‖z i‖ ≤ A) ∧ (univ.filter (fun i => ‖z i‖ = A)).Nonempty ∧
      ∃ K, ∀ k, K ≤ k → C * ρ ^ k < A ^ k / 16 ∧ |(∑ i, z i ^ k).re -
        A ^ k * (∑ i ∈ univ.filter (fun i => ‖z i‖ = A), (z i / A) ^ k).re| ≤ A ^ k / 16 := by
  obtain ⟨i₀, -, hi₀⟩ := exists_max_image univ (fun i => ‖z i‖) ⟨i₁, mem_univ _⟩
  set A := ‖z i₀‖
  have hmax : ∀ i, ‖z i‖ ≤ A := fun i => hi₀ i (mem_univ i)
  have hρA : ρ < A := hi₁.trans_le (hmax i₁)
  have hA : 0 < A := hρ.trans hρA
  obtain ⟨K₁, hK₁⟩ := exists_abs_re_sum_pow_sub_top_le z hA hmax (by norm_num : (0 : ℝ) < 1 / 16)
  have hratio : Tendsto (fun k : ℕ => C * (ρ / A) ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hρ.le hA.le)
      ((div_lt_one hA).mpr hρA)).const_mul C
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp (hratio.eventually (gt_mem_nhds (by norm_num :
    (0 : ℝ) < 1 / 16)))
  refine ⟨A, hρA, hmax, ⟨i₀, by simp [A]⟩, max K₁ K₂, fun k hk => ⟨?_, ?_⟩⟩
  · have h2 := hK₂ k (le_of_max_le_right hk)
    have hAk : 0 < A ^ k := pow_pos hA k
    have hCρ : C * ρ ^ k = A ^ k * (C * (ρ / A) ^ k) := by
      rw [div_pow]; field_simp
    rw [hCρ]
    have := mul_lt_mul_of_pos_left h2 hAk
    linarith
  · have h1 := hK₁ k (le_of_max_le_left hk)
    linarith

/-- **An upper one-sided power-sum bound bounds every modulus.** If
`Re Σ_i z_i^k ≤ C ρ^k` for every `k`, then `‖z_i‖ ≤ ρ` for every `i`. -/
theorem norm_le_of_re_sum_pow_le {C ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ k : ℕ, (∑ i, z i ^ k).re ≤ C * ρ ^ k) : ∀ i, ‖z i‖ ≤ ρ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i₁, hi₁⟩ := hcon
  obtain ⟨A, hρA, -, hJ, K, hK⟩ := top_data z hρ hi₁ C
  have hA : 0 < A := hρ.trans hρA
  have hw : ∀ i ∈ univ.filter (fun i => ‖z i‖ = A), ‖z i / A‖ = 1 := by
    intro i hi
    rw [norm_div, (mem_filter.mp hi).2, Complex.norm_real, Real.norm_of_nonneg hA.le,
      div_self hA.ne']
  obtain ⟨k, hk, hpos⟩ := exists_lt_re_powerSum _ (fun i => z i / A) hJ hw K
  obtain ⟨hC, hclose⟩ := hK k hk
  have hAk : 0 < A ^ k := pow_pos hA k
  have hmul : A ^ k / 8 < A ^ k * (∑ i ∈ univ.filter (fun i => ‖z i‖ = A), (z i / A) ^ k).re := by
    have := mul_lt_mul_of_pos_left hpos hAk
    linarith
  have := h k
  linarith [(abs_le.mp hclose).1]

/-- **A lower one-sided power-sum bound bounds every modulus unless the top is real.** If
`Re Σ_i z_i^k ≥ −C ρ^k` for every `k` and no member of modulus `> ρ` is a positive real number,
then `‖z_i‖ ≤ ρ` for every `i`. -/
theorem norm_le_of_neg_le_re_sum_pow {C ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ k : ℕ, -(C * ρ ^ k) ≤ (∑ i, z i ^ k).re)
    (hreal : ∀ i, ρ < ‖z i‖ → z i ≠ (‖z i‖ : ℂ)) : ∀ i, ‖z i‖ ≤ ρ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i₁, hi₁⟩ := hcon
  obtain ⟨A, hρA, -, hJ, K, hK⟩ := top_data z hρ hi₁ C
  have hA : 0 < A := hρ.trans hρA
  have hw : ∀ i ∈ univ.filter (fun i => ‖z i‖ = A), ‖z i / A‖ = 1 := by
    intro i hi
    rw [norm_div, (mem_filter.mp hi).2, Complex.norm_real, Real.norm_of_nonneg hA.le,
      div_self hA.ne']
  have hne : ∀ i ∈ univ.filter (fun i => ‖z i‖ = A), z i / A ≠ 1 := by
    intro i hi hone
    have hiA := (mem_filter.mp hi).2
    have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
    have hz : z i = (A : ℂ) := (div_eq_one_iff_eq hA0).mp hone
    exact hreal i (hiA ▸ hρA) (by rw [hiA]; exact hz)
  obtain ⟨k, hk, hneg⟩ := exists_re_powerSum_lt _ (fun i => z i / A) hJ hw hne K
  obtain ⟨hC, hclose⟩ := hK k hk
  have hAk : 0 < A ^ k := pow_pos hA k
  have hmul : A ^ k * (∑ i ∈ univ.filter (fun i => ‖z i‖ = A), (z i / A) ^ k).re < -(A ^ k / 8) := by
    have := mul_lt_mul_of_pos_left hneg hAk
    linarith
  have := h k
  linarith [(abs_le.mp hclose).2]

end Transfer

/-! ### 4. Curve data: the two one-sided Lefschetz bounds -/

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- An **outer eigenvalue that is a positive real number**: over `𝔽_q` this is a real zero of the
zeta function right of the critical line. -/
def HasRealOuterEigenvalue : Prop := ∃ i, 1 < ‖D.β i‖ ∧ D.β i = (‖D.β i‖ : ℂ)

private theorem unitary_of_norm_le_one (hle : ∀ i, ‖D.β i‖ ≤ 1) : ∀ i, ‖D.β i‖ = 1 := by
  intro i
  have hfe := congrArg norm (D.β_fePerm i)
  rw [norm_mul, norm_one] at hfe
  have hi := hle i
  have hf := hle (D.fePerm i)
  nlinarith [norm_nonneg (D.β i), norm_nonneg (D.β (D.fePerm i))]

theorem abs_trace_le_card_of_unitary (hU : ∀ i, ‖D.β i‖ = 1) (k : ℕ) :
    |D.trace k| ≤ Fintype.card ι := by
  rw [D.abs_trace_eq_norm_powerSum]
  calc ‖∑ i, D.β i ^ k‖ ≤ ∑ i, ‖D.β i ^ k‖ := norm_sum_le _ _
    _ = ∑ _i : ι, (1 : ℝ) := sum_congr rfl fun i _ => by rw [norm_pow, hU i, one_pow]
    _ = Fintype.card ι := by simp

/-- **A lower Lefschetz bound forces the Riemann hypothesis for the datum**: `trace k ≤ C` for all
`k`, i.e. `N_k ≥ q^k + 1 − C q^{k/2}`, implies unitarity. -/
theorem unitary_of_trace_le {C : ℝ} (hC : ∀ k : ℕ, D.trace k ≤ C) : ∀ i, ‖D.β i‖ = 1 :=
  D.unitary_of_norm_le_one (norm_le_of_re_sum_pow_le D.β one_pos (C := C) fun k => by
    rw [one_pow, mul_one]; exact hC k)

/-- **An upper Lefschetz bound forces the Riemann hypothesis unless there is a real zero**:
`trace k ≥ −C` for all `k`, i.e. `N_k ≤ q^k + 1 + C q^{k/2}`, and no real outer eigenvalue imply
unitarity. -/
theorem unitary_of_neg_le_trace {C : ℝ} (hC : ∀ k : ℕ, -C ≤ D.trace k)
    (hreal : ¬ D.HasRealOuterEigenvalue) : ∀ i, ‖D.β i‖ = 1 :=
  D.unitary_of_norm_le_one (norm_le_of_neg_le_re_sum_pow D.β one_pos (C := C)
    (fun k => by rw [one_pow, mul_one]; exact hC k)
    (fun i hi heq => hreal ⟨i, hi, heq⟩))

theorem trace_le_iff_pointCount_ge (k : ℕ) (C : ℝ) :
    D.trace k ≤ C ↔ D.q ^ k + 1 - C * D.sqrtq ^ k ≤ D.pointCount k := by
  have hs : 0 < D.sqrtq ^ k := pow_pos D.sqrtq_pos k
  unfold pointCount
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h hs.le
    linarith
  · intro h
    exact le_of_mul_le_mul_left (by linarith : D.sqrtq ^ k * D.trace k ≤ D.sqrtq ^ k * C) hs

theorem neg_le_trace_iff_pointCount_le (k : ℕ) (C : ℝ) :
    -C ≤ D.trace k ↔ D.pointCount k ≤ D.q ^ k + 1 + C * D.sqrtq ^ k := by
  have hs : 0 < D.sqrtq ^ k := pow_pos D.sqrtq_pos k
  unfold pointCount
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h hs.le
    linarith
  · intro h
    exact le_of_mul_le_mul_left (by linarith : D.sqrtq ^ k * (-C) ≤ D.sqrtq ^ k * D.trace k) hs

/-- **The one-sided forcing equivalences.** For a curve datum the following are equivalent:
unitarity; a lower Lefschetz bound `N_k ≥ q^k + 1 − C q^{k/2}`; an upper Lefschetz bound
`N_k ≤ q^k + 1 + C q^{k/2}` together with the absence of real outer eigenvalues. -/
theorem oneSided_forcing_tfae :
    List.TFAE
      [ ∀ i, ‖D.β i‖ = 1,
        ∃ C : ℝ, ∀ k : ℕ, D.q ^ k + 1 - C * D.sqrtq ^ k ≤ D.pointCount k,
        (∃ C : ℝ, ∀ k : ℕ, D.pointCount k ≤ D.q ^ k + 1 + C * D.sqrtq ^ k) ∧
          ¬ D.HasRealOuterEigenvalue ] := by
  tfae_have 1 → 2 := fun hU => ⟨Fintype.card ι, fun k =>
    (D.trace_le_iff_pointCount_ge k _).mp (abs_le.mp (D.abs_trace_le_card_of_unitary hU k)).2⟩
  tfae_have 2 → 1 := fun ⟨C, hC⟩ => D.unitary_of_trace_le (C := C) fun k =>
    (D.trace_le_iff_pointCount_ge k C).mpr (hC k)
  tfae_have 1 → 3 := fun hU => ⟨⟨Fintype.card ι, fun k =>
      (D.neg_le_trace_iff_pointCount_le k _).mp (abs_le.mp (D.abs_trace_le_card_of_unitary hU k)).1⟩,
    fun ⟨i, hi, _⟩ => by rw [hU i] at hi; exact lt_irrefl _ hi⟩
  tfae_have 3 → 1 := fun ⟨⟨C, hC⟩, hreal⟩ => D.unitary_of_neg_le_trace (C := C)
    (fun k => (D.neg_le_trace_iff_pointCount_le k C).mpr (hC k)) hreal
  tfae_finish

/-! ### 5. Lag tests read the two sides separately -/

variable (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)
include hD

/-- The **difference lag test** `g − g(· − n log q)` reads the upper side of the trace:
`Re W = 2 log q ‖g‖² (#ι − trace n)`. -/
theorem re_W_curveConfig_differenceLagTest {g : ℝ → ℂ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2)) (hwL : w < Real.log D.q) (n : ℕ) :
    ((D.curveConfig hD).W (lagTest g ((-1 : ℝ) : ℂ) (n * Real.log D.q))
        (lagTest g ((-1 : ℝ) : ℂ) (n * Real.log D.q))).re =
      2 * Real.log D.q * (∫ u, ‖g u‖ ^ 2) * (Fintype.card ι - D.trace n) := by
  rw [D.re_W_curveConfig_lagTest hD hg hgs hwL, D.trace_zero]; ring

/-- The **sum lag test** `g + g(· − n log q)` reads the lower side of the trace:
`Re W = 2 log q ‖g‖² (#ι + trace n)`. -/
theorem re_W_curveConfig_sumLagTest {g : ℝ → ℂ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2)) (hwL : w < Real.log D.q) (n : ℕ) :
    ((D.curveConfig hD).W (lagTest g ((1 : ℝ) : ℂ) (n * Real.log D.q))
        (lagTest g ((1 : ℝ) : ℂ) (n * Real.log D.q))).re =
      2 * Real.log D.q * (∫ u, ‖g u‖ ^ 2) * (Fintype.card ι + D.trace n) := by
  rw [D.re_W_curveConfig_lagTest hD hg hgs hwL, D.trace_zero]; ring

/-- **Difference lag tests see every impure curve**: all of them are Weil-nonnegative iff the
datum is unitary. -/
theorem differenceLagTests_nonneg_iff_unitary {g : ℝ → ℂ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2)) (hwL : w < Real.log D.q)
    (hg0 : 0 < ∫ u, ‖g u‖ ^ 2) :
    (∀ n : ℕ, 0 ≤ ((D.curveConfig hD).W (lagTest g ((-1 : ℝ) : ℂ) (n * Real.log D.q))
        (lagTest g ((-1 : ℝ) : ℂ) (n * Real.log D.q))).re) ↔ ∀ i, ‖D.β i‖ = 1 := by
  have hK : 0 < 2 * Real.log D.q * ∫ u, ‖g u‖ ^ 2 := by
    have := D.log_q_pos; positivity
  simp_rw [D.re_W_curveConfig_differenceLagTest hD hg hgs hwL]
  constructor
  · intro h
    exact D.unitary_of_trace_le (C := Fintype.card ι) fun k => by
      have := (mul_nonneg_iff_of_pos_left hK).mp (h k); linarith
  · intro hU k
    have := (abs_le.mp (D.abs_trace_le_card_of_unitary hU k)).2
    exact mul_nonneg hK.le (by linarith)

/-- **Sum lag tests see every impure curve without a real zero**: in the absence of real outer
eigenvalues, all of them are Weil-nonnegative iff the datum is unitary. -/
theorem sumLagTests_nonneg_iff_unitary (hreal : ¬ D.HasRealOuterEigenvalue) {g : ℝ → ℂ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2))
    (hwL : w < Real.log D.q) (hg0 : 0 < ∫ u, ‖g u‖ ^ 2) :
    (∀ n : ℕ, 0 ≤ ((D.curveConfig hD).W (lagTest g ((1 : ℝ) : ℂ) (n * Real.log D.q))
        (lagTest g ((1 : ℝ) : ℂ) (n * Real.log D.q))).re) ↔ ∀ i, ‖D.β i‖ = 1 := by
  have hK : 0 < 2 * Real.log D.q * ∫ u, ‖g u‖ ^ 2 := by
    have := D.log_q_pos; positivity
  simp_rw [D.re_W_curveConfig_sumLagTest hD hg hgs hwL]
  constructor
  · intro h
    exact D.unitary_of_neg_le_trace (C := Fintype.card ι) (fun k => by
      have := (mul_nonneg_iff_of_pos_left hK).mp (h k); linarith) hreal
  · intro hU k
    have := (abs_le.mp (D.abs_trace_le_card_of_unitary hU k)).1
    exact mul_nonneg hK.le (by linarith)

end CurveDatum

/-! ### 6. The golden curve is a real-zero fake -/

open Real in
theorem goldenDatum_trace_nonneg (k : ℕ) : 0 ≤ goldenDatum.trace k := by
  rw [goldenDatum_trace]; positivity

open Real in
theorem goldenDatum_hasRealOuterEigenvalue : goldenDatum.HasRealOuterEigenvalue := by
  refine ⟨0, ?_, ?_⟩
  · show 1 < ‖((goldenRatio : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg goldenRatio_pos.le]
    exact one_lt_goldenRatio
  · show ((goldenRatio : ℝ) : ℂ) = ((‖((goldenRatio : ℝ) : ℂ)‖ : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg goldenRatio_pos.le]

/-- **The golden curve satisfies every upper Lefschetz bound and fails purity through a real
zero**: `N_k ≤ q^k + 1` for all `k`, the datum is not unitary, its outer eigenvalue `φ` is real,
and its lower Lefschetz bounds fail for every constant. -/
theorem goldenDatum_upper_lefschetz_bound_and_real_zero :
    (∀ k : ℕ, goldenDatum.pointCount k ≤ goldenDatum.q ^ k + 1) ∧
      ¬ (∀ i, ‖goldenDatum.β i‖ = 1) ∧ goldenDatum.HasRealOuterEigenvalue ∧
      ∀ C : ℝ, ∃ k : ℕ, goldenDatum.pointCount k < goldenDatum.q ^ k + 1 - C * goldenDatum.sqrtq ^ k := by
  refine ⟨fun k => ?_, goldenDatum_not_unitary, goldenDatum_hasRealOuterEigenvalue, fun C => ?_⟩
  · have := (goldenDatum.neg_le_trace_iff_pointCount_le k 0).mp (by
      rw [neg_zero]; exact goldenDatum_trace_nonneg k)
    simpa using this
  · by_contra h
    push Not at h
    exact goldenDatum_not_unitary (goldenDatum.unitary_of_trace_le (C := C) fun k =>
      (goldenDatum.trace_le_iff_pointCount_ge k C).mpr (h k))

/-- On the scaling surface of the golden curve **every sum lag test is Weil-nonnegative**, while a
difference lag test is negative (`goldenDatum_lagTest_neg`). -/
theorem goldenDatum_sumLagTests_nonneg {g : ℝ → ℂ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2)) (hwL : w < Real.log goldenDatum.q) (n : ℕ) :
    0 ≤ ((goldenDatum.curveConfig goldenDatum_strip).W
        (lagTest g ((1 : ℝ) : ℂ) (n * Real.log goldenDatum.q))
        (lagTest g ((1 : ℝ) : ℂ) (n * Real.log goldenDatum.q))).re := by
  rw [goldenDatum.re_W_curveConfig_sumLagTest goldenDatum_strip hg hgs hwL]
  have hK : 0 ≤ 2 * Real.log goldenDatum.q * ∫ u, ‖g u‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) goldenDatum.log_q_pos.le)
      (MeasureTheory.integral_nonneg fun _ => by positivity)
  exact mul_nonneg hK (add_nonneg (Nat.cast_nonneg _) (goldenDatum_trace_nonneg n))

end

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
