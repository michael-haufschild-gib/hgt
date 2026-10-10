import GaloisForLFunctions.RHTower.LiCriterion

/-!
# The Li growth law

Write `w_ρ = 1 - 1/ρ` and let `v_ρ` be the member of `{w_ρ, w_ρ⁻¹}` of modulus at least one; the
paired Li coefficients are `2λ_n = Σ_ρ m_ρ (2 - v_ρⁿ - v_ρ⁻ⁿ)`.

**Theorem** (`cayley_le_iff_xiLiPaired_lower`). For `r ≥ 1`, every zero of `ξ` has `‖v_ρ‖ ≤ r` iff
for every `r' > r` there is `C` with `Re(2λ_n) ≥ -C r'ⁿ` for all `n`. The negative part of the Li
coefficients therefore grows exactly at the exponential rate `max_ρ ‖v_ρ‖`.

* `r = 1` is RH (`riemannHypothesis_iff_cayley_le_one`), so Li's criterion needs only a
  subexponential lower bound (`riemannHypothesis_iff_xiLiPaired_subexp`).
* Under the Cayley bound, `‖2λ_n‖ ≤ C n² rⁿ` (`exists_norm_xiLiPaired_le_of_cayley`); under RH,
  `‖2λ_n‖ ≤ C n²`.

**Mechanism** (`exists_re_tsum_liTerm_lt_neg_pow`). A root of modulus `W > 1` makes the finite
dominant part at most `3T - m W ⁿ/2` at the torus-recurrence times of the dominant directions.
The tail is `O(n² qⁿ)` with `q < W`, so `Re(2λ_n) < -B ρⁿ` for every `ρ < W` along those times.
Conversely `‖2 - vⁿ - v⁻ⁿ‖ ≤ n² ‖v‖ⁿ ‖v - 1‖²` and `Σ m_ρ ‖v_ρ - 1‖² < ∞`.
-/
open Complex
noncomputable section
namespace RHTower

variable {ι : Type*} {v : ι → ℂ} {m : ι → ℝ} {M : ℝ}

/-- **Quantitative hard half of Li's criterion.**  If one member of the family has modulus
`W > 1`, then for every `0 ≤ ρ < W` and every real `B` some paired Li sum is below `-B ρⁿ`. -/
theorem exists_re_tsum_liTerm_lt_neg_pow
    (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ))
    {i₀ : ι} (hlt : 1 < ‖v i₀‖) {ρ B : ℝ} (hρ0 : 0 ≤ ρ) (hρW : ρ < ‖v i₀‖) :
    ∃ n : ℕ, (∑' i, m i * (liTerm (v i) n).re) < -(B * ρ ^ n) := by
  classical
  by_contra hcon
  push Not at hcon
  set W : ℝ := ‖v i₀‖ with hWdef
  set q : ℝ := (1 + W) / 2 with hqdef
  have hq1 : 1 < q := by rw [hqdef]; linarith
  have hqW : q < W := by rw [hqdef]; linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hFfin : {i | q ≤ ‖v i‖}.Finite := finite_far_set hm hs hq1
  set S : Finset ι := hFfin.toFinset with hSdef
  have hmemS : ∀ i, i ∈ S ↔ q ≤ ‖v i‖ := by
    intro i
    rw [hSdef, Set.Finite.mem_toFinset]
    rfl
  have hi₀S : i₀ ∈ S := (hmemS i₀).mpr (le_of_lt hqW)
  set C : ℝ := ∑' i, m i * ‖v i - 1‖ ^ (2 : ℕ) with hCdef
  have hC0 : 0 ≤ C := tsum_nonneg fun i => by
    have := hm i
    have h2 : (0:ℝ) ≤ ‖v i - 1‖ ^ (2 : ℕ) := sq_nonneg _
    nlinarith
  set T : ℝ := ∑ i ∈ S, m i with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => by linarith [hm i]
  have hm0 : ∀ i, (0:ℝ) ≤ m i := fun i => by linarith [hm i]
  -- the exponential eventually beats the polynomial
  set r : ℝ := q / W with hrdef
  have hW0 : (0:ℝ) < W := by linarith
  have hr0 : (0:ℝ) ≤ r := by rw [hrdef]; positivity
  have hr1 : r < 1 := by
    rw [hrdef, div_lt_one hW0]
    exact hqW
  have hlim1 : Filter.Tendsto (fun n : ℕ => 3 * T * r ^ n) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    simpa using this.const_mul (3 * T)
  have hlim2 : Filter.Tendsto (fun n : ℕ => C * ((n : ℝ) ^ (2 : ℕ) * r ^ n)) Filter.atTop (nhds 0) := by
    have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (2 : ℕ) * r ^ n) := by
      refine summable_pow_mul_geometric_of_norm_lt_one 2 ?_
      rw [Real.norm_eq_abs, abs_of_nonneg hr0]
      exact hr1
    simpa using hsum.tendsto_atTop_zero.const_mul C
  set ρr : ℝ := ρ / W with hρrdef
  have hρr0 : 0 ≤ ρr := by rw [hρrdef]; positivity
  have hρr1 : ρr < 1 := by rw [hρrdef, div_lt_one hW0]; exact hρW
  have hlim3 : Filter.Tendsto (fun n : ℕ => B * ρr ^ n) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρr0 hρr1).const_mul B
  have hlim : Filter.Tendsto (fun n : ℕ => 3 * T * r ^ n + C * ((n : ℝ) ^ (2 : ℕ) * r ^ n) +
      B * ρr ^ n) Filter.atTop (nhds 0) := by simpa using (hlim1.add hlim2).add hlim3
  have hm0pos : (0:ℝ) < m i₀ / 2 := by linarith [hm i₀]
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hm0pos)).exists_forall_of_atTop
  -- pigeonhole
  have hunit : ∀ i : {x // x ∈ S}, ‖v (i : ι) / (‖v (i : ι)‖ : ℂ)‖ = 1 := by
    rintro ⟨i, hi⟩
    have hvi : (0:ℝ) < ‖v i‖ := lt_of_lt_of_le zero_lt_one (hv i)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hvi, div_self (ne_of_gt hvi)]
  obtain ⟨n, hnN, hnpos, hnre⟩ :=
    exists_ge_pow_re_gt_half (fun i : {x // x ∈ S} => v (i : ι) / (‖v (i : ι)‖ : ℂ)) hunit N
  -- the split
  have hsummable := summable_re_liTerm_of_one_le hm0 hv hM hs n
  have hsplit := hsummable.sum_add_tsum_compl (s := S)
  -- the tail is small
  have hBsum : Summable fun i : {x // x ∈ (↑S : Set ι)ᶜ} =>
      (n : ℝ) ^ (2 : ℕ) * q ^ n * (m (i : ι) * ‖v (i : ι) - 1‖ ^ (2 : ℕ)) :=
    (hs.subtype _).mul_left _
  have hBle : ∀ i : {x // x ∈ (↑S : Set ι)ᶜ},
      m (i : ι) * (liTerm (v (i : ι)) n).re
        ≤ (n : ℝ) ^ (2 : ℕ) * q ^ n * (m (i : ι) * ‖v (i : ι) - 1‖ ^ (2 : ℕ)) := by
    rintro ⟨i, hi⟩
    have hiS : ¬ (q ≤ ‖v i‖) := by
      intro h
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hi
      exact hi ((hmemS i).mpr h)
    have hlt' : ‖v i‖ < q := lt_of_not_ge hiS
    have hvne : v i ≠ 0 := by
      intro h
      have h1 := hv i
      rw [h] at h1
      simp at h1
      linarith
    have hmax : max ‖v i‖ ‖v i‖⁻¹ = ‖v i‖ := by
      refine max_eq_left ?_
      have h1 : (0:ℝ) < ‖v i‖ := lt_of_lt_of_le zero_lt_one (hv i)
      rw [inv_le_iff_one_le_mul₀ h1]
      nlinarith [hv i]
    have hbase := norm_liTerm_le hvne n
    rw [hmax] at hbase
    have hpow : ‖v i‖ ^ n ≤ q ^ n := pow_le_pow_left₀ (norm_nonneg _) hlt'.le n
    have hre : (liTerm (v i) n).re ≤ ‖liTerm (v i) n‖ := Complex.re_le_norm _
    have hchain : ‖liTerm (v i) n‖ ≤ (n : ℝ) ^ (2 : ℕ) * q ^ n * ‖v i - 1‖ ^ (2 : ℕ) := by
      refine le_trans hbase ?_
      have h2 : (0:ℝ) ≤ ‖v i - 1‖ ^ (2 : ℕ) := sq_nonneg _
      have h3 : (0:ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := sq_nonneg _
      rw [mul_assoc, mul_assoc]
      gcongr
    calc m i * (liTerm (v i) n).re
        ≤ m i * ((n : ℝ) ^ (2 : ℕ) * q ^ n * ‖v i - 1‖ ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left (le_trans hre hchain) (hm0 i)
      _ = (n : ℝ) ^ (2 : ℕ) * q ^ n * (m i * ‖v i - 1‖ ^ (2 : ℕ)) := by ring
  have htailC : (∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, m (i : ι) * ‖v (i : ι) - 1‖ ^ (2 : ℕ)) ≤ C := by
    have hsp := hs.sum_add_tsum_compl (s := S)
    have hSnn : (0:ℝ) ≤ ∑ i ∈ S, m i * ‖v i - 1‖ ^ (2 : ℕ) :=
      Finset.sum_nonneg fun i _ => by nlinarith [hm0 i, sq_nonneg ‖v i - 1‖]
    rw [hCdef, ← hsp]
    linarith
  have htail : (∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, m (i : ι) * (liTerm (v (i : ι)) n).re)
      ≤ (n : ℝ) ^ (2 : ℕ) * q ^ n * C := by
    refine le_trans (Summable.tsum_le_tsum hBle
      (hsummable.subtype ((↑S : Set ι)ᶜ)) hBsum) ?_
    rw [Summable.tsum_mul_left]
    · have hcoef : (0:ℝ) ≤ (n : ℝ) ^ (2 : ℕ) * q ^ n := by positivity
      exact mul_le_mul_of_nonneg_left htailC hcoef
    · exact hs.subtype _
  -- so the finite part is bounded below
  have hSlow : -((n : ℝ) ^ (2 : ℕ) * q ^ n * C) - B * ρ ^ n ≤
      ∑ i ∈ S, m i * (liTerm (v i) n).re := by
    have h0 := hcon n
    rw [← hsplit] at h0
    linarith
  -- the finite part is bounded above by `3T - Σ m (vⁿ).re`
  have hSup : ∑ i ∈ S, m i * (liTerm (v i) n).re
      ≤ 3 * T - ∑ i ∈ S, m i * (v i ^ n).re := by
    rw [hTdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hvne : v i ≠ 0 := by
      intro h
      have h1 := hv i
      rw [h] at h1
      simp at h1
      linarith
    have hinv : (-1 : ℝ) ≤ ((v i)⁻¹ ^ n).re := by
      have h2 : ‖(v i)⁻¹ ^ n‖ ≤ 1 := by
        rw [norm_pow, norm_inv]
        refine pow_le_one₀ (by positivity) ?_
        rw [inv_le_one₀ (lt_of_lt_of_le zero_lt_one (hv i))]
        exact hv i
      have h3 : -‖(v i)⁻¹ ^ n‖ ≤ ((v i)⁻¹ ^ n).re := neg_le_of_abs_le (Complex.abs_re_le_norm _)
      linarith
    have hlire : (liTerm (v i) n).re = 2 - (v i ^ n).re - ((v i)⁻¹ ^ n).re := by
      rw [liTerm]
      simp
    have hgoal : m i * (liTerm (v i) n).re ≤ 3 * m i - m i * (v i ^ n).re := by
      rw [hlire]
      nlinarith [hm0 i]
    linarith
  -- the pigeonhole makes every `(vⁿ).re` large
  have hbig : ∀ i ∈ S, ‖v i‖ ^ n / 2 ≤ (v i ^ n).re := by
    intro i hi
    have hvi : (0:ℝ) < ‖v i‖ := lt_of_lt_of_le zero_lt_one (hv i)
    have hcne : ((‖v i‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hvi)
    have hfac : v i = (‖v i‖ : ℂ) * (v i / (‖v i‖ : ℂ)) := by
      field_simp
    have hpow : v i ^ n = ((‖v i‖ : ℂ)) ^ n * (v i / (‖v i‖ : ℂ)) ^ n := by
      rw [← mul_pow, ← hfac]
    have hre : (v i ^ n).re = ‖v i‖ ^ n * ((v i / (‖v i‖ : ℂ)) ^ n).re := by
      rw [hpow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    have hhalf := hnre ⟨i, hi⟩
    rw [hre]
    have hpos : (0:ℝ) < ‖v i‖ ^ n := by positivity
    nlinarith
  have hall : ∀ i ∈ S, (0:ℝ) ≤ m i * (v i ^ n).re := by
    intro i hi
    have h1 := hbig i hi
    have h2 : (0:ℝ) ≤ ‖v i‖ ^ n := by positivity
    nlinarith [hm0 i]
  have hone : m i₀ * (v i₀ ^ n).re ≤ ∑ i ∈ S, m i * (v i ^ n).re :=
    Finset.single_le_sum hall hi₀S
  have hkey : m i₀ * (W ^ n / 2) ≤ 3 * T + (n : ℝ) ^ (2 : ℕ) * q ^ n * C + B * ρ ^ n := by
    have h1 := hbig i₀ hi₀S
    have h2 : m i₀ * (W ^ n / 2) ≤ m i₀ * (v i₀ ^ n).re := by
      have := hm0 i₀
      nlinarith
    linarith
  -- exponential beats polynomial
  have hW0n : (0:ℝ) < W ^ n := by positivity
  have hqn : (1:ℝ) ≤ q ^ n := one_le_pow₀ hq1.le
  have hrn : r ^ n = q ^ n / W ^ n := by rw [hrdef, div_pow]
  have hfinal : m i₀ / 2 ≤ 3 * T * r ^ n + C * ((n : ℝ) ^ (2 : ℕ) * r ^ n) + B * ρr ^ n := by
    have hrn' : r ^ n * W ^ n = q ^ n := by
      rw [hrn]
      field_simp
    have hρn' : ρr ^ n * W ^ n = ρ ^ n := by
      rw [hρrdef, div_pow]
      field_simp
    have hstep : m i₀ / 2 * W ^ n ≤ 3 * T + (n : ℝ) ^ (2 : ℕ) * q ^ n * C + B * ρ ^ n := by
      calc m i₀ / 2 * W ^ n = m i₀ * (W ^ n / 2) := by ring
        _ ≤ 3 * T + (n : ℝ) ^ (2 : ℕ) * q ^ n * C + B * ρ ^ n := hkey
    have hexp : (3 * T * r ^ n + C * ((n : ℝ) ^ (2 : ℕ) * r ^ n) + B * ρr ^ n) * W ^ n
        = 3 * T * q ^ n + C * (n : ℝ) ^ (2 : ℕ) * q ^ n + B * ρ ^ n := by
      rw [show (3 * T * r ^ n + C * ((n : ℝ) ^ (2 : ℕ) * r ^ n) + B * ρr ^ n) * W ^ n
        = 3 * T * (r ^ n * W ^ n) + C * (n : ℝ) ^ (2 : ℕ) * (r ^ n * W ^ n) +
          B * (ρr ^ n * W ^ n) from by ring, hrn', hρn']
    refine le_of_mul_le_mul_right ?_ hW0n
    rw [hexp]
    have h3T : 3 * T ≤ 3 * T * q ^ n := le_mul_of_one_le_right (by linarith) hqn
    linarith
  have hlast := hN n hnN
  linarith


/-! ### The Xi divisor -/

theorem liSupport_ne_zero (ρ : XiDivisorSupport) : (ρ : ℂ) ≠ 0 := by
  intro h
  have him := xi_divisor_support_im_ne_zero ρ
  rw [h] at him
  simp at him

theorem liSupport_ne_one (ρ : XiDivisorSupport) : (ρ : ℂ) ≠ 1 := by
  intro h
  have him := xi_divisor_support_im_ne_zero ρ
  rw [h] at him
  simp at him

theorem one_le_liSupport_mult (ρ : XiDivisorSupport) :
    (1 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
  have := xi_divisor_pos_on_support ρ
  exact_mod_cast this

/-- The weighted squares `Σ_ρ m_ρ ‖v_ρ - 1‖²` of the normalised Cayley roots are summable. -/
theorem summable_liSupport_mult_norm_xiRootV_sub_one_sq :
    Summable fun ρ : XiDivisorSupport =>
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ) := by
  obtain ⟨M, hM1, hMb⟩ := exists_bound_xiRootW
  refine Summable.of_nonneg_of_le
    (fun ρ => mul_nonneg (by linarith [one_le_liSupport_mult ρ]) (sq_nonneg _))
    (fun ρ => ?_) (xi_zero_multiplicity_inv_sq_summable.mul_left (M ^ (2 : ℕ)))
  have hb := norm_xiRootV_sub_one_le (liSupport_ne_zero ρ) (liSupport_ne_one ρ) hM1 (hMb ρ)
  rw [norm_xiRootW_sub_one] at hb
  have hsq : ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) * (1 / ‖(ρ : ℂ)‖ ^ (2 : ℕ)) := by
    rw [← one_div_pow, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  calc ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ)
      ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
          (M ^ (2 : ℕ) * (1 / ‖(ρ : ℂ)‖ ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hsq (by linarith [one_le_liSupport_mult ρ])
    _ = M ^ (2 : ℕ) * (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) /
          ‖(ρ : ℂ)‖ ^ (2 : ℕ)) := by ring

theorem re_xiLiPaired_eq_tsum (n : ℕ) :
    (xiLiPaired n).re = ∑' ρ : XiDivisorSupport,
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * (liTerm (xiRootV (ρ : ℂ)) n).re := by
  rw [xiLiPaired, Complex.re_tsum (summable_xiLiPairedTerm n)]
  refine tsum_congr fun ρ => ?_
  rw [xiLiPairedTerm, Complex.re_ofReal_mul, liTerm_xiRootV]

/-- **Upper half of the Li growth law.** If every normalised Cayley root has modulus at most `r`,
then `‖2λ_n‖ ≤ C n² rⁿ`. -/
theorem exists_norm_xiLiPaired_le_of_cayley {r : ℝ}
    (h : ∀ ρ : ℂ, xi ρ = 0 → ‖xiRootV ρ‖ ≤ r) :
    ∃ C : ℝ, ∀ n : ℕ, ‖xiLiPaired n‖ ≤ C * ((n : ℝ) ^ (2 : ℕ) * r ^ n) := by
  set S := summable_liSupport_mult_norm_xiRootV_sub_one_sq
  refine ⟨∑' ρ : XiDivisorSupport,
    ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ),
    fun n => ?_⟩
  have hterm : ∀ ρ : XiDivisorSupport, ‖xiLiPairedTerm n ρ‖ ≤ (n : ℝ) ^ (2 : ℕ) * r ^ n *
      (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ)) := by
    intro ρ
    have hv1 := one_le_norm_xiRootV (liSupport_ne_zero ρ) (liSupport_ne_one ρ)
    have hvr : ‖xiRootV (ρ : ℂ)‖ ≤ r := h ρ (xi_eq_zero_of_mem_divisor_support ρ)
    have hvne : xiRootV (ρ : ℂ) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hv1; linarith
    have hmax : max ‖xiRootV (ρ : ℂ)‖ ‖xiRootV (ρ : ℂ)‖⁻¹ = ‖xiRootV (ρ : ℂ)‖ :=
      max_eq_left ((inv_le_one_of_one_le₀ hv1).trans hv1)
    have hb := norm_liTerm_le hvne n
    rw [hmax] at hb
    have hpow : ‖xiRootV (ρ : ℂ)‖ ^ n ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg _) hvr n
    rw [xiLiPairedTerm, norm_mul, ← liTerm_xiRootV, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [one_le_liSupport_mult ρ])]
    have hm0 : (0 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
      linarith [one_le_liSupport_mult ρ]
    have hb' : ‖liTerm (xiRootV (ρ : ℂ)) n‖ ≤
        (n : ℝ) ^ (2 : ℕ) * r ^ n * ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ) :=
      hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (sq_nonneg _)) (sq_nonneg _))
    calc ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖liTerm (xiRootV (ρ : ℂ)) n‖
        ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
            ((n : ℝ) ^ (2 : ℕ) * r ^ n * ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hb' hm0
      _ = _ := by ring
  have hsum : Summable fun ρ : XiDivisorSupport => ‖xiLiPairedTerm n ρ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (S.mul_left _)
  calc ‖xiLiPaired n‖ ≤ ∑' ρ : XiDivisorSupport, ‖xiLiPairedTerm n ρ‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' ρ : XiDivisorSupport, (n : ℝ) ^ (2 : ℕ) * r ^ n *
          (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ)) :=
        Summable.tsum_le_tsum hterm hsum (S.mul_left _)
    _ = _ := by rw [tsum_mul_left]; ring

/-- `n² rⁿ ≤ K r'ⁿ` for `0 ≤ r < r'`. -/
theorem exists_sq_mul_pow_le_pow {r r' : ℝ} (hr : 0 ≤ r) (hrr : r < r') :
    ∃ K : ℝ, ∀ n : ℕ, (n : ℝ) ^ (2 : ℕ) * r ^ n ≤ K * r' ^ n := by
  have hr'0 : 0 < r' := lt_of_le_of_lt hr hrr
  have hq0 : 0 ≤ r / r' := div_nonneg hr hr'0.le
  have hq1 : r / r' < 1 := (div_lt_one hr'0).mpr hrr
  have hsum : Summable fun n : ℕ => (n : ℝ) ^ (2 : ℕ) * (r / r') ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])
  refine ⟨∑' n : ℕ, (n : ℝ) ^ (2 : ℕ) * (r / r') ^ n, fun n => ?_⟩
  have hle : (n : ℝ) ^ (2 : ℕ) * (r / r') ^ n ≤ ∑' n : ℕ, (n : ℝ) ^ (2 : ℕ) * (r / r') ^ n :=
    hsum.le_tsum n fun j _ => by positivity
  have hpos : 0 < r' ^ n := pow_pos hr'0 n
  calc (n : ℝ) ^ (2 : ℕ) * r ^ n = (n : ℝ) ^ (2 : ℕ) * (r / r') ^ n * r' ^ n := by
        rw [div_pow, mul_assoc, div_mul_cancel₀ _ hpos.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right hle hpos.le

/-- **Lower half of the Li growth law.** If `Re(2λ_n) ≥ -C r'ⁿ` holds for every `r' > r` (with
`r ≥ 1`), then every normalised Cayley root has modulus at most `r`. -/
theorem cayley_le_of_xiLiPaired_lower {r : ℝ} (hr : 1 ≤ r)
    (h : ∀ r' : ℝ, r < r' → ∃ C : ℝ, ∀ n : ℕ, -(C * r' ^ n) ≤ (xiLiPaired n).re) :
    ∀ ρ : ℂ, xi ρ = 0 → ‖xiRootV ρ‖ ≤ r := by
  intro ρ₁ hρ₁
  by_contra hlt
  push Not at hlt
  set ρ₀ : XiDivisorSupport := ⟨ρ₁, mem_xi_divisor_support_of_eq_zero hρ₁⟩
  obtain ⟨M, hM1, hMb⟩ := exists_bound_xiRootW
  have hvM : ∀ ρ : XiDivisorSupport, ‖xiRootV (ρ : ℂ)‖ ≤ M := fun ρ => by
    rw [norm_xiRootV (liSupport_ne_zero ρ) (liSupport_ne_one ρ)]; exact hMb ρ
  set r' : ℝ := (r + ‖xiRootV ρ₁‖) / 2
  obtain ⟨C, hC⟩ := h r' (by simp only [r']; linarith)
  obtain ⟨n, hn⟩ := exists_re_tsum_liTerm_lt_neg_pow one_le_liSupport_mult
    (fun ρ => one_le_norm_xiRootV (liSupport_ne_zero ρ) (liSupport_ne_one ρ)) hvM
    summable_liSupport_mult_norm_xiRootV_sub_one_sq (i₀ := ρ₀) (by simp only [ρ₀]; linarith)
    (ρ := r') (B := C) (by simp only [r']; linarith) (by simp only [ρ₀, r']; linarith)
  have hCn := hC n
  rw [re_xiLiPaired_eq_tsum] at hCn
  linarith

/-- **The Li growth law.** For `r ≥ 1`, every normalised Cayley root `v_ρ` (the member of
`{w_ρ, w_ρ⁻¹}` of modulus at least one) has modulus at most `r` iff for every `r' > r` some `C`
gives `Re(2λ_n) ≥ -C r'ⁿ` for all `n`. The negative Li coefficients therefore grow exactly at the rate
`max_ρ ‖v_ρ‖`. -/
theorem cayley_le_iff_xiLiPaired_lower {r : ℝ} (hr : 1 ≤ r) :
    (∀ ρ : ℂ, xi ρ = 0 → ‖xiRootV ρ‖ ≤ r) ↔
      ∀ r' : ℝ, r < r' → ∃ C : ℝ, ∀ n : ℕ, -(C * r' ^ n) ≤ (xiLiPaired n).re := by
  refine ⟨fun h r' hrr => ?_, cayley_le_of_xiLiPaired_lower hr⟩
  obtain ⟨C, hC⟩ := exists_norm_xiLiPaired_le_of_cayley h
  obtain ⟨K, hK⟩ := exists_sq_mul_pow_le_pow (by linarith) hrr
  refine ⟨max C 0 * K, fun n => ?_⟩
  have h1 : ‖xiLiPaired n‖ ≤ max C 0 * ((n : ℝ) ^ (2 : ℕ) * r ^ n) :=
    (hC n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have h2 : max C 0 * ((n : ℝ) ^ (2 : ℕ) * r ^ n) ≤ max C 0 * (K * r' ^ n) :=
    mul_le_mul_of_nonneg_left (hK n) (le_max_right _ _)
  have h3 : -‖xiLiPaired n‖ ≤ (xiLiPaired n).re := by
    have := Complex.abs_re_le_norm (xiLiPaired n); linarith [neg_abs_le (xiLiPaired n).re]
  linarith [mul_assoc (max C 0) K (r' ^ n)]

/-- RH is the case `r = 1` of the Cayley bound. -/
theorem riemannHypothesis_iff_cayley_le_one :
    RiemannHypothesis ↔ ∀ ρ : ℂ, xi ρ = 0 → ‖xiRootV ρ‖ ≤ 1 := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  refine forall₂_congr fun ρ hρ => ?_
  set q : XiDivisorSupport := ⟨ρ, mem_xi_divisor_support_of_eq_zero hρ⟩
  have h0 : ρ ≠ 0 := liSupport_ne_zero q
  have h1 : ρ ≠ 1 := liSupport_ne_one q
  have hpos : 0 < ‖xiRootW ρ‖ := norm_pos_iff.mpr (xiRootW_ne_zero h0 h1)
  rw [← norm_xiRootW_eq_one_iff h0, norm_xiRootV h0 h1]
  constructor
  · intro h; rw [h, inv_one, max_self]
  · intro h
    have ha : ‖xiRootW ρ‖ ≤ 1 := (le_max_left _ _).trans h
    have hb : ‖xiRootW ρ‖⁻¹ ≤ 1 := (le_max_right _ _).trans h
    rw [inv_le_one₀ hpos] at hb
    linarith

/-- **Li's criterion with exponential slack.** RH holds iff for every `r > 1` some `C` gives
`Re(2λ_n) ≥ -C rⁿ` for all `n`. -/
theorem riemannHypothesis_iff_xiLiPaired_subexp :
    RiemannHypothesis ↔
      ∀ r : ℝ, 1 < r → ∃ C : ℝ, ∀ n : ℕ, -(C * r ^ n) ≤ (xiLiPaired n).re := by
  rw [riemannHypothesis_iff_cayley_le_one]
  exact cayley_le_iff_xiLiPaired_lower le_rfl

/-- Under RH, `‖2λ_n‖ ≤ C n²`. -/
theorem exists_norm_xiLiPaired_le_sq_of_rh (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ n : ℕ, ‖xiLiPaired n‖ ≤ C * (n : ℝ) ^ (2 : ℕ) := by
  obtain ⟨C, hC⟩ := exists_norm_xiLiPaired_le_of_cayley (riemannHypothesis_iff_cayley_le_one.mp hRH)
  exact ⟨C, fun n => by simpa using hC n⟩

end RHTower
