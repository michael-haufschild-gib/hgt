import GaloisForLFunctions.RHTower.LiTermBound
noncomputable section

/-!
# The hard half of Li's criterion, abstractly

Let `w : ι → ℂ` be a family with multiplicities `m i ≥ 1`, all `‖w i‖` in a fixed annulus, and
`Σ m i ‖w i - 1‖² < ∞`.  If some `w i₀` is **not** unimodular then one of the paired Li sums

`Σ_i m i (2 - w iⁿ - w i⁻ⁿ)`

has negative real part.

The proof is elementary — no analytic continuation and no Pringsheim.  Normalise each `w` to the
representative of `{w, w⁻¹}` of modulus `≥ 1` (the summand is invariant).  Only finitely many
representatives can exceed `q := (1 + ‖w i₀‖)/2 > 1`, because `‖w - 1‖ ≥ ‖w‖ - 1` and the weighted
squares are summable.  The infinite tail is `O(n² qⁿ)` by `LiTermBound`, while a simultaneous
recurrence on the torus — a pigeonhole from compactness of a finite product of unit circles —
produces arbitrarily large `n` with every `Re(wⁿ)` at least `‖w‖ⁿ/2`, so the finite part is at least
`m i₀ ‖w i₀‖ⁿ/2`.  Since `‖w i₀‖ > q`, the exponential beats the polynomial.
-/

open Complex
namespace RHTower

/-- **Simultaneous recurrence on the torus.**  Finitely many unimodular numbers have a common
power arbitrarily close to `1`. -/
theorem exists_pos_pow_sub_one_lt {ι : Type*} [Fintype ι] (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ m : ℕ, 0 < m ∧ ∀ i, ‖u i ^ m - 1‖ < ε := by
  classical
  set f : ℕ → (ι → ℂ) := fun n i => u i ^ n with hf
  have hmem : ∀ n, f n ∈ Metric.closedBall (0 : ι → ℂ) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    show ‖u i ^ n‖ ≤ 1
    rw [norm_pow, hu i, one_pow]
  have hcpt : IsCompact (Metric.closedBall (0 : ι → ℂ) 1) := isCompact_closedBall _ _
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hmem
  have hcauchy : CauchySeq (f ∘ φ) := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy ε hε
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  refine ⟨φ (N + 1) - φ N, by omega, fun i => ?_⟩
  have hd : dist ((f ∘ φ) (N + 1)) ((f ∘ φ) N) < ε := hN (N + 1) (by omega) N (by omega)
  rw [dist_eq_norm] at hd
  have hcoord : ‖(f (φ (N + 1)) - f (φ N)) i‖ ≤ ‖f (φ (N + 1)) - f (φ N)‖ :=
    norm_le_pi_norm _ i
  have hval : (f (φ (N + 1)) - f (φ N)) i = u i ^ φ N * (u i ^ (φ (N + 1) - φ N) - 1) := by
    show u i ^ φ (N + 1) - u i ^ φ N = u i ^ φ N * (u i ^ (φ (N + 1) - φ N) - 1)
    rw [mul_sub, mul_one, ← pow_add]
    congr 2
    omega
  rw [hval, norm_mul, norm_pow, hu i, one_pow, one_mul] at hcoord
  exact lt_of_le_of_lt hcoord hd

/-- A unimodular number within distance `1` of `1` has real part above `1/2`. -/
theorem re_ge_half_of_norm_sub_one_lt_one {v : ℂ} (hv : ‖v‖ = 1) (h : ‖v - 1‖ < 1) :
    1 / 2 < v.re := by
  have hsq : ‖v - 1‖ ^ 2 = 2 - 2 * v.re := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    have hv2 : v.re ^ 2 + v.im ^ 2 = 1 := by
      have hh : ‖v‖ ^ 2 = 1 := by rw [hv]; norm_num
      rw [Complex.sq_norm, Complex.normSq_apply] at hh
      nlinarith [hh]
    nlinarith
  nlinarith [norm_nonneg (v - 1), hsq]

/-- Powers of unimodular numbers can be made simultaneously close to `1` at arbitrarily large
exponents. -/
theorem exists_ge_pow_re_gt_half {ι : Type*} [Fintype ι] (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (N : ℕ) : ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∀ i, 1 / 2 < (u i ^ n).re := by
  obtain ⟨m, hm, hlt⟩ := exists_pos_pow_sub_one_lt (fun i => u i ^ (N + 1)) (by
    intro i
    rw [norm_pow, hu i, one_pow]) (ε := 1) one_pos
  refine ⟨(N + 1) * m, ?_, by positivity, fun i => ?_⟩
  · calc N ≤ (N + 1) * 1 := by omega
      _ ≤ (N + 1) * m := by
          exact Nat.mul_le_mul_left _ hm
  · have hpow : u i ^ ((N + 1) * m) = (u i ^ (N + 1)) ^ m := by rw [← pow_mul]
    have hnorm : ‖u i ^ ((N + 1) * m)‖ = 1 := by rw [norm_pow, hu i, one_pow]
    refine re_ge_half_of_norm_sub_one_lt_one hnorm ?_
    rw [hpow]
    exact hlt i


variable {ι : Type*} {v : ι → ℂ} {m : ι → ℝ} {M : ℝ}

/-- For a family bounded away from the unit circle from inside, the `n`-th Li family is
summable. -/
theorem summable_re_liTerm_of_one_le
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ 2) (n : ℕ) :
    Summable fun i => m i * (liTerm (v i) n).re := by
  refine Summable.of_norm_bounded (hs.mul_left ((n : ℝ) ^ 2 * M ^ n)) fun i => ?_
  have hvne : v i ≠ 0 := by
    intro h
    have := hv i
    rw [h] at this
    simp at this
    linarith
  have hmax : max ‖v i‖ ‖v i‖⁻¹ = ‖v i‖ := by
    refine max_eq_left ?_
    have h1 : (0:ℝ) < ‖v i‖ := lt_of_lt_of_le zero_lt_one (hv i)
    rw [inv_le_iff_one_le_mul₀ h1]
    nlinarith [hv i]
  have hbase := norm_liTerm_le hvne n
  rw [hmax] at hbase
  have hpow : ‖v i‖ ^ n ≤ M ^ n := pow_le_pow_left₀ (norm_nonneg _) (hM i) n
  have hre : ‖m i * (liTerm (v i) n).re‖ ≤ m i * ‖liTerm (v i) n‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hm i)]
    exact mul_le_mul_of_nonneg_left (le_trans (abs_re_le_norm _) (le_refl _)) (hm i)
  refine le_trans hre ?_
  have hstep : ‖liTerm (v i) n‖ ≤ (n : ℝ) ^ 2 * M ^ n * ‖v i - 1‖ ^ 2 := by
    refine le_trans hbase ?_
    have h2 : (0:ℝ) ≤ ‖v i - 1‖ ^ 2 := sq_nonneg _
    have h3 : (0:ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    rw [mul_assoc, mul_assoc]
    gcongr
  calc m i * ‖liTerm (v i) n‖ ≤ m i * ((n : ℝ) ^ 2 * M ^ n * ‖v i - 1‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hstep (hm i)
    _ = (n : ℝ) ^ 2 * M ^ n * (m i * ‖v i - 1‖ ^ 2) := by ring


theorem finite_far_set (hm : ∀ i, 1 ≤ m i)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ 2) {q : ℝ} (hq : 1 < q) :
    {i | q ≤ ‖v i‖}.Finite := by
  have hpos : (0:ℝ) < (q - 1) ^ 2 := by positivity
  have htend := hs.tendsto_cofinite_zero
  have hev : ∀ᶠ i in Filter.cofinite,
      m i * ‖v i - 1‖ ^ 2 ∈ Metric.ball (0 : ℝ) ((q - 1) ^ 2) :=
    htend (Metric.ball_mem_nhds 0 hpos)
  have hfin : {i | ¬ (m i * ‖v i - 1‖ ^ 2 ∈ Metric.ball (0 : ℝ) ((q - 1) ^ 2))}.Finite :=
    Filter.eventually_cofinite.mp hev
  refine Set.Finite.subset hfin fun i hi => ?_
  have hge : q ≤ ‖v i‖ := hi
  have hsub : q - 1 ≤ ‖v i - 1‖ := by
    have h := norm_sub_norm_le (v i) (1 : ℂ)
    rw [norm_one] at h
    linarith
  simp only [Set.mem_setOf_eq, Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
  have h1 : (q - 1) ^ 2 ≤ ‖v i - 1‖ ^ 2 := by nlinarith [hq]
  have h2 : ‖v i - 1‖ ^ 2 ≤ m i * ‖v i - 1‖ ^ 2 := by
    nlinarith [sq_nonneg ‖v i - 1‖, hm i]
  rw [abs_of_nonneg (by nlinarith [sq_nonneg ‖v i - 1‖, hm i] : (0:ℝ) ≤ m i * ‖v i - 1‖ ^ 2)]
  linarith


/-- **The hard half of Li's criterion, abstract form.**  If one member of the family lies strictly
outside the unit circle, then some paired Li sum is negative. -/
theorem exists_re_tsum_liTerm_neg
    (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ 2)
    {i₀ : ι} (hlt : 1 < ‖v i₀‖) :
    ∃ n : ℕ, (∑' i, m i * (liTerm (v i) n).re) < 0 := by
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
  set C : ℝ := ∑' i, m i * ‖v i - 1‖ ^ 2 with hCdef
  have hC0 : 0 ≤ C := tsum_nonneg fun i => by
    have := hm i
    have h2 : (0:ℝ) ≤ ‖v i - 1‖ ^ 2 := sq_nonneg _
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
  have hlim2 : Filter.Tendsto (fun n : ℕ => C * ((n : ℝ) ^ 2 * r ^ n)) Filter.atTop (nhds 0) := by
    have hsum : Summable (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) := by
      refine summable_pow_mul_geometric_of_norm_lt_one 2 ?_
      rw [Real.norm_eq_abs, abs_of_nonneg hr0]
      exact hr1
    simpa using hsum.tendsto_atTop_zero.const_mul C
  have hlim : Filter.Tendsto (fun n : ℕ => 3 * T * r ^ n + C * ((n : ℝ) ^ 2 * r ^ n))
      Filter.atTop (nhds 0) := by simpa using hlim1.add hlim2
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
      (n : ℝ) ^ 2 * q ^ n * (m (i : ι) * ‖v (i : ι) - 1‖ ^ 2) :=
    (hs.subtype _).mul_left _
  have hBle : ∀ i : {x // x ∈ (↑S : Set ι)ᶜ},
      m (i : ι) * (liTerm (v (i : ι)) n).re
        ≤ (n : ℝ) ^ 2 * q ^ n * (m (i : ι) * ‖v (i : ι) - 1‖ ^ 2) := by
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
    have hchain : ‖liTerm (v i) n‖ ≤ (n : ℝ) ^ 2 * q ^ n * ‖v i - 1‖ ^ 2 := by
      refine le_trans hbase ?_
      have h2 : (0:ℝ) ≤ ‖v i - 1‖ ^ 2 := sq_nonneg _
      have h3 : (0:ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
      rw [mul_assoc, mul_assoc]
      gcongr
    calc m i * (liTerm (v i) n).re
        ≤ m i * ((n : ℝ) ^ 2 * q ^ n * ‖v i - 1‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (le_trans hre hchain) (hm0 i)
      _ = (n : ℝ) ^ 2 * q ^ n * (m i * ‖v i - 1‖ ^ 2) := by ring
  have htailC : (∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, m (i : ι) * ‖v (i : ι) - 1‖ ^ 2) ≤ C := by
    have hsp := hs.sum_add_tsum_compl (s := S)
    have hSnn : (0:ℝ) ≤ ∑ i ∈ S, m i * ‖v i - 1‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => by nlinarith [hm0 i, sq_nonneg ‖v i - 1‖]
    rw [hCdef, ← hsp]
    linarith
  have htail : (∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, m (i : ι) * (liTerm (v (i : ι)) n).re)
      ≤ (n : ℝ) ^ 2 * q ^ n * C := by
    refine le_trans (Summable.tsum_le_tsum hBle
      (hsummable.subtype ((↑S : Set ι)ᶜ)) hBsum) ?_
    rw [Summable.tsum_mul_left]
    · have hcoef : (0:ℝ) ≤ (n : ℝ) ^ 2 * q ^ n := by positivity
      exact mul_le_mul_of_nonneg_left htailC hcoef
    · exact hs.subtype _
  -- so the finite part is bounded below
  have hSlow : -((n : ℝ) ^ 2 * q ^ n * C) ≤ ∑ i ∈ S, m i * (liTerm (v i) n).re := by
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
  have hkey : m i₀ * (W ^ n / 2) ≤ 3 * T + (n : ℝ) ^ 2 * q ^ n * C := by
    have h1 := hbig i₀ hi₀S
    have h2 : m i₀ * (W ^ n / 2) ≤ m i₀ * (v i₀ ^ n).re := by
      have := hm0 i₀
      nlinarith
    linarith
  -- exponential beats polynomial
  have hW0n : (0:ℝ) < W ^ n := by positivity
  have hqn : (1:ℝ) ≤ q ^ n := one_le_pow₀ hq1.le
  have hrn : r ^ n = q ^ n / W ^ n := by rw [hrdef, div_pow]
  have hfinal : m i₀ / 2 ≤ 3 * T * r ^ n + C * ((n : ℝ) ^ 2 * r ^ n) := by
    have hrn' : r ^ n * W ^ n = q ^ n := by
      rw [hrn]
      field_simp
    have hstep : m i₀ / 2 * W ^ n ≤ 3 * T + (n : ℝ) ^ 2 * q ^ n * C := by
      calc m i₀ / 2 * W ^ n = m i₀ * (W ^ n / 2) := by ring
        _ ≤ 3 * T + (n : ℝ) ^ 2 * q ^ n * C := hkey
    have hexp : (3 * T * r ^ n + C * ((n : ℝ) ^ 2 * r ^ n)) * W ^ n
        = 3 * T * q ^ n + C * (n : ℝ) ^ 2 * q ^ n := by
      rw [show (3 * T * r ^ n + C * ((n : ℝ) ^ 2 * r ^ n)) * W ^ n
        = 3 * T * (r ^ n * W ^ n) + C * (n : ℝ) ^ 2 * (r ^ n * W ^ n) from by ring, hrn']
    refine le_of_mul_le_mul_right ?_ hW0n
    rw [hexp]
    nlinarith [hT0, hqn, hC0]
  have hlast := hN n hnN
  linarith

end RHTower
