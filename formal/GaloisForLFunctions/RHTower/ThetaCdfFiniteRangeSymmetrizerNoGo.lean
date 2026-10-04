import GaloisForLFunctions.RHTower.ThetaCdfFixedShiftAction

/-!
# The theta CDF quotient has no coercive finite-range Fourier symmetrizer

The exact quotient matrix on `ℓ²(ℤ∖{0})` is `D_{m,n} = (Φ_m − Φ_{n−m})/(2πn)`.  A bounded operator
`G` that is uniformly coercive, has finite absolute-frequency range `W`
(`G_{m,n} = 0` when `||m| − |n|| > W`) and satisfies `GD = D*G` entrywise does not exist: the
fixed-shift law forces every row sum of `G` to vanish, and then the block indicators `u_N` have
bounded quadratic form while `‖u_N‖² = 2N`.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-! ## The quotient matrix and its entry asymptotics -/

/-- The exact theta CDF-action quotient `D_{m,n} = (Φ_m − Φ_{n−m})/(2πn)`. -/
def cdfQuotientMatrix (m n : ℤ) : ℝ := (cdfAction m - cdfAction (n - m)) / (2 * Real.pi * n)

theorem tendsto_cdfAction_add_sub (a : ℤ) :
    Tendsto (fun n : ℕ => cdfAction (n + a) - cdfAction n) atTop (𝓝 0) := by
  have h := (tendsto_mul_cdfAction_add_sub a).div_atTop tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem tendsto_mul_cdfAction_sub_shift (j i : ℤ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (cdfAction (n + j) - cdfAction (n + i))) atTop (𝓝 0) := by
  have h := (tendsto_mul_cdfAction_add_sub j).sub (tendsto_mul_cdfAction_add_sub i)
  rw [sub_zero] at h
  refine h.congr fun n => ?_
  ring

/-- Column entries at `k = n + j`: `n D_{n+j, m} → 0`. -/
theorem tendsto_mul_cdfQuotientMatrix_add (m j : ℤ) :
    Tendsto (fun n : ℕ => (n : ℝ) * cdfQuotientMatrix ((n : ℤ) + j) m) atTop (𝓝 0) := by
  have h := (tendsto_mul_cdfAction_sub_shift j (j - m)).div_const (2 * Real.pi * m)
  rw [zero_div] at h
  refine h.congr fun n => ?_
  rw [cdfQuotientMatrix, show m - ((n : ℤ) + j) = -((n : ℤ) + (j - m)) by ring, cdfAction_neg]
  ring

/-- Column entries at `k = −(n + j)`: `n D_{−(n+j), m} → 0`. -/
theorem tendsto_mul_cdfQuotientMatrix_neg_add (m j : ℤ) :
    Tendsto (fun n : ℕ => (n : ℝ) * cdfQuotientMatrix (-((n : ℤ) + j)) m) atTop (𝓝 0) := by
  have h := (tendsto_mul_cdfAction_sub_shift j (j + m)).div_const (2 * Real.pi * m)
  rw [zero_div] at h
  refine h.congr fun n => ?_
  rw [cdfQuotientMatrix, cdfAction_neg, show m - -((n : ℤ) + j) = (n : ℤ) + (j + m) by ring]
  ring

/-! ## Abstract banded matrices -/

/-- The finite band `{n : ||n| − |m|| ≤ W}`. -/
def bandSet (W : ℕ) (m : ℤ) : Finset ℤ :=
  Finset.Icc (|m| - W) (|m| + W) ∪ Finset.Icc (-|m| - W) (-|m| + W)

theorem mem_bandSet_of_abs_sub_le {W : ℕ} {m n : ℤ} (h : |(|m| - |n|)| ≤ W) : n ∈ bandSet W m := by
  rw [bandSet, Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
  rcases abs_le.1 h with ⟨h1, h2⟩
  rcases le_total 0 n with hn | hn
  · left; rw [abs_of_nonneg hn] at h1 h2; constructor <;> linarith
  · right; rw [abs_of_nonpos hn] at h1 h2; constructor <;> linarith

theorem card_bandSet_le (W : ℕ) (m : ℤ) : (bandSet W m).card ≤ 2 * (2 * W + 1) := by
  refine (Finset.card_union_le _ _).trans ?_
  rw [Int.card_Icc, Int.card_Icc]
  omega

theorem bandedMatrix_eq_zero_of_not_mem_bandSet {A : ℤ → ℤ → ℂ} {W : ℕ}
    (hband : ∀ m n, (W : ℤ) < |(|m| - |n|)| → A m n = 0) {m n : ℤ} (h : n ∉ bandSet W m) :
    A m n = 0 :=
  hband m n (not_le.1 fun h' => h (mem_bandSet_of_abs_sub_le h'))

/-- The window `[−L, L]` around a row. -/
theorem bandedMatrix_eq_zero_of_not_mem_Icc {A : ℤ → ℤ → ℂ} {W : ℕ}
    (hband : ∀ m n, (W : ℤ) < |(|m| - |n|)| → A m n = 0) {m n : ℤ}
    (h : n ∉ Finset.Icc (-(|m| + W)) (|m| + W)) : A m n = 0 := by
  refine hband m n ?_
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at h
  have hn : |m| + W < |n| := by
    rcases h with h | h
    · rw [abs_of_neg (by linarith [abs_nonneg m] : n < 0)]; linarith
    · rw [abs_of_pos (by linarith [abs_nonneg m] : 0 < n)]; linarith
  rw [abs_of_neg (by linarith)]
  linarith

/-- **Every row sum vanishes.**  For a bounded banded matrix with `GD = D*G` entrywise. -/
theorem rowSum_eq_zero_of_intertwining (A : ℤ → ℤ → ℂ) (B : ℝ) (W : ℕ)
    (hbound : ∀ m n, ‖A m n‖ ≤ B)
    (hband : ∀ m n, (W : ℤ) < |(|m| - |n|)| → A m n = 0)
    (hinter : ∀ m n : ℤ, m ≠ 0 → n ≠ 0 →
      ∑' k, A m k * cdfQuotientMatrix k n = ∑' k, (cdfQuotientMatrix k m : ℂ) * A k n)
    {m : ℤ} (hm : m ≠ 0) :
    ∑ k ∈ Finset.Icc (-(|m| + W)) (|m| + W), A m k = 0 := by
  set K := Finset.Icc (-(|m| + W)) (|m| + W)
  set S := ∑ k ∈ K, A m k
  set C : ℂ := ∑ k ∈ K, A m k * (cdfAction k : ℂ)
  -- the left side
  have hleft : ∀ n : ℕ, 0 < n → (2 * Real.pi * n : ℂ) * ∑' k, A m k * cdfQuotientMatrix k n =
      C - S * cdfAction n - ∑ k ∈ K, A m k * ((cdfAction ((n : ℤ) + -k) - cdfAction n : ℝ) : ℂ) := by
    intro n hn
    have hnC : (2 * Real.pi * n : ℂ) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
      simp [this, hπ]
    rw [tsum_eq_sum (s := K) fun k hk => by rw [bandedMatrix_eq_zero_of_not_mem_Icc hband hk, zero_mul],
      Finset.mul_sum]
    simp only [C, S, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cdfQuotientMatrix, show (n : ℤ) + -k = (n : ℤ) - k by ring]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    push_cast
    field_simp
    ring
  -- the right side
  have hright : Tendsto (fun n : ℕ => (2 * Real.pi * n : ℂ) *
      ∑' k, (cdfQuotientMatrix k m : ℂ) * A k n) atTop (𝓝 0) := by
    set J := Finset.Icc (-(W : ℤ)) W
    have hlim : Tendsto (fun n : ℕ => 2 * Real.pi * B * ∑ j ∈ J,
        (|(n : ℝ) * cdfQuotientMatrix ((n : ℤ) + j) m| +
          |(n : ℝ) * cdfQuotientMatrix (-((n : ℤ) + j)) m|)) atTop (𝓝 0) := by
      have := tendsto_finsetSum J fun j _ =>
        ((tendsto_mul_cdfQuotientMatrix_add m j).abs.add (tendsto_mul_cdfQuotientMatrix_neg_add m j).abs)
      simp only [abs_zero, add_zero, Finset.sum_const_zero] at this
      simpa using this.const_mul (2 * Real.pi * B)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_gt_atTop W] with n hn
    set T := J.image (fun j => (n : ℤ) + j) ∪ J.image (fun j => -((n : ℤ) + j))
    have hT : ∀ k, k ∉ T → A k n = 0 := by
      intro k hk
      refine hband k n ?_
      by_contra hle
      push Not at hle
      apply hk
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
      have hn0 : (0 : ℤ) ≤ n := by positivity
      rw [abs_of_nonneg hn0] at hle
      rcases abs_le.1 hle with ⟨h1, h2⟩
      rcases le_total 0 k with hk0 | hk0
      · left; refine ⟨k - n, ?_, by ring⟩
        rw [abs_of_nonneg hk0] at h1 h2
        rw [Finset.mem_Icc]; constructor <;> linarith
      · right; refine ⟨-k - n, ?_, by ring⟩
        rw [abs_of_nonpos hk0] at h1 h2
        rw [Finset.mem_Icc]; constructor <;> linarith
    rw [tsum_eq_sum (s := T) fun k hk => by rw [hT k hk, mul_zero], Finset.mul_sum]
    have hB : 0 ≤ B := (norm_nonneg _).trans (hbound 0 0)
    have hterm : ∀ k, ‖(2 * Real.pi * n : ℂ) * ((cdfQuotientMatrix k m : ℂ) * A k n)‖ ≤
        2 * Real.pi * B * |(n : ℝ) * cdfQuotientMatrix k m| := fun k => by
      have h2 : ‖(2 * Real.pi * n : ℂ)‖ = 2 * Real.pi * n := by
        rw [show (2 * Real.pi * n : ℂ) = ((2 * Real.pi * n : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖(2 * Real.pi * n : ℂ) * ((cdfQuotientMatrix k m : ℂ) * A k n)‖
          = ‖(2 * Real.pi * n : ℂ)‖ * (‖(cdfQuotientMatrix k m : ℂ)‖ * ‖A k n‖) := by
            rw [norm_mul (2 * Real.pi * n : ℂ), norm_mul (cdfQuotientMatrix k m : ℂ)]
        _ = 2 * Real.pi * n * (|cdfQuotientMatrix k m| * ‖A k n‖) := by
            rw [h2, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 2 * Real.pi * n * (|cdfQuotientMatrix k m| * B) := by
            gcongr; exact hbound k n
        _ = 2 * Real.pi * B * |(n : ℝ) * cdfQuotientMatrix k m| := by
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (n : ℕ) : (0 : ℝ) ≤ n)]; ring
    have hinj1 : Set.InjOn (fun j : ℤ => (n : ℤ) + j) J := fun a _ b _ h => by simpa using h
    have hinj2 : Set.InjOn (fun j : ℤ => -((n : ℤ) + j)) J := fun a _ b _ h => by simpa using h
    calc ‖∑ k ∈ T, (2 * Real.pi * n : ℂ) * ((cdfQuotientMatrix k m : ℂ) * A k n)‖
        ≤ ∑ k ∈ T, 2 * Real.pi * B * |(n : ℝ) * cdfQuotientMatrix k m| :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hterm k)
      _ ≤ ∑ k ∈ J.image (fun j => (n : ℤ) + j), 2 * Real.pi * B * |(n : ℝ) * cdfQuotientMatrix k m| +
          ∑ k ∈ J.image (fun j => -((n : ℤ) + j)), 2 * Real.pi * B * |(n : ℝ) * cdfQuotientMatrix k m| := by
          rw [← Finset.sum_union_inter]
          have : 0 ≤ ∑ k ∈ J.image (fun j => (n : ℤ) + j) ∩ J.image (fun j => -((n : ℤ) + j)),
              2 * Real.pi * B * |(n : ℝ) * cdfQuotientMatrix k m| :=
            Finset.sum_nonneg fun k _ => by positivity
          linarith
      _ = 2 * Real.pi * B * ∑ j ∈ J, (|(n : ℝ) * cdfQuotientMatrix ((n : ℤ) + j) m| +
          |(n : ℝ) * cdfQuotientMatrix (-((n : ℤ) + j)) m|) := by
          rw [Finset.sum_image hinj1, Finset.sum_image hinj2, ← Finset.mul_sum, ← Finset.mul_sum,
            ← mul_add, ← Finset.sum_add_distrib]
  -- combine
  have hE : Tendsto (fun n : ℕ => ∑ k ∈ K, A m k * ((cdfAction ((n : ℤ) + -k) - cdfAction n : ℝ) : ℂ))
      atTop (𝓝 0) := by
    have := tendsto_finsetSum K fun k _ =>
      ((Complex.continuous_ofReal.tendsto 0).comp (tendsto_cdfAction_add_sub (-k))).const_mul (A m k)
    simpa using this
  have hSΦ : Tendsto (fun n : ℕ => S * (cdfAction n : ℂ)) atTop (𝓝 C) := by
    have hdiff := hright.add hE
    rw [add_zero] at hdiff
    have h2 := (tendsto_const_nhds (x := C)).sub hdiff
    rw [sub_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← hinter m n hm (by exact_mod_cast hn.ne'), hleft n hn]
    ring
  by_contra hS
  have hnorm : Tendsto (fun n : ℕ => ‖S‖ * cdfAction n) atTop atTop :=
    tendsto_cdfAction_atTop.const_mul_atTop (norm_pos_iff.2 hS)
  have h1 : Tendsto (fun n : ℕ => ‖S * (cdfAction n : ℂ)‖) atTop (𝓝 ‖C‖) := hSΦ.norm
  have h2 : Tendsto (fun n : ℕ => ‖S * (cdfAction n : ℂ)‖) atTop atTop := by
    refine hnorm.congr' ?_
    filter_upwards [tendsto_cdfAction_atTop.eventually_ge_atTop 0] with n hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  exact not_tendsto_nhds_of_tendsto_atTop h2 _ h1

/-! ## Block indicators have bounded quadratic form -/

/-- The block support `{n : 1 ≤ |n| ≤ N}`. -/
def blockSupport (N : ℕ) : Finset ℤ := (Finset.Icc (-(N : ℤ)) N).erase 0

theorem card_blockSupport (N : ℕ) : (blockSupport N).card = 2 * N := by
  rw [blockSupport, Finset.card_erase_of_mem (by simp), Int.card_Icc]
  omega

theorem ne_zero_of_mem_blockSupport {N : ℕ} {m : ℤ} (h : m ∈ blockSupport N) : m ≠ 0 :=
  Finset.ne_of_mem_erase h

/-- **Bounded quadratic form.**  With zero row sums, only the `≤ 2W` boundary rows of the block
contribute, each with at most `2(2W+1)` nonzero entries. -/
theorem norm_blockQuadForm_le (A : ℤ → ℤ → ℂ) (B : ℝ) (W : ℕ)
    (hbound : ∀ m n, ‖A m n‖ ≤ B)
    (hband : ∀ m n, (W : ℤ) < |(|m| - |n|)| → A m n = 0)
    (hrow : ∀ m : ℤ, m ≠ 0 → ∑ k ∈ Finset.Icc (-(|m| + W)) (|m| + W), A m k = 0)
    (hcol0 : ∀ m, A m 0 = 0) (N : ℕ) :
    ‖∑ m ∈ blockSupport N, ∑ n ∈ blockSupport N, A m n‖ ≤ 2 * W * (2 * (2 * W + 1) * B) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbound 0 0)
  set P : ℤ → Prop := fun m => (N : ℤ) < |m| + W
  have hinterior : ∀ m ∈ blockSupport N, ¬ P m → ∑ n ∈ blockSupport N, A m n = 0 := by
    intro m hm hP
    simp only [P, not_lt] at hP
    rw [blockSupport, Finset.sum_erase _ (hcol0 m)]
    rw [← Finset.sum_subset (s₁ := Finset.Icc (-(|m| + W)) (|m| + W))
      (fun n hn => by rw [Finset.mem_Icc] at hn ⊢; constructor <;> linarith [hn.1, hn.2])
      (fun n _ hn => bandedMatrix_eq_zero_of_not_mem_Icc hband hn)]
    exact hrow m (ne_zero_of_mem_blockSupport hm)
  have hrowbound : ∀ m, ‖∑ n ∈ blockSupport N, A m n‖ ≤ 2 * (2 * W + 1) * B := by
    intro m
    calc ‖∑ n ∈ blockSupport N, A m n‖ ≤ ∑ n ∈ blockSupport N, ‖A m n‖ := norm_sum_le _ _
      _ = ∑ n ∈ (blockSupport N).filter (· ∈ bandSet W m), ‖A m n‖ := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun n _ => ?_
          split_ifs with h
          · rfl
          · rw [bandedMatrix_eq_zero_of_not_mem_bandSet hband h, norm_zero]
      _ ≤ ∑ n ∈ bandSet W m, ‖A m n‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => (Finset.mem_filter.1 hn).2)
            fun _ _ _ => norm_nonneg _
      _ ≤ ∑ n ∈ bandSet W m, B := Finset.sum_le_sum fun n _ => hbound m n
      _ = (bandSet W m).card * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (2 * W + 1) * B := by
          gcongr
          exact_mod_cast card_bandSet_le W m
  have hcard : ((blockSupport N).filter P).card ≤ 2 * W := by
    have hsub : (blockSupport N).filter P ⊆
        Finset.Icc ((N : ℤ) - W + 1) N ∪ Finset.Icc (-(N : ℤ)) (-(N : ℤ) + W - 1) := by
      intro m hm
      rw [Finset.mem_filter, blockSupport, Finset.mem_erase, Finset.mem_Icc] at hm
      obtain ⟨⟨hm0, h1, h2⟩, hP⟩ := hm
      simp only [P] at hP
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
      rcases le_total 0 m with hm' | hm'
      · left; rw [abs_of_nonneg hm'] at hP; constructor <;> linarith
      · right; rw [abs_of_nonpos hm'] at hP; constructor <;> linarith
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    rw [Int.card_Icc, Int.card_Icc]
    omega
  calc ‖∑ m ∈ blockSupport N, ∑ n ∈ blockSupport N, A m n‖
      ≤ ∑ m ∈ blockSupport N, ‖∑ n ∈ blockSupport N, A m n‖ := norm_sum_le _ _
    _ = ∑ m ∈ (blockSupport N).filter P, ‖∑ n ∈ blockSupport N, A m n‖ := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun m hm => ?_
        split_ifs with h
        · rfl
        · rw [hinterior m hm h, norm_zero]
    _ ≤ ∑ m ∈ (blockSupport N).filter P, 2 * (2 * W + 1) * B := Finset.sum_le_sum fun m _ => hrowbound m
    _ = ((blockSupport N).filter P).card * (2 * (2 * W + 1) * B) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * W * (2 * (2 * W + 1) * B) := by
        gcongr
        exact_mod_cast hcard

/-- **Abstract no-go.**  No bounded banded matrix on `ℤ∖{0}` intertwines `D` with `D*` and is
coercive on the block indicators. -/
theorem no_coercive_banded_intertwiner (A : ℤ → ℤ → ℂ) (B : ℝ) (W : ℕ) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ m n, ‖A m n‖ ≤ B)
    (hband : ∀ m n, (W : ℤ) < |(|m| - |n|)| → A m n = 0)
    (hcol0 : ∀ m, A m 0 = 0)
    (hinter : ∀ m n : ℤ, m ≠ 0 → n ≠ 0 →
      ∑' k, A m k * cdfQuotientMatrix k n = ∑' k, (cdfQuotientMatrix k m : ℂ) * A k n)
    (hcoer : ∀ N : ℕ, c * (2 * N) ≤ (∑ m ∈ blockSupport N, ∑ n ∈ blockSupport N, A m n).re) :
    False := by
  have hrow : ∀ m : ℤ, m ≠ 0 → ∑ k ∈ Finset.Icc (-(|m| + W)) (|m| + W), A m k = 0 :=
    fun m hm => rowSum_eq_zero_of_intertwining A B W hbound hband hinter hm
  set K : ℝ := 2 * W * (2 * (2 * W + 1) * B)
  obtain ⟨N, hN⟩ := exists_nat_gt (K / (2 * c))
  have h1 := hcoer N
  have h2 := (Complex.re_le_norm _).trans (norm_blockQuadForm_le A B W hbound hband hrow hcol0 N)
  rw [div_lt_iff₀ (by positivity)] at hN
  linarith

/-! ## The operator statement on `ℓ²(ℤ∖{0})` -/

/-- The mean-zero Fourier index set `ℤ∖{0}`. -/
abbrev NonzeroFreq : Set ℤ := {0}ᶜ

/-- `ℓ²(ℤ∖{0})`. -/
abbrev nonzeroFreqL2 := lp (fun _ : NonzeroFreq => ℂ) 2

/-- The basis vector `e_i`. -/
def freqBasis (i : NonzeroFreq) : nonzeroFreqL2 := lp.single 2 i 1

theorem inner_freqBasis_left (i : NonzeroFreq) (f : nonzeroFreqL2) :
    ⟪freqBasis i, f⟫_ℂ = f i := by
  rw [freqBasis, lp.inner_single_left]
  simp

theorem norm_freqBasis (i : NonzeroFreq) : ‖freqBasis i‖ = 1 := by
  rw [freqBasis, lp.norm_single (by norm_num)]; simp

theorem inner_freqBasis_freqBasis (i j : NonzeroFreq) :
    ⟪freqBasis i, freqBasis j⟫_ℂ = if i = j then 1 else 0 := by
  rw [inner_freqBasis_left, freqBasis, lp.single_apply, Pi.single_apply]

/-- The matrix of an operator, extended by zero to all of `ℤ`. -/
def freqMatrix (G : nonzeroFreqL2 →L[ℂ] nonzeroFreqL2) (m n : ℤ) : ℂ :=
  if h : m ≠ 0 ∧ n ≠ 0 then ⟪freqBasis ⟨m, h.1⟩, G (freqBasis ⟨n, h.2⟩)⟫_ℂ else 0

theorem freqMatrix_apply (G : nonzeroFreqL2 →L[ℂ] nonzeroFreqL2) (m n : NonzeroFreq) :
    freqMatrix G m n = ⟪freqBasis m, G (freqBasis n)⟫_ℂ := by
  rw [freqMatrix, dif_pos ⟨m.2, n.2⟩]

/-- The block indicator `u_N = Σ_{1 ≤ |n| ≤ N} e_n`. -/
def blockIndicator (N : ℕ) : nonzeroFreqL2 :=
  ∑ m ∈ blockSupport N, if h : m ≠ 0 then freqBasis ⟨m, h⟩ else 0

theorem inner_blockIndicator (G : nonzeroFreqL2 →L[ℂ] nonzeroFreqL2) (N : ℕ) :
    ⟪blockIndicator N, G (blockIndicator N)⟫_ℂ =
      ∑ m ∈ blockSupport N, ∑ n ∈ blockSupport N, freqMatrix G m n := by
  rw [blockIndicator, map_sum, sum_inner]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [dif_pos (ne_zero_of_mem_blockSupport hm), dif_pos (ne_zero_of_mem_blockSupport hn),
    freqMatrix, dif_pos ⟨ne_zero_of_mem_blockSupport hm, ne_zero_of_mem_blockSupport hn⟩]

theorem norm_sq_blockIndicator (N : ℕ) : ‖blockIndicator N‖ ^ 2 = 2 * N := by
  rw [@norm_sq_eq_re_inner ℂ, blockIndicator, sum_inner]
  have h : ∀ m ∈ blockSupport N, ⟪(if h : m ≠ 0 then freqBasis ⟨m, h⟩ else 0),
      ∑ n ∈ blockSupport N, (if h : n ≠ 0 then freqBasis ⟨n, h⟩ else 0)⟫_ℂ = 1 := by
    intro m hm
    rw [inner_sum, dif_pos (ne_zero_of_mem_blockSupport hm)]
    rw [Finset.sum_eq_single m]
    · rw [dif_pos (ne_zero_of_mem_blockSupport hm), inner_freqBasis_freqBasis, if_pos rfl]
    · intro n hn hnm
      rw [dif_pos (ne_zero_of_mem_blockSupport hn), inner_freqBasis_freqBasis, if_neg]
      intro h; apply hnm; exact (congrArg Subtype.val h).symm
    · intro h; exact absurd hm h
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_blockSupport]
  simp

/-- **The theorem of the card.**  There is no bounded operator `G` on `ℓ²(ℤ∖{0})` with
`⟨u,Gu⟩ ≥ c‖u‖²`, `G_{m,n} = 0` for `||m|−|n|| > W`, and `GD = D*G` (entrywise, the sums being finite). -/
theorem no_coercive_finite_range_symmetrizer (G : nonzeroFreqL2 →L[ℂ] nonzeroFreqL2) {c : ℝ}
    (hc : 0 < c) (W : ℕ)
    (hcoer : ∀ u : nonzeroFreqL2, c * ‖u‖ ^ 2 ≤ (⟪u, G u⟫_ℂ).re)
    (hrange : ∀ m n : NonzeroFreq, (W : ℤ) < |(|(m : ℤ)| - |(n : ℤ)|)| →
      ⟪freqBasis m, G (freqBasis n)⟫_ℂ = 0)
    (hinter : ∀ m n : NonzeroFreq,
      ∑' k : NonzeroFreq, ⟪freqBasis m, G (freqBasis k)⟫_ℂ * cdfQuotientMatrix k n =
        ∑' k : NonzeroFreq, (cdfQuotientMatrix k m : ℂ) * ⟪freqBasis k, G (freqBasis n)⟫_ℂ) :
    False := by
  set A := freqMatrix G
  have hbound : ∀ m n, ‖A m n‖ ≤ ‖G‖ := by
    intro m n
    simp only [A, freqMatrix]
    split_ifs with h
    · refine (norm_inner_le_norm _ _).trans ?_
      rw [norm_freqBasis, one_mul]
      refine (G.le_opNorm _).trans ?_
      rw [norm_freqBasis, mul_one]
    · rw [norm_zero]; exact norm_nonneg _
  have hband : ∀ m n, (W : ℤ) < |(|m| - |n|)| → A m n = 0 := by
    intro m n h
    simp only [A, freqMatrix]
    split_ifs with h'
    · exact hrange ⟨m, h'.1⟩ ⟨n, h'.2⟩ h
    · rfl
  have hcol0 : ∀ m, A m 0 = 0 := fun m => by simp [A, freqMatrix]
  have hrow0 : ∀ n, A 0 n = 0 := fun n => by simp [A, freqMatrix]
  have hinter' : ∀ m n : ℤ, m ≠ 0 → n ≠ 0 →
      ∑' k, A m k * cdfQuotientMatrix k n = ∑' k, (cdfQuotientMatrix k m : ℂ) * A k n := by
    intro m n hm hn
    have h := hinter ⟨m, hm⟩ ⟨n, hn⟩
    have e1 := tsum_subtype NonzeroFreq (fun k => A m k * cdfQuotientMatrix k n)
    have e2 := tsum_subtype NonzeroFreq (fun k => (cdfQuotientMatrix k m : ℂ) * A k n)
    have i1 : NonzeroFreq.indicator (fun k => A m k * cdfQuotientMatrix k n) =
        fun k => A m k * cdfQuotientMatrix k n := by
      funext k
      by_cases hk : k ∈ NonzeroFreq
      · rw [Set.indicator_of_mem hk]
      · have : k = 0 := by simpa [NonzeroFreq] using hk
        rw [Set.indicator_of_notMem hk, this, hcol0, zero_mul]
    have i2 : NonzeroFreq.indicator (fun k => (cdfQuotientMatrix k m : ℂ) * A k n) =
        fun k => (cdfQuotientMatrix k m : ℂ) * A k n := by
      funext k
      by_cases hk : k ∈ NonzeroFreq
      · rw [Set.indicator_of_mem hk]
      · have : k = 0 := by simpa [NonzeroFreq] using hk
        rw [Set.indicator_of_notMem hk, this, hrow0, mul_zero]
    rw [i1] at e1
    rw [i2] at e2
    rw [← e1, ← e2]
    have h1 : ∀ k : NonzeroFreq, A m k = ⟪freqBasis ⟨m, hm⟩, G (freqBasis k)⟫_ℂ := fun k =>
      freqMatrix_apply G ⟨m, hm⟩ k
    have h2 : ∀ k : NonzeroFreq, A k n = ⟪freqBasis k, G (freqBasis ⟨n, hn⟩)⟫_ℂ := fun k =>
      freqMatrix_apply G k ⟨n, hn⟩
    simp_rw [h1, h2]
    exact h
  refine no_coercive_banded_intertwiner A ‖G‖ W hc hbound hband hcol0 hinter' fun N => ?_
  have := hcoer (blockIndicator N)
  rwa [norm_sq_blockIndicator, inner_blockIndicator] at this

/-- The card's formulation with a bounded **self-adjoint** `G`. -/
theorem no_coercive_finite_range_selfAdjoint_symmetrizer
    (G : nonzeroFreqL2 →L[ℂ] nonzeroFreqL2) (_hG : IsSelfAdjoint G) {c : ℝ} (hc : 0 < c) (W : ℕ)
    (hcoer : ∀ u : nonzeroFreqL2, c * ‖u‖ ^ 2 ≤ (⟪u, G u⟫_ℂ).re)
    (hrange : ∀ m n : NonzeroFreq, (W : ℤ) < |(|(m : ℤ)| - |(n : ℤ)|)| →
      ⟪freqBasis m, G (freqBasis n)⟫_ℂ = 0)
    (hinter : ∀ m n : NonzeroFreq,
      ∑' k : NonzeroFreq, ⟪freqBasis m, G (freqBasis k)⟫_ℂ * cdfQuotientMatrix k n =
        ∑' k : NonzeroFreq, (cdfQuotientMatrix k m : ℂ) * ⟪freqBasis k, G (freqBasis n)⟫_ℂ) :
    False :=
  no_coercive_finite_range_symmetrizer G hc W hcoer hrange hinter

end

end RHTower
