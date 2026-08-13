import GaloisForLFunctions.HTGeometry.EntryComplexLimit
import GaloisForLFunctions.HTGeometry.NevanlinnaEntire
import GaloisForLFunctions.HTGeometry.MinimalTypeNoArithmeticProgression

/-!
# Minimal exponential type of the limiting Nevanlinna entries

The truncated Nevanlinna matrix acts as a transfer product: the two Duhamel comparisons at the
pair `(0, z)` say

`p_n(z) = q_n(0)·D_n(z) − p_n(0)·B_n(z)`,  `q_n(z) = q_n(0)·C_n(z) − p_n(0)·A_n(z)`,

and the level-`n+1` increments of the four truncated entries are the rank-one step
`(h₀ z / h_{n+1}) · (value at 0) · (polynomial at z)`.  Hence the maximum modulus of the four
truncated entries obeys the multiplicative recursion `m_{n+1} ≤ m_n (1 + ‖z‖ c_{n+1})` with
`c_j = (h₀/h_j)(‖p_j(0)‖ + ‖q_j(0)‖)²`, which is summable exactly when both kernel roots are
bounded at `0`.  Splitting the product at a tail of sum at most `A/2` bounds every truncation by
`C_A · exp(A‖z‖)`, so the limiting entries are entire of minimal exponential type.  This is
M. Riesz's theorem in transfer form: no factorization theory enters.
-/

open Filter Topology

namespace HTGeometry

variable {s : ℕ → ℝ}

noncomputable section

/-! ## The truncation increments -/

theorem nevAtruncC_succ (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    nevAtruncC s (n + 1) z = nevAtruncC s n z +
      ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
        (secondKindC s (n + 1) 0 * secondKindC s (n + 1) z /
          ((momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) : ℝ) : ℂ)) := by
  unfold nevAtruncC bilinearPartialSum
  rw [Finset.sum_range_succ]
  ring

theorem nevBtruncC_succ (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    nevBtruncC s (n + 1) z = nevBtruncC s n z +
      ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
        (secondKindC s (n + 1) 0 * monicOrthoC s (n + 1) z /
          ((momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) : ℝ) : ℂ)) := by
  unfold nevBtruncC bilinearPartialSum
  rw [Finset.sum_range_succ]
  ring

theorem nevCtruncC_succ (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    nevCtruncC s (n + 1) z = nevCtruncC s n z +
      ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
        (monicOrthoC s (n + 1) 0 * secondKindC s (n + 1) z /
          ((momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) : ℝ) : ℂ)) := by
  unfold nevCtruncC bilinearPartialSum
  rw [Finset.sum_range_succ]
  ring

theorem nevDtruncC_succ (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    nevDtruncC s (n + 1) z = nevDtruncC s n z +
      ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
        (monicOrthoC s (n + 1) 0 * monicOrthoC s (n + 1) z /
          ((momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) : ℝ) : ℂ)) := by
  unfold nevDtruncC bilinearPartialSum
  rw [Finset.sum_range_succ]
  ring

/-! ## The transfer identities -/

/-- **The first-kind transfer identity.**  The truncated entries act on the initial values at `0`
and return the polynomial at `z`: the Duhamel comparison at the pair `(0, z)`. -/
theorem monicOrthoC_eq_transfer (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    monicOrthoC s n z =
      secondKindC s n 0 * nevDtruncC s n z - monicOrthoC s n 0 * nevBtruncC s n z := by
  have hd := monicOrthoC_duhamel h n 0 z
  have hsumB : bilinearPartialSum s (fun k => secondKindC s k 0)
      (fun w k => monicOrthoC s k w) (n + 1) z =
      ∑ j ∈ Finset.range (n + 1), monicOrthoC s j z * secondKindC s j 0 /
        ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ) := by
    unfold bilinearPartialSum
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsumD : bilinearPartialSum s (fun k => monicOrthoC s k 0)
      (fun w k => monicOrthoC s k w) (n + 1) z =
      ∑ j ∈ Finset.range (n + 1), monicOrthoC s j z * monicOrthoC s j 0 /
        ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ) := by
    unfold bilinearPartialSum
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold nevDtruncC nevBtruncC
  rw [hsumB, hsumD]
  linear_combination hd

/-- **The second-kind transfer identity.** -/
theorem secondKindC_eq_transfer (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    secondKindC s n z =
      secondKindC s n 0 * nevCtruncC s n z - monicOrthoC s n 0 * nevAtruncC s n z := by
  have hd := secondKindC_duhamel h n 0 z
  have hsumA : bilinearPartialSum s (fun k => secondKindC s k 0)
      (fun w k => secondKindC s k w) (n + 1) z =
      ∑ j ∈ Finset.range (n + 1), secondKindC s j z * secondKindC s j 0 /
        ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ) := by
    unfold bilinearPartialSum
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsumC : bilinearPartialSum s (fun k => monicOrthoC s k 0)
      (fun w k => secondKindC s k w) (n + 1) z =
      ∑ j ∈ Finset.range (n + 1), monicOrthoC s j 0 * secondKindC s j z /
        ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ) := by
    unfold bilinearPartialSum
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold nevCtruncC nevAtruncC
  rw [hsumA, hsumC]
  linear_combination hd

/-- The first-kind transfer identity with the entries one level down: the top cross terms cancel
by antisymmetry of the rank-one step. -/
theorem monicOrthoC_succ_eq_transfer (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    monicOrthoC s (n + 1) z =
      secondKindC s (n + 1) 0 * nevDtruncC s n z -
        monicOrthoC s (n + 1) 0 * nevBtruncC s n z := by
  have h1 := monicOrthoC_eq_transfer h (n + 1) z
  rw [nevDtruncC_succ, nevBtruncC_succ] at h1
  linear_combination h1

/-- The second-kind transfer identity one level down. -/
theorem secondKindC_succ_eq_transfer (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    secondKindC s (n + 1) z =
      secondKindC s (n + 1) 0 * nevCtruncC s n z -
        monicOrthoC s (n + 1) 0 * nevAtruncC s n z := by
  have h1 := secondKindC_eq_transfer h (n + 1) z
  rw [nevCtruncC_succ, nevAtruncC_succ] at h1
  linear_combination h1

/-! ## The multiplicative recursion -/

/-- The transfer-step weight `(h₀/h_j)(‖p_j(0)‖ + ‖q_j(0)‖)²`. -/
def transferStepBound (s : ℕ → ℝ) (j : ℕ) : ℝ :=
  momentInner s (monicOrtho s 0) (monicOrtho s 0) /
    momentInner s (monicOrtho s j) (monicOrtho s j) *
    (‖monicOrthoC s j 0‖ + ‖secondKindC s j 0‖) ^ 2

theorem transferStepBound_nonneg (h : PositiveMomentForm s) (j : ℕ) :
    0 ≤ transferStepBound s j := by
  unfold transferStepBound
  have h0 := monicOrtho_inner_self_pos h 0
  have hj := monicOrtho_inner_self_pos h j
  positivity

/-- The maximum modulus of the four truncated entries. -/
def truncEntryMax (s : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℝ :=
  max (max ‖nevAtruncC s n z‖ ‖nevBtruncC s n z‖)
    (max ‖nevCtruncC s n z‖ ‖nevDtruncC s n z‖)

theorem truncEntryMax_nonneg (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    0 ≤ truncEntryMax s n z :=
  le_trans (norm_nonneg _) (le_max_of_le_left (le_max_left _ _))

theorem norm_nevAtruncC_le_truncEntryMax (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    ‖nevAtruncC s n z‖ ≤ truncEntryMax s n z :=
  le_max_of_le_left (le_max_left _ _)

theorem norm_nevBtruncC_le_truncEntryMax (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    ‖nevBtruncC s n z‖ ≤ truncEntryMax s n z :=
  le_max_of_le_left (le_max_right _ _)

theorem norm_nevCtruncC_le_truncEntryMax (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    ‖nevCtruncC s n z‖ ≤ truncEntryMax s n z :=
  le_max_of_le_right (le_max_left _ _)

theorem norm_nevDtruncC_le_truncEntryMax (s : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    ‖nevDtruncC s n z‖ ≤ truncEntryMax s n z :=
  le_max_of_le_right (le_max_right _ _)

/-- One transfer step multiplies the entry maximum by at most `1 + ‖z‖·c_{n+1}`. -/
theorem truncEntryMax_succ_le (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    truncEntryMax s (n + 1) z ≤
      truncEntryMax s n z * (1 + ‖z‖ * transferStepBound s (n + 1)) := by
  set m := truncEntryMax s n z with hm
  set h0r := momentInner s (monicOrtho s 0) (monicOrtho s 0) with hh0
  set hnr := momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) with hhn
  have h0pos : 0 < h0r := monicOrtho_inner_self_pos h 0
  have hnpos : 0 < hnr := monicOrtho_inner_self_pos h (n + 1)
  set p0 := ‖monicOrthoC s (n + 1) 0‖ with hp0
  set q0 := ‖secondKindC s (n + 1) 0‖ with hq0
  have hp0n : 0 ≤ p0 := norm_nonneg _
  have hq0n : 0 ≤ q0 := norm_nonneg _
  have hmn : 0 ≤ m := truncEntryMax_nonneg s n z
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  have hdiv : 0 ≤ h0r / hnr := le_of_lt (div_pos h0pos hnpos)
  have hstep : transferStepBound s (n + 1) = h0r / hnr * (p0 + q0) ^ 2 := rfl
  have hpz : ‖monicOrthoC s (n + 1) z‖ ≤ (p0 + q0) * m := by
    rw [monicOrthoC_succ_eq_transfer h n z]
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul, norm_mul]
    have hD := norm_nevDtruncC_le_truncEntryMax s n z
    have hB := norm_nevBtruncC_le_truncEntryMax s n z
    nlinarith [hq0n, hp0n, hmn, norm_nonneg (nevDtruncC s n z),
      norm_nonneg (nevBtruncC s n z)]
  have hqz : ‖secondKindC s (n + 1) z‖ ≤ (p0 + q0) * m := by
    rw [secondKindC_succ_eq_transfer h n z]
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul, norm_mul]
    have hC := norm_nevCtruncC_le_truncEntryMax s n z
    have hA := norm_nevAtruncC_le_truncEntryMax s n z
    nlinarith [hq0n, hp0n, hmn, norm_nonneg (nevCtruncC s n z),
      norm_nonneg (nevAtruncC s n z)]
  have hincr : ∀ v w : ℂ, ‖((h0r : ℝ) : ℂ) * z * (v * w / ((hnr : ℝ) : ℂ))‖ =
      h0r / hnr * ‖z‖ * (‖v‖ * ‖w‖) := by
    intro v w
    rw [norm_mul, norm_mul, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h0pos, abs_of_pos hnpos]
    field_simp
  have hentry : ∀ E v w : ℂ, ‖E‖ ≤ m → ‖v‖ ≤ p0 + q0 → ‖w‖ ≤ (p0 + q0) * m →
      ‖E + ((h0r : ℝ) : ℂ) * z * (v * w / ((hnr : ℝ) : ℂ))‖ ≤
        m * (1 + ‖z‖ * transferStepBound s (n + 1)) := by
    intro E v w hE hv hw
    refine le_trans (norm_add_le _ _) ?_
    rw [hincr, hstep]
    have h1 : ‖v‖ * ‖w‖ ≤ (p0 + q0) * ((p0 + q0) * m) :=
      mul_le_mul hv hw (norm_nonneg w) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hdiv hznn)
    nlinarith [h2, hE]
  unfold truncEntryMax
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
  · rw [nevAtruncC_succ]
    exact hentry _ _ _ (norm_nevAtruncC_le_truncEntryMax s n z)
      (le_add_of_nonneg_left hp0n) hqz
  · rw [nevBtruncC_succ]
    exact hentry _ _ _ (norm_nevBtruncC_le_truncEntryMax s n z)
      (le_add_of_nonneg_left hp0n) hpz
  · rw [nevCtruncC_succ]
    exact hentry _ _ _ (norm_nevCtruncC_le_truncEntryMax s n z)
      (le_add_of_nonneg_right hq0n) hqz
  · rw [nevDtruncC_succ]
    exact hentry _ _ _ (norm_nevDtruncC_le_truncEntryMax s n z)
      (le_add_of_nonneg_right hq0n) hpz

/-- The level-zero entries are `0`, `−1`, `1`, `z`, and the zeroth step weight is `1`. -/
theorem truncEntryMax_zero_le (h : PositiveMomentForm s) (z : ℂ) :
    truncEntryMax s 0 z ≤ 1 + ‖z‖ * transferStepBound s 0 := by
  have h0pos : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    monicOrtho_inner_self_pos h 0
  have h0ne : ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h0pos
  have hp00 : monicOrthoC s 0 (0 : ℂ) = 1 := by
    simp [monicOrthoC]
  have hpz : ∀ w : ℂ, monicOrthoC s 0 w = 1 := by
    intro w
    simp [monicOrthoC]
  have hA : nevAtruncC s 0 z = 0 := by
    unfold nevAtruncC bilinearPartialSum
    simp
  have hB : nevBtruncC s 0 z = -1 := by
    unfold nevBtruncC bilinearPartialSum
    simp
  have hC : nevCtruncC s 0 z = 1 := by
    unfold nevCtruncC bilinearPartialSum
    simp
  have hD : nevDtruncC s 0 z = z := by
    unfold nevDtruncC bilinearPartialSum
    rw [Finset.sum_range_one]
    simp only
    rw [hp00, hpz z]
    rw [one_mul, one_div,
      mul_comm (((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ)) z,
      mul_assoc, mul_inv_cancel₀ h0ne, mul_one]
  have hstep0 : transferStepBound s 0 = 1 := by
    unfold transferStepBound
    rw [hp00, secondKindC_zero]
    rw [div_self (ne_of_gt h0pos)]
    simp
  rw [hstep0]
  unfold truncEntryMax
  rw [hA, hB, hC, hD]
  have hzn := norm_nonneg z
  simp only [norm_zero, norm_neg, norm_one, mul_one]
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
  · linarith
  · linarith
  · linarith
  · linarith

/-- **The product bound**: every truncation level is controlled by the transfer product. -/
theorem truncEntryMax_le_prod (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    truncEntryMax s n z ≤
      ∏ j ∈ Finset.range (n + 1), (1 + ‖z‖ * transferStepBound s j) := by
  induction n with
  | zero =>
      simpa using truncEntryMax_zero_le h z
  | succ n ih =>
      rw [Finset.prod_range_succ]
      refine le_trans (truncEntryMax_succ_le h n z) ?_
      have hfac : 0 ≤ 1 + ‖z‖ * transferStepBound s (n + 1) := by
        have := transferStepBound_nonneg h (n + 1)
        have := norm_nonneg z
        positivity
      exact mul_le_mul_of_nonneg_right ih hfac

/-! ## Summability of the step weights -/

/-- A uniform kernel-root bound gives summability, for an arbitrary evaluation family. -/
theorem summable_normSq_div_of_kernelRoot_le (h : PositiveMomentForm s) (p : ℕ → ℂ) {C : ℝ}
    (hC : ∀ n, kernelRoot s p n ≤ C) :
    Summable (fun k => Complex.normSq (p k) /
      momentInner s (monicOrtho s k) (monicOrtho s k)) := by
  have hterm : ∀ k, 0 ≤ Complex.normSq (p k) /
      momentInner s (monicOrtho s k) (monicOrtho s k) := by
    intro k
    have := monicOrtho_inner_self_pos h k
    have := Complex.normSq_nonneg (p k)
    positivity
  refine summable_of_sum_range_le (c := C ^ 2) hterm ?_
  intro n
  have hsub : ∑ j ∈ Finset.range n, Complex.normSq (p j) /
      momentInner s (monicOrtho s j) (monicOrtho s j) ≤
      ∑ j ∈ Finset.range (n + 1), Complex.normSq (p j) /
        momentInner s (monicOrtho s j) (monicOrtho s j) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    · intro j _ _
      exact hterm j
  refine le_trans hsub ?_
  rw [← kernelRoot_sq_eq_normSq_sum h p n]
  have hn := kernelRoot_nonneg s p n
  have hCn := hC n
  nlinarith [hn, hCn]

/-- Bounded kernels at `0` make the transfer-step weights summable. -/
theorem summable_transferStepBound (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    Summable (transferStepBound s) := by
  obtain ⟨S, P, _hSpos, _hPpos, hS, hP⟩ := h0b
  set h0r := momentInner s (monicOrtho s 0) (monicOrtho s 0) with hh0
  have h0pos : 0 < h0r := monicOrtho_inner_self_pos h 0
  have hmono := summable_normSq_div_of_kernelRoot_le h (fun j => monicOrthoC s j 0) hS
  have hsec := summable_normSq_div_of_kernelRoot_le h (fun j => secondKindC s j 0) hP
  have hsum := ((hmono.add hsec).mul_left (2 * h0r))
  refine Summable.of_nonneg_of_le (transferStepBound_nonneg h) ?_ hsum
  intro j
  have hjpos : 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    monicOrtho_inner_self_pos h j
  unfold transferStepBound
  rw [← hh0]
  have hnormP : Complex.normSq (monicOrthoC s j 0) = ‖monicOrthoC s j 0‖ ^ 2 := by
    rw [Complex.sq_norm]
  have hnormQ : Complex.normSq (secondKindC s j 0) = ‖secondKindC s j 0‖ ^ 2 := by
    rw [Complex.sq_norm]
  rw [div_mul_eq_mul_div, div_le_iff₀ hjpos]
  rw [hnormP, hnormQ]
  set a := ‖monicOrthoC s j 0‖
  set b := ‖secondKindC s j 0‖
  have han : 0 ≤ a := norm_nonneg _
  have hbn : 0 ≤ b := norm_nonneg _
  have hsq : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have hexp : 2 * h0r * (a ^ 2 / momentInner s (monicOrtho s j) (monicOrtho s j) +
      b ^ 2 / momentInner s (monicOrtho s j) (monicOrtho s j)) *
        momentInner s (monicOrtho s j) (monicOrtho s j) =
      2 * h0r * (a ^ 2 + b ^ 2) := by
    field_simp
  rw [hexp]
  nlinarith [hsq, h0pos.le]

/-! ## The tail-split exponential bound -/

/-- A summable nonnegative sequence has uniformly small tails over initial segments. -/
theorem exists_forall_Ico_sum_le {c : ℕ → ℝ} (hc : Summable c) (hc0 : ∀ j, 0 ≤ c j)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, ∑ j ∈ Finset.Ico N n, c j ≤ ε := by
  have htend := hc.hasSum.tendsto_sum_nat
  set L := ∑' j, c j with hL
  have hev : ∀ᶠ N in atTop, L - ε < ∑ j ∈ Finset.range N, c j := by
    apply htend.eventually
    apply eventually_gt_nhds
    linarith
  obtain ⟨N, hN⟩ := hev.exists
  refine ⟨N, ?_⟩
  intro n
  by_cases hn : n ≤ N
  · have hempty : Finset.Ico N n = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    exact hε.le
  · have hn' : N ≤ n := by omega
    have hsplit : ∑ j ∈ Finset.range N, c j + ∑ j ∈ Finset.Ico N n, c j =
        ∑ j ∈ Finset.range n, c j := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
      exact Finset.sum_Ico_consecutive _ (Nat.zero_le N) hn'
    have hle : ∑ j ∈ Finset.range n, c j ≤ L :=
      Summable.sum_le_tsum (Finset.range n) (fun j _ => hc0 j) hc
    linarith

/-- **The tail-split exponential bound.**  For a summable nonnegative weight sequence, the
products `∏ (1 + r c_j)` grow slower than every exponential `exp(A r)`, uniformly in length. -/
theorem exists_prod_le_exp_of_summable {c : ℕ → ℝ} (hc : Summable c) (hc0 : ∀ j, 0 ≤ c j)
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
      ∏ j ∈ Finset.range n, (1 + r * c j) ≤ C * Real.exp (A * r) := by
  obtain ⟨N0, hN0⟩ := exists_forall_Ico_sum_le hc hc0 (half_pos hA)
  set N : ℕ := N0 + 1 with hNdef
  have hNposR : 0 < (N : ℝ) := by
    rw [hNdef]
    positivity
  have hN : ∀ n : ℕ, ∑ j ∈ Finset.Ico N n, c j ≤ A / 2 := by
    intro n
    refine le_trans ?_ (hN0 n)
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico (Nat.le_succ N0) le_rfl) ?_
    intro j _ _
    exact hc0 j
  set C0 : ℝ := ∏ j ∈ Finset.range N, (1 + c j * (2 * N / A)) with hC0
  have hfacone : ∀ j : ℕ, 1 ≤ 1 + c j * (2 * N / A) := by
    intro j
    have h1 := hc0 j
    have h2 : 0 ≤ c j * (2 * N / A) := by positivity
    linarith
  have hC0one : 1 ≤ C0 := by
    rw [hC0]
    refine Finset.one_le_prod ?_
    intro j _
    exact hfacone j
  refine ⟨C0, hC0one, ?_⟩
  intro n r hr
  have hδr : 0 ≤ A / (2 * N) * r := by positivity
  have hperfac : ∀ j, 1 + r * c j ≤
      (1 + c j * (2 * N / A)) * (1 + A / (2 * N) * r) := by
    intro j
    have e1 : (1 + c j * (2 * N / A)) * (1 + A / (2 * N) * r) =
        1 + A / (2 * N) * r + c j * (2 * N / A) +
          c j * (2 * N / A) * (A / (2 * N) * r) := by
      ring
    have e2 : c j * (2 * N / A) * (A / (2 * N) * r) = c j * r := by
      field_simp
    rw [e1, e2]
    have h4 : 0 ≤ c j * (2 * N / A) := by
      have := hc0 j
      positivity
    have hcomm : r * c j = c j * r := mul_comm _ _
    rw [hcomm]
    linarith
  have hfacpos : ∀ j, 0 ≤ 1 + r * c j := by
    intro j
    have := hc0 j
    have : 0 ≤ r * c j := by positivity
    linarith
  have hhead : ∀ m : ℕ, m ≤ N → ∏ j ∈ Finset.range m, (1 + r * c j) ≤
      C0 * Real.exp (A * r / 2) := by
    intro m hm
    calc ∏ j ∈ Finset.range m, (1 + r * c j)
        ≤ ∏ j ∈ Finset.range m,
            ((1 + c j * (2 * N / A)) * (1 + A / (2 * N) * r)) := by
          refine Finset.prod_le_prod (fun j _ => hfacpos j) (fun j _ => hperfac j)
      _ = (∏ j ∈ Finset.range m, (1 + c j * (2 * N / A))) *
            (1 + A / (2 * N) * r) ^ m := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      _ ≤ C0 * Real.exp (A * r / 2) := by
          have hfirst : ∏ j ∈ Finset.range m, (1 + c j * (2 * N / A)) ≤ C0 := by
            rw [hC0]
            have hsplit2 : (∏ j ∈ Finset.range m, (1 + c j * (2 * N / A))) *
                ∏ j ∈ Finset.Ico m N, (1 + c j * (2 * N / A)) =
                ∏ j ∈ Finset.range N, (1 + c j * (2 * N / A)) := by
              rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
              exact Finset.prod_Ico_consecutive _ (Nat.zero_le m) hm
            have h1tail : 1 ≤ ∏ j ∈ Finset.Ico m N, (1 + c j * (2 * N / A)) := by
              refine Finset.one_le_prod ?_
              intro j _
              exact hfacone j
            have hmnn : 0 ≤ ∏ j ∈ Finset.range m, (1 + c j * (2 * N / A)) := by
              refine Finset.prod_nonneg ?_
              intro j _
              exact le_trans zero_le_one (hfacone j)
            calc ∏ j ∈ Finset.range m, (1 + c j * (2 * N / A))
                ≤ (∏ j ∈ Finset.range m, (1 + c j * (2 * N / A))) *
                    ∏ j ∈ Finset.Ico m N, (1 + c j * (2 * N / A)) :=
                  le_mul_of_one_le_right hmnn h1tail
              _ = ∏ j ∈ Finset.range N, (1 + c j * (2 * N / A)) := hsplit2
          have hsecond : (1 + A / (2 * N) * r) ^ m ≤ Real.exp (A * r / 2) := by
            have hbase : 1 + A / (2 * N) * r ≤ Real.exp (A / (2 * N) * r) := by
              have := Real.add_one_le_exp (A / (2 * N) * r)
              linarith
            have hpow : (1 + A / (2 * N) * r) ^ m ≤
                Real.exp (A / (2 * N) * r) ^ m := by
              refine pow_le_pow_left₀ (by linarith) hbase m
            refine le_trans hpow ?_
            rw [← Real.exp_nat_mul]
            refine Real.exp_le_exp.mpr ?_
            have hmN : (m : ℝ) ≤ N := by exact_mod_cast hm
            have hstep : (m : ℝ) * (A / (2 * N) * r) ≤
                (N : ℝ) * (A / (2 * N) * r) :=
              mul_le_mul_of_nonneg_right hmN hδr
            refine le_trans hstep ?_
            rw [show (N : ℝ) * (A / (2 * N) * r) = A * r / 2 * (N / N) by ring]
            rw [div_self (ne_of_gt hNposR)]
            rw [mul_one]
          have hC0nn : 0 ≤ C0 := le_trans zero_le_one hC0one
          have hprodnn : 0 ≤ ∏ j ∈ Finset.range m, (1 + c j * (2 * N / A)) := by
            refine Finset.prod_nonneg ?_
            intro j _
            have := hc0 j
            positivity
          exact mul_le_mul hfirst hsecond (by positivity) hC0nn
  by_cases hn : n ≤ N
  · refine le_trans (hhead n hn) ?_
    have hexp : Real.exp (A * r / 2) ≤ Real.exp (A * r) := by
      refine Real.exp_le_exp.mpr ?_
      have : 0 ≤ A * r := by positivity
      linarith
    have hC0nn : 0 ≤ C0 := le_trans zero_le_one hC0one
    exact mul_le_mul_of_nonneg_left hexp hC0nn
  · have hsplit : (∏ j ∈ Finset.range N, (1 + r * c j)) *
        ∏ j ∈ Finset.Ico N n, (1 + r * c j) =
        ∏ j ∈ Finset.range n, (1 + r * c j) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
      exact Finset.prod_Ico_consecutive _ (Nat.zero_le N) (by omega : N ≤ n)
    rw [← hsplit]
    have htail : ∏ j ∈ Finset.Ico N n, (1 + r * c j) ≤ Real.exp (A * r / 2) := by
      have hstep1 : ∏ j ∈ Finset.Ico N n, (1 + r * c j) ≤
          ∏ j ∈ Finset.Ico N n, Real.exp (r * c j) := by
        refine Finset.prod_le_prod (fun j _ => hfacpos j) ?_
        intro j _
        have := Real.add_one_le_exp (r * c j)
        linarith
      rw [← Real.exp_sum] at hstep1
      refine le_trans hstep1 ?_
      refine Real.exp_le_exp.mpr ?_
      rw [← Finset.mul_sum]
      have := mul_le_mul_of_nonneg_left (hN n) hr
      linarith
    have hheadN := hhead N le_rfl
    have htailnn : 0 ≤ ∏ j ∈ Finset.Ico N n, (1 + r * c j) :=
      Finset.prod_nonneg (fun j _ => hfacpos j)
    have hCexp : 0 ≤ C0 * Real.exp (A * r / 2) := by
      have hC0nn : 0 ≤ C0 := le_trans zero_le_one hC0one
      positivity
    calc (∏ j ∈ Finset.range N, (1 + r * c j)) *
        ∏ j ∈ Finset.Ico N n, (1 + r * c j)
        ≤ (C0 * Real.exp (A * r / 2)) * Real.exp (A * r / 2) := by
          exact mul_le_mul hheadN htail htailnn hCexp
      _ = C0 * Real.exp (A * r) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

/-! ## Minimal exponential type of the four limiting entries -/

/-- The uniform truncation bound produced by the transfer product. -/
theorem exists_forall_truncEntry_le_exp (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (z : ℂ),
      truncEntryMax s n z ≤ C * Real.exp (A * ‖z‖) := by
  obtain ⟨C, hC1, hC⟩ := exists_prod_le_exp_of_summable
    (summable_transferStepBound h h0b) (transferStepBound_nonneg h) hA
  refine ⟨C, hC1, ?_⟩
  intro n z
  refine le_trans (truncEntryMax_le_prod h n z) ?_
  exact hC (n + 1) ‖z‖ (norm_nonneg z)

/-- **M. Riesz's theorem, `B` entry**: the limiting `B` is entire of minimal exponential type. -/
theorem nevBinf_hasMinimalExponentialType (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) :
    GaloisForLFunctions.HTGeometry.HasMinimalExponentialType (nevBinf s) := by
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  refine ⟨(nevanlinna_entire_unimodular h ⟨S, P, hSpos, hPpos, hS, hP⟩).2.1, ?_⟩
  intro A hA
  obtain ⟨C, hC1, hC⟩ := exists_forall_truncEntry_le_exp h
    ⟨S, P, hSpos, hPpos, hS, hP⟩ hA
  refine ⟨C, hC1, ?_⟩
  intro z
  have htend := (tendsto_nevBtruncC h hS hP z).norm
  refine le_of_tendsto htend ?_
  filter_upwards with n
  exact le_trans (norm_nevBtruncC_le_truncEntryMax s n z) (hC n z)

/-- **M. Riesz's theorem, `A` entry.** -/
theorem nevAinf_hasMinimalExponentialType (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) :
    GaloisForLFunctions.HTGeometry.HasMinimalExponentialType (nevAinf s) := by
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  refine ⟨(nevanlinna_entire_unimodular h ⟨S, P, hSpos, hPpos, hS, hP⟩).1, ?_⟩
  intro A hA
  obtain ⟨C, hC1, hC⟩ := exists_forall_truncEntry_le_exp h
    ⟨S, P, hSpos, hPpos, hS, hP⟩ hA
  refine ⟨C, hC1, ?_⟩
  intro z
  have htend := (tendsto_nevAtruncC h hS hP z).norm
  refine le_of_tendsto htend ?_
  filter_upwards with n
  exact le_trans (norm_nevAtruncC_le_truncEntryMax s n z) (hC n z)

/-- **M. Riesz's theorem, `C` entry.** -/
theorem nevCinf_hasMinimalExponentialType (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) :
    GaloisForLFunctions.HTGeometry.HasMinimalExponentialType (nevCinf s) := by
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  refine ⟨(nevanlinna_entire_unimodular h ⟨S, P, hSpos, hPpos, hS, hP⟩).2.2.1, ?_⟩
  intro A hA
  obtain ⟨C, hC1, hC⟩ := exists_forall_truncEntry_le_exp h
    ⟨S, P, hSpos, hPpos, hS, hP⟩ hA
  refine ⟨C, hC1, ?_⟩
  intro z
  have htend := (tendsto_nevCtruncC h hS hP z).norm
  refine le_of_tendsto htend ?_
  filter_upwards with n
  exact le_trans (norm_nevCtruncC_le_truncEntryMax s n z) (hC n z)

/-- **M. Riesz's theorem, `D` entry.** -/
theorem nevDinf_hasMinimalExponentialType (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) :
    GaloisForLFunctions.HTGeometry.HasMinimalExponentialType (nevDinf s) := by
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  refine ⟨(nevanlinna_entire_unimodular h ⟨S, P, hSpos, hPpos, hS, hP⟩).2.2.2.1, ?_⟩
  intro A hA
  obtain ⟨C, hC1, hC⟩ := exists_forall_truncEntry_le_exp h
    ⟨S, P, hSpos, hPpos, hS, hP⟩ hA
  refine ⟨C, hC1, ?_⟩
  intro z
  have htend := (tendsto_nevDtruncC h hS hP z).norm
  refine le_of_tendsto htend ?_
  filter_upwards with n
  exact le_trans (norm_nevDtruncC_le_truncEntryMax s n z) (hC n z)

end

end HTGeometry
