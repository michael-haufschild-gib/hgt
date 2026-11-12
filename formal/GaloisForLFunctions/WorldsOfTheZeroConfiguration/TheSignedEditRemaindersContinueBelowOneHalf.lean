import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheSignedEditSeriesContinuesBelowOneHalf

/-!
# The prime-power remainders of the signed edit continue below one half

Two remainders complete the edit series `H₁` to the logarithm of `ζ_B / F`, `F` the tempered model
with the zero pair `ρ, ρ̄` (`ρ = β + iγ`):

* `Q(s) = Σ_p e(p) (-log(1 - p^{-s}) - p^{-s})` (`TwoSidedEdits.editRem`), and
* `R(s) = Σ_{p ≥ 2^{k₀}} (λ(p^{-(s+1-ρ)}) + λ(p^{-(s+1-ρ̄)}))`, `λ(z) = -log(1 - z) - z`
  (`pairRem`).

**Sparsity** (`summable_abs_sEdit_rpow`).  At most `3 · 2^{kα}` primes of the block `k` are
edited, so `Σ_p |e(p)| p^{-θ} < ∞` for every `θ > α`.

**Continuation** (`differentiableOn_editRem_sparse`, `differentiableOn_pairRem`).  `Q` is
holomorphic on `Re s > α/2` and `R` on `Re s > β - 1/2`; both are bounded on every half-plane
`Re s ≥ σ₀` strictly inside (`exists_norm_editRem_le`, `exists_norm_pairRem_le`).
-/

open Complex Finset Filter Topology
open RHTower.BeurlingDeletion RHTower.BeurlingDeletion.DeletionData
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit

variable {α β : ℝ}

/-! ## Sparsity of the edit -/

/-- `[1, 2^K)` is the union of the dyadic blocks `k < K`. -/
theorem sum_Ico_one_two_pow_eq (f : ℕ → ℝ) (K : ℕ) :
    ∑ n ∈ Finset.Ico 1 (2 ^ K), f n =
      ∑ k ∈ Finset.range K, ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_Ico_consecutive _ Nat.one_le_two_pow
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K))]

/-- The edited primes of block `k` contribute at most `3 · (2^{α-θ})^k` at the exponent `θ`. -/
theorem sum_block_abs_sEdit_rpow_le (hα0 : 0 < α) (hα : α < 1) (γ : ℝ) (k₀ k : ℕ) {θ : ℝ}
    (hθ : 0 ≤ θ) :
    ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), |(sEdit α β γ k₀ n : ℝ)| * (n : ℝ) ^ (-θ) ≤
      3 * ((2 : ℝ) ^ (α - θ)) ^ k := by
  classical
  set S := (blockPrimes k).filter fun p => sEdit α β γ k₀ p ≠ 0 with hS
  have hsub : ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), |(sEdit α β γ k₀ n : ℝ)| * (n : ℝ) ^ (-θ) =
      ∑ n ∈ S, |(sEdit α β γ k₀ n : ℝ)| * (n : ℝ) ^ (-θ) := by
    symm
    refine Finset.sum_subset (fun n hn => ?_) fun n hn hnS => ?_
    · exact Finset.mem_Ico.mpr (mem_blockPrimes.mp (Finset.mem_filter.mp hn).1).2
    · have h0 : sEdit α β γ k₀ n = 0 := by
        by_contra hne
        refine hnS (Finset.mem_filter.mpr ⟨mem_blockPrimes.mpr ⟨?_, Finset.mem_Ico.mp hn⟩, hne⟩)
        by_contra hp
        exact hne ((isEdit_sEdit α β γ k₀).prime n hp)
      rw [h0]; simp
  have hterm : ∀ n ∈ S, |(sEdit α β γ k₀ n : ℝ)| * (n : ℝ) ^ (-θ) ≤ (2 : ℝ) ^ (-((k : ℝ) * θ)) := by
    intro n hn
    have hnb := (mem_blockPrimes.mp (Finset.mem_filter.mp hn).1).2.1
    have h1 : |(sEdit α β γ k₀ n : ℝ)| ≤ 1 := (isEdit_sEdit α β γ k₀).abs_le_one n
    have h2 : (n : ℝ) ^ (-θ) ≤ (2 : ℝ) ^ (-((k : ℝ) * θ)) := by
      have hk : ((2 : ℝ) ^ k) ≤ n := by exact_mod_cast hnb
      calc (n : ℝ) ^ (-θ) ≤ ((2 : ℝ) ^ k) ^ (-θ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hk (by linarith)
        _ = (2 : ℝ) ^ (-((k : ℝ) * θ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
    calc |(sEdit α β γ k₀ n : ℝ)| * (n : ℝ) ^ (-θ) ≤ 1 * (2 : ℝ) ^ (-((k : ℝ) * θ)) :=
          mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = _ := one_mul _
  have hcard : (S.card : ℝ) ≤ 3 * (2 : ℝ) ^ ((k : ℝ) * α) :=
    le_trans (by exact_mod_cast card_sEdit_ne_zero_le γ k₀ k) (blockCount_le hα0 hα k)
  rw [hsub]
  calc ∑ n ∈ S, |(sEdit α β γ k₀ n : ℝ)| * (n : ℝ) ^ (-θ)
      ≤ ∑ _n ∈ S, (2 : ℝ) ^ (-((k : ℝ) * θ)) := Finset.sum_le_sum hterm
    _ = S.card * (2 : ℝ) ^ (-((k : ℝ) * θ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * (2 : ℝ) ^ ((k : ℝ) * α) * (2 : ℝ) ^ (-((k : ℝ) * θ)) := by gcongr
    _ = 3 * ((2 : ℝ) ^ (α - θ)) ^ k := by
        rw [mul_assoc, ← Real.rpow_add (by norm_num), ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num)]
        ring_nf

/-- **Sparsity.**  `Σ_n |e(n)| n^{-θ} < ∞` for every `θ > α`. -/
theorem summable_abs_sEdit_rpow (hα0 : 0 < α) (hα : α < 1) (γ : ℝ) (k₀ : ℕ) {θ : ℝ}
    (hθ : α < θ) : Summable fun n : ℕ => |(sEdit α β γ k₀ n : ℝ)| * (n : ℝ) ^ (-θ) := by
  have hθ0 : 0 ≤ θ := by linarith
  set r : ℝ := (2 : ℝ) ^ (α - θ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeo : ∀ K, ∑ k ∈ Finset.range K, 3 * r ^ k ≤ 3 / (1 - r) := by
    intro K
    have hs := (summable_geometric_of_lt_one hr0 hr1).mul_left 3
    have heq : ∑' k : ℕ, 3 * r ^ k = 3 / (1 - r) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
    exact heq ▸ sum_le_tsum _ (fun _ _ => by positivity) hs
  refine summable_of_sum_range_le (c := 3 / (1 - r)) (fun n => by positivity) fun N => ?_
  have h0 : |(sEdit α β γ k₀ 0 : ℝ)| * ((0 : ℕ) : ℝ) ^ (-θ) = 0 := by
    rw [(isEdit_sEdit α β γ k₀).prime 0 Nat.not_prime_zero]; simp
  calc ∑ n ∈ Finset.range N, |(sEdit α β γ k₀ n : ℝ)| * (n : ℝ) ^ (-θ)
      ≤ ∑ n ∈ Finset.range (2 ^ N), |(sEdit α β γ k₀ n : ℝ)| * (n : ℝ) ^ (-θ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono Nat.lt_two_pow_self.le)
          fun _ _ _ => by positivity
    _ = ∑ n ∈ Finset.Ico 1 (2 ^ N), |(sEdit α β γ k₀ n : ℝ)| * (n : ℝ) ^ (-θ) := by
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.two_pow_pos N), h0, zero_add]
    _ = ∑ k ∈ Finset.range N, ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          |(sEdit α β γ k₀ n : ℝ)| * (n : ℝ) ^ (-θ) := sum_Ico_one_two_pow_eq _ N
    _ ≤ ∑ k ∈ Finset.range N, 3 * r ^ k :=
        Finset.sum_le_sum fun k _ => sum_block_abs_sEdit_rpow_le hα0 hα γ k₀ k hθ0
    _ ≤ 3 / (1 - r) := hgeo N

/-! ## The remainder `Q` -/

theorem summable_editRem_majorant (hα0 : 0 < α) (hα : α < 1) (γ : ℝ) (k₀ : ℕ) {a : ℝ}
    (ha : α / 2 < a) :
    Summable fun p : Nat.Primes => |(sEdit α β γ k₀ p : ℝ)| * ((p : ℕ) : ℝ) ^ (-(2 * a)) *
      (1 - (2 : ℝ) ^ (-a))⁻¹ / 2 :=
  (((summable_abs_sEdit_rpow hα0 hα γ k₀ (θ := 2 * a) (by linarith)).subtype _).mul_right _).div_const _

theorem norm_sEdit_mul_logRem_le (γ : ℝ) (k₀ : ℕ) (p : Nat.Primes) {a : ℝ} (ha : 0 < a) {w : ℂ}
    (hw : a ≤ w.re) :
    ‖(sEdit α β γ k₀ p : ℂ) * logRem (((p : ℕ) : ℂ) ^ (-w))‖ ≤
      |(sEdit α β γ k₀ p : ℝ)| * ((p : ℕ) : ℝ) ^ (-(2 * a)) * (1 - (2 : ℝ) ^ (-a))⁻¹ / 2 := by
  have h := norm_logRem_cpow_le (n := (p : ℕ)) p.2.two_le (c := 0) (s := w) (a := a) (σ := a)
    ha le_rfl (by rw [add_zero]; exact hw)
  rw [add_zero] at h
  rw [norm_mul, Complex.norm_intCast]
  calc |(sEdit α β γ k₀ p : ℝ)| * ‖logRem (((p : ℕ) : ℂ) ^ (-w))‖
      ≤ |(sEdit α β γ k₀ p : ℝ)| * (((p : ℕ) : ℝ) ^ (-(2 * a)) * (1 - (2 : ℝ) ^ (-a))⁻¹ / 2) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by ring

/-- **`Q` continues to `Re s > α/2`.** -/
theorem differentiableOn_editRem_sparse (hα0 : 0 < α) (hα : α < 1) (γ : ℝ) (k₀ : ℕ) :
    DifferentiableOn ℂ (editRem (sEdit α β γ k₀)) {s : ℂ | α / 2 < s.re} := by
  intro s hs
  have hs' : α / 2 < s.re := hs
  set a : ℝ := (α / 2 + s.re) / 2 with ha
  have ha1 : α / 2 < a := by rw [ha]; linarith
  have ha0 : 0 < a := by linarith
  set U : Set ℂ := {w : ℂ | a < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (editRem (sEdit α β γ k₀)) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (summable_editRem_majorant hα0 hα γ k₀ ha1) (fun p => ?_) hUo
      (fun p w hw => norm_sEdit_mul_logRem_le γ k₀ p ha0 (le_of_lt hw))
    intro w hw
    have hw' : a < w.re := hw
    have hlt : ‖((p : ℕ) : ℂ) ^ (-(w + 0))‖ < 1 := by
      rw [norm_natCast_cpow_neg (p : ℕ) p.2.pos (w + 0)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt)
        (by simp only [add_zero]; linarith)
    have h := differentiableAt_logRem_cpow (n := (p : ℕ)) p.2.pos (c := 0) (s := w) hlt
    simp only [add_zero] at h
    exact (h.const_mul _).differentiableWithinAt
  exact (hd.differentiableAt (hUo.mem_nhds (by show a < s.re; rw [ha]; linarith))).differentiableWithinAt

/-- `Q` is bounded on `Re s ≥ σ₀ > α/2`. -/
theorem exists_norm_editRem_le (hα0 : 0 < α) (hα : α < 1) (γ : ℝ) (k₀ : ℕ) {σ₀ : ℝ}
    (hσ₀ : α / 2 < σ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → ‖editRem (sEdit α β γ k₀) s‖ ≤ C := by
  have hσ₀0 : 0 < σ₀ := by linarith
  have hmaj := summable_editRem_majorant (β := β) hα0 hα γ k₀ hσ₀
  refine ⟨∑' p : Nat.Primes, |(sEdit α β γ k₀ p : ℝ)| * ((p : ℕ) : ℝ) ^ (-(2 * σ₀)) *
    (1 - (2 : ℝ) ^ (-σ₀))⁻¹ / 2, tsum_nonneg fun p => ?_, fun s hs => ?_⟩
  · have : (2 : ℝ) ^ (-σ₀) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have : 0 ≤ (1 - (2 : ℝ) ^ (-σ₀))⁻¹ := inv_nonneg.mpr (by linarith)
    positivity
  have hb := fun p => norm_sEdit_mul_logRem_le (α := α) (β := β) γ k₀ p hσ₀0 hs
  unfold editRem
  exact (norm_tsum_le_tsum_norm (hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) hb)).trans
    (Summable.tsum_le_tsum hb (hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) hb) hmaj)

/-! ## The remainder `R` -/

/-- The zero `ρ = β + iγ`. -/
def zeroPt (β γ : ℝ) : ℂ := (β : ℂ) + (γ : ℂ) * I

/-- `R(s) = Σ_{p ≥ 2^{k₀}} (λ(p^{-(s+1-ρ)}) + λ(p^{-(s+1-ρ̄)}))`. -/
def pairRem (β γ : ℝ) (k₀ : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, if n.Prime ∧ 2 ^ k₀ ≤ n then
    logRem ((n : ℂ) ^ (-(s + (1 - zeroPt β γ)))) +
      logRem ((n : ℂ) ^ (-(s + (1 - (starRingEnd ℂ) (zeroPt β γ))))) else 0

theorem re_add_one_sub_zeroPt (β γ : ℝ) (s : ℂ) : (s + (1 - zeroPt β γ)).re = s.re + 1 - β := by
  simp [zeroPt]; ring

theorem re_add_one_sub_conj_zeroPt (β γ : ℝ) (s : ℂ) :
    (s + (1 - (starRingEnd ℂ) (zeroPt β γ))).re = s.re + 1 - β := by
  simp [zeroPt]; ring

/-- The majorant `2 n^{-2a} (1 - 2^{-a})⁻¹ / 2` of the terms of `R` on `Re s + 1 - β ≥ a`. -/
theorem norm_pairRem_term_le (β γ : ℝ) (k₀ : ℕ) (n : ℕ) {a : ℝ} (ha : 0 < a) {w : ℂ}
    (hw : a ≤ w.re + 1 - β) :
    ‖(if n.Prime ∧ 2 ^ k₀ ≤ n then
        logRem ((n : ℂ) ^ (-(w + (1 - zeroPt β γ)))) +
          logRem ((n : ℂ) ^ (-(w + (1 - (starRingEnd ℂ) (zeroPt β γ))))) else 0)‖ ≤
      2 * ((n : ℝ) ^ (-(2 * a)) * (1 - (2 : ℝ) ^ (-a))⁻¹ / 2) := by
  have hq : 0 ≤ (1 - (2 : ℝ) ^ (-a))⁻¹ := by
    have : (2 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact inv_nonneg.mpr (by linarith)
  split_ifs with h
  · have h2 := h.1.two_le
    have b1 := norm_logRem_cpow_le (n := n) h2 (c := 1 - zeroPt β γ) (s := w) (a := a) (σ := a)
      ha le_rfl (by rw [re_add_one_sub_zeroPt]; exact hw)
    have b2 := norm_logRem_cpow_le (n := n) h2 (c := 1 - (starRingEnd ℂ) (zeroPt β γ)) (s := w)
      (a := a) (σ := a) ha le_rfl (by rw [re_add_one_sub_conj_zeroPt]; exact hw)
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add b1 b2
      _ = _ := by ring
  · rw [norm_zero]; positivity

theorem summable_pairRem_majorant {a : ℝ} (ha : 1 / 2 < a) :
    Summable fun n : ℕ => 2 * ((n : ℝ) ^ (-(2 * a)) * (1 - (2 : ℝ) ^ (-a))⁻¹ / 2) :=
  ((((Real.summable_nat_rpow.mpr (by linarith : -(2 * a) < -1)).mul_right _).div_const _).mul_left 2)

/-- **`R` continues to `Re s > β - 1/2`.** -/
theorem differentiableOn_pairRem (β γ : ℝ) (k₀ : ℕ) :
    DifferentiableOn ℂ (pairRem β γ k₀) {s : ℂ | β - 1 / 2 < s.re} := by
  intro s hs
  have hs' : β - 1 / 2 < s.re := hs
  set σ₀ : ℝ := (β - 1 / 2 + s.re) / 2 with hσ₀
  set a : ℝ := σ₀ + 1 - β with ha
  have ha1 : 1 / 2 < a := by rw [ha, hσ₀]; linarith
  set U : Set ℂ := {w : ℂ | σ₀ < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (pairRem β γ k₀) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm (summable_pairRem_majorant ha1)
      (fun n => ?_) hUo (fun n w hw => norm_pairRem_term_le β γ k₀ n (by linarith)
        (by have : σ₀ < w.re := hw; rw [ha]; linarith))
    intro w hw
    have hw' : σ₀ < w.re := hw
    split_ifs with h
    · have hn := h.1.pos
      have hlt1 : ‖(n : ℂ) ^ (-(w + (1 - zeroPt β γ)))‖ < 1 := by
        rw [norm_natCast_cpow_neg n hn, re_add_one_sub_zeroPt]
        exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast h.1.one_lt) (by linarith)
      have hlt2 : ‖(n : ℂ) ^ (-(w + (1 - (starRingEnd ℂ) (zeroPt β γ))))‖ < 1 := by
        rw [norm_natCast_cpow_neg n hn, re_add_one_sub_conj_zeroPt]
        exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast h.1.one_lt) (by linarith)
      exact ((differentiableAt_logRem_cpow hn hlt1).add
        (differentiableAt_logRem_cpow hn hlt2)).differentiableWithinAt
    · exact differentiableWithinAt_const _
  exact (hd.differentiableAt (hUo.mem_nhds (by show σ₀ < s.re; rw [hσ₀]; linarith))).differentiableWithinAt

/-- `R` is bounded on `Re s ≥ σ₀ > β - 1/2`. -/
theorem exists_norm_pairRem_le (β γ : ℝ) (k₀ : ℕ) {σ₀ : ℝ} (hσ₀ : β - 1 / 2 < σ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → ‖pairRem β γ k₀ s‖ ≤ C := by
  set a : ℝ := σ₀ + 1 - β with ha
  have ha1 : 1 / 2 < a := by rw [ha]; linarith
  have hmaj := summable_pairRem_majorant ha1
  have hq : 0 ≤ (1 - (2 : ℝ) ^ (-a))⁻¹ := by
    have : (2 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact inv_nonneg.mpr (by linarith)
  refine ⟨∑' n : ℕ, 2 * ((n : ℝ) ^ (-(2 * a)) * (1 - (2 : ℝ) ^ (-a))⁻¹ / 2),
    tsum_nonneg fun n => by positivity, fun s hs => ?_⟩
  have hb := fun n => norm_pairRem_term_le β γ k₀ n (by linarith : 0 < a) (w := s)
    (by rw [ha]; linarith)
  unfold pairRem
  exact (norm_tsum_le_tsum_norm (hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) hb)).trans
    (Summable.tsum_le_tsum hb (hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) hb) hmaj)

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit
