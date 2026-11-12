import GaloisForLFunctions.WorldsOfTheZeroConfiguration.ASignedGroupedEditHasSquareRootDiscrepancy

/-!
# The series of the signed edit continues below one half

Let `c(p) = e(p) + 2 p^{β-1} cos(γ log p)` be the target of the signed grouped edit
(`SignedEdit.target`).  Its Dirichlet series above the cutoff `2^{k₀}`,

`H₁(s) = Σ_{p ≥ 2^{k₀}} c(p) p^{-s} = Σ_{k ≥ k₀} h_k(s)`,   `h_k(s) = Σ_{p ∈ [2^k, 2^{k+1})} c(p) p^{-s}`,

is summed block by block (`editSeries`).

* **Block bound** (`norm_blockSeries_le`).  Summation by parts in a block against the decreasing
  weight `n^{-σ}`, with the square-root discrepancy of the partial sums, gives
  `|h_k(σ + it)| ≤ (26 · 2^{kα/2} √(k+1) √log(|t|+2) + 2) · 2^{-kσ}`.
* **Continuation** (`differentiableOn_editSeries`).  `H₁` is holomorphic on `Re s > α/2`.
* **Height bound** (`exists_norm_editSeries_le`).  On `Re s ≥ σ₀ > α/2`,
  `|H₁(s)| ≤ C₁ √log(|Im s| + 2) + C₂`: the exponential of `H₁` is `O((1 + |t|)^ε)` for every `ε`.
* **The prime sum** (`editSeries_eq_tsum`).  On `Re s > 1`, `H₁` is the absolutely convergent
  sum `Σ_{p prime, p ≥ 2^{k₀}} c(p) p^{-s}`.
-/

open Complex Finset Filter Topology
open RHTower.BeurlingDeletion

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit

variable {α β : ℝ}

/-- The block series `h_k(s) = Σ_{p ∈ block k} c(p) p^{-s}`. -/
def blockSeries (α β γ : ℝ) (k₀ k : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ blockPrimes k, target α β γ k₀ p * (p : ℂ) ^ (-s)

/-- The edit series `H₁(s) = Σ_{k ≥ k₀} h_k(s)`. -/
def editSeries (α β γ : ℝ) (k₀ : ℕ) (s : ℂ) : ℂ :=
  ∑' k : ℕ, blockSeries α β γ k₀ (k + k₀) s

/-- The discrepancy constant of block `k` at height `t`. -/
def blockDisc (α : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  26 * (2 : ℝ) ^ ((k : ℝ) * α / 2) * Real.sqrt ((k : ℝ) + 1) * Real.sqrt (Real.log (|t| + 2)) + 2

theorem blockDisc_nonneg (α : ℝ) (k : ℕ) (t : ℝ) : 0 ≤ blockDisc α k t := by
  unfold blockDisc; positivity

/-- Telescoping a decreasing weight. -/
theorem sum_Ico_sub_succ (g : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, (g i - g (i + 1)) = g m - g n := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih => rw [Finset.sum_Ico_succ_top hmn, ih]; ring

theorem natCast_cpow_split {p : ℕ} (hp : 0 < p) (σ t : ℝ) :
    (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
      (((p : ℝ) ^ (-σ) : ℝ) : ℂ) * (p : ℂ) ^ (-((t : ℂ) * I)) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [neg_add, Complex.cpow_add _ _ hp0, Complex.ofReal_cpow (Nat.cast_nonneg p)]
  push_cast
  rfl

/-- **The block bound.**  For `k ≥ k₀` and `σ ≥ 0`,
`|h_k(σ + it)| ≤ (26 · 2^{kα/2} √(k+1) √log(|t|+2) + 2) · 2^{-kσ}`. -/
theorem norm_blockSeries_le (hα0 : 0 < α) (hα : α < 1) (hβ : β < 1) (γ : ℝ) {k₀ k : ℕ}
    (hk : 1 ≤ (k : ℝ) * (α - β)) (hkk : k₀ ≤ k) {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) :
    ‖blockSeries α β γ k₀ k ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      blockDisc α k t * (2 : ℝ) ^ (-((k : ℝ) * σ)) := by
  classical
  set M : ℕ := 2 ^ k with hM
  set N : ℕ := 2 ^ (k + 1) with hN
  have hMN : M < N := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  set F : ℕ → ℂ := fun n => target α β γ k₀ n * (n : ℂ) ^ (-((t : ℂ) * I)) with hF
  set a : ℕ → ℂ := fun n => if n ∈ blockPrimes k then F n else 0 with ha
  set f : ℕ → ℂ := fun n => (((n : ℝ) ^ (-σ) : ℝ) : ℂ) with hf
  set Δ := blockDisc α k t with hΔ
  -- the block series as a weighted sum over `[M, N)`
  have hser : blockSeries α β γ k₀ k ((σ : ℂ) + (t : ℂ) * I) =
      ∑ i ∈ Finset.Ico M N, f i • a i := by
    unfold blockSeries
    rw [show blockPrimes k = (Finset.Ico M N).filter Nat.Prime from rfl, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hmem : n ∈ blockPrimes k ↔ n.Prime := by
      rw [mem_blockPrimes]
      simp only [Finset.mem_Ico] at hn
      exact ⟨fun h => h.1, fun h => ⟨h, hn⟩⟩
    by_cases hp : n.Prime
    · rw [if_pos hp, smul_eq_mul]
      simp only [ha, hF, hf, if_pos (hmem.mpr hp)]
      rw [natCast_cpow_split hp.pos σ t]
      ring
    · rw [if_neg hp, smul_eq_mul]
      simp only [ha, if_neg (fun h => hp (hmem.mp h)), mul_zero]
  -- the partial sums are block deviations
  have hG : ∀ j : ℕ, ‖∑ i ∈ Finset.range (j + 1), a i‖ ≤ Δ := by
    intro j
    have e1 : ∑ i ∈ Finset.range (j + 1), a i = ∑ i ∈ Finset.range (j + 1) ∩ blockPrimes k, F i :=
      Finset.sum_ite_mem _ _ _
    have e2 : ∑ p ∈ blockPrimes k, target α β γ k₀ p * testFn (j : ℝ) t p =
        ∑ p ∈ blockPrimes k ∩ Finset.range (j + 1), F p := by
      rw [← Finset.sum_ite_mem]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp0 : 0 < p := (mem_blockPrimes.mp hp).1.pos
      unfold testFn
      by_cases hpj : p ≤ j
      · rw [if_pos ⟨hp0, by exact_mod_cast hpj⟩, if_pos (Finset.mem_range.mpr (by omega))]
      · rw [if_neg fun h => hpj (by exact_mod_cast h.2), if_neg fun h => hpj (by
          have := Finset.mem_range.mp h; omega), mul_zero]
    rw [e1, Finset.inter_comm, ← e2]
    exact norm_sum_target_testFn_le hα0 hα hβ γ hk hkk (j : ℝ) t
  have hGM : ∑ i ∈ Finset.range M, a i = 0 := Finset.sum_eq_zero fun i hi => by
    simp only [ha]
    rw [if_neg]
    intro h
    have h1 := (mem_blockPrimes.mp h).2.1
    have h2 := Finset.mem_range.mp hi
    omega
  have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel (by omega)
  have hGN : ‖∑ i ∈ Finset.range N, a i‖ ≤ Δ := by rw [← hN1]; exact hG _
  set g : ℕ → ℝ := fun n => (n : ℝ) ^ (-σ) with hg
  have hfn : ∀ n : ℕ, ‖f n‖ = g n := fun n => by
    simp only [hf, hg]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hfd : ∀ i ∈ Finset.Ico M (N - 1), ‖f (i + 1) - f i‖ = g i - g (i + 1) := by
    intro i hi
    have hi1 : (1 : ℝ) ≤ i := by
      have := (Finset.mem_Ico.mp hi).1
      exact_mod_cast le_trans hM1 this
    have hmono : g (i + 1) ≤ g i := by
      simp only [hg]
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by push_cast; linarith) (by linarith)
    simp only [hf, hg]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by
      simp only [hg] at hmono; linarith)]
    ring
  have hMle : M ≤ N - 1 := by omega
  rw [hser, Finset.sum_Ico_by_parts f a hMN, hGM, smul_zero, sub_zero]
  have hsum_le : ‖∑ i ∈ Finset.Ico M (N - 1), (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), a j‖
      ≤ ∑ i ∈ Finset.Ico M (N - 1), (g i - g (i + 1)) * Δ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_smul, hfd i hi]
    exact mul_le_mul_of_nonneg_left (hG i) (by rw [← hfd i hi]; exact norm_nonneg _)
  have htel : ∑ i ∈ Finset.Ico M (N - 1), (g i - g (i + 1)) * Δ = (g M - g (N - 1)) * Δ := by
    rw [← Finset.sum_mul, sum_Ico_sub_succ g hMle]
  have hgM : g M = (2 : ℝ) ^ (-((k : ℝ) * σ)) := by
    simp only [hg, hM]
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    ring_nf
  calc ‖f (N - 1) • ∑ i ∈ Finset.range N, a i -
        ∑ i ∈ Finset.Ico M (N - 1), (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), a j‖
      ≤ ‖f (N - 1) • ∑ i ∈ Finset.range N, a i‖ +
          ‖∑ i ∈ Finset.Ico M (N - 1), (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), a j‖ :=
        norm_sub_le _ _
    _ ≤ g (N - 1) * Δ + (g M - g (N - 1)) * Δ := by
        rw [norm_smul, hfn]
        exact add_le_add (mul_le_mul_of_nonneg_left hGN (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (hsum_le.trans htel.le)
    _ = Δ * (2 : ℝ) ^ (-((k : ℝ) * σ)) := by rw [← hgM]; ring

theorem differentiable_blockSeries (α β γ : ℝ) (k₀ k : ℕ) :
    Differentiable ℂ (blockSeries α β γ k₀ k) := by
  unfold blockSeries
  refine Differentiable.fun_sum fun p hp => ?_
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (mem_blockPrimes.mp hp).1.ne_zero
  intro s
  exact (differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hp0))

/-- The summable majorant of the shifted blocks on `Re s ≥ σ₀`, `|Im s| ≤ T`. -/
def blockMajorant (α σ₀ : ℝ) (k₀ : ℕ) (L : ℝ) (k : ℕ) : ℝ :=
  26 * Real.sqrt L * (((k + k₀ : ℕ) : ℝ) + 1) * ((2 : ℝ) ^ (α / 2 - σ₀)) ^ (k + k₀) +
    2 * ((2 : ℝ) ^ (-σ₀)) ^ (k + k₀)

theorem summable_blockMajorant {σ₀ : ℝ} (hσ₀ : α / 2 < σ₀) (hσ₀0 : 0 < σ₀) (k₀ : ℕ) (L : ℝ) :
    Summable (blockMajorant α σ₀ k₀ L) := by
  have hr : (2 : ℝ) ^ (α / 2 - σ₀) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr0 : 0 ≤ (2 : ℝ) ^ (α / 2 - σ₀) := by positivity
  have hq : (2 : ℝ) ^ (-σ₀) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0 : 0 ≤ (2 : ℝ) ^ (-σ₀) := by positivity
  have h1 : Summable fun K : ℕ => ((K : ℝ) + 1) * ((2 : ℝ) ^ (α / 2 - σ₀)) ^ K := by
    have ha := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (r := (2 : ℝ) ^ (α / 2 - σ₀)) (by rw [Real.norm_of_nonneg hr0]; exact hr)
    have hb := summable_geometric_of_lt_one hr0 hr
    exact (ha.add hb).congr fun K => by simp only [pow_one]; ring
  have h2 : Summable fun K : ℕ => ((2 : ℝ) ^ (-σ₀)) ^ K := summable_geometric_of_lt_one hq0 hq
  have h1' := ((summable_nat_add_iff k₀).mpr h1).mul_left (26 * Real.sqrt L)
  have h2' := ((summable_nat_add_iff k₀).mpr h2).mul_left 2
  refine (h1'.add h2').congr fun k => ?_
  unfold blockMajorant
  push_cast
  ring

/-- Each shifted block is bounded by the majorant at the height `|t|`. -/
theorem norm_blockSeries_le_majorant (hα0 : 0 < α) (hα : α < 1) (hβ : β < 1) (γ : ℝ) {k₀ : ℕ}
    (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {σ₀ : ℝ} (hσ₀0 : 0 ≤ σ₀) {s : ℂ} (hs : σ₀ ≤ s.re) (k : ℕ) :
    ‖blockSeries α β γ k₀ (k + k₀) s‖ ≤
      blockMajorant α σ₀ k₀ (Real.log (|s.im| + 2)) k := by
  have hαβ : β < α := by
    by_contra h
    push Not at h
    have : (k₀ : ℝ) * (α - β) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
    linarith
  set K := k + k₀ with hK
  have hk : 1 ≤ (K : ℝ) * (α - β) := one_le_of_le hαβ hk₀ (by omega)
  have hs' : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I := (Complex.re_add_im s).symm
  have hb := norm_blockSeries_le hα0 hα hβ γ hk (by omega : k₀ ≤ K) (le_trans hσ₀0 hs) s.im
  rw [← hs'] at hb
  refine hb.trans ?_
  have hpow : (2 : ℝ) ^ (-((K : ℝ) * s.re)) ≤ ((2 : ℝ) ^ (-σ₀)) ^ K := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [(Nat.cast_nonneg K : (0:ℝ) ≤ K)])
  have hmix : (2 : ℝ) ^ ((K : ℝ) * α / 2) * ((2 : ℝ) ^ (-σ₀)) ^ K = ((2 : ℝ) ^ (α / 2 - σ₀)) ^ K := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1; ring
  have hsq : Real.sqrt ((K : ℝ) + 1) ≤ (K : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith [(Nat.cast_nonneg K : (0:ℝ) ≤ K)]
  unfold blockDisc blockMajorant
  rw [← hK]
  have hL0 : 0 ≤ Real.sqrt (Real.log (|s.im| + 2)) := Real.sqrt_nonneg _
  have hq0 : 0 ≤ ((2 : ℝ) ^ (-σ₀)) ^ K := by positivity
  calc (26 * (2 : ℝ) ^ ((K : ℝ) * α / 2) * Real.sqrt ((K : ℝ) + 1) *
        Real.sqrt (Real.log (|s.im| + 2)) + 2) * (2 : ℝ) ^ (-((K : ℝ) * s.re))
      ≤ (26 * (2 : ℝ) ^ ((K : ℝ) * α / 2) * Real.sqrt ((K : ℝ) + 1) *
        Real.sqrt (Real.log (|s.im| + 2)) + 2) * ((2 : ℝ) ^ (-σ₀)) ^ K := by gcongr
    _ = 26 * Real.sqrt (Real.log (|s.im| + 2)) * Real.sqrt ((K : ℝ) + 1) *
          ((2 : ℝ) ^ ((K : ℝ) * α / 2) * ((2 : ℝ) ^ (-σ₀)) ^ K) + 2 * ((2 : ℝ) ^ (-σ₀)) ^ K := by
        ring
    _ ≤ 26 * Real.sqrt (Real.log (|s.im| + 2)) * ((K : ℝ) + 1) * ((2 : ℝ) ^ (α / 2 - σ₀)) ^ K +
          2 * ((2 : ℝ) ^ (-σ₀)) ^ K := by
        rw [hmix]; gcongr

/-- **The edit series is holomorphic on `Re s > α/2`.** -/
theorem differentiableOn_editSeries (hα0 : 0 < α) (hα : α < 1) (hβ : β < 1) (γ : ℝ) {k₀ : ℕ}
    (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) :
    DifferentiableOn ℂ (editSeries α β γ k₀) {s : ℂ | α / 2 < s.re} := by
  intro s hs
  have hs' : α / 2 < s.re := hs
  set σ₀ : ℝ := (α / 2 + s.re) / 2 with hσ₀
  set T : ℝ := |s.im| + 1 with hT
  set U : Set ℂ := {z : ℂ | σ₀ < z.re ∧ |z.im| < T} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  have hsU : s ∈ U := ⟨by rw [hσ₀]; linarith, by rw [hT]; linarith⟩
  have hσ₀0 : 0 < σ₀ := by rw [hσ₀]; linarith
  have hdiff : DifferentiableOn ℂ (editSeries α β γ k₀) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (summable_blockMajorant (α := α) (σ₀ := σ₀) (by rw [hσ₀]; linarith) hσ₀0 k₀
        (Real.log (T + 2)))
      (fun k => (differentiable_blockSeries α β γ k₀ (k + k₀)).differentiableOn) hUo
      fun k z hz => ?_
    refine (norm_blockSeries_le_majorant hα0 hα hβ γ hk₀ hσ₀0.le hz.1.le k).trans ?_
    unfold blockMajorant
    have hlog : Real.log (|z.im| + 2) ≤ Real.log (T + 2) :=
      Real.log_le_log (by positivity) (by linarith [hz.2])
    gcongr
  exact (hdiff.differentiableAt (hUo.mem_nhds hsU)).differentiableWithinAt

/-- **The height bound.**  On `Re s ≥ σ₀ > α/2`, `|H₁(s)| ≤ C₁ √log(|Im s| + 2) + C₂`. -/
theorem exists_norm_editSeries_le (hα0 : 0 < α) (hα : α < 1) (hβ : β < 1) (γ : ℝ) {k₀ : ℕ}
    (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {σ₀ : ℝ} (hσ₀ : α / 2 < σ₀) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ s : ℂ, σ₀ ≤ s.re →
      ‖editSeries α β γ k₀ s‖ ≤ C₁ * Real.sqrt (Real.log (|s.im| + 2)) + C₂ := by
  have hσ₀0 : 0 < σ₀ := by linarith
  have hr0 : 0 ≤ (2 : ℝ) ^ (α / 2 - σ₀) := by positivity
  have hq0 : 0 ≤ (2 : ℝ) ^ (-σ₀) := by positivity
  set A₁ : ℝ := ∑' k : ℕ, (((k + k₀ : ℕ) : ℝ) + 1) * ((2 : ℝ) ^ (α / 2 - σ₀)) ^ (k + k₀) with hA₁
  set A₂ : ℝ := ∑' k : ℕ, ((2 : ℝ) ^ (-σ₀)) ^ (k + k₀) with hA₂
  have hr : (2 : ℝ) ^ (α / 2 - σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hS1 : Summable fun k : ℕ =>
      (((k + k₀ : ℕ) : ℝ) + 1) * ((2 : ℝ) ^ (α / 2 - σ₀)) ^ (k + k₀) := by
    have ha := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (r := (2 : ℝ) ^ (α / 2 - σ₀)) (by rw [Real.norm_of_nonneg hr0]; exact hr)
    have hb := summable_geometric_of_lt_one hr0 hr
    have h1 : Summable fun K : ℕ => ((K : ℝ) + 1) * ((2 : ℝ) ^ (α / 2 - σ₀)) ^ K :=
      (ha.add hb).congr fun K => by simp only [pow_one]; ring
    exact (summable_nat_add_iff k₀).mpr h1
  have hS2 : Summable fun k : ℕ => ((2 : ℝ) ^ (-σ₀)) ^ (k + k₀) :=
    (summable_nat_add_iff k₀).mpr (summable_geometric_of_lt_one hq0
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))
  refine ⟨26 * A₁, 2 * A₂, by positivity, by positivity, fun s hs => ?_⟩
  set L := Real.log (|s.im| + 2) with hL
  have hbound := norm_blockSeries_le_majorant hα0 hα hβ γ hk₀ hσ₀0.le hs
  have hmaj := summable_blockMajorant hσ₀ hσ₀0 k₀ L
  have hnorm : Summable fun k => ‖blockSeries α β γ k₀ (k + k₀) s‖ :=
    hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have htsum : ∑' k, blockMajorant α σ₀ k₀ L k = 26 * Real.sqrt L * A₁ + 2 * A₂ := by
    have h1 := hS1.hasSum.mul_left (26 * Real.sqrt L)
    have h2 := hS2.hasSum.mul_left 2
    have hfun : (fun k => blockMajorant α σ₀ k₀ L k) = fun k =>
        26 * Real.sqrt L * ((((k + k₀ : ℕ) : ℝ) + 1) * ((2 : ℝ) ^ (α / 2 - σ₀)) ^ (k + k₀)) +
          2 * ((2 : ℝ) ^ (-σ₀)) ^ (k + k₀) := by
      funext k; unfold blockMajorant; ring
    rw [hfun]
    exact (h1.add h2).tsum_eq
  calc ‖editSeries α β γ k₀ s‖ ≤ ∑' k, ‖blockSeries α β γ k₀ (k + k₀) s‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k, blockMajorant α σ₀ k₀ L k := Summable.tsum_le_tsum hbound hnorm hmaj
    _ = 26 * A₁ * Real.sqrt L + 2 * A₂ := by rw [htsum]; ring

/-! ## The prime sum on `Re s > 1` -/

/-- The prime sum `Σ_{p prime, p ≥ 2^{k₀}} c(p) p^{-s}` as a sum over `ℕ`. -/
def primeTerm (α β γ : ℝ) (k₀ : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  if n.Prime ∧ 2 ^ k₀ ≤ n then target α β γ k₀ n * (n : ℂ) ^ (-s) else 0

theorem norm_target_le (hβ : β ≤ 1) (γ : ℝ) (k₀ : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ‖target α β γ k₀ n‖ ≤ 3 := by
  unfold target
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(sEdit α β γ k₀ n : ℂ)‖ ≤ 1 := (isEdit_sEdit α β γ k₀).norm_le_one n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (β - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have h2 : ‖((2 * (n : ℝ) ^ (β - 1) * Real.cos (γ * Real.log n) : ℝ) : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_two,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    have := Real.abs_cos_le_one (γ * Real.log n)
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg n) (β - 1), abs_nonneg (Real.cos (γ * Real.log n))]
  linarith

theorem summable_primeTerm (hβ : β ≤ 1) (γ : ℝ) (k₀ : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (primeTerm α β γ k₀ s) := by
  have hmaj : Summable fun n : ℕ => 3 * ((n : ℝ) ^ s.re)⁻¹ :=
    (Real.summable_nat_rpow_inv.mpr hs).mul_left 3
  refine Summable.of_norm_bounded hmaj fun n => ?_
  unfold primeTerm
  split_ifs with h
  · have hn := h.1.pos
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re, Real.rpow_neg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_right (norm_target_le hβ γ k₀ hn) (by positivity)
  · rw [norm_zero]; positivity

/-- **The edit series is the prime sum on `Re s > 1`.** -/
theorem editSeries_eq_tsum (hβ : β ≤ 1) (γ : ℝ) (k₀ : ℕ) {s : ℂ} (hs : 1 < s.re) :
    editSeries α β γ k₀ s = ∑' n, primeTerm α β γ k₀ s n := by
  classical
  have hsum := (summable_primeTerm (α := α) hβ γ k₀ hs).hasSum
  have hfib := hsum.tsum_fiberwise (Nat.log 2)
  -- the fiber over `K` is the block `[2^K, 2^{K+1})`
  have hblock : ∀ K : ℕ, ∑' (b : (Nat.log 2 ⁻¹' {K} : Set ℕ)), primeTerm α β γ k₀ s b =
      if k₀ ≤ K then blockSeries α β γ k₀ K s else 0 := by
    intro K
    rw [_root_.tsum_subtype, tsum_eq_sum (s := Finset.Ico (2 ^ K) (2 ^ (K + 1))) fun n hn => ?_]
    · have hrw : ∀ n ∈ Finset.Ico (2 ^ K) (2 ^ (K + 1)),
          (Nat.log 2 ⁻¹' {K}).indicator (primeTerm α β γ k₀ s) n = primeTerm α β γ k₀ s n := by
        intro n hn
        rw [Set.indicator_of_mem]
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hn
        exact Nat.log_eq_of_pow_le_of_lt_pow h1 h2
      rw [Finset.sum_congr rfl hrw]
      split_ifs with hK
      · unfold blockSeries
        rw [show blockPrimes K = (Finset.Ico (2 ^ K) (2 ^ (K + 1))).filter Nat.Prime from rfl,
          Finset.sum_filter]
        refine Finset.sum_congr rfl fun n hn => ?_
        have h2 : 2 ^ k₀ ≤ n :=
          le_trans (Nat.pow_le_pow_right (by norm_num) hK) (Finset.mem_Ico.mp hn).1
        unfold primeTerm
        by_cases hp : n.Prime
        · rw [if_pos ⟨hp, h2⟩, if_pos hp]
        · rw [if_neg fun h => hp h.1, if_neg hp]
      · refine Finset.sum_eq_zero fun n hn => ?_
        have hlt : n < 2 ^ k₀ := lt_of_lt_of_le (Finset.mem_Ico.mp hn).2
          (Nat.pow_le_pow_right (by norm_num) (by omega))
        unfold primeTerm
        rw [if_neg fun h => absurd h.2 (not_le.mpr hlt)]
    · rw [Set.indicator_apply]
      split_ifs with hmem
      · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hmem
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; simp [primeTerm, Nat.not_prime_zero]
        · exfalso
          apply hn
          rw [Finset.mem_Ico, ← hmem]
          exact ⟨Nat.pow_log_le_self 2 hpos.ne', Nat.lt_pow_succ_log_self (by norm_num) n⟩
      · rfl
  simp_rw [hblock] at hfib
  have hshift := (hasSum_nat_add_iff' k₀).mpr hfib
  have hzero : ∑ i ∈ Finset.range k₀, (if k₀ ≤ i then blockSeries α β γ k₀ i s else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [if_neg (by have := Finset.mem_range.mp hi; omega)]
  rw [hzero, sub_zero] at hshift
  unfold editSeries
  refine (hshift.congr_fun fun k => ?_).tsum_eq
  rw [if_pos (by omega)]

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit
