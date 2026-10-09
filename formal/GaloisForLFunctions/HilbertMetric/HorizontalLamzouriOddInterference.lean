import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriPositivePart

/-!
# Odd interference costs only through an angle

Let `Q(v) = α⟪u, v⟫² − Σ_k b_k ⟪h_k, v⟫²` with `α ≥ 0` and `b_k ≥ 0`: one even direction `u`
against any number of odd directions `h_k` of any size. Let `κ` bound the cosine of the angle
between `u` and the odd span, in the form `|⟪d, u⟫| ≤ κ ‖d‖` for every `d ∈ span{h_k}`
(so `κ = ‖P_{span h} u‖` is admissible).

**Theorem** (`positivePartForm_ge_of_oddInterference`). For every `f`,
`α · ((|⟪u, f⟫| − κ‖f‖)⁺)² ≤ ⟪Q⁺ f, f⟫`.

The bound does not depend on the weights `b_k`. However large the odd vectors are, they lower
the positive part only through `κ`. By contrast, the form itself loses `Σ_k b_k⟪h_k, f⟫²`.

**Proof.** `Q ≤ α⟪u, ·⟫²` has at most one positive eigenvalue `λ`, with unit eigenvector `w`.
* If there is none, then `Q ≤ 0` on `{h}^⊥`, so `u ⊥ {h}^⊥`, i.e. `u ∈ span h`. Then `‖u‖ ≤ κ`
  and the left side vanishes.
* Otherwise `α⟪u, w⟫u − Bw = λw` with `B = Σ b_k h_k ⊗ h_k ≥ 0`. Put `z = (λ/α⟪u, w⟫) w`, so
  that `λ(u − z) = Bz`. Then `d = u − z ∈ span h`, `⟪d, z⟫ ≥ 0`, hence `‖d‖ ≤ κ` and
  `⟪u, z⟫ ≥ ‖z‖²`. Since `λ = α⟪u, z⟫`, the positive part at `f` is
  `λ⟪z, f⟫²/‖z‖² ≥ α⟪z, f⟫² ≥ α(|⟪u, f⟫| − κ‖f‖)²`.
-/

open scoped RealInnerProductSpace
open Finset Module

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Scale-free decoupling from odd interference.** For
`Q(v) = α⟪u, v⟫² − Σ_k b_k⟪h_k, v⟫²` (`α, b_k ≥ 0`) diagonalised by `(e, λ)`, and `κ` with
`|⟪d, u⟫| ≤ κ‖d‖` on `span{h_k}`: `α((|⟪u, f⟫| − κ‖f‖)⁺)² ≤ ⟪Q⁺f, f⟫` for every `f`. -/
theorem positivePartForm_ge_of_oddInterference {ι : Type*} [Fintype ι] {n : ℕ}
    (e : OrthonormalBasis (Fin n) ℝ V) (ev : Fin n → ℝ) {α : ℝ} (hα : 0 ≤ α) (u : V)
    (b : ι → ℝ) (hb : ∀ k, 0 ≤ b k) (h : ι → V)
    (hd : ∀ v, α * ⟪u, v⟫ ^ 2 - ∑ k, b k * ⟪h k, v⟫ ^ 2 = ∑ j, ev j * ⟪e j, v⟫ ^ 2)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : ∀ d ∈ Submodule.span ℝ (Set.range h), |⟪d, u⟫| ≤ κ * ‖d‖)
    (f : V) :
    α * max (|⟪u, f⟫| - κ * ‖f‖) 0 ^ 2 ≤ positivePartForm e ev f := by
  classical
  have hPp0 := positivePartForm_nonneg e ev f
  rcases eq_or_lt_of_le hα with hα0 | hαpos
  · rw [← hα0, zero_mul]; exact hPp0
  -- the form as a weighted family and its polarisation
  set c : Unit ⊕ ι → ℝ := Sum.elim (fun _ => α) fun k => -b k with hc
  set w : Unit ⊕ ι → V := Sum.elim (fun _ => u) h with hw
  have hform : ∀ v, weightedForm c w v = α * ⟪u, v⟫ ^ 2 - ∑ k, b k * ⟪h k, v⟫ ^ 2 := fun v => by
    simp only [weightedForm, c, w, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.univ_unique, Finset.sum_singleton, neg_mul, Finset.sum_neg_distrib]
    ring
  have hdw : ∀ v, weightedForm c w v = ∑ j, ev j * ⟪e j, v⟫ ^ 2 := fun v => by
    rw [hform, hd]
  have hpol : ∀ v x, α * (⟪u, v⟫ * ⟪u, x⟫) - ∑ k, b k * (⟪h k, v⟫ * ⟪h k, x⟫) =
      ∑ j, ev j * (⟪e j, v⟫ * ⟪e j, x⟫) := fun v x => by
    rw [← weightedBilin_eq e ev hdw v x]
    simp only [c, w, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
      Finset.sum_singleton, neg_mul, Finset.sum_neg_distrib]
    ring
  -- at most one positive eigenvalue
  have hcap : ∀ v, (∀ _p : Unit, ⟪u, v⟫ = 0) → weightedForm c w v ≤ 0 := fun v hv => by
    rw [hform, hv ()]
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) =>
      mul_nonneg (hb k) (sq_nonneg ⟪h k, v⟫)
    nlinarith
  have hcard := card_positiveEigen_le c w (fun _ : Unit => u) e ev hdw hcap
  rw [Fintype.card_unit] at hcard
  set Bv : V → V := fun v => ∑ k, (b k * ⟪h k, v⟫) • h k with hBv
  have hBmem : ∀ v, Bv v ∈ Submodule.span ℝ (Set.range h) := fun v =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self k))
  have hBinner : ∀ v x, ⟪Bv v, x⟫ = ∑ k, b k * (⟪h k, v⟫ * ⟪h k, x⟫) := fun v x => by
    simp only [Bv, sum_inner, real_inner_smul_left]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hBpos : ∀ v, 0 ≤ ⟪Bv v, v⟫ := fun v => by
    rw [hBinner]
    exact Finset.sum_nonneg fun k _ => by nlinarith [hb k, sq_nonneg ⟪h k, v⟫]
  have hBsmul : ∀ (r : ℝ) v, Bv (r • v) = r • Bv v := fun r v => by
    simp only [Bv, real_inner_smul_right, Finset.smul_sum, smul_smul]
    exact Finset.sum_congr rfl fun k _ => by congr 1; ring
  by_cases hex : ∃ j, 0 < ev j
  · obtain ⟨j₀, hj₀⟩ := hex
    have honly : ∀ j, j ≠ j₀ → ev j ≤ 0 := fun j hj => by
      by_contra hcon
      push Not at hcon
      exact hj (Finset.card_le_one.mp hcard j (by simp [hcon]) j₀ (by simp [hj₀]))
    set lam := ev j₀ with hlam
    set w₀ := e j₀ with hw₀
    have hw₀n : ‖w₀‖ = 1 := e.orthonormal.1 j₀
    -- the positive part is carried by `w₀`
    have hPp : positivePartForm e ev f = lam * ⟪w₀, f⟫ ^ 2 := by
      unfold positivePartForm
      rw [Finset.sum_eq_single j₀]
      · rw [max_eq_left hj₀.le]
      · intro j _ hj; rw [max_eq_right (honly j hj)]; ring
      · simp
    -- the eigenvector equation `α⟪u,w₀⟫u − Bw₀ = λw₀`
    set s := α * ⟪u, w₀⟫ with hs
    have heig : s • u - Bv w₀ = lam • w₀ := by
      refine ext_inner_right ℝ fun x => ?_
      rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hBinner]
      have h1 := hpol w₀ x
      have h2 : ∑ j, ev j * (⟪e j, w₀⟫ * ⟪e j, x⟫) = lam * ⟪w₀, x⟫ := by
        rw [Finset.sum_eq_single j₀]
        · rw [hw₀, real_inner_self_eq_norm_sq, e.orthonormal.1 j₀]; ring
        · intro j _ hj; rw [hw₀, e.orthonormal.2 hj]; ring
        · simp
      rw [h2] at h1
      rw [hs]
      linarith
    have hBw : Bv w₀ = s • u - lam • w₀ := by rw [← heig]; abel
    have hs0 : s ≠ 0 := by
      intro hs0
      have h1 : ⟪Bv w₀, w₀⟫ = -lam := by
        rw [hBw, hs0, zero_smul, zero_sub, inner_neg_left, real_inner_smul_left,
          real_inner_self_eq_norm_sq, hw₀n]
        ring
      linarith [hBpos w₀]
    have hss : lam / s * s = lam := div_mul_cancel₀ lam hs0
    obtain ⟨z, hz⟩ : ∃ z : V, z = (lam / s) • w₀ := ⟨_, rfl⟩
    obtain ⟨d, hdd⟩ : ∃ d : V, d = u - z := ⟨_, rfl⟩
    -- `λ d = B z`
    have hdB : d = (1 / lam) • Bv z := by
      have e1 : 1 / lam * (lam / s * s) = 1 := by field_simp
      have e2 : 1 / lam * (lam / s * lam) = lam / s := by field_simp
      rw [hdd, hz, hBsmul, hBw]
      simp only [smul_sub, smul_smul]
      rw [e1, e2, one_smul]
    have hdmem : d ∈ Submodule.span ℝ (Set.range h) := by
      rw [hdB]; exact Submodule.smul_mem _ _ (hBmem z)
    have hdz : 0 ≤ ⟪d, z⟫ := by
      rw [hdB, real_inner_smul_left]
      exact mul_nonneg (by positivity) (hBpos z)
    -- `‖d‖ ≤ κ`
    have hdκ : ‖d‖ ≤ κ := by
      have h1 : ‖d‖ ^ 2 ≤ |⟪d, u⟫| := by
        have : ‖d‖ ^ 2 = ⟪d, u⟫ - ⟪d, z⟫ := by
          have : ⟪d, d⟫ = ⟪d, u⟫ - ⟪d, z⟫ := by
            rw [← inner_sub_right, ← hdd]
          rw [← real_inner_self_eq_norm_sq, this]
        rw [this]
        linarith [le_abs_self ⟪d, u⟫]
      have h2 := h1.trans (hκ d hdmem)
      rcases eq_or_lt_of_le (norm_nonneg d) with h0 | hpos
      · rw [← h0]; exact hκ0
      · nlinarith
    -- `⟪u, z⟫ ≥ ‖z‖²` and `λ = α⟪u, z⟫`
    have huz : ‖z‖ ^ 2 ≤ ⟪u, z⟫ := by
      have : ⟪u, z⟫ = ‖z‖ ^ 2 + ⟪d, z⟫ := by
        rw [hdd, inner_sub_left, real_inner_self_eq_norm_sq]; ring
      linarith
    have hlamz : lam = α * ⟪u, z⟫ := by
      have : α * ⟪u, z⟫ = lam / s * s := by
        rw [hz, real_inner_smul_right, hs]; ring
      rw [this, hss]
    have hne : lam / s ≠ 0 := div_ne_zero hj₀.ne' hs0
    have hzn : ‖z‖ ^ 2 = (lam / s) ^ 2 := by
      rw [hz, norm_smul, hw₀n, mul_one, Real.norm_eq_abs, sq_abs]
    have hzpos : 0 < ‖z‖ ^ 2 := by
      rw [hzn]; exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
    have hwf : ⟪w₀, f⟫ ^ 2 = ⟪z, f⟫ ^ 2 / ‖z‖ ^ 2 := by
      rw [hzn, hz, real_inner_smul_left, mul_pow]
      field_simp
    -- assemble
    have hmain : α * ⟪z, f⟫ ^ 2 ≤ positivePartForm e ev f := by
      rw [hPp, hwf, mul_div_assoc', le_div_iff₀ hzpos, hlamz]
      have := mul_le_mul_of_nonneg_left huz (mul_nonneg hα (sq_nonneg ⟪z, f⟫))
      nlinarith
    have hzf : max (|⟪u, f⟫| - κ * ‖f‖) 0 ^ 2 ≤ ⟪z, f⟫ ^ 2 := by
      rcases le_total (|⟪u, f⟫| - κ * ‖f‖) 0 with hle | hle
      · rw [max_eq_right hle]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact sq_nonneg _
      · rw [max_eq_left hle]
        have hu : ⟪u, f⟫ = ⟪z, f⟫ + ⟪d, f⟫ := by
          rw [hdd, inner_sub_left]; ring
        have hdf : |⟪d, f⟫| ≤ κ * ‖f‖ :=
          (abs_real_inner_le_norm d f).trans (mul_le_mul_of_nonneg_right hdκ (norm_nonneg f))
        have : |⟪u, f⟫| - κ * ‖f‖ ≤ |⟪z, f⟫| := by
          rw [hu]
          linarith [abs_add_le ⟪z, f⟫ ⟪d, f⟫]
        calc (|⟪u, f⟫| - κ * ‖f‖) ^ 2 ≤ |⟪z, f⟫| ^ 2 := pow_le_pow_left₀ hle this 2
          _ = ⟪z, f⟫ ^ 2 := sq_abs _
    exact (mul_le_mul_of_nonneg_left hzf hα).trans hmain
  · -- no positive eigenvalue: `u ∈ span h`
    push Not at hex
    have hPp' : positivePartForm e ev f = 0 := Finset.sum_eq_zero fun j _ => by
      rw [max_eq_right (hex j)]; ring
    set K := Submodule.span ℝ (Set.range h) with hK
    have huK : u ∈ K := by
      rw [← Submodule.orthogonal_orthogonal K, Submodule.mem_orthogonal]
      intro v hv
      have hvh : ∀ k, ⟪h k, v⟫ = 0 := fun k =>
        (Submodule.mem_orthogonal K v).mp hv (h k) (Submodule.subset_span (Set.mem_range_self k))
      have hle : α * ⟪u, v⟫ ^ 2 ≤ 0 := by
        have := hd v
        simp only [hvh, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
          Finset.sum_const_zero, sub_zero] at this
        rw [this]
        exact Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (hex j) (sq_nonneg _)
      have h2 : ⟪u, v⟫ ^ 2 = 0 :=
        le_antisymm (by nlinarith [sq_nonneg ⟪u, v⟫]) (sq_nonneg _)
      rw [real_inner_comm]
      exact pow_eq_zero_iff two_ne_zero |>.mp h2
    have hu := hκ u huK
    rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hu
    have hunorm : ‖u‖ ≤ κ := by
      rcases eq_or_lt_of_le (norm_nonneg u) with h0 | hpos
      · rw [← h0]; exact hκ0
      · nlinarith
    have hzero : |⟪u, f⟫| - κ * ‖f‖ ≤ 0 := by
      have := abs_real_inner_le_norm u f
      nlinarith [norm_nonneg f]
    rw [max_eq_right hzero, hPp']
    simp

end GaloisForLFunctions.HilbertMetric
