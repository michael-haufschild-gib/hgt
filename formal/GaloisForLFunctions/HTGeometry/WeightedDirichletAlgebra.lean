import GaloisForLFunctions.HTGeometry.WeightedDirichletZeroCount
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# The weighted Wiener algebra of Dirichlet readouts

For `η ∈ ℝ` let `A_η` be the arithmetic functions `f` with `‖f‖_η = Σ ‖f n‖ n^η < ∞`.

* `A_η` is a subring of the ring of arithmetic functions under Dirichlet convolution, and
  `‖f * g‖_η ≤ ‖f‖_η ‖g‖_η` because `(mn)^η = m^η n^η`;
* `A_η` is complete: a `‖·‖_η`-Cauchy sequence converges in `‖·‖_η` to an element of `A_η`;
* for `Im z ≥ -η` the readout `f ↦ Σ f(n) n^{iz}` is a ring homomorphism `A_η → ℂ`, so it carries
  determinants to determinants, and it is `1`-Lipschitz for `‖·‖_η`, uniformly in `z`.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set LSeries ArithmeticFunction

namespace GaloisForLFunctions.HTGeometry

/-- The weighted norm `‖f‖_η = Σ ‖f n‖ n^η`. -/
def weightedNorm (f : ℕ → ℂ) (η : ℝ) : ℝ := ∑' n, ‖f n‖ * (n : ℝ) ^ η

theorem weightedNorm_nonneg (f : ℕ → ℂ) (η : ℝ) : 0 ≤ weightedNorm f η :=
  tsum_nonneg fun _ => by positivity

theorem norm_term_neg_eq {f : ℕ → ℂ} (hf0 : f 0 = 0) (η : ℝ) (n : ℕ) :
    ‖term f (-(η : ℂ)) n‖ = ‖f n‖ * (n : ℝ) ^ η := by
  rw [norm_term_eq]
  split_ifs with hn
  · rw [hn, hf0]; simp
  · simp only [neg_re, ofReal_re]
    rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n), neg_neg]

theorem weightedAbsSummable_of_lSeriesSummable {f : ℕ → ℂ} (hf0 : f 0 = 0) {η : ℝ}
    (h : LSeriesSummable f (-(η : ℂ))) : WeightedAbsSummable f η := by
  have := summable_norm_iff.mpr h
  exact this.congr (norm_term_neg_eq hf0 η)

theorem WeightedAbsSummable.lSeriesSummable_neg {f : ℕ → ℂ} {η : ℝ}
    (hf : WeightedAbsSummable f η) : LSeriesSummable f (-(η : ℂ)) :=
  hf.lSeriesSummable (by simp)

/-! ### The subring `A_η` -/

theorem weightedAbsSummable_zero (η : ℝ) : WeightedAbsSummable (0 : ℕ → ℂ) η := by
  simp [WeightedAbsSummable]

theorem arith_sub_apply (f g : ArithmeticFunction ℂ) (n : ℕ) : (f - g) n = f n - g n := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, ← sub_eq_add_neg]

theorem arith_coe_add (f g : ArithmeticFunction ℂ) : ⇑(f + g) = ⇑f + ⇑g :=
  funext fun _ => ArithmeticFunction.add_apply

theorem arith_coe_sub (f g : ArithmeticFunction ℂ) : ⇑(f - g) = ⇑f - ⇑g :=
  funext fun n => arith_sub_apply f g n

/-- `A_η` as a subring of the arithmetic functions. -/
def weightedDirichletSubring (η : ℝ) : Subring (ArithmeticFunction ℂ) where
  carrier := {f | WeightedAbsSummable (⇑f) η}
  mul_mem' := by
    intro f g hf hg
    exact weightedAbsSummable_of_lSeriesSummable ArithmeticFunction.map_zero
      (ArithmeticFunction.LSeriesSummable_mul hf.lSeriesSummable_neg hg.lSeriesSummable_neg)
  one_mem' := by
    refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
    rw [Finset.mem_singleton] at hn
    simp [hn]
  add_mem' := by
    intro f g hf hg
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) (hf.add hg)
    rw [ArithmeticFunction.add_apply, ← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  zero_mem' := weightedAbsSummable_zero η
  neg_mem' := by
    intro f hf
    refine hf.congr fun n => ?_
    simp [ArithmeticFunction.neg_apply]

theorem mem_weightedDirichletSubring {η : ℝ} {f : ArithmeticFunction ℂ} :
    f ∈ weightedDirichletSubring η ↔ WeightedAbsSummable (⇑f) η := Iff.rfl

/-- The pointwise modulus of an arithmetic function. -/
def absArith (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => (‖f n‖ : ℂ), by simp⟩

theorem absArith_apply (f : ArithmeticFunction ℂ) (n : ℕ) : absArith f n = (‖f n‖ : ℂ) := rfl

theorem lSeries_absArith_neg (f : ArithmeticFunction ℂ) (η : ℝ) :
    LSeries (⇑(absArith f)) (-(η : ℂ)) = (weightedNorm (⇑f) η : ℂ) := by
  rw [LSeries, weightedNorm, ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [ArithmeticFunction.map_zero]
  · rw [term_of_ne_zero hpos.ne', absArith_apply, ← ofReal_natCast,
      ← ofReal_neg, ← ofReal_cpow (Nat.cast_nonneg n), div_eq_mul_inv, ← ofReal_inv,
      ← Real.rpow_neg (Nat.cast_nonneg n), neg_neg, ← ofReal_mul]

theorem weightedAbsSummable_absArith {f : ArithmeticFunction ℂ} {η : ℝ}
    (hf : WeightedAbsSummable (⇑f) η) : WeightedAbsSummable (⇑(absArith f)) η :=
  hf.congr fun n => by rw [absArith_apply, Complex.norm_real, Real.norm_eq_abs, abs_norm]

theorem norm_mul_apply_le (f g : ArithmeticFunction ℂ) (n : ℕ) :
    ‖(f * g) n‖ ≤ ((absArith f * absArith g) n).re := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Complex.re_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [absArith_apply, absArith_apply, ← ofReal_mul, ofReal_re, norm_mul]

/-- **Submultiplicativity** `‖f * g‖_η ≤ ‖f‖_η ‖g‖_η`. -/
theorem weightedNorm_mul_le {f g : ArithmeticFunction ℂ} {η : ℝ}
    (hf : WeightedAbsSummable (⇑f) η) (hg : WeightedAbsSummable (⇑g) η) :
    weightedNorm (⇑(f * g)) η ≤ weightedNorm (⇑f) η * weightedNorm (⇑g) η := by
  have hF := weightedAbsSummable_absArith hf
  have hG := weightedAbsSummable_absArith hg
  have hFG : WeightedAbsSummable (⇑(absArith f * absArith g)) η :=
    (weightedDirichletSubring η).mul_mem hF hG
  have hL := ArithmeticFunction.LSeries_mul' hF.lSeriesSummable_neg hG.lSeriesSummable_neg
  rw [lSeries_absArith_neg f η, lSeries_absArith_neg g η] at hL
  have hre : (LSeries (⇑(absArith f * absArith g)) (-(η : ℂ))).re =
      ∑' n, ((absArith f * absArith g) n).re * (n : ℝ) ^ η := by
    rw [LSeries, Complex.re_tsum hFG.lSeriesSummable_neg]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [ArithmeticFunction.map_zero]
    · rw [term_of_ne_zero hpos.ne', ← ofReal_natCast, ← ofReal_neg,
        ← ofReal_cpow (Nat.cast_nonneg n), Complex.div_ofReal_re, div_eq_mul_inv,
        ← Real.rpow_neg (Nat.cast_nonneg n), neg_neg]
  have hre' : (LSeries (⇑(absArith f * absArith g)) (-(η : ℂ))).re =
      weightedNorm (⇑f) η * weightedNorm (⇑g) η := by
    rw [hL, ← ofReal_mul, ofReal_re]
  have hsum2 : Summable fun n => ((absArith f * absArith g) n).re * (n : ℝ) ^ η :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg ((norm_nonneg _).trans (norm_mul_apply_le f g n))
      (by positivity)) (fun n => mul_le_mul_of_nonneg_right (Complex.re_le_norm _) (by positivity))
      hFG
  rw [← hre', hre, weightedNorm]
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (norm_mul_apply_le f g n)
    (by positivity)) ((weightedDirichletSubring η).mul_mem hf hg) hsum2

/-! ### Completeness -/

theorem norm_apply_mul_le_weightedNorm {f : ℕ → ℂ} {η : ℝ} (hf : WeightedAbsSummable f η)
    (n : ℕ) : ‖f n‖ * (n : ℝ) ^ η ≤ weightedNorm f η :=
  hf.le_tsum n fun _ _ => by positivity

/-- **`A_η` is complete.**  A `‖·‖_η`-Cauchy sequence in `A_η` converges in `‖·‖_η` to an element
of `A_η`. -/
theorem exists_limit_of_weightedCauchy {η : ℝ} (f : ℕ → ArithmeticFunction ℂ)
    (hf : ∀ k, f k ∈ weightedDirichletSubring η)
    (hcauchy : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, weightedNorm (⇑(f k - f l)) η < ε) :
    ∃ g ∈ weightedDirichletSubring η,
      Tendsto (fun k => weightedNorm (⇑(f k - g)) η) atTop (𝓝 0) := by
  have hdiff : ∀ k l, WeightedAbsSummable (⇑(f k - f l)) η := fun k l =>
    (weightedDirichletSubring η).sub_mem (hf k) (hf l)
  -- pointwise Cauchy
  have hpt : ∀ n, 0 < n → CauchySeq fun k => f k n := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) ^ η := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy (ε * (n : ℝ) ^ η) (by positivity)
    refine ⟨N, fun k hk l hl => ?_⟩
    have h1 := norm_apply_mul_le_weightedNorm (hdiff k l) n
    have h2 := hN k hk l hl
    rw [dist_eq_norm, ← arith_sub_apply]
    have : ‖(f k - f l) n‖ * (n : ℝ) ^ η < ε * (n : ℝ) ^ η := lt_of_le_of_lt h1 h2
    exact lt_of_mul_lt_mul_right this hn0.le
  classical
  set g0 : ℕ → ℂ := fun n => if h : 0 < n then Classical.choose
    (cauchySeq_tendsto_of_complete (hpt n h)) else 0 with hg0def
  have hg0 : ∀ n, 0 < n → Tendsto (fun k => f k n) atTop (𝓝 (g0 n)) := by
    intro n hn
    simp only [hg0def, dif_pos hn]
    exact Classical.choose_spec (cauchySeq_tendsto_of_complete (hpt n hn))
  let g : ArithmeticFunction ℂ := ⟨g0, by simp [hg0def]⟩
  have hgapp : ∀ n, g n = g0 n := fun n => rfl
  -- the uniform tail bound
  have hbound : ∀ ε > 0, ∃ N, ∀ k ≥ N, WeightedAbsSummable (⇑(f k - g)) η ∧
      weightedNorm (⇑(f k - g)) η ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun k hk => ?_⟩
    have hpartial : ∀ M, ∑ n ∈ Finset.range M, ‖(f k - g) n‖ * (n : ℝ) ^ η ≤ ε := by
      intro M
      have hlimM : Tendsto (fun l => ∑ n ∈ Finset.range M, ‖(f k - f l) n‖ * (n : ℝ) ^ η) atTop
          (𝓝 (∑ n ∈ Finset.range M, ‖(f k - g) n‖ * (n : ℝ) ^ η)) := by
        refine tendsto_finsetSum _ fun n _ => ?_
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          simp [ArithmeticFunction.map_zero]
        · have h1 := (((tendsto_const_nhds (x := f k n)).sub (hg0 n hpos)).norm).mul_const
            ((n : ℝ) ^ η)
          simpa only [arith_sub_apply, hgapp] using h1
      refine le_of_tendsto hlimM ?_
      filter_upwards [eventually_ge_atTop N] with l hl
      exact ((Summable.sum_le_tsum _ (fun _ _ => by positivity) (hdiff k l)).trans
        (hN k hk l hl).le)
    have hsum : WeightedAbsSummable (⇑(f k - g)) η :=
      summable_of_sum_range_le (fun _ => by positivity) hpartial
    exact ⟨hsum, Real.tsum_le_of_sum_range_le (fun _ => by positivity) hpartial⟩
  obtain ⟨N₁, hN₁⟩ := hbound 1 one_pos
  have hgmem : g ∈ weightedDirichletSubring η := by
    have h := (weightedDirichletSubring η).sub_mem (hf N₁) (hN₁ N₁ le_rfl).1
    simpa using h
  refine ⟨g, hgmem, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hbound (ε / 2) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (weightedNorm_nonneg _ _)]
  linarith [(hN k hk).2]

/-! ### The readout homomorphism -/

theorem one_eq_delta : ⇑(1 : ArithmeticFunction ℂ) = LSeries.delta := by
  funext n
  simp [ArithmeticFunction.one_apply, LSeries.delta]

/-- **The readout at `z` (`Im z ≥ -η`) is a ring homomorphism `A_η → ℂ`.** -/
def readoutHom (η : ℝ) (z : ℂ) (hz : -η ≤ z.im) : weightedDirichletSubring η →+* ℂ where
  toFun f := dirichletReadout (⇑(f : ArithmeticFunction ℂ)) z
  map_one' := by
    change LSeries (⇑(1 : ArithmeticFunction ℂ)) _ = 1
    rw [one_eq_delta, LSeries_delta]; rfl
  map_mul' := fun f g => by
    have hs : -η ≤ (-(I * z)).re := by rw [re_neg_I_mul_eq_im]; exact hz
    exact ArithmeticFunction.LSeries_mul' (f.2.lSeriesSummable hs) (g.2.lSeriesSummable hs)
  map_zero' := by
    change LSeries (⇑(0 : ArithmeticFunction ℂ)) _ = 0
    rw [show ⇑(0 : ArithmeticFunction ℂ) = (0 : ℕ → ℂ) from funext fun _ => rfl, LSeries_zero]
    rfl
  map_add' := fun f g => by
    have hs : -η ≤ (-(I * z)).re := by rw [re_neg_I_mul_eq_im]; exact hz
    change LSeries (⇑((f : ArithmeticFunction ℂ) + g)) _ = _
    rw [arith_coe_add]
    exact LSeries_add (f.2.lSeriesSummable hs) (g.2.lSeriesSummable hs)

theorem readoutHom_apply (η : ℝ) (z : ℂ) (hz : -η ≤ z.im) (f : weightedDirichletSubring η) :
    readoutHom η z hz f = dirichletReadout (⇑(f : ArithmeticFunction ℂ)) z := rfl

/-- **Determinants are read entrywise.**  The readout of the determinant of a matrix over `A_η`
is the determinant of the readouts. -/
theorem readoutHom_det {ι : Type*} [Fintype ι] [DecidableEq ι] (η : ℝ) (z : ℂ) (hz : -η ≤ z.im)
    (M : Matrix ι ι (weightedDirichletSubring η)) :
    readoutHom η z hz M.det = (M.map (readoutHom η z hz)).det :=
  RingHom.map_det _ M

/-- **The readout is `‖·‖_η`-Lipschitz**, uniformly on `Im z ≥ -η`. -/
theorem norm_dirichletReadout_sub_le {f g : ArithmeticFunction ℂ} {η : ℝ}
    (hf : WeightedAbsSummable (⇑f) η) (hg : WeightedAbsSummable (⇑g) η) {z : ℂ}
    (hz : -η ≤ z.im) :
    ‖dirichletReadout (⇑f) z - dirichletReadout (⇑g) z‖ ≤ weightedNorm (⇑(f - g)) η := by
  have hs : -η ≤ (-(I * z)).re := by rw [re_neg_I_mul_eq_im]; exact hz
  have hfg : WeightedAbsSummable (⇑(f - g)) η := (weightedDirichletSubring η).sub_mem hf hg
  have e : dirichletReadout (⇑f) z - dirichletReadout (⇑g) z = dirichletReadout (⇑(f - g)) z := by
    unfold dirichletReadout
    rw [arith_coe_sub, LSeries_sub (hf.lSeriesSummable hs) (hg.lSeriesSummable hs)]
  rw [e]
  exact norm_dirichletReadout_le hfg hz

/-- **Limits in `A_η`.**  If `f_k ∈ A_η` and `‖f_k - g‖_η → 0` with each `f_k - g ∈ A_η`, then
`g ∈ A_η` and the readouts converge uniformly on `Im z ≥ -η`. -/
theorem readout_limit {η : ℝ} (f : ℕ → ArithmeticFunction ℂ)
    (hf : ∀ k, f k ∈ weightedDirichletSubring η) (g : ArithmeticFunction ℂ)
    (hfg : ∀ k, WeightedAbsSummable (⇑(f k - g)) η)
    (hlim : Tendsto (fun k => weightedNorm (⇑(f k - g)) η) atTop (𝓝 0)) :
    g ∈ weightedDirichletSubring η ∧
      TendstoUniformlyOn (fun k z => dirichletReadout (⇑(f k)) z) (dirichletReadout (⇑g)) atTop
        {z : ℂ | -η ≤ z.im} := by
  have hg : g ∈ weightedDirichletSubring η := by
    have h := (weightedDirichletSubring η).sub_mem (hf 0) (hfg 0)
    simpa using h
  refine ⟨hg, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with k hk z hz
  rw [dist_comm, dist_eq_norm]
  exact lt_of_le_of_lt (norm_dirichletReadout_sub_le (hf k) hg hz) hk

end GaloisForLFunctions.HTGeometry
