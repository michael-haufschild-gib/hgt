import GaloisForLFunctions.BiScaleUncertainty.SelbergSieveTailQuadraticFormAndTruncatedDivisorGram
import GaloisForLFunctions.BiScaleUncertainty.MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity
import GaloisForLFunctions.RHTower.BaezDuarteLeastSquares

/-!
# Vasyunin / Báez–Duarte Reciprocity & Exact Global-Minus-Head Tail Gram Producer

This module builds **Missing Tool 1** of the `BiScaleUncertainty` framework, resolving the
structural obstruction in `SelbergSieveTailQuadraticFormAndTruncatedDivisorGram` where finite-$K$
truncation via Graham's lemma introduced an uncancelled $+\|c\|_{\ell^1}^2$ remainder:

1. **Exact Reciprocal-Cell Partition of the Bulk Head $(1/(N+1), 1]$ (§1):**
   For every cutoff $N \ge 0$ and integrable function $f$ on $(0, 1]$, the bulk head integral
   on $(1/(N+1), 1]$ decomposes identically into the finite sum over reciprocal cells
   $I_n = (1/(n+1), 1/n]$ ($1 \le n \le N$), each of exact Lebesgue measure
   $\frac{1}{n} - \frac{1}{n+1} = \frac{1}{n(n+1)}$.

2. **Exact Global-Minus-Head Fermi–Nyman Tail Gram Matrix (§2):**
   Evaluating `fermiNymanGen` on each reciprocal cell via `fermiCellMatrix` yields an exact
   closed-form formula for the bulk head Gram matrix on $(1/(N+1), 1]$:
   $$\operatorname{fermiHeadGram}(N, d_1, d_2)
     = \sum_{n=1}^N \frac{\operatorname{fermiCellMatrix}(d_1+1, n)\,\operatorname{fermiCellMatrix}(d_2+1, n)}{n(n+1)},$$
   and expresses the small-$t$ origin-tail Gram matrix on $(0, 1/(N+1)]$ identically as
   $$\operatorname{fermiTailGram}(N, d_1, d_2)
     = \operatorname{fermiGlobalGram}(d_1, d_2) - \operatorname{fermiHeadGram}(N, d_1, d_2),$$
   completely eliminating the $+\|c\|_{\ell^1}^2$ finite-$K$ truncation artifact.

3. **Exact Bulk-Head & Origin-Tail Energy Identities for `singleCellFermiCombinator` (§3):**
   Because `singleCellFermiCombinator (k + 1) N` is a Kronecker delta across the bulk cells
   $I_1, \dots, I_N$, its bulk head $L^2$ energy on $(1/(N+1), 1]$ equals $\frac{1}{(k+1)(k+2)}$
   whenever $k + 1 \le N$, and its small-$t$ origin-tail energy on $(0, 1/(N+1)]$ equals its
   global $L^2(0, 1]$ energy minus $\frac{1}{(k+1)(k+2)}$.

4. **Báez–Duarte Least-Squares Quadratic Producer & Reciprocal Certificate Bridge (§4):**
   Connects the discrete Báez–Duarte Gram quadratic form `bdGram` on reciprocal generators
   `bdDiscrete i = 1/(i+1)` directly to `bdDistDiscrete N ^ 2` and `RiemannHypothesis`.
-/

open Complex MeasureTheory Set Filter Topology Finset
open GaloisForLFunctions.NymanMellin RHTower
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

/-! ## §1. Exact Reciprocal-Cell Partition of the Bulk Head `(1/(N+1), 1]` -/

/-- The Lebesgue measure of the reciprocal cell `Ioc (1 / (n + 1)) (1 / n)` (`n > 0`) is
`1 / (n * (n + 1))`. -/
theorem real_volume_reciprocal_cell {n : ℕ} (hn : 0 < n) :
    Measure.real volume (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) =
      1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn1R : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hnR (by linarith)
  rw [Real.volume_real_Ioc_of_le hle]
  field_simp [hnR.ne', hn1R.ne']
  ring

/-- Integrating a constant `c` over the reciprocal cell `Ioc (1 / (n + 1)) (1 / n)` (`n > 0`)
multiplies `c` by `1 / (n * (n + 1))`. -/
theorem setIntegral_const_on_reciprocal_cell
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ} (hn : 0 < n) (c : E) :
    (∫ _ in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), c) =
      (1 / ((n : ℝ) * ((n : ℝ) + 1))) • c := by
  rw [setIntegral_const, real_volume_reciprocal_cell hn]

/-- **Exact Reciprocal-Cell Partition of the Bulk Head Integral:**
For every `N : ℕ` and every function `f : ℝ → E` integrable on `Ioc 0 1`, the integral of `f`
over the bulk head `Ioc (1 / (N + 1)) 1` decomposes identically into the sum of its integrals
over the individual reciprocal cells `Ioc (1 / (n + 1)) (1 / n)` for `1 ≤ n ≤ N`. -/
theorem setIntegral_Ioc_inv_succ_one_eq_sum_cells
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) {f : ℝ → E} (hf : IntegrableOn f (Ioc (0 : ℝ) 1)) :
    (∫ t in Ioc (1 / ((N : ℝ) + 1)) 1, f t) =
      ∑ n ∈ Finset.Icc 1 N,
        ∫ t in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), f t := by
  induction N with
  | zero =>
    simp
  | succ N ih =>
    set a : ℝ := 1 / (((N + 1 : ℕ) : ℝ) + 1)
    set b : ℝ := 1 / ((N : ℝ) + 1)
    have ha0 : 0 ≤ a := by positivity
    have hab : a ≤ b := by
      unfold a b
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith
    have hb1 : b ≤ 1 :=
      (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg N))
    have hunion : Ioc a b ∪ Ioc b 1 = Ioc a 1 := Ioc_union_Ioc_eq_Ioc hab hb1
    have hdisj : Disjoint (Ioc a b) (Ioc b 1) := Ioc_disjoint_Ioc_of_le le_rfl
    have hint_ab : IntegrableOn f (Ioc a b) :=
      hf.mono_set (Set.Ioc_subset_Ioc ha0 hb1)
    have hint_b1 : IntegrableOn f (Ioc b 1) :=
      hf.mono_set (Set.Ioc_subset_Ioc (ha0.trans hab) le_rfl)
    have hsplit : (∫ t in Ioc a 1, f t) =
        (∫ t in Ioc a b, f t) + (∫ t in Ioc b 1, f t) := by
      rw [← hunion, setIntegral_union hdisj measurableSet_Ioc hint_ab hint_b1]
    have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotMem : N + 1 ∉ Finset.Icc 1 N := by
      simp only [Finset.mem_Icc]
      omega
    have hb_eq : b = 1 / ((N + 1 : ℕ) : ℝ) := by
      unfold b
      push_cast
      rfl
    rw [hsplit, ih, hIcc, Finset.sum_insert hnotMem, ← hb_eq]

/-! ## §2. Exact Global-Minus-Head Fermi–Nyman Tail Gram Matrix -/

/-- The global `L²(0, 1]` Fermi–Nyman Gram entry at natural scales `d₁ + 1` and `d₂ + 1`. -/
def fermiGlobalGram (d₁ d₂ : ℕ) : ℂ :=
  ∫ t in Ioc (0 : ℝ) 1,
    fermiNymanGen ((d₁ + 1 : ℕ) : ℝ) t *
      (starRingEnd ℂ) (fermiNymanGen ((d₂ + 1 : ℕ) : ℝ) t)

/-- The bulk-head Fermi–Nyman Gram entry on `(1 / (N + 1), 1]` at natural scales `d₁ + 1, d₂ + 1`. -/
def fermiHeadGram (N d₁ d₂ : ℕ) : ℂ :=
  ∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
    fermiNymanGen ((d₁ + 1 : ℕ) : ℝ) t *
      (starRingEnd ℂ) (fermiNymanGen ((d₂ + 1 : ℕ) : ℝ) t)

/-- The small-`t` origin-tail Fermi–Nyman Gram entry on `(0, 1 / (N + 1)]` at natural scales `d₁ + 1, d₂ + 1`. -/
def fermiTailGram (N d₁ d₂ : ℕ) : ℂ :=
  ∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
    fermiNymanGen ((d₁ + 1 : ℕ) : ℝ) t *
      (starRingEnd ℂ) (fermiNymanGen ((d₂ + 1 : ℕ) : ℝ) t)

theorem integrableOn_fermiNymanGen_mul_conj (d₁ d₂ : ℕ) :
    IntegrableOn
      (fun t => fermiNymanGen ((d₁ + 1 : ℕ) : ℝ) t *
        (starRingEnd ℂ) (fermiNymanGen ((d₂ + 1 : ℕ) : ℝ) t))
      (Ioc (0 : ℝ) 1) :=
  integrableOn_mul_conj_of_sq (measurable_fermiNymanGen _) (measurable_fermiNymanGen _)
    (integrableOn_normSq_fermiNymanGen _) (integrableOn_normSq_fermiNymanGen _)

/-- **Exact Tail + Head Split of `fermiGlobalGram`:**
For every cutoff `N : ℕ` and scales `d₁, d₂ : ℕ`, the global Gram entry splits identically into
the small-`t` origin-tail Gram entry plus the bulk-head Gram entry. -/
theorem fermiGlobalGram_eq_tail_add_head (N d₁ d₂ : ℕ) :
    fermiGlobalGram d₁ d₂ = fermiTailGram N d₁ d₂ + fermiHeadGram N d₁ d₂ := by
  unfold fermiGlobalGram fermiTailGram fermiHeadGram
  have hc0 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  have hc1 : 1 / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hint := integrableOn_fermiNymanGen_mul_conj d₁ d₂
  rw [← Ioc_union_Ioc_eq_Ioc hc0 hc1,
    setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hint.mono_set (Set.Ioc_subset_Ioc le_rfl hc1))
      (hint.mono_set (Set.Ioc_subset_Ioc hc0 le_rfl))]

/-- **Exact Global-Minus-Head Identity for `fermiTailGram`:**
The small-`t` origin-tail Gram entry equals the global Gram entry minus the bulk-head Gram entry. -/
theorem fermiTailGram_eq_global_sub_head (N d₁ d₂ : ℕ) :
    fermiTailGram N d₁ d₂ = fermiGlobalGram d₁ d₂ - fermiHeadGram N d₁ d₂ := by
  rw [fermiGlobalGram_eq_tail_add_head N d₁ d₂]
  ring

/-- **Exact Discrete Cellular Formula for `fermiHeadGram`:**
For every `N d₁ d₂ : ℕ`, the bulk-head Gram integral on `(1 / (N + 1), 1]` equals the finite
reciprocal-cell sum of `fermiCellMatrix (d₁ + 1) n * fermiCellMatrix (d₂ + 1) n / (n * (n + 1))`. -/
theorem fermiHeadGram_eq_sum_cellMatrix (N d₁ d₂ : ℕ) :
    fermiHeadGram N d₁ d₂ =
      ((∑ n ∈ Finset.Icc 1 N,
        (fermiCellMatrix (d₁ + 1) n * fermiCellMatrix (d₂ + 1) n) /
          ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
  unfold fermiHeadGram
  rw [setIntegral_Ioc_inv_succ_one_eq_sum_cells N (integrableOn_fermiNymanGen_mul_conj d₁ d₂),
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn_pos : 0 < n := (Finset.mem_Icc.mp hn).1
  have hcongr : EqOn
      (fun t => fermiNymanGen ((d₁ + 1 : ℕ) : ℝ) t *
        (starRingEnd ℂ) (fermiNymanGen ((d₂ + 1 : ℕ) : ℝ) t))
      (fun _ => ((fermiCellMatrix (d₁ + 1) n * fermiCellMatrix (d₂ + 1) n : ℝ) : ℂ))
      (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
    intro t ht
    dsimp only
    rw [fermiNymanGen_eq_fermiCellMatrix_on_cell hn_pos ht,
      fermiNymanGen_eq_fermiCellMatrix_on_cell hn_pos ht,
      Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
    setIntegral_const_on_reciprocal_cell hn_pos, Complex.real_smul]
  push_cast
  ring

/-- **Exact Global-Minus-Cellular-Head Formula for `fermiTailGram`:**
For every `N d₁ d₂ : ℕ`, the small-`t` origin-tail Gram entry on `(0, 1 / (N + 1)]` equals
`fermiGlobalGram d₁ d₂` minus the exact finite cellular sum over `1 ≤ n ≤ N`, with **zero
truncation remainder**. -/
theorem fermiTailGram_eq_global_sub_sum_cellMatrix (N d₁ d₂ : ℕ) :
    fermiTailGram N d₁ d₂ =
      fermiGlobalGram d₁ d₂ -
        ((∑ n ∈ Finset.Icc 1 N,
          (fermiCellMatrix (d₁ + 1) n * fermiCellMatrix (d₂ + 1) n) /
            ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
  rw [fermiTailGram_eq_global_sub_head, fermiHeadGram_eq_sum_cellMatrix]

/-! ## §3. Exact Bulk-Head & Origin-Tail Energy of `singleCellFermiCombinator` -/

theorem integrableOn_normSq_of_norm_le {f : ℝ → ℂ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ t, ‖f t‖ ≤ M) :
    IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioc (0 : ℝ) 1) := by
  refine Measure.integrableOn_of_bounded (M := M ^ 2) measure_Ioc_lt_top.ne
    (hf.norm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb t) 2

theorem measurable_dilatedMobiusFermiCombinator (k N : ℕ) :
    Measurable (dilatedMobiusFermiCombinator k N) := by
  unfold dilatedMobiusFermiCombinator
  exact (Finset.measurable_sum _ fun m _ =>
    measurable_const.mul (measurable_fermiNymanGen _)).neg

theorem norm_dilatedMobiusFermiCombinator_le (k N : ℕ) (t : ℝ) :
    ‖dilatedMobiusFermiCombinator k N t‖ ≤
      ∑ m ∈ Finset.Icc 1 (N / k),
        ‖((ArithmeticFunction.moebius m : ℤ) : ℂ)‖ * 3 := by
  unfold dilatedMobiusFermiCombinator
  rw [norm_neg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_fermiNymanGen_le _ _) (norm_nonneg _)

theorem integrableOn_normSq_dilatedMobiusFermiCombinator (k N : ℕ) :
    IntegrableOn (fun t => ‖dilatedMobiusFermiCombinator k N t‖ ^ 2) (Ioc (0 : ℝ) 1) :=
  integrableOn_normSq_of_norm_le (measurable_dilatedMobiusFermiCombinator k N)
    (norm_dilatedMobiusFermiCombinator_le k N)

theorem measurable_dyadicResolventCellThreshold (k N : ℕ) :
    Measurable (dyadicResolventCellThreshold k N) := by
  unfold dyadicResolventCellThreshold
  exact Finset.measurable_sum _ fun j _ =>
    measurable_const.mul (measurable_dilatedMobiusFermiCombinator _ N)

theorem norm_dyadicResolventCellThreshold_le (k N : ℕ) (t : ℝ) :
    ‖dyadicResolventCellThreshold k N t‖ ≤
      ∑ j ∈ Finset.range (N + 1),
        ‖((2 : ℂ) ^ j)‖ *
          ∑ m ∈ Finset.Icc 1 (N / (2 ^ j * k)),
            ‖((ArithmeticFunction.moebius m : ℤ) : ℂ)‖ * 3 := by
  unfold dyadicResolventCellThreshold
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_dilatedMobiusFermiCombinator_le _ N t) (norm_nonneg _)

theorem integrableOn_normSq_dyadicResolventCellThreshold (k N : ℕ) :
    IntegrableOn (fun t => ‖dyadicResolventCellThreshold k N t‖ ^ 2) (Ioc (0 : ℝ) 1) :=
  integrableOn_normSq_of_norm_le (measurable_dyadicResolventCellThreshold k N)
    (norm_dyadicResolventCellThreshold_le k N)

theorem measurable_singleCellFermiCombinator (k N : ℕ) :
    Measurable (singleCellFermiCombinator k N) :=
  (measurable_dyadicResolventCellThreshold k N).sub
    (measurable_dyadicResolventCellThreshold (k + 1) N)

theorem integrableOn_normSq_singleCellFermiCombinator (k N : ℕ) :
    IntegrableOn (fun t => ‖singleCellFermiCombinator k N t‖ ^ 2) (Ioc (0 : ℝ) 1) :=
  integrableOn_normSq_sub (measurable_dyadicResolventCellThreshold k N)
    (measurable_dyadicResolventCellThreshold (k + 1) N)
    (integrableOn_normSq_dyadicResolventCellThreshold k N)
    (integrableOn_normSq_dyadicResolventCellThreshold (k + 1) N)

/-- **Exact Bulk-Head Energy of `singleCellFermiCombinator`:**
For every `k N : ℕ`, the bulk-head `L²` energy of `singleCellFermiCombinator (k + 1) N` on
`(1 / (N + 1), 1]` equals `1 / ((k + 1) * (k + 2))` if `k + 1 ≤ N`, and `0` otherwise. -/
theorem integral_normSq_singleCellFermiCombinator_head_eq (k N : ℕ) :
    (∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
      ‖singleCellFermiCombinator (k + 1) N t‖ ^ 2) =
      if k + 1 ≤ N then 1 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) else 0 := by
  rw [setIntegral_Ioc_inv_succ_one_eq_sum_cells N
    (integrableOn_normSq_singleCellFermiCombinator (k + 1) N)]
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      (∫ t in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)),
        ‖singleCellFermiCombinator (k + 1) N t‖ ^ 2) =
      if n = k + 1 then 1 / ((n : ℝ) * ((n : ℝ) + 1)) else 0 := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hk1 : 0 < k + 1 := Nat.succ_pos k
    have hcongr : EqOn
        (fun t => ‖singleCellFermiCombinator (k + 1) N t‖ ^ 2)
        (fun _ => if n = k + 1 then (1 : ℝ) else 0)
        (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
      intro t ht
      dsimp only
      rw [singleCellFermiCombinator_eq_kronecker_on_cell hk1 hn1 hnN ht]
      split_ifs <;> simp
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
      setIntegral_const_on_reciprocal_cell hn1, smul_eq_mul]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_ite_eq', Finset.mem_Icc, Nat.le_add_left 1 k, true_and]

/-- **Exact Global-Minus-Cell Identity for the Origin-Tail Energy of `singleCellFermiCombinator`:**
For every `k N : ℕ`, the small-`t` origin-tail `L²` energy of `singleCellFermiCombinator (k + 1) N`
on `(0, 1 / (N + 1)]` equals its global `L²(0, 1]` energy minus its single-cell bulk energy. -/
theorem integral_normSq_singleCellFermiCombinator_tail_eq_global_sub_cell (k N : ℕ) :
    (∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
      ‖singleCellFermiCombinator (k + 1) N t‖ ^ 2) =
      (∫ t in Ioc (0 : ℝ) 1, ‖singleCellFermiCombinator (k + 1) N t‖ ^ 2) -
        (if k + 1 ≤ N then 1 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) else 0) := by
  have hc0 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  have hc1 : 1 / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hint := integrableOn_normSq_singleCellFermiCombinator (k + 1) N
  have hsplit :
      (∫ t in Ioc (0 : ℝ) 1, ‖singleCellFermiCombinator (k + 1) N t‖ ^ 2) =
      (∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
        ‖singleCellFermiCombinator (k + 1) N t‖ ^ 2) +
      (∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
        ‖singleCellFermiCombinator (k + 1) N t‖ ^ 2) := by
    rw [← Ioc_union_Ioc_eq_Ioc hc0 hc1,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hint.mono_set (Set.Ioc_subset_Ioc le_rfl hc1))
        (hint.mono_set (Set.Ioc_subset_Ioc hc0 le_rfl))]
  rw [hsplit, integral_normSq_singleCellFermiCombinator_head_eq]
  ring

/-- Specializing `integral_normSq_singleCellFermiCombinator_tail_eq_global_sub_cell` to the top
octave `k = 0` (`I₁ = (1/2, 1]`) at cutoff `N + 1 ≥ 1`: the small-`t` tail energy on
`(0, 1 / (N + 2)]` equals the global `L²(0, 1]` energy minus `1 / 2`. -/
theorem integral_normSq_topOctaveSingleCell_tail_eq_global_sub_half (N : ℕ) :
    (∫ t in Ioc (0 : ℝ) (1 / (((N + 1 : ℕ) : ℝ) + 1)),
      ‖singleCellFermiCombinator 1 (N + 1) t‖ ^ 2) =
      (∫ t in Ioc (0 : ℝ) 1, ‖singleCellFermiCombinator 1 (N + 1) t‖ ^ 2) - 1 / 2 := by
  have h := integral_normSq_singleCellFermiCombinator_tail_eq_global_sub_cell 0 (N + 1)
  simp only [Nat.zero_add, Nat.le_add_left 1 N, ↓reduceIte, Nat.cast_one] at h
  linarith

/-! ## §4. Báez–Duarte Least-Squares Quadratic Producer & Reciprocal Gram Bridge -/

/-- **Unconditional Báez–Duarte Discrete Quadratic Producer:**
For every cutoff `N : ℕ` and coefficient vector `c : {n // n ∈ Finset.range N} → ℝ`, the squared
Báez–Duarte distance `bdDistDiscrete N ^ 2` is bounded above by the explicit Gram quadratic form
`1 + 2 ∑ᵢ cᵢ θᵢ log θᵢ + ∑ᵢⱼ cᵢ cⱼ bdGram θᵢ θⱼ` at `θᵢ = 1 / (i + 1)`. -/
theorem bdDistDiscrete_sq_le_quadratic_producer (N : ℕ)
    (c : {n // n ∈ Finset.range N} → ℝ) :
    bdDistDiscrete N ^ (2 : ℕ) ≤
      1 + 2 * (∑ i, c i * (bdDiscrete i * Real.log (bdDiscrete i))) +
        ∑ i, ∑ j, c i * c j * bdGram (bdDiscrete i) (bdDiscrete j) :=
  bdDist_sq_le_quadratic
    (fun i : {n // n ∈ Finset.range N} => bdDiscrete i)
    (fun i => bdDiscrete_mem i.1) c

/-- **Báez–Duarte Reciprocal Gram Certificate Bridge to `RiemannHypothesis`:**
Existence of explicit finite `bdGram` quadratic certificates below `(1 / (k + 1))²` at every
threshold `k : ℕ` implies `RiemannHypothesis`. -/
theorem riemannHypothesis_of_bdDiscreteGramReciprocalCertificates_bridge
    (h : BdDiscreteGramReciprocalCertificates) : RiemannHypothesis :=
  riemannHypothesis_of_bdDiscreteGramReciprocalCertificates h

end GaloisForLFunctions.BiScaleUncertainty

end
