import GaloisForLFunctions.HTGeometry.WeierstrassGenusFactor
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The Weierstrass factorization theorem on `ℂ`

For any sequence of nonzero points tending to infinity there is an entire function vanishing
exactly there.  Taking the genus of the `n`-th elementary factor to be `n` makes the product
converge with no hypothesis beyond `‖a n‖ → ∞`: on a compact set all but finitely many factors have
argument in the half disc, where the genus estimate bounds the deviation from one by
`e·(1/2)^{n+1}`.

The uniform constant is available because the genus bound

`B_p = ∑_{k<p} (1/2)^{k+1}/(k+1)`

is at most `1` for every `p`.
-/

namespace GaloisForLFunctions

open Complex Filter Topology Set

noncomputable section

/-! ### A uniform genus constant -/

theorem weierstrassLogBound_le_one (p : ℕ) : weierstrassLogBound p ≤ 1 := by
  have hterm : ∀ k ∈ Finset.range p,
      (1 / 2 : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) ^ (k + 1) := by
    intro k _
    have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hpow : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (k + 1) := by positivity
    calc (1 / 2 : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)
        ≤ (1 / 2 : ℝ) ^ (k + 1) / 1 := by
          refine div_le_div_of_nonneg_left hpow one_pos hk
      _ = (1 / 2 : ℝ) ^ (k + 1) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hgeo : ∑ k ∈ Finset.range p, (1 / 2 : ℝ) ^ (k + 1)
      = (1 / 2 : ℝ) * ∑ k ∈ Finset.range p, (1 / 2 : ℝ) ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hgeo, geom_sum_eq (by norm_num)]
  have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ p := by positivity
  have hval : (1 / 2 : ℝ) * (((1 / 2 : ℝ) ^ p - 1) / (1 / 2 - 1)) = 1 - (1 / 2 : ℝ) ^ p := by
    field_simp
    ring
  rw [hval]
  linarith

theorem norm_weierstrassFactor_sub_one_le_uniform (p : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖weierstrassFactor p w - 1‖ ≤ Real.exp 1 * ‖w‖ ^ (p + 1) := by
  refine le_trans (norm_weierstrassFactor_sub_one_le p hw) ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact Real.exp_le_exp.mpr (weierstrassLogBound_le_one p)

/-! ### The product -/

/-- The Weierstrass product with increasing genus: the `n`-th factor has genus `n`. -/
def weierstrassGenusFactorAt (a : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  weierstrassFactor n (z / a n)

/-- The Weierstrass canonical product attached to a sequence of zeros. -/
def weierstrassGenusProduct (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassGenusFactorAt a n z

theorem differentiable_weierstrassGenusFactorAt {a : ℕ → ℂ} (_hane : ∀ n, a n ≠ 0) (n : ℕ) :
    Differentiable ℂ (weierstrassGenusFactorAt a n) :=
  (differentiable_weierstrassFactor n).comp (differentiable_id.div_const (a n))

/-- Beyond a finite set of indices the argument of the factor lies in the half disc. -/
theorem finite_setOf_norm_lt {a : ℕ → ℂ} (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (c : ℝ) :
    {n : ℕ | ‖a n‖ < c}.Finite := by
  have h : ∀ᶠ n in atTop, c < ‖a n‖ := ha.eventually_gt_atTop c
  have hcof : ∀ᶠ n in cofinite, c < ‖a n‖ := by
    rwa [Nat.cofinite_eq_atTop]
  rw [Filter.eventually_cofinite] at hcof
  exact hcof.subset fun n hn => by
    simp only [mem_setOf_eq] at hn ⊢
    exact not_lt.mpr hn.le

theorem norm_weierstrassGenusFactorAt_sub_one_le {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0)
    {n : ℕ} {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) (hn : 2 * R ≤ ‖a n‖) :
    ‖weierstrassGenusFactorAt a n z - 1‖ ≤ Real.exp 1 * (1 / 2 : ℝ) ^ (n + 1) := by
  have hapos : 0 < ‖a n‖ := norm_pos_iff.mpr (hane n)
  have hhalf : ‖z / a n‖ ≤ 1 / 2 := by
    rw [norm_div]
    rw [div_le_iff₀ hapos]
    linarith
  refine le_trans (norm_weierstrassFactor_sub_one_le_uniform n hhalf) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
  exact pow_le_pow_left₀ (norm_nonneg _) hhalf _

theorem summable_uniform_bound : Summable fun n : ℕ => Real.exp 1 * (1 / 2 : ℝ) ^ (n + 1) := by
  have hgeo : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine (hgeo.mul_left (Real.exp 1 * (1 / 2 : ℝ))).congr fun n => ?_
  ring

/-- **The Weierstrass product converges locally uniformly.** -/
theorem hasProdLocallyUniformlyOn_weierstrassGenusFactorAt {a : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (weierstrassGenusFactorAt a) (weierstrassGenusProduct a) univ := by
  classical
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨C, hC⟩ := hK.bddAbove_image (continuous_norm (E := ℂ)).continuousOn
  set R : ℝ := max C 0 with hR
  have hRnn : (0 : ℝ) ≤ R := le_max_right _ _
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R := fun z hz =>
    (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hbound : ∀ᶠ n : ℕ in cofinite, ∀ z ∈ K,
      ‖weierstrassGenusFactorAt a n z - 1‖ ≤ Real.exp 1 * (1 / 2 : ℝ) ^ (n + 1) := by
    rw [Filter.eventually_cofinite]
    refine (finite_setOf_norm_lt ha (2 * R)).subset fun n hn => ?_
    simp only [mem_setOf_eq] at hn ⊢
    by_contra hcon
    exact hn fun z hz =>
      norm_weierstrassGenusFactorAt_sub_one_le hane (hKR z hz) (not_lt.mp hcon)
  have hcont : ∀ n : ℕ, ContinuousOn (fun z => weierstrassGenusFactorAt a n z - 1) K := fun n =>
    ((differentiable_weierstrassGenusFactorAt hane n).continuous.sub continuous_const).continuousOn
  have hprod := Summable.hasProdUniformlyOn_one_add hK summable_uniform_bound hbound hcont
  have heq : (fun (n : ℕ) (z : ℂ) => 1 + (weierstrassGenusFactorAt a n z - 1))
      = weierstrassGenusFactorAt a := by
    funext n z; ring
  have heq2 : (fun z : ℂ => ∏' n : ℕ, (1 + (weierstrassGenusFactorAt a n z - 1)))
      = weierstrassGenusProduct a := by
    funext z
    rw [weierstrassGenusProduct]
    exact tprod_congr fun n => by ring
  rw [heq, heq2] at hprod
  exact hprod

/-- **The Weierstrass product is entire.** -/
theorem differentiable_weierstrassGenusProduct {a : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0) :
    Differentiable ℂ (weierstrassGenusProduct a) := by
  have ht : TendstoLocallyUniformlyOn
      (fun (S : Finset ℕ) (z : ℂ) => ∏ n ∈ S, weierstrassGenusFactorAt a n z)
      (weierstrassGenusProduct a) atTop univ :=
    hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
      (hasProdLocallyUniformlyOn_weierstrassGenusFactorAt ha hane)
  have hd : ∀ᶠ S : Finset ℕ in atTop,
      DifferentiableOn ℂ (fun z => ∏ n ∈ S, weierstrassGenusFactorAt a n z) univ := by
    filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun n _ =>
      (differentiable_weierstrassGenusFactorAt hane n).differentiableOn
  have := ht.differentiableOn hd isOpen_univ
  exact fun z => this.differentiableAt (by simp)

/-! ### The zero set -/

theorem weierstrassFactor_eq_zero_iff (p : ℕ) (w : ℂ) : weierstrassFactor p w = 0 ↔ w = 1 := by
  rw [weierstrassFactor, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h (Complex.exp_ne_zero _)
  · rintro rfl
    simp

theorem weierstrassGenusFactorAt_eq_zero_iff {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (n : ℕ) (z : ℂ) :
    weierstrassGenusFactorAt a n z = 0 ↔ z = a n := by
  rw [weierstrassGenusFactorAt, weierstrassFactor_eq_zero_iff, div_eq_one_iff_eq (hane n)]

theorem summable_norm_weierstrassGenusFactorAt_sub_one {a : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0) (z : ℂ) :
    Summable fun n : ℕ => ‖weierstrassGenusFactorAt a n z - 1‖ := by
  refine Summable.of_norm_bounded_eventually_nat summable_uniform_bound ?_
  filter_upwards [ha.eventually_ge_atTop (2 * ‖z‖)] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_weierstrassGenusFactorAt_sub_one_le hane le_rfl hn

theorem multipliable_weierstrassGenusFactorAt {a : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0) (z : ℂ) :
    Multipliable fun n : ℕ => weierstrassGenusFactorAt a n z := by
  have := multipliable_one_add_of_summable
    (f := fun n : ℕ => weierstrassGenusFactorAt a n z - 1)
    (summable_norm_weierstrassGenusFactorAt_sub_one ha hane z)
  refine this.congr fun n => ?_
  ring

/-- **The Weierstrass factorization theorem on `ℂ`.**  The canonical product with increasing genus
attached to a sequence of nonzero points tending to infinity is entire and vanishes exactly at those
points. -/
theorem weierstrassGenusProduct_eq_zero_iff {a : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0) (z : ℂ) :
    weierstrassGenusProduct a z = 0 ↔ ∃ n : ℕ, z = a n := by
  constructor
  · intro h
    by_contra hcon
    simp only [not_exists] at hcon
    have hne : ∀ n : ℕ, 1 + (weierstrassGenusFactorAt a n z - 1) ≠ 0 := by
      intro n
      have heq : (1 : ℂ) + (weierstrassGenusFactorAt a n z - 1)
          = weierstrassGenusFactorAt a n z := by ring
      rw [heq]
      intro hz
      exact hcon n ((weierstrassGenusFactorAt_eq_zero_iff hane n z).mp hz)
    have hprod : ∏' n : ℕ, (1 + (weierstrassGenusFactorAt a n z - 1)) ≠ 0 :=
      tprod_one_add_ne_zero_of_summable hne
        (summable_norm_weierstrassGenusFactorAt_sub_one ha hane z)
    apply hprod
    rw [← h, weierstrassGenusProduct]
    exact tprod_congr fun n => by ring
  · rintro ⟨n, hn⟩
    exact tprod_of_exists_eq_zero ⟨n, (weierstrassGenusFactorAt_eq_zero_iff hane n z).mpr hn⟩

end

end GaloisForLFunctions
