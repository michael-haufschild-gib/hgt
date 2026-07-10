import Mathlib
import GaloisForLFunctions.RHTower.WeierstrassFactor

/-!
# Genus-one Weierstrass canonical products are entire

Given a sequence `a : ℕ → ℂ` of nonzero points whose reciprocals are square-summable
(`∑ₙ ‖aₙ‖⁻² < ∞`), the *genus-one canonical product*

`canonicalProductE1 a z = ∏' n, E₁(z / aₙ)`,   `E₁(w) = (1 - w)·exp w`,

converges locally uniformly on `ℂ` to an entire function.

The mechanism is the standard Weierstrass convergence criterion driven through mathlib's
locally-uniform infinite-product machinery.  On a ball `B(0, S)` write each factor as
`E₁(z / aₙ) = 1 + (E₁(z / aₙ) - 1)`.  Square-summability forces `‖aₙ‖ → ∞`, so eventually
`‖aₙ‖ ≥ S`; for such `n` and `‖z‖ < S` one has `‖z / aₙ‖ ≤ 1`, and the sharp quadratic factor
estimate `‖E₁(w) - 1‖ ≤ ‖w‖²` gives `‖E₁(z / aₙ) - 1‖ ≤ ‖z‖²/‖aₙ‖² ≤ S²·‖aₙ‖⁻²`.  The
majorant `S²·‖aₙ‖⁻²` is summable in `n`, so `Summable.hasProdLocallyUniformlyOn_nat_one_add`
yields locally-uniform convergence of the partial products on `B(0, S)`.  Each partial product
is a finite product of entire functions, hence differentiable; a locally-uniform limit of
holomorphic functions is holomorphic (`TendstoLocallyUniformlyOn.differentiableOn`), so the
product is differentiable — hence analytic — on every ball, and therefore on all of `ℂ`.
-/

open Filter Topology Metric

namespace RHTower

/-- The genus-one Weierstrass canonical product `∏' n, E₁(z / aₙ)` attached to a sequence `a`
of prescribed zeros, with `E₁` the genus-one elementary factor `weierstrassE1`. -/
noncomputable def canonicalProductE1 (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n, weierstrassE1 (z / a n)

/-- The genus-one canonical product of a square-summable zero sequence is entire: if every `aₙ`
is nonzero and `∑ₙ ‖aₙ‖⁻² < ∞`, then `z ↦ ∏' n, E₁(z / aₙ)` is analytic on all of `ℂ`.

Convergence is obtained from the quadratic factor estimate `‖E₁(w) - 1‖ ≤ ‖w‖²` and mathlib's
locally-uniform product machinery: on each ball `B(0, S)` the tail factors are dominated by the
summable series `S²·‖aₙ‖⁻²`, so the partial products converge locally uniformly to the product,
which is therefore a locally-uniform limit of holomorphic functions and hence holomorphic. -/
theorem canonicalProductE1_analytic (a : ℕ → ℂ) (ha : ∀ n, a n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖a n‖ ^ 2)) :
    AnalyticOnNhd ℂ (canonicalProductE1 a) Set.univ := by
  -- Analyticity on an arbitrary ball `B(0, S)` with `S > 0`.
  have hball : ∀ S : ℝ, 0 < S →
      AnalyticOnNhd ℂ (canonicalProductE1 a) (Metric.ball 0 S) := by
    intro S hSpos
    -- The genus-one factor centred at `1`: `f n z = E₁(z / aₙ) - 1`.
    set f : ℕ → ℂ → ℂ := fun n z => weierstrassE1 (z / a n) - 1 with hf
    -- The dominating summable series `u n = S²·‖aₙ‖⁻²`.
    have hu : Summable (fun n => S ^ 2 * (1 / ‖a n‖ ^ 2)) := hsum.mul_left _
    -- Square-summability forces `‖aₙ‖ → ∞`, so eventually `S ≤ ‖aₙ‖`.
    have hev : ∀ᶠ n in atTop, S ≤ ‖a n‖ := by
      have htend : Tendsto (fun n => 1 / ‖a n‖ ^ 2) atTop (𝓝 0) := hsum.tendsto_atTop_zero
      have hlt : ∀ᶠ n in atTop, 1 / ‖a n‖ ^ 2 < 1 / S ^ 2 :=
        htend.eventually_lt_const (by positivity)
      filter_upwards [hlt] with n hn
      have hanpos : 0 < ‖a n‖ :=
        (norm_nonneg _).lt_of_ne (Ne.symm (norm_ne_zero_iff.mpr (ha n)))
      have hsq : S ^ 2 < ‖a n‖ ^ 2 := lt_of_one_div_lt_one_div (pow_pos hanpos 2) hn
      exact le_of_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq)
    -- The eventual local domination `‖f n z‖ ≤ S²·‖aₙ‖⁻²` on `B(0, S)`.
    have hbound : ∀ᶠ n in atTop, ∀ z ∈ Metric.ball (0 : ℂ) S,
        ‖f n z‖ ≤ S ^ 2 * (1 / ‖a n‖ ^ 2) := by
      filter_upwards [hev] with n hn z hz
      have hzS : ‖z‖ < S := mem_ball_zero_iff.mp hz
      have hanpos : 0 < ‖a n‖ := lt_of_lt_of_le hSpos hn
      have hzlt : ‖z‖ < ‖a n‖ := lt_of_lt_of_le hzS hn
      have hdiv : ‖z / a n‖ = ‖z‖ / ‖a n‖ := norm_div z (a n)
      have hle1 : ‖z / a n‖ ≤ 1 := by
        rw [hdiv]; exact le_of_lt ((div_lt_one hanpos).mpr hzlt)
      calc ‖f n z‖ = ‖weierstrassE1 (z / a n) - 1‖ := by simp only [hf]
        _ ≤ ‖z / a n‖ ^ 2 := weierstrassE1_sub_one_norm_le hle1
        _ = ‖z‖ ^ 2 * (1 / ‖a n‖ ^ 2) := by rw [hdiv, div_pow, div_eq_mul_one_div]
        _ ≤ S ^ 2 * (1 / ‖a n‖ ^ 2) :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg z) (le_of_lt hzS) 2) (by positivity)
    -- Each centred factor is continuous (entire, even) on the ball.
    have hcts : ∀ n, ContinuousOn (f n) (Metric.ball (0 : ℂ) S) := by
      intro n
      have : Continuous (f n) := by simp only [hf, weierstrassE1]; fun_prop
      exact this.continuousOn
    -- Locally-uniform convergence of the partial products on `B(0, S)`.
    have hpl := Summable.hasProdLocallyUniformlyOn_nat_one_add
      (K := Metric.ball (0 : ℂ) S) isOpen_ball hu hbound hcts
    have htlu := hpl.tendstoLocallyUniformlyOn_finsetRange
    -- Each partial product is a finite product of entire functions, hence differentiable.
    have hFdiff : ∀ᶠ N in atTop,
        DifferentiableOn ℂ (fun z => ∏ i ∈ Finset.range N, (1 + f i z))
          (Metric.ball (0 : ℂ) S) := by
      refine Eventually.of_forall (fun N => ?_)
      apply Differentiable.differentiableOn
      apply Differentiable.fun_finsetProd
      intro i _
      simp only [hf, weierstrassE1]
      fun_prop
    -- The limit (the infinite product) is holomorphic on the ball.
    have hlim : DifferentiableOn ℂ (fun z => ∏' i : ℕ, (1 + f i z))
        (Metric.ball (0 : ℂ) S) :=
      htlu.differentiableOn hFdiff isOpen_ball
    -- Identify the limit with the canonical product and conclude analyticity.
    have hEq : DifferentiableOn ℂ (canonicalProductE1 a) (Metric.ball (0 : ℂ) S) := by
      refine hlim.congr (fun z _ => ?_)
      simp only [canonicalProductE1, hf]
      exact tprod_congr (fun i => by ring)
    exact hEq.analyticOnNhd isOpen_ball
  -- Every point lies in some ball, so analyticity on all balls gives analyticity on `ℂ`.
  intro x _
  exact hball (‖x‖ + 1) (by positivity) x (by
    rw [mem_ball_zero_iff]; linarith [norm_nonneg x])

/-- The genus-one canonical product over an arbitrary index type.  This form is suited to a
divisor with multiplicity: the index can be the sigma type of support points and their finite
multiplicity copies, without choosing an enumeration of the support. -/
noncomputable def canonicalProductE1Indexed {ι : Type*} (a : ι → ℂ) (z : ℂ) : ℂ :=
  ∏' i, weierstrassE1 (z / a i)

/-- Square-summability of the reciprocal zero norms gives locally-uniform convergence of the
arbitrarily indexed genus-one product. -/
theorem canonicalProductE1Indexed_hasProdLocallyUniformlyOn {ι : Type*}
    (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ 2)) :
    HasProdLocallyUniformlyOn (fun i z => weierstrassE1 (z / a i))
      (canonicalProductE1Indexed a) Set.univ := by
  have hball : ∀ S : ℝ, 0 < S →
      HasProdLocallyUniformlyOn (fun i z => weierstrassE1 (z / a i))
        (canonicalProductE1Indexed a) (Metric.ball 0 S) := by
    intro S hSpos
    set f : ι → ℂ → ℂ := fun i z => weierstrassE1 (z / a i) - 1 with hf
    have hu : Summable (fun i => S ^ 2 * (1 / ‖a i‖ ^ 2)) := hsum.mul_left _
    have hev : ∀ᶠ i in cofinite, S ≤ ‖a i‖ := by
      have htend : Tendsto (fun i => 1 / ‖a i‖ ^ 2) cofinite (𝓝 0) :=
        hsum.tendsto_cofinite_zero
      have hlt : ∀ᶠ i in cofinite, 1 / ‖a i‖ ^ 2 < 1 / S ^ 2 :=
        htend.eventually_lt_const (by positivity)
      filter_upwards [hlt] with i hi
      have haipos : 0 < ‖a i‖ :=
        (norm_nonneg _).lt_of_ne (Ne.symm (norm_ne_zero_iff.mpr (ha i)))
      have hsq : S ^ 2 < ‖a i‖ ^ 2 := lt_of_one_div_lt_one_div (pow_pos haipos 2) hi
      exact le_of_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq)
    have hbound : ∀ᶠ i in cofinite, ∀ z ∈ Metric.ball (0 : ℂ) S,
        ‖f i z‖ ≤ S ^ 2 * (1 / ‖a i‖ ^ 2) := by
      filter_upwards [hev] with i hi z hz
      have hzS : ‖z‖ < S := mem_ball_zero_iff.mp hz
      have haipos : 0 < ‖a i‖ := lt_of_lt_of_le hSpos hi
      have hzlt : ‖z‖ < ‖a i‖ := lt_of_lt_of_le hzS hi
      have hdiv : ‖z / a i‖ = ‖z‖ / ‖a i‖ := norm_div z (a i)
      have hle1 : ‖z / a i‖ ≤ 1 := by
        rw [hdiv]
        exact le_of_lt ((div_lt_one haipos).mpr hzlt)
      calc
        ‖f i z‖ = ‖weierstrassE1 (z / a i) - 1‖ := by simp only [hf]
        _ ≤ ‖z / a i‖ ^ 2 := weierstrassE1_sub_one_norm_le hle1
        _ = ‖z‖ ^ 2 * (1 / ‖a i‖ ^ 2) := by rw [hdiv, div_pow, div_eq_mul_one_div]
        _ ≤ S ^ 2 * (1 / ‖a i‖ ^ 2) :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg z) (le_of_lt hzS) 2) (by positivity)
    have hcts : ∀ i, ContinuousOn (f i) (Metric.ball (0 : ℂ) S) := by
      intro i
      have : Continuous (f i) := by simp only [hf, weierstrassE1]; fun_prop
      exact this.continuousOn
    have hpl := Summable.hasProdLocallyUniformlyOn_one_add isOpen_ball hu hbound hcts
    convert hpl using 1
    · ext i z
      simp only [hf]
      ring
    · funext z
      exact tprod_congr (fun i => by simp only [hf]; ring)
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hKcompact
  obtain ⟨S, hSpos, hKS⟩ : ∃ S : ℝ, 0 < S ∧ K ⊆ Metric.ball (0 : ℂ) S :=
    hKcompact.isBounded.subset_ball_lt 0 0
  exact ((hball S hSpos).mono hKS).hasProdUniformlyOn_of_isCompact hKcompact

/-- An arbitrarily indexed genus-one product with square-summable reciprocal zero norms is
entire. -/
theorem canonicalProductE1Indexed_analytic {ι : Type*}
    (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ 2)) :
    AnalyticOnNhd ℂ (canonicalProductE1Indexed a) Set.univ := by
  have hpl := canonicalProductE1Indexed_hasProdLocallyUniformlyOn a ha hsum
  have hdiff : ∀ᶠ s : Finset ι in atTop,
      DifferentiableOn ℂ (fun z => ∏ i ∈ s, weierstrassE1 (z / a i)) Set.univ := by
    exact Eventually.of_forall fun s => (Differentiable.fun_finsetProd fun i _ => by
      simp only [weierstrassE1]
      fun_prop).differentiableOn
  exact (show TendstoLocallyUniformlyOn
      (fun s : Finset ι => fun z => ∏ i ∈ s, weierstrassE1 (z / a i))
      (canonicalProductE1Indexed a) atTop Set.univ from hpl).differentiableOn
        hdiff isOpen_univ |>.analyticOnNhd isOpen_univ

end RHTower
