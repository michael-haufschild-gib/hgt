import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Exponential

/-!
# Positive-definite Laplace sums detect the sign of the weight

Let `g` be continuous on `[0, ∞)` with `|g(t)| ≤ C e^{−βt}`, `β > 0`. If every sum
`∫_0^∞ g(t) |Σ_j w_j e^{−i x_j t}|² dt` (real `w_j`, real `x_j`) is nonnegative — i.e. the cosine
transform `u ↦ ∫_0^∞ g(t) cos(ut) dt` is positive definite — then `g ≥ 0` on `(0, ∞)`
(`nonneg_of_laplace_posDef`). This is the uniqueness half of Bochner's theorem for one-sided
cosine–Laplace transforms.

**Proof.** At `t₀` with `g(t₀) < 0` take the points `x_j = jh` (`j < N`) with weights
`cos(jht₀)` and `sin(jht₀)`. The two sums add up to `½ ∫ g (F_N(h(t − t₀)) + F_N(h(t + t₀)))`,
with the Fejér kernel `F_N(θ) = |Σ_{j<N} e^{−ijθ}|²` (`normSq_cos_add_normSq_sin`). The kernel is
`≥ N²/4` on `|θ| ≤ 1/N`, `≤ π²/a²` on `a ≤ |θ| ≤ π` and `≤ N²` everywhere. With `h = 1/k`,
`N = k³` the main lobe contributes `≤ −ε k⁴/2`, the rest of the first period `O(k²)` and the
recurrences `O(k⁶ e^{−πβk/2})`: the sum is negative for large `k`.
-/

open Complex Filter Topology MeasureTheory Set Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry.LaplaceWeights

/-- The Dirichlet sum `Σ_{j<N} e^{−ijθ}`. -/
def dirichletSum (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ j ∈ Finset.range N, Complex.exp (((-((j : ℝ) * θ) : ℝ) : ℂ) * I)

/-- The Fejér kernel `|Σ_{j<N} e^{−ijθ}|²` (unnormalized). -/
def fejerKernel (N : ℕ) (θ : ℝ) : ℝ := Complex.normSq (dirichletSum N θ)

theorem fejerKernel_nonneg (N : ℕ) (θ : ℝ) : 0 ≤ fejerKernel N θ := Complex.normSq_nonneg _

theorem continuous_fejerKernel (N : ℕ) : Continuous (fejerKernel N) := by
  unfold fejerKernel dirichletSum
  refine Complex.continuous_normSq.comp (continuous_finsetSum _ fun j _ => ?_)
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id).neg).mul continuous_const)

theorem fejerKernel_le_sq (N : ℕ) (θ : ℝ) : fejerKernel N θ ≤ (N : ℝ) ^ 2 := by
  have h : ‖dirichletSum N θ‖ ≤ N := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun j _ => Complex.norm_exp_ofReal_mul_I _]
    simp
  rw [fejerKernel, Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The geometric sum: `D_N(θ)(e^{−iθ} − 1) = e^{−iNθ} − 1`. -/
theorem dirichletSum_mul (N : ℕ) (θ : ℝ) :
    dirichletSum N θ * (Complex.exp (((-θ : ℝ) : ℂ) * I) - 1) =
      Complex.exp (((-((N : ℝ) * θ) : ℝ) : ℂ) * I) - 1 := by
  have hpow : ∀ j : ℕ, Complex.exp (((-((j : ℝ) * θ) : ℝ) : ℂ) * I) =
      Complex.exp (((-θ : ℝ) : ℂ) * I) ^ j := by
    intro j; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [dirichletSum, Finset.sum_congr rfl (fun j _ => hpow j), geom_sum_mul, ← hpow]

theorem normSq_exp_sub_one (θ : ℝ) :
    Complex.normSq (Complex.exp ((θ : ℂ) * I) - 1) = 4 * Real.sin (θ / 2) ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im, sub_zero]
  have hθ : θ = 2 * (θ / 2) := by ring
  rw [hθ, Real.cos_two_mul, Real.sin_two_mul, show 2 * (θ / 2) / 2 = θ / 2 by ring]
  have h := Real.sin_sq_add_cos_sq (θ / 2)
  linear_combination 4 * (Real.cos (θ / 2) ^ 2 - 1) * h

/-- `F_N(θ) sin²(θ/2) ≤ 1`. -/
theorem fejerKernel_mul_sin_sq_le (N : ℕ) (θ : ℝ) : fejerKernel N θ * Real.sin (θ / 2) ^ 2 ≤ 1 := by
  have h := congrArg Complex.normSq (dirichletSum_mul N θ)
  rw [Complex.normSq_mul, normSq_exp_sub_one, normSq_exp_sub_one] at h
  have hs : Real.sin (-θ / 2) ^ 2 = Real.sin (θ / 2) ^ 2 := by rw [neg_div, Real.sin_neg, neg_sq]
  rw [hs] at h
  have := Real.sin_sq_le_one (-((N : ℝ) * θ) / 2)
  rw [fejerKernel]
  nlinarith

/-- On the main lobe `|θ| N ≤ 1` the kernel is at least `N²/4`. -/
theorem sq_le_four_mul_fejerKernel {N : ℕ} {θ : ℝ} (hθ : |θ| * N ≤ 1) :
    (N : ℝ) ^ 2 ≤ 4 * fejerKernel N θ := by
  have hre : (N : ℝ) / 2 ≤ (dirichletSum N θ).re := by
    rw [dirichletSum, Complex.re_sum]
    have hterm : ∀ j ∈ Finset.range N,
        (1 : ℝ) / 2 ≤ (Complex.exp (((-((j : ℝ) * θ) : ℝ) : ℂ) * I)).re := by
      intro j hj
      rw [Complex.exp_ofReal_mul_I_re]
      have hjN : (j : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hj).le
      have habs : |(-((j : ℝ) * θ))| ≤ 1 := by
        rw [abs_neg, abs_mul, Nat.abs_cast]
        calc (j : ℝ) * |θ| ≤ N * |θ| := mul_le_mul_of_nonneg_right hjN (abs_nonneg _)
          _ ≤ 1 := by linarith
      have hc := Real.one_sub_sq_div_two_le_cos (x := -((j : ℝ) * θ))
      have hsq : (-((j : ℝ) * θ)) ^ 2 ≤ 1 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (-((j : ℝ) * θ))]
      linarith
    calc (N : ℝ) / 2 = ∑ _j ∈ Finset.range N, (1 : ℝ) / 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum hterm
  have h0 : (0 : ℝ) ≤ N / 2 := by positivity
  have := Complex.re_sq_le_normSq (dirichletSum N θ)
  rw [fejerKernel]
  nlinarith

/-- Off the main lobe, on `a ≤ |θ| ≤ π`, the kernel is at most `π²/a²` (Jordan's inequality). -/
theorem fejerKernel_le_of_le_abs {N : ℕ} {a θ : ℝ} (ha : 0 < a) (haθ : a ≤ |θ|)
    (hθπ : |θ| ≤ π) : fejerKernel N θ ≤ π ^ 2 / a ^ 2 := by
  have hjordan := Real.mul_le_sin (x := |θ| / 2) (by positivity) (by linarith)
  have hsq : Real.sin (θ / 2) ^ 2 = Real.sin (|θ| / 2) ^ 2 := by
    rcases le_total 0 θ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, neg_div, Real.sin_neg, neg_sq]
  have hlow : a / π ≤ Real.sin (|θ| / 2) := by
    calc a / π ≤ |θ| / π := div_le_div_of_nonneg_right haθ Real.pi_pos.le
      _ = 2 / π * (|θ| / 2) := by ring
      _ ≤ _ := hjordan
  have hs2 : (a / π) ^ 2 ≤ Real.sin (θ / 2) ^ 2 := by
    rw [hsq]; exact pow_le_pow_left₀ (by positivity) hlow 2
  have hk := fejerKernel_mul_sin_sq_le N θ
  have hK := fejerKernel_nonneg N θ
  rw [le_div_iff₀ (by positivity)]
  have hpi := Real.pi_pos
  have : a ^ 2 / π ^ 2 ≤ Real.sin (θ / 2) ^ 2 := by rw [← div_pow]; exact hs2
  have h3 : fejerKernel N θ * (a ^ 2 / π ^ 2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left this hK).trans hk
  have h4 : fejerKernel N θ * a ^ 2 = fejerKernel N θ * (a ^ 2 / π ^ 2) * π ^ 2 := by
    field_simp
  rw [h4]
  nlinarith [sq_nonneg π]

/-- **The cosine and sine weights add up to two Fejér kernels.** -/
theorem normSq_cos_add_normSq_sin (N : ℕ) (h s t : ℝ) :
    Complex.normSq (∑ j : Fin N, ((Real.cos ((j : ℕ) * h * s) : ℝ) : ℂ) *
        Complex.exp (-((((j : ℕ) * h * t : ℝ)) : ℂ) * I)) +
      Complex.normSq (∑ j : Fin N, ((Real.sin ((j : ℕ) * h * s) : ℝ) : ℂ) *
        Complex.exp (-((((j : ℕ) * h * t : ℝ)) : ℂ) * I)) =
      (fejerKernel N (h * (t - s)) + fejerKernel N (h * (t + s))) / 2 := by
  set α := dirichletSum N (h * (t - s))
  set β := dirichletSum N (h * (t + s))
  -- the two exponential factorizations of a Dirichlet term
  have e1 : ∀ j : ℕ, Complex.exp (((-((j : ℝ) * (h * (t - s))) : ℝ) : ℂ) * I) =
      Complex.exp (-(((j * h * t : ℝ)) : ℂ) * I) *
        Complex.exp ((((j : ℝ) * h * s : ℝ) : ℂ) * I) := by
    intro j; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : ∀ j : ℕ, Complex.exp (((-((j : ℝ) * (h * (t + s))) : ℝ) : ℂ) * I) =
      Complex.exp (-(((j * h * t : ℝ)) : ℂ) * I) *
        Complex.exp (-((((j : ℝ) * h * s : ℝ) : ℂ)) * I) := by
    intro j; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hc : (∑ j : Fin N, ((Real.cos ((j : ℕ) * h * s) : ℝ) : ℂ) *
        Complex.exp (-((((j : ℕ) * h * t : ℝ)) : ℂ) * I)) = (α + β) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ((Real.cos (j * h * s) : ℝ) : ℂ) *
      Complex.exp (-(((j * h * t : ℝ)) : ℂ) * I)) N]
    simp only [α, β, dirichletSum, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [e1, e2, Complex.ofReal_cos, ← Complex.cos_add_sin_I (((j : ℝ) * h * s : ℝ) : ℂ),
      ← Complex.cos_sub_sin_I (((j : ℝ) * h * s : ℝ) : ℂ)]
    ring
  have hs : (∑ j : Fin N, ((Real.sin ((j : ℕ) * h * s) : ℝ) : ℂ) *
        Complex.exp (-((((j : ℕ) * h * t : ℝ)) : ℂ) * I)) = (α - β) / (2 * I) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ((Real.sin (j * h * s) : ℝ) : ℂ) *
      Complex.exp (-(((j * h * t : ℝ)) : ℂ) * I)) N]
    rw [eq_div_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero), Finset.sum_mul]
    simp only [α, β, dirichletSum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [e1, e2, Complex.ofReal_sin, ← Complex.cos_add_sin_I (((j : ℝ) * h * s : ℝ) : ℂ),
      ← Complex.cos_sub_sin_I (((j : ℝ) * h * s : ℝ) : ℂ)]
    ring
  rw [hc, hs, Complex.normSq_div, Complex.normSq_div, Complex.normSq_add, Complex.normSq_sub]
  have h2 : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  have h2I : Complex.normSq (2 * I) = 4 := by
    rw [Complex.normSq_mul, Complex.normSq_I, h2, mul_one]
  rw [h2, h2I, fejerKernel, fejerKernel]
  ring

/-- The pair of Fejér kernels at `t − t₀` and `t + t₀`, at scale `1/k` and order `N = k³`. -/
def fejerPair (k : ℕ) (t₀ t : ℝ) : ℝ :=
  fejerKernel (k ^ 3) (1 / k * (t - t₀)) + fejerKernel (k ^ 3) (1 / k * (t + t₀))

/-- The comparison function: a negative main lobe, the first period and the recurrences. -/
def fejerMajorant (ε C β δ t₀ : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  -(ε * (k : ℝ) ^ 6 / 4) * (Icc (t₀ - 1 / (k : ℝ) ^ 2) (t₀ + 1 / (k : ℝ) ^ 2)).indicator
      (fun _ => (1 : ℝ)) t +
    C * Real.exp (-(β * t)) * (π ^ 2 * (k : ℝ) ^ 2 / δ ^ 2 + π ^ 2 * (k : ℝ) ^ 2 / t₀ ^ 2) +
    2 * (k : ℝ) ^ 6 * C * Real.exp (-(β * (π * k - t₀) / 2)) * Real.exp (-(β / 2 * t))

theorem fejerPair_nonneg (k : ℕ) (t₀ t : ℝ) : 0 ≤ fejerPair k t₀ t :=
  add_nonneg (fejerKernel_nonneg _ _) (fejerKernel_nonneg _ _)

theorem fejerPair_le (k : ℕ) (t₀ t : ℝ) : fejerPair k t₀ t ≤ 2 * (k : ℝ) ^ 6 := by
  have h1 := fejerKernel_le_sq (k ^ 3) (1 / k * (t - t₀))
  have h2 := fejerKernel_le_sq (k ^ 3) (1 / k * (t + t₀))
  push_cast at h1 h2
  rw [fejerPair]
  have : ((k : ℝ) ^ 3) ^ 2 = (k : ℝ) ^ 6 := by ring
  linarith

theorem continuous_fejerPair (k : ℕ) (t₀ : ℝ) : Continuous (fejerPair k t₀) :=
  ((continuous_fejerKernel _).comp (continuous_const.mul (continuous_id.sub continuous_const))).add
    ((continuous_fejerKernel _).comp (continuous_const.mul (continuous_id.add continuous_const)))

/-- **Pointwise comparison** `g K ≤ B` on `t > 0`. -/
theorem mul_fejerPair_le {g : ℝ → ℝ} {C β ε δ t₀ : ℝ} {k : ℕ}
    (hC : ∀ t, 0 ≤ t → |g t| ≤ C * Real.exp (-(β * t))) (hC0 : 0 ≤ C) (hβ : 0 < β)
    (hε0 : 0 < ε) (hδ0 : 0 < δ) (ht₀ : 0 < t₀) (hI : ∀ t, |t - t₀| ≤ δ → g t ≤ -ε)
    (hk1 : 1 ≤ (k : ℝ)) (hrδ : 1 / (k : ℝ) ^ 2 ≤ δ) {t : ℝ} (ht : 0 < t) :
    g t * fejerPair k t₀ t ≤ fejerMajorant ε C β δ t₀ k t := by
  have hkpos : (0 : ℝ) < k := by linarith
  have hh0 : (0 : ℝ) < 1 / k := by positivity
  have hgC := hC t ht.le
  have hKnn := fejerPair_nonneg k t₀ t
  set Q := π ^ 2 * (k : ℝ) ^ 2 / δ ^ 2 + π ^ 2 * (k : ℝ) ^ 2 / t₀ ^ 2 with hQ
  have hex1 : 0 ≤ C * Real.exp (-(β * t)) * Q := by positivity
  have hex2 : 0 ≤ 2 * (k : ℝ) ^ 6 * C * Real.exp (-(β * (π * k - t₀) / 2)) *
      Real.exp (-(β / 2 * t)) := by positivity
  by_cases hL : t ∈ Icc (t₀ - 1 / (k : ℝ) ^ 2) (t₀ + 1 / (k : ℝ) ^ 2)
  · -- the main lobe
    have hab : |t - t₀| ≤ 1 / (k : ℝ) ^ 2 := by
      rw [abs_le]; constructor <;> linarith [hL.1, hL.2]
    have hgI : g t ≤ -ε := hI t (hab.trans hrδ)
    have hlobe : ((k ^ 3 : ℕ) : ℝ) ^ 2 ≤ 4 * fejerKernel (k ^ 3) (1 / k * (t - t₀)) := by
      apply sq_le_four_mul_fejerKernel
      rw [abs_mul, abs_of_pos hh0]
      push_cast
      calc 1 / (k : ℝ) * |t - t₀| * (k : ℝ) ^ 3 = |t - t₀| * (k : ℝ) ^ 2 := by
            field_simp
        _ ≤ 1 / (k : ℝ) ^ 2 * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hab (by positivity)
        _ = 1 := by field_simp
    push_cast at hlobe
    have hK2 : (k : ℝ) ^ 6 / 4 ≤ fejerPair k t₀ t := by
      rw [fejerPair]
      have : ((k : ℝ) ^ 3) ^ 2 = (k : ℝ) ^ 6 := by ring
      linarith [fejerKernel_nonneg (k ^ 3) (1 / k * (t + t₀))]
    have h1 : g t * fejerPair k t₀ t ≤ -ε * fejerPair k t₀ t :=
      mul_le_mul_of_nonneg_right hgI hKnn
    have h2 : -ε * fejerPair k t₀ t ≤ -ε * ((k : ℝ) ^ 6 / 4) :=
      mul_le_mul_of_nonpos_left hK2 (by linarith)
    rw [fejerMajorant, Set.indicator_of_mem hL]
    linarith
  · rw [fejerMajorant, Set.indicator_of_notMem hL, mul_zero, zero_add]
    by_cases hIt : |t - t₀| ≤ δ
    · -- the rest of the neighbourhood, where `g < 0`
      have : g t * fejerPair k t₀ t ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith [hI t hIt]) hKnn
      linarith
    · rw [not_le] at hIt
      have hgK : g t * fejerPair k t₀ t ≤ C * Real.exp (-(β * t)) * fejerPair k t₀ t := by
        have habs : |g t * fejerPair k t₀ t| ≤ C * Real.exp (-(β * t)) * fejerPair k t₀ t := by
          rw [abs_mul, abs_of_nonneg hKnn]
          exact mul_le_mul_of_nonneg_right hgC hKnn
        exact (le_abs_self _).trans habs
      by_cases hT : t ≤ π * k - t₀
      · -- the first period
        have hπh : π / (1 / (k : ℝ)) = π * k := by field_simp
        have hk1' : fejerKernel (k ^ 3) (1 / k * (t - t₀)) ≤ π ^ 2 / (1 / k * δ) ^ 2 := by
          apply fejerKernel_le_of_le_abs (by positivity)
          · rw [abs_mul, abs_of_pos hh0]; exact mul_le_mul_of_nonneg_left hIt.le hh0.le
          · rw [abs_mul, abs_of_pos hh0]
            have hab : |t - t₀| ≤ π * k := abs_le.mpr ⟨by linarith, by linarith⟩
            calc 1 / (k : ℝ) * |t - t₀| ≤ 1 / k * (π * k) := mul_le_mul_of_nonneg_left hab hh0.le
              _ = π := by field_simp
        have hk2' : fejerKernel (k ^ 3) (1 / k * (t + t₀)) ≤ π ^ 2 / (1 / k * t₀) ^ 2 := by
          apply fejerKernel_le_of_le_abs (by positivity)
          · rw [abs_of_pos (by positivity)]
            exact mul_le_mul_of_nonneg_left (by linarith) hh0.le
          · rw [abs_of_pos (by positivity)]
            calc 1 / (k : ℝ) * (t + t₀) ≤ 1 / k * (π * k) :=
                  mul_le_mul_of_nonneg_left (by linarith) hh0.le
              _ = π := by field_simp
        have hKQ : fejerPair k t₀ t ≤ Q := by
          have e1 : π ^ 2 / (1 / (k : ℝ) * δ) ^ 2 = π ^ 2 * (k : ℝ) ^ 2 / δ ^ 2 := by field_simp
          have e2 : π ^ 2 / (1 / (k : ℝ) * t₀) ^ 2 = π ^ 2 * (k : ℝ) ^ 2 / t₀ ^ 2 := by field_simp
          rw [fejerPair, hQ]
          linarith
        have := mul_le_mul_of_nonneg_left hKQ (by positivity : (0 : ℝ) ≤ C * Real.exp (-(β * t)))
        linarith
      · -- the recurrences
        rw [not_le] at hT
        have hexp : Real.exp (-(β * t)) ≤
            Real.exp (-(β * (π * k - t₀) / 2)) * Real.exp (-(β / 2 * t)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_left hT.le (by linarith : (0 : ℝ) ≤ β / 2)
          linarith
        have h1 : C * Real.exp (-(β * t)) * fejerPair k t₀ t ≤
            C * (Real.exp (-(β * (π * k - t₀) / 2)) * Real.exp (-(β / 2 * t))) *
              (2 * (k : ℝ) ^ 6) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp hC0) (fejerPair_le k t₀ t) hKnn
            (by positivity)
        linarith

theorem integrableOn_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t => Real.exp (-(c * t))) (Ioi 0) := by
  have := integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0
  simpa [neg_mul] using this

theorem integral_exp_neg_mul_Ioi {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(c * t)) = 1 / c := by
  have := integral_exp_mul_Ioi (a := -c) (by linarith) 0
  simp only [neg_mul, mul_zero, Real.exp_zero] at this ⊢
  rw [this]; field_simp

theorem integrableOn_lobe (a b : ℝ) :
    IntegrableOn ((Icc a b).indicator (fun _ => (1 : ℝ))) (Ioi 0) :=
  ((integrableOn_const (s := Icc a b) (μ := volume) (C := (1 : ℝ))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
    measurableSet_Icc).integrableOn

/-- **The comparison integral.** -/
theorem integral_fejerMajorant {ε C β δ t₀ : ℝ} {k : ℕ} (hβ : 0 < β) (hk1 : 1 ≤ (k : ℝ))
    (hlobe : 0 < t₀ - 1 / (k : ℝ) ^ 2) :
    ∫ t in Ioi (0 : ℝ), fejerMajorant ε C β δ t₀ k t =
      -(ε * (k : ℝ) ^ 4 / 2) + C / β * π ^ 2 * (1 / δ ^ 2 + 1 / t₀ ^ 2) * (k : ℝ) ^ 2 +
        4 * C / β * Real.exp (β * t₀ / 2) * (k : ℝ) ^ 6 * Real.exp (-(β * π * k / 2)) := by
  have hkpos : (0 : ℝ) < k := by linarith
  set a := t₀ - 1 / (k : ℝ) ^ 2
  set b := t₀ + 1 / (k : ℝ) ^ 2
  have hsub : Icc a b ⊆ Ioi 0 := fun t ht => by have := ht.1; show 0 < t; linarith
  have hi1 : ∫ t in Ioi (0 : ℝ), (Icc a b).indicator (fun _ => (1 : ℝ)) t = 2 / (k : ℝ) ^ 2 := by
    rw [integral_indicator_const _ measurableSet_Icc, Measure.real_def,
      Measure.restrict_apply measurableSet_Icc, Set.inter_eq_left.mpr hsub, Real.volume_Icc,
      smul_eq_mul, mul_one, ENNReal.toReal_ofReal (by
        simp only [a, b]; have : (0 : ℝ) < 1 / (k : ℝ) ^ 2 := by positivity
        linarith)]
    simp only [a, b]; ring
  have I1 : IntegrableOn (fun t => -(ε * (k : ℝ) ^ 6 / 4) *
      (Icc a b).indicator (fun _ => (1 : ℝ)) t) (Ioi 0) := (integrableOn_lobe a b).const_mul _
  have I2 : IntegrableOn (fun t => C * (π ^ 2 * (k : ℝ) ^ 2 / δ ^ 2 + π ^ 2 * (k : ℝ) ^ 2 / t₀ ^ 2) *
      Real.exp (-(β * t))) (Ioi 0) := (integrableOn_exp_neg_mul hβ).const_mul _
  have I12 : IntegrableOn (fun t => -(ε * (k : ℝ) ^ 6 / 4) *
      (Icc a b).indicator (fun _ => (1 : ℝ)) t +
      C * (π ^ 2 * (k : ℝ) ^ 2 / δ ^ 2 + π ^ 2 * (k : ℝ) ^ 2 / t₀ ^ 2) *
        Real.exp (-(β * t))) (Ioi 0) := I1.add I2
  have I3 : IntegrableOn (fun t => 2 * (k : ℝ) ^ 6 * C * Real.exp (-(β * (π * k - t₀) / 2)) *
      Real.exp (-(β / 2 * t))) (Ioi 0) :=
    (integrableOn_exp_neg_mul (by positivity : 0 < β / 2)).const_mul _
  have hsplit : ∫ t in Ioi (0 : ℝ), fejerMajorant ε C β δ t₀ k t =
      -(ε * (k : ℝ) ^ 6 / 4) * (∫ t in Ioi (0 : ℝ), (Icc a b).indicator (fun _ => (1 : ℝ)) t) +
        C * (π ^ 2 * (k : ℝ) ^ 2 / δ ^ 2 + π ^ 2 * (k : ℝ) ^ 2 / t₀ ^ 2) *
          (∫ t in Ioi (0 : ℝ), Real.exp (-(β * t))) +
        2 * (k : ℝ) ^ 6 * C * Real.exp (-(β * (π * k - t₀) / 2)) *
          (∫ t in Ioi (0 : ℝ), Real.exp (-(β / 2 * t))) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun t => (show fejerMajorant ε C β δ t₀ k t =
        -(ε * (k : ℝ) ^ 6 / 4) * (Icc a b).indicator (fun _ => (1 : ℝ)) t +
          C * (π ^ 2 * (k : ℝ) ^ 2 / δ ^ 2 + π ^ 2 * (k : ℝ) ^ 2 / t₀ ^ 2) *
            Real.exp (-(β * t)) +
          2 * (k : ℝ) ^ 6 * C * Real.exp (-(β * (π * k - t₀) / 2)) *
            Real.exp (-(β / 2 * t)) by simp only [fejerMajorant, a, b]; ring)),
      integral_add I12 I3, integral_add I1 I2, integral_const_mul, integral_const_mul,
      integral_const_mul]
  rw [hsplit, hi1, integral_exp_neg_mul_Ioi hβ, integral_exp_neg_mul_Ioi (by positivity : 0 < β / 2)]
  have hexp : Real.exp (-(β * (π * k - t₀) / 2)) =
      Real.exp (β * t₀ / 2) * Real.exp (-(β * π * k / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  field_simp
  ring

/-- **The Fejér sums are nonnegative.** -/
theorem integral_mul_fejerPair_nonneg {g : ℝ → ℝ} (hg : Continuous g) {C β : ℝ} (hβ : 0 < β)
    (hC : ∀ t, 0 ≤ t → |g t| ≤ C * Real.exp (-(β * t)))
    (hpd : ∀ (n : ℕ) (x w : Fin n → ℝ), 0 ≤ ∫ t in Ioi (0 : ℝ),
      g t * Complex.normSq (∑ i, (w i : ℂ) * Complex.exp (-((x i * t : ℝ) : ℂ) * I)))
    (k : ℕ) (t₀ : ℝ) : 0 ≤ ∫ t in Ioi (0 : ℝ), g t * fejerPair k t₀ t := by
  set N := k ^ 3
  set h : ℝ := 1 / k
  set x : Fin N → ℝ := fun j => (j : ℕ) * h
  set Ac : ℝ → ℝ := fun t => Complex.normSq (∑ i : Fin N, ((Real.cos ((i : ℕ) * h * t₀) : ℝ) : ℂ) *
    Complex.exp (-((x i * t : ℝ) : ℂ) * I))
  set As : ℝ → ℝ := fun t => Complex.normSq (∑ i : Fin N, ((Real.sin ((i : ℕ) * h * t₀) : ℝ) : ℂ) *
    Complex.exp (-((x i * t : ℝ) : ℂ) * I))
  have hbd : ∀ t, Ac t + As t = fejerPair k t₀ t / 2 := fun t =>
    normSq_cos_add_normSq_sin N h t₀ t
  have hc : 0 ≤ ∫ t in Ioi (0 : ℝ), g t * Ac t := hpd N x (fun j => Real.cos ((j : ℕ) * h * t₀))
  have hs : 0 ≤ ∫ t in Ioi (0 : ℝ), g t * As t := hpd N x (fun j => Real.sin ((j : ℕ) * h * t₀))
  have hcont : ∀ w : Fin N → ℝ, Continuous fun t => Complex.normSq (∑ i, (w i : ℂ) *
      Complex.exp (-((x i * t : ℝ) : ℂ) * I)) := fun w =>
    Complex.continuous_normSq.comp (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (Complex.continuous_exp.comp (((Complex.continuous_ofReal.comp
        (continuous_const.mul continuous_id)).neg).mul continuous_const)))
  have hint : ∀ F : ℝ → ℝ, Continuous F → (∀ t, 0 ≤ F t ∧ F t ≤ 2 * (k : ℝ) ^ 6) →
      IntegrableOn (fun t => g t * F t) (Ioi 0) := by
    intro F hF hFb
    refine Integrable.mono' ((integrableOn_exp_neg_mul hβ).const_mul (C * (2 * (k : ℝ) ^ 6)))
      (hg.mul hF).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hFb t).1]
    calc |g t| * F t ≤ C * Real.exp (-(β * t)) * (2 * (k : ℝ) ^ 6) :=
          mul_le_mul (hC t (le_of_lt ht)) (hFb t).2 (hFb t).1 (by
            have := (abs_nonneg _).trans (hC t (le_of_lt ht)); exact this)
      _ = C * (2 * (k : ℝ) ^ 6) * Real.exp (-(β * t)) := by ring
  have hAc : IntegrableOn (fun t => g t * Ac t) (Ioi 0) := hint Ac (hcont _) fun t =>
    ⟨Complex.normSq_nonneg _, by
      have := hbd t; have := Complex.normSq_nonneg (∑ i : Fin N, ((Real.sin ((i : ℕ) * h * t₀) : ℝ) : ℂ) *
        Complex.exp (-((x i * t : ℝ) : ℂ) * I))
      have := fejerPair_le k t₀ t; have := fejerPair_nonneg k t₀ t
      simp only [Ac, As] at *; linarith⟩
  have hAs : IntegrableOn (fun t => g t * As t) (Ioi 0) := hint As (hcont _) fun t =>
    ⟨Complex.normSq_nonneg _, by
      have := hbd t; have := Complex.normSq_nonneg (∑ i : Fin N, ((Real.cos ((i : ℕ) * h * t₀) : ℝ) : ℂ) *
        Complex.exp (-((x i * t : ℝ) : ℂ) * I))
      have := fejerPair_le k t₀ t; have := fejerPair_nonneg k t₀ t
      simp only [Ac, As] at *; linarith⟩
  have hid : (fun t => g t * fejerPair k t₀ t) = fun t => 2 * (g t * Ac t) + 2 * (g t * As t) := by
    funext t; rw [← mul_add, ← mul_add, hbd t]; ring
  rw [hid, integral_add (hAc.const_mul 2) (hAs.const_mul 2), integral_const_mul, integral_const_mul]
  linarith

/-- **A positive-definite cosine–Laplace transform has a nonnegative weight.** -/
theorem nonneg_of_laplace_posDef {g : ℝ → ℝ} (hg : Continuous g) {C β : ℝ} (hβ : 0 < β)
    (hC : ∀ t, 0 ≤ t → |g t| ≤ C * Real.exp (-(β * t)))
    (hpd : ∀ (n : ℕ) (x w : Fin n → ℝ), 0 ≤ ∫ t in Ioi (0 : ℝ),
      g t * Complex.normSq (∑ i, (w i : ℂ) * Complex.exp (-((x i * t : ℝ) : ℂ) * I)))
    {t₀ : ℝ} (ht₀ : 0 < t₀) : 0 ≤ g t₀ := by
  by_contra hneg
  rw [not_le] at hneg
  set ε := -g t₀ / 2 with hεdef
  have hε0 : 0 < ε := by linarith
  have hC0 : 0 ≤ C := by simpa using (abs_nonneg _).trans (hC 0 le_rfl)
  -- a closed neighbourhood of `t₀` where `g ≤ −ε`
  obtain ⟨δ₀, hδ₀, hδ₀g⟩ : ∃ δ₀ > 0, ∀ t, dist t t₀ < δ₀ → g t < -ε :=
    Metric.eventually_nhds_iff.mp
      ((hg.continuousAt (x := t₀)).eventually (gt_mem_nhds (show g t₀ < -ε by linarith)))
  set δ := min (δ₀ / 2) (t₀ / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδt : δ ≤ t₀ / 2 := min_le_right _ _
  have hI : ∀ t, |t - t₀| ≤ δ → g t ≤ -ε := fun t ht =>
    (hδ₀g t (by rw [Real.dist_eq]; linarith [min_le_left (δ₀ / 2) (t₀ / 2)])).le
  -- the scale `k`
  set A := C / β * π ^ 2 * (1 / δ ^ 2 + 1 / t₀ ^ 2) with hAdef
  set D := 4 * C / β * Real.exp (β * t₀ / 2) * ((Nat.factorial 7 : ℝ) / (β * π / 2) ^ 7)
    with hDdef
  have hA0 : 0 ≤ A := by positivity
  have hD0 : 0 ≤ D := by positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (4 * A / ε + 4 * D / ε + 1 / δ + t₀ / π + 1)
  have hk1 : (1 : ℝ) ≤ k := by
    have : 0 ≤ 4 * A / ε + 4 * D / ε + 1 / δ + t₀ / π := by positivity
    linarith
  have hkpos : (0 : ℝ) < k := by linarith
  have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := le_self_pow₀ hk1 (by norm_num)
  have hk4 : (k : ℝ) ≤ (k : ℝ) ^ 4 := le_self_pow₀ hk1 (by norm_num)
  have hrδ : 1 / (k : ℝ) ^ 2 ≤ δ := by
    have hkδ : 1 / δ < k := by
      have : 0 ≤ 4 * A / ε + 4 * D / ε + t₀ / π := by positivity
      linarith
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 < δ * k := by rwa [div_lt_iff₀ hδ0, mul_comm] at hkδ
    calc (1 : ℝ) ≤ δ * k := h1.le
      _ ≤ δ * k ^ 2 := mul_le_mul_of_nonneg_left hk2 hδ0.le
  have hkt : t₀ ≤ π * k := by
    have : t₀ / π < k := by
      have : 0 ≤ 4 * A / ε + 4 * D / ε + 1 / δ := by positivity
      linarith
    rw [div_lt_iff₀ Real.pi_pos] at this
    linarith
  -- the Fejér sums against the comparison function
  have hlower := integral_mul_fejerPair_nonneg hg hβ hC hpd k t₀
  have hgKint : IntegrableOn (fun t => g t * fejerPair k t₀ t) (Ioi 0) := by
    refine Integrable.mono' ((integrableOn_exp_neg_mul hβ).const_mul (C * (2 * (k : ℝ) ^ 6)))
      (hg.mul (continuous_fejerPair k t₀)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fejerPair_nonneg k t₀ t)]
    calc |g t| * fejerPair k t₀ t ≤ C * Real.exp (-(β * t)) * (2 * (k : ℝ) ^ 6) :=
          mul_le_mul (hC t (le_of_lt ht)) (fejerPair_le k t₀ t) (fejerPair_nonneg k t₀ t)
            (by positivity)
      _ = C * (2 * (k : ℝ) ^ 6) * Real.exp (-(β * t)) := by ring
  have hBint : IntegrableOn (fejerMajorant ε C β δ t₀ k) (Ioi 0) := by
    have hfun : fejerMajorant ε C β δ t₀ k = fun t =>
        (-(ε * (k : ℝ) ^ 6 / 4) *
            (Icc (t₀ - 1 / (k : ℝ) ^ 2) (t₀ + 1 / (k : ℝ) ^ 2)).indicator (fun _ => (1 : ℝ)) t +
          C * (π ^ 2 * (k : ℝ) ^ 2 / δ ^ 2 + π ^ 2 * (k : ℝ) ^ 2 / t₀ ^ 2) *
            Real.exp (-(β * t))) +
          2 * (k : ℝ) ^ 6 * C * Real.exp (-(β * (π * k - t₀) / 2)) * Real.exp (-(β / 2 * t)) := by
      funext t; simp only [fejerMajorant]; ring
    rw [hfun]
    exact (((integrableOn_lobe _ _).const_mul _).add ((integrableOn_exp_neg_mul hβ).const_mul _)).add
      ((integrableOn_exp_neg_mul (by positivity : 0 < β / 2)).const_mul _)
  have hupper := setIntegral_mono_on hgKint hBint measurableSet_Ioi fun t ht =>
    mul_fejerPair_le hC hC0 hβ hε0 hδ0 ht₀ hI hk1 hrδ ht
  have hlobe : 0 < t₀ - 1 / (k : ℝ) ^ 2 := by linarith
  rw [integral_fejerMajorant hβ hk1 hlobe] at hupper
  -- the comparison integral is negative
  have htail : 4 * C / β * Real.exp (β * t₀ / 2) * (k : ℝ) ^ 6 * Real.exp (-(β * π * k / 2)) ≤
      D := by
    have hx : 0 ≤ β * π * k / 2 := by positivity
    have hexpk : Real.exp (-(β * π * k / 2)) ≤
        (Nat.factorial 7 : ℝ) / ((β * π / 2) ^ 7 * (k : ℝ) ^ 7) := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
      have hfac := Real.pow_div_factorial_le_exp _ hx 7
      have : (β * π * k / 2) ^ 7 = (β * π / 2) ^ 7 * (k : ℝ) ^ 7 := by ring
      rwa [this] at hfac
    have hpos : 0 ≤ 4 * C / β * Real.exp (β * t₀ / 2) * (k : ℝ) ^ 6 := by positivity
    calc 4 * C / β * Real.exp (β * t₀ / 2) * (k : ℝ) ^ 6 * Real.exp (-(β * π * k / 2))
        ≤ 4 * C / β * Real.exp (β * t₀ / 2) * (k : ℝ) ^ 6 *
            ((Nat.factorial 7 : ℝ) / ((β * π / 2) ^ 7 * (k : ℝ) ^ 7)) :=
          mul_le_mul_of_nonneg_left hexpk hpos
      _ = D / k := by
          have hπ : π ≠ 0 := Real.pi_ne_zero
          have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
          have hβ0 : β ≠ 0 := hβ.ne'
          rw [hDdef]; field_simp
      _ ≤ D := div_le_self hD0 hk1
  have e1 : A * (k : ℝ) ^ 2 < ε * (k : ℝ) ^ 4 / 4 := by
    have hkA : 4 * A / ε < k := by
      have : 0 ≤ 4 * D / ε + 1 / δ + t₀ / π := by positivity
      linarith
    have h1 : 4 * A < ε * k := by have := (div_lt_iff₀ hε0).mp hkA; linarith
    have h2 : ε * k ≤ ε * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hk2 hε0.le
    have h3 := mul_lt_mul_of_pos_right (h1.trans_le h2) (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)
    have h4 : ε * (k : ℝ) ^ 2 * (k : ℝ) ^ 2 = ε * (k : ℝ) ^ 4 := by ring
    linarith
  have e2 : D < ε * (k : ℝ) ^ 4 / 4 := by
    have hkD : 4 * D / ε < k := by
      have : 0 ≤ 4 * A / ε + 1 / δ + t₀ / π := by positivity
      linarith
    have h1 : 4 * D < ε * k := by have := (div_lt_iff₀ hε0).mp hkD; linarith
    have h2 : ε * k ≤ ε * (k : ℝ) ^ 4 := mul_le_mul_of_nonneg_left hk4 hε0.le
    linarith
  have hAk : C / β * π ^ 2 * (1 / δ ^ 2 + 1 / t₀ ^ 2) * (k : ℝ) ^ 2 = A * (k : ℝ) ^ 2 := by
    rw [hAdef]
  linarith

end GaloisForLFunctions.HTGeometry.LaplaceWeights
