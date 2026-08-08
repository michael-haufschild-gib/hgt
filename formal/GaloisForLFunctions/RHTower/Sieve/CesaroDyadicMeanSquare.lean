import GaloisForLFunctions.RHTower.Sieve.CesaroWeightedL1
import GaloisForLFunctions.HTGeometry.VerticalKernelBlockConstants

/-!
# The Cesàro analytic side is height-free

Cauchy–Schwarz against the kernel still pays the mean square of the whole range, so its bound grows
like `√(Q + κT)`.  The dyadic split pays the mean square once per block against a kernel constant that
*decays* with the block, and for the second-order kernel

`x^σ/‖σ+it‖² ≤ (x^σ/(σ2^m))/|t|`   on `σ2^m ≤ |t| ≤ σ2^{m+1}`,

so the block constants are geometric with ratio `1/2`.  Both geometric sums converge, and the height
disappears entirely:

`∫_{|t| ≤ T} ‖L(g,σ+it)·x^s/s²‖ dt ≤ 8x^σ√Q + 12x^σ√κ`   for every `T`,

with `Q` the constant and `κ` the rate of the affine mean square.  For `|f| ≤ 1` truncated at `N` this
is `≍ x^σ√(log N)` uniformly in the height, where the unweighted first moment gives `≍ x^σ√(T + log N)`
and the pointwise route `≍ x^σ log N`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- `√2 ≤ 3/2`. -/
theorem sqrt_two_le_three_halves : Real.sqrt 2 ≤ 3 / 2 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [Real.sqrt_nonneg 2]

/-- **The block sums of the second-order kernel.**  Ratio `1/2` in both terms. -/
theorem sum_range_block_kernel_le {A B x σ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hσ : 1 ≤ σ)
    (hx : 0 ≤ x ^ σ) (M : ℕ) :
    ∑ m ∈ Finset.range M, (x ^ σ / (σ * 2 ^ m)) * (A * (Real.sqrt 2 / 2) ^ m + B)
      ≤ 2 * (x ^ σ * A / σ) + 2 * (x ^ σ * B / σ) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hs2 : Real.sqrt 2 / 4 ≤ 1 / 2 := by
    have := sqrt_two_le_three_halves
    linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 / 4 := by positivity
  have hterm : ∀ m : ℕ, (x ^ σ / (σ * 2 ^ m)) * (A * (Real.sqrt 2 / 2) ^ m + B)
      = (x ^ σ * A / σ) * (Real.sqrt 2 / 4) ^ m + (x ^ σ * B / σ) * (1 / 2 : ℝ) ^ m := by
    intro m
    have h2m : ((2 : ℝ) ^ m) ≠ 0 := by positivity
    have hq : (Real.sqrt 2 / 4 : ℝ) ^ m = (Real.sqrt 2 / 2) ^ m / (2 : ℝ) ^ m := by
      rw [eq_div_iff h2m, ← mul_pow]
      congr 1
      ring
    have hh : ((1 : ℝ) / 2) ^ m = 1 / (2 : ℝ) ^ m := by
      rw [div_pow, one_pow]
    rw [hq, hh]
    field_simp
  rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have hgeo1 : ∑ m ∈ Finset.range M, (Real.sqrt 2 / 4 : ℝ) ^ m ≤ 2 := by
    refine le_trans (Finset.sum_le_sum fun m _ => pow_le_pow_left₀ hs0 hs2 m) ?_
    exact sum_geometric_two_le M
  have hgeo2 : ∑ m ∈ Finset.range M, (1 / 2 : ℝ) ^ m ≤ 2 := sum_geometric_two_le M
  have hA0 : (0 : ℝ) ≤ x ^ σ * A / σ := by positivity
  have hB0 : (0 : ℝ) ≤ x ^ σ * B / σ := by positivity
  have h1 := mul_le_mul_of_nonneg_left hgeo1 hA0
  have h2 := mul_le_mul_of_nonneg_left hgeo2 hB0
  linarith

/-- **The first moment against the second-order kernel, uniformly in the height.**  The dyadic split
with a block constant that decays: any object with an affine mean square on the ranges beyond the base
scale `σ` obeys the same bound, with no dependence on `T` at all. -/
theorem integral_symm_norm_mul_cesaroKernel_le_of_meanSquare {D : ℝ → ℂ} (hDc : Continuous D)
    {Q κ σ x T : ℝ} (hQ0 : 0 ≤ Q) (hκ0 : 0 ≤ κ) (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hx : 0 < x)
    (hT : 0 ≤ T)
    (hms : ∀ U : ℝ, σ ≤ U → (∫ t in Set.Icc (-U) U, ‖D t‖ ^ 2) ≤ Q + κ * U) :
    (∫ t in (-T)..T, ‖D t‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2))
      ≤ 8 * x ^ σ * Real.sqrt Q + 12 * x ^ σ * Real.sqrt κ := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hxσ : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hx σ
  set G : ℝ → ℝ := fun t => x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 with hG
  have hGc : Continuous G := by
    have hKeq : G = fun t : ℝ => x ^ σ * (1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2) := by
      funext t
      rw [hG, mul_one_div]
    rw [hKeq]
    exact continuous_const.mul (continuous_inv_normSq_line hσ0)
  have hGnn : ∀ t : ℝ, 0 ≤ G t := fun t => by
    rw [hG]
    exact div_nonneg hxσ.le (by positivity)
  -- the kernel below the base scale
  have hσle : ∀ t : ℝ, σ ≤ ‖(σ : ℂ) + (t : ℝ) * I‖ := by
    intro t
    have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
    have h := Complex.abs_re_le_norm ((σ : ℂ) + (t : ℝ) * I)
    rw [hre, abs_of_pos hσ0] at h
    exact h
  have hGlow : ∀ t : ℝ, |t| ≤ σ → G t ≤ x ^ σ / σ ^ 2 := by
    intro t _
    rw [hG]
    refine div_le_div_of_nonneg_left hxσ.le (by positivity) ?_
    exact pow_le_pow_left₀ hσ0.le (hσle t) 2
  -- the kernel on the blocks
  have habsle : ∀ t : ℝ, |t| ≤ ‖(σ : ℂ) + (t : ℝ) * I‖ := by
    intro t
    have him : ((σ : ℂ) + (t : ℝ) * I).im = t := by simp
    have h := Complex.abs_im_le_norm ((σ : ℂ) + (t : ℝ) * I)
    rwa [him] at h
  have hGblock : ∀ m : ℕ, ∀ t : ℝ, σ * 2 ^ m ≤ |t| → |t| ≤ σ * 2 ^ (m + 1) →
      G t ≤ (x ^ σ / (σ * 2 ^ m)) / |t| := by
    intro m t hlow _
    have hblock0 : (0 : ℝ) < σ * 2 ^ m := by positivity
    have ht0 : (0 : ℝ) < |t| := lt_of_lt_of_le hblock0 hlow
    have hden : (σ * 2 ^ m) * |t| ≤ ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 := by
      have h1 : (σ * 2 ^ m) * |t| ≤ |t| * |t| :=
        mul_le_mul_of_nonneg_right hlow (le_of_lt ht0)
      have h2 : |t| * |t| ≤ ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 := by
        have hb := habsle t
        nlinarith [ht0.le, hb, norm_nonneg ((σ : ℂ) + (t : ℝ) * I)]
      linarith
    have hval : (x ^ σ / (σ * 2 ^ m)) / |t| = x ^ σ / ((σ * 2 ^ m) * |t|) := by
      rw [div_div]
    rw [hG, hval]
    refine div_le_div_of_nonneg_left hxσ.le (by positivity) hden
  -- the machine
  have hmain := fun M : ℕ =>
    GaloisForLFunctions.HTGeometry.integral_symm_norm_mul_kernel_var_le hDc hGc
      (C := fun m => x ^ σ / (σ * 2 ^ m)) (C₀ := x ^ σ / σ ^ 2)
      (fun m => by positivity) (by positivity) hQ0 hκ0 hσ0 hGlow hms M
      (fun m _ t h1 h2 => hGblock m t h1 h2)
  -- the geometric sums
  have hsum : ∀ M : ℕ, ∑ m ∈ Finset.range M, (x ^ σ / (σ * 2 ^ m))
        * ((Real.sqrt Q * Real.sqrt 2 / Real.sqrt σ) * (Real.sqrt 2 / 2) ^ m + 2 * Real.sqrt κ)
      ≤ 3 * (x ^ σ * Real.sqrt Q) + 4 * (x ^ σ * Real.sqrt κ) := by
    intro M
    have hA : (0 : ℝ) ≤ Real.sqrt Q * Real.sqrt 2 / Real.sqrt σ := by positivity
    have hB : (0 : ℝ) ≤ 2 * Real.sqrt κ := by positivity
    have hstep := sum_range_block_kernel_le hA hB hσ1 hxσ.le M
    have hσ1' : (1 : ℝ) ≤ Real.sqrt σ := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt hσ1
    have hAle : x ^ σ * (Real.sqrt Q * Real.sqrt 2 / Real.sqrt σ) / σ
        ≤ (3 / 2) * (x ^ σ * Real.sqrt Q) := by
      have h1 : Real.sqrt Q * Real.sqrt 2 / Real.sqrt σ ≤ Real.sqrt Q * (3 / 2) := by
        have hnum : Real.sqrt Q * Real.sqrt 2 ≤ Real.sqrt Q * (3 / 2) :=
          mul_le_mul_of_nonneg_left sqrt_two_le_three_halves (Real.sqrt_nonneg Q)
        have hdiv : Real.sqrt Q * Real.sqrt 2 / Real.sqrt σ ≤ Real.sqrt Q * Real.sqrt 2 := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.sqrt σ)]
          nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg Q) (Real.sqrt_nonneg 2))
            (by linarith : (0 : ℝ) ≤ Real.sqrt σ - 1)]
        linarith
      have h2 : x ^ σ * (Real.sqrt Q * Real.sqrt 2 / Real.sqrt σ) / σ
          ≤ x ^ σ * (Real.sqrt Q * (3 / 2)) / σ := by
        refine div_le_div_of_nonneg_right ?_ hσ0.le
        exact mul_le_mul_of_nonneg_left h1 hxσ.le
      have h3 : x ^ σ * (Real.sqrt Q * (3 / 2)) / σ ≤ x ^ σ * (Real.sqrt Q * (3 / 2)) := by
        rw [div_le_iff₀ hσ0]
        nlinarith [mul_nonneg (mul_nonneg hxσ.le
          (mul_nonneg (Real.sqrt_nonneg Q) (by norm_num : (0 : ℝ) ≤ 3 / 2)))
          (by linarith : (0 : ℝ) ≤ σ - 1)]
      have h4 : x ^ σ * (Real.sqrt Q * (3 / 2)) = (3 / 2) * (x ^ σ * Real.sqrt Q) := by ring
      linarith
    have hBle : x ^ σ * (2 * Real.sqrt κ) / σ ≤ 2 * (x ^ σ * Real.sqrt κ) := by
      rw [div_le_iff₀ hσ0]
      nlinarith [mul_nonneg (mul_nonneg hxσ.le (Real.sqrt_nonneg κ))
        (by linarith : (0 : ℝ) ≤ σ - 1)]
    linarith
  -- the low range
  have hlow : x ^ σ / σ ^ 2 * (Real.sqrt (2 * σ) * Real.sqrt (Q + κ * σ))
      ≤ 2 * (x ^ σ * Real.sqrt Q) + 3 * (x ^ σ * Real.sqrt κ) := by
    have hκσ : (0 : ℝ) ≤ κ * σ := by positivity
    have hsplit : Real.sqrt (Q + κ * σ) ≤ Real.sqrt Q + Real.sqrt (κ * σ) := by
      have hsq : Q + κ * σ ≤ (Real.sqrt Q + Real.sqrt (κ * σ)) ^ 2 := by
        nlinarith [Real.sq_sqrt hQ0, Real.sq_sqrt hκσ, Real.sqrt_nonneg Q,
          Real.sqrt_nonneg (κ * σ)]
      calc Real.sqrt (Q + κ * σ) ≤ Real.sqrt ((Real.sqrt Q + Real.sqrt (κ * σ)) ^ 2) :=
            Real.sqrt_le_sqrt hsq
        _ = Real.sqrt Q + Real.sqrt (κ * σ) := Real.sqrt_sq (by positivity)
    have hκs : Real.sqrt (κ * σ) ≤ (3 / 2) * Real.sqrt κ := by
      have h1 : Real.sqrt (κ * σ) ≤ Real.sqrt (κ * 2) :=
        Real.sqrt_le_sqrt (by nlinarith [hκ0])
      have h2 : Real.sqrt (κ * 2) = Real.sqrt κ * Real.sqrt 2 := Real.sqrt_mul hκ0 2
      have h3 : Real.sqrt κ * Real.sqrt 2 ≤ Real.sqrt κ * (3 / 2) :=
        mul_le_mul_of_nonneg_left sqrt_two_le_three_halves (Real.sqrt_nonneg κ)
      rw [h2] at h1
      linarith
    have h2σ : Real.sqrt (2 * σ) ≤ 2 := by
      have h1 : Real.sqrt (2 * σ) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
      have h2 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      linarith
    have hinv : x ^ σ / σ ^ 2 ≤ x ^ σ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hxσ.le (by nlinarith : (0 : ℝ) ≤ σ ^ 2 - 1)]
    have hprodnn : (0 : ℝ) ≤ Real.sqrt (2 * σ) * Real.sqrt (Q + κ * σ) := by positivity
    calc x ^ σ / σ ^ 2 * (Real.sqrt (2 * σ) * Real.sqrt (Q + κ * σ))
        ≤ x ^ σ * (Real.sqrt (2 * σ) * Real.sqrt (Q + κ * σ)) :=
          mul_le_mul_of_nonneg_right hinv hprodnn
      _ ≤ x ^ σ * (2 * (Real.sqrt Q + (3 / 2) * Real.sqrt κ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hxσ.le
          have hQs : (0 : ℝ) ≤ Real.sqrt (Q + κ * σ) := Real.sqrt_nonneg _
          have hstep1 : Real.sqrt (2 * σ) * Real.sqrt (Q + κ * σ)
              ≤ 2 * Real.sqrt (Q + κ * σ) := mul_le_mul_of_nonneg_right h2σ hQs
          have hstep2 : 2 * Real.sqrt (Q + κ * σ)
              ≤ 2 * (Real.sqrt Q + (3 / 2) * Real.sqrt κ) := by linarith
          linarith
      _ = 2 * (x ^ σ * Real.sqrt Q) + 3 * (x ^ σ * Real.sqrt κ) := by ring
  -- choose a dyadic range containing the interval
  obtain ⟨M, hM⟩ : ∃ M : ℕ, T ≤ σ * 2 ^ M := by
    refine ⟨⌈T⌉₊, ?_⟩
    have h1 : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
    have h2 : (⌈T⌉₊ : ℝ) < (2 : ℝ) ^ (⌈T⌉₊ : ℕ) := by
      have h := Nat.lt_two_pow_self (n := ⌈T⌉₊)
      calc (⌈T⌉₊ : ℝ) < ((2 ^ (⌈T⌉₊ : ℕ) : ℕ) : ℝ) := by exact_mod_cast h
        _ = (2 : ℝ) ^ (⌈T⌉₊ : ℕ) := by push_cast; ring
    have h3 : (0 : ℝ) < (2 : ℝ) ^ (⌈T⌉₊ : ℕ) := by positivity
    nlinarith [hσ1]
  have hnn : ∀ t : ℝ, 0 ≤ ‖D t‖ * G t := fun t => mul_nonneg (norm_nonneg _) (hGnn t)
  have hmono : (∫ t in (-T)..T, ‖D t‖ * G t)
      ≤ ∫ t in (-(σ * 2 ^ M))..(σ * 2 ^ M), ‖D t‖ * G t := by
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) hM ?_
      ((hDc.norm.mul hGc).intervalIntegrable (μ := volume) _ _)
    filter_upwards with t
    exact hnn t
  have hfin := hmain M
  have hs := hsum M
  linarith [hmono, hfin, hs, hlow, mul_nonneg hxσ.le (Real.sqrt_nonneg κ)]

/-- **The Cesàro vertical integral of a finitely supported Dirichlet series, uniformly in the
height.** -/
theorem integral_symm_norm_cesaro_le_of_meanSquare_dyadic {g : ℕ → ℂ} {sg : Finset ℕ}
    (hg0 : 0 ∉ sg) (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ sg) {σ x T : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2)
    (hx : 0 < x) (hT : 0 ≤ T) :
    (∫ t in (-T)..T,
        ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖)
      ≤ 8 * x ^ σ * Real.sqrt (generalMeanSquareConst g sg σ)
        + 12 * x ^ σ * Real.sqrt (generalMeanSquareRate g sg σ) := by
  have hcongr : (∫ t in (-T)..T,
        ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖)
      = ∫ t in (-T)..T, ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖
          * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2) :=
    intervalIntegral.integral_congr fun t _ => norm_cesaro_integrand hx _ σ t
  rw [hcongr]
  exact integral_symm_norm_mul_cesaroKernel_le_of_meanSquare
    (continuous_LSeries_line_of_support hg0 hgsupp σ)
    (generalMeanSquareConst_nonneg g sg σ) (generalMeanSquareRate_nonneg g sg σ) hσ1 hσ2 hx hT
    (fun U hU => integral_Icc_normSq_LSeries_le_general_affine hg0 hgsupp σ (by linarith))

/-- **The Cesàro chain with a height-free analytic term.**  For every bounded `f` truncated at `N`, the
analytic side is `≍ x^σ√(log N)` uniformly in the height, with no distance hypothesis. -/
theorem norm_sum_Icc_mul_log_div_le_cesaro_dyadic {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1) {N : ℕ}
    (hN : 1 ≤ N) {σ T x : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ T) (hxN : (N : ℝ) ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 N, truncSeq f N n * ((Real.log (x / n) : ℝ) : ℂ)‖
      ≤ (∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x / n))
        + (1 / (2 * Real.pi))
          * (8 * x ^ σ * Real.sqrt (5 * Real.pi * Real.exp 1 * (1 + Real.log N))
            + 12 * x ^ σ * Real.sqrt (5 * Real.pi)) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : (0 : ℝ) < x := by linarith
  have hxσ : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hx σ
  have hTle : -T ≤ T := by linarith
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  have hsupp : ∀ n : ℕ, truncSeq f N n ≠ 0 → n ∈ Finset.Icc 1 N := fun _ h => truncSeq_support h
  have hker := integral_symm_norm_cesaro_le_of_meanSquare_dyadic hs0 hsupp (x := x) (T := T)
    hσ1 hσ2 hx hT0.le
  have hCle : Real.sqrt (generalMeanSquareConst (truncSeq f N) (Finset.Icc 1 N) σ)
      ≤ Real.sqrt (5 * Real.pi * Real.exp 1 * (1 + Real.log N)) :=
    Real.sqrt_le_sqrt (generalMeanSquareConst_truncSeq_le hbdd N hσ1)
  have hRle : Real.sqrt (generalMeanSquareRate (truncSeq f N) (Finset.Icc 1 N) σ)
      ≤ Real.sqrt (5 * Real.pi) :=
    Real.sqrt_le_sqrt (generalMeanSquareRate_truncSeq_le hbdd N hσ1)
  have hA : (∫ t in (-T)..T,
        ‖LSeries (truncSeq f N) ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖)
      ≤ 8 * x ^ σ * Real.sqrt (5 * Real.pi * Real.exp 1 * (1 + Real.log N))
        + 12 * x ^ σ * Real.sqrt (5 * Real.pi) := by
    have h1 : 8 * x ^ σ * Real.sqrt (generalMeanSquareConst (truncSeq f N) (Finset.Icc 1 N) σ)
        ≤ 8 * x ^ σ * Real.sqrt (5 * Real.pi * Real.exp 1 * (1 + Real.log N)) :=
      mul_le_mul_of_nonneg_left hCle (by positivity)
    have h2 : 12 * x ^ σ * Real.sqrt (generalMeanSquareRate (truncSeq f N) (Finset.Icc 1 N) σ)
        ≤ 12 * x ^ σ * Real.sqrt (5 * Real.pi) :=
      mul_le_mul_of_nonneg_left hRle (by positivity)
    linarith [hker]
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun t : ℝ => LSeries (truncSeq f N) ((σ : ℂ) + (t : ℝ) * I)
      * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)) hTle
  exact norm_sum_Icc_mul_log_div_le_cesaro_of_integral hbdd hN hσ1 hσ2 hT hxN
    (le_trans hnorm hA)

end RHTower.Sieve
end
