import GaloisForLFunctions.BiScaleUncertainty.MultiplicativeChainBesselAndOriginLeverage

/-!
# Shared-origin leverage for multiple orthogonal chains

All chains constrain the same origin coordinate. Their joint support function involves the
sum of the block Euclidean norms, squared, rather than the sum of their squares. This accounts
for the origin energy exactly once and gives a simultaneous dyadic-coset inequality.
-/

open Finset
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

variable {ι κ : Type*}

/-- Sum of Euclidean norms of the coefficient blocks. -/
def blockWeightNorm (M : Finset ι) (s : ι → Finset κ) (w : ι → κ → ℝ) : ℝ :=
  ∑ m ∈ M, Real.sqrt (∑ k ∈ s m, w m k ^ 2)

theorem blockWeightNorm_nonneg (M : Finset ι) (s : ι → Finset κ) (w : ι → κ → ℝ) :
    0 ≤ blockWeightNorm M s w :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- The support-function upper bound for balls with a common origin coordinate. -/
theorem shared_origin_weighted_sum_le (M : Finset ι) (hM : M.Nonempty)
    (s : ι → Finset κ) (w u : ι → κ → ℝ) (W u₀ R : ℝ) (hR : 0 ≤ R)
    (hsph : ∀ m ∈ M, u₀ ^ 2 + ∑ k ∈ s m, u m k ^ 2 ≤ R ^ 2) :
    W * u₀ + ∑ m ∈ M, ∑ k ∈ s m, w m k * u m k ≤
      Real.sqrt (W ^ 2 + blockWeightNorm M s w ^ 2) * R := by
  have hres : 0 ≤ R ^ 2 - u₀ ^ 2 := by
    obtain ⟨m, hm⟩ := hM
    have := hsph m hm
    have := Finset.sum_nonneg (s := s m) (fun k _ => sq_nonneg (u m k))
    linarith
  let r := Real.sqrt (R ^ 2 - u₀ ^ 2)
  have hr : r ^ 2 = R ^ 2 - u₀ ^ 2 := Real.sq_sqrt hres
  have hblock : ∀ m ∈ M, (∑ k ∈ s m, w m k * u m k) ≤
      Real.sqrt (∑ k ∈ s m, w m k ^ 2) * r := by
    intro m hm
    have h := sphere_weighted_sum_le_sqrt_mul (s m) 0 (w m) (u m) 0 r
      (Real.sqrt_nonneg _) (by
        rw [hr]
        have := hsph m hm
        linarith)
    simpa using h
  have hsum : (∑ m ∈ M, ∑ k ∈ s m, w m k * u m k) ≤ blockWeightNorm M s w * r := by
    simpa only [blockWeightNorm, Finset.sum_mul] using Finset.sum_le_sum hblock
  have hfinal := sphere_weighted_sum_le_sqrt_mul ({()} : Finset Unit) W
    (fun _ => blockWeightNorm M s w) (fun _ => r) u₀ R hR
    (by simpa only [Finset.sum_singleton] using (show u₀ ^ 2 + r ^ 2 ≤ R ^ 2 by linarith))
  simp only [Finset.sum_singleton] at hfinal
  linarith

/-- Exact joint leverage bound, with the origin weight charged once. -/
theorem shared_origin_leverage_bound (M : Finset ι) (hM : M.Nonempty)
    (s : ι → Finset κ) (w u : ι → κ → ℝ) (W u₀ R : ℝ) (hR : 0 ≤ R)
    (hsph : ∀ m ∈ M, u₀ ^ 2 + ∑ k ∈ s m, u m k ^ 2 ≤ R ^ 2) :
    (W + (∑ m ∈ M, ∑ k ∈ s m, w m k) -
      Real.sqrt (W ^ 2 + blockWeightNorm M s w ^ 2)) * R ≤
    W * (R - u₀) + ∑ m ∈ M, ∑ k ∈ s m, w m k * (R - u m k) := by
  have h := shared_origin_weighted_sum_le M hM s w u W u₀ R hR hsph
  have hid : W * (R - u₀) + (∑ m ∈ M, ∑ k ∈ s m, w m k * (R - u m k)) =
      (W + ∑ m ∈ M, ∑ k ∈ s m, w m k) * R -
        (W * u₀ + ∑ m ∈ M, ∑ k ∈ s m, w m k * u m k) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [hid]
  linarith

/-- Rationalized origin leverage includes all cross terms between block norms. -/
theorem shared_origin_leverage_rational_bound (M : Finset ι) (hM : M.Nonempty)
    (s : ι → Finset κ) (w u : ι → κ → ℝ) {W : ℝ} (hW : 0 < W)
    (u₀ R : ℝ) (hR : 0 ≤ R)
    (hsph : ∀ m ∈ M, u₀ ^ 2 + ∑ k ∈ s m, u m k ^ 2 ≤ R ^ 2) :
    ((∑ m ∈ M, ∑ k ∈ s m, w m k) - blockWeightNorm M s w ^ 2 / (2 * W)) * R ≤
    W * (R - u₀) + ∑ m ∈ M, ∑ k ∈ s m, w m k * (R - u m k) := by
  let Q := blockWeightNorm M s w
  have hupper : Real.sqrt (W ^ 2 + Q ^ 2) ≤ W + Q ^ 2 / (2 * W) := by
    have hnonneg : 0 ≤ W + Q ^ 2 / (2 * W) := by positivity
    rw [← Real.sqrt_sq hnonneg]
    apply Real.sqrt_le_sqrt
    have hid : (W + Q ^ 2 / (2 * W)) ^ 2 =
        W ^ 2 + Q ^ 2 + (Q ^ 2 / (2 * W)) ^ 2 := by
      field_simp
      ring
    rw [hid]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have h := shared_origin_leverage_bound M hM s w u W u₀ R hR hsph
  have hm := mul_le_mul_of_nonneg_right hupper hR
  dsimp [Q] at hm
  nlinarith

private theorem normalized_block_sq_sum_le (s : Finset κ) (w : κ → ℝ) :
    (∑ k ∈ s, (w k / Real.sqrt (∑ j ∈ s, w j ^ 2)) ^ 2) ≤ 1 := by
  let q := Real.sqrt (∑ j ∈ s, w j ^ 2)
  have hq : q ^ 2 = ∑ j ∈ s, w j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (w j))
  change (∑ k ∈ s, (w k / q) ^ 2) ≤ 1
  simp_rw [div_pow, ← Finset.sum_div]
  rw [← hq]
  by_cases hz : q = 0
  · simp [hz]
  · simp [hz]

private theorem weighted_normalized_block_sum (s : Finset κ) (w : κ → ℝ) :
    (∑ k ∈ s, w k * (w k / Real.sqrt (∑ j ∈ s, w j ^ 2))) =
      Real.sqrt (∑ j ∈ s, w j ^ 2) := by
  let q := Real.sqrt (∑ j ∈ s, w j ^ 2)
  have hq : q ^ 2 = ∑ j ∈ s, w j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (w j))
  change (∑ k ∈ s, w k * (w k / q)) = q
  simp_rw [show ∀ k, w k * (w k / q) = w k ^ 2 / q by intro k; ring]
  rw [← Finset.sum_div, ← hq]
  by_cases hz : q = 0
  · simp [hz]
  · field_simp

/-- The shared-origin support function is attained. No compatibility between distinct blocks
is imposed; the witness certifies sharpness of precisely this sphere relaxation. -/
theorem shared_origin_support_attained (M : Finset ι) (s : ι → Finset κ)
    (w : ι → κ → ℝ) {W : ℝ} (hW : 0 < W) (R : ℝ) :
    ∃ (u₀ : ℝ) (u : ι → κ → ℝ),
      (∀ m ∈ M, u₀ ^ 2 + ∑ k ∈ s m, u m k ^ 2 ≤ R ^ 2) ∧
      W * u₀ + (∑ m ∈ M, ∑ k ∈ s m, w m k * u m k) =
        Real.sqrt (W ^ 2 + blockWeightNorm M s w ^ 2) * R := by
  let Q := blockWeightNorm M s w
  let D := Real.sqrt (W ^ 2 + Q ^ 2)
  have hDsq : D ^ 2 = W ^ 2 + Q ^ 2 := Real.sq_sqrt (by positivity)
  have hD : D ≠ 0 := by
    intro hz
    rw [hz] at hDsq
    nlinarith [sq_nonneg Q]
  let a := R * W / D
  let b := R * Q / D
  have hab : a ^ 2 + b ^ 2 = R ^ 2 := by
    dsimp [a, b]
    calc
      (R * W / D) ^ 2 + (R * Q / D) ^ 2 = R ^ 2 * (W ^ 2 + Q ^ 2) / D ^ 2 := by ring
      _ = R ^ 2 := by rw [← hDsq]; field_simp
  refine ⟨a, (fun m k => b * (w m k / Real.sqrt (∑ j ∈ s m, w m j ^ 2))), ?_, ?_⟩
  · intro m _
    have hb := mul_le_mul_of_nonneg_left (normalized_block_sq_sum_le (s m) (w m)) (sq_nonneg b)
    simp_rw [mul_pow, ← Finset.mul_sum]
    nlinarith
  · have hsum : (∑ m ∈ M, ∑ k ∈ s m,
        w m k * (b * (w m k / Real.sqrt (∑ j ∈ s m, w m j ^ 2)))) = b * Q := by
      calc
        _ = ∑ m ∈ M, b * Real.sqrt (∑ j ∈ s m, w m j ^ 2) := by
          apply Finset.sum_congr rfl
          intro m _
          calc
            _ = b * ∑ k ∈ s m,
                w m k * (w m k / Real.sqrt (∑ j ∈ s m, w m j ^ 2)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
            _ = b * Real.sqrt (∑ j ∈ s m, w m j ^ 2) := by
              rw [weighted_normalized_block_sum]
        _ = b * Q := (Finset.mul_sum ..).symm
    rw [hsum]
    change W * a + b * Q = D * R
    dsimp [a, b]
    calc
      W * (R * W / D) + R * Q / D * Q = R * (W ^ 2 + Q ^ 2) / D := by ring
      _ = D * R := by rw [← hDsq]; field_simp

/-- Simultaneous dyadic-coset bound under the literal logarithmic-grid zero condition. -/
theorem autocorr_multi_dyadic_coset_leverage (f : ℝ → ℝ)
    (hfc : HasCompactSupport f) (hf : Continuous f) {N : ℕ}
    (hgrid : ∀ n ∈ Finset.Icc 2 N, autocorr f (Real.log (n : ℝ)) = 0)
    (M : Finset ℕ) (hM : M.Nonempty) (hm : ∀ m ∈ M, 1 ≤ m)
    (s : ℕ → Finset ℕ)
    (hs : ∀ m ∈ M, ∀ k ∈ s m, 2 ≤ m * 2 ^ k ∧ m * 2 ^ k ≤ N)
    (W : ℝ) (w : ℕ → ℕ → ℝ) (y : ℝ) :
    (W + (∑ m ∈ M, ∑ k ∈ s m, w m k) -
      Real.sqrt (W ^ 2 + blockWeightNorm M s w ^ 2)) * autocorr f 0 ≤
    W * (autocorr f 0 - autocorr f y) +
      ∑ m ∈ M, ∑ k ∈ s m,
        w m k * (autocorr f 0 - autocorr f (Real.log ((m * 2 ^ k : ℕ) : ℝ) - y)) := by
  apply shared_origin_leverage_bound M hM s w
    (fun m k => autocorr f (Real.log ((m * 2 ^ k : ℕ) : ℝ) - y)) W
    (autocorr f y) (autocorr f 0) (autocorr_zero_nonneg f)
  intro m hmem
  exact autocorr_dyadic_coset_sphere_sub_le hfc hf (hm m hmem) hgrid (s m) (hs m hmem) y

end

end GaloisForLFunctions.BiScaleUncertainty
