import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSTwoReductionSixOne
import GaloisForLFunctions.RHTower.ZetaZeroExponentialDetectorTypeTwo

/-!
# Guth–Maynard §6: (6.1) assembled

For the Chen–Gupta–Li bump, every `ε ∈ (0,1]`, `T ≥ 1`, `N ≥ 1` and every `T^ε`-separated
`W ⊂ [0,T]` (`gmS2_le_sixOne`):

`‖S₂‖ ≤ C (T^ε)^4 Σ_{k long} Σ_{j ≤ log₂ M_k} (N²/2^j) Σ_{t₁,t₂∈W} |Σ_{m ∈ block_j(M_k)} m^{i(t₁−t₂)}|²
      + C N² |W|²`.

Per pair `t₁ ≠ t₂` (`τ = t₁ − t₂`, class `k`): in a long class Lemma 6.2 at length `M_k` gives
`N³|A(τ)|² ≤ (N³ 4C²U/2^k) G_k(t₁,t₂) + 8C² N²`; in a short class Lemma 4.3 gives
`N³|A(τ)|² ≤ c_s N²`.  The diagonal is `N³|A(0)|² ≤ c_d²`, the off-diagonal error of
`S₂ − 3N³ĥ₀(0) Σ|A|²` is `≤ 96 c_d² B_n N²|W|²` (using `|W| ≤ T + 1`), and the long-class integrals
are the block sums of (6.1) by `gmClassWeight_mul_integral_le`.
-/

set_option autoImplicit false

open Complex Finset
open scoped FourierTransform

noncomputable section

namespace RHTower.GuthMaynard

open Sieve

/-- The diagonal constant `c_d = 2(1+Z) A₂` of Lemma 4.3 for `A`. -/
def gmDiagConst (w : CGLRealSmoothBump) : ℝ :=
  2 * (1 + cglGMInverseSquareMass) *
    (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2)

/-- The short-class constant `c_s = (2(1+Z) A_j)² 4^j`, `j = ⌈104/ε²⌉ + 2`. -/
def gmShortConst (w : CGLRealSmoothBump) (ε : ℝ) : ℝ :=
  (2 * (1 + cglGMInverseSquareMass) *
    (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump (cglGMLemma62FourierOrder ε) /
      (2 * Real.pi) ^ cglGMLemma62FourierOrder ε)) ^ 2 * 4 ^ cglGMLemma62FourierOrder ε

theorem gmDiagConst_nonneg (w : CGLRealSmoothBump) : 0 ≤ gmDiagConst w := by
  have := cglGMInverseSquareMass_nonneg
  have := cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump 2
  unfold gmDiagConst
  positivity

theorem gmShortConst_nonneg (w : CGLRealSmoothBump) (ε : ℝ) : 0 ≤ gmShortConst w ε := by
  unfold gmShortConst
  positivity

/-- `|A(τ)| ≤ c_d (1+|τ|)² / N²`. -/
theorem norm_gmNonzero_le_diagConst (w : CGLRealSmoothBump) {N : ℝ} (hN : 1 ≤ N) (τ : ℝ) :
    ‖gmNonzero w N τ‖ ≤ gmDiagConst w * (1 + |τ|) ^ 2 / N ^ 2 := by
  refine (norm_gmNonzero_le_decay w hN le_rfl τ).trans (le_of_eq ?_)
  unfold gmDiagConst
  ring

/-- **The diagonal pair.** `N³ |A(0)|² ≤ c_d²`. -/
theorem cube_normSq_gmNonzero_zero_le (w : CGLRealSmoothBump) {N : ℝ} (hN : 1 ≤ N) :
    N ^ 3 * ‖gmNonzero w N 0‖ ^ 2 ≤ gmDiagConst w ^ 2 := by
  have hN0 : 0 < N := by linarith
  have h := norm_gmNonzero_le_diagConst w hN 0
  rw [abs_zero, add_zero, one_pow, mul_one] at h
  have hc := gmDiagConst_nonneg w
  calc N ^ 3 * ‖gmNonzero w N 0‖ ^ 2 ≤ N ^ 3 * (gmDiagConst w / N ^ 2) ^ 2 := by gcongr
    _ = gmDiagConst w ^ 2 / N := by field_simp
    _ ≤ gmDiagConst w ^ 2 := div_le_self (by positivity) hN

/-- **An off-diagonal pair.**  For `T^ε ≤ |τ| ≤ T`, `τ = x − y`:
`N³ |A(τ)|² ≤ Σ_{k long} (N³ 4C²U/2^k) G_k(x,y) + (8C² + c_s) N²`. -/
theorem cube_normSq_gmNonzero_le_offDiag (w : CGLRealSmoothBump) {ε C N T : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hC0 : 0 ≤ C) (hC : GMLemma62Bound w ε C) (hN : 1 ≤ N) (hT : 1 ≤ T)
    {x y : ℝ} (hsep : T ^ ε ≤ |x - y|) (hxy : |x - y| ≤ T) :
    N ^ 3 * ‖gmNonzero w N (x - y)‖ ^ 2 ≤
      ∑ k ∈ gmLongClasses ε N T, gmClassWeight ε C N T k * gmClassIntegral ε N T k x y +
        (8 * C ^ 2 + gmShortConst w ε) * N ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  have hτ1 : 1 ≤ |x - y| := (Real.one_le_rpow hT hε.le).trans hsep
  have hkK := gmClass_lt_count hxy
  have hk2T := two_pow_le_of_lt_count hT hkK
  have hk2τ := two_pow_gmClass_le hτ1
  have hτk := lt_two_pow_gmClass_succ (x - y)
  have hsum0 : 0 ≤ ∑ k ∈ gmLongClasses ε N T,
      gmClassWeight ε C N T k * gmClassIntegral ε N T k x y :=
    Finset.sum_nonneg fun k _ => mul_nonneg (gmClassWeight_nonneg ε C N T hN0.le hT0.le k)
      (gmClassIntegral_nonneg ε N T hT0.le k x y)
  have hS0 := gmShortConst_nonneg w ε
  by_cases hlong : N ≤ ((2 : ℝ) ^ (gmClass (x - y) + 1)) ^ (1 + ε)
  · have hkL : gmClass (x - y) ∈ gmLongClasses ε N T :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkK, hlong⟩
    obtain ⟨hM1, hM8, hadm⟩ := gmClassLength_spec hε hε1 hN hT hk2T
    have h62 := hC T (x - y) N (gmClassLength ε N (gmClass (x - y))) hT hN hsep hxy hM1
      (hadm (x - y) hτk) hM8
    have hsq := normSq_gmNonzero_le_long w (U := T ^ ε / 2)
      (by have := Real.rpow_nonneg hT0.le ε; positivity) hk2τ h62
    have hNle : N ≤ 4 * T ^ 2 := hlong.trans (classPower_le hε hε1 hT hk2T).2
    have he0 : 0 ≤ T ^ (-100 : ℝ) := Real.rpow_nonneg hT0.le _
    have he1 : T ^ (-100 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT (by norm_num)
    have he2 := rpow_neg_hundred_le_inv_sq hT
    have hNe : N * (T ^ (-100 : ℝ)) ^ 2 ≤ 4 := by
      have hsq' : (T ^ (-100 : ℝ)) ^ 2 ≤ (T ^ 2)⁻¹ := by nlinarith
      calc N * (T ^ (-100 : ℝ)) ^ 2 ≤ (4 * T ^ 2) * (T ^ 2)⁻¹ :=
            mul_le_mul hNle hsq' (by positivity) (by positivity)
        _ = 4 := by field_simp
    have hterm : N ^ 3 * ‖gmNonzero w N (x - y)‖ ^ 2 ≤
        gmClassWeight ε C N T (gmClass (x - y)) * gmClassIntegral ε N T (gmClass (x - y)) x y +
          8 * C ^ 2 * N ^ 2 := by
      calc N ^ 3 * ‖gmNonzero w N (x - y)‖ ^ 2
          ≤ N ^ 3 * (4 * C ^ 2 * (T ^ ε / 2) * ((2 : ℝ) ^ gmClass (x - y))⁻¹ *
              gmClassIntegral ε N T (gmClass (x - y)) x y + 2 * C ^ 2 * (T ^ (-100 : ℝ)) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = gmClassWeight ε C N T (gmClass (x - y)) *
              gmClassIntegral ε N T (gmClass (x - y)) x y +
            2 * C ^ 2 * N ^ 2 * (N * (T ^ (-100 : ℝ)) ^ 2) := by
            unfold gmClassWeight; ring
        _ ≤ _ := by
            have := mul_le_mul_of_nonneg_left hNe (by positivity : (0 : ℝ) ≤ 2 * C ^ 2 * N ^ 2)
            linarith
    have hsingle := Finset.single_le_sum (f := fun k =>
      gmClassWeight ε C N T k * gmClassIntegral ε N T k x y)
      (fun k _ => mul_nonneg (gmClassWeight_nonneg ε C N T hN0.le hT0.le k)
        (gmClassIntegral_nonneg ε N T hT0.le k x y)) hkL
    nlinarith [mul_nonneg hS0 (sq_nonneg N)]
  · have hshort : |x - y| ^ (1 + ε) < N :=
      (Real.rpow_lt_rpow (abs_nonneg _) hτk (by linarith)).trans (not_le.mp hlong)
    obtain ⟨hj2, hjε⟩ := cglGMLemma62FourierOrder_spec hε
    have hjε' : 1 ≤ ε ^ 2 * (2 * (cglGMLemma62FourierOrder ε : ℝ) - 1) := by
      have hj1 : (2 : ℝ) ≤ cglGMLemma62FourierOrder ε := by exact_mod_cast hj2
      nlinarith [sq_nonneg ε]
    have h := mul_normSq_gmNonzero_le_short w hε hT hN hsep hxy hshort hj2 hjε'
    have h' : N ^ 3 * ‖gmNonzero w N (x - y)‖ ^ 2 ≤ gmShortConst w ε * N ^ 2 := by
      calc N ^ 3 * ‖gmNonzero w N (x - y)‖ ^ 2
          = N ^ 2 * (N * ‖gmNonzero w N (x - y)‖ ^ 2) := by ring
        _ ≤ N ^ 2 * gmShortConst w ε := mul_le_mul_of_nonneg_left h (by positivity)
        _ = gmShortConst w ε * N ^ 2 := by ring
    nlinarith [mul_nonneg (sq_nonneg C) (sq_nonneg N)]

end RHTower.GuthMaynard
