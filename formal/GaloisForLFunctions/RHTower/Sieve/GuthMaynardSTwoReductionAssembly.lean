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
    (hε1 : ε ≤ 1) (hC : GMLemma62Bound w ε C) (hN : 1 ≤ N) (hT : 1 ≤ T)
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

/-- **Summing the pairs.**
`N³ Σ_{x,y∈W} |A(x−y)|² ≤ |W| c_d² + Σ_{k long} w_k ∫ Σ_{x,y} |D_{M_k}(x−y+u)|² + (8C² + c_s) N² |W|²`. -/
theorem cube_mul_gmS2Diagonal_le (w : CGLRealSmoothBump) {ε C N T : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hC : GMLemma62Bound w ε C) (hN : 1 ≤ N) (hT : 1 ≤ T) {W : Finset ℝ}
    (hsep : IsSeparated (T ^ ε) W) (hW : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T) :
    N ^ 3 * gmS2Diagonal w N W ≤ (W.card : ℝ) * gmDiagConst w ^ 2 +
      ∑ k ∈ gmLongClasses ε N T, gmClassWeight ε C N T k *
        (∫ u in (-(T ^ ε / 2))..(T ^ ε / 2),
          ∑ x ∈ W, ∑ y ∈ W, ‖cglGMHeadPoly (gmClassLength ε N k) (x - y + u)‖ ^ 2) +
      (8 * C ^ 2 + gmShortConst w ε) * N ^ 2 * (W.card : ℝ) ^ 2 := by
  classical
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  set c' : ℝ := 8 * C ^ 2 + gmShortConst w ε with hc'
  have hc'0 : 0 ≤ c' := by have := gmShortConst_nonneg w ε; positivity
  set F : ℝ → ℝ → ℝ := fun x y => ∑ k ∈ gmLongClasses ε N T,
    gmClassWeight ε C N T k * gmClassIntegral ε N T k x y with hF
  have hF0 : ∀ x y, 0 ≤ F x y := fun x y => Finset.sum_nonneg fun k _ =>
    mul_nonneg (gmClassWeight_nonneg ε C N T hN0.le hT0.le k)
      (gmClassIntegral_nonneg ε N T hT0.le k x y)
  have hrow : ∀ x ∈ W, ∑ y ∈ W, N ^ 3 * ‖gmNonzero w N (x - y)‖ ^ 2 ≤
      gmDiagConst w ^ 2 + ∑ y ∈ W, F x y + (W.card : ℝ) * (c' * N ^ 2) := by
    intro x hx
    rw [← Finset.add_sum_erase W _ hx, sub_self]
    have hdiag := cube_normSq_gmNonzero_zero_le w hN
    have hoff : ∑ y ∈ W.erase x, N ^ 3 * ‖gmNonzero w N (x - y)‖ ^ 2 ≤
        ∑ y ∈ W.erase x, (F x y + c' * N ^ 2) := by
      refine Finset.sum_le_sum fun y hy => ?_
      have hyW := Finset.mem_of_mem_erase hy
      have hxy : x ≠ y := (Finset.ne_of_mem_erase hy).symm
      have hd : |x - y| ≤ T := abs_sub_le_iff.mpr
        ⟨by linarith [(hW x hx).2, (hW y hyW).1], by linarith [(hW y hyW).2, (hW x hx).1]⟩
      have h := cube_normSq_gmNonzero_le_offDiag w hε hε1 hC hN hT (hsep x hx y hyW hxy) hd
      rw [hF]; linarith
    have hext : ∑ y ∈ W.erase x, F x y ≤ ∑ y ∈ W, F x y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset x W) fun y _ _ => hF0 x y
    have hcard : ((W.erase x).card : ℝ) ≤ W.card := by exact_mod_cast Finset.card_erase_le
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hoff
    have : ((W.erase x).card : ℝ) * (c' * N ^ 2) ≤ (W.card : ℝ) * (c' * N ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    linarith
  have hswap : ∑ x ∈ W, ∑ y ∈ W, F x y = ∑ k ∈ gmLongClasses ε N T, gmClassWeight ε C N T k *
      (∫ u in (-(T ^ ε / 2))..(T ^ ε / 2),
        ∑ x ∈ W, ∑ y ∈ W, ‖cglGMHeadPoly (gmClassLength ε N k) (x - y + u)‖ ^ 2) := by
    calc ∑ x ∈ W, ∑ y ∈ W, F x y
        = ∑ x ∈ W, ∑ k ∈ gmLongClasses ε N T, ∑ y ∈ W,
            gmClassWeight ε C N T k * gmClassIntegral ε N T k x y :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ k ∈ gmLongClasses ε N T, ∑ x ∈ W, ∑ y ∈ W,
            gmClassWeight ε C N T k * gmClassIntegral ε N T k x y := Finset.sum_comm
      _ = ∑ k ∈ gmLongClasses ε N T, gmClassWeight ε C N T k *
            ∑ x ∈ W, ∑ y ∈ W, gmClassIntegral ε N T k x y := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sum_gmClassIntegral_eq]
  calc N ^ 3 * gmS2Diagonal w N W
      = ∑ x ∈ W, ∑ y ∈ W, N ^ 3 * ‖gmNonzero w N (x - y)‖ ^ 2 := by
        rw [gmS2Diagonal, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _
    _ ≤ ∑ x ∈ W, (gmDiagConst w ^ 2 + ∑ y ∈ W, F x y + (W.card : ℝ) * (c' * N ^ 2)) :=
        Finset.sum_le_sum hrow
    _ = (W.card : ℝ) * gmDiagConst w ^ 2 + ∑ x ∈ W, ∑ y ∈ W, F x y +
          c' * N ^ 2 * (W.card : ℝ) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
          nsmul_eq_mul, nsmul_eq_mul]
        ring
    _ = _ := by rw [hswap]

/-- **The off-diagonal error of the diagonal extraction.**  With `α = c_d(1+T)²/N²`,
`β = B_n/(T^ε)^n` (`εn ≥ 104`) and `|W| ≤ T+1`: `3N³|W|³α²β ≤ 96 c_d² B_n N² |W|²`. -/
theorem gmS2_offDiag_error_le (w : CGLRealSmoothBump) {ε N T : ℝ} (hε : 0 < ε) (hN : 1 ≤ N)
    (hT : 1 ≤ T) {W : Finset ℝ} (hcard : (W.card : ℝ) ≤ T + 1) :
    3 * N ^ 3 * ((W.card : ℝ) ^ 3 * ((gmDiagConst w * (1 + T) ^ 2 / N ^ 2) ^ 2 *
        (cglGMMellinBudget w (cglGMLemma62MellinOrder ε) /
          (T ^ ε) ^ cglGMLemma62MellinOrder ε))) ≤
      96 * gmDiagConst w ^ 2 * cglGMMellinBudget w (cglGMLemma62MellinOrder ε) * N ^ 2 *
        (W.card : ℝ) ^ 2 := by
  set n := cglGMLemma62MellinOrder ε with hn
  set c := gmDiagConst w with hc
  set B := cglGMMellinBudget w n with hB
  set X : ℝ := (W.card : ℝ) with hX
  have hc0 : 0 ≤ c := gmDiagConst_nonneg w
  have hB0 : 0 ≤ B := cglGMMellinBudget_nonneg w n
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  have hTn : T ^ 104 ≤ (T ^ ε) ^ n := by
    rw [← Real.rpow_mul_natCast hT0.le]
    exact pow_hundredFour_le_rpow hT (cglGMLemma62MellinOrder_spec hε)
  have hX3 : X ^ 3 * (1 + T) ^ 4 ≤ 32 * T ^ 104 * X ^ 2 := by
    have h1 : X ^ 3 * (1 + T) ^ 4 ≤ X ^ 2 * (1 + T) ^ 5 := by
      have : X ^ 3 * (1 + T) ^ 4 = X ^ 2 * (X * (1 + T) ^ 4) := by ring
      rw [this, show (1 + T) ^ 5 = (1 + T) * (1 + T) ^ 4 by ring]
      gcongr
      linarith
    have h2 : (1 + T) ^ 5 ≤ 32 * T ^ 104 := by
      calc (1 + T) ^ 5 ≤ (2 * T) ^ 5 := by gcongr; linarith
        _ = 32 * T ^ 5 := by ring
        _ ≤ 32 * T ^ 104 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by norm_num)) (by norm_num)
    calc X ^ 3 * (1 + T) ^ 4 ≤ X ^ 2 * (32 * T ^ 104) := h1.trans (by gcongr)
      _ = 32 * T ^ 104 * X ^ 2 := by ring
  have hTn0 : 0 < (T ^ ε) ^ n := by positivity
  have hrw : 3 * N ^ 3 * (X ^ 3 * ((c * (1 + T) ^ 2 / N ^ 2) ^ 2 * (B / (T ^ ε) ^ n))) =
      3 * c ^ 2 * B * (X ^ 3 * (1 + T) ^ 4) / (N * (T ^ ε) ^ n) := by
    field_simp
  rw [hrw]
  have hN2 : (1 : ℝ) ≤ N ^ 2 := one_le_pow₀ hN
  calc 3 * c ^ 2 * B * (X ^ 3 * (1 + T) ^ 4) / (N * (T ^ ε) ^ n)
      ≤ 3 * c ^ 2 * B * (32 * T ^ 104 * X ^ 2) / (1 * T ^ 104) := by
        gcongr
    _ = 96 * c ^ 2 * B * X ^ 2 := by field_simp; ring
    _ ≤ 96 * c ^ 2 * B * N ^ 2 * X ^ 2 := by
        have : 0 ≤ 96 * c ^ 2 * B * X ^ 2 := by positivity
        nlinarith

/-- The real-number combination behind (6.1). -/
theorem sixOne_real_combine {s d m nd t4R nx e B₀ α β : ℝ} (hs : s ≤ d + m) (hd : d ≤ e * nx)
    (hm : m ≤ 3 * B₀ * nd) (hnd : nd ≤ α * t4R + β * nx) (hB₀ : 0 ≤ B₀) (hnx : 0 ≤ nx)
    (ht4R : 0 ≤ t4R) (he : 0 ≤ e) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    s ≤ (3 * B₀ * α + (3 * B₀ * β + e)) * t4R + (3 * B₀ * α + (3 * B₀ * β + e)) * nx := by
  have h1 : 3 * B₀ * nd ≤ 3 * B₀ * (α * t4R + β * nx) :=
    mul_le_mul_of_nonneg_left hnd (by positivity)
  have h2 : 0 ≤ (3 * B₀ * β + e) * t4R := by positivity
  have h3 : 0 ≤ 3 * B₀ * α * nx := by positivity
  nlinarith

/-- `‖S₂‖ ≤ 3B₀ · N³ Σ|A|² + 96 c_d² B_n N² |W|²` (diagonal extraction and its error). -/
theorem norm_gmS2_le_diag_add (w : CGLRealSmoothBump) {ε T N : ℝ} (hε : 0 < ε) (hT : 1 ≤ T)
    (hN : 1 ≤ N) {W : Finset ℝ} (hsep : IsSeparated (T ^ ε) W) (hW : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T) :
    ‖gmS2 w N W‖ ≤ 96 * gmDiagConst w ^ 2 * cglGMMellinBudget w (cglGMLemma62MellinOrder ε) *
        (N ^ 2 * (W.card : ℝ) ^ 2) +
      3 * cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 0 * (N ^ 3 * gmS2Diagonal w N W) := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  have hTe : 0 < T ^ ε := Real.rpow_pos_of_pos hT0 ε
  have hcard : (W.card : ℝ) ≤ T + 1 := by
    have h := card_le_of_separated_subset_Icc (S := W) (a := 0) (ℓ := T) hT0.le
      (fun s hs => by simpa using hW s hs)
      (fun s hs s' hs' hne => (Real.one_le_rpow hT hε.le).trans (hsep s hs s' hs' hne))
    simpa using h
  have hα : ∀ x ∈ W, ∀ y ∈ W, ‖gmNonzero w N (x - y)‖ ≤ gmDiagConst w * (1 + T) ^ 2 / N ^ 2 := by
    intro x hx y hy
    have hd : |x - y| ≤ T := abs_sub_le_iff.mpr
      ⟨by linarith [(hW x hx).2, (hW y hy).1], by linarith [(hW y hy).2, (hW x hx).1]⟩
    refine (norm_gmNonzero_le_diagConst w hN (x - y)).trans ?_
    have := gmDiagConst_nonneg w
    gcongr
  have hβ : ∀ x ∈ W, ∀ z ∈ W, z ≠ x → ‖gmHat w (z - x) 0‖ ≤
      cglGMMellinBudget w (cglGMLemma62MellinOrder ε) / (T ^ ε) ^ cglGMLemma62MellinOrder ε :=
    fun x hx z hz hzx => norm_gmHat_zero_le_of_separated w _ hTe hsep hx hz hzx
  have hdiag := norm_gmS2_sub_diag_le w hN0 W hα
    (div_nonneg (cglGMMellinBudget_nonneg w _) (by positivity)) hβ
  have herr := gmS2_offDiag_error_le w hε hN hT hcard
  have hD0 : 0 ≤ gmS2Diagonal w N W :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by positivity
  have hhat : ‖gmHat w 0 0‖ ≤ cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 0 := by
    simpa [gmHat, bumpFourier] using
      cglSmoothBumpHt_allOrder_fourier_decay w.toCGLSmoothBump 0 0 0
  have hmain : ‖3 * ((N : ℂ) ^ 3 * (gmHat w 0 0 * (gmS2Diagonal w N W : ℂ)))‖ ≤
      3 * cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 0 * (N ^ 3 * gmS2Diagonal w N W) := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hN0.le, Real.norm_of_nonneg hD0, show ‖(3 : ℂ)‖ = 3 by norm_num]
    calc 3 * (N ^ 3 * (‖gmHat w 0 0‖ * gmS2Diagonal w N W))
        = 3 * ‖gmHat w 0 0‖ * (N ^ 3 * gmS2Diagonal w N W) := by ring
      _ ≤ _ := by gcongr
  calc ‖gmS2 w N W‖ ≤ ‖gmS2 w N W - 3 * ((N : ℂ) ^ 3 * (gmHat w 0 0 *
        (gmS2Diagonal w N W : ℂ)))‖ + ‖3 * ((N : ℂ) ^ 3 * (gmHat w 0 0 *
        (gmS2Diagonal w N W : ℂ)))‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := by
        refine add_le_add (hdiag.trans (herr.trans (le_of_eq ?_))) hmain
        ring

/-- `N³ Σ|A|² ≤ 16C²(15 + 4/ε) (T^ε)^4 R + (c_d² + 8C² + c_s) N² |W|²`. -/
theorem cube_mul_gmS2Diagonal_le_sixOne (w : CGLRealSmoothBump) {ε C N T : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hC : GMLemma62Bound w ε C) (hN : 1 ≤ N) (hT : 1 ≤ T) {W : Finset ℝ}
    (hsep : IsSeparated (T ^ ε) W) (hW : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T) :
    N ^ 3 * gmS2Diagonal w N W ≤
      16 * C ^ 2 * (15 + 4 / ε) * ((T ^ ε) ^ 4 * gmSixOneSum ε N T W) +
        (gmDiagConst w ^ 2 + (8 * C ^ 2 + gmShortConst w ε)) * (N ^ 2 * (W.card : ℝ) ^ 2) := by
  have hsum := cube_mul_gmS2Diagonal_le w hε hε1 hC hN hT hsep hW
  have hclass : ∑ k ∈ gmLongClasses ε N T, gmClassWeight ε C N T k *
      (∫ u in (-(T ^ ε / 2))..(T ^ ε / 2),
        ∑ x ∈ W, ∑ y ∈ W, ‖cglGMHeadPoly (gmClassLength ε N k) (x - y + u)‖ ^ 2) ≤
      16 * C ^ 2 * (15 + 4 / ε) * ((T ^ ε) ^ 4 * gmSixOneSum ε N T W) := by
    rw [gmSixOneSum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have := gmClassWeight_mul_integral_le (C := C) hε hε1 hN hT hk W
    linarith
  have hX : (W.card : ℝ) ≤ (W.card : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos W.card with h0 | hpos
    · simp [h0]
    · have : (1 : ℝ) ≤ W.card := by exact_mod_cast hpos
      nlinarith
  have hN2 : (1 : ℝ) ≤ N ^ 2 := one_le_pow₀ hN
  have hW2 : (W.card : ℝ) * gmDiagConst w ^ 2 ≤ gmDiagConst w ^ 2 * (N ^ 2 * (W.card : ℝ) ^ 2) := by
    have h1 : (W.card : ℝ) ≤ N ^ 2 * (W.card : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (W.card : ℝ)]
    nlinarith [sq_nonneg (gmDiagConst w)]
  calc N ^ 3 * gmS2Diagonal w N W
      ≤ (W.card : ℝ) * gmDiagConst w ^ 2 +
          16 * C ^ 2 * (15 + 4 / ε) * ((T ^ ε) ^ 4 * gmSixOneSum ε N T W) +
          (8 * C ^ 2 + gmShortConst w ε) * N ^ 2 * (W.card : ℝ) ^ 2 := by linarith
    _ ≤ gmDiagConst w ^ 2 * (N ^ 2 * (W.card : ℝ) ^ 2) +
          16 * C ^ 2 * (15 + 4 / ε) * ((T ^ ε) ^ 4 * gmSixOneSum ε N T W) +
          (8 * C ^ 2 + gmShortConst w ε) * N ^ 2 * (W.card : ℝ) ^ 2 := by linarith
    _ = _ := by ring

/-- **Guth–Maynard (6.1) for `ζ`, summed form.**  For every `ε ∈ (0,1]` there is `C ≥ 0` such that
for all `T ≥ 1`, `N ≥ 1` and every `T^ε`-separated `W ⊂ [0,T]`:
`‖S₂‖ ≤ C (T^ε)^4 Σ_{k long} Σ_{j ≤ log₂ M_k} (N²/2^j) Σ_{t₁,t₂∈W} |Σ_{m∈block_j(M_k)} m^{i(t₁−t₂)}|²
  + C N² |W|²`. -/
theorem gmS2_le_sixOne (w : CGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ), 1 ≤ T → 1 ≤ N →
      IsSeparated (T ^ ε) W → (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
      ‖gmS2 w N W‖ ≤ C * ((T ^ ε) ^ 4 * gmSixOneSum ε N T W) + C * (N ^ 2 * (W.card : ℝ) ^ 2) := by
  obtain ⟨C, _, hC⟩ := exists_gmLemma62Bound w hε
  have hB₀ := cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump 0
  have hcd := gmDiagConst_nonneg w
  have hcs := gmShortConst_nonneg w ε
  have hBn := cglGMMellinBudget_nonneg w (cglGMLemma62MellinOrder ε)
  refine ⟨3 * cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 0 * (16 * C ^ 2 * (15 + 4 / ε)) +
    (3 * cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 0 *
        (gmDiagConst w ^ 2 + (8 * C ^ 2 + gmShortConst w ε)) +
      96 * gmDiagConst w ^ 2 * cglGMMellinBudget w (cglGMLemma62MellinOrder ε)),
    by positivity, ?_⟩
  intro T N W hT hN hsep hW
  exact sixOne_real_combine (norm_gmS2_le_diag_add w hε hT hN hsep hW) le_rfl le_rfl
    (cube_mul_gmS2Diagonal_le_sixOne w hε hε1 hC hN hT hsep hW) hB₀ (by positivity)
    (mul_nonneg (by positivity) (gmSixOneSum_nonneg ε N T W)) (by positivity) (by positivity)
    (by positivity)

end RHTower.GuthMaynard
