import GaloisForLFunctions.RHTower.PolarPrimeMellinDefect
import GaloisForLFunctions.RHTower.PrimeVandermondeSchurResidual
import GaloisForLFunctions.RHTower.MFreeLadder
import Mathlib.Analysis.Matrix.PosDef

open scoped BigOperators ComplexOrder ArithmeticFunction
open Finset Complex Matrix ArithmeticFunction LSeries

namespace RHTower

noncomputable section

abbrev strictPrimeLaplaceCoeff (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ)

def strictPrimeLaplaceWeight (n : ℕ) : ℂ :=
  LSeries.term strictPrimeLaplaceCoeff 1 n

def strictPrimeLaplaceFeature (x : ℝ) (n : ℕ) : ℂ :=
  ((n : ℂ) ^ (x : ℂ))⁻¹

def resolvedStrictPrimeLaplaceGram {N : ℕ} (x : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ∑' n, strictPrimeLaplaceWeight n * strictPrimeLaplaceFeature (x i) n *
    strictPrimeLaplaceFeature (x j) n

theorem strictPrimeLaplaceWeight_nonneg (n : ℕ) :
    0 ≤ strictPrimeLaplaceWeight n := by
  apply LSeries.term_nonneg
  exact Complex.nonneg_iff.mpr ⟨ArithmeticFunction.vonMangoldt_nonneg, rfl⟩

theorem strictPrimeLaplaceFeature_pos {x : ℝ} {n : ℕ} (hn : n ≠ 0) :
    0 < strictPrimeLaplaceFeature x n := by
  exact Complex.inv_natCast_cpow_ofReal_pos hn x

theorem strictPrimeLaplaceFeature_star {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (starRingEnd ℂ) (strictPrimeLaplaceFeature x n) =
      strictPrimeLaplaceFeature x n := by
  by_cases hn : n = 0
  · subst n
    simp [strictPrimeLaplaceFeature,
      Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hx.ne')]
  · have h := (strictPrimeLaplaceFeature_pos (x := x) hn).le
    rcases Complex.nonneg_iff.mp h with ⟨_, him⟩
    exact RCLike.conj_eq_iff_im.mpr him.symm

theorem vonMangoldtTerm_eq_strictWeight_mul_features
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (n : ℕ) :
    LSeries.term strictPrimeLaplaceCoeff (((x + y + 1 : ℝ) : ℂ)) n =
      strictPrimeLaplaceWeight n * strictPrimeLaplaceFeature x n *
        strictPrimeLaplaceFeature y n := by
  by_cases hn : n = 0
  · subst n
    simp [strictPrimeLaplaceWeight, strictPrimeLaplaceFeature, LSeries.term,
      Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hx.ne'),
      Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hy.ne')]
  · rw [LSeries.term_of_ne_zero hn]
    simp only [strictPrimeLaplaceWeight, strictPrimeLaplaceFeature]
    rw [LSeries.term_of_ne_zero hn]
    simp only [Complex.ofReal_add, Complex.ofReal_one]
    rw [show (x : ℂ) + (y : ℂ) + 1 = (1 : ℂ) + (x : ℂ) + (y : ℂ) by ring]
    rw [Complex.cpow_add ((1 : ℂ) + (x : ℂ)) (y : ℂ) (Nat.cast_ne_zero.mpr hn),
      Complex.cpow_add (1 : ℂ) (x : ℂ) (Nat.cast_ne_zero.mpr hn)]
    simp only [div_eq_mul_inv]
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
    ac_rfl

theorem summable_strictWeight_mul_features
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Summable (fun n => strictPrimeLaplaceWeight n * strictPrimeLaplaceFeature x n *
      strictPrimeLaplaceFeature y n) := by
  have hs : 1 < ((((x + y + 1 : ℝ) : ℂ))).re := by
    norm_num
    linarith
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).congr
    (fun n => vonMangoldtTerm_eq_strictWeight_mul_features hx hy n)

theorem resolvedStrictPrimeLaplaceGram_eq
    {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i) :
    resolvedStrictPrimeLaplaceGram x = vonMangoldtPrimeLaplaceGram x := by
  ext i j
  rw [resolvedStrictPrimeLaplaceGram, vonMangoldtPrimeLaplaceGram,
    vonMangoldtPrimeLaplaceChannel, LSeries]
  apply tsum_congr
  intro n
  exact (vonMangoldtTerm_eq_strictWeight_mul_features (hx i) (hx j) n).symm

def strictPrimeBaseFeature (x : ℝ) : ℂ :=
  ((2 : ℝ) ^ (-x) : ℝ)

theorem strictPrimeBaseFeature_ne_zero (x : ℝ) :
    strictPrimeBaseFeature x ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne'

theorem strictPrimeBaseFeature_injective :
    Function.Injective strictPrimeBaseFeature := by
  intro x y hxy
  apply neg_injective
  apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
  exact Complex.ofReal_injective hxy

theorem strictPrimeLaplaceFeature_two_pow (x : ℝ) (m : ℕ) :
    strictPrimeLaplaceFeature x (2 ^ m) = strictPrimeBaseFeature x ^ m := by
  rw [strictPrimeLaplaceFeature, natCast_pow_cpow]
  rw [← inv_pow]
  congr 1
  rw [strictPrimeBaseFeature, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Complex.ofReal_inv, Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
  rfl

theorem exists_primePower_feature_combination_ne_zero
    {N : ℕ} {x : Fin N → ℝ} (hxinj : Function.Injective x)
    {c : Fin N → ℂ} (hc : c ≠ 0) :
    ∃ m : Fin N, ∑ i : Fin N,
      c i * strictPrimeLaplaceFeature (x i) (2 ^ ((m : ℕ) + 1)) ≠ 0 := by
  let q : Fin N → ℂ := fun i => strictPrimeBaseFeature (x i)
  have hqinj : Function.Injective q := strictPrimeBaseFeature_injective.comp hxinj
  let d : Fin N → ℂ := fun i => c i * q i
  have hd : d ≠ 0 := by
    intro hd0
    apply hc
    funext i
    have hi := congrFun hd0 i
    dsimp [d] at hi
    exact (mul_eq_zero.mp hi).resolve_right (strictPrimeBaseFeature_ne_zero (x i))
  let A : Matrix (Fin N) (Fin N) ℂ := finiteMomentSamplingMatrix q
  have hAunit : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (finiteMomentSamplingMatrix_det_ne_zero hqinj)
  have hAd : A.mulVec d ≠ 0 := by
    intro hzero
    apply hd
    exact (Matrix.mulVec_injective_of_isUnit hAunit) (hzero.trans (Matrix.mulVec_zero A).symm)
  obtain ⟨m, hm⟩ : ∃ m, A.mulVec d m ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hAd
    funext m
    exact hall m
  refine ⟨m, ?_⟩
  simp_rw [strictPrimeLaplaceFeature_two_pow]
  simpa [A, d, q, finiteMomentSamplingMatrix, Matrix.mulVec, dotProduct,
    pow_succ, mul_assoc, mul_comm, mul_left_comm] using hm

theorem dotProduct_resolvedStrictPrimeLaplaceGram_eq_tsum
    {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i) (c : Fin N → ℂ) :
    star c ⬝ᵥ (resolvedStrictPrimeLaplaceGram x).mulVec c =
      ∑' n, star (∑ k, c k * strictPrimeLaplaceFeature (x k) n) *
        (strictPrimeLaplaceWeight n *
          ∑ k, c k * strictPrimeLaplaceFeature (x k) n) := by
  let P : ℕ → ℂ := fun n => ∑ k, c k * strictPrimeLaplaceFeature (x k) n
  have hpairs : ∀ i j : Fin N,
      Summable (fun n => star (c i) * (c j *
        (strictPrimeLaplaceWeight n * strictPrimeLaplaceFeature (x i) n *
          strictPrimeLaplaceFeature (x j) n))) := by
    intro i j
    exact (((summable_strictWeight_mul_features (hx i) (hx j)).mul_left (c j)).mul_left
      (star (c i))).congr (fun n => by ring)
  simp only [dotProduct, Pi.star_apply]
  have hswap : ∀ i,
      star (c i) * (resolvedStrictPrimeLaplaceGram x).mulVec c i =
        ∑' n, ∑ j, star (c i) * (c j *
          (strictPrimeLaplaceWeight n * strictPrimeLaplaceFeature (x i) n *
            strictPrimeLaplaceFeature (x j) n)) := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [resolvedStrictPrimeLaplaceGram]
      rw [← (summable_strictWeight_mul_features (hx i) (hx j)).tsum_mul_right (c j)]
      rw [← ((summable_strictWeight_mul_features (hx i) (hx j)).mul_right
        (c j)).tsum_mul_left (star (c i))]
      apply tsum_congr
      intro n
      ring
    · intro j hj
      exact hpairs i j
  calc
    (∑ i, star (c i) * (resolvedStrictPrimeLaplaceGram x).mulVec c i) =
        ∑ i, ∑' n, ∑ j, star (c i) * (c j *
          (strictPrimeLaplaceWeight n * strictPrimeLaplaceFeature (x i) n *
            strictPrimeLaplaceFeature (x j) n)) :=
      Finset.sum_congr rfl (fun i _ => hswap i)
    _ = ∑' n, star (P n) * (strictPrimeLaplaceWeight n * P n) := by
      rw [← Summable.tsum_finsetSum]
      · apply tsum_congr
        intro n
        change (∑ i, ∑ j, star (c i) * (c j *
            (strictPrimeLaplaceWeight n * strictPrimeLaplaceFeature (x i) n *
              strictPrimeLaplaceFeature (x j) n))) =
          (starRingEnd ℂ) (∑ k, c k * strictPrimeLaplaceFeature (x k) n) *
            (strictPrimeLaplaceWeight n *
              ∑ k, c k * strictPrimeLaplaceFeature (x k) n)
        rw [map_sum]
        have hstar (k : Fin N) :
            (starRingEnd ℂ) (c k * strictPrimeLaplaceFeature (x k) n) =
              (starRingEnd ℂ) (c k) * strictPrimeLaplaceFeature (x k) n := by
          rw [map_mul, strictPrimeLaplaceFeature_star (hx k)]
        simp_rw [hstar]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hcstar : (starRingEnd ℂ) (c i) = star (c i) := rfl
        rw [hcstar]
        ring
      · intro i hi
        exact summable_sum (fun j hj => hpairs i j)
    _ = _ := rfl

theorem strictPrimeLaplaceWeight_two_pow_pos (m : ℕ) :
    0 < strictPrimeLaplaceWeight (2 ^ (m + 1)) := by
  apply LSeries.term_pos (pow_ne_zero _ (by norm_num))
  rw [show strictPrimeLaplaceCoeff (2 ^ (m + 1)) =
      ((ArithmeticFunction.vonMangoldt (2 ^ (m + 1)) : ℝ) : ℂ) by rfl,
    ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact Complex.pos_iff.mpr ⟨Real.log_pos (by norm_num), rfl⟩

theorem summable_strictPrimeLaplaceQuadratic
    {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i) (c : Fin N → ℂ) :
    Summable (fun n =>
      star (∑ k, c k * strictPrimeLaplaceFeature (x k) n) *
        (strictPrimeLaplaceWeight n *
          ∑ k, c k * strictPrimeLaplaceFeature (x k) n)) := by
  have hpairs : ∀ i j : Fin N,
      Summable (fun n => star (c i) * (c j *
        (strictPrimeLaplaceWeight n * strictPrimeLaplaceFeature (x i) n *
          strictPrimeLaplaceFeature (x j) n))) := by
    intro i j
    exact (((summable_strictWeight_mul_features (hx i) (hx j)).mul_left (c j)).mul_left
      (star (c i))).congr (fun n => by ring)
  have hsum : Summable (fun n => ∑ i, ∑ j, star (c i) * (c j *
      (strictPrimeLaplaceWeight n * strictPrimeLaplaceFeature (x i) n *
        strictPrimeLaplaceFeature (x j) n))) :=
    summable_sum (fun i _ => summable_sum (fun j _ => hpairs i j))
  apply hsum.congr
  intro n
  change (∑ i, ∑ j, star (c i) * (c j *
      (strictPrimeLaplaceWeight n * strictPrimeLaplaceFeature (x i) n *
        strictPrimeLaplaceFeature (x j) n))) =
    (starRingEnd ℂ) (∑ k, c k * strictPrimeLaplaceFeature (x k) n) *
      (strictPrimeLaplaceWeight n *
        ∑ k, c k * strictPrimeLaplaceFeature (x k) n)
  rw [map_sum]
  have hstar (k : Fin N) :
      (starRingEnd ℂ) (c k * strictPrimeLaplaceFeature (x k) n) =
        (starRingEnd ℂ) (c k) * strictPrimeLaplaceFeature (x k) n := by
    rw [map_mul, strictPrimeLaplaceFeature_star (hx k)]
  simp_rw [hstar]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hcstar : (starRingEnd ℂ) (c i) = star (c i) := rfl
  rw [hcstar]
  ring

theorem vonMangoldtPrimeLaplaceGram_posDef
    {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i)
    (hxinj : Function.Injective x) :
    (vonMangoldtPrimeLaplaceGram x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact (vonMangoldtPrimeLaplaceGram_posSemidef x hx).1
  · intro c hc
    rw [← resolvedStrictPrimeLaplaceGram_eq x hx,
      dotProduct_resolvedStrictPrimeLaplaceGram_eq_tsum x hx c]
    let P : ℕ → ℂ := fun n => ∑ k, c k * strictPrimeLaplaceFeature (x k) n
    have hsum := summable_strictPrimeLaplaceQuadratic x hx c
    obtain ⟨m, hm⟩ := exists_primePower_feature_combination_ne_zero hxinj hc
    apply hsum.tsum_pos
    · intro n
      rw [show star (P n) * (strictPrimeLaplaceWeight n * P n) =
          strictPrimeLaplaceWeight n * (star (P n) * P n) by ring]
      apply mul_nonneg (strictPrimeLaplaceWeight_nonneg n)
      change 0 ≤ (starRingEnd ℂ) (P n) * P n
      rw [← Complex.normSq_eq_conj_mul_self]
      exact Complex.nonneg_iff.mpr ⟨Complex.normSq_nonneg _, rfl⟩
    · rw [show star (P (2 ^ ((m : ℕ) + 1))) *
          (strictPrimeLaplaceWeight (2 ^ ((m : ℕ) + 1)) *
            P (2 ^ ((m : ℕ) + 1))) =
          strictPrimeLaplaceWeight (2 ^ ((m : ℕ) + 1)) *
            (star (P (2 ^ ((m : ℕ) + 1))) * P (2 ^ ((m : ℕ) + 1))) by ring]
      apply mul_pos (strictPrimeLaplaceWeight_two_pow_pos (m : ℕ))
      change 0 < (starRingEnd ℂ) (P (2 ^ ((m : ℕ) + 1))) *
        P (2 ^ ((m : ℕ) + 1))
      rw [← Complex.normSq_eq_conj_mul_self]
      exact Complex.pos_iff.mpr ⟨Complex.normSq_pos.mpr hm, rfl⟩

/-- Every finite packet of distinct positive Laplace nodes has a strictly positive resolved Euler
determinant. -/
theorem det_vonMangoldtPrimeLaplaceGram_pos
    {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i)
    (hxinj : Function.Injective x) :
    0 < (vonMangoldtPrimeLaplaceGram x).det :=
  (vonMangoldtPrimeLaplaceGram_posDef x hx hxinj).det_pos

end

end RHTower

