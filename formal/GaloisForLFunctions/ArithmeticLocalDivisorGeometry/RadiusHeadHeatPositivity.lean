import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.RootRadiusHeatCone
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.SourceDivisorGeometry
import GaloisForLFunctions.RHTower.XiZeroCountRVMRemainder
import GaloisForLFunctions.RHTower.XiOrderedZeroCopyEnumeration
import GaloisForLFunctions.RHTower.XiSliceHeatFiniteHeadReduction

/-!
# Every finite head of `ξ` is heat-repaired at every large height

The radius-`R` finite head of the horizontal `Ξ`-slice at height `t` is the unnormalized divisor
polynomial `D_{t,R}(y) = ∏_crit (y + (γ−t)²) ∏_pairs ((y + u² − δ²)² + 4u²δ²)` over the zero copies
`z` with `|z − t| ≤ R`.  All its roots `−(z − t)²` lie in the disc `|y| ≤ R²`, and its degree is
the number `N(t, R)` of retained copies.

**Degree law** (`coeffNonneg_heat_localDivisorPolynomial_radiusHead`).  At every height `t`, the
heated head `e^{s∂_x²} D_{t,R}(x²)` has nonnegative coefficients as soon as `32 R² ≤ s N(t, R)`.
The configuration of the retained zeros (off-line pairs, clusters, central multiplicities) plays
no role: only the radius and the number of retained copies.

**Counting** (`exists_le_card_radiusHead`).  For every radius `R ≥ R₀` (with `R₀` fixed by the
Riemann–von Mangoldt remainder) the number of retained copies tends to infinity with `|t|`.

**Head positivity at every large height** (`exists_radiusHead_heat_coeffNonneg`).  For every
`R ≥ R₀` and every heat `λ > 0` there is `T` such that the heated radius-`R` head at heat `λ/2`
is coefficient-positive at every height `|t| ≥ T`.  This is the finite-head counterpart of the
Ki–Kim–Lee large-height reality, obtained from zero counting alone.

**Slice consequence** (`exists_xiSliceHeatTransfer_nonneg_of_head_counting`).  Through the exact
head/tail transfer, every heated slice coefficient `T_n(λ, 0, t)` is nonnegative at every large
height with `Ξ(t) ≠ 0`.  The Euler region is not used: the heat needed to repair the local zero
divisor is `O(R²/N(t,R))`, and the counting function makes `N(t,R) → ∞`.
-/

open Polynomial Complex Finset
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn
open scoped ComplexOrder

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry

noncomputable section

/-! ## The local divisor is a product of disc factors -/

theorem discFactor_X_add_C {r c : ℝ} (hc : |c| ≤ r) : DiscFactor r (X + C c) := by
  have h : (X + C c : ℝ[X]) = X - C (-c) := by rw [C_neg, sub_neg_eq_add]
  rw [h]
  exact DiscFactor.lin (-c) (by rwa [abs_neg])

theorem discFactor_pairFactor {r u δ : ℝ} (h : u ^ 2 + δ ^ 2 ≤ r) :
    DiscFactor r (pairFactor u δ) := by
  have e : pairFactor u δ = X ^ 2 - C (2 * (δ ^ 2 - u ^ 2)) * X + C ((u ^ 2 + δ ^ 2) ^ 2) := by
    unfold pairFactor
    simp only [map_mul, map_sub, map_ofNat, map_pow, map_add]
    ring
  rw [e]
  exact DiscFactor.quad _ _
    (by nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg δ)])
    (pow_le_pow_left₀ (by positivity) h 2)

/-- The local divisor polynomial as a list product of its factors. -/
theorem localDivisorPolynomial_eq_list_prod (t : ℝ) (S : Finset XiZeroCopy) :
    localDivisorPolynomial t S =
      (((sliceTruncCrit S).toList.map fun q => X + C (((xiSpectralPoint q).re - t) ^ 2)) ++
        ((sliceTruncUp S).toList.map fun q =>
          pairFactor ((xiSpectralPoint q).re - t) (xiSpectralPoint q).im)).prod := by
  rw [List.prod_append, Finset.prod_map_toList, Finset.prod_map_toList]
  rfl

theorem sq_norm_sub_ofReal (z : ℂ) (t : ℝ) : ‖z - t‖ ^ 2 = (z.re - t) ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
  ring

theorem discFactors_localDivisorPolynomial_radiusHead (t R : ℝ) :
    ∀ F ∈ (((sliceTruncCrit (xiSliceGaussianRadiusHead t R)).toList.map
        fun q => X + C (((xiSpectralPoint q).re - t) ^ 2)) ++
      ((sliceTruncUp (xiSliceGaussianRadiusHead t R)).toList.map fun q =>
        pairFactor ((xiSpectralPoint q).re - t) (xiSpectralPoint q).im)),
      DiscFactor (R ^ 2) F := by
  intro F hF
  have hhead : ∀ q ∈ xiSliceGaussianRadiusHead t R,
      ((xiSpectralPoint q).re - t) ^ 2 + (xiSpectralPoint q).im ^ 2 ≤ R ^ 2 := by
    intro q hq
    rw [← sq_norm_sub_ofReal]
    exact pow_le_pow_left₀ (norm_nonneg _) ((mem_xiSliceGaussianRadiusHead t R q).mp hq) 2
  rcases List.mem_append.mp hF with h | h
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    have hq' := (mem_sliceTruncCrit.mp (Finset.mem_toList.mp hq)).1
    refine discFactor_X_add_C ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hhead q hq', sq_nonneg (xiSpectralPoint q).im]
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    have hq' := (mem_sliceTruncUp.mp (Finset.mem_toList.mp hq)).1
    exact discFactor_pairFactor (hhead q hq')

/-- **Degree law for the actual head.**  At every height, the heated radius-`R` head is
coefficient-positive once `32 R² ≤ s · N(t, R)`. -/
theorem coeffNonneg_heat_localDivisorPolynomial_radiusHead {t R s : ℝ} (hs : 0 < s)
    (hcard : 32 * R ^ 2 ≤ s * (xiSliceGaussianRadiusHead t R).card) :
    CoeffNonneg (forwardPolyHeat s
      (expand ℝ 2 (localDivisorPolynomial t (xiSliceGaussianRadiusHead t R)))) := by
  have hdeg := localDivisorPolynomial_degree t (xiSliceGaussianRadiusHead t R)
  rw [sliceTrunc_radiusHead] at hdeg
  rw [localDivisorPolynomial_eq_list_prod] at hdeg ⊢
  refine coeffNonneg_forwardPolyHeat_expand_of_discFactors (sq_nonneg R) hs
    (discFactors_localDivisorPolynomial_radiusHead t R) ?_
  rw [hdeg]
  exact hcard

/-! ## The normalized head used by the slice transfer -/

theorem sliceAtom_mul_sq_norm {t : ℝ} {q : XiZeroCopy} (hq : xiSpectralPoint q ≠ t) :
    sliceAtom t q * ‖xiSpectralPoint q - t‖ ^ 2 = 1 := by
  have h : ‖xiSpectralPoint q - t‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hq)
  unfold sliceAtom
  field_simp

/-- A normalized critical factor: `1 + a y = a (y + c)` when `a c = 1`. -/
theorem crit_normalized_eq {a c : ℝ} (h : a * c = 1) : (1 + C a * X : ℝ[X]) = C a * (X + C c) := by
  rw [mul_add, ← C_mul, h, map_one]; ring

/-- A normalized pair factor: `(1 + a y)² − 4δ²a² y = a² · pairFactor(u, δ)` when
`a (u² + δ²) = 1`. -/
theorem pair_normalized_eq {a u δ : ℝ} (hm : a * (u ^ 2 + δ ^ 2) = 1) :
    (1 + C a * X) ^ 2 - C (4 * (δ ^ 2 * a ^ 2)) * X = C (a ^ 2) * pairFactor u δ := by
  have h1 : a ^ 2 * (2 * (u ^ 2 - δ ^ 2)) = 2 * a - 4 * (δ ^ 2 * a ^ 2) := by
    linear_combination (2 * a) * hm
  have h2 : a ^ 2 * (u ^ 2 + δ ^ 2) ^ 2 = 1 := by
    linear_combination (a * (u ^ 2 + δ ^ 2) + 1) * hm
  unfold pairFactor
  have e : C (a ^ 2) * (X ^ 2 + C (2 * (u ^ 2 - δ ^ 2)) * X + C ((u ^ 2 + δ ^ 2) ^ 2)) =
      C (a ^ 2) * X ^ 2 + C (a ^ 2 * (2 * (u ^ 2 - δ ^ 2))) * X +
        C (a ^ 2 * (u ^ 2 + δ ^ 2) ^ 2) := by
    simp only [C_mul]; ring
  rw [e, h1, h2]
  simp only [map_sub, map_mul, map_ofNat, map_pow, map_one]
  ring

/-- Off the zero ordinates the normalized head is a positive multiple of the divisor polynomial. -/
theorem sliceTruncPoly_eq_C_mul_localDivisorPolynomial {t : ℝ} {S : Finset XiZeroCopy}
    (hS : ∀ q ∈ S, xiSpectralPoint q ≠ t) :
    ∃ c : ℝ, 0 < c ∧ sliceTruncPoly t S = C c * localDivisorPolynomial t S := by
  have hpos : ∀ q ∈ S, 0 < sliceAtom t q := fun q hq => by
    unfold sliceAtom
    have : 0 < ‖xiSpectralPoint q - t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hS q hq))
    positivity
  refine ⟨(∏ q ∈ sliceTruncCrit S, sliceAtom t q) * ∏ q ∈ sliceTruncUp S, sliceAtom t q ^ 2,
    mul_pos (prod_pos fun q hq => hpos q (mem_sliceTruncCrit.mp hq).1)
      (prod_pos fun q hq => pow_pos (hpos q (mem_sliceTruncUp.mp hq).1) 2), ?_⟩
  have hA : (∏ q ∈ sliceTruncCrit S, (1 + C (sliceAtom t q) * X)) =
      ∏ q ∈ sliceTruncCrit S, (C (sliceAtom t q) * (X + C (((xiSpectralPoint q).re - t) ^ 2))) := by
    refine prod_congr rfl fun q hq => crit_normalized_eq ?_
    have hcrit := mem_sliceTruncCrit.mp hq
    have hm := sliceAtom_mul_sq_norm (hS q hcrit.1)
    rw [sq_norm_sub_ofReal, show (xiSpectralPoint q).im = 0 from hcrit.2] at hm
    simpa using hm
  have hB : (∏ q ∈ sliceTruncUp S, ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X)) =
      ∏ q ∈ sliceTruncUp S, (C (sliceAtom t q ^ 2) *
        pairFactor ((xiSpectralPoint q).re - t) (xiSpectralPoint q).im) := by
    refine prod_congr rfl fun q hq => ?_
    have hm := sliceAtom_mul_sq_norm (hS q (mem_sliceTruncUp.mp hq).1)
    rw [sq_norm_sub_ofReal] at hm
    have hdef : sliceDefect t q = (xiSpectralPoint q).im ^ 2 * sliceAtom t q ^ 2 := by
      unfold sliceDefect sliceAtom; ring
    rw [hdef]
    exact pair_normalized_eq hm
  unfold sliceTruncPoly localDivisorPolynomial
  rw [hA, hB, prod_mul_distrib, prod_mul_distrib, map_mul, map_prod, map_prod]
  ring

/-- **Normalized degree law.**  At a height `t` with `Ξ(t) ≠ 0`, the normalized radius-`R` head
used by the slice transfer is heat-positive once `32 R² ≤ s · N(t, R)`. -/
theorem coeffNonneg_heat_sliceTruncPoly_radiusHead {t R s : ℝ} (ht : XiC (t : ℂ) ≠ 0)
    (hs : 0 < s) (hcard : 32 * R ^ 2 ≤ s * (xiSliceGaussianRadiusHead t R).card) :
    CoeffNonneg (forwardPolyHeat s (expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)))) := by
  have hS : ∀ q ∈ xiSliceGaussianRadiusHead t R, xiSpectralPoint q ≠ t := fun q _ h =>
    ht (by rw [← h]; exact XiC_xiSpectralPoint_eq_zero q)
  obtain ⟨c, hc, he⟩ := sliceTruncPoly_eq_C_mul_localDivisorPolynomial hS
  rw [he, map_mul, expand_C, forwardPolyHeat_C_mul]
  have h := coeffNonneg_heat_localDivisorPolynomial_radiusHead hs hcard
  intro n
  rw [coeff_C_mul]
  exact mul_nonneg hc.le (h n)

/-! ## Counting the retained copies -/

/-- Copies with ordinate in `(t − R/2, t + R/2]` are retained by the radius-`R` head (`R ≥ 1`). -/
theorem sdiff_xiCopiesPos_subset_radiusHead {t R : ℝ} (hR : 1 ≤ R) :
    xiCopiesPos (t + R / 2) \ xiCopiesPos (t - R / 2) ⊆ xiSliceGaussianRadiusHead t R := by
  intro q hq
  rw [Finset.mem_sdiff, mem_xiCopiesPos, mem_xiCopiesPos] at hq
  obtain ⟨⟨hle, hpos⟩, hnot⟩ := hq
  have hlow : t - R / 2 < (q.1 : ℂ).im := by
    by_contra h
    push Not at h
    exact hnot ⟨by rw [abs_of_pos hpos]; exact h, hpos⟩
  rw [abs_of_pos hpos] at hle
  rw [mem_xiSliceGaussianRadiusHead]
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint, Complex.mul_re]
  have him : (xiSpectralPoint q).im ^ 2 < 1 / 4 := by
    have h := xiZeroCopy_re_mem_open_unit q
    have : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
    rw [this, neg_sq]
    nlinarith [h.1, h.2]
  have hsq : ‖xiSpectralPoint q - t‖ ^ 2 ≤ R ^ 2 := by
    rw [sq_norm_sub_ofReal, hre]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) two_ne_zero).mp hsq

theorem card_sdiff_xiCopiesPos_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((xiCopiesPos b \ xiCopiesPos a).card : ℝ) = (xiZeroCount b : ℝ) - (xiZeroCount a : ℝ) := by
  have hsub : xiCopiesPos a ⊆ xiCopiesPos b := fun q hq =>
    mem_xiCopiesPos.mpr ⟨(mem_xiCopiesPos.mp hq).1.trans hab, (mem_xiCopiesPos.mp hq).2⟩
  have haC : ((xiCopiesPos a).card : ℝ) = (xiZeroCount a : ℝ) := by
    exact_mod_cast intCast_card_xiCopiesPos ha
  have hbC : ((xiCopiesPos b).card : ℝ) = (xiZeroCount b : ℝ) := by
    exact_mod_cast intCast_card_xiCopiesPos (ha.trans hab)
  rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub), hbC, haC]

/-- Tangent-line bound for the smooth counting function: `M(b) − M(a) ≥ (b − a) log(a/2π)/(2π)`. -/
theorem routeKSmoothRVMCount_sub_ge {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * Real.log (a / (2 * Real.pi)) / (2 * Real.pi) ≤
      routeKSmoothRVMCount b - routeKSmoothRVMCount a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hpi : 0 < 2 * Real.pi := by positivity
  unfold routeKSmoothRVMCount routeKRVMBase
  have hlogB : Real.log (2 * Real.pi * Real.exp 1) = Real.log (2 * Real.pi) + 1 := by
    rw [Real.log_mul hpi.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have hA : Real.log (a / (2 * Real.pi * Real.exp 1)) = Real.log a - (Real.log (2 * Real.pi) + 1) := by
    rw [Real.log_div ha.ne' (by positivity), hlogB]
  have hB : Real.log (b / (2 * Real.pi * Real.exp 1)) = Real.log b - (Real.log (2 * Real.pi) + 1) := by
    rw [Real.log_div hb.ne' (by positivity), hlogB]
  have hC : Real.log (a / (2 * Real.pi)) = Real.log a - Real.log (2 * Real.pi) :=
    Real.log_div ha.ne' hpi.ne'
  rw [hA, hB, hC]
  have hkey : b - a ≤ b * (Real.log b - Real.log a) := by
    have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
    rw [Real.log_div ha.ne' hb.ne'] at h
    have : a / b * b = a := by field_simp
    nlinarith [hb]
  rw [div_le_iff₀ hpi]
  field_simp
  nlinarith [hkey]

/-- **The number of retained copies tends to infinity.**  There is `R₀ ≥ 1` such that for every
`R ≥ R₀` and every bound `M`, the radius-`R` head retains at least `M` copies at every large
height. -/
theorem exists_le_card_radiusHead :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ M : ℝ, ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      M ≤ ((xiSliceGaussianRadiusHead t R).card : ℝ) := by
  obtain ⟨C, hC, T₀, hT₀, hrvm⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  refine ⟨max 1 (8 * Real.pi * C), le_max_left _ _, fun R hR M => ?_⟩
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRC : 8 * Real.pi * C ≤ R := (le_max_right _ _).trans hR
  have hpi : 0 < Real.pi := Real.pi_pos
  set K : ℝ := (M + C * (4 * Real.log (4 * Real.pi) + 2 * Real.log 2)) / (2 * C) with hK
  refine ⟨max (max (2 * R) (T₀ + R)) (max (4 * Real.pi + R) (Real.exp K)), fun t ht => ?_⟩
  have ht1 : 2 * R ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have ht2 : T₀ + R ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have ht3 : 4 * Real.pi + R ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have ht4 : Real.exp K ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have htpos : 0 < t := by linarith
  set a := t - R / 2 with ha
  set b := t + R / 2 with hb
  have ha0 : 0 < a := by rw [ha]; linarith
  have hab : a ≤ b := by rw [ha, hb]; linarith
  -- the window copies are retained
  have hsub := sdiff_xiCopiesPos_subset_radiusHead (t := t) hR1
  have hcard : (((xiCopiesPos b \ xiCopiesPos a).card : ℕ) : ℝ) ≤
      ((xiSliceGaussianRadiusHead t R).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  rw [card_sdiff_xiCopiesPos_eq ha0.le hab] at hcard
  -- Riemann–von Mangoldt on both ends
  have hra := hrvm a (by rw [ha]; linarith)
  have hrb := hrvm b (by rw [hb]; linarith)
  rw [abs_le] at hra hrb
  have htan := routeKSmoothRVMCount_sub_ge ha0 hab
  have hba : b - a = R := by rw [ha, hb]; ring
  rw [hba] at htan
  -- logarithmic estimates
  have hloga : Real.log t - Real.log (4 * Real.pi) ≤ Real.log (a / (2 * Real.pi)) := by
    rw [← Real.log_div htpos.ne' (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hlogb : Real.log b ≤ Real.log t + Real.log 2 := by
    rw [← Real.log_mul htpos.ne' two_ne_zero]
    exact Real.log_le_log (by rw [hb]; linarith) (by rw [hb]; linarith)
  have hlogab : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  have hlogt : K ≤ Real.log t := by
    rw [← Real.log_exp K]; exact Real.log_le_log (Real.exp_pos K) ht4
  have hlog4 : 0 ≤ Real.log (a / (2 * Real.pi)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ (by positivity)]
    rw [ha]; linarith
  -- assemble
  have hmain : 4 * C * Real.log (a / (2 * Real.pi)) ≤ R * Real.log (a / (2 * Real.pi)) / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hRC hlog4]
  have hKdef : 2 * C * K = M + C * (4 * Real.log (4 * Real.pi) + 2 * Real.log 2) := by
    rw [hK]; field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlogt (by positivity : (0 : ℝ) ≤ 2 * C),
    mul_le_mul_of_nonneg_left hloga (by positivity : (0 : ℝ) ≤ 4 * C),
    mul_le_mul_of_nonneg_left hlogb hC.le, mul_le_mul_of_nonneg_left hlogab hC.le]

/-- Reflection `z ↦ −z` maps the radius head at `t` onto the radius head at `−t`. -/
theorem card_radiusHead_neg (t R : ℝ) :
    (xiSliceGaussianRadiusHead (-t) R).card = (xiSliceGaussianRadiusHead t R).card := by
  refine Finset.card_bij (fun q _ => xiZeroCopyReflectEquiv q) (fun q hq => ?_)
    (fun q₁ _ q₂ _ h => xiZeroCopyReflectEquiv.injective h) (fun q hq => ?_)
  · rw [mem_xiSliceGaussianRadiusHead] at hq ⊢
    rw [xiSpectralPoint_reflect, show -xiSpectralPoint q - ((t : ℝ) : ℂ) =
      -(xiSpectralPoint q - ((-t : ℝ) : ℂ)) by push_cast; ring, norm_neg]
    exact hq
  · refine ⟨xiZeroCopyReflectEquiv.symm q, ?_, Equiv.apply_symm_apply _ _⟩
    rw [mem_xiSliceGaussianRadiusHead] at hq ⊢
    have h := xiSpectralPoint_reflect (xiZeroCopyReflectEquiv.symm q)
    rw [Equiv.apply_symm_apply] at h
    rw [show xiSpectralPoint (xiZeroCopyReflectEquiv.symm q) = -xiSpectralPoint q by
      rw [h, neg_neg], show -xiSpectralPoint q - ((-t : ℝ) : ℂ) =
      -(xiSpectralPoint q - ((t : ℝ) : ℂ)) by push_cast; ring, norm_neg]
    exact hq

/-! ## Head positivity at every large height -/

/-- **Finite-head heat positivity at every large height.**  For every radius `R ≥ R₀` and every
heat `λ > 0`, the heated radius-`R` divisor head at heat `λ/2` is coefficient-positive at every
height `|t| ≥ T`. -/
theorem exists_radiusHead_heat_coeffNonneg :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ lam : ℝ, 0 < lam → ∃ T : ℝ, ∀ t : ℝ, T ≤ |t| →
      CoeffNonneg (forwardPolyHeat (lam / 2)
        (expand ℝ 2 (localDivisorPolynomial t (xiSliceGaussianRadiusHead t R)))) := by
  obtain ⟨R₀, hR₀, hcount⟩ := exists_le_card_radiusHead
  refine ⟨R₀, hR₀, fun R hR lam hlam => ?_⟩
  obtain ⟨T, hT⟩ := hcount R hR (64 * R ^ 2 / lam)
  have hR0 : 0 ≤ R := by linarith
  have hcard : ∀ t : ℝ, T ≤ t → 32 * R ^ 2 ≤ lam / 2 * (xiSliceGaussianRadiusHead t R).card := by
    intro t ht
    have h := hT t ht
    rw [div_le_iff₀ hlam] at h
    linarith
  refine ⟨T, fun t ht => ?_⟩
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at ht
    exact coeffNonneg_heat_localDivisorPolynomial_radiusHead (by positivity) (hcard t ht)
  · rw [abs_of_neg h0] at ht
    refine coeffNonneg_heat_localDivisorPolynomial_radiusHead (by positivity) ?_
    rw [← card_radiusHead_neg t R]
    simpa using hcard (-t) ht

/-- **Large-height slice positivity from zero counting.**  For every heat `λ > 0`, every heated
slice coefficient is nonnegative at every large height off the zero ordinates.  The proof goes
through the finite head only: degree law plus counting, then the exact head/tail transfer. -/
theorem exists_xiSliceHeatTransfer_nonneg_of_head_counting {lam : ℝ} (hlam : 0 < lam) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ |t| → XiC (t : ℂ) ≠ 0 → ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer lam 0 t n := by
  obtain ⟨R₀, hR₀, hcount⟩ := exists_le_card_radiusHead
  obtain ⟨T, hT⟩ := hcount R₀ le_rfl (64 * R₀ ^ 2 / lam)
  have hR0 : 0 ≤ R₀ := by linarith
  refine ⟨T, fun t ht hXi n => ?_⟩
  have hcardt : 32 * R₀ ^ 2 ≤ lam / 2 * (xiSliceGaussianRadiusHead t R₀).card := by
    have h : 64 * R₀ ^ 2 / lam ≤ ((xiSliceGaussianRadiusHead t R₀).card : ℝ) := by
      rcases le_or_gt 0 t with h0 | h0
      · rw [abs_of_nonneg h0] at ht; exact hT t ht
      · rw [abs_of_neg h0] at ht
        rw [← card_radiusHead_neg t R₀]
        simpa using hT (-t) ht
    rw [div_le_iff₀ hlam] at h
    linarith
  have hhead := coeffNonneg_heat_sliceTruncPoly_radiusHead hXi (by positivity) hcardt
  exact xiSliceHeatTransfer_nonneg_of_finiteHead_poly hlam.le le_rfl hXi hR0
    (by nlinarith) hhead n

end

end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
