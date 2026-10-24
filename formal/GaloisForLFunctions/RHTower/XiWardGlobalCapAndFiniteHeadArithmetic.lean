import GaloisForLFunctions.RHTower.DeBruijnCollisionMassAndCriticalHeat
import GaloisForLFunctions.RHTower.XiWardGlobalCapRightZeroSum
import GaloisForLFunctions.RHTower.XiLaguerreExplicitFormula
import GaloisForLFunctions.RHTower.PrimeArchLogHeightDefectOrderTwentyThreeEndpointOptimization
import GaloisForLFunctions.RHTower.XiEndpointSchwarzPairHeightGap
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit
import GaloisForLFunctions.RHTower.XiLogDerivSymmetry
import GaloisForLFunctions.SquareRootThreshold.TheRoutesMeasureOneZeroWidth

/-!
# Polynomial Heat Inversion, Finite-Head Arithmetic Explicit Formula, and Global Ward Cap Doubling

This module establishes four unconditional structural laws connecting polynomial heat positivity on
retained finite zero blocks, the Prime–Cesàro explicit formula, the Global Ward Cap Stieltjes
transform, and the graded zero-width dictionary across the corpus:

1. **Polynomial Heat Semigroup Inversion and Universal Root Obstruction
   (`forwardPolyHeat_forwardPolyHeat`, `polyHeat_forwardPolyHeat`, `eval_polyHeat_eq_sum_hermiteWeight`,
   `not_coeffNonneg_taylor_forwardPolyHeat_of_eval_zero`):**
   On `ℝ[X]`, `forwardPolyHeat s₁ (forwardPolyHeat s₂ p) = forwardPolyHeat (s₁ + s₂) p` and
   `polyHeat s (forwardPolyHeat s p) = p`.  At `s = λ/2` (`λ > 0`), backward heat sends `X^N` to
   the scaled probabilists' Hermite polynomial `λ^{N/2} He_N(X / √λ)`, so
   `(polyHeat (λ/2) Q).eval δ = ∑_{N ≤ deg Q} Q.coeff N · sliceHermiteWeight λ δ N`.  Consequently,
   if `P ≠ 0` vanishes at `δ > σ ≥ 0`, then `taylor σ (forwardPolyHeat (λ/2) P)` cannot have
   nonnegative coefficients whenever `0 ≤ λ` and `4 λ · deg P ≤ (δ − σ)²`.
2. **Multiplicity-Sharp Finite-Head Detection, Pure-Quadratic Strip Law, and Graded Width Equivalence
   (`not_coeffNonneg_taylor_forwardPolyHeat_finiteHead_of_offLine_zero`,
   `zetaZeroWidth_le_of_finiteHead_pure_quadratic_heat`,
   `zetaZeroWidth_le_iff_forall_pos_taylor_forwardPolyHeat_finiteHead_nonneg`):**
   Passing directly through the retained finite polynomial `sliceTruncPoly t (xiSliceGaussianRadiusHead t R)`
   eliminates both the three-radii `log(3/δ)` loss and the `t ≥ e^{16}` barrier of the full-slice
   Hermite detector: for any fixed `R ∈ [1/2, 1]`, finite-head heat positivity at the pure quadratic
   rate `0 ≤ λ(t) ≤ δ₀² / (320 log(180|t|))` on `|t| ≥ 73/5` forces `zetaZeroWidth ≤ δ₀` across all
   heights.  Unconditionally removing `Ξ(t) ≠ 0` from `sliceTruncPoly` gives the exact equivalence
   between `zetaZeroWidth ≤ σ`, unheated shifted finite-head positivity at `σ`, and small-heat
   shifted finite-head positivity at `σ`.
3. **Prime–Cesàro Explicit Formula for the Retained Finite-Head Coefficients
   (`xiSliceGaussianFiniteHead_eq_XiC_sq_mul_eval_sliceTruncPoly`,
   `coeff_one_sliceTruncPoly_radius_eq_sum_re`, `coeff_one_sliceTruncPoly_radius_eq_cesaro`):**
   The linear coefficient `[y¹] sliceTruncPoly t H` (`H = xiSliceGaussianRadiusHead t R`) equals
   `∑_{q ∈ H} Re((z_q − t)⁻²)`.  At `Ξ(t) ≠ 0` and every `Y > 1`, combining this with the Laguerre
   explicit formula expresses `[y¹] sliceTruncPoly t H` directly through the archimedean digamma term,
   the Cesàro prime sum `D_Y(½ + it)`, the finite-head `Y`-twist, and the compensated `Y`-tail.
4. **Sharpened Global Ward Cap Horizon, Euler–Stieltjes Sum Rule, Reflection Doubling, and Corpus
   Zero-Width Dictionary (`re_xiWardZeroStieltjes_neg_of_offLine`,
   `tsum_xiWardZeroStieltjes_eq_im_logDeriv_xi`, `neg_re_xiWardZeroStieltjes_lt_lineConj`,
   `two_mul_xiWardRightStieltjesSum_le_euler_sub_critical`,
   `riemannHypothesis_iff_xiWardCriticalStieltjesSum_eq_euler`,
   `routeWD_and_corpus_zeroWidth_dictionary`):**
   Every zero copy has negative Ward–Stieltjes real part up to `τ = 32/5`, and every off-line zero
   copy up to `τ = 366/25` (`14.64`, sharpening `12`).  Summing over all zero copies yields
   `−8πτ ∑_q ((ρ_q + 1/100)² + τ²)⁻¹ = 8π Im(ξ'/ξ(101/100 + iτ))`.  Because the Ward poles lie left
   of the critical line (`−1/100 < 1/2`), reflecting a right-half-strip zero `ρ` to `1 − ρ̄` strictly
   increases `−Re(((ρ + 1/100)² + τ²)⁻¹)` on `(0, 366/25]`, bounding **twice** the Global Ward Cap by
   the deficit `8π Im(ξ'/ξ(101/100 + iτ)) − L_crit(τ)` and characterizing RH by critical-line
   saturation at any single `τ ∈ (0, 366/25]`.
-/

open Complex MeasureTheory Filter Topology Set Metric Polynomial Finset
open scoped ComplexOrder BigOperators
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.SquareRootThreshold

namespace RHTower

noncomputable section

/-! ## 1. Polynomial heat semigroup inversion, Hermite evaluation, and universal root obstruction -/

/-- `forwardPolyHeat` at time `0` is the identity on `ℝ[X]`. -/
theorem forwardPolyHeat_zero (p : ℝ[X]) : forwardPolyHeat 0 p = p := by
  unfold forwardPolyHeat
  rw [Finset.sum_range_succ']
  simp [zero_pow (Nat.succ_ne_zero _)]

/-- `forwardPolyHeat s 0 = 0`. -/
theorem forwardPolyHeat_zero_poly (s : ℝ) : forwardPolyHeat s 0 = 0 := by
  simpa using forwardPolyHeat_C s 0

/-- `forwardPolyHeat s` commutes with finite sums in `ℝ[X]`. -/
theorem forwardPolyHeat_finset_sum {ι : Type*} (s : ℝ) (A : Finset ι) (f : ι → ℝ[X]) :
    forwardPolyHeat s (∑ i ∈ A, f i) = ∑ i ∈ A, forwardPolyHeat s (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [forwardPolyHeat_zero_poly]
  | insert a A ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, forwardPolyHeat_add, ih]

/-- `polyHeat τ p = forwardPolyHeat (-τ) p`. -/
theorem polyHeat_eq_forwardPolyHeat (τ : ℝ) (p : ℝ[X]) :
    polyHeat τ p = forwardPolyHeat (-τ) p := by
  rw [forwardPolyHeat_eq_polyHeat, neg_neg]

private theorem forwardPolyHeat_forwardPolyHeat_X_pow (s₁ s₂ : ℝ) :
    ∀ n : ℕ, forwardPolyHeat s₁ (forwardPolyHeat s₂ (X ^ n)) =
      forwardPolyHeat (s₁ + s₂) (X ^ n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · simp [forwardPolyHeat_one]
    · have ih_n : forwardPolyHeat s₁ (forwardPolyHeat s₂ (X ^ n)) =
          forwardPolyHeat (s₁ + s₂) (X ^ n) := ih n (Nat.lt_succ_self n)
      have ih_deriv : forwardPolyHeat s₁ (forwardPolyHeat s₂ (derivative (X ^ n))) =
          forwardPolyHeat (s₁ + s₂) (derivative (X ^ n)) := by
        rcases n with _ | m
        · simp [forwardPolyHeat_zero_poly]
        · rw [derivative_X_pow, Nat.add_sub_cancel, forwardPolyHeat_C_mul, forwardPolyHeat_C_mul,
            forwardPolyHeat_C_mul, ih m (by omega)]
      rw [pow_succ', forwardPolyHeat_X_mul, forwardPolyHeat_add, forwardPolyHeat_X_mul,
        forwardPolyHeat_C_mul, derivative_forwardPolyHeat s₂, ih_deriv, ih_n,
        ← derivative_forwardPolyHeat (s₁ + s₂), forwardPolyHeat_X_mul, mul_add, C_add]
      ring

/-- **Semigroup law for `forwardPolyHeat`.**  For all `s₁, s₂ ∈ ℝ` and `p ∈ ℝ[X]`,
`e^{s₁ D²}(e^{s₂ D²} p) = e^{(s₁ + s₂) D²} p`. -/
theorem forwardPolyHeat_forwardPolyHeat (s₁ s₂ : ℝ) (p : ℝ[X]) :
    forwardPolyHeat s₁ (forwardPolyHeat s₂ p) = forwardPolyHeat (s₁ + s₂) p := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  conv_rhs => rw [p.as_sum_range_C_mul_X_pow]
  rw [forwardPolyHeat_finset_sum, forwardPolyHeat_finset_sum, forwardPolyHeat_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [forwardPolyHeat_C_mul, forwardPolyHeat_C_mul, forwardPolyHeat_C_mul,
    forwardPolyHeat_forwardPolyHeat_X_pow]

/-- **Exact backward-heat inversion.**  `polyHeat s (forwardPolyHeat s p) = p` for all `s ∈ ℝ`
and `p ∈ ℝ[X]`. -/
theorem polyHeat_forwardPolyHeat (s : ℝ) (p : ℝ[X]) :
    polyHeat s (forwardPolyHeat s p) = p := by
  rw [polyHeat_eq_forwardPolyHeat, forwardPolyHeat_forwardPolyHeat, neg_add_cancel,
    forwardPolyHeat_zero]

/-- **Exact forward-heat inversion.**  `forwardPolyHeat s (polyHeat s p) = p` for all `s ∈ ℝ`
and `p ∈ ℝ[X]`. -/
theorem forwardPolyHeat_polyHeat (s : ℝ) (p : ℝ[X]) :
    forwardPolyHeat s (polyHeat s p) = p := by
  rw [polyHeat_eq_forwardPolyHeat, forwardPolyHeat_forwardPolyHeat, add_neg_cancel,
    forwardPolyHeat_zero]

/-- Forward heat never increases `natDegree`. -/
theorem natDegree_forwardPolyHeat_le (s : ℝ) (p : ℝ[X]) :
    (forwardPolyHeat s p).natDegree ≤ p.natDegree := by
  unfold forwardPolyHeat
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  exact (natDegree_C_mul_le _ _).trans ((natDegree_iterate_derivative _ _).trans (Nat.sub_le _ _))

/-- The scaled probabilists' Hermite polynomial `λ^{N/2} He_N(X / √λ)` in `ℝ[X]`. -/
def scaledHermitePoly (lam : ℝ) (N : ℕ) : ℝ[X] :=
  C (Real.sqrt lam ^ N) * ((hermite N).map (algebraMap ℤ ℝ)).comp (C (Real.sqrt lam)⁻¹ * X)

/-- Evaluating `scaledHermitePoly lam N` at `δ` gives `sliceHermiteWeight lam δ N`. -/
theorem eval_scaledHermitePoly (lam δ : ℝ) (N : ℕ) :
    (scaledHermitePoly lam N).eval δ = DeBruijn.sliceHermiteWeight lam δ N := by
  unfold scaledHermitePoly DeBruijn.sliceHermiteWeight
  rw [eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X, aeval_def, ← eval_map,
    div_eq_inv_mul]

/-- **Monomial backward-heat identity.**  For `λ > 0` and every `N : ℕ`,
`polyHeat (λ / 2) (X ^ N) = scaledHermitePoly λ N`. -/
theorem polyHeat_X_pow_eq_scaledHermitePoly {lam : ℝ} (hlam : 0 < lam) (N : ℕ) :
    polyHeat (lam / 2) (X ^ N) = scaledHermitePoly lam N := by
  set s := Real.sqrt lam with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hlam
  have hs0 : s ≠ 0 := hs_pos.ne'
  have hs_sq : s * s = lam := Real.mul_self_sqrt hlam.le
  induction N with
  | zero =>
    rw [pow_zero, polyHeat_eq_forwardPolyHeat, forwardPolyHeat_one]
    simp [scaledHermitePoly, hermite_zero]
  | succ N ih =>
    set H : ℝ[X] := (hermite N).map (algebraMap ℤ ℝ)
    set u : ℝ[X] := C s⁻¹ * X
    have hinv_cancel : s⁻¹ * s = 1 := inv_mul_cancel₀ hs0
    have hmul_inv : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
    have hHcomp : H.comp u = C (s⁻¹ ^ N) * polyHeat (lam / 2) (X ^ N) := by
      rw [ih, scaledHermitePoly, ← mul_assoc, ← C_mul, ← mul_pow, hinv_cancel, one_pow, C_1,
        one_mul]
    have hderiv_u : derivative u = C s⁻¹ := by
      simp [u]
    have hderiv_comp : C (s ^ (N + 1)) * (derivative H).comp u =
        C lam * derivative (polyHeat (lam / 2) (X ^ N)) := by
      have hd := congrArg derivative hHcomp
      rw [derivative_comp, hderiv_u, derivative_C_mul] at hd
      have hd' := congrArg (fun q => C (s ^ (N + 1) * s) * q) hd
      have hLHS : C (s ^ (N + 1) * s) * (C s⁻¹ * (derivative H).comp u) =
          C (s ^ (N + 1)) * (derivative H).comp u := by
        rw [← mul_assoc, ← C_mul, mul_assoc (s ^ (N + 1)) s s⁻¹, hmul_inv, mul_one]
      have hRHS : C (s ^ (N + 1) * s) * (C (s⁻¹ ^ N) * derivative (polyHeat (lam / 2) (X ^ N))) =
          C lam * derivative (polyHeat (lam / 2) (X ^ N)) := by
        rw [← mul_assoc, ← C_mul]
        congr 1
        rw [pow_succ, show s ^ N * s * s * s⁻¹ ^ N = (s * s⁻¹) ^ N * (s * s) by ring,
          hmul_inv, one_pow, one_mul, hs_sq]
      rw [hLHS, hRHS] at hd'
      exact hd'
    have hmap_succ : (hermite (N + 1)).map (algebraMap ℤ ℝ) = X * H - derivative H := by
      rw [hermite_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
        Polynomial.derivative_map]
    have hscaled_succ : scaledHermitePoly lam (N + 1) =
        X * polyHeat (lam / 2) (X ^ N) - C lam * derivative (polyHeat (lam / 2) (X ^ N)) := by
      unfold scaledHermitePoly
      rw [← hs_def, hmap_succ, sub_comp, mul_comp, X_comp, mul_sub, hderiv_comp, ih]
      unfold scaledHermitePoly
      rw [← hs_def]
      congr 1
      calc C (s ^ (N + 1)) * (C s⁻¹ * X * H.comp u)
          = (C (s ^ (N + 1)) * C s⁻¹) * X * H.comp u := by ring
        _ = C (s ^ N) * X * H.comp u := by
            rw [← C_mul, pow_succ, mul_assoc (s ^ N) s s⁻¹, hmul_inv, mul_one]
        _ = X * (C (s ^ N) * H.comp u) := by ring
    rw [hscaled_succ, pow_succ', polyHeat_eq_forwardPolyHeat, forwardPolyHeat_X_mul,
      ← polyHeat_eq_forwardPolyHeat]
    have h2 : C (2 * -(lam / 2)) = -C lam := by
      rw [← C_neg]; congr 1; ring
    rw [h2]
    ring

/-- **Exact Hermite evaluation of `polyHeat`.**  For `λ > 0`, `δ ∈ ℝ`, and any polynomial `Q ∈ ℝ[X]`,
`(polyHeat (λ / 2) Q).eval δ = ∑_{N ≤ deg Q} Q.coeff N · sliceHermiteWeight λ δ N`. -/
theorem eval_polyHeat_eq_sum_hermiteWeight {lam : ℝ} (hlam : 0 < lam) (δ : ℝ) (Q : ℝ[X]) :
    (polyHeat (lam / 2) Q).eval δ =
      ∑ N ∈ range (Q.natDegree + 1), Q.coeff N * DeBruijn.sliceHermiteWeight lam δ N := by
  conv_lhs => rw [Q.as_sum_range_C_mul_X_pow]
  rw [polyHeat_eq_forwardPolyHeat, forwardPolyHeat_finset_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [forwardPolyHeat_C_mul, ← polyHeat_eq_forwardPolyHeat, polyHeat_X_pow_eq_scaledHermitePoly hlam,
    eval_mul, eval_C, eval_scaledHermitePoly]

/-- A nonzero polynomial with nonnegative coefficients is strictly positive at every `δ > 0`. -/
theorem eval_pos_of_coeffNonneg {P : ℝ[X]} (hP : P ≠ 0) (hnn : CoeffNonneg P) {δ : ℝ}
    (hδ : 0 < δ) : 0 < P.eval δ := by
  rw [eval_eq_sum_range]
  have hmem : P.natDegree ∈ range (P.natDegree + 1) := mem_range.mpr (Nat.lt_succ_self _)
  have hlead_ne : P.coeff P.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have hlead_pos : 0 < P.coeff P.natDegree * δ ^ P.natDegree :=
    mul_pos (lt_of_le_of_ne (hnn P.natDegree) hlead_ne.symm) (pow_pos hδ _)
  exact lt_of_lt_of_le hlead_pos
    (Finset.single_le_sum (fun i _ => mul_nonneg (hnn i) (pow_nonneg hδ.le i)) hmem)

/-- **Universal finite-degree root obstruction to polynomial heat positivity.**
If `P ∈ ℝ[X]` is nonzero and vanishes at `δ > 0`, then `forwardPolyHeat (λ / 2) P` cannot have
all nonnegative coefficients whenever `0 ≤ λ` and `4 λ · deg P ≤ δ²`. -/
theorem not_coeffNonneg_forwardPolyHeat_of_eval_zero {P : ℝ[X]} (hP : P ≠ 0) {δ lam : ℝ}
    (hδ : 0 < δ) (hlam : 0 ≤ lam) (hz : P.eval δ = 0)
    (hdeg : 4 * lam * (P.natDegree : ℝ) ≤ δ ^ 2) :
    ¬ CoeffNonneg (forwardPolyHeat (lam / 2) P) := by
  intro hnn
  rcases eq_or_lt_of_le hlam with rfl | hlam_pos
  · rw [zero_div, forwardPolyHeat_zero] at hnn
    exact (eval_pos_of_coeffNonneg hP hnn hδ).ne' hz
  · set Q := forwardPolyHeat (lam / 2) P with hQ_def
    have hPQ : polyHeat (lam / 2) Q = P := polyHeat_forwardPolyHeat (lam / 2) P
    have hQ_ne : Q ≠ 0 := by
      intro h0
      apply hP
      rw [← hPQ, h0, polyHeat_eq_forwardPolyHeat, forwardPolyHeat_zero_poly]
    have hQdeg : Q.natDegree ≤ P.natDegree := natDegree_forwardPolyHeat_le (lam / 2) P
    have heval : 0 = ∑ N ∈ range (Q.natDegree + 1),
        Q.coeff N * DeBruijn.sliceHermiteWeight lam δ N := by
      rw [← eval_polyHeat_eq_sum_hermiteWeight hlam_pos δ Q, hPQ, hz]
    have hterm_nn : ∀ N ∈ range (Q.natDegree + 1),
        0 ≤ Q.coeff N * DeBruijn.sliceHermiteWeight lam δ N := by
      intro N hN
      have hNP : (N : ℝ) ≤ P.natDegree := by
        exact_mod_cast (Nat.lt_succ_iff.mp (mem_range.mp hN)).trans hQdeg
      have hw := DeBruijn.hermiteWeight_ge hlam_pos hδ.le (N := N) (by nlinarith)
      exact mul_nonneg (hnn N) (le_trans (pow_nonneg (half_pos hδ).le N) hw)
    have hmem : Q.natDegree ∈ range (Q.natDegree + 1) := mem_range.mpr (Nat.lt_succ_self _)
    have hQP : (Q.natDegree : ℝ) ≤ P.natDegree := by exact_mod_cast hQdeg
    have hw_top := DeBruijn.hermiteWeight_ge hlam_pos hδ.le (N := Q.natDegree) (by nlinarith)
    have hlead_pos : 0 < Q.coeff Q.natDegree :=
      lt_of_le_of_ne (hnn Q.natDegree) (leadingCoeff_ne_zero.mpr hQ_ne).symm
    have htop_pos : 0 < Q.coeff Q.natDegree * DeBruijn.sliceHermiteWeight lam δ Q.natDegree :=
      mul_pos hlead_pos (lt_of_lt_of_le (pow_pos (half_pos hδ) _) hw_top)
    have hsum_pos : 0 < ∑ N ∈ range (Q.natDegree + 1),
        Q.coeff N * DeBruijn.sliceHermiteWeight lam δ N :=
      lt_of_lt_of_le htop_pos (Finset.single_le_sum hterm_nn hmem)
    linarith

/-- **Shifted finite-degree root obstruction to polynomial heat positivity.**
If `P ∈ ℝ[X]` is nonzero and vanishes at `δ > σ ≥ 0`, then `taylor σ (forwardPolyHeat (λ / 2) P)`
cannot have nonnegative coefficients whenever `0 ≤ λ` and `4 λ · deg P ≤ (δ − σ)²`. -/
theorem not_coeffNonneg_taylor_forwardPolyHeat_of_eval_zero {P : ℝ[X]} (hP : P ≠ 0)
    {σ δ lam : ℝ} (hσδ : σ < δ) (hlam : 0 ≤ lam) (hz : P.eval δ = 0)
    (hdeg : 4 * lam * (P.natDegree : ℝ) ≤ (δ - σ) ^ 2) :
    ¬ CoeffNonneg (taylor σ (forwardPolyHeat (lam / 2) P)) := by
  rw [← forwardPolyHeat_taylor]
  have hPσ_ne : taylor σ P ≠ 0 := by
    intro h0
    apply leadingCoeff_ne_zero.mpr hP
    rw [← leadingCoeff_taylor σ, h0, leadingCoeff_zero]
  have hev : (taylor σ P).eval (δ - σ) = 0 := by
    rw [taylor_apply, eval_comp, eval_add, eval_X, eval_C, sub_add_cancel, hz]
  refine not_coeffNonneg_forwardPolyHeat_of_eval_zero hPσ_ne (sub_pos.mpr hσδ) hlam hev ?_
  rwa [natDegree_taylor]

/-! ## 2. Multiplicity-sharp finite-head detection, pure-quadratic strip law, and graded width equivalence -/

/-- The spectral-radius head `xiSliceGaussianRadiusHead t R` is invariant under
`xiZeroCopyLineConjEquiv`. -/
theorem mem_xiSliceGaussianRadiusHead_lineConj_iff (t R : ℝ) (q : XiZeroCopy) :
    xiZeroCopyLineConjEquiv q ∈ xiSliceGaussianRadiusHead t R ↔
      q ∈ xiSliceGaussianRadiusHead t R := by
  rw [mem_xiSliceGaussianRadiusHead, mem_xiSliceGaussianRadiusHead, xiSpectralPoint_lineConj]
  have hc : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by simp
  rw [← hc, ← map_sub, Complex.norm_conj, hc]

/-- Because `xiSliceGaussianRadiusHead t R` is closed under critical-line conjugation, its
symmetric truncation equals itself. -/
theorem sliceTrunc_xiSliceGaussianRadiusHead (t R : ℝ) :
    sliceTrunc (xiSliceGaussianRadiusHead t R) = xiSliceGaussianRadiusHead t R := by
  classical
  set H := xiSliceGaussianRadiusHead t R
  ext q
  simp only [sliceTrunc, Finset.mem_union, mem_sliceTruncCrit, mem_sliceTruncUp, Finset.mem_map,
    Equiv.coe_toEmbedding]
  constructor
  · rintro ((⟨hq, -⟩ | ⟨hq, -⟩) | ⟨r, ⟨hr, -⟩, rfl⟩)
    · exact hq
    · exact hq
    · exact (mem_xiSliceGaussianRadiusHead_lineConj_iff t R r).mpr hr
  · intro hq
    rcases lt_trichotomy (xiSpectralPoint q).im 0 with hlt | heq | hgt
    · right
      refine ⟨xiZeroCopyLineConjEquiv.symm q, ⟨?_, ?_⟩, Equiv.apply_symm_apply _ _⟩
      · exact (mem_xiSliceGaussianRadiusHead_lineConj_iff t R _).mp
          (by rwa [Equiv.apply_symm_apply])
      · unfold XiCopyUpper
        have hs := im_xiSpectralPoint_lineConj (xiZeroCopyLineConjEquiv.symm q)
        rw [Equiv.apply_symm_apply] at hs
        linarith
    · exact Or.inl (Or.inl ⟨hq, heq⟩)
    · exact Or.inl (Or.inr ⟨hq, hgt⟩)

/-- Exact cardinality partition of any symmetric truncation `sliceTrunc S`. -/
theorem card_sliceTrunc (S : Finset XiZeroCopy) :
    (sliceTrunc S).card = (sliceTruncCrit S).card + 2 * (sliceTruncUp S).card := by
  classical
  have hd1 : Disjoint (sliceTruncCrit S) (sliceTruncUp S) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    have h1' := (mem_sliceTruncCrit.mp h1).2
    have h2' := (mem_sliceTruncUp.mp h2).2
    unfold XiCopyCritical XiCopyUpper at *
    linarith
  have hd2 : Disjoint (sliceTruncCrit S ∪ sliceTruncUp S)
      ((sliceTruncUp S).map xiZeroCopyLineConjEquiv.toEmbedding) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp h2
    have hup := (mem_sliceTruncUp.mp hr).2
    unfold XiCopyUpper at hup
    simp only [Equiv.coe_toEmbedding] at h1
    have him := im_xiSpectralPoint_lineConj r
    rcases Finset.mem_union.mp h1 with h | h
    · have hc := (mem_sliceTruncCrit.mp h).2
      unfold XiCopyCritical at hc
      linarith
    · have hu := (mem_sliceTruncUp.mp h).2
      unfold XiCopyUpper at hu
      linarith
  unfold sliceTrunc
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, Finset.card_map]
  omega

/-- Every `sliceTruncPoly t S` evaluates to `1` at `0`. -/
theorem eval_zero_sliceTruncPoly (t : ℝ) (S : Finset XiZeroCopy) :
    (sliceTruncPoly t S).eval 0 = 1 := by
  unfold sliceTruncPoly
  rw [eval_mul, eval_prod, eval_prod]
  have h1 : ∀ q ∈ sliceTruncCrit S, (1 + C (sliceAtom t q) * X).eval 0 = 1 := fun _ _ => by simp
  have h2 : ∀ q ∈ sliceTruncUp S,
      ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X).eval 0 = 1 :=
    fun _ _ => by simp
  rw [Finset.prod_eq_one h1, Finset.prod_eq_one h2, mul_one]

/-- Every `expand ℝ 2 (sliceTruncPoly t S)` evaluates to `1` at `0`, hence is nonzero without any
nonvanishing hypothesis on `Ξ(t)`. -/
theorem expand_sliceTruncPoly_ne_zero (t : ℝ) (S : Finset XiZeroCopy) :
    expand ℝ 2 (sliceTruncPoly t S) ≠ 0 := by
  intro h0
  have hev : (expand ℝ 2 (sliceTruncPoly t S)).eval 0 = 1 := by
    rw [expand_eval, zero_pow (by decide : 2 ≠ 0), eval_zero_sliceTruncPoly]
  rw [h0, eval_zero] at hev
  exact zero_ne_one hev

private theorem natDegree_one_add_C_mul_X_le (a : ℝ) :
    (1 + C a * X : ℝ[X]).natDegree ≤ 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_add, ← C_1, coeff_C, coeff_C_mul, coeff_X, if_neg (by omega), if_neg (by omega),
    mul_zero, add_zero]

private theorem natDegree_one_add_C_mul_X_add_C_mul_X_sq_le (b c : ℝ) :
    (1 + C b * X + C c * X ^ 2 : ℝ[X]).natDegree ≤ 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_add, coeff_add, ← C_1, coeff_C, coeff_C_mul, coeff_X, coeff_C_mul, coeff_X_pow,
    if_neg (by omega), if_neg (by omega), if_neg (by omega), mul_zero, mul_zero, add_zero,
    add_zero]

private theorem natDegree_prod_le_card_mul (A : Finset XiZeroCopy) (f : XiZeroCopy → ℝ[X]) (d : ℕ)
    (hf : ∀ q ∈ A, (f q).natDegree ≤ d) :
    (∏ q ∈ A, f q).natDegree ≤ d * A.card := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    have hcard : (insert a A).card = A.card + 1 := by simp [ha]
    rw [Finset.prod_insert ha, hcard, Nat.mul_add, Nat.mul_one]
    have ha_le : (f a).natDegree ≤ d := hf a (Finset.mem_insert_self a A)
    have hA_le : (∏ q ∈ A, f q).natDegree ≤ d * A.card :=
      ih fun q hq => hf q (Finset.mem_insert_of_mem hq)
    have hmul : (f a * ∏ q ∈ A, f q).natDegree ≤ (f a).natDegree + (∏ q ∈ A, f q).natDegree :=
      @Polynomial.natDegree_mul_le ℝ _ (f a) (∏ q ∈ A, f q)
    omega

/-- Degree bound for `sliceTruncPoly t S`: `(sliceTruncPoly t S).natDegree ≤ (sliceTrunc S).card`. -/
theorem natDegree_sliceTruncPoly_le (t : ℝ) (S : Finset XiZeroCopy) :
    (sliceTruncPoly t S).natDegree ≤ (sliceTrunc S).card := by
  rw [card_sliceTrunc]
  unfold sliceTruncPoly
  have h1 : (∏ q ∈ sliceTruncCrit S, (1 + C (sliceAtom t q) * X)).natDegree ≤
      1 * (sliceTruncCrit S).card :=
    natDegree_prod_le_card_mul (sliceTruncCrit S) _ 1 fun q _ =>
      natDegree_one_add_C_mul_X_le (sliceAtom t q)
  have h2 : (∏ q ∈ sliceTruncUp S,
      ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X)).natDegree ≤
      2 * (sliceTruncUp S).card :=
    natDegree_prod_le_card_mul (sliceTruncUp S) _ 2 fun q _ => by
      rw [DeBruijn.slicePairFactor_eq]
      exact natDegree_one_add_C_mul_X_add_C_mul_X_sq_le _ _
  have hmul : ((∏ q ∈ sliceTruncCrit S, (1 + C (sliceAtom t q) * X)) *
      ∏ q ∈ sliceTruncUp S,
        ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X)).natDegree ≤
      (∏ q ∈ sliceTruncCrit S, (1 + C (sliceAtom t q) * X)).natDegree +
        (∏ q ∈ sliceTruncUp S,
          ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X)).natDegree :=
    @Polynomial.natDegree_mul_le ℝ _ _ _
  omega

/-- For the radius head `H = xiSliceGaussianRadiusHead t R`, `expand ℝ 2 (sliceTruncPoly t H)` has
degree at most `2 * H.card`. -/
theorem natDegree_expand_sliceTruncPoly_radius_le (t R : ℝ) :
    (expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R))).natDegree ≤
      2 * (xiSliceGaussianRadiusHead t R).card := by
  rw [natDegree_expand, mul_comm]
  exact Nat.mul_le_mul_left 2
    ((natDegree_sliceTruncPoly_le t _).trans_eq
      (congrArg Finset.card (sliceTrunc_xiSliceGaussianRadiusHead t R)))

/-- Any off-line zero `ξ(ρ) = 0` with `δ = |Re ρ − 1/2| > 0` and `δ ≤ R` produces an upper spectral
zero copy in `xiSliceGaussianRadiusHead (Im ρ) R` where `expand ℝ 2 (sliceTruncPoly (Im ρ) H)`
vanishes at `δ`. -/
theorem eval_expand_sliceTruncPoly_eq_zero_of_offLine {ρ : ℂ} (hxi : xi ρ = 0) {R : ℝ}
    (hδ_pos : 0 < |ρ.re - 1 / 2|) (hδR : |ρ.re - 1 / 2| ≤ R) :
    (expand ℝ 2 (sliceTruncPoly ρ.im (xiSliceGaussianRadiusHead ρ.im R))).eval |ρ.re - 1 / 2| =
      0 := by
  classical
  set t := ρ.im
  set δ := |ρ.re - 1 / 2|
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  have hre₁ : (xiSpectralPoint q₁).re = t := by
    simp [xiSpectralPoint, hq₁, t]
  have him₁ : (xiSpectralPoint q₁).im = 1 / 2 - ρ.re := by
    simp [xiSpectralPoint, hq₁]
  have hexists : ∃ q₀ : XiZeroCopy,
      (xiSpectralPoint q₀).re = t ∧ (xiSpectralPoint q₀).im = δ := by
    rcases lt_or_ge ρ.re (1 / 2) with hlt | hge
    · refine ⟨q₁, hre₁, ?_⟩
      have habs : δ = 1 / 2 - ρ.re := by
        simp only [δ]
        rw [abs_of_neg (by linarith)]
        ring
      rw [him₁, habs]
    · refine ⟨xiZeroCopyLineConjEquiv q₁, ?_, ?_⟩
      · rw [xiSpectralPoint_lineConj, Complex.conj_re, hre₁]
      · rw [xiSpectralPoint_lineConj, Complex.conj_im, him₁]
        have habs : δ = ρ.re - 1 / 2 := abs_of_nonneg (by linarith)
        linarith
  obtain ⟨q₀, hre₀, him₀⟩ := hexists
  have hsub : xiSpectralPoint q₀ - (t : ℂ) = (δ : ℂ) * I := by
    apply Complex.ext <;> simp [hre₀, him₀]
  have hnorm : ‖xiSpectralPoint q₀ - (t : ℂ)‖ = δ := by
    rw [hsub, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos hδ_pos]
  have hmemH : q₀ ∈ xiSliceGaussianRadiusHead t R :=
    (mem_xiSliceGaussianRadiusHead t R q₀).mpr (hnorm.trans_le hδR)
  have hmemUp : q₀ ∈ sliceTruncUp (xiSliceGaussianRadiusHead t R) :=
    mem_sliceTruncUp.mpr ⟨hmemH, by unfold XiCopyUpper; linarith⟩
  have hatom : sliceAtom t q₀ = 1 / δ ^ 2 := by
    unfold sliceAtom; rw [hnorm]
  have hdef : sliceDefect t q₀ = 1 / δ ^ 2 := by
    unfold sliceDefect
    rw [him₀, hnorm]
    have hδ2 : δ ^ 2 ≠ 0 := pow_ne_zero 2 hδ_pos.ne'
    field_simp
  rw [expand_eval, sliceTruncPoly, eval_mul, eval_prod, eval_prod]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hmemUp ?_)
  simp only [eval_sub, eval_pow, eval_add, eval_one, eval_mul, eval_C, eval_X, hatom, hdef]
  have hδ2 : δ ^ 2 ≠ 0 := pow_ne_zero 2 hδ_pos.ne'
  rw [mul_assoc 4, div_mul_cancel₀ 1 hδ2]
  norm_num

/-- **Multiplicity-sharp shifted finite-head detection.**
If `ξ(ρ) = 0` with `σ < δ := |Re ρ − 1/2| ≤ R`, then for every `λ ≥ 0` satisfying
`8 λ · |xiSliceGaussianRadiusHead (Im ρ) R| ≤ (δ − σ)²`, the shifted heated finite-head polynomial
fails `CoeffNonneg`. -/
theorem not_coeffNonneg_taylor_forwardPolyHeat_finiteHead_of_offLine_zero {ρ : ℂ} (hxi : xi ρ = 0)
    {σ R lam : ℝ} (hσ : 0 ≤ σ) (hσδ : σ < |ρ.re - 1 / 2|) (hδR : |ρ.re - 1 / 2| ≤ R)
    (hlam : 0 ≤ lam)
    (hcard : 8 * lam * ((xiSliceGaussianRadiusHead ρ.im R).card : ℝ) ≤ (|ρ.re - 1 / 2| - σ) ^ 2) :
    ¬ CoeffNonneg (taylor σ (forwardPolyHeat (lam / 2)
        (expand ℝ 2 (sliceTruncPoly ρ.im (xiSliceGaussianRadiusHead ρ.im R))))) := by
  have hδ_pos : 0 < |ρ.re - 1 / 2| := lt_of_le_of_lt hσ hσδ
  have hdeg_nat := natDegree_expand_sliceTruncPoly_radius_le ρ.im R
  have hdeg_real :
      ((expand ℝ 2 (sliceTruncPoly ρ.im (xiSliceGaussianRadiusHead ρ.im R))).natDegree : ℝ) ≤
        2 * ((xiSliceGaussianRadiusHead ρ.im R).card : ℝ) := by
    exact_mod_cast hdeg_nat
  refine not_coeffNonneg_taylor_forwardPolyHeat_of_eval_zero
    (expand_sliceTruncPoly_ne_zero ρ.im _) hσδ hlam
    (eval_expand_sliceTruncPoly_eq_zero_of_offLine hxi hδ_pos hδR) ?_
  nlinarith

/-- Unshifted (`σ = 0`) multiplicity-sharp finite-head detection at `8 λ · |H| ≤ δ²`. -/
theorem not_coeffNonneg_forwardPolyHeat_finiteHead_of_offLine_zero {ρ : ℂ} (hxi : xi ρ = 0)
    {R lam : ℝ} (hδ_pos : 0 < |ρ.re - 1 / 2|) (hδR : |ρ.re - 1 / 2| ≤ R) (hlam : 0 ≤ lam)
    (hcard : 8 * lam * ((xiSliceGaussianRadiusHead ρ.im R).card : ℝ) ≤ |ρ.re - 1 / 2| ^ 2) :
    ¬ CoeffNonneg (forwardPolyHeat (lam / 2)
        (expand ℝ 2 (sliceTruncPoly ρ.im (xiSliceGaussianRadiusHead ρ.im R)))) := by
  intro hnn
  apply not_coeffNonneg_taylor_forwardPolyHeat_finiteHead_of_offLine_zero hxi le_rfl hδ_pos hδR
    hlam (by simpa using hcard)
  intro n
  have h := hnn n
  simpa [taylor_zero] using h

/-- For `|t| ≥ 4` and `R ≤ 1`, the spectral-radius head `xiSliceGaussianRadiusHead t R` has
cardinality at most `40 log(180|t|)`. -/
theorem card_xiSliceGaussianRadiusHead_le {t R : ℝ} (ht : 4 ≤ |t|) (hR1 : R ≤ 1) :
    ((xiSliceGaussianRadiusHead t R).card : ℝ) ≤ 40 * Real.log (180 * |t|) := by
  refine card_le_of_ordinates_in_window ht _ fun q hq => ?_
  have hnorm : ‖xiSpectralPoint q - (t : ℂ)‖ ≤ R := (mem_xiSliceGaussianRadiusHead t R q).mp hq
  have hre : |(q.1 : ℂ).im - t| ≤ ‖xiSpectralPoint q - (t : ℂ)‖ := by
    have h := Complex.abs_re_le_norm (xiSpectralPoint q - (t : ℂ))
    have hspec : (xiSpectralPoint q - (t : ℂ)).re = (q.1 : ℂ).im - t := by
      simp [xiSpectralPoint]
    rwa [hspec] at h
  exact hre.trans (hnorm.trans hR1)

/-- **All-height `log(1/δ)`-free pure-quadratic strip law on the retained finite head.**
Let `0 ≤ δ₀` and `1/2 ≤ R ≤ 1`.  If for every real height `t` with `|t| ≥ 73/5` there exists a heat
parameter `0 ≤ λ ≤ δ₀² / (320 log(180|t|))` at which the retained finite-head polynomial
`forwardPolyHeat (λ / 2) (expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)))` has
nonnegative coefficients, then `zetaZeroWidth ≤ δ₀` unconditionally across all heights. -/
theorem zetaZeroWidth_le_of_finiteHead_pure_quadratic_heat {δ₀ R : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hR_lo : 1 / 2 ≤ R) (hR_hi : R ≤ 1)
    (hpos : ∀ t : ℝ, 73 / 5 ≤ |t| → ∃ lam : ℝ,
      0 ≤ lam ∧ lam ≤ δ₀ ^ 2 / (320 * Real.log (180 * |t|)) ∧
      CoeffNonneg (forwardPolyHeat (lam / 2)
        (expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R))))) :
    zetaZeroWidth ≤ δ₀ := by
  rw [zetaZeroWidth_le_iff_re_le hδ₀]
  intro ρ hρ
  obtain ⟨hζ, hre0, hre1⟩ : riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := hρ
  by_contra hlt
  push Not at hlt
  have hρ0 : ρ ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hre0; linarith
  have hρ1 : ρ ≠ 1 := by intro h1; rw [h1, Complex.one_re] at hre1; linarith
  have hxi : xi ρ = 0 := by
    rw [xi_eq_archFactor_mul_zeta hρ0 hρ1 (Gammaℝ_ne_zero_of_re_pos hre0), hζ, mul_zero]
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := by rw [hq]; linarith
  have him_sq := orderTwentyThreeOptimizedHeightSq_le_im_sq_of_xiZeroCopy_offLine q hoff
  rw [hq] at him_sq
  have ht73 : 73 / 5 ≤ |ρ.im| := by
    have hnum : (73 / 5 : ℝ) ^ 2 < xiOrderTwentyThreeOptimizedHeightSq := by
      norm_num [xiOrderTwentyThreeOptimizedHeightSq]
    have hsq : (73 / 5 : ℝ) ^ 2 < |ρ.im| ^ 2 := by
      rw [sq_abs]
      linarith
    nlinarith [abs_nonneg ρ.im]
  have ht4 : 4 ≤ |ρ.im| := by linarith
  have hlog_pos : 0 < Real.log (180 * |ρ.im|) := Real.log_pos (by linarith)
  obtain ⟨lam, hlam0, hlam_le, hnn⟩ := hpos ρ.im ht73
  have hcard := card_xiSliceGaussianRadiusHead_le (R := R) ht4 hR_hi
  have hδ_gt : δ₀ < |ρ.re - 1 / 2| := by
    rw [abs_of_pos (by linarith)]
    linarith
  have hδ_pos : 0 < |ρ.re - 1 / 2| := lt_of_le_of_lt hδ₀ hδ_gt
  have hδR : |ρ.re - 1 / 2| ≤ R := by
    rw [abs_of_pos (by linarith)]
    linarith [hre1]
  have hlam_mul : 320 * Real.log (180 * |ρ.im|) * lam ≤ δ₀ ^ 2 := by
    have hden : 0 < 320 * Real.log (180 * |ρ.im|) := by positivity
    exact (le_div_iff₀' hden).mp hlam_le
  have hstrict_sq : δ₀ ^ 2 < |ρ.re - 1 / 2| ^ 2 := by
    nlinarith
  have h8 : 8 * lam * ((xiSliceGaussianRadiusHead ρ.im R).card : ℝ) < |ρ.re - 1 / 2| ^ 2 := by
    have hstep : 8 * lam * ((xiSliceGaussianRadiusHead ρ.im R).card : ℝ) ≤
        8 * lam * (40 * Real.log (180 * |ρ.im|)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    linarith
  exact not_coeffNonneg_forwardPolyHeat_finiteHead_of_offLine_zero hxi hδ_pos hδR hlam0 h8.le hnn

/-- Every zero copy `q : XiZeroCopy` satisfies `|(Im z_q)| ≤ zetaZeroWidth`. -/
theorem abs_im_xiSpectralPoint_le_zetaZeroWidth (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| ≤ zetaZeroWidth := by
  have him : |(xiSpectralPoint q).im| = |(q.1 : ℂ).re - 1 / 2| := by
    have h : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
    rw [h, abs_neg]
  rw [him]
  exact abs_re_sub_half_le_zetaZeroWidth
    (CrossRouteReceiverBridges.xiZeroCopy_mem_zetaZeroConfig_carrier q)

/-- **Unconditional polynomial heat positivity of `sliceTruncPoly` at every height** (no `Ξ(t) ≠ 0`
needed, since every upper zero copy has `Im z_q > 0`, hence `z_q ≠ t`). -/
theorem coeffNonneg_taylor_forwardPolyHeat_sliceTruncPoly_all {t s r : ℝ}
    {S : Finset XiZeroCopy} (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hcone : ∀ q ∈ S, XiCopyUpper q →
      (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + r ^ 2 + 6 * s) :
    CoeffNonneg (taylor r (forwardPolyHeat s (expand ℝ 2 (sliceTruncPoly t S)))) := by
  classical
  unfold sliceTruncPoly
  rw [map_mul, map_prod, map_prod]
  refine coeffNonneg_taylor_forwardPolyHeat_mul hs r
    (coeffNonneg_taylor_forwardPolyHeat_prod hs r _ fun q _ => ?_)
    (coeffNonneg_taylor_forwardPolyHeat_prod hs r _ fun q hq => ?_)
  · exact DeBruijn.coeffNonneg_taylor_forwardPolyHeat_sliceLin hs
      (by unfold sliceAtom; positivity) hr
  · obtain ⟨hqS, hup⟩ := mem_sliceTruncUp.mp hq
    have hne : xiSpectralPoint q ≠ (t : ℂ) := by
      intro heq
      have him := congrArg Complex.im heq
      unfold XiCopyUpper at hup
      simp at him
      linarith
    exact DeBruijn.coeffNonneg_taylor_forwardPolyHeat_slicePair hs hr hne (hcone q hqS hup)

/-- **Exact unheated shifted finite-head characterization of `zetaZeroWidth ≤ σ`.**
For every `σ ≥ 0` and `R ≥ 1/2`, `zetaZeroWidth ≤ σ` holds iff for every `t ∈ ℝ`, the Taylor shift
at `σ` of `expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R))` has nonnegative
coefficients. -/
theorem zetaZeroWidth_le_iff_forall_taylor_finiteHead_nonneg {σ R : ℝ} (hσ : 0 ≤ σ)
    (hR : 1 / 2 ≤ R) :
    zetaZeroWidth ≤ σ ↔
      ∀ t : ℝ, CoeffNonneg (taylor σ
        (expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)))) := by
  constructor
  · intro hw t
    simpa [forwardPolyHeat_zero] using
      coeffNonneg_taylor_forwardPolyHeat_sliceTruncPoly_all (S := xiSliceGaussianRadiusHead t R)
        (t := t) (s := 0) (r := σ) le_rfl hσ fun q _ _ => by
          have habs := (abs_im_xiSpectralPoint_le_zetaZeroWidth q).trans hw
          have hsq : (xiSpectralPoint q).im ^ 2 ≤ σ ^ 2 := by
            rw [← sq_abs ((xiSpectralPoint q).im)]
            exact pow_le_pow_left₀ (abs_nonneg _) habs 2
          nlinarith [sq_nonneg ((xiSpectralPoint q).re - t)]
  · intro hall
    rw [zetaZeroWidth_le_iff_re_le hσ]
    intro ρ hρ
    obtain ⟨hζ, hre0, hre1⟩ : riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := hρ
    by_contra hlt
    push Not at hlt
    have hρ0 : ρ ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hre0; linarith
    have hρ1 : ρ ≠ 1 := by intro h1; rw [h1, Complex.one_re] at hre1; linarith
    have hxi : xi ρ = 0 := by
      rw [xi_eq_archFactor_mul_zeta hρ0 hρ1 (Gammaℝ_ne_zero_of_re_pos hre0), hζ, mul_zero]
    have hσδ : σ < |ρ.re - 1 / 2| := by
      rw [abs_of_pos (by linarith)]; linarith
    have hδR : |ρ.re - 1 / 2| ≤ R := by
      rw [abs_of_pos (by linarith)]; linarith [hre1]
    apply not_coeffNonneg_taylor_forwardPolyHeat_finiteHead_of_offLine_zero hxi hσ hσδ hδR
      (lam := 0) le_rfl (by rw [mul_zero, zero_mul]; exact sq_nonneg _)
    simpa [forwardPolyHeat_zero] using hall ρ.im

/-- **Exact small-heat shifted finite-head characterization of `zetaZeroWidth ≤ σ`.**
For every `σ ≥ 0` and `R ≥ 1/2`, `zetaZeroWidth ≤ σ` holds iff for every `λ > 0` and `t ∈ ℝ`,
`taylor σ (forwardPolyHeat (λ / 2) (expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R))))`
has nonnegative coefficients. -/
theorem zetaZeroWidth_le_iff_forall_pos_taylor_forwardPolyHeat_finiteHead_nonneg {σ R : ℝ}
    (hσ : 0 ≤ σ) (hR : 1 / 2 ≤ R) :
    zetaZeroWidth ≤ σ ↔
      ∀ lam > 0, ∀ t : ℝ, CoeffNonneg (taylor σ (forwardPolyHeat (lam / 2)
        (expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R))))) := by
  constructor
  · intro hw lam hlam t
    exact coeffNonneg_taylor_forwardPolyHeat_sliceTruncPoly_all (S := xiSliceGaussianRadiusHead t R)
      (t := t) (s := lam / 2) (r := σ) (by positivity) hσ fun q _ _ => by
        have habs := (abs_im_xiSpectralPoint_le_zetaZeroWidth q).trans hw
        have hsq : (xiSpectralPoint q).im ^ 2 ≤ σ ^ 2 := by
          rw [← sq_abs ((xiSpectralPoint q).im)]
          exact pow_le_pow_left₀ (abs_nonneg _) habs 2
        nlinarith [sq_nonneg ((xiSpectralPoint q).re - t)]
  · intro hall
    rw [zetaZeroWidth_le_iff_re_le hσ]
    intro ρ hρ
    obtain ⟨hζ, hre0, hre1⟩ : riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := hρ
    by_contra hlt
    push Not at hlt
    have hρ0 : ρ ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hre0; linarith
    have hρ1 : ρ ≠ 1 := by intro h1; rw [h1, Complex.one_re] at hre1; linarith
    have hxi : xi ρ = 0 := by
      rw [xi_eq_archFactor_mul_zeta hρ0 hρ1 (Gammaℝ_ne_zero_of_re_pos hre0), hζ, mul_zero]
    have hσδ : σ < |ρ.re - 1 / 2| := by
      rw [abs_of_pos (by linarith)]; linarith
    have hδR : |ρ.re - 1 / 2| ≤ R := by
      rw [abs_of_pos (by linarith)]; linarith [hre1]
    set Ccard : ℝ := ((xiSliceGaussianRadiusHead ρ.im R).card : ℝ)
    have hCcard : 0 ≤ Ccard := Nat.cast_nonneg _
    set lam : ℝ := (|ρ.re - 1 / 2| - σ) ^ 2 / (8 * (Ccard + 1))
    have hlam_pos : 0 < lam := div_pos (sq_pos_of_pos (sub_pos.mpr hσδ)) (by positivity)
    have hcard : 8 * lam * Ccard ≤ (|ρ.re - 1 / 2| - σ) ^ 2 := by
      have hden : 0 < 8 * (Ccard + 1) := by positivity
      calc 8 * lam * Ccard
          = (|ρ.re - 1 / 2| - σ) ^ 2 * (8 * Ccard) / (8 * (Ccard + 1)) := by
            simp only [lam]; ring
        _ ≤ (|ρ.re - 1 / 2| - σ) ^ 2 := by
            rw [div_le_iff₀ hden]
            nlinarith [sq_nonneg (|ρ.re - 1 / 2| - σ)]
    exact not_coeffNonneg_taylor_forwardPolyHeat_finiteHead_of_offLine_zero hxi hσ hσδ hδR
      hlam_pos.le hcard (hall lam hlam_pos ρ.im)

/-! ## 3. Exact Prime–Cesàro explicit formula for the retained finite-head coefficients -/

/-- At `Ξ(t) ≠ 0` and `R ≥ 0`, the retained finite-head entire function `xiSliceGaussianFiniteHead`
equals `Ξ(t)²` times `(sliceTruncPoly t (xiSliceGaussianRadiusHead t R))` evaluated at `z²`. -/
theorem xiSliceGaussianFiniteHead_eq_XiC_sq_mul_eval_sliceTruncPoly {t R : ℝ} (ht : XiC t ≠ 0)
    (hR : 0 ≤ R) (z : ℂ) :
    xiSliceGaussianFiniteHead t R z =
      XiC t ^ 2 * ((sliceTruncPoly t (xiSliceGaussianRadiusHead t R)).map
        (algebraMap ℝ ℂ)).eval (z ^ 2) := by
  set H := xiSliceGaussianRadiusHead t R
  have htail0 : xiSliceGaussianTail t H 0 = 1 := by
    unfold xiSliceGaussianTail
    simp
  have hhead0 : xiSliceGaussianFiniteHead t R 0 = XiC t ^ 2 := by
    have h0 := xiSliceProduct_eq_gaussianFiniteHead_mul_tail t hR 0
    rw [htail0, mul_one, xiSliceProduct_eq_XiC_mul] at h0
    simpa [sq] using h0.symm
  have hhead0_prod : xiSliceGaussianFiniteHeadScalar t R *
      ∏ q ∈ H, (xiSpectralPoint q - (t : ℂ)) ^ 2 = XiC t ^ 2 := by
    simpa [xiSliceGaussianFiniteHead, H] using hhead0
  have hfac : ∀ q ∈ H, z ^ 2 + (xiSpectralPoint q - (t : ℂ)) ^ 2 =
      (xiSpectralPoint q - (t : ℂ)) ^ 2 * (1 + sliceFactorTerm t q (I * z)) := by
    intro q _
    have hne : (xiSpectralPoint q - (t : ℂ)) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal ht q))
    unfold sliceFactorTerm
    have hIz : (I * z) ^ 2 = -z ^ 2 := by ring_nf; rw [I_sq]; ring
    rw [hIz, neg_div, neg_neg, mul_add, mul_one, mul_div_cancel₀ _ hne, add_comm]
  calc xiSliceGaussianFiniteHead t R z
      = xiSliceGaussianFiniteHeadScalar t R *
          ∏ q ∈ H, ((xiSpectralPoint q - (t : ℂ)) ^ 2 * (1 + sliceFactorTerm t q (I * z))) := by
        unfold xiSliceGaussianFiniteHead
        rw [Finset.prod_congr rfl hfac]
    _ = (xiSliceGaussianFiniteHeadScalar t R * ∏ q ∈ H, (xiSpectralPoint q - (t : ℂ)) ^ 2) *
          ∏ q ∈ sliceTrunc H, (1 + sliceFactorTerm t q (I * z)) := by
        rw [Finset.prod_mul_distrib, ← mul_assoc, sliceTrunc_xiSliceGaussianRadiusHead]
    _ = XiC t ^ 2 * ((sliceTruncPoly t H).map (algebraMap ℝ ℂ)).eval (z ^ 2) := by
        rw [hhead0_prod, prod_sliceTrunc_eq_eval ht H (I * z)]
        have hIz : -(I * z) ^ 2 = z ^ 2 := by ring_nf; rw [I_sq]; ring
        rw [hIz]

private theorem coeff_zero_and_one_prod {ι : Type*} (A : Finset ι) (f : ι → ℝ[X])
    (hf0 : ∀ i ∈ A, (f i).coeff 0 = 1) :
    (∏ i ∈ A, f i).coeff 0 = 1 ∧ (∏ i ∈ A, f i).coeff 1 = ∑ i ∈ A, (f i).coeff 1 := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [coeff_one]
  | insert a A ha ih =>
    obtain ⟨ih0, ih1⟩ := ih fun i hi => hf0 i (Finset.mem_insert_of_mem hi)
    have ha0 : (f a).coeff 0 = 1 := hf0 a (Finset.mem_insert_self a A)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    refine ⟨?_, ?_⟩
    · rw [mul_coeff_zero, ha0, ih0, mul_one]
    · rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
        Finset.sum_range_one]
      simp only [Nat.sub_zero, Nat.sub_self, ha0, ih0, one_mul, mul_one, ih1]
      ring

private theorem re_xiSliceGaussianReciprocal_eq (t : ℝ) (q : XiZeroCopy) :
    (xiSliceGaussianReciprocal t q).re = sliceAtom t q - 2 * sliceDefect t q := by
  set c : ℂ := xiSpectralPoint q - (t : ℂ) with hc_def
  by_cases hc : c = 0
  · have him : (xiSpectralPoint q).im = 0 := by
      have h := congrArg Complex.im hc
      simpa [hc_def] using h
    unfold xiSliceGaussianReciprocal sliceAtom sliceDefect
    rw [← hc_def, hc, him]
    simp
  · have hnorm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hnormSq : Complex.normSq c = ‖c‖ ^ 2 := Complex.normSq_eq_norm_sq c
    have hc2_re : (c ^ 2).re = c.re ^ 2 - c.im ^ 2 := by
      rw [sq, Complex.mul_re]; ring
    have hsum_sq : c.re ^ 2 + c.im ^ 2 = ‖c‖ ^ 2 := by
      rw [← hnormSq, Complex.normSq_apply]; ring
    have hc_im : c.im = (xiSpectralPoint q).im := by simp [hc_def]
    unfold xiSliceGaussianReciprocal sliceAtom sliceDefect
    rw [← hc_def, Complex.inv_re, map_pow, hnormSq, hc2_re, ← hc_im]
    have hn2 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm_pos.ne'
    have hn4 : (‖c‖ ^ 2) ^ 2 = ‖c‖ ^ 4 := by ring
    rw [hn4]
    field_simp
    nlinarith [hsum_sq]

/-- For every `t ∈ ℝ` and finite set `S`, `[y¹] sliceTruncPoly t S` is the exact real reciprocal-square
sum `∑_{q ∈ sliceTrunc S} Re((z_q − t)⁻²)`. -/
theorem coeff_one_sliceTruncPoly_eq_sum_re (t : ℝ) (S : Finset XiZeroCopy) :
    (sliceTruncPoly t S).coeff 1 = ∑ q ∈ sliceTrunc S, (xiSliceGaussianReciprocal t q).re := by
  classical
  obtain ⟨h0_crit, h1_crit⟩ := coeff_zero_and_one_prod (sliceTruncCrit S)
    (fun q => (1 + C (sliceAtom t q) * X : ℝ[X])) (fun q _ => by simp)
  obtain ⟨h0_up, h1_up⟩ := coeff_zero_and_one_prod (sliceTruncUp S)
    (fun q => ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X : ℝ[X]))
    (fun q _ => by rw [DeBruijn.slicePairFactor_eq]; simp)
  have h1_mul : (sliceTruncPoly t S).coeff 1 =
      (∑ q ∈ sliceTruncCrit S, sliceAtom t q) +
        ∑ q ∈ sliceTruncUp S, (2 * sliceAtom t q - 4 * sliceDefect t q) := by
    unfold sliceTruncPoly
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Finset.sum_range_one]
    simp only [Nat.sub_zero, Nat.sub_self, h0_crit, h0_up, one_mul, mul_one, h1_crit, h1_up]
    have hc1 : ∀ q ∈ sliceTruncCrit S, (1 + C (sliceAtom t q) * X : ℝ[X]).coeff 1 =
        sliceAtom t q := fun _ _ => by simp [coeff_one]
    have hu1 : ∀ q ∈ sliceTruncUp S,
        ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X : ℝ[X]).coeff 1 =
          2 * sliceAtom t q - 4 * sliceDefect t q := fun q _ => by
      rw [DeBruijn.slicePairFactor_eq, coeff_add, coeff_add, ← C_1, coeff_C, coeff_C_mul,
        coeff_X_one, coeff_C_mul, coeff_X_pow]
      norm_num
    rw [Finset.sum_congr rfl hc1, Finset.sum_congr rfl hu1, add_comm]
  have hd1 : Disjoint (sliceTruncCrit S) (sliceTruncUp S) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    have h1' := (mem_sliceTruncCrit.mp h1).2
    have h2' := (mem_sliceTruncUp.mp h2).2
    unfold XiCopyCritical XiCopyUpper at *; linarith
  have hd2 : Disjoint (sliceTruncCrit S ∪ sliceTruncUp S)
      ((sliceTruncUp S).map xiZeroCopyLineConjEquiv.toEmbedding) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp h2
    have hup := (mem_sliceTruncUp.mp hr).2
    unfold XiCopyUpper at hup
    simp only [Equiv.coe_toEmbedding] at h1
    have him := im_xiSpectralPoint_lineConj r
    rcases Finset.mem_union.mp h1 with h | h
    · have hc := (mem_sliceTruncCrit.mp h).2; unfold XiCopyCritical at hc; linarith
    · have hu := (mem_sliceTruncUp.mp h).2; unfold XiCopyUpper at hu; linarith
  rw [h1_mul]
  unfold sliceTrunc
  rw [Finset.sum_union hd2, Finset.sum_union hd1, Finset.sum_map, add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun q hq => ?_
    have him : (xiSpectralPoint q).im = 0 := (mem_sliceTruncCrit.mp hq).2
    rw [re_xiSliceGaussianReciprocal_eq, sliceDefect, him]
    ring
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Equiv.coe_toEmbedding]
    have hconj : xiSliceGaussianReciprocal t (xiZeroCopyLineConjEquiv q) =
        starRingEnd ℂ (xiSliceGaussianReciprocal t q) := by
      unfold xiSliceGaussianReciprocal
      conv_lhs => rw [xiSpectralPoint_lineConj, ← Complex.conj_ofReal t, ← map_sub, ← map_pow,
        ← map_inv₀]
    rw [hconj, Complex.conj_re, re_xiSliceGaussianReciprocal_eq]
    ring

/-- For the radius head `H = xiSliceGaussianRadiusHead t R`, `[y¹] sliceTruncPoly t H` equals
`∑_{q ∈ H} Re((z_q − t)⁻²)` unconditionally for all `t, R ∈ ℝ`. -/
theorem coeff_one_sliceTruncPoly_radius_eq_sum_re (t R : ℝ) :
    (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)).coeff 1 =
      ∑ q ∈ xiSliceGaussianRadiusHead t R, (xiSliceGaussianReciprocal t q).re := by
  rw [coeff_one_sliceTruncPoly_eq_sum_re, sliceTrunc_xiSliceGaussianRadiusHead]

/-- At `Ξ(t) ≠ 0`, `[y¹] sliceTruncPoly t H` (`H = xiSliceGaussianRadiusHead t R`) equals the global
slice coefficient `Re(c₂(t) / Ξ(t)²)` minus the tail quadratic moment
`Re(xiSliceGaussianTailQuadratic t H)`. -/
theorem coeff_one_sliceTruncPoly_radius_eq_sliceCoeff_sub_tail {t : ℝ} (ht : XiC t ≠ 0) (R : ℝ) :
    (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)).coeff 1 =
      (xiSliceCoeff t 2 / XiC t ^ 2).re -
        (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re := by
  set H := xiSliceGaussianRadiusHead t R
  have hsum : Summable (xiSliceGaussianReciprocal t) :=
    (summable_norm_xiSliceGaussianReciprocal t).of_norm
  have hsplit := hsum.sum_add_tsum_subtype_compl H
  have hlag : xiSliceCoeff t 2 / XiC t ^ 2 = ∑' q : XiZeroCopy, xiSliceGaussianReciprocal t q := by
    rw [xiSliceCoeff_two_eq_laguerre, laguerre_XiC_eq_tsum_inv_sq ht, mul_div_cancel_left₀ _
      (pow_ne_zero 2 ht)]
    refine tsum_congr fun q => ?_
    unfold xiSliceGaussianReciprocal
    congr 1
    ring
  have hre_eq : (xiSliceCoeff t 2 / XiC t ^ 2).re =
      (∑ q ∈ H, (xiSliceGaussianReciprocal t q).re) + (xiSliceGaussianTailQuadratic t H).re := by
    rw [hlag, ← hsplit, Complex.add_re, Complex.re_sum]
    rfl
  rw [coeff_one_sliceTruncPoly_radius_eq_sum_re]
  linarith

/-- **Prime–Cesàro explicit formula for the retained finite-head linear coefficient.**
At `Ξ(t) ≠ 0` and every `Y > 1`, `[y¹] sliceTruncPoly t (xiSliceGaussianRadiusHead t R)` equals the
Prime–Archimedean Cesàro expression minus the `Y`-twisted divisor sum and the quadratic tail moment. -/
theorem coeff_one_sliceTruncPoly_radius_eq_cesaro {t : ℝ} (ht : XiC t ≠ 0) (R : ℝ) {Y : ℝ}
    (hY : 1 < Y) :
    (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)).coeff 1 =
      Real.log Y * (archLogDeriv (laguerreLinePoint t)).re -
        (cesaroPrimeSum Y (laguerreLinePoint t)).re -
        (twistedDivisorSum Y (laguerreLinePoint t)).re +
        (laguerreRemainder Y (laguerreLinePoint t)).re -
        (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re := by
  rw [coeff_one_sliceTruncPoly_radius_eq_sliceCoeff_sub_tail ht R,
    xiSliceCoeff_two_div_eq_cesaro t ht hY]

/-- **Compensated head–tail Prime–Cesàro explicit formula for `[y¹] sliceTruncPoly t H`.**
Splitting the `Y`-twisted divisor sum across `H = xiSliceGaussianRadiusHead t R` cancels the
leading `-1/(ρ_q − s)²` tail against `xiSliceGaussianTailQuadratic t H`, leaving the finite-head
twist `∑_{q ∈ H} Y^{ρ_q − s}/(ρ_q − s)²` and the compensated tail
`∑_{q ∉ H} (Y^{ρ_q − s} − 1)/(ρ_q − s)²`. -/
theorem coeff_one_sliceTruncPoly_radius_eq_cesaro_compensated {t : ℝ} (ht : XiC t ≠ 0) (R : ℝ)
    {Y : ℝ} (hY : 1 < Y) :
    (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)).coeff 1 =
      Real.log Y * (archLogDeriv (laguerreLinePoint t)).re -
        (cesaroPrimeSum Y (laguerreLinePoint t)).re +
        (laguerreRemainder Y (laguerreLinePoint t)).re -
        (∑ q ∈ xiSliceGaussianRadiusHead t R,
          (Y : ℂ) ^ ((q.1 : ℂ) - laguerreLinePoint t) /
            ((q.1 : ℂ) - laguerreLinePoint t) ^ 2).re -
        (∑' q : {q : XiZeroCopy // q ∉ xiSliceGaussianRadiusHead t R},
          ((Y : ℂ) ^ ((q.1.1 : ℂ) - laguerreLinePoint t) - 1) /
            ((q.1.1 : ℂ) - laguerreLinePoint t) ^ 2).re := by
  set s : ℂ := laguerreLinePoint t with hs_def
  set H := xiSliceGaussianRadiusHead t R with hH_def
  have hY0 : 0 < Y := by linarith
  have hξ : xi s ≠ 0 := by rw [hs_def, xi_laguerreLinePoint]; exact ht
  have hP0 : (Y : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hY0.ne'))
  have hsq_rel : ∀ q : XiZeroCopy,
      (((q.1 : ℂ) - s) ^ 2)⁻¹ = -xiSliceGaussianReciprocal t q := by
    intro q
    have hdiff : (q.1 : ℂ) - s = I * (xiSpectralPoint q - (t : ℂ)) := by
      simp only [hs_def, xiSpectralPoint, laguerreLinePoint]
      ring_nf
      rw [I_sq]
      ring
    unfold xiSliceGaussianReciprocal
    rw [hdiff, mul_pow, I_sq, neg_one_mul, inv_neg]
  have hsum_rec : Summable (xiSliceGaussianReciprocal t) :=
    (summable_norm_xiSliceGaussianReciprocal t).of_norm
  have hinvQ : Summable (fun q : XiZeroCopy => (((q.1 : ℂ) - s) ^ 2)⁻¹) :=
    hsum_rec.neg.congr fun q => (hsq_rel q).symm
  have hsumQ := summable_zero_pow hY hξ
  have htw_eq : ∀ q : XiZeroCopy,
      (Y : ℂ) ^ ((q.1 : ℂ) - s) / ((q.1 : ℂ) - s) ^ 2 =
        ((Y : ℂ) ^ (q.1 : ℂ) - (Y : ℂ) ^ s) / ((q.1 : ℂ) - s) ^ 2 * ((Y : ℂ) ^ s)⁻¹ +
          (((q.1 : ℂ) - s) ^ 2)⁻¹ := by
    intro q
    have hq0 : (q.1 : ℂ) - s ≠ 0 := by
      intro h; apply hξ; rw [← sub_eq_zero.mp h]; exact xi_xiZeroCopy_eq_zero q
    have hcp : (Y : ℂ) ^ ((q.1 : ℂ) - s) = (Y : ℂ) ^ (q.1 : ℂ) * ((Y : ℂ) ^ s)⁻¹ := by
      rw [Complex.cpow_sub _ _ (by exact_mod_cast hY0.ne'), div_eq_mul_inv]
    rw [hcp]
    field_simp
    ring
  have htwQ : Summable (fun q : XiZeroCopy => (Y : ℂ) ^ ((q.1 : ℂ) - s) / ((q.1 : ℂ) - s) ^ 2) :=
    ((hsumQ.mul_right ((Y : ℂ) ^ s)⁻¹).add hinvQ).congr fun q => (htw_eq q).symm
  have hsplit_tw := htwQ.sum_add_tsum_subtype_compl H
  have hsub_tw : Summable (fun q : {q : XiZeroCopy // q ∉ H} =>
      (Y : ℂ) ^ ((q.1.1 : ℂ) - s) / ((q.1.1 : ℂ) - s) ^ 2) := htwQ.subtype _
  have hsub_rec : Summable (fun q : {q : XiZeroCopy // q ∉ H} =>
      xiSliceGaussianReciprocal t q.1) := hsum_rec.subtype _
  have hcomp_eq : (∑' q : {q : XiZeroCopy // q ∉ H},
      (Y : ℂ) ^ ((q.1.1 : ℂ) - s) / ((q.1.1 : ℂ) - s) ^ 2) + xiSliceGaussianTailQuadratic t H =
      ∑' q : {q : XiZeroCopy // q ∉ H},
        ((Y : ℂ) ^ ((q.1.1 : ℂ) - s) - 1) / ((q.1.1 : ℂ) - s) ^ 2 := by
    unfold xiSliceGaussianTailQuadratic
    rw [← hsub_tw.tsum_add hsub_rec]
    refine tsum_congr fun q => ?_
    have hrel := neg_eq_iff_eq_neg.mpr (hsq_rel q.1)
    rw [← hrel, sub_div, one_div, ← sub_eq_add_neg]
  rw [coeff_one_sliceTruncPoly_radius_eq_cesaro ht R hY, ← hs_def, ← hH_def]
  have htw_re : (twistedDivisorSum Y s).re + (xiSliceGaussianTailQuadratic t H).re =
      (∑ q ∈ H, (Y : ℂ) ^ ((q.1 : ℂ) - s) / ((q.1 : ℂ) - s) ^ 2).re +
        (∑' q : {q : XiZeroCopy // q ∉ H},
          ((Y : ℂ) ^ ((q.1.1 : ℂ) - s) - 1) / ((q.1.1 : ℂ) - s) ^ 2).re := by
    have hc : twistedDivisorSum Y s + xiSliceGaussianTailQuadratic t H =
        (∑ q ∈ H, (Y : ℂ) ^ ((q.1 : ℂ) - s) / ((q.1 : ℂ) - s) ^ 2) +
          ∑' q : {q : XiZeroCopy // q ∉ H},
            ((Y : ℂ) ^ ((q.1.1 : ℂ) - s) - 1) / ((q.1.1 : ℂ) - s) ^ 2 := by
      unfold twistedDivisorSum
      rw [← hsplit_tw, add_assoc, hcomp_eq]
    have hre := congrArg Complex.re hc
    simpa [Complex.add_re] using hre
  linarith

/-! ## 4. Global Ward Cap horizon, Euler–Stieltjes sum rule, reflection doubling, and width dictionary -/

/-- The unconditional Ward–Stieltjes weight `(((ρ_q + 1/100)² + τ²)⁻¹)` of any zero copy `q`. -/
def xiWardZeroStieltjes (tau : ℝ) (q : XiZeroCopy) : ℂ :=
  (((q.1 : ℂ) + 1 / 100) ^ 2 + (tau : ℂ) ^ 2)⁻¹

theorem xiWardRightZeroStieltjes_eq_ite (θ tau : ℝ) (q : XiZeroCopy) :
    xiWardRightZeroStieltjes θ tau q =
      if 1 / 2 + θ < (q.1 : ℂ).re then xiWardZeroStieltjes tau q else 0 := rfl

/-- **All-zero Stieltjes sign up to `τ = 32/5`.**
Because every zero copy of `ξ` satisfies `(Im ρ)² > 9769 / 231`, for `0 ≤ τ ≤ 32/5` every zero copy
(including critical-line zeros) satisfies `Re(xiWardZeroStieltjes τ q) < 0`. -/
theorem re_xiWardZeroStieltjes_neg_of_le_32_div_5 {tau : ℝ} (hτ0 : 0 ≤ tau) (hτ : tau ≤ 32 / 5)
    (q : XiZeroCopy) : (xiWardZeroStieltjes tau q).re < 0 := by
  unfold xiWardZeroStieltjes
  set z : ℂ := ((q.1 : ℂ) + 1 / 100) ^ 2 + (tau : ℂ) ^ 2 with hz
  have hγ := xiZeroCopy_nineThousandSevenHundredSixtyNine_div_twoHundredThirtyOne_lt_im_sq q
  have hβ0 := xiZeroCopy_re_pos q
  have hβ1 := xiZeroCopy_re_lt_one q
  have hre : z.re = ((q.1 : ℂ).re + 1 / 100) ^ 2 - (q.1 : ℂ).im ^ 2 + tau ^ 2 := by
    simp only [hz, Complex.add_re, sq, Complex.mul_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im]
    norm_num
  have hzre : z.re < 0 := by
    rw [hre]
    nlinarith
  have hnz : 0 < Complex.normSq z := by
    rw [Complex.normSq_pos]; intro h; rw [h, Complex.zero_re] at hzre; exact lt_irrefl 0 hzre
  rw [Complex.inv_re]
  exact div_neg_of_neg_of_pos hzre hnz

/-- **Off-line Stieltjes sign up to `τ = 366/25` (`14.64`, sharpening `12`).**
Because every off-line zero copy of `ξ` satisfies `(Im ρ)² ≥ 431349 / 2000`, for `0 ≤ τ ≤ 366/25`
every off-line zero copy (`Re ρ ≠ 1/2`) satisfies `Re(xiWardZeroStieltjes τ q) < 0`. -/
theorem re_xiWardZeroStieltjes_neg_of_offLine {tau : ℝ} (hτ0 : 0 ≤ tau) (hτ : tau ≤ 366 / 25)
    {q : XiZeroCopy} (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    (xiWardZeroStieltjes tau q).re < 0 := by
  unfold xiWardZeroStieltjes
  set z : ℂ := ((q.1 : ℂ) + 1 / 100) ^ 2 + (tau : ℂ) ^ 2 with hz
  have hγ := orderTwentyThreeOptimizedHeightSq_le_im_sq_of_xiZeroCopy_offLine q hoff
  have hγ_num : (431349 / 2000 : ℝ) ≤ (q.1 : ℂ).im ^ 2 := by
    simpa [xiOrderTwentyThreeOptimizedHeightSq] using hγ
  have hβ0 := xiZeroCopy_re_pos q
  have hβ1 := xiZeroCopy_re_lt_one q
  have hre : z.re = ((q.1 : ℂ).re + 1 / 100) ^ 2 - (q.1 : ℂ).im ^ 2 + tau ^ 2 := by
    simp only [hz, Complex.add_re, sq, Complex.mul_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im]
    norm_num
  have hzre : z.re < 0 := by
    rw [hre]
    nlinarith
  have hnz : 0 < Complex.normSq z := by
    rw [Complex.normSq_pos]; intro h; rw [h, Complex.zero_re] at hzre; exact lt_irrefl 0 hzre
  rw [Complex.inv_re]
  exact div_neg_of_neg_of_pos hzre hnz

/-- Sharpened right-zero Stieltjes sign up to `τ = 366/25` for all `θ ≥ 0`. -/
theorem re_xiWardRightZeroStieltjes_neg_optimized {θ tau : ℝ} (hθ : 0 ≤ θ) (hτ0 : 0 ≤ tau)
    (hτ : tau ≤ 366 / 25) {q : XiZeroCopy} (hq : 1 / 2 + θ < (q.1 : ℂ).re) :
    (xiWardRightZeroStieltjes θ tau q).re < 0 := by
  rw [xiWardRightZeroStieltjes_eq_ite, if_pos hq]
  exact re_xiWardZeroStieltjes_neg_of_offLine hτ0 hτ (by linarith)

theorem re_xiWardRightZeroStieltjes_nonpos_optimized {θ tau : ℝ} (hθ : 0 ≤ θ) (hτ0 : 0 ≤ tau)
    (hτ : tau ≤ 366 / 25) (q : XiZeroCopy) :
    (xiWardRightZeroStieltjes θ tau q).re ≤ 0 := by
  by_cases hq : 1 / 2 + θ < (q.1 : ℂ).re
  · exact (re_xiWardRightZeroStieltjes_neg_optimized hθ hτ0 hτ hq).le
  · rw [xiWardRightZeroStieltjes_eq_ite, if_neg hq]; simp

/-- **Sharpened one-sided Global Ward Cap (`0 < τ ≤ 366/25`).**
For almost every canonical level and every `0 < τ ≤ 366/25`, the Global Ward Cap has nonnegative
real part and vanishes iff no zero copy lies right of the cap line. -/
theorem ae_forall_xiWardGlobalCap_re_nonneg_optimized :
    ∀ᵐ s : ℝ ∂(volume : Measure ℝ), ∀ tau ∈ Ioc (0 : ℝ) (366 / 25),
      0 ≤ (∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
          continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).re ∧
      ((∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
          continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).re = 0 ↔
        ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + xiWardTransverseLevel s) := by
  filter_upwards [ae_forall_xiWardGlobalCap_eq_rightZeroSum] with s hs tau hτ
  set θ := xiWardTransverseLevel s
  have hθ : 0 < θ := (xiWardTransverseLevel_mem_Ioo s).1
  have hsum := summable_xiWardRightZeroStieltjes θ hτ.1.ne'
  have hsumre : Summable fun q => -(xiWardRightZeroStieltjes θ tau q).re :=
    (Complex.reCLM.summable hsum).neg
  have hnn : ∀ q, 0 ≤ -(xiWardRightZeroStieltjes θ tau q).re := fun q =>
    neg_nonneg.mpr (re_xiWardRightZeroStieltjes_nonpos_optimized hθ.le hτ.1.le hτ.2 q)
  have hre : (∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
      continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).re =
      8 * Real.pi * tau * ∑' q, -(xiWardRightZeroStieltjes θ tau q).re := by
    rw [hs tau, show -(8 * Real.pi * tau : ℂ) = ((-(8 * Real.pi * tau) : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul, Complex.re_tsum hsum, tsum_neg]
    ring
  have hpos : 0 < 8 * Real.pi * tau := by have := hτ.1; positivity
  rw [hre]
  refine ⟨mul_nonneg hpos.le (tsum_nonneg hnn), ⟨fun h0 => ?_, fun hall => ?_⟩⟩
  · intro q
    by_contra hq
    push Not at hq
    have hts := hsumre.tsum_pos hnn q
      (neg_pos.mpr (re_xiWardRightZeroStieltjes_neg_optimized hθ.le hτ.1.le hτ.2 hq))
    have : 0 < 8 * Real.pi * tau * ∑' q, -(xiWardRightZeroStieltjes θ tau q).re :=
      mul_pos hpos hts
    linarith
  · have hz : ∀ q, -(xiWardRightZeroStieltjes θ tau q).re = 0 := by
      intro q
      rw [xiWardRightZeroStieltjes_eq_ite, if_neg (not_lt.mpr (hall q))]
      simp
    simp [hz]

private theorem xi_ne_zero_of_re_le_zero {s : ℂ} (hs : s.re ≤ 0) : xi s ≠ 0 := by
  intro hz
  have h0 := (xi_zero_re_mem_open_unit hz).1
  linarith

private theorem partialFractionDiff_wardPoles (tau : ℝ) (q : XiZeroCopy) :
    ((-(1 / 100 : ℂ) - (tau : ℂ) * I) - (q.1 : ℂ))⁻¹ -
      ((-(1 / 100 : ℂ) + (tau : ℂ) * I) - (q.1 : ℂ))⁻¹ =
      2 * I * (tau : ℂ) * xiWardZeroStieltjes tau q := by
  have hre_pos := xiZeroCopy_re_pos q
  set A : ℂ := (-(1 / 100 : ℂ) - (tau : ℂ) * I) - (q.1 : ℂ)
  set B : ℂ := (-(1 / 100 : ℂ) + (tau : ℂ) * I) - (q.1 : ℂ)
  have h1 : A ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [A, Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      Complex.zero_re] at hre
    linarith
  have h2 : B ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [B, Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.div_ofNat_re,
      Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, Complex.zero_re] at hre
    linarith
  have hprod : A * B = ((q.1 : ℂ) + 1 / 100) ^ 2 + (tau : ℂ) ^ 2 := by
    simp only [A, B]
    ring_nf
    rw [I_sq]
    ring
  have hprod_ne : ((q.1 : ℂ) + 1 / 100) ^ 2 + (tau : ℂ) ^ 2 ≠ 0 := by
    rw [← hprod]; exact mul_ne_zero h1 h2
  unfold xiWardZeroStieltjes
  apply mul_right_cancel₀ hprod_ne
  calc (A⁻¹ - B⁻¹) * (((q.1 : ℂ) + 1 / 100) ^ 2 + (tau : ℂ) ^ 2)
      = A⁻¹ * A * B - B⁻¹ * B * A := by rw [← hprod]; ring
    _ = B - A := by rw [inv_mul_cancel₀ h1, inv_mul_cancel₀ h2, one_mul, one_mul]
    _ = 2 * I * (tau : ℂ) := by simp only [A, B]; ring
    _ = 2 * I * (tau : ℂ) * (((q.1 : ℂ) + 1 / 100) ^ 2 + (tau : ℂ) ^ 2)⁻¹ *
          (((q.1 : ℂ) + 1 / 100) ^ 2 + (tau : ℂ) ^ 2) := by
        rw [mul_assoc (2 * I * (tau : ℂ)), inv_mul_cancel₀ hprod_ne, mul_one]

/-- For every `τ ≠ 0`, the full Ward–Stieltjes family `xiWardZeroStieltjes τ` is summable over
`XiZeroCopy`. -/
theorem summable_xiWardZeroStieltjes {tau : ℝ} (hτ : tau ≠ 0) :
    Summable (xiWardZeroStieltjes tau) := by
  set s₁ : ℂ := -(1 / 100 : ℂ) - (tau : ℂ) * I
  set s₂ : ℂ := -(1 / 100 : ℂ) + (tau : ℂ) * I
  have hs₁ : xi s₁ ≠ 0 := xi_ne_zero_of_re_le_zero (by simp [s₁])
  have hs₂ : xi s₂ ≠ 0 := xi_ne_zero_of_re_le_zero (by simp [s₂])
  have hc_ne : (2 * I * (tau : ℂ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (by exact_mod_cast hτ)
  refine ((summable_partialFractionDiff hs₁ hs₂).mul_left (2 * I * (tau : ℂ))⁻¹).congr fun q => ?_
  rw [partialFractionDiff_wardPoles, inv_mul_cancel_left₀ hc_ne]

/-- **Euler–Stieltjes sum rule for the full Ward–Stieltjes divisor sum.**
For every `τ ∈ ℝ`,
`−8πτ ∑_q ((ρ_q + 1/100)² + τ²)⁻¹ = 8π Im(ξ'/ξ(101/100 + iτ))`. -/
theorem tsum_xiWardZeroStieltjes_eq_im_logDeriv_xi (tau : ℝ) :
    -(8 * Real.pi * tau : ℂ) * ∑' q : XiZeroCopy, xiWardZeroStieltjes tau q =
      ((8 * Real.pi * (logDeriv xi ((101 / 100 : ℂ) + (tau : ℂ) * I)).im : ℝ) : ℂ) := by
  rcases eq_or_ne tau 0 with rfl | hτ
  · have him0 : (logDeriv xi (101 / 100 : ℂ)).im = 0 := by
      have h := im_logDeriv_xi_conj_line (101 / 100) 0
      simp only [Complex.ofReal_zero, zero_mul, sub_zero, add_zero] at h
      push_cast at h
      linarith
    simp [him0]
  · set s₁ : ℂ := -(1 / 100 : ℂ) - (tau : ℂ) * I
    set s₂ : ℂ := -(1 / 100 : ℂ) + (tau : ℂ) * I
    set w : ℂ := (101 / 100 : ℂ) + (tau : ℂ) * I
    have hs₁ : xi s₁ ≠ 0 := xi_ne_zero_of_re_le_zero (by simp [s₁])
    have hs₂ : xi s₂ ≠ 0 := xi_ne_zero_of_re_le_zero (by simp [s₂])
    have hdiff : logDeriv xi s₁ - logDeriv xi s₂ =
        ∑' q : XiZeroCopy, 2 * I * (tau : ℂ) * xiWardZeroStieltjes tau q :=
      (logDeriv_xi_sub_eq_tsum hs₁ hs₂).trans
        (tsum_congr fun q => partialFractionDiff_wardPoles tau q)
    rw [tsum_mul_left] at hdiff
    have hw₁ : s₁ = 1 - w := by simp only [s₁, w]; ring
    have hw₂ : s₂ = 1 - starRingEnd ℂ w := by
      simp only [s₂, w, map_add, map_div₀, map_ofNat, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    have hsym₁ : logDeriv xi s₁ = -logDeriv xi w := by
      rw [hw₁, logDeriv_xi_one_sub_xiLogDerivSymmetry]
    have hsym₂ : logDeriv xi s₂ = -starRingEnd ℂ (logDeriv xi w) := by
      rw [hw₂, logDeriv_xi_one_sub_xiLogDerivSymmetry, logDeriv_xi_conj_xiLogDerivSymmetry]
    rw [hsym₁, hsym₂] at hdiff
    have hconj_sub : -logDeriv xi w - -starRingEnd ℂ (logDeriv xi w) =
        -2 * I * ((logDeriv xi w).im : ℂ) := by
      apply Complex.ext
      · simp
      · simp; ring
    rw [hconj_sub] at hdiff
    have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
    have htau_sum : (tau : ℂ) * ∑' q : XiZeroCopy, xiWardZeroStieltjes tau q =
        -((logDeriv xi w).im : ℂ) := by
      apply mul_left_cancel₀ h2I
      linear_combination -hdiff
    calc -(8 * Real.pi * tau : ℂ) * ∑' q : XiZeroCopy, xiWardZeroStieltjes tau q
        = -(8 * Real.pi : ℂ) * ((tau : ℂ) * ∑' q : XiZeroCopy, xiWardZeroStieltjes tau q) := by
          ring
      _ = -(8 * Real.pi : ℂ) * -((logDeriv xi w).im : ℂ) := by rw [htau_sum]
      _ = ((8 * Real.pi * (logDeriv xi w).im : ℝ) : ℂ) := by push_cast; ring

/-- **Prime–Gamma Euler-region evaluation of the full Ward–Stieltjes divisor sum.**
At `101/100 + iτ` (`Re > 1`), `ξ'/ξ` opens into pole terms, `logDeriv Γ_ℝ`, and the absolutely
convergent von Mangoldt `L`-series. -/
theorem tsum_xiWardZeroStieltjes_eq_arithmetic (tau : ℝ) :
    (-(8 * Real.pi * tau : ℂ) * ∑' q : XiZeroCopy, xiWardZeroStieltjes tau q).re =
      8 * Real.pi *
        ((((101 / 100 : ℂ) + (tau : ℂ) * I)⁻¹ +
          ((1 / 100 : ℂ) + (tau : ℂ) * I)⁻¹ +
          logDeriv Complex.Gammaℝ ((101 / 100 : ℂ) + (tau : ℂ) * I) -
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            ((101 / 100 : ℂ) + (tau : ℂ) * I)).im) := by
  rw [tsum_xiWardZeroStieltjes_eq_im_logDeriv_xi, Complex.ofReal_re]
  have hre : 1 < ((101 / 100 : ℂ) + (tau : ℂ) * I).re := by simp; norm_num
  rw [logDeriv_xi_eq_arithmetic hre]
  have hsub : (101 / 100 : ℂ) + (tau : ℂ) * I - 1 = (1 / 100 : ℂ) + (tau : ℂ) * I := by ring
  rw [hsub]

private theorem re_im_xiZeroCopyLineConjEquiv (q : XiZeroCopy) :
    ((xiZeroCopyLineConjEquiv q).1 : ℂ).re = 1 - (q.1 : ℂ).re ∧
      ((xiZeroCopyLineConjEquiv q).1 : ℂ).im = (q.1 : ℂ).im := by
  have h := xiSpectralPoint_lineConj q
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [xiSpectralPoint, Complex.mul_re, Complex.sub_re, Complex.neg_re, Complex.I_re,
    Complex.sub_im, Complex.neg_im, Complex.I_im, Complex.conj_re, Complex.conj_im] at hre him
  norm_num at hre him
  constructor <;> linarith

private theorem wardQuad_re_and_normSq (a γ tau : ℝ) :
    -(((a : ℂ) + (γ : ℂ) * I) ^ 2 + (tau : ℂ) ^ 2).re = (γ ^ 2 - tau ^ 2) - a ^ 2 ∧
      Complex.normSq (((a : ℂ) + (γ : ℂ) * I) ^ 2 + (tau : ℂ) ^ 2) =
        a ^ 4 + 2 * a ^ 2 * (γ ^ 2 + tau ^ 2) + (γ ^ 2 - tau ^ 2) ^ 2 := by
  have hre : (((a : ℂ) + (γ : ℂ) * I) ^ 2 + (tau : ℂ) ^ 2).re = a ^ 2 - γ ^ 2 + tau ^ 2 := by
    simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
    ring
  have him : (((a : ℂ) + (γ : ℂ) * I) ^ 2 + (tau : ℂ) ^ 2).im = 2 * a * γ := by
    simp only [sq, Complex.add_im, Complex.mul_im, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  refine ⟨by linarith, ?_⟩
  rw [Complex.normSq_apply, hre, him]
  ring

private theorem neg_re_inv_wardQuad_lt {a a' γ tau : ℝ}
    (ha'_pos : 0 < a') (ha'_lt_a : a' < a) (ha2_lt : a ^ 2 < γ ^ 2 - tau ^ 2) :
    -((((a : ℂ) + (γ : ℂ) * I) ^ 2 + (tau : ℂ) ^ 2)⁻¹).re <
      -((((a' : ℂ) + (γ : ℂ) * I) ^ 2 + (tau : ℂ) ^ 2)⁻¹).re := by
  obtain ⟨hre, hns⟩ := wardQuad_re_and_normSq a γ tau
  obtain ⟨hre', hns'⟩ := wardQuad_re_and_normSq a' γ tau
  have ha2 : a' ^ 2 < a ^ 2 := by
    simpa [sq] using mul_self_lt_mul_self ha'_pos.le ha'_lt_a
  have ha4 : a' ^ 4 < a ^ 4 := by
    have h := mul_self_lt_mul_self (sq_nonneg a') ha2
    have h1 : a' ^ 2 * a' ^ 2 = a' ^ 4 := by ring
    have h2 : a ^ 2 * a ^ 2 = a ^ 4 := by ring
    rwa [h1, h2] at h
  have hM_pos : 0 < γ ^ 2 - tau ^ 2 := lt_of_le_of_lt (sq_nonneg a) ha2_lt
  have hγt_pos : 0 < γ ^ 2 + tau ^ 2 := by linarith [sq_nonneg tau]
  have hns'_pos : 0 < Complex.normSq (((a' : ℂ) + (γ : ℂ) * I) ^ 2 + (tau : ℂ) ^ 2) := by
    rw [hns']; positivity
  have hns_lt : Complex.normSq (((a' : ℂ) + (γ : ℂ) * I) ^ 2 + (tau : ℂ) ^ 2) <
      Complex.normSq (((a : ℂ) + (γ : ℂ) * I) ^ 2 + (tau : ℂ) ^ 2) := by
    rw [hns', hns]
    have hmul : a' ^ 2 * (γ ^ 2 + tau ^ 2) < a ^ 2 * (γ ^ 2 + tau ^ 2) :=
      mul_lt_mul_of_pos_right ha2 hγt_pos
    linarith
  have hns_pos : 0 < Complex.normSq (((a : ℂ) + (γ : ℂ) * I) ^ 2 + (tau : ℂ) ^ 2) :=
    hns'_pos.trans hns_lt
  rw [Complex.inv_re, Complex.inv_re, ← neg_div, ← neg_div, hre, hre',
    div_lt_div_iff₀ hns_pos hns'_pos]
  have hnum_pos : 0 < (γ ^ 2 - tau ^ 2) - a ^ 2 := sub_pos.mpr ha2_lt
  have hnum_lt : (γ ^ 2 - tau ^ 2) - a ^ 2 < (γ ^ 2 - tau ^ 2) - a' ^ 2 := sub_lt_sub_left ha2 _
  calc ((γ ^ 2 - tau ^ 2) - a ^ 2) *
        Complex.normSq (((a' : ℂ) + (γ : ℂ) * I) ^ 2 + (tau : ℂ) ^ 2)
      < ((γ ^ 2 - tau ^ 2) - a ^ 2) *
          Complex.normSq (((a : ℂ) + (γ : ℂ) * I) ^ 2 + (tau : ℂ) ^ 2) :=
        mul_lt_mul_of_pos_left hns_lt hnum_pos
    _ < ((γ ^ 2 - tau ^ 2) - a' ^ 2) *
          Complex.normSq (((a : ℂ) + (γ : ℂ) * I) ^ 2 + (tau : ℂ) ^ 2) :=
        mul_lt_mul_of_pos_right hnum_lt hns_pos

/-- **Reflection-asymmetry strict comparison across the critical line.**
Because the Ward poles sit at `−1/100 < 1/2`, reflecting any right-half-strip zero copy `q`
(`Re ρ_q > 1/2`) to `q' = xiZeroCopyLineConjEquiv q` (`Re ρ_{q'} = 1 − Re ρ_q`) simultaneously
increases the negative real numerator and decreases `normSq` of `(ρ + 1/100)² + τ²`.  Hence for
every `0 ≤ τ ≤ 366/25` and `Re ρ_q > 1/2`,
`0 < −Re(xiWardZeroStieltjes τ q) < −Re(xiWardZeroStieltjes τ (xiZeroCopyLineConjEquiv q))`. -/
theorem neg_re_xiWardZeroStieltjes_lt_lineConj {tau : ℝ} (hτ0 : 0 ≤ tau) (hτ : tau ≤ 366 / 25)
    {q : XiZeroCopy} (hq : 1 / 2 < (q.1 : ℂ).re) :
    0 < -(xiWardZeroStieltjes tau q).re ∧
      -(xiWardZeroStieltjes tau q).re <
        -(xiWardZeroStieltjes tau (xiZeroCopyLineConjEquiv q)).re := by
  refine ⟨neg_pos.mpr (re_xiWardZeroStieltjes_neg_of_offLine hτ0 hτ (by linarith)), ?_⟩
  obtain ⟨hre_q', him_q'⟩ := re_im_xiZeroCopyLineConjEquiv q
  have hβ1 := xiZeroCopy_re_lt_one q
  have hγ_sq : (431349 / 2000 : ℝ) ≤ (q.1 : ℂ).im ^ 2 := by
    simpa [xiOrderTwentyThreeOptimizedHeightSq] using
      orderTwentyThreeOptimizedHeightSq_le_im_sq_of_xiZeroCopy_offLine q (by linarith)
  have hz_eq : (q.1 : ℂ) + 1 / 100 =
      (((q.1 : ℂ).re + 1 / 100 : ℝ) : ℂ) + ((q.1 : ℂ).im : ℂ) * I := by
    apply Complex.ext <;> simp
  have hz'_eq : ((xiZeroCopyLineConjEquiv q).1 : ℂ) + 1 / 100 =
      ((1 - (q.1 : ℂ).re + 1 / 100 : ℝ) : ℂ) + ((q.1 : ℂ).im : ℂ) * I := by
    apply Complex.ext <;> simp [hre_q', him_q']
  unfold xiWardZeroStieltjes
  rw [hz_eq, hz'_eq]
  refine neg_re_inv_wardQuad_lt (by linarith) (by linarith) ?_
  have hτ_sq : tau ^ 2 ≤ (366 / 25 : ℝ) ^ 2 := by nlinarith [hτ0, hτ]
  have ha_sq : ((q.1 : ℂ).re + 1 / 100) ^ 2 < (101 / 100 : ℝ) ^ 2 := by nlinarith [hq, hβ1]
  have hnum : (101 / 100 : ℝ) ^ 2 + (366 / 25 : ℝ) ^ 2 < 431349 / 2000 := by norm_num
  linarith

/-- The critical-line contribution `8πτ ∑_{Re ρ = 1/2} (−Re(((ρ + 1/100)² + τ²)⁻¹))`. -/
def xiWardCriticalStieltjesSum (tau : ℝ) : ℝ :=
  8 * Real.pi * tau *
    ∑' q : XiZeroCopy, if (q.1 : ℂ).re = 1 / 2 then -(xiWardZeroStieltjes tau q).re else 0

/-- The right-of-level contribution `8πτ ∑_{Re ρ > 1/2 + θ} (−Re(((ρ + 1/100)² + τ²)⁻¹))`. -/
def xiWardRightStieltjesSum (θ tau : ℝ) : ℝ :=
  8 * Real.pi * tau * ∑' q : XiZeroCopy, -(xiWardRightZeroStieltjes θ tau q).re

/-- On `0 ≤ θ₁ ≤ θ₂` and `0 < τ ≤ 366/25`, `xiWardRightStieltjesSum θ τ` is antitone in `θ` and
nonnegative. -/
theorem xiWardRightStieltjesSum_anti {θ₁ θ₂ tau : ℝ} (hθ₁ : 0 ≤ θ₁) (hθ₁₂ : θ₁ ≤ θ₂)
    (hτ : tau ∈ Ioc (0 : ℝ) (366 / 25)) :
    0 ≤ xiWardRightStieltjesSum θ₂ tau ∧
      xiWardRightStieltjesSum θ₂ tau ≤ xiWardRightStieltjesSum θ₁ tau := by
  have hθ₂ : 0 ≤ θ₂ := hθ₁.trans hθ₁₂
  have hs₁ : Summable fun q => -(xiWardRightZeroStieltjes θ₁ tau q).re :=
    (Complex.reCLM.summable (summable_xiWardRightZeroStieltjes θ₁ hτ.1.ne')).neg
  have hs₂ : Summable fun q => -(xiWardRightZeroStieltjes θ₂ tau q).re :=
    (Complex.reCLM.summable (summable_xiWardRightZeroStieltjes θ₂ hτ.1.ne')).neg
  have hpos : 0 ≤ 8 * Real.pi * tau := by have := hτ.1; positivity
  refine ⟨mul_nonneg hpos (tsum_nonneg fun q =>
    neg_nonneg.mpr (re_xiWardRightZeroStieltjes_nonpos_optimized hθ₂ hτ.1.le hτ.2 q)),
    mul_le_mul_of_nonneg_left (hs₂.tsum_le_tsum (fun q => ?_) hs₁) hpos⟩
  by_cases hq₂ : 1 / 2 + θ₂ < (q.1 : ℂ).re
  · have hq₁ : 1 / 2 + θ₁ < (q.1 : ℂ).re := by linarith
    rw [xiWardRightZeroStieltjes_eq_ite, if_pos hq₂, xiWardRightZeroStieltjes_eq_ite, if_pos hq₁]
  · rw [xiWardRightZeroStieltjes_eq_ite, if_neg hq₂]
    simp only [Complex.zero_re, neg_zero]
    exact neg_nonneg.mpr (re_xiWardRightZeroStieltjes_nonpos_optimized hθ₁ hτ.1.le hτ.2 q)

/-- **Reflection-doubling inequality for the Global Ward Cap.**
For every `0 < τ ≤ 366/25` and `θ ≥ 0`, twice the right-of-level Stieltjes mass plus the
critical-line Stieltjes sum is bounded above by `8π Im(ξ'/ξ(101/100 + iτ))`. -/
theorem two_mul_xiWardRightStieltjesSum_le_euler_sub_critical {θ tau : ℝ} (hθ : 0 ≤ θ)
    (hτ : tau ∈ Ioc (0 : ℝ) (366 / 25)) :
    2 * xiWardRightStieltjesSum θ tau ≤
      8 * Real.pi * (logDeriv xi ((101 / 100 : ℂ) + (tau : ℂ) * I)).im -
        xiWardCriticalStieltjesSum tau := by
  set f : XiZeroCopy → ℝ := fun q => -(xiWardZeroStieltjes tau q).re
  have hf_sum : Summable f :=
    (Complex.reCLM.summable (summable_xiWardZeroStieltjes hτ.1.ne')).neg
  have hf_norm : Summable fun q => ‖f q‖ := hf_sum.norm
  set f_crit : XiZeroCopy → ℝ := fun q => if (q.1 : ℂ).re = 1 / 2 then f q else 0
  set f_right : XiZeroCopy → ℝ := fun q => if 1 / 2 < (q.1 : ℂ).re then f q else 0
  set f_left : XiZeroCopy → ℝ := fun q => if (q.1 : ℂ).re < 1 / 2 then f q else 0
  have hs_crit : Summable f_crit := hf_norm.of_norm_bounded fun q => by
    simp only [f_crit]; split_ifs <;> simp
  have hs_right : Summable f_right := hf_norm.of_norm_bounded fun q => by
    simp only [f_right]; split_ifs <;> simp
  have hs_left : Summable f_left := hf_norm.of_norm_bounded fun q => by
    simp only [f_left]; split_ifs <;> simp
  have hpart : ∀ q : XiZeroCopy, f q = f_crit q + f_right q + f_left q := by
    intro q
    simp only [f_crit, f_right, f_left]
    rcases lt_trichotomy (q.1 : ℂ).re (1 / 2) with hlt | heq | hgt
    · rw [if_neg hlt.ne, if_neg (not_lt.mpr hlt.le), if_pos hlt]; ring
    · rw [if_pos heq, if_neg (by linarith), if_neg (by linarith)]; ring
    · rw [if_neg hgt.ne', if_pos hgt, if_neg (not_lt.mpr hgt.le)]; ring
  have htsum_part : (∑' q, f q) = (∑' q, f_crit q) + (∑' q, f_right q) + (∑' q, f_left q) := by
    have h1 : (∑' q, f q) = ∑' q, (f_crit q + f_right q + f_left q) := tsum_congr hpart
    rw [h1, (hs_crit.add hs_right).tsum_add hs_left, hs_crit.tsum_add hs_right]
  have hleft_reindex : (∑' q, f_left q) =
      ∑' q, if 1 / 2 < (q.1 : ℂ).re then f (xiZeroCopyLineConjEquiv q) else 0 := by
    rw [← xiZeroCopyLineConjEquiv.tsum_eq f_left]
    refine tsum_congr fun q => ?_
    simp only [f_left, (re_im_xiZeroCopyLineConjEquiv q).1]
    have hiff : (1 - (q.1 : ℂ).re < 1 / 2) ↔ (1 / 2 < (q.1 : ℂ).re) := by constructor <;> intro h <;> linarith
    by_cases hq : 1 / 2 < (q.1 : ℂ).re
    · rw [if_pos (hiff.mpr hq), if_pos hq]
    · rw [if_neg (mt hiff.mp hq), if_neg hq]
  have hs_left_reindexed : Summable (fun q =>
      if 1 / 2 < (q.1 : ℂ).re then f (xiZeroCopyLineConjEquiv q) else 0) := by
    refine (xiZeroCopyLineConjEquiv.summable_iff.mpr hs_left).congr fun q => ?_
    simp only [Function.comp_apply, f_left, (re_im_xiZeroCopyLineConjEquiv q).1]
    have hiff : (1 - (q.1 : ℂ).re < 1 / 2) ↔ (1 / 2 < (q.1 : ℂ).re) := by constructor <;> intro h <;> linarith
    by_cases hq : 1 / 2 < (q.1 : ℂ).re
    · rw [if_pos (hiff.mpr hq), if_pos hq]
    · rw [if_neg (mt hiff.mp hq), if_neg hq]
  have hright_le_left : (∑' q, f_right q) ≤ ∑' q, f_left q := by
    rw [hleft_reindex]
    refine hs_right.tsum_le_tsum (fun q => ?_) hs_left_reindexed
    simp only [f_right]
    split_ifs with hq
    · exact (neg_re_xiWardZeroStieltjes_lt_lineConj hτ.1.le hτ.2 hq).2.le
    · exact le_rfl
  have heuler : 8 * Real.pi * tau * (∑' q, f q) =
      8 * Real.pi * (logDeriv xi ((101 / 100 : ℂ) + (tau : ℂ) * I)).im := by
    have h := congrArg Complex.re (tsum_xiWardZeroStieltjes_eq_im_logDeriv_xi tau)
    rw [show -(8 * Real.pi * tau : ℂ) = ((-(8 * Real.pi * tau) : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul, Complex.re_tsum (summable_xiWardZeroStieltjes hτ.1.ne'),
      Complex.ofReal_re] at h
    have hneg : -(8 * Real.pi * tau) * (∑' q, (xiWardZeroStieltjes tau q).re) =
        8 * Real.pi * tau * ∑' q, f q := by
      simp only [f, tsum_neg]; ring
    linarith
  have hright0_eq : xiWardRightStieltjesSum 0 tau = 8 * Real.pi * tau * ∑' q, f_right q := by
    unfold xiWardRightStieltjesSum
    congr 1
    refine tsum_congr fun q => ?_
    simp only [xiWardRightZeroStieltjes_eq_ite, add_zero, f_right, f]
    split_ifs <;> simp
  have hcrit_eq : xiWardCriticalStieltjesSum tau = 8 * Real.pi * tau * ∑' q, f_crit q := rfl
  have hpos : 0 < 8 * Real.pi * tau := by have := hτ.1; positivity
  have h0_le : 2 * xiWardRightStieltjesSum 0 tau ≤
      8 * Real.pi * (logDeriv xi ((101 / 100 : ℂ) + (tau : ℂ) * I)).im -
        xiWardCriticalStieltjesSum tau := by
    rw [← heuler, htsum_part, hright0_eq, hcrit_eq]
    nlinarith [mul_le_mul_of_nonneg_left hright_le_left hpos.le]
  have hanti := (xiWardRightStieltjesSum_anti le_rfl hθ hτ).2
  linarith

/-- Almost everywhere, twice the Global Ward Cap is bounded by the Euler–Stieltjes critical-line
deficit `8π Im(ξ'/ξ(101/100 + iτ)) − xiWardCriticalStieltjesSum τ` for every `0 < τ ≤ 366/25`. -/
theorem ae_forall_two_mul_xiWardGlobalCap_re_le_euler_sub_critical :
    ∀ᵐ s : ℝ ∂(volume : Measure ℝ), ∀ tau ∈ Ioc (0 : ℝ) (366 / 25),
      2 * (∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
          continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).re ≤
        8 * Real.pi * (logDeriv xi ((101 / 100 : ℂ) + (tau : ℂ) * I)).im -
          xiWardCriticalStieltjesSum tau := by
  filter_upwards [ae_forall_xiWardGlobalCap_eq_rightZeroSum] with s hs tau hτ
  set θ := xiWardTransverseLevel s
  have hθ : 0 < θ := (xiWardTransverseLevel_mem_Ioo s).1
  have hsum := summable_xiWardRightZeroStieltjes θ hτ.1.ne'
  have hre : (∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
      continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).re =
      xiWardRightStieltjesSum θ tau := by
    unfold xiWardRightStieltjesSum
    rw [hs tau, show -(8 * Real.pi * tau : ℂ) = ((-(8 * Real.pi * tau) : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul, Complex.re_tsum hsum, tsum_neg]
    ring
  rw [hre]
  exact two_mul_xiWardRightStieltjesSum_le_euler_sub_critical hθ.le hτ

/-- For `σ ≥ 0`, `zetaZeroWidth ≤ σ` iff every `q : XiZeroCopy` satisfies `Re ρ_q ≤ 1/2 + σ`. -/
theorem zetaZeroWidth_le_iff_forall_xiZeroCopy_re_le {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + σ := by
  rw [zetaZeroWidth_le_iff_re_le hσ]
  constructor
  · intro h q
    exact h (q.1 : ℂ) (CrossRouteReceiverBridges.xiZeroCopy_mem_zetaZeroConfig_carrier q)
  · intro h ρ hρ
    obtain ⟨hζ, hre0, hre1⟩ : riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := hρ
    have hρ1 : ρ ≠ 1 := by intro h1; rw [h1, Complex.one_re] at hre1; linarith
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_riemannZeta_eq_zero hre0 hρ1 hζ
    rw [← hq]
    exact h q

/-- `RiemannHypothesis` is equivalent to `(q.1 : ℂ).re = 1/2` for every `q : XiZeroCopy`. -/
theorem riemannHypothesis_iff_forall_xiZeroCopy_re_eq_half :
    RiemannHypothesis ↔ ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
  have hz0 : zetaZeroWidth = 0 ↔ zetaZeroWidth ≤ 0 :=
    le_antisymm_iff.trans (and_iff_left zetaZeroWidth_nonneg)
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero, hz0,
    zetaZeroWidth_le_iff_forall_xiZeroCopy_re_le le_rfl]
  constructor
  · intro h
    exact xiZeroCopy_re_eq_half_of_forall_le fun q => by linarith [h q]
  · intro hall q
    linarith [hall q]

/-- **Critical-line Stieltjes saturation equivalence.**
For every `0 < τ ≤ 366/25`, `xiWardCriticalStieltjesSum τ ≤ 8π Im(ξ'/ξ(101/100 + iτ))`
unconditionally, and equality at **any single** `τ ∈ (0, 366/25]` is equivalent to
`RiemannHypothesis`. -/
theorem riemannHypothesis_iff_xiWardCriticalStieltjesSum_eq_euler {tau : ℝ}
    (hτ : tau ∈ Ioc (0 : ℝ) (366 / 25)) :
    xiWardCriticalStieltjesSum tau ≤
        8 * Real.pi * (logDeriv xi ((101 / 100 : ℂ) + (tau : ℂ) * I)).im ∧
      (RiemannHypothesis ↔
        xiWardCriticalStieltjesSum tau =
          8 * Real.pi * (logDeriv xi ((101 / 100 : ℂ) + (tau : ℂ) * I)).im) := by
  have h0_nn := (xiWardRightStieltjesSum_anti le_rfl le_rfl hτ).1
  have h2 := two_mul_xiWardRightStieltjesSum_le_euler_sub_critical le_rfl hτ
  refine ⟨by linarith, ?_⟩
  rw [riemannHypothesis_iff_forall_xiZeroCopy_re_eq_half]
  constructor
  · intro hall
    have heuler : 8 * Real.pi * tau * (∑' q : XiZeroCopy, -(xiWardZeroStieltjes tau q).re) =
        8 * Real.pi * (logDeriv xi ((101 / 100 : ℂ) + (tau : ℂ) * I)).im := by
      have h := congrArg Complex.re (tsum_xiWardZeroStieltjes_eq_im_logDeriv_xi tau)
      rw [show -(8 * Real.pi * tau : ℂ) = ((-(8 * Real.pi * tau) : ℝ) : ℂ) by push_cast; ring,
        Complex.re_ofReal_mul, Complex.re_tsum (summable_xiWardZeroStieltjes hτ.1.ne'),
        Complex.ofReal_re] at h
      have hneg : -(8 * Real.pi * tau) * (∑' q : XiZeroCopy, (xiWardZeroStieltjes tau q).re) =
          8 * Real.pi * tau * ∑' q : XiZeroCopy, -(xiWardZeroStieltjes tau q).re := by
        rw [tsum_neg]; ring
      linarith
    rw [← heuler]
    unfold xiWardCriticalStieltjesSum
    congr 1
    refine tsum_congr fun q => ?_
    rw [if_pos (hall q)]
  · intro heq
    have hright0 : xiWardRightStieltjesSum 0 tau = 0 := by linarith
    refine xiZeroCopy_re_eq_half_of_forall_le fun q => ?_
    by_contra hq
    push Not at hq
    have hs0 : Summable fun r => -(xiWardRightZeroStieltjes 0 tau r).re :=
      (Complex.reCLM.summable (summable_xiWardRightZeroStieltjes 0 hτ.1.ne')).neg
    have hnn0 : ∀ r, 0 ≤ -(xiWardRightZeroStieltjes 0 tau r).re := fun r =>
      neg_nonneg.mpr (re_xiWardRightZeroStieltjes_nonpos_optimized le_rfl hτ.1.le hτ.2 r)
    have hpos_q : 0 < -(xiWardRightZeroStieltjes 0 tau q).re :=
      neg_pos.mpr (re_xiWardRightZeroStieltjes_neg_optimized le_rfl hτ.1.le hτ.2 (by linarith))
    have hts := hs0.tsum_pos hnn0 q hpos_q
    have hpos_mul : 0 < xiWardRightStieltjesSum 0 tau :=
      mul_pos (by have := hτ.1; positivity) hts
    linarith

/-- **Graded Global Ward Cap zero-width characterization.**
For any `σ ≥ 0` and any single height `τ ∈ (0, 366/25]`, `zetaZeroWidth ≤ σ` holds iff the
Global Ward Cap vanishes almost everywhere above transverse level `σ`. -/
theorem zetaZeroWidth_le_iff_ae_xiWardGlobalCap_eq_zero_above {σ tau : ℝ} (hσ0 : 0 ≤ σ)
    (hτ : tau ∈ Ioc (0 : ℝ) (366 / 25)) :
    zetaZeroWidth ≤ σ ↔
      ∀ᵐ s : ℝ ∂(volume : Measure ℝ), σ ≤ xiWardTransverseLevel s →
        ∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
            continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x) = 0 := by
  rw [zetaZeroWidth_le_iff_forall_xiZeroCopy_re_le hσ0]
  constructor
  · intro hall
    filter_upwards [ae_forall_xiWardGlobalCap_eq_rightZeroSum] with s hs hlev
    rw [hs tau]
    have hz : ∀ q : XiZeroCopy, xiWardRightZeroStieltjes (xiWardTransverseLevel s) tau q = 0 := by
      intro q
      rw [xiWardRightZeroStieltjes_eq_ite, if_neg (by linarith [hall q])]
    simp [hz]
  · intro hae q₀
    by_contra hq₀
    push Not at hq₀
    set a₀ : ℝ := (q₀.1 : ℂ).re - 1 / 2 with ha₀_def
    have ha₀_mem : a₀ ∈ Ioo (0 : ℝ) (1 / 2) :=
      ⟨by linarith [ha₀_def], by linarith [ha₀_def, xiZeroCopy_re_lt_one q₀]⟩
    have hσ_lt_a₀ : σ < a₀ := by linarith [ha₀_def]
    set b : ℝ := (σ + a₀) / 2 with hb_def
    have hb_mem : b ∈ Ioo (0 : ℝ) (1 / 2) := ⟨by linarith [hb_def],
      by linarith [hb_def, ha₀_mem.2]⟩
    have hba₀ : b < a₀ := by linarith [hb_def]
    set s₁ : ℝ := xiWardTransverseCoordinate b
    set s₂ : ℝ := xiWardTransverseCoordinate a₀
    have hs₁₂ : s₁ < s₂ := by
      by_contra hge
      push Not at hge
      have hle := xiWardTransverseLevel_strictMono.monotone hge
      rw [xiWardTransverseLevel_coordinate hb_mem, xiWardTransverseLevel_coordinate ha₀_mem] at hle
      linarith
    have hvol_ne : volume (Ioo s₁ s₂) ≠ 0 := by
      rw [Real.volume_Ioo]
      exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hs₁₂)).ne'
    have hboth := hae.and ae_forall_xiWardGlobalCap_re_nonneg_optimized
    obtain ⟨s, hs_mem, hcap_zero, hsign⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hvol_ne (ae_restrict_of_ae hboth)
    have hlev_lo : σ < xiWardTransverseLevel s := by
      have h := xiWardTransverseLevel_strictMono hs_mem.1
      rw [xiWardTransverseLevel_coordinate hb_mem] at h
      linarith [hb_def]
    have hlev_hi : xiWardTransverseLevel s < a₀ := by
      have h := xiWardTransverseLevel_strictMono hs_mem.2
      rwa [xiWardTransverseLevel_coordinate ha₀_mem] at h
    have hq_le := (hsign tau hτ).2.mp (by rw [hcap_zero hlev_lo.le, Complex.zero_re]) q₀
    linarith [ha₀_def]

/-- **Unified Route-WD and Cross-Corpus Zero-Width Dictionary.**
For `0 ≤ σ < 1/2`, `R ≥ 1/2`, and `0 < τ ≤ 366/25`, the single invariant `zetaZeroWidth ≤ σ` is
simultaneously equivalent to:
- almost-everywhere vanishing of the Global Ward Cap above transverse level `σ`,
- all-height unheated shifted positivity of the retained finite zero-head polynomial at `σ`,
- all-height arbitrarily-small-heat shifted positivity of the retained finite zero-head polynomial
  at `σ`,
- the graded prime-side, theta-side, Suzuki, thermal, CCM/HCF, and dyadic-window laws of
  `theRoutesMeasureOneZeroWidth`,
and implies `wdHeatThreshold ≤ σ² / 3`, `newmanConstant ≤ σ² / 2`, `collisionMass u = 0` for all
`u > σ² / 2`, Lagarias strip positivity right of `1/2 + σ`, and Laguerre–Pólya real-rootedness of
`cos(hD)Ξ` for every `h > σ`. -/
theorem routeWD_and_corpus_zeroWidth_dictionary {σ R tau : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2)
    (hR : 1 / 2 ≤ R) (hτ : tau ∈ Ioc (0 : ℝ) (366 / 25)) :
    (zetaZeroWidth ≤ σ ↔
      ∀ᵐ s : ℝ ∂(volume : Measure ℝ), σ ≤ xiWardTransverseLevel s →
        ∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
            continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x) = 0) ∧
    (zetaZeroWidth ≤ σ ↔
      ∀ t : ℝ, CoeffNonneg (taylor σ
        (expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R))))) ∧
    (zetaZeroWidth ≤ σ ↔
      ∀ lam > 0, ∀ t : ℝ, CoeffNonneg (taylor σ (forwardPolyHeat (lam / 2)
        (expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)))))) ∧
    (zetaZeroWidth ≤ σ →
      DeBruijn.wdHeatThreshold ≤ σ ^ 2 / 3 ∧
      DeBruijn.newmanConstant ≤ σ ^ 2 / 2 ∧
      (∀ u : ℝ, σ ^ 2 / 2 < u → DeBruijn.collisionMass u = 0) ∧
      (∀ z : ℂ, 1 / 2 + σ < z.re → xi z ≠ 0 → 0 ≤ (logDeriv xi z).re) ∧
      (∀ h : ℝ, σ < h →
        GaloisForLFunctions.HTGeometry.LaguerrePolya
          (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2))) ∧
    ((zetaZeroWidth ≤ σ ↔ ConvergesRightOf logZetaRegCoeff (1 / 2 + σ)) ∧
      (zetaZeroWidth ≤ σ ↔ ∀ u : ℝ, 0 < u → u < 1 / 2 - σ → WoldNatResidualSquareEnergy u) ∧
      (zetaZeroWidth ≤ σ ↔ SuzukiZetaZeroFreeRightOf σ) ∧
      (zetaZeroWidth ≤ σ ↔ ∀ m : ℕ, xiThermalProjectiveMoment m ≤
        normalizedPrimeArchMoment 0 * σ ^ m) ∧
      (zetaZeroWidth ≤ σ ↔ CriticalMellinDefectAnalyticAbove σ) ∧
      (zetaZeroWidth ≤ σ ↔ ∃ N : ℕ, DyadicWeightedPrimeWindowPowerUpper σ N) ∧
      (zetaZeroWidth ≤ σ ↔ xiProjectiveReflectionRadius ≤ σ)) := by
  refine ⟨zetaZeroWidth_le_iff_ae_xiWardGlobalCap_eq_zero_above hσ0 hτ,
    zetaZeroWidth_le_iff_forall_taylor_finiteHead_nonneg hσ0 hR,
    zetaZeroWidth_le_iff_forall_pos_taylor_forwardPolyHeat_finiteHead_nonneg hσ0 hR,
    fun hw => ?_,
    theRoutesMeasureOneZeroWidth hσ0 hσ⟩
  have hsq : zetaZeroWidth ^ 2 ≤ σ ^ 2 :=
    pow_le_pow_left₀ zetaZeroWidth_nonneg hw 2
  have hwd : DeBruijn.wdHeatThreshold ≤ σ ^ 2 / 3 :=
    DeBruijn.wdHeatThreshold_le_third_sq_zetaZeroWidth.trans (by linarith)
  have hΛ : DeBruijn.newmanConstant ≤ σ ^ 2 / 2 := by
    have hΛ0 : DeBruijn.newmanConstant ≤ zetaZeroWidth ^ 2 / 2 :=
      csInf_le DeBruijn.realRootedTimes_bddBelow
        ⟨by positivity,
          fun _ hz => riemannHeat_zeros_real_of_half_sq_zetaZeroWidth_le le_rfl hz⟩
    linarith
  refine ⟨hwd, hΛ,
    fun u hu => DeBruijn.collisionMass_eq_zero_of_half_sq_zetaZeroWidth_lt (by linarith),
    fun z hz hxi => re_logDeriv_xi_nonneg_of_zetaZeroWidth_le hw hz hxi,
    fun h hh => laguerrePolya_cosineShiftXi_of_zetaZeroWidth_lt (lt_of_le_of_lt hw hh)⟩

end

end RHTower

