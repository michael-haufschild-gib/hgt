import GaloisForLFunctions.FiniteFreeProbability.JensenStripContraction
import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.TheZeroMassHasItsSecondTerm
import GaloisForLFunctions.RHTower.PrimeArchHausdorffFixedOrderLargeShiftPositivity
import GaloisForLFunctions.RHTower.VerifiedHeightAmplification
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# Jensen polynomials of degree `≲ (T log T)^{1/4}` from verified zeros

**Theorem** (`jensenNonrealCount_eq_zero_of_verified`). If RH holds through `T ≥ 1` and
`2·10⁷ d⁴ ≤ T log T` with `d ≥ 1`, then `R_d(Ξ)` has only real roots. The condition forces `T ≥ e¹²`, the height
from which the two-sided Riemann–von Mangoldt count is used.

Split the zeros at height `T`. The verified zeros are real, so their symbol creates no non-real root
(Hermite–Poulain). The tail `t = ∏_{|γ| > T} (1 - w/ρ)` satisfies `t(w) = t(-w)`, hence
`|t(w) e^{cw²}|² = ∏ |E₁(w²/ρ²)|`, `2c = Σ ρ⁻²`, and the fourth inverse moment of the tail controls this on a
circle. The Riemann–von Mangoldt count gives `2c ≳ log T / T` and `Σ |ρ|⁻⁴ ≲ log T / T³`, so the Gaussian factor
contracts the root strip of the remainder to the real line.
-/

open Polynomial Filter Topology Complex Set
open GaloisForLFunctions.HTGeometry RHTower FiniteFreeProbability
open scoped ComplexConjugate

namespace GaloisForLFunctions.VerifiedHeightRungs

noncomputable section

/-! ## Spectral coordinates of the zero copies -/

theorem re_xiSpectralPoint (q : XiZeroCopy) : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
  simp [xiSpectralPoint]

theorem im_xiSpectralPoint (q : XiZeroCopy) : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
  simp [xiSpectralPoint]

theorem abs_im_xiSpectralPoint_lt (q : XiZeroCopy) : |(xiSpectralPoint q).im| < 1 / 2 := by
  have h := xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support q.1)
  rw [im_xiSpectralPoint, abs_lt]
  constructor <;> linarith only [h.1, h.2]

/-- Verified zeros have real spectral points. -/
theorem im_xiSpectralPoint_eq_zero {T : ℝ} (hRH : RHVerifiedThrough T) (q : XiZeroCopy)
    (hq : |(xiSpectralPoint q).re| ≤ T) : (xiSpectralPoint q).im = 0 := by
  have hρ := xi_eq_zero_of_mem_divisor_support q.1
  have hstrip := xi_zero_re_mem_open_unit hρ
  have him := xiSupport_im_ne_zero q.1
  rw [re_xiSpectralPoint] at hq
  rw [im_xiSpectralPoint]
  rcases lt_or_gt_of_ne him with hneg | hpos
  · have hc : xi ((starRingEnd ℂ) (q.1 : ℂ)) = 0 := by rw [xi_conj, hρ, map_zero]
    have h := hRH hc (by simpa using hstrip.1) (by simpa using hstrip.2)
      (by simpa using hneg) (by
        rw [Complex.conj_im]
        rw [abs_of_neg hneg] at hq
        exact hq)
    rw [Complex.conj_re] at h
    linarith only [h]
  · have h := hRH hρ hstrip.1 hstrip.2 hpos (by
      rw [abs_of_pos hpos] at hq
      exact hq)
    linarith only [h]

theorem re_inv_sq_eq (w : ℂ) : ((w ^ 2)⁻¹).re = (w.re ^ 2 - w.im ^ 2) / (w.re ^ 2 + w.im ^ 2) ^ 2 := by
  rw [Complex.inv_re, map_pow, Complex.normSq_apply, sq w, Complex.mul_re]
  ring_nf

theorem re_inv_sq_nonneg {w : ℂ} (h : |w.im| ≤ |w.re|) : 0 ≤ ((w ^ 2)⁻¹).re := by
  rw [re_inv_sq_eq]
  apply div_nonneg _ (sq_nonneg _)
  have := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, sq_abs] at this
  linarith only [this]

/-- A band term of `Σ ρ⁻²` is at least `1/(50 T²)`. -/
theorem le_re_inv_sq {w : ℂ} {T : ℝ} (hT : 1 ≤ T) (hx : T < |w.re|) (hx2 : |w.re| ≤ 2 * T)
    (hy : |w.im| < 1 / 2) : 1 / (50 * T ^ 2) ≤ ((w ^ 2)⁻¹).re := by
  rw [re_inv_sq_eq]
  have hT0 : 0 < T := by linarith only [hT]
  have hx1 : T ^ 2 ≤ w.re ^ 2 := by
    rw [← sq_abs w.re]
    exact pow_le_pow_left₀ hT0.le hx.le 2
  have hx3 : w.re ^ 2 ≤ 4 * T ^ 2 := by
    rw [← sq_abs w.re]
    have := pow_le_pow_left₀ (abs_nonneg _) hx2 2
    nlinarith only [this]
  have hy1 : w.im ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs w.im]
    have := pow_le_pow_left₀ (abs_nonneg _) hy.le 2
    nlinarith only [this]
  have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
  have hN0 : 0 < w.re ^ 2 + w.im ^ 2 := by nlinarith only [hx1, hT2, sq_nonneg w.im]
  have hN1 : w.re ^ 2 + w.im ^ 2 ≤ 5 * T ^ 2 := by linarith only [hx3, hy1, hT2]
  have hN2 : (w.re ^ 2 + w.im ^ 2) ^ 2 ≤ 25 * T ^ 4 := by
    have := pow_le_pow_left₀ hN0.le hN1 2
    nlinarith only [this]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hnum : T ^ 2 / 2 ≤ w.re ^ 2 - w.im ^ 2 := by linarith only [hx1, hy1, hT2]
  have h1 : 50 * T ^ 2 * (T ^ 2 / 2) ≤ 50 * T ^ 2 * (w.re ^ 2 - w.im ^ 2) :=
    mul_le_mul_of_nonneg_left hnum (by positivity)
  nlinarith only [h1, hN2]

/-! ## Riemann–von Mangoldt input -/

/-- The band `(T, 2T]` carries at least `0.27 T log T` copies. -/
theorem le_card_band {T : ℝ} (hT : Real.exp 12 ≤ T) :
    27 / 100 * (T * Real.log T) ≤ ((xiCopiesBand T (2 * T)).card : ℝ) := by
  have hT0 : 0 < T := (Real.exp_pos 12).trans_le hT
  rw [card_xiCopiesBand_eq_real hT0.le (by linarith only [hT0])]
  exact le_xiSymmetricMass_band_of_exp_twelve_le hT

theorem sum_dyadic_le (K : ℕ) :
    ∑ k ∈ Finset.range K, ((k : ℝ) + 2) / 8 ^ k = 120 / 49 - (8 / 7 * K + 120 / 49) / 8 ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have h8 : ((8 : ℝ) ^ K) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- **The fourth inverse moment of the tail.** -/
theorem sum_inv_norm_four_le {T : ℝ} (hT : Real.exp 12 ≤ T) (B : Finset XiZeroCopy)
    (hB : ∀ q ∈ B, T < |(xiSpectralPoint q).re|) :
    ∑ q ∈ B, (‖xiSpectralPoint q‖ ^ 4)⁻¹ ≤ 17 / 10 * (Real.log T / T ^ 3) := by
  classical
  have hT4 : 4 ≤ T := four_le_of_exp_twelve_le hT
  have hT0 : 0 < T := by linarith only [hT4]
  have hL : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith only [hT4])
  have hL0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith only [hT4])
  -- The sum over ordinates up to `2^K T` is dominated by its dyadic majorant.
  have hstep (K : ℕ) : ∑ q ∈ B.filter fun q => |(xiSpectralPoint q).re| ≤ 2 ^ K * T,
      (‖xiSpectralPoint q‖ ^ 4)⁻¹ ≤
      66 / 100 * (Real.log T / T ^ 3) * ∑ k ∈ Finset.range K, ((k : ℝ) + 2) / 8 ^ k := by
    induction K with
    | zero =>
      rw [Finset.filter_false_of_mem, Finset.sum_empty]
      · simp
      · intro q hq
        have := hB q hq
        rw [pow_zero, one_mul]
        exact not_le.2 this
    | succ K ih =>
      set X := (2 : ℝ) ^ K * T with hX
      have hX0 : 0 < X := by positivity
      have hX1 : T ≤ X := by
        rw [hX]
        exact le_mul_of_one_le_left hT0.le (one_le_pow₀ (by norm_num))
      have h2X : (2 : ℝ) ^ (K + 1) * T = 2 * X := by
        rw [hX, pow_succ]
        ring
      rw [h2X]
      have h2Xh : Real.exp 12 ≤ 2 * X := hT.trans (by linarith only [hX1, hT0])
      set S := B.filter fun q => |(xiSpectralPoint q).re| ≤ 2 * X with hS
      set S₀ := B.filter fun q => |(xiSpectralPoint q).re| ≤ X with hS₀
      have hsub : S₀ ⊆ S := by
        intro q hq
        rw [hS₀, Finset.mem_filter] at hq
        rw [hS, Finset.mem_filter]
        exact ⟨hq.1, hq.2.trans (by linarith only [hX0])⟩
      rw [← Finset.sum_sdiff hsub]
      -- The new shell.
      have hshell : ∑ q ∈ S \ S₀, (‖xiSpectralPoint q‖ ^ 4)⁻¹ ≤
          ((S \ S₀).card : ℝ) * (X ^ 4)⁻¹ := by
        rw [← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul _ _ _ fun q hq => ?_
        rw [Finset.mem_sdiff, hS, hS₀, Finset.mem_filter, Finset.mem_filter] at hq
        have hgt : X < |(xiSpectralPoint q).re| := by
          by_contra hc
          exact hq.2 ⟨hq.1.1, not_lt.1 hc⟩
        have hn : X ≤ ‖xiSpectralPoint q‖ := hgt.le.trans (Complex.abs_re_le_norm _)
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hX0.le hn 4)
      have hcard : ((S \ S₀).card : ℝ) ≤ xiSymmetricMass (2 * X) := by
        refine card_le_xiSymmetricMass_of_forall_abs_im_le (by positivity) fun q hq => ?_
        rw [Finset.mem_sdiff, hS, Finset.mem_filter] at hq
        rw [← re_xiSpectralPoint]
        exact hq.1.2
      have hmass := xiSymmetricMass_le_of_exp_twelve_le h2Xh
      -- `log 2X ≤ (K + 2) log T`.
      have hlog2X : Real.log (2 * X) ≤ ((K : ℝ) + 2) * Real.log T := by
        have e : 2 * X = 2 ^ (K + 1) * T := by
          rw [hX, pow_succ]
          ring
        rw [e, Real.log_mul (by positivity) hT0.ne', Real.log_pow]
        push_cast
        nlinarith only [hL, (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1)]
      have hterm : ((S \ S₀).card : ℝ) * (X ^ 4)⁻¹ ≤
          66 / 100 * (Real.log T / T ^ 3) * (((K : ℝ) + 2) / 8 ^ K) := by
        have hX4 : 0 < X ^ 4 := by positivity
        rw [← div_eq_mul_inv, div_le_iff₀ hX4]
        have hbound : ((S \ S₀).card : ℝ) ≤ 33 / 100 * (2 * X * (((K : ℝ) + 2) * Real.log T)) := by
          refine hcard.trans (hmass.trans ?_)
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlog2X (by positivity)) (by norm_num)
        refine hbound.trans (le_of_eq ?_)
        have hX3 : X ^ 3 = 8 ^ K * T ^ 3 := by
          rw [hX, mul_pow, ← pow_mul, mul_comm K 3, pow_mul]
          norm_num
        have hX4' : X ^ 4 = X * (8 ^ K * T ^ 3) := by
          rw [← hX3]
          ring
        rw [hX4']
        have h8 : ((8 : ℝ) ^ K) ≠ 0 := by positivity
        field_simp
        ring
      rw [Finset.sum_range_succ, mul_add]
      linarith only [hshell, hterm, ih]
  -- Choose `K` above every ordinate.
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ q ∈ B, |(xiSpectralPoint q).re| ≤ 2 ^ K * T := by
    obtain ⟨M, hM⟩ := (B.image fun q => |(xiSpectralPoint q).re|).exists_le
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (M / T) (by norm_num : (1 : ℝ) < 2)
    refine ⟨K, fun q hq => (hM _ (Finset.mem_image_of_mem _ hq)).trans ?_⟩
    rw [div_lt_iff₀ hT0] at hK
    exact hK.le
  have hall := hstep K
  rw [Finset.filter_true_of_mem hK] at hall
  refine hall.trans ?_
  have hsum : ∑ k ∈ Finset.range K, ((k : ℝ) + 2) / 8 ^ k ≤ 120 / 49 := by
    rw [sum_dyadic_le]
    have : 0 ≤ (8 / 7 * (K : ℝ) + 120 / 49) / 8 ^ K := by positivity
    linarith only [this]
  have hpos : 0 ≤ Real.log T / T ^ 3 := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left hsum hpos, hpos]

/-! ## The factorization at height `T` -/

/-- The verified symbol creates no non-real root. -/
theorem nonrealRootCount_diffOp_real_prod {ι : Type*} [DecidableEq ι] (A : Finset ι) (γ : ι → ℝ)
    (hγ : ∀ q ∈ A, γ q ≠ 0) (p : ℝ[X]) :
    nonrealRootCount (diffOp (∏ q ∈ A, (1 - C (γ q)⁻¹ * X)) p) ≤ nonrealRootCount p := by
  induction A using Finset.induction_on with
  | empty => simp [diffOp]
  | insert a A ha ih =>
    rw [Finset.prod_insert ha, diffOp_mul]
    have hne : γ a ≠ 0 := hγ a (Finset.mem_insert_self a A)
    have hfac : (1 : ℝ[X]) - C (γ a)⁻¹ * X = C (-(γ a)⁻¹) * (X - C (γ a)) := by
      have h1 : C (γ a)⁻¹ * C (γ a) = (1 : ℝ[X]) := by rw [← C_mul, inv_mul_cancel₀ hne, C_1]
      rw [C_neg]
      linear_combination (-1 : ℝ[X]) * h1
    have hk : -(γ a)⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hne)
    rw [hfac, diffOp_C_mul_left, nonrealRootCount_C_mul hk]
    exact (diffOp_X_sub_C_count hne _).2.trans
      (ih fun q hq => hγ q (Finset.mem_insert_of_mem hq))

/-- The copies above height `T` in the `n`-th symmetric zero set. -/
def tailFinset (T : ℝ) (n : ℕ) : Finset XiZeroCopy :=
  (xiPairedCopyFinset (DeBruijn.xiConjClosedFinset n)).filter
    fun q => ¬ |(xiSpectralPoint q).re| ≤ T

/-- The copies through height `T` in the `n`-th symmetric zero set. -/
def headFinset (T : ℝ) (n : ℕ) : Finset XiZeroCopy :=
  (xiPairedCopyFinset (DeBruijn.xiConjClosedFinset n)).filter
    fun q => |(xiSpectralPoint q).re| ≤ T

theorem mem_tailFinset_lineConj {T : ℝ} {n : ℕ} {q : XiZeroCopy} :
    xiZeroCopyLineConjEquiv q ∈ tailFinset T n ↔ q ∈ tailFinset T n := by
  have hre : (xiSpectralPoint (xiZeroCopyLineConjEquiv q)).re = (xiSpectralPoint q).re := by
    rw [xiSpectralPoint_lineConj, Complex.conj_re]
  simp only [tailFinset, Finset.mem_filter, hre]
  rw [← DeBruijn.xiZeroCopyLineConjEquiv_mem_iff]

theorem mem_tailFinset_reflect {T : ℝ} {n : ℕ} {q : XiZeroCopy} :
    xiZeroCopyReflectEquiv q ∈ tailFinset T n ↔ q ∈ tailFinset T n := by
  have hre : |(xiSpectralPoint (xiZeroCopyReflectEquiv q)).re| = |(xiSpectralPoint q).re| := by
    rw [xiSpectralPoint_reflect, Complex.neg_re, abs_neg]
  simp only [tailFinset, Finset.mem_filter, hre, xiPairedCopyFinset_reflect_mem_iff]

theorem exists_real_tail (T : ℝ) (n : ℕ) :
    ∃ t : ℝ[X], t.map Complex.ofRealHom = DeBruijn.xiZeroPoly (tailFinset T n) := by
  have hconj : (DeBruijn.xiZeroPoly (tailFinset T n)).map (starRingEnd ℂ) =
      DeBruijn.xiZeroPoly (tailFinset T n) := by
    rw [DeBruijn.xiZeroPoly, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, map_X, map_inv₀]
    refine Finset.prod_equiv xiZeroCopyLineConjEquiv (fun q => mem_tailFinset_lineConj.symm) ?_
    intro q _
    rw [xiSpectralPoint_lineConj]
  have hmem : DeBruijn.xiZeroPoly (tailFinset T n) ∈ lifts Complex.ofRealHom := by
    rw [lifts_iff_coeff_lifts]
    intro k
    have h := congrArg (fun P => P.coeff k) hconj
    simp only [coeff_map] at h
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp h
    exact ⟨r, hr.symm⟩
  exact (mem_lifts _).mp hmem

/-- `Σ ρ⁻²` over the tail is real. -/
theorem sum_inv_sq_tail_real (T : ℝ) (n : ℕ) :
    ∑ q ∈ tailFinset T n, ((xiSpectralPoint q) ^ 2)⁻¹ =
      ((∑ q ∈ tailFinset T n, ((xiSpectralPoint q) ^ 2)⁻¹).re : ℝ) := by
  have h : conj (∑ q ∈ tailFinset T n, ((xiSpectralPoint q) ^ 2)⁻¹) =
      ∑ q ∈ tailFinset T n, ((xiSpectralPoint q) ^ 2)⁻¹ := by
    rw [map_sum]
    refine Finset.sum_equiv xiZeroCopyLineConjEquiv (fun q => mem_tailFinset_lineConj.symm) ?_
    intro q _
    rw [xiSpectralPoint_lineConj, map_inv₀, map_pow]
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp h
  rw [hr, Complex.ofReal_re]

/-- **Size of the tail with its Gaussian removed.** -/
theorem norm_tail_mul_exp_le {T : ℝ} {n : ℕ} {c : ℝ}
    (hc : (2 * c : ℂ) = ∑ q ∈ tailFinset T n, ((xiSpectralPoint q) ^ 2)⁻¹) (w : ℂ) :
    ‖(DeBruijn.xiZeroPoly (tailFinset T n)).eval w * Complex.exp (c * w ^ 2)‖ ^ 2 ≤
      Real.exp (2 * ‖w‖ ^ 4 * ∑ q ∈ tailFinset T n, (‖xiSpectralPoint q‖ ^ 4)⁻¹) := by
  set B := tailFinset T n with hB
  have hne (q : XiZeroCopy) : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have heven : (DeBruijn.xiZeroPoly B).eval (-w) = (DeBruijn.xiZeroPoly B).eval w := by
    rw [DeBruijn.eval_xiZeroPoly, DeBruijn.eval_xiZeroPoly]
    refine Finset.prod_equiv xiZeroCopyReflectEquiv (fun q => mem_tailFinset_reflect.symm) ?_
    intro q _
    rw [xiSpectralPoint_reflect]
    field_simp [hne q]
  have hsq : ‖(DeBruijn.xiZeroPoly B).eval w‖ ^ 2 =
      ∏ q ∈ B, ‖1 - (w / xiSpectralPoint q) ^ 2‖ := by
    have h1 : ‖(DeBruijn.xiZeroPoly B).eval w‖ ^ 2 =
        ‖(DeBruijn.xiZeroPoly B).eval w * (DeBruijn.xiZeroPoly B).eval (-w)‖ := by
      rw [heven, norm_mul, sq]
    rw [h1, DeBruijn.eval_xiZeroPoly, DeBruijn.eval_xiZeroPoly, ← Finset.prod_mul_distrib,
      norm_prod]
    refine Finset.prod_congr rfl fun q _ => ?_
    congr 1
    field_simp [hne q]
    ring
  have hexp : ‖Complex.exp (c * w ^ 2)‖ ^ 2 =
      ∏ q ∈ B, ‖Complex.exp ((w / xiSpectralPoint q) ^ 2)‖ := by
    have h1 : ‖Complex.exp (c * w ^ 2)‖ ^ 2 = ‖Complex.exp (2 * c * w ^ 2)‖ := by
      rw [sq, ← norm_mul, ← Complex.exp_add]
      congr 2
      ring
    rw [h1, hc, ← norm_prod, ← Complex.exp_sum, Finset.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun q _ => ?_
    field_simp [hne q]
  rw [norm_mul, mul_pow, hsq, hexp, ← Finset.prod_mul_distrib]
  have hbound (q : XiZeroCopy) :
      ‖1 - (w / xiSpectralPoint q) ^ 2‖ * ‖Complex.exp ((w / xiSpectralPoint q) ^ 2)‖ ≤
        Real.exp (2 * ‖w‖ ^ 4 * (‖xiSpectralPoint q‖ ^ 4)⁻¹) := by
    have h := DeBruijn.norm_weierstrassE1_le_exp_two_mul_sq ((w / xiSpectralPoint q) ^ 2)
    rw [weierstrassE1, norm_mul] at h
    refine h.trans (Real.exp_le_exp.2 (le_of_eq ?_))
    rw [norm_pow, norm_div]
    field_simp
  refine (Finset.prod_le_prod (fun _ _ => by positivity) fun q _ => hbound q).trans (le_of_eq ?_)
  rw [← Real.exp_sum, Finset.mul_sum]

/-- The tail of the `n`-th approximant is real-rooted once it contains the band `(T, 2T]`. -/
theorem nonrealRootCount_tail_eq_zero {T : ℝ} (hT : Real.exp 12 ≤ T) {d n : ℕ}
    (hd : 2 * 10 ^ 7 * (d : ℝ) ^ 4 ≤ T * Real.log T)
    (hband : xiCopiesBand T (2 * T) ⊆ tailFinset T n) {t : ℝ[X]}
    (ht : t.map Complex.ofRealHom = DeBruijn.xiZeroPoly (tailFinset T n)) :
    nonrealRootCount (diffOp t (X ^ d)) = 0 := by
  classical
  have hT4 : 4 ≤ T := four_le_of_exp_twelve_le hT
  have hT0 : 0 < T := by linarith only [hT4]
  have hL0 : 0 < Real.log T := Real.log_pos (by linarith only [hT4])
  set B := tailFinset T n with hB
  have hBgt : ∀ q ∈ B, T < |(xiSpectralPoint q).re| := fun q hq => by
    rw [hB, tailFinset, Finset.mem_filter] at hq
    exact not_le.1 hq.2
  -- The Gaussian coefficient.
  set P := ∑ q ∈ B, ((xiSpectralPoint q) ^ 2)⁻¹ with hP
  have hPreal : P = (P.re : ℝ) := sum_inv_sq_tail_real T n
  set c : ℝ := P.re / 2 with hc
  have hcC : (2 * c : ℂ) = P := by
    conv_rhs => rw [hPreal]
    rw [hc]
    push_cast
    ring
  have hPlow : 27 / 5000 * (Real.log T / T) ≤ P.re := by
    have hre : P.re = ∑ q ∈ B, (((xiSpectralPoint q) ^ 2)⁻¹).re := by
      rw [hP, Complex.re_sum]
    rw [hre]
    have hnn : ∀ q ∈ B, 0 ≤ (((xiSpectralPoint q) ^ 2)⁻¹).re := fun q hq => by
      apply re_inv_sq_nonneg
      have h1 := abs_im_xiSpectralPoint_lt q
      have h2 := hBgt q hq
      linarith only [h1, h2, hT4]
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg hband (fun q hq _ => hnn q hq)
    refine le_trans ?_ hsub
    have hlow : ∀ q ∈ xiCopiesBand T (2 * T), 1 / (50 * T ^ 2) ≤ (((xiSpectralPoint q) ^ 2)⁻¹).re := by
      intro q hq
      rw [mem_xiCopiesBand, ← re_xiSpectralPoint] at hq
      exact le_re_inv_sq (by linarith only [hT4]) hq.1 hq.2 (abs_im_xiSpectralPoint_lt q)
    have hsum := Finset.card_nsmul_le_sum _ _ _ hlow
    rw [nsmul_eq_mul] at hsum
    refine le_trans ?_ hsum
    have hcard := le_card_band hT
    calc
      27 / 5000 * (Real.log T / T) = 27 / 100 * (T * Real.log T) * (1 / (50 * T ^ 2)) := by
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hPpos : 0 < 27 / 5000 * (Real.log T / T) := by positivity
  have hcpos : 0 < c := by
    rw [hc]
    linarith only [hPlow, hPpos]
  -- The moment and the radius.
  set M₄ := 17 / 10 * (Real.log T / T ^ 3) with hM₄
  have hM₄pos : 0 < M₄ := by positivity
  have hmom := sum_inv_norm_four_le hT B hBgt
  set ρ₂ := Real.sqrt (M₄⁻¹) with hρ₂
  have hρ₂pos : 0 < ρ₂ := Real.sqrt_pos.2 (inv_pos.2 hM₄pos)
  have hρ₂sq : ρ₂ ^ 2 = M₄⁻¹ := Real.sq_sqrt (inv_pos.2 hM₄pos).le
  set r := Real.sqrt ρ₂ with hr
  have hrpos : 0 < r := Real.sqrt_pos.2 hρ₂pos
  have hr2 : r ^ 2 = ρ₂ := Real.sq_sqrt hρ₂pos.le
  have hr4 : r ^ 4 * M₄ = 1 := by
    have : r ^ 4 = M₄⁻¹ := by
      calc r ^ 4 = (r ^ 2) ^ 2 := by ring
        _ = M₄⁻¹ := by rw [hr2, hρ₂sq]
    rw [this, inv_mul_cancel₀ hM₄pos.ne']
  have ht0 : t.coeff 0 = 1 := by
    have h := congrArg (eval 0) ht
    have h2 := eval_map_apply (p := t) (f := Complex.ofRealHom) (0 : ℝ)
    rw [map_zero] at h2
    rw [h2, DeBruijn.eval_xiZeroPoly] at h
    simp only [zero_div, sub_zero, Finset.prod_const_one] at h
    rw [coeff_zero_eq_eval_zero]
    rw [Complex.ofRealHom_eq_coe] at h
    exact_mod_cast h
  refine nonrealRootCount_diffOp_X_pow_eq_zero ht0 d (c := c) (r := r) (M := Real.exp 1) hcpos hrpos
    (Real.exp_pos 1).le ?_ ?_
  · -- `|t e^{c·²}| ≤ e` on the circle.
    intro w hw
    rw [ht]
    have hmain := norm_tail_mul_exp_le hcC w
    have hbd : 2 * ‖w‖ ^ 4 * ∑ q ∈ B, (‖xiSpectralPoint q‖ ^ 4)⁻¹ ≤ 2 := by
      rw [hw]
      have h1 : r ^ 4 * ∑ q ∈ B, (‖xiSpectralPoint q‖ ^ 4)⁻¹ ≤ r ^ 4 * M₄ :=
        mul_le_mul_of_nonneg_left hmom (by positivity)
      rw [hr4] at h1
      linarith only [h1]
    have h2 := hmain.trans (Real.exp_le_exp.2 hbd)
    apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos 1).le).mp
    refine h2.trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]
    norm_num
  · -- The strip is contracted to the real line.
    have he : 1 + Real.exp 1 ≤ 4 := by
      have := Real.exp_one_lt_d9
      linarith only [this]
    have he0 : 0 ≤ 1 + Real.exp 1 := by positivity
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h1 : ((1 + Real.exp 1) * d / r) ^ 2 ≤ 16 * (d : ℝ) ^ 2 / ρ₂ := by
      rw [div_pow, mul_pow, hr2]
      apply div_le_div_of_nonneg_right _ hρ₂pos.le
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have := pow_le_pow_left₀ he0 he 2
      linarith only [this]
    refine h1.trans ?_
    have h2c : 2 * c = P.re := by
      rw [hc]
      ring
    rw [h2c]
    refine le_trans ?_ hPlow
    -- Square both sides.
    have hρinv : 1 / ρ₂ = Real.sqrt M₄ := by
      rw [hρ₂, Real.sqrt_inv, one_div, inv_inv]
    have hsqrt : Real.sqrt M₄ ^ 2 = M₄ := Real.sq_sqrt hM₄pos.le
    have hlhs : 16 * (d : ℝ) ^ 2 / ρ₂ = 16 * (d : ℝ) ^ 2 * Real.sqrt M₄ := by
      rw [← hρinv]
      ring
    rw [hlhs]
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    have hT3 : 0 < T ^ 3 := by positivity
    have e1 : (16 * (d : ℝ) ^ 2 * Real.sqrt M₄) ^ 2 =
        (256 * (17 / 10) * (d : ℝ) ^ 4) * Real.log T / T ^ 3 := by
      rw [mul_pow, hsqrt, hM₄]
      ring
    have e2 : (27 / 5000 * (Real.log T / T)) ^ 2 =
        ((27 / 5000 : ℝ) ^ 2 * (T * Real.log T)) * Real.log T / T ^ 3 := by
      field_simp
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ hT3.le
    apply mul_le_mul_of_nonneg_right _ hL0.le
    have : (256 * (17 / 10) : ℝ) * (2 * 10 ^ 7)⁻¹ ≤ (27 / 5000 : ℝ) ^ 2 := by norm_num
    have hd4 : (d : ℝ) ^ 4 ≤ (2 * 10 ^ 7)⁻¹ * (T * Real.log T) := by
      rw [inv_mul_eq_div, le_div_iff₀ (by norm_num)]
      linarith only [hd]
    have hprod : 0 ≤ T * Real.log T := by positivity
    calc
      256 * (17 / 10) * (d : ℝ) ^ 4 ≤ 256 * (17 / 10) * ((2 * 10 ^ 7)⁻¹ * (T * Real.log T)) :=
        mul_le_mul_of_nonneg_left hd4 (by norm_num)
      _ = (256 * (17 / 10) * (2 * 10 ^ 7)⁻¹) * (T * Real.log T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this hprod

/-- **Jensen rung.** If RH holds through `T ≥ e¹²` and `2·10⁷ d⁴ ≤ T log T`, then `R_d(Ξ)` has
only real roots. -/
theorem jensenNonrealCount_eq_zero_of_rhVerifiedThrough {T : ℝ} (hT : Real.exp 12 ≤ T)
    (hRH : RHVerifiedThrough T) {d : ℕ} (hd : 2 * 10 ^ 7 * (d : ℝ) ^ 4 ≤ T * Real.log T) :
    jensenNonrealCount d = 0 := by
  classical
  have hT4 : 4 ≤ T := four_le_of_exp_twelve_le hT
  have hT0 : 0 < T := by linarith only [hT4]
  -- From some index on, the approximants contain the whole band.
  have hlim : Tendsto (fun n => xiPairedCopyFinset (DeBruijn.xiConjClosedFinset n)) atTop atTop :=
    xiPairedCopyFinset_tendsto_atTop.comp DeBruijn.xiConjClosedFinset_tendsto
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hlim.eventually_ge_atTop (xiCopiesBand T (2 * T)))
  have hbandsub (n : ℕ) (hn : n₀ ≤ n) : xiCopiesBand T (2 * T) ⊆ tailFinset T n := by
    intro q hq
    rw [tailFinset, Finset.mem_filter]
    refine ⟨hn₀ n hn hq, ?_⟩
    rw [mem_xiCopiesBand, ← re_xiSpectralPoint] at hq
    exact not_le.2 hq.1
  set S : ℕ → ℝ[X] := fun n => diffOp (DeBruijn.xiRealApprox (n + n₀)) (X ^ d) with hS
  have hcoeff0 : ∀ n, (DeBruijn.xiRealApprox n).coeff 0 ≠ 0 := fun n => by
    rw [coeff_zero_eq_eval_zero]
    exact eval_zero_xiRealApprox n
  have hSne : ∀ n, S n ≠ 0 := fun n h => by
    have hco := coeff_diffOp_X_pow (DeBruijn.xiRealApprox (n + n₀)) (le_refl d)
    rw [show diffOp (DeBruijn.xiRealApprox (n + n₀)) (X ^ d) = S n from rfl, h, coeff_zero] at hco
    simp only [Nat.sub_self, Nat.descFactorial_zero, Nat.cast_one, mul_one] at hco
    exact hcoeff0 _ hco.symm
  have hSdeg : ∀ n, (S n).natDegree ≤ d := fun n =>
    (natDegree_diffOp_le _ _).trans (natDegree_X_pow_le d)
  -- Every approximant is real-rooted.
  have hcount : ∀ n, nonrealRootCount (S n) ≤ 0 := by
    intro n
    set m := n + n₀ with hm
    obtain ⟨t, ht⟩ := exists_real_tail T m
    have hheadreal : ∀ q ∈ headFinset T m, (xiSpectralPoint q).im = 0 := fun q hq => by
      rw [headFinset, Finset.mem_filter] at hq
      exact im_xiSpectralPoint_eq_zero hRH q hq.2
    let γ : XiZeroCopy → ℝ := fun q => (xiSpectralPoint q).re
    have hγC : ∀ q ∈ headFinset T m, ((γ q : ℝ) : ℂ) = xiSpectralPoint q := fun q hq =>
      Complex.ext (by simp [γ]) (by simp [hheadreal q hq])
    have hγ0 : ∀ q ∈ headFinset T m, γ q ≠ 0 := fun q hq h0 => by
      have := hγC q hq
      rw [h0, Complex.ofReal_zero] at this
      exact xiSpectralPoint_ne_zero q this.symm
    set r : ℝ[X] := ∏ q ∈ headFinset T m, (1 - C (γ q)⁻¹ * X) with hr
    have hrmap : r.map Complex.ofRealHom = DeBruijn.xiZeroPoly (headFinset T m) := by
      rw [hr, Polynomial.map_prod, DeBruijn.xiZeroPoly]
      refine Finset.prod_congr rfl fun q hq => ?_
      simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, map_X, map_inv₀,
        Complex.ofRealHom_eq_coe, hγC q hq]
    have hsplit : DeBruijn.xiZeroPoly (xiPairedCopyFinset (DeBruijn.xiConjClosedFinset m)) =
        DeBruijn.xiZeroPoly (headFinset T m) * DeBruijn.xiZeroPoly (tailFinset T m) := by
      simp only [DeBruijn.xiZeroPoly, headFinset, tailFinset]
      exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
    have hspec := (DeBruijn.exists_real_xiZeroPoly m).choose_spec
    have hprod : (DeBruijn.exists_real_xiZeroPoly m).choose = r * t := by
      apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
      rw [hspec, Polynomial.map_mul, hrmap, ht, hsplit]
    have hXi : (XiC 0).re ≠ 0 := by
      intro h
      apply DeBruijn.XiC_zero_ne_zero
      rw [← DeBruijn.ofReal_re_XiC_zero, h, Complex.ofReal_zero]
    change nonrealRootCount (diffOp (DeBruijn.xiRealApprox m) (X ^ d)) ≤ 0
    rw [DeBruijn.xiRealApprox, hprod, diffOp_C_mul_left, nonrealRootCount_C_mul hXi, diffOp_mul]
    refine (nonrealRootCount_diffOp_real_prod _ γ hγ0 _).trans ?_
    exact le_of_eq (nonrealRootCount_tail_eq_zero hT hd
      (hbandsub m (Nat.le_add_left _ _)) ht)
  rw [jensenNonrealCount_eq]
  refine Nat.le_zero.1 (nonrealRootCount_le_of_tendsto (xiJensenReal_ne_zero d) hSne hcount ?_)
  refine tendstoLocallyUniformly_eval_of_coeff (D := d)
    (fun n => natDegree_map_le.trans (hSdeg n))
    (natDegree_map_le.trans (natDegree_xiJensenReal d).le) fun j => ?_
  simp only [coeff_map]
  rcases le_or_gt j d with hj | hj
  · have hL : (xiJensenReal d).coeff j =
        realTaylorCoeff XiC (d - j) * (d.descFactorial (d - j) : ℝ) := by
      rw [xiJensenReal_eq, jensenRev_eq_sum, finsetSum_coeff, Finset.sum_eq_single (d - j)]
      · rw [coeff_C_mul_X_pow, if_pos (by omega), PowerSeries.coeff_mk]
      · intro i hi hij
        rw [coeff_C_mul_X_pow, if_neg (by have := Finset.mem_range.1 hi; omega)]
      · intro h'
        exact absurd (Finset.mem_range.2 (by omega)) h'
    simp only [S, coeff_diffOp_X_pow _ hj, hL, Complex.ofRealHom_eq_coe]
    push_cast
    exact ((tendsto_coeff_xiRealApprox (d - j)).comp (tendsto_add_atTop_nat n₀)).mul_const _
  · have h1 : (xiJensenReal d).coeff j = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [natDegree_xiJensenReal]; exact hj)
    have h2 : ∀ n, (S n).coeff j = 0 := fun n => coeff_eq_zero_of_natDegree_lt ((hSdeg n).trans_lt hj)
    simp only [h1, h2, map_zero, tendsto_const_nhds_iff]

end

/-- `2·10⁷ ≤ T log T` forces `T ≥ e¹²`. -/
theorem exp_twelve_le_of_le_mul_log {T : ℝ} (hT1 : 1 ≤ T) (h : 2 * 10 ^ 7 ≤ T * Real.log T) :
    Real.exp 12 ≤ T := by
  by_contra hc
  rw [not_le] at hc
  have hT0 : 0 < T := by linarith only [hT1]
  have hL : Real.log T < 12 := (Real.log_lt_iff_lt_exp hT0).mpr hc
  have hE : Real.exp 12 ≤ 162756 := by
    have h2 : Real.exp 12 = Real.exp 1 ^ 12 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h2]
    calc Real.exp 1 ^ 12 ≤ (2.7182818286 : ℝ) ^ 12 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 12
      _ ≤ _ := by norm_num
  have h1 : T * Real.log T ≤ T * 12 := mul_le_mul_of_nonneg_left hL.le hT0.le
  linarith only [h, h1, hc, hE]

/-- **Jensen rung without a height floor.** If RH holds through `T ≥ 1` and `2·10⁷ d⁴ ≤ T log T`, `d ≥ 1`,
then `R_d(Ξ)` has only real roots. -/
theorem jensenNonrealCount_eq_zero_of_verified {T : ℝ} (hT1 : 1 ≤ T) (hRH : RHVerifiedThrough T) {d : ℕ}
    (hd1 : 1 ≤ d) (hd : 2 * 10 ^ 7 * (d : ℝ) ^ 4 ≤ T * Real.log T) : jensenNonrealCount d = 0 := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hd1)
  refine jensenNonrealCount_eq_zero_of_rhVerifiedThrough
    (exp_twelve_le_of_le_mul_log hT1 ?_) hRH hd
  linarith only [hd, hd']

end GaloisForLFunctions.VerifiedHeightRungs

#print axioms GaloisForLFunctions.VerifiedHeightRungs.sum_inv_norm_four_le
#print axioms GaloisForLFunctions.VerifiedHeightRungs.nonrealRootCount_tail_eq_zero
#print axioms GaloisForLFunctions.VerifiedHeightRungs.jensenNonrealCount_eq_zero_of_rhVerifiedThrough
