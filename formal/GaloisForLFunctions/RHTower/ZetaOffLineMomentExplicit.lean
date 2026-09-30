import GaloisForLFunctions.RHTower.ZetaGateProductAFESharpHighBlock
import GaloisForLFunctions.RHTower.ZetaGateProductAFEZetaBlock
import GaloisForLFunctions.RHTower.ZetaGateProductAFEDyadicLaw
import GaloisForLFunctions.RHTower.ZetaConvexityBound

/-!
# An explicit unconditional bound for the off-line first moment

The mollified mean square of `ζΨ` on the Levinson line `Re s = ½ − R/log U`, with the mollifier
length `N = ⌊U^{1/15}⌋`, is split into dyadic blocks `[a, v]`, `v ≤ 2a`:

* for `a ≥ U^{5/6}` the sharp high-block bound gives `(c_R + ε)(v − a) + ε a`,
  `c_R = (15/(2R)) e^{2R + 4R/15}` (`exists_highBlock_bound_sharp`);
* for `U^{1/2} ≤ a < U^{5/6}`, `|Ψ| ≤ N` and the block mean square `∫_a^v |ζ|² ≪ a log U`
  (`exists_zetaBlock_meanSquare_le`) give `≪ U^{2/15 + 5/6} log U = U^{29/30} log U`;
* for `a < U^{1/2}` the convexity bound `|ζ(½ − d + it)| ≤ C t^{13/50}` gives `≪ U^{67/75}`
  (`integral_normSq_zeta_mul_edPoly_convexity`);

both lower ranges are negligible against `U/log U`.  This is the dyadic mean-square law with constant
`c_R` (`zetaDyadicMeanSquareLaw_long`), hence the mollified mean-square gate, and through the
two-thirds ceiling `4π Σ_{0 < Im ρ ≤ V} m(ρ)(Re ρ − ½) ≤ (log c_R − (5/3)R + η) V`.  At `R = 3/2`,
`log c − 5/2 = log 5 + 0.9 ≤ 2.4 log 2 + 0.9 < 0.84 π − 1/20`, so

  `Σ_{0 < Im ρ ≤ V} m(ρ) (Re ρ − ½) ≤ (21/100) V`   for all large `V`

(`eventually_offLineMoment_le`), unconditionally.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- **The low blocks by convexity.** With `|ζ(σ + it)| ≤ C t^{(1 + 1/100 − σ)/2}`, `0 < d ≤ 1/100`
and coefficients of modulus at most one,
`∫_a^v ‖ζΨ(½ − d + iτ)‖² dτ ≤ (v − a) (C v^{13/50} N)²`. -/
theorem integral_normSq_zeta_mul_edPoly_convexity {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ σ t : ℝ, -(1 / 100) ≤ σ → σ ≤ 1 + 1 / 100 → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * t ^ ((1 + 1 / 100 - σ) / 2))
    {d a v : ℝ} (hd : 0 < d) (hd' : d ≤ 1 / 100) (ha : 8 ≤ a) (hav : a ≤ v)
    {b : ℕ → ℂ} {N : ℕ} (hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) :
    (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ) *
        edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) ≤
      (v - a) * (C * v ^ ((13 : ℝ) / 50) * N) ^ 2 := by
  have hv1 : 1 ≤ v := by linarith
  have hM0 : 0 ≤ C * v ^ ((13 : ℝ) / 50) := mul_nonneg hC0 (by positivity)
  have hpoint : ∀ τ ∈ Set.Icc a v,
      ‖riemannZeta (displacedLinePt d τ) * edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2 ≤
        (C * v ^ ((13 : ℝ) / 50) * N) ^ 2 := by
    intro τ hτ
    have hτ8 : 8 ≤ τ := by linarith [hτ.1]
    have hτ1 : 1 ≤ τ := by linarith
    have hζ : ‖riemannZeta (displacedLinePt d τ)‖ ≤ C * v ^ ((13 : ℝ) / 50) := by
      have h := hC (1 / 2 - d) τ (by linarith) (by linarith) hτ8
      have hpt : displacedLinePt d τ = (((1 / 2 - d : ℝ)) : ℂ) + (τ : ℂ) * I := rfl
      rw [hpt]
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      calc τ ^ ((1 + 1 / 100 - (1 / 2 - d)) / 2) ≤ τ ^ ((13 : ℝ) / 50) :=
            Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)
        _ ≤ v ^ ((13 : ℝ) / 50) := Real.rpow_le_rpow (by linarith) hτ.2 (by norm_num)
    have hΨ : ‖edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ≤ N :=
      norm_edPoly_le_card hbn (by rw [displacedLinePt_re]; linarith)
    rw [norm_mul]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul hζ hΨ (norm_nonneg _) hM0) 2
  have hcont : Continuous (fun τ : ℝ => ‖riemannZeta (displacedLinePt d τ) *
      edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) :=
    ((continuous_riemannZeta_displacedLinePt hd).mul
      (continuous_edPoly_displacedLinePt b N d)).norm.pow 2
  have hgint : IntervalIntegrable (fun _ : ℝ => (C * v ^ ((13 : ℝ) / 50) * N) ^ 2) volume a v :=
    (continuous_const : Continuous (fun _ : ℝ =>
      (C * v ^ ((13 : ℝ) / 50) * N) ^ 2)).intervalIntegrable a v
  have h := intervalIntegral.integral_mono_on hav (hcont.intervalIntegrable a v) hgint hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  exact h

/-- `(v − a)(C v^{13/50} N)² ≤ 8 C² U^{67/75}` on a low block `v ≤ 2 U^{1/2}`, `N ≤ U^{1/15}`. -/
theorem lowBlock_power_le {C U a v : ℝ} {N : ℕ} (hC0 : 0 ≤ C) (hU1 : 1 ≤ U) (ha : 0 ≤ a)
    (hav : a ≤ v) (hv : v ≤ 2 * U ^ ((1 : ℝ) / 2)) (hN : (N : ℝ) ≤ U ^ ((1 : ℝ) / 15)) :
    (v - a) * (C * v ^ ((13 : ℝ) / 50) * N) ^ 2 ≤ 8 * C ^ 2 * U ^ ((67 : ℝ) / 75) := by
  have hU0 : 0 < U := by linarith
  have hv0 : 0 ≤ v := by linarith
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = U ^ ((1 : ℝ) / 300) := ⟨_, rfl⟩
  have hW0 : 0 < W := hW ▸ Real.rpow_pos_of_pos hU0 _
  have hpow : ∀ k : ℕ, U ^ ((k : ℝ) / 300) = W ^ k := by
    intro k
    rw [hW, ← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
    congr 1
    ring
  have h150 : U ^ ((1 : ℝ) / 2) = W ^ 150 := by rw [← hpow]; norm_num
  have h20 : U ^ ((1 : ℝ) / 15) = W ^ 20 := by rw [← hpow]; norm_num
  have h268 : U ^ ((67 : ℝ) / 75) = W ^ 268 := by rw [← hpow]; norm_num
  rw [h150] at hv
  rw [h20] at hN
  rw [h268]
  have hv13 : v ^ ((13 : ℝ) / 50) ≤ 2 * W ^ 39 := by
    calc v ^ ((13 : ℝ) / 50) ≤ (2 * W ^ 150) ^ ((13 : ℝ) / 50) :=
          Real.rpow_le_rpow hv0 hv (by norm_num)
      _ = 2 ^ ((13 : ℝ) / 50) * W ^ 39 := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast W 150,
            ← Real.rpow_mul hW0.le]
          norm_num
      _ ≤ 2 * W ^ 39 := by
          have : (2 : ℝ) ^ ((13 : ℝ) / 50) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          rw [Real.rpow_one] at this
          exact mul_le_mul_of_nonneg_right this (by positivity)
  have hfac : C * v ^ ((13 : ℝ) / 50) * N ≤ C * (2 * W ^ 39) * W ^ 20 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hv13 hC0) hN (Nat.cast_nonneg _) (by positivity)
  have hfac0 : 0 ≤ C * v ^ ((13 : ℝ) / 50) * N := by positivity
  calc (v - a) * (C * v ^ ((13 : ℝ) / 50) * N) ^ 2
      ≤ (2 * W ^ 150) * (C * (2 * W ^ 39) * W ^ 20) ^ 2 :=
        mul_le_mul (by linarith) (pow_le_pow_left₀ hfac0 hfac 2) (sq_nonneg _) (by positivity)
    _ = 8 * C ^ 2 * W ^ 268 := by ring

/-- **The middle blocks.** For `|Ψ| ≤ N`, `∫_a^v ‖ζΨ‖² ≤ N² ∫_a^v ‖ζ‖²`. -/
theorem integral_normSq_zeta_mul_edPoly_le_sq_mul {d a v : ℝ} (hd : 0 < d) (hd' : d ≤ 1 / 2)
    (hav : a ≤ v) {b : ℕ → ℂ} {N : ℕ} (hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) :
    (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ) *
        edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) ≤
      (N : ℝ) ^ 2 * ∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)‖ ^ 2 := by
  have hcont1 : Continuous (fun τ : ℝ => ‖riemannZeta (displacedLinePt d τ) *
      edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) :=
    ((continuous_riemannZeta_displacedLinePt hd).mul
      (continuous_edPoly_displacedLinePt b N d)).norm.pow 2
  have hcont2 : Continuous (fun τ : ℝ => (N : ℝ) ^ 2 * ‖riemannZeta (displacedLinePt d τ)‖ ^ 2) :=
    continuous_const.mul ((continuous_riemannZeta_displacedLinePt hd).norm.pow 2)
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hav (hcont1.intervalIntegrable a v)
    (hcont2.intervalIntegrable a v) fun τ _ => ?_
  have hΨ : ‖edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ≤ N :=
    norm_edPoly_le_card hbn (by rw [displacedLinePt_re]; linarith)
  rw [norm_mul, mul_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hΨ 2) (sq_nonneg _)

/-- **The dyadic mean-square law with the long mollifier** and constant
`c_R = (15/(2R)) e^{2R + 4R/15}`. -/
theorem zetaDyadicMeanSquareLaw_long {R : ℝ} (hR : 0 < R) :
    ZetaDyadicMeanSquareLaw R (sharpBlockConst R) := by
  have hblock := exists_highBlock_bound_sharp hR
  have hc₀0 := sharpBlockConst_nonneg hR
  obtain ⟨C, hC, hconv⟩ := exists_norm_riemannZeta_le_convexity (η := 1 / 100) (by norm_num)
    (by norm_num)
  obtain ⟨K, hK0, hzeta⟩ := exists_zetaBlock_meanSquare_le hR
  intro ε hε
  filter_upwards [hblock ε hε, hzeta, Filter.eventually_ge_atTop (Real.exp 2),
    Filter.eventually_ge_atTop (Real.exp (100 * R) + 1),
    Filter.eventually_ge_atTop ((2 : ℝ) ^ 100),
    eventually_const_mul_rpow_neg_mul_log_pow_le (8 * C ^ 2) ((8 : ℝ) / 75)
      (by norm_num) 1 hε,
    eventually_const_mul_rpow_neg_mul_log_pow_le K ((1 : ℝ) / 30) (by norm_num) 2 hε]
    with U hblockU hzetaU hUe hUR hU2 hlow hmidε
  have hU1 : (1 : ℝ) ≤ U := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith only [this, hUe]
  have hU0 : (0 : ℝ) < U := by linarith only [hU1]
  have hU3 : (3 : ℝ) ≤ U := by
    have : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ)
      linarith only [this]
    linarith only [this, hUe]
  have hlogU : 2 ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos 2) hUe
    rwa [Real.log_exp] at this
  have hlogU1 : 100 * R ≤ Real.log (U - 1) := by
    have := Real.log_le_log (Real.exp_pos _) (by linarith : Real.exp (100 * R) ≤ U - 1)
    rwa [Real.log_exp] at this
  -- the mollifier length
  have hNle : (mollLong U : ℝ) ≤ U ^ ((1 : ℝ) / 15) := mollLong_le hU0.le
  have hU25 : (2 : ℝ) ≤ U ^ ((1 : ℝ) / 15) :=
    two_le_rpow_one_div_fifteen (le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hU2)
  have hNgt := mollLong_gt U
  have hN2 : 2 ≤ mollLong U := by
    have h1 : (1 : ℝ) < mollLong U := by linarith only [hNgt, hU25]
    have : (2 : ℝ) ≤ mollLong U := by
      have : (1 : ℤ) < (mollLong U : ℤ) := by exact_mod_cast h1
      have : (2 : ℤ) ≤ (mollLong U : ℤ) := this
      exact_mod_cast this
    exact_mod_cast this
  have hN1 : 1 ≤ mollLong U := by omega
  have hNU : (mollLong U : ℝ) ≤ U - 1 := by
    have h1 : U ^ ((1 : ℝ) / 15) ≤ U ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
    have h2 : U ^ ((1 : ℝ) / 2) ≤ U / 2 := by
      have hsq : U ^ ((1 : ℝ) / 2) * U ^ ((1 : ℝ) / 2) = U := by
        rw [← Real.rpow_add hU0]
        norm_num
      have h4 : (2 : ℝ) ≤ U ^ ((1 : ℝ) / 2) :=
        le_trans hU25 (Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num))
      nlinarith [Real.rpow_nonneg hU0.le ((1 : ℝ) / 2)]
    linarith only [hNle, h1, h2, hU3]
  have hNpos : (1 : ℝ) ≤ (mollLong U : ℝ) := by exact_mod_cast hN1
  refine ⟨(mollLong U : ℝ) ^ (5 : ℕ), hbCoeff (mollLong U), mollLong U, hN1, hbCoeff_one hN2,
    fun n hn => norm_hbCoeff_le hN2 hn, fun n _ => conj_hbCoeff _ n,
    one_le_pow₀ hNpos, sum_norm_hbCoeff_mul_rpow_le hN2, ?_, ?_⟩
  · rw [Real.log_pow]
    push_cast
    have : Real.log (mollLong U : ℝ) ≤ Real.log (U - 1) :=
      Real.log_le_log (by linarith only [hNpos]) hNU
    linarith only [this]
  intro σ₀ hσ₀ hσ₀' hR1 hR2 a v ha hav hv2 hvU
  have hlogpos : 0 < Real.log (U - 1) := by
    have : 0 < 100 * R := by positivity
    linarith only [this, hlogU1]
  have hd : 0 < 1 / 2 - σ₀ := by linarith only [hσ₀']
  have hd100 : 1 / 2 - σ₀ ≤ 1 / 100 := by
    by_contra hcon
    rw [not_le] at hcon
    have : R < (1 / 2 - σ₀) * Real.log (U - 1) := by
      calc R = (1 / 100) * (100 * R) := by ring
        _ ≤ (1 / 100) * Real.log (U - 1) := by gcongr
        _ < (1 / 2 - σ₀) * Real.log (U - 1) := by gcongr
    linarith only [this, hR2]
  have hd8 : 1 / 2 - σ₀ ≤ 1 / 8 := by linarith only [hd100]
  have hpt : ∀ t : ℝ, (σ₀ : ℂ) + (t : ℂ) * I = displacedLinePt (1 / 2 - σ₀) t := fun t =>
    (displacedLinePt_half_sub σ₀ t).symm
  simp_rw [hpt]
  have hlogU0 : 0 < Real.log U := by linarith only [hlogU]
  have hdU : (1 / 2 - σ₀) * Real.log U ≤ 2 * R := by
    have hlog2 : Real.log U ≤ 2 * Real.log (U - 1) := by
      have h1 : U ≤ (U - 1) ^ 2 := by
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ U - 3) hU0.le
        nlinarith [this]
      have h2 : Real.log U ≤ Real.log ((U - 1) ^ 2) := Real.log_le_log hU0 h1
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith only [h2]
    calc (1 / 2 - σ₀) * Real.log U ≤ (1 / 2 - σ₀) * (2 * Real.log (U - 1)) :=
          mul_le_mul_of_nonneg_left hlog2 hd.le
      _ = 2 * ((1 / 2 - σ₀) * Real.log (U - 1)) := by ring
      _ ≤ 2 * R := by linarith only [hR2]
  have hva0 : 0 ≤ (sharpBlockConst R + ε) * (v - a) :=
    mul_nonneg (by positivity) (by linarith only [hav])
  have hUlog : ε * (U / Real.log U) ≤ ε * (a + U / Real.log U) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    linarith only [ha]
  rcases le_or_gt (U ^ ((5 : ℝ) / 6)) a with hhigh | hnhigh
  · have h := hblockU (1 / 2 - σ₀) hd hd8 hR1 hR2 a v ha hhigh hav hv2 hvU
    have : ε * a ≤ ε * (a + U / Real.log U) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      have : 0 ≤ U / Real.log U := by positivity
      linarith only [this]
    linarith only [h, this]
  rcases le_or_gt (U ^ ((1 : ℝ) / 2)) a with hmid | hlow'
  · -- the middle blocks by the mean square of `ζ`
    have hU8a : U ^ ((1 : ℝ) / 8) ≤ a :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)) hmid
    have hz := hzetaU (1 / 2 - σ₀) hd hd8 hR1 hdU a v hU8a hav hv2 hvU
    have hm := integral_normSq_zeta_mul_edPoly_le_sq_mul hd (by linarith only [hd100]) hav
      (b := hbCoeff (mollLong U)) (N := mollLong U) (fun n hn => norm_hbCoeff_le hN2 hn)
    have hNsq : (mollLong U : ℝ) ^ 2 ≤ U ^ ((2 : ℝ) / 15) := by
      calc (mollLong U : ℝ) ^ 2 ≤ (U ^ ((1 : ℝ) / 15)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hNle 2
        _ = U ^ ((2 : ℝ) / 15) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
            norm_num
    have hKa : K * Real.log U * a ≤ K * Real.log U * U ^ ((5 : ℝ) / 6) :=
      mul_le_mul_of_nonneg_left hnhigh.le (by positivity)
    have hint0 : 0 ≤ ∫ τ in a..v, ‖riemannZeta (displacedLinePt (1 / 2 - σ₀) τ)‖ ^ 2 :=
      intervalIntegral.integral_nonneg hav fun τ _ => by positivity
    have hstep : (mollLong U : ℝ) ^ 2
          * ∫ τ in a..v, ‖riemannZeta (displacedLinePt (1 / 2 - σ₀) τ)‖ ^ 2
        ≤ U ^ ((2 : ℝ) / 15) * (K * Real.log U * U ^ ((5 : ℝ) / 6)) :=
      mul_le_mul hNsq (hz.trans hKa) hint0 (by positivity)
    have hsplit : U ^ ((2 : ℝ) / 15) * (K * Real.log U * U ^ ((5 : ℝ) / 6))
        = (K * (U ^ (-((1 : ℝ) / 30)) * Real.log U ^ 2)) * (U / Real.log U) := by
      have e : U ^ ((2 : ℝ) / 15) * U ^ ((5 : ℝ) / 6) = U ^ (-((1 : ℝ) / 30)) * U := by
        rw [← Real.rpow_add hU0, show (2 : ℝ) / 15 + 5 / 6 = -((1 : ℝ) / 30) + 1 by norm_num,
          Real.rpow_add hU0, Real.rpow_one]
      have e2 : U ^ ((2 : ℝ) / 15) * (K * Real.log U * U ^ ((5 : ℝ) / 6))
          = K * Real.log U * (U ^ ((2 : ℝ) / 15) * U ^ ((5 : ℝ) / 6)) := by ring
      rw [e2, e]
      field_simp
    have hmain : (K * (U ^ (-((1 : ℝ) / 30)) * Real.log U ^ 2)) * (U / Real.log U)
        ≤ ε * (U / Real.log U) := mul_le_mul_of_nonneg_right hmidε (by positivity)
    rw [hsplit] at hstep
    linarith only [hm, hstep, hmain, hUlog, hva0]
  · -- the low blocks by convexity
    have hcx := integral_normSq_zeta_mul_edPoly_convexity hC.le hconv hd hd100
      (by linarith only [ha]) hav (b := hbCoeff (mollLong U)) (N := mollLong U)
      (fun n hn => norm_hbCoeff_le hN2 hn)
    have hv : v ≤ 2 * U ^ ((1 : ℝ) / 2) := by linarith only [hv2, hlow']
    have hpw := lowBlock_power_le hC.le hU1 (by linarith only [ha]) hav hv hNle
    have hsplit : 8 * C ^ 2 * U ^ ((67 : ℝ) / 75) =
        (8 * C ^ 2 * (U ^ (-((8 : ℝ) / 75)) * Real.log U ^ 1)) * (U / Real.log U) := by
      rw [pow_one]
      have e : U ^ ((67 : ℝ) / 75) = U ^ (-((8 : ℝ) / 75)) * U := by
        rw [show ((67 : ℝ) / 75) = -((8 : ℝ) / 75) + 1 by norm_num, Real.rpow_add hU0,
          Real.rpow_one]
      rw [e]
      field_simp
    have hmain : 8 * C ^ 2 * U ^ ((67 : ℝ) / 75) ≤ ε * (a + U / Real.log U) := by
      rw [hsplit]
      exact (mul_le_mul_of_nonneg_right hlow (by positivity)).trans hUlog
    linarith only [hcx, hpw, hmain, hva0]

/-- **The mollified mean-square gate with the sharp constant.** -/
theorem zetaMollifiedMeanSquareGate_sharp {R : ℝ} (hR : 0 < R) :
    ZetaMollifiedMeanSquareGate R (max (sharpBlockConst R) 1) :=
  zetaMollifiedMeanSquareGate_of_dyadicLaw hR
    (zetaDyadicMeanSquareLaw_mono (le_max_left _ _) (zetaDyadicMeanSquareLaw_long hR))

/-- `log 5 ≤ (12/5) log 2`, from `5^{10} ≤ 2^{24}`. -/
theorem log_five_le : Real.log 5 ≤ 12 / 5 * Real.log 2 := by
  have h : Real.log ((5 : ℝ) ^ (10 : ℕ)) ≤ Real.log ((2 : ℝ) ^ (24 : ℕ)) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- `log c_{3/2} − 5/2 + 1/20 ≤ 4π · 21/100`. -/
theorem log_sharpBlockConst_three_halves_le :
    Real.log (max (sharpBlockConst (3 / 2)) 1) - 5 / 3 * (3 / 2) + 1 / 20
      ≤ 4 * Real.pi * (21 / 100) := by
  have hC : sharpBlockConst (3 / 2) = 5 * Real.exp (2 * (3 / 2) + 4 * (3 / 2) / 15) := by
    unfold sharpBlockConst
    norm_num
  have hC1 : 1 ≤ sharpBlockConst (3 / 2) := by
    rw [hC]
    have h1 : (1 : ℝ) ≤ Real.exp (2 * (3 / 2) + 4 * (3 / 2) / 15) := Real.one_le_exp (by norm_num)
    nlinarith
  rw [max_eq_left hC1, hC, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
  have h1 := log_five_le
  have h2 := Real.log_two_lt_d9
  have h3 := Real.pi_gt_d2
  norm_num at h2 h3 ⊢
  linarith

/-- **The off-line first moment is at most `21/100` of the height, unconditionally.** -/
theorem eventually_offLineMoment_le :
    ∀ᶠ V in atTop, offLineMoment V ≤ 21 / 100 * V := by
  have h := eventually_offLineMoment_le_of_zetaGate_twoThirds (R := 3 / 2) (η := 1 / 20)
    (by norm_num) (le_max_right _ _) (by norm_num) (zetaMollifiedMeanSquareGate_sharp (by norm_num))
  filter_upwards [h, eventually_ge_atTop 0] with V hV hV0
  have hc := log_sharpBlockConst_three_halves_le
  have hπ : 0 < 4 * Real.pi := by positivity
  have h1 : 4 * Real.pi * offLineMoment V ≤ 4 * Real.pi * (21 / 100) * V :=
    hV.trans (mul_le_mul_of_nonneg_right hc hV0)
  have h2 : 4 * Real.pi * (21 / 100) * V = 4 * Real.pi * (21 / 100 * V) := by ring
  rw [h2] at h1
  exact le_of_mul_le_mul_left h1 hπ

end RHTower.ZetaGateProductAFE

end
