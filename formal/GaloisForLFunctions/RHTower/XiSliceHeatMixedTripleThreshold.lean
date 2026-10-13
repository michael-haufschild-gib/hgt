import GaloisForLFunctions.RHTower.XiSliceHeatIsolatedPairThreshold
import GaloisForLFunctions.RHTower.DeBruijnClusterPersistence

/-!
# The WD heat threshold of an isolated mixed triple

A mixed triple is a critical zero `½ + iγ` together with an off-line pair `½ ± b + iγ` at the same
ordinate.  Write `Ξ = (z − γ)((z − γ)² + b²) g` with `g = mixedTripleQuotient γ b`
(`XiC_eq_mixedTriple_mul`).

**Theorem** (`re_xiSliceHeatTransfer_four_neg_of_mixed_triple`).  At the ordinate the slice is
`S(γ, y) = y²(b² − y²)² G̃(y)`, `G̃(y) = g(γ − iy) g(γ + iy)` (`xiSliceProduct_eq_triple_mul`), and
`g(γ)` is real (`mixedTripleQuotient_self_im`).  With the Hermite representation at order four and
`∫ g₄(w) λw²(b² − λw²)² dw = 24√(2π) λ²(15λ − 2b²)` (`integral_hermiteGauss_four_mul_tripleSlice`):
if the cofactor deviation is below `24√(2π) λ²(2b² − 15λ) g(γ)²`, then `Re T₄(λ, 0, γ) < 0`, hence
`λ ≤ λ_WD` (`le_wdHeatThreshold_of_mixed_triple`).

The order-two coefficient of the heated triple, `b⁴ − 12b²λ + 45λ²`, is positive for every `λ`, so
the critical zero hides the pair at order two.  Order four exposes it for `λ < 2b²/15`.  Against the
de Bruijn–Newman persistence time `b²/6` of the triple (`lt_newmanConstant_of_mixed_triple`), the
ratio of the two per-configuration thresholds is `(2/15)/(1/6) = 4/5`, against `2/3` for an isolated
pair (`isolatedDeepestPair_threshold_bounds`).
-/

open Complex MeasureTheory Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

theorem hermiteGauss_four (x : ℝ) :
    hermiteGauss 4 x = (x ^ 4 - 6 * x ^ 2 + 3) * Real.exp (-(x ^ 2 / 2)) := by
  unfold hermiteGauss
  congr 1
  simp [hermite_succ]
  ring

/-- `∫ g₄(w) λw²(b² − λw²)² dw = 24√(2π) λ²(15λ − 2b²)`. -/
theorem integral_hermiteGauss_four_mul_tripleSlice (b lam : ℝ) :
    ∫ w : ℝ, hermiteGauss 4 w * (lam * w ^ 2 * (b ^ 2 - lam * w ^ 2) ^ 2)
      = Real.sqrt (2 * Real.pi) * (24 * lam ^ 2 * (15 * lam - 2 * b ^ 2)) := by
  set c : ℕ → ℝ := fun m => if m = 1 then 3 * b ^ 4 * lam
    else if m = 2 then -6 * b ^ 4 * lam - 6 * b ^ 2 * lam ^ 2
    else if m = 3 then b ^ 4 * lam + 12 * b ^ 2 * lam ^ 2 + 3 * lam ^ 3
    else if m = 4 then -2 * b ^ 2 * lam ^ 2 - 6 * lam ^ 3
    else if m = 5 then lam ^ 3 else 0 with hc
  have e : ∀ w : ℝ, hermiteGauss 4 w * (lam * w ^ 2 * (b ^ 2 - lam * w ^ 2) ^ 2)
      = ∑ m ∈ Finset.range 6, c m * (Real.exp (-(w ^ 2 / 2)) * w ^ (2 * m)) := by
    intro w; rw [hermiteGauss_four]; simp [Finset.sum_range_succ, hc]; ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun m _ => (integrable_exp_neg_sq_half_mul_pow (2 * m)).const_mul _)]
  simp_rw [integral_const_mul, integral_exp_neg_sq_half_mul_pow_even]
  simp [Finset.sum_range_succ, hc, Nat.factorial]
  ring

theorem integrable_hermiteGauss_four_mul_tripleSlice (b lam : ℝ) :
    Integrable (fun w : ℝ => hermiteGauss 4 w * (lam * w ^ 2 * (b ^ 2 - lam * w ^ 2) ^ 2)) := by
  have hsum : Integrable (fun w : ℝ =>
      ∑ m ∈ Finset.range 6, (if m = 1 then 3 * b ^ 4 * lam
        else if m = 2 then -6 * b ^ 4 * lam - 6 * b ^ 2 * lam ^ 2
        else if m = 3 then b ^ 4 * lam + 12 * b ^ 2 * lam ^ 2 + 3 * lam ^ 3
        else if m = 4 then -2 * b ^ 2 * lam ^ 2 - 6 * lam ^ 3
        else if m = 5 then lam ^ 3 else 0) * (Real.exp (-(w ^ 2 / 2)) * w ^ (2 * m))) :=
    integrable_finsetSum _ fun m _ => (integrable_exp_neg_sq_half_mul_pow (2 * m)).const_mul _
  refine hsum.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [hermiteGauss_four, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- At a critical ordinate carrying an off-line pair the slice factors as
`S(γ, y) = y²(b² − y²)² · G̃(y)`, `G̃(y) = g(γ − iy) g(γ + iy)`, `g = mixedTripleQuotient γ b`. -/
theorem xiSliceProduct_eq_triple_mul {γ b : ℝ} (hb : 0 < b) (hz : XiC ((γ : ℂ) - b * I) = 0)
    (hγ : XiC (γ : ℂ) = 0) (y : ℂ) :
    xiSliceProduct γ y = y ^ 2 * ((b : ℂ) ^ 2 - y ^ 2) ^ 2 *
      (mixedTripleQuotient γ b ((γ : ℂ) - y * I) * mixedTripleQuotient γ b ((γ : ℂ) + y * I)) := by
  have h1 : xi (1 / 2 + y + γ * I) = XiC ((γ : ℂ) - y * I) := by
    unfold XiC; congr 1; ring_nf; rw [I_sq]; ring
  have h2 : xi (1 / 2 - y + γ * I) = XiC ((γ : ℂ) + y * I) := by
    unfold XiC; congr 1; ring_nf; rw [I_sq]; ring
  have t1 : ((γ : ℂ) - y * I - γ) * (((γ : ℂ) - y * I - γ) ^ 2 + (b : ℂ) ^ 2)
      = -(y * I) * ((b : ℂ) ^ 2 - y ^ 2) := by linear_combination (-y ^ 3 * I) * I_sq
  have t2 : ((γ : ℂ) + y * I - γ) * (((γ : ℂ) + y * I - γ) ^ 2 + (b : ℂ) ^ 2)
      = (y * I) * ((b : ℂ) ^ 2 - y ^ 2) := by linear_combination (y ^ 3 * I) * I_sq
  unfold xiSliceProduct
  rw [h1, h2, XiC_eq_mixedTriple_mul hb hz hγ, XiC_eq_mixedTriple_mul hb hz hγ,
    eval_mixedTriplePoly, eval_mixedTriplePoly, t1, t2]
  linear_combination (-y ^ 2 * ((b : ℂ) ^ 2 - y ^ 2) ^ 2 *
    mixedTripleQuotient γ b ((γ : ℂ) - y * I) * mixedTripleQuotient γ b ((γ : ℂ) + y * I)) * I_sq

/-- The pair quotient is real on the real axis. -/
theorem xiPairQuotient_ofReal_im {γ b : ℝ} (hb : 0 < b) (hz : XiC ((γ : ℂ) - b * I) = 0)
    (x : ℝ) : (xiPairQuotient γ b x).im = 0 := by
  have h := XiC_eq_quadratic_mul_xiPairQuotient hb hz x
  have him : (XiC (x : ℂ)).im = 0 := by
    have h' := XiC_conj ((x : ℂ))
    rw [Complex.conj_ofReal] at h'
    exact Complex.conj_eq_iff_im.mp h'.symm
  have hq : ((x : ℂ) - γ) ^ 2 + (b : ℂ) ^ 2 = (((x - γ) ^ 2 + b ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hqpos : (0 : ℝ) < (x - γ) ^ 2 + b ^ 2 := by positivity
  rw [hq] at h
  have h2 := congrArg Complex.im h
  rw [Complex.im_ofReal_mul, him] at h2
  exact ((mul_eq_zero.mp h2.symm).resolve_left hqpos.ne')

/-- The mixed-triple cofactor is real at the critical ordinate. -/
theorem mixedTripleQuotient_self_im {γ b : ℝ} (hb : 0 < b) (hz : XiC ((γ : ℂ) - b * I) = 0) :
    (mixedTripleQuotient γ b γ).im = 0 := by
  rw [mixedTripleQuotient, dslope_same]
  set f := xiPairQuotient γ b with hf
  have hd : HasDerivAt f (deriv f γ) (γ : ℂ) :=
    ((differentiable_xiPairQuotient γ b) (γ : ℂ)).hasDerivAt
  have h2 : HasDerivAt (fun y : ℝ => (f y).im) (deriv f γ).im γ := by
    have := (hd.const_mul (-I)).real_of_complex
    simpa using this
  have h3 : HasDerivAt (fun y : ℝ => (f y).im) 0 γ := by
    have : (fun y : ℝ => (f y).im) = fun _ => (0 : ℝ) := by
      funext y; exact xiPairQuotient_ofReal_im hb hz y
    rw [this]; exact hasDerivAt_const _ _
  exact h2.unique h3

/-- **Order-four heated coefficient of an isolated mixed triple.**  Let `γ` be a critical ordinate
(`Ξ(γ) = 0`) carrying an off-line pair `γ ∓ ib`, `λ > 0`, `g = mixedTripleQuotient γ b` and
`G̃(y) = g(γ − iy) g(γ + iy)`.  If the cofactor deviation, weighted by `g₄(w) λw²(b² − λw²)²`, is
below `24√(2π) λ²(2b² − 15λ) |g(γ)|²`, then `Re T₄(λ, 0, γ) < 0`. -/
theorem re_xiSliceHeatTransfer_four_neg_of_mixed_triple {γ b lam : ℝ} (hb : 0 < b)
    (hlam : 0 < lam) (hz : XiC ((γ : ℂ) - b * I) = 0) (hγ : XiC (γ : ℂ) = 0)
    (hvar : ‖∫ w : ℝ, (hermiteGauss 4 w : ℂ) *
        (((Real.sqrt lam * w : ℝ) : ℂ) ^ 2 * ((b : ℂ) ^ 2 - ((Real.sqrt lam * w : ℝ) : ℂ) ^ 2) ^ 2 *
          (mixedTripleQuotient γ b ((γ : ℂ) - ((Real.sqrt lam * w : ℝ) : ℂ) * I) *
            mixedTripleQuotient γ b ((γ : ℂ) + ((Real.sqrt lam * w : ℝ) : ℂ) * I)
              - mixedTripleQuotient γ b γ ^ 2))‖
      < Real.sqrt (2 * Real.pi) * (24 * lam ^ 2 * (2 * b ^ 2 - 15 * lam))
          * ‖mixedTripleQuotient γ b γ‖ ^ 2) :
    (xiSliceHeatTransfer lam 0 γ 4).re < 0 := by
  set sl := Real.sqrt lam with hsl
  have hsl2 : sl ^ 2 = lam := Real.sq_sqrt hlam.le
  set g := mixedTripleQuotient γ b with hgdef
  set r : ℝ := (g γ).re with hr
  have hgr : g γ = (r : ℂ) :=
    Complex.ext (by simp [hr]) (by simpa [hgdef] using mixedTripleQuotient_self_im hb hz)
  set E : ℂ := ∫ w : ℝ, (hermiteGauss 4 w : ℂ) *
      (((sl * w : ℝ) : ℂ) ^ 2 * ((b : ℂ) ^ 2 - ((sl * w : ℝ) : ℂ) ^ 2) ^ 2 *
        (g ((γ : ℂ) - ((sl * w : ℝ) : ℂ) * I) * g ((γ : ℂ) + ((sl * w : ℝ) : ℂ) * I) - g γ ^ 2))
    with hE
  set M : ℝ := ∫ w : ℝ, hermiteGauss 4 w * (lam * w ^ 2 * (b ^ 2 - lam * w ^ 2) ^ 2) with hM
  have hMval : M = Real.sqrt (2 * Real.pi) * (24 * lam ^ 2 * (15 * lam - 2 * b ^ 2)) :=
    integral_hermiteGauss_four_mul_tripleSlice b lam
  have hmainInt : Integrable (fun w : ℝ => (hermiteGauss 4 w : ℂ) *
      (((sl * w : ℝ) : ℂ) ^ 2 * ((b : ℂ) ^ 2 - ((sl * w : ℝ) : ℂ) ^ 2) ^ 2 * g γ ^ 2)) := by
    refine ((integrable_hermiteGauss_four_mul_tripleSlice b lam).ofReal.mul_const
      (g γ ^ 2)).congr (Filter.Eventually.of_forall fun w => ?_)
    show ((hermiteGauss 4 w * (lam * w ^ 2 * (b ^ 2 - lam * w ^ 2) ^ 2) : ℝ) : ℂ) * g γ ^ 2 = _
    rw [← hsl2]
    push_cast
    ring
  have hmain : ∫ w : ℝ, (hermiteGauss 4 w : ℂ) *
      (((sl * w : ℝ) : ℂ) ^ 2 * ((b : ℂ) ^ 2 - ((sl * w : ℝ) : ℂ) ^ 2) ^ 2 * g γ ^ 2)
      = (M : ℂ) * g γ ^ 2 := by
    rw [hM, ← integral_complex_ofReal, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    show _ = ((hermiteGauss 4 w * (lam * w ^ 2 * (b ^ 2 - lam * w ^ 2) ^ 2) : ℝ) : ℂ) * g γ ^ 2
    rw [← hsl2]
    push_cast
    ring
  have hH := integral_hermiteGauss_mul_xiSliceProduct hlam.le γ 4
  have hSint := integrable_hermiteGauss_mul_xiSliceProduct hlam.le γ 4
  have hsplit : ∫ w : ℝ, (hermiteGauss 4 w : ℂ) * xiSliceProduct γ ((sl * w : ℝ) : ℂ)
      = (M : ℂ) * g γ ^ 2 + E := by
    rw [← hmain, hE, ← integral_add hmainInt]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only [xiSliceProduct_eq_triple_mul hb hz hγ]
      ring
    · refine (hSint.sub hmainInt).congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [Pi.sub_apply, xiSliceProduct_eq_triple_mul hb hz hγ]
      ring
  rw [hsplit] at hH
  set T := xiSliceHeatTransfer lam 0 γ 4 with hT
  have hc : (0 : ℝ) < Real.sqrt (2 * Real.pi) * sl ^ 4 * (Nat.factorial 4 : ℝ) := by
    have : sl ^ 4 = lam ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hsl2]
    rw [this]; positivity
  have hre := congrArg Complex.re hH
  rw [Complex.re_ofReal_mul, Complex.add_re, hgr] at hre
  have hMr : ((M : ℂ) * (r : ℂ) ^ 2).re = M * r ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hMr] at hre
  have hEle : E.re ≤ ‖E‖ := Complex.re_le_norm E
  have hgn : ‖g γ‖ ^ 2 = r ^ 2 := by rw [hgr, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hgn] at hvar
  have hvar' : ‖E‖ < Real.sqrt (2 * Real.pi) * (24 * lam ^ 2 * (2 * b ^ 2 - 15 * lam)) * r ^ 2 := by
    simpa [hE, hsl] using hvar
  have hsum : M * r ^ 2 + E.re < 0 := by
    rw [hMval]; nlinarith
  by_contra hTnn
  push Not at hTnn
  have : 0 ≤ Real.sqrt (2 * Real.pi) * sl ^ 4 * (Nat.factorial 4 : ℝ) * T.re :=
    mul_nonneg hc.le hTnn
  linarith

/-- **WD threshold of an isolated mixed triple.**  Under the hypotheses of
`re_xiSliceHeatTransfer_four_neg_of_mixed_triple`, `λ ≤ λ_WD`. -/
theorem le_wdHeatThreshold_of_mixed_triple {γ b lam : ℝ} (hb : 0 < b) (hlam : 0 < lam)
    (hz : XiC ((γ : ℂ) - b * I) = 0) (hγ : XiC (γ : ℂ) = 0)
    (hvar : ‖∫ w : ℝ, (hermiteGauss 4 w : ℂ) *
        (((Real.sqrt lam * w : ℝ) : ℂ) ^ 2 * ((b : ℂ) ^ 2 - ((Real.sqrt lam * w : ℝ) : ℂ) ^ 2) ^ 2 *
          (mixedTripleQuotient γ b ((γ : ℂ) - ((Real.sqrt lam * w : ℝ) : ℂ) * I) *
            mixedTripleQuotient γ b ((γ : ℂ) + ((Real.sqrt lam * w : ℝ) : ℂ) * I)
              - mixedTripleQuotient γ b γ ^ 2))‖
      < Real.sqrt (2 * Real.pi) * (24 * lam ^ 2 * (2 * b ^ 2 - 15 * lam))
          * ‖mixedTripleQuotient γ b γ‖ ^ 2) :
    lam ≤ wdHeatThreshold := by
  by_contra h
  push Not at h
  have hadm := mem_wdHeatAdmissible_of_lt h γ 4
  have hneg := re_xiSliceHeatTransfer_four_neg_of_mixed_triple hb hlam hz hγ hvar
  have := (Complex.le_def.mp hadm).1
  simp only [Complex.zero_re] at this
  linarith

end

end RHTower.DeBruijn
