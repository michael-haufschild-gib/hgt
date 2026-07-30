import GaloisForLFunctions.Hurwitz.N2HZeta
import GaloisForLFunctions.Hurwitz.LadderDeformation
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Analytic continuation of Hurwitz zeta in the complex shift

For arbitrary exponent `s`, the raw series `∑ₘ (m+a)⁻ˢ` need not converge.  This file starts a
concrete, hypothesis-free continuation by subtracting a finite Taylor packet at the reference shift
`a = 1`.  If `K` satisfies `0 < Re s + K`, the remainder is summable; the removed terms are restored
by meromorphically continued Riemann-zeta values in the next layer.

The construction is designed to preserve the exact local branch term `(a+n)⁻ˢ`, so it can replace
the convergence-half-plane object in the joint monodromy proof.
-/

open Complex Filter Asymptotics Topology HurwitzLadder
open HurwitzN2HZeta

namespace HurwitzZetaContinuation

/-- The `r`th Taylor term at the reference shift `a = 1` for the `m`th Hurwitz summand. -/
noncomputable def taylorTerm (s a : ℂ) (r m : ℕ) : ℂ :=
  Ring.choose (-s) r * (a - 1) ^ r * ((m + 1 : ℕ) : ℂ) ^ (-(s + r))

/-- Taylor packet through degree `K` for one Hurwitz summand. -/
noncomputable def taylorPoly (K : ℕ) (s a : ℂ) (m : ℕ) : ℂ :=
  ∑ r ∈ Finset.range (K + 1), taylorTerm s a r m

/-- Taylor-subtracted `m`th Hurwitz summand. -/
noncomputable def remainder (K : ℕ) (s a : ℂ) (m : ℕ) : ℂ :=
  ((m : ℂ) + a) ^ (-s) - taylorPoly K s a m

/-- The binomial formal series has the expected scalar partial sum. -/
lemma binomial_partialSum (K : ℕ) (s y : ℂ) :
    (binomialSeries ℂ (-s)).partialSum (K + 1) y =
      ∑ r ∈ Finset.range (K + 1), Ring.choose (-s) r * y ^ r := by
  rw [FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [binomialSeries_apply]
  simp

/-- On the upper half-plane a Hurwitz summand factors through its Taylor coordinate at `a = 1`. -/
lemma term_factor {s a : ℂ} (ha : 0 < a.im) (m : ℕ) :
    ((m : ℂ) + a) ^ (-s) =
      (((m + 1 : ℕ) : ℂ) ^ (-s)) *
        (1 + (a - 1) / ((m + 1 : ℕ) : ℂ)) ^ (-s) := by
  have h := term_split (c := -s) (x := a - 1) (by simpa using ha)
    (m := m + 1) (n := 0) (by omega)
  convert! h using 1
  · congr 1
    push_cast
    ring
  · push_cast
    simp

/-- A cut-free factorization criterion that does not require `a` to lie in the upper half-plane.
It applies whenever the Taylor coordinate stays in the unit disk. -/
lemma term_factor_of_norm_lt_one {s a : ℂ} (m : ℕ)
    (hy : ‖(a - 1) / ((m + 1 : ℕ) : ℂ)‖ < 1) :
    ((m : ℂ) + a) ^ (-s) =
      (((m + 1 : ℕ) : ℂ) ^ (-s)) *
        (1 + (a - 1) / ((m + 1 : ℕ) : ℂ)) ^ (-s) := by
  let r : ℝ := (m + 1 : ℕ)
  let y : ℂ := (a - 1) / ((m + 1 : ℕ) : ℂ)
  have hr : 0 < r := by dsimp [r]; positivity
  have hy' : ‖y‖ < 1 := by simpa [y] using hy
  have hy0 : 1 + y ≠ 0 := by
    intro h
    have : y = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hy'
    linarith
  have hbase : (m : ℂ) + a = (r : ℂ) * (1 + y) := by
    dsimp only [r, y]
    have hm : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (by omega : m + 1 ≠ 0)
    push_cast
    field_simp
    ring
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hlogr : Complex.log (r : ℂ) = (Real.log r : ℂ) := by
    simpa using (Complex.log_ofReal_mul hr (x := (1 : ℂ)) one_ne_zero)
  rw [hbase]
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr0 hy0),
    Complex.log_ofReal_mul hr hy0, add_mul, Complex.exp_add]
  change Complex.exp ((Real.log r : ℂ) * -s) * Complex.exp (Complex.log (1 + y) * -s) =
    (r : ℂ) ^ (-s) * (1 + y) ^ (-s)
  rw [Complex.cpow_def_of_ne_zero hr0, Complex.cpow_def_of_ne_zero hy0, hlogr]

/-- The subtracted Taylor packet is the corresponding binomial partial sum after factorization. -/
lemma taylor_factor (K : ℕ) (s a : ℂ) (m : ℕ) :
    taylorPoly K s a m =
      (((m + 1 : ℕ) : ℂ) ^ (-s)) *
        (binomialSeries ℂ (-s)).partialSum (K + 1)
          ((a - 1) / ((m + 1 : ℕ) : ℂ)) := by
  rw [taylorPoly, binomial_partialSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [taylorTerm]
  have hm : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (by omega : m + 1 ≠ 0)
  rw [div_pow]
  rw [show -(s + (r : ℂ)) = -s + (-(r : ℂ)) by ring]
  rw [Complex.cpow_add _ _ hm]
  have hnr : (((m + 1 : ℕ) : ℂ)) ^ (-(r : ℂ)) =
      ((((m + 1 : ℕ) : ℂ)) ^ r)⁻¹ := by
    rw [Complex.cpow_neg, Complex.cpow_natCast]
  rw [hnr]
  field_simp

/-- Exact norm identity converting the analytic Taylor remainder into a summable Hurwitz
majorant. -/
lemma majorant_eq (K : ℕ) (s a : ℂ) (m : ℕ) :
    ‖(((m + 1 : ℕ) : ℂ) ^ (-s))‖ *
        ‖(a - 1) / ((m + 1 : ℕ) : ℂ)‖ ^ (K + 1) =
      ‖a - 1‖ ^ (K + 1) *
        ‖(((m + 1 : ℕ) : ℂ) ^ (-(s + (K + 1 : ℕ))))‖ := by
  have hmR : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  rw [norm_div, Complex.norm_natCast]
  have hright :
      ‖(((m + 1 : ℕ) : ℂ) ^ (-(s + (K + 1 : ℕ))))‖ =
        (m + 1 : ℝ) ^ (-(s.re + (K + 1 : ℝ))) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re, Complex.add_re,
      Complex.natCast_re]
    push_cast
    rfl
  rw [hright, div_pow]
  push_cast
  have hpow : ((m + 1 : ℝ) : ℝ) ^ (K + 1) = (m + 1 : ℝ) ^ ((K + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
  rw [hpow, div_eq_mul_inv]
  have hb : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [← Real.rpow_neg hb.le]
  calc
    ((m : ℝ) + 1) ^ (-s.re) *
          (‖a - 1‖ ^ (K + 1) * ((m : ℝ) + 1) ^ (-((K + 1 : ℕ) : ℝ))) =
        ‖a - 1‖ ^ (K + 1) *
          (((m : ℝ) + 1) ^ (-s.re) *
            ((m : ℝ) + 1) ^ (-((K + 1 : ℕ) : ℝ))) := by ring
    _ = ‖a - 1‖ ^ (K + 1) *
          ((m : ℝ) + 1) ^ ((-s.re) + (-((K + 1 : ℕ) : ℝ))) := by
            rw [Real.rpow_add hb]
    _ = ‖a - 1‖ ^ (K + 1) *
          ((m : ℝ) + 1) ^ (-(s.re + ((K + 1 : ℕ) : ℝ))) := by
            have he : (-s.re) + (-((K + 1 : ℕ) : ℝ)) =
                -(s.re + ((K + 1 : ℕ) : ℝ)) := by ring
            rw [he]
    _ = ‖a - 1‖ ^ (K + 1) *
          ((m : ℝ) + 1) ^ (-(s.re + (((K : ℕ) : ℝ) + 1))) := by
            push_cast
            rfl

/-- A uniform Taylor-remainder bound on the half-unit disk. -/
lemma exists_binomial_remainder_bound (K : ℕ) (s : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℂ, ‖y‖ < 1 / 2 →
      ‖(1 + y) ^ (-s) - (binomialSeries ℂ (-s)).partialSum (K + 1) y‖
        ≤ C * ‖y‖ ^ (K + 1) := by
  let r' : NNReal := ⟨1 / 2, by positivity⟩
  have hr' : (r' : ENNReal) < 1 := by
    exact_mod_cast (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨q, hq, D, hD, hbound⟩ :=
    (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := -s)).uniform_geometric_approx' hr'
  refine ⟨D * (q * 2) ^ (K + 1),
    mul_nonneg hD.le (pow_nonneg (mul_nonneg hq.1.le (by norm_num)) _), ?_⟩
  intro y hy
  have hymem : y ∈ Metric.ball (0 : ℂ) (r' : ℝ) := by
    rw [Metric.mem_ball, dist_zero_right]
    simpa [r'] using! hy
  have h := hbound y hymem (K + 1)
  simp only [zero_add] at h
  calc
    ‖(1 + y) ^ (-s) - (binomialSeries ℂ (-s)).partialSum (K + 1) y‖
        ≤ D * (q * (‖y‖ / (r' : ℝ))) ^ (K + 1) := h
    _ = D * (q * 2) ^ (K + 1) * ‖y‖ ^ (K + 1) := by
      have hrcoe : (r' : ℝ) = 1 / 2 := rfl
      rw [hrcoe]
      norm_num
      ring

/-- **Finite Taylor subtraction gives a convergent Hurwitz remainder.**  Degree `K` suffices as
soon as `Re s + K > 0`; the summand is then `O(m^{-Re s-K-1})`. -/
theorem summable_remainder {K : ℕ} {s a : ℂ} (ha : 0 < a.im)
    (hK : 0 < s.re + K) : Summable (remainder K s a) := by
  let y : ℕ → ℂ := fun m => (a - 1) / ((m + 1 : ℕ) : ℂ)
  let f : ℂ → ℂ := fun z => (1 + z) ^ (-s) -
    (binomialSeries ℂ (-s)).partialSum (K + 1) z
  have hO : f =O[𝓝 0] fun z : ℂ => ‖z‖ ^ (K + 1) := by
    simpa [f] using
      (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := -s)).isBigO_sub_partialSum_pow (K + 1)
  have hy : Tendsto y atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => a - 1) atTop (𝓝 (a - 1)) := tendsto_const_nhds
    have h := hc.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
    convert! h using 1 <;> simp [y, div_eq_mul_inv]
  obtain ⟨C, hC⟩ := (hO.comp_tendsto hy).bound
  have hsK : 1 < (s + (K + 1 : ℕ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    norm_num at hK ⊢
    linarith
  have hbase : Summable (fun m : ℕ =>
      (((m + 1 : ℕ) : ℂ) ^ (-(s + (K + 1 : ℕ))))) := by
    simpa [add_comm] using HurwitzZetaShift.summable_hurwitzSeries hsK 1
  have hg : Summable (fun m : ℕ =>
      C * ‖a - 1‖ ^ (K + 1) *
        ‖(((m + 1 : ℕ) : ℂ) ^ (-(s + (K + 1 : ℕ))))‖) := by
    exact ((summable_norm_iff.mpr hbase).mul_left (C * ‖a - 1‖ ^ (K + 1)))
  apply Summable.of_norm_bounded_eventually hg
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hC] with m hm
  have hrem : remainder K s a m =
      (((m + 1 : ℕ) : ℂ) ^ (-s)) * f (y m) := by
    rw [remainder, term_factor ha, taylor_factor]
    simp only [f, y]
    ring
  rw [hrem, norm_mul]
  calc
    ‖(((m + 1 : ℕ) : ℂ) ^ (-s))‖ * ‖f (y m)‖
        ≤ ‖(((m + 1 : ℕ) : ℂ) ^ (-s))‖ *
            (C * ‖y m‖ ^ (K + 1)) :=
          mul_le_mul_of_nonneg_left (by simpa using hm) (norm_nonneg _)
    _ = C * (‖(((m + 1 : ℕ) : ℂ) ^ (-s))‖ *
            ‖(a - 1) / ((m + 1 : ℕ) : ℂ)‖ ^ (K + 1)) := by
          simp only [y]
          ring
    _ = C * (‖a - 1‖ ^ (K + 1) *
            ‖(((m + 1 : ℕ) : ℂ) ^ (-(s + (K + 1 : ℕ))))‖) := by
          rw [majorant_eq]
    _ = C * ‖a - 1‖ ^ (K + 1) *
            ‖(((m + 1 : ℕ) : ℂ) ^ (-(s + (K + 1 : ℕ))))‖ := by ring

/-- The `r`th Taylor term restored with the meromorphically continued zeta value at `a = 1`. -/
noncomputable def restoreTerm (s a : ℂ) (r : ℕ) : ℂ :=
  Ring.choose (-s) r * (a - 1) ^ r * riemannZeta (s + r)

/-- Finite restoration packet through degree `K`. -/
noncomputable def restoration (K : ℕ) (s a : ℂ) : ℂ :=
  ∑ r ∈ Finset.range (K + 1), restoreTerm s a r

/-- The degree-`K` Taylor-regularized Hurwitz value. -/
noncomputable def continuedAt (K : ℕ) (s a : ℂ) : ℂ :=
  ∑' m : ℕ, remainder K s a m + restoration K s a

lemma taylorPoly_succ (K : ℕ) (s a : ℂ) (m : ℕ) :
    taylorPoly (K + 1) s a m = taylorPoly K s a m + taylorTerm s a (K + 1) m := by
  rw [taylorPoly, taylorPoly]
  convert! Finset.sum_range_succ (fun r => taylorTerm s a r m) (K + 1) using 1

lemma remainder_succ (K : ℕ) (s a : ℂ) (m : ℕ) :
    remainder (K + 1) s a m = remainder K s a m - taylorTerm s a (K + 1) m := by
  rw [remainder, remainder, taylorPoly_succ]
  ring

lemma restoration_succ (K : ℕ) (s a : ℂ) :
    restoration (K + 1) s a = restoration K s a + restoreTerm s a (K + 1) := by
  rw [restoration, restoration]
  convert! Finset.sum_range_succ (fun r => restoreTerm s a r) (K + 1) using 1

lemma base_tsum_eq_riemannZeta {u : ℂ} (hu : 1 < u.re) :
    (∑' m : ℕ, (((m + 1 : ℕ) : ℂ) ^ (-u))) = riemannZeta u := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hu]
  symm
  apply tsum_congr
  intro m
  rw [Complex.cpow_neg, one_div]
  push_cast
  rfl

lemma summable_taylorTerm {s a : ℂ} {r : ℕ} (hr : 1 < (s + r).re) :
    Summable (taylorTerm s a r) := by
  have hb : Summable (fun m : ℕ => (((m + 1 : ℕ) : ℂ) ^ (-(s + r)))) := by
    simpa [add_comm] using HurwitzZetaShift.summable_hurwitzSeries hr 1
  convert! hb.mul_left (Ring.choose (-s) r * (a - 1) ^ r) using 1

lemma tsum_taylorTerm {s a : ℂ} {r : ℕ} (hr : 1 < (s + r).re) :
    (∑' m : ℕ, taylorTerm s a r m) = restoreTerm s a r := by
  have hb : Summable (fun m : ℕ => (((m + 1 : ℕ) : ℂ) ^ (-(s + r)))) := by
    simpa [add_comm] using HurwitzZetaShift.summable_hurwitzSeries hr 1
  let C : ℂ := Ring.choose (-s) r * (a - 1) ^ r
  have heq : taylorTerm s a r =
      fun m : ℕ => C * (((m + 1 : ℕ) : ℂ) ^ (-(s + r))) := by
    funext m
    rw [taylorTerm]
  rw [heq, hb.tsum_mul_left, restoreTerm]
  rw [base_tsum_eq_riemannZeta hr]

/-- Once the Taylor degree is sufficient for convergence, increasing it does not change the
regularized Hurwitz value. -/
theorem continuedAt_succ {K : ℕ} {s a : ℂ} (ha : 0 < a.im)
    (hK : 0 < s.re + K) : continuedAt (K + 1) s a = continuedAt K s a := by
  have hK' : 0 < s.re + (K + 1 : ℕ) := by norm_num at hK ⊢; linarith
  have hrem := summable_remainder ha hK
  have hrem' := summable_remainder ha hK'
  have hr : 1 < (s + (K + 1 : ℕ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    norm_num at hK ⊢
    linarith
  have ht := summable_taylorTerm (s := s) (a := a) hr
  rw [continuedAt, continuedAt, restoration_succ]
  have htsub := hrem.tsum_sub ht
  have heqRem : (fun b : ℕ => remainder K s a b - taylorTerm s a (K + 1) b) =
      remainder (K + 1) s a := by
    funext b
    exact (remainder_succ K s a b).symm
  rw [heqRem] at htsub
  rw [htsub, tsum_taylorTerm hr]
  ring

/-- Every Taylor-subtracted summand is holomorphic on the upper half-plane. -/
lemma remainder_differentiableOn (K : ℕ) (s : ℂ) (m : ℕ) :
    DifferentiableOn ℂ (fun a => remainder K s a m) UHP := by
  intro a ha
  unfold remainder taylorPoly
  apply DifferentiableWithinAt.sub
  · exact (HurwitzLadder.term_differentiableAt ha m (-s)).differentiableWithinAt
  · apply DifferentiableWithinAt.fun_sum
    intro r hr
    unfold taylorTerm
    fun_prop

/-- The finite restoration packet is entire in the shift. -/
lemma restoration_differentiable (K : ℕ) (s : ℂ) :
    Differentiable ℂ (restoration K s) := by
  unfold restoration
  apply Differentiable.fun_sum
  intro r hr
  unfold restoreTerm
  fun_prop

/-- Differentiating the `(r+1)`st binomial coefficient produces the shifted `r`th coefficient. -/
lemma choose_deriv_coeff (s : ℂ) (r : ℕ) :
    ((r + 1 : ℕ) : ℂ) * Ring.choose (-s) (r + 1) =
      -s * Ring.choose (-(s + 1)) r := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul]
  rw [descPochhammer_succ_left, Polynomial.smeval_mul, Polynomial.smeval_X,
    Polynomial.smeval_comp]
  simp
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  rw [show -s - 1 = -1 + -s by ring]

/-- Derivative of one positive-degree Taylor term. -/
lemma taylorTerm_succ_hasDerivAt (s a : ℂ) (r m : ℕ) :
    HasDerivAt (fun w => taylorTerm s w (r + 1) m)
      (-s * taylorTerm (s + 1) a r m) a := by
  have hpow : HasDerivAt (fun w : ℂ => (w - 1) ^ (r + 1))
      (((r + 1 : ℕ) : ℂ) * (a - 1) ^ r) a := by
    simpa [Nat.add_sub_cancel] using! ((hasDerivAt_id a).sub_const 1).pow (r + 1)
  have h := hpow.const_mul
    (Ring.choose (-s) (r + 1) * (((m + 1 : ℕ) : ℂ) ^ (-(s + (r + 1 : ℕ)))))
  convert! h using 1
  · funext w
    rw [taylorTerm]
    ring
  · rw [taylorTerm]
    have hm : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (by omega : m + 1 ≠ 0)
    rw [show -(s + (r + 1 : ℕ)) = -(s + 1 + r) by push_cast; ring]
    have hc := choose_deriv_coeff s r
    linear_combination -(a - 1) ^ r *
      (((m + 1 : ℕ) : ℂ) ^ (-(s + 1 + r))) * hc

/-- Derivative of one unregularized Hurwitz summand. -/
lemma rawTerm_hasDerivAt {s a : ℂ} (ha : a ∈ UHP) (m : ℕ) :
    HasDerivAt (fun w : ℂ => ((m : ℂ) + w) ^ (-s))
      (-s * ((m : ℂ) + a) ^ (-(s + 1))) a := by
  have hb : ((m : ℂ) + a) ∈ Complex.slitPlane := natCast_add_mem_slitPlane ha m
  have h := (Complex.hasStrictDerivAt_cpow_const (c := -s) hb).hasDerivAt.comp a
    ((hasDerivAt_const a (m : ℂ)).add (hasDerivAt_id a))
  convert! h using 1 <;> ring

/-- Derivative of a finite Taylor packet. -/
lemma taylorPoly_succ_hasDerivAt (K : ℕ) (s a : ℂ) (m : ℕ) :
    HasDerivAt (fun w => taylorPoly (K + 1) s w m)
      (-s * taylorPoly K (s + 1) a m) a := by
  rw [show K + 1 = K + 1 by rfl]
  have hzero : HasDerivAt (fun _ : ℂ => taylorTerm s a 0 m) 0 a := hasDerivAt_const _ _
  have hsum : HasDerivAt
      (fun w : ℂ => ∑ r ∈ Finset.range (K + 1), taylorTerm s w (r + 1) m)
      (∑ r ∈ Finset.range (K + 1), -s * taylorTerm (s + 1) a r m) a := by
    apply HasDerivAt.fun_sum
    intro r hr
    exact taylorTerm_succ_hasDerivAt s a r m
  have h := hzero.add hsum
  convert! h using 1
  · funext w
    rw [taylorPoly]
    rw [Finset.sum_range_succ']
    simp [show taylorTerm s w 0 m = taylorTerm s a 0 m by simp [taylorTerm]]
    ring
  · rw [taylorPoly, Finset.mul_sum]
    simp

/-- Derivative of a Taylor-regularized summand. -/
lemma remainder_succ_hasDerivAt {K : ℕ} {s a : ℂ} (ha : a ∈ UHP) (m : ℕ) :
    HasDerivAt (fun w => remainder (K + 1) s w m)
      (-s * remainder K (s + 1) a m) a := by
  have hraw := rawTerm_hasDerivAt (s := s) ha m
  have ht := taylorPoly_succ_hasDerivAt K s a m
  convert! hraw.sub ht using 1
  rw [remainder]
  ring

/-- Derivative of a finite restoration packet. -/
lemma restoration_succ_hasDerivAt (K : ℕ) (s a : ℂ) :
    HasDerivAt (restoration (K + 1) s)
      (-s * restoration K (s + 1) a) a := by
  have hzero : HasDerivAt (fun _ : ℂ => restoreTerm s a 0) 0 a := hasDerivAt_const _ _
  have hsum : HasDerivAt
      (fun w : ℂ => ∑ r ∈ Finset.range (K + 1), restoreTerm s w (r + 1))
      (∑ r ∈ Finset.range (K + 1), -s * restoreTerm (s + 1) a r) a := by
    apply HasDerivAt.fun_sum
    intro r hr
    have hpow : HasDerivAt (fun w : ℂ => (w - 1) ^ (r + 1))
        (((r + 1 : ℕ) : ℂ) * (a - 1) ^ r) a := by
      simpa [Nat.add_sub_cancel] using! ((hasDerivAt_id a).sub_const 1).pow (r + 1)
    have h := hpow.const_mul (Ring.choose (-s) (r + 1) * riemannZeta (s + (r + 1)))
    convert! h using 1
    · funext w
      rw [restoreTerm]
      rw [show s + (r + 1 : ℕ) = s + 1 + r by push_cast; ring]
      ring
    · rw [restoreTerm]
      rw [show s + ((r : ℂ) + 1) = s + 1 + r by ring]
      have hc := choose_deriv_coeff s r
      linear_combination -(a - 1) ^ r * riemannZeta (s + 1 + r) * hc
  have h := hzero.add hsum
  convert! h using 1
  · funext w
    rw [restoration]
    rw [Finset.sum_range_succ']
    simp [show restoreTerm s w 0 = restoreTerm s a 0 by simp [restoreTerm]]
    ring
  · rw [restoration, Finset.mul_sum]
    simp

/-- **The Taylor-regularized Hurwitz function is holomorphic on the upper half-plane.** -/
theorem continuedAt_differentiableOn {K : ℕ} {s : ℂ} (hK : 0 < s.re + K) :
    DifferentiableOn ℂ (continuedAt K s) UHP := by
  intro a₀ ha₀
  have ha₀im : 0 < a₀.im := ha₀
  set ρ : ℝ := a₀.im / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  set B : ℝ := ‖a₀ - 1‖ + ρ with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * B)
  obtain ⟨C, hC0, hC⟩ := exists_binomial_remainder_bound K s
  have hballU : Metric.ball a₀ ρ ⊆ UHP := by
    intro w hw
    have hd : ‖w - a₀‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have himle : |(w - a₀).im| ≤ ‖w - a₀‖ := Complex.abs_im_le_norm _
    have him : (w - a₀).im = w.im - a₀.im := by simp
    rw [him] at himle
    have habs := abs_lt.mp (lt_of_le_of_lt himle hd)
    show 0 < w.im
    rw [hρ] at habs
    linarith
  have hballB : ∀ w ∈ Metric.ball a₀ ρ, ‖w - 1‖ < B := by
    intro w hw
    have hd : ‖w - a₀‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    calc
      ‖w - 1‖ = ‖(w - a₀) + (a₀ - 1)‖ := by congr 1; ring
      _ ≤ ‖w - a₀‖ + ‖a₀ - 1‖ := norm_add_le _ _
      _ < B := by rw [hB]; linarith
  have hsK : 1 < (s + (K + 1 : ℕ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    norm_num at hK ⊢
    linarith
  let u : ℕ → ℝ := fun m => C * B ^ (K + 1) *
    ‖(((m + M + 1 : ℕ) : ℂ) ^ (-(s + (K + 1 : ℕ))))‖
  have hbase : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℂ) ^ (-(s + (K + 1 : ℕ))))) := by
    simpa [add_comm] using HurwitzZetaShift.summable_hurwitzSeries hsK 1
  have hbaseShift : Summable (fun m : ℕ =>
      (((m + M + 1 : ℕ) : ℂ) ^ (-(s + (K + 1 : ℕ))))) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (summable_nat_add_iff M).mpr hbase
  have hu : Summable u := by
    exact (summable_norm_iff.mpr hbaseShift).mul_left (C * B ^ (K + 1))
  let tail : ℂ → ℂ := fun w => ∑' m : ℕ, remainder K s w (m + M)
  have htailDiff : DifferentiableOn ℂ tail (Metric.ball a₀ ρ) := by
    apply Complex.differentiableOn_tsum_of_summable_norm hu
    · intro m
      exact (remainder_differentiableOn K s (m + M)).mono hballU
    · exact Metric.isOpen_ball
    · intro m w hw
      have hwU : w ∈ UHP := hballU hw
      let y : ℂ := (w - 1) / ((m + M + 1 : ℕ) : ℂ)
      have hden : (2 * B : ℝ) < (m + M + 1 : ℕ) := by
        have hm0 : (0 : ℝ) ≤ m := by positivity
        norm_num at hM ⊢
        linarith
      have hy : ‖y‖ < 1 / 2 := by
        dsimp only [y]
        rw [norm_div, Complex.norm_natCast]
        have hwB := hballB w hw
        have hdenpos : (0 : ℝ) < (m + M + 1 : ℕ) := by positivity
        apply (div_lt_iff₀ hdenpos).mpr
        linarith
      have hbin := hC y hy
      have hrem : remainder K s w (m + M) =
          (((m + M + 1 : ℕ) : ℂ) ^ (-s)) *
            ((1 + y) ^ (-s) - (binomialSeries ℂ (-s)).partialSum (K + 1) y) := by
        rw [remainder, term_factor hwU, taylor_factor]
        dsimp only [y]
        ring
      rw [hrem, norm_mul]
      calc
        ‖(((m + M + 1 : ℕ) : ℂ) ^ (-s))‖ *
              ‖(1 + y) ^ (-s) - (binomialSeries ℂ (-s)).partialSum (K + 1) y‖
            ≤ ‖(((m + M + 1 : ℕ) : ℂ) ^ (-s))‖ *
                (C * ‖y‖ ^ (K + 1)) :=
              mul_le_mul_of_nonneg_left hbin (norm_nonneg _)
        _ = C * (‖(((m + M + 1 : ℕ) : ℂ) ^ (-s))‖ *
                ‖(w - 1) / ((m + M + 1 : ℕ) : ℂ)‖ ^ (K + 1)) := by
              simp only [y]
              ring
        _ = C * (‖w - 1‖ ^ (K + 1) *
                ‖(((m + M + 1 : ℕ) : ℂ) ^ (-(s + (K + 1 : ℕ))))‖) := by
              rw [majorant_eq]
        _ ≤ C * (B ^ (K + 1) *
                ‖(((m + M + 1 : ℕ) : ℂ) ^ (-(s + (K + 1 : ℕ))))‖) := by
              gcongr
              exact (hballB w hw).le
        _ = u m := by dsimp only [u]; ring
  let head : ℂ → ℂ := fun w =>
    ∑ m ∈ Finset.range M, remainder K s w m
  have hheadDiff : DifferentiableOn ℂ head (Metric.ball a₀ ρ) := by
    apply DifferentiableOn.fun_sum
    intro m hm
    exact (remainder_differentiableOn K s m).mono hballU
  let F : ℂ → ℂ := fun w => head w + tail w + restoration K s w
  have hFDiff : DifferentiableOn ℂ F (Metric.ball a₀ ρ) :=
    (hheadDiff.add htailDiff).add (restoration_differentiable K s).differentiableOn
  have heq : ∀ w ∈ Metric.ball a₀ ρ, continuedAt K s w = F w := by
    intro w hw
    have hsum := summable_remainder (hballU hw) hK
    unfold continuedAt
    dsimp only [F, head, tail]
    rw [← hsum.sum_add_tsum_nat_add M]
  have hFinal : DifferentiableOn ℂ (continuedAt K s) (Metric.ball a₀ ρ) :=
    hFDiff.congr (fun w hw => heq w hw)
  exact (hFinal.differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρpos))).differentiableWithinAt

/-- **Shift-derivative law for the regularized continuation.**  Raising the Taylor degree by one
and differentiating advances the Hurwitz exponent by one. -/
theorem continuedAt_succ_hasDerivAt {K : ℕ} {s a : ℂ} (ha : a ∈ UHP)
    (hK : 0 < s.re + K) :
    HasDerivAt (continuedAt (K + 1) s) (-s * continuedAt K (s + 1) a) a := by
  have hdeg : 0 < s.re + (K + 1 : ℕ) := by norm_num at hK ⊢; linarith
  have hshift : 0 < (s + 1).re + K := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  set ρ : ℝ := a.im / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith [show 0 < a.im from ha]
  set B : ℝ := ‖a - 1‖ + ρ with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * B)
  obtain ⟨C, hC0, hC⟩ := exists_binomial_remainder_bound (K + 1) s
  have hballU : Metric.ball a ρ ⊆ UHP := by
    intro w hw
    have hd : ‖w - a‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have himle : |(w - a).im| ≤ ‖w - a‖ := Complex.abs_im_le_norm _
    have him : (w - a).im = w.im - a.im := by simp
    rw [him] at himle
    have habs := abs_lt.mp (lt_of_le_of_lt himle hd)
    show 0 < w.im
    rw [hρ] at habs
    linarith
  have hballB : ∀ w ∈ Metric.ball a ρ, ‖w - 1‖ < B := by
    intro w hw
    have hd : ‖w - a‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    calc
      ‖w - 1‖ = ‖(w - a) + (a - 1)‖ := by congr 1; ring
      _ ≤ ‖w - a‖ + ‖a - 1‖ := norm_add_le _ _
      _ < B := by rw [hB]; linarith
  have hsK : 1 < (s + (K + 2 : ℕ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    norm_num at hK ⊢
    linarith
  let u : ℕ → ℝ := fun m => C * B ^ (K + 2) *
    ‖(((m + M + 1 : ℕ) : ℂ) ^ (-(s + (K + 2 : ℕ))))‖
  have hbase : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℂ) ^ (-(s + (K + 2 : ℕ))))) := by
    simpa [add_comm] using HurwitzZetaShift.summable_hurwitzSeries hsK 1
  have hbaseShift : Summable (fun m : ℕ =>
      (((m + M + 1 : ℕ) : ℂ) ^ (-(s + (K + 2 : ℕ))))) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (summable_nat_add_iff M).mpr hbase
  have hu : Summable u := by
    exact (summable_norm_iff.mpr hbaseShift).mul_left (C * B ^ (K + 2))
  let R : ℕ → ℂ → ℂ := fun m w => remainder (K + 1) s w (m + M)
  have hRdiff : ∀ m, DifferentiableOn ℂ (R m) (Metric.ball a ρ) := by
    intro m
    exact (remainder_differentiableOn (K + 1) s (m + M)).mono hballU
  have hRbound : ∀ m w, w ∈ Metric.ball a ρ → ‖R m w‖ ≤ u m := by
    intro m w hw
    have hwU : w ∈ UHP := hballU hw
    let y : ℂ := (w - 1) / ((m + M + 1 : ℕ) : ℂ)
    have hden : (2 * B : ℝ) < (m + M + 1 : ℕ) := by
      have hm0 : (0 : ℝ) ≤ m := by positivity
      norm_num at hM ⊢
      linarith
    have hy : ‖y‖ < 1 / 2 := by
      dsimp only [y]
      rw [norm_div, Complex.norm_natCast]
      have hwB := hballB w hw
      have hdenpos : (0 : ℝ) < (m + M + 1 : ℕ) := by positivity
      apply (div_lt_iff₀ hdenpos).mpr
      linarith
    have hbin := hC y hy
    have hrem : R m w =
        (((m + M + 1 : ℕ) : ℂ) ^ (-s)) *
          ((1 + y) ^ (-s) - (binomialSeries ℂ (-s)).partialSum (K + 2) y) := by
      dsimp only [R]
      rw [remainder, term_factor hwU, taylor_factor]
      dsimp only [y]
      ring
    rw [hrem, norm_mul]
    calc
      ‖(((m + M + 1 : ℕ) : ℂ) ^ (-s))‖ *
            ‖(1 + y) ^ (-s) - (binomialSeries ℂ (-s)).partialSum (K + 2) y‖
          ≤ ‖(((m + M + 1 : ℕ) : ℂ) ^ (-s))‖ *
              (C * ‖y‖ ^ (K + 2)) := mul_le_mul_of_nonneg_left hbin (norm_nonneg _)
      _ = C * (‖(((m + M + 1 : ℕ) : ℂ) ^ (-s))‖ *
              ‖(w - 1) / ((m + M + 1 : ℕ) : ℂ)‖ ^ (K + 2)) := by
            simp only [y]
            ring
      _ = C * (‖w - 1‖ ^ (K + 2) *
              ‖(((m + M + 1 : ℕ) : ℂ) ^ (-(s + (K + 2 : ℕ))))‖) := by
            rw [majorant_eq (K + 1)]
      _ ≤ C * (B ^ (K + 2) *
              ‖(((m + M + 1 : ℕ) : ℂ) ^ (-(s + (K + 2 : ℕ))))‖) := by
            gcongr
            exact (hballB w hw).le
      _ = u m := by dsimp only [u]; ring
  let tail : ℂ → ℂ := fun w => ∑' m : ℕ, R m w
  have htailDiff : DifferentiableOn ℂ tail (Metric.ball a ρ) :=
    Complex.differentiableOn_tsum_of_summable_norm hu hRdiff Metric.isOpen_ball hRbound
  have hDerivSum := Complex.hasSum_deriv_of_summable_norm hu hRdiff Metric.isOpen_ball hRbound
    (Metric.mem_ball_self hρpos)
  have hDerivSum' : HasSum
      (fun m : ℕ => -s * remainder K (s + 1) a (m + M)) (deriv tail a) := by
    convert! hDerivSum using 1
    funext m
    exact (remainder_succ_hasDerivAt (K := K) (s := s) (a := a) ha (m + M)).deriv.symm
  have htailValue : deriv tail a =
      -s * ∑' m : ℕ, remainder K (s + 1) a (m + M) := by
    rw [← hDerivSum'.tsum_eq]
    rw [tsum_mul_left]
  have htailHas : HasDerivAt tail
      (-s * ∑' m : ℕ, remainder K (s + 1) a (m + M)) a := by
    have h := (htailDiff.differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρpos))).hasDerivAt
    rwa [htailValue] at h
  let head : ℂ → ℂ := fun w => ∑ m ∈ Finset.range M, remainder (K + 1) s w m
  have hheadHas : HasDerivAt head
      (∑ m ∈ Finset.range M, -s * remainder K (s + 1) a m) a := by
    apply HasDerivAt.fun_sum
    intro m hm
    exact remainder_succ_hasDerivAt ha m
  have hrest := restoration_succ_hasDerivAt K s a
  let F : ℂ → ℂ := fun w => head w + tail w + restoration (K + 1) s w
  have hF : HasDerivAt F
      ((∑ m ∈ Finset.range M, -s * remainder K (s + 1) a m) +
        (-s * ∑' m : ℕ, remainder K (s + 1) a (m + M)) +
        (-s * restoration K (s + 1) a)) a :=
    (hheadHas.add htailHas).add hrest
  have heq : ∀ w ∈ Metric.ball a ρ, continuedAt (K + 1) s w = F w := by
    intro w hw
    have hsum := summable_remainder (hballU hw) hdeg
    unfold continuedAt
    dsimp only [F, head, tail, R]
    rw [← hsum.sum_add_tsum_nat_add M]
  have hev : continuedAt (K + 1) s =ᶠ[𝓝 a] F := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρpos)] with w hw
    exact heq w hw
  have hcont := hF.congr_of_eventuallyEq hev
  convert! hcont using 1
  have hsumShift := summable_remainder ha hshift
  rw [continuedAt]
  rw [← hsumShift.sum_add_tsum_nat_add M]
  rw [← Finset.mul_sum]
  ring

/-- A canonical sufficient Taylor degree.  It is zero throughout `Re s > 0` and otherwise is the
least natural number strictly larger than `-Re s`. -/
noncomputable def regularizationOrder (s : ℂ) : ℕ :=
  if 0 < s.re then 0 else Nat.find (exists_nat_gt (-s.re))

lemma regularizationOrder_eq_zero {s : ℂ} (hs : 0 < s.re) :
    regularizationOrder s = 0 := by simp [regularizationOrder, hs]

/-- The canonical Taylor degree always lies in the summability chamber. -/
lemma regularizationOrder_adequate (s : ℂ) :
    0 < s.re + regularizationOrder s := by
  by_cases hs : 0 < s.re
  · simp [regularizationOrder, hs]
  · rw [regularizationOrder, if_neg hs]
    have h := Nat.find_spec (exists_nat_gt (-s.re))
    norm_num at h ⊢
    linarith

/-- Once a Taylor degree is adequate, every larger degree defines the same continued value. -/
theorem continuedAt_eq_of_le {K L : ℕ} {s a : ℂ} (ha : a ∈ UHP)
    (hKL : K ≤ L) (hK : 0 < s.re + K) :
    continuedAt L s a = continuedAt K s a := by
  induction L, hKL using Nat.le_induction with
  | base => rfl
  | succ L hKL ih =>
      rw [continuedAt_succ ha]
      · exact ih
      · have hcast : (K : ℝ) ≤ L := by exact_mod_cast hKL
        linarith

/-- The continued value is independent of every adequate Taylor degree. -/
theorem continuedAt_eq_of_adequate {K L : ℕ} {s a : ℂ} (ha : a ∈ UHP)
    (hK : 0 < s.re + K) (hL : 0 < s.re + L) :
    continuedAt K s a = continuedAt L s a := by
  rcases le_total K L with hKL | hLK
  · exact (continuedAt_eq_of_le ha hKL hK).symm
  · exact continuedAt_eq_of_le ha hLK hL

/-- **Concrete analytically continued Hurwitz value in the shift variable.**  The definition uses
the canonical finite Taylor subtraction; `continuedHzeta_eq_hzeta` proves that it agrees with the
normally convergent Hurwitz series on `Re s > 1`. -/
noncomputable def continuedHzeta (s a : ℂ) : ℂ :=
  continuedAt (regularizationOrder s) s a

/-- **Unrestricted shift-derivative law.**  For every complex exponent, the concrete continued
Hurwitz function satisfies `∂ₐ ζ(s,a) = -s ζ(s+1,a)` throughout the upper half-plane. -/
theorem continuedHzeta_hasDerivAt {s a : ℂ} (ha : a ∈ UHP) :
    HasDerivAt (continuedHzeta s) (-s * continuedHzeta (s + 1) a) a := by
  let K := regularizationOrder s
  have hK : 0 < s.re + K := regularizationOrder_adequate s
  have hraw := continuedAt_succ_hasDerivAt (K := K) (s := s) ha hK
  have hevent : continuedHzeta s =ᶠ[𝓝 a] continuedAt (K + 1) s := by
    filter_upwards [isOpen_UHP.mem_nhds ha] with w hw
    rw [continuedHzeta]
    exact (continuedAt_succ hw hK).symm
  have h := hraw.congr_of_eventuallyEq hevent
  convert! h using 1
  have hshift : 0 < (s + 1).re + K := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  simpa [continuedHzeta] using! congrArg (fun z : ℂ => -s * z)
    (continuedAt_eq_of_adequate (K := K) (L := regularizationOrder (s + 1))
      ha hshift (regularizationOrder_adequate (s + 1))).symm

/-- The concrete continued Hurwitz function is holomorphic on the upper half-plane for every
complex exponent. -/
theorem continuedHzeta_differentiableOn (s : ℂ) :
    DifferentiableOn ℂ (continuedHzeta s) UHP := by
  intro a ha
  exact (continuedHzeta_hasDerivAt ha).differentiableAt.differentiableWithinAt

/-- Analytic form of unrestricted upper-half-plane continuation. -/
theorem continuedHzeta_analyticOnNhd (s : ℂ) :
    AnalyticOnNhd ℂ (continuedHzeta s) UHP :=
  (continuedHzeta_differentiableOn s).analyticOnNhd isOpen_UHP

/-- **All-order unrestricted Hurwitz differential ladder.**  For every complex exponent,
`d^r/da^r ζ(s,a) = (-1)^r (s)_r ζ(s+r,a)` on the upper half-plane. -/
theorem continuedHzeta_iteratedDeriv (r : ℕ) {s a : ℂ} (ha : a ∈ UHP) :
    iteratedDeriv r (continuedHzeta s) a =
      (-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s * continuedHzeta (s + r) a := by
  induction r generalizing a with
  | zero => simp
  | succ r ih =>
      rw [show r + 1 = Nat.succ r by rfl, iteratedDeriv_succ]
      have hevent : iteratedDeriv r (continuedHzeta s) =ᶠ[𝓝 a]
          (fun z => (-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s *
            continuedHzeta (s + r) z) := by
        filter_upwards [isOpen_UHP.mem_nhds ha] with z hz
        exact ih hz
      rw [hevent.deriv_eq]
      have hd := (continuedHzeta_hasDerivAt (s := s + (r : ℂ)) ha).const_mul
        ((-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s)
      rw [hd.deriv]
      rw [ascPochhammer_succ_eval]
      push_cast
      rw [pow_succ]
      ring_nf

lemma taylorPoly_at_one (K : ℕ) (s : ℂ) (m : ℕ) :
    taylorPoly K s 1 m = (((m + 1 : ℕ) : ℂ) ^ (-s)) := by
  rw [taylorPoly]
  rw [Finset.sum_eq_single 0]
  · simp [taylorTerm]
  · intro r hr hr0
    simp [taylorTerm, hr0]
  · simp

lemma restoration_at_one (K : ℕ) (s : ℂ) :
    restoration K s 1 = riemannZeta s := by
  rw [restoration]
  rw [Finset.sum_eq_single 0]
  · simp [restoreTerm]
  · intro r hr hr0
    simp [restoreTerm, hr0]
  · simp

/-- The continuation is normalized by the meromorphically continued Riemann zeta value at the
reference shift. -/
theorem continuedHzeta_at_one (s : ℂ) :
    continuedHzeta s 1 = riemannZeta s := by
  rw [continuedHzeta, continuedAt, restoration_at_one]
  have hrem : (fun m : ℕ => remainder (regularizationOrder s) s 1 m) = 0 := by
    funext m
    rw [remainder, taylorPoly_at_one]
    push_cast
    simp
  rw [hrem]
  change (∑' _m : ℕ, (0 : ℂ)) + riemannZeta s = riemannZeta s
  simp

lemma taylorPoly_zero (s a : ℂ) (m : ℕ) :
    taylorPoly 0 s a m = (((m + 1 : ℕ) : ℂ) ^ (-s)) := by
  simp [taylorPoly, taylorTerm]

lemma restoration_zero (s a : ℂ) : restoration 0 s a = riemannZeta s := by
  simp [restoration, restoreTerm]

/-- In the convergence half-plane, the zero-degree regularization is the original Hurwitz series. -/
lemma continuedAt_zero_eq_hzeta {s a : ℂ} (hs : 1 < s.re) :
    continuedAt 0 s a = HurwitzZetaShift.hzeta s a := by
  have ha := HurwitzZetaShift.summable_hurwitzSeries hs a
  have h1 := HurwitzZetaShift.summable_hurwitzSeries hs 1
  rw [continuedAt, restoration_zero]
  have hsub := ha.tsum_sub h1
  have heq : (fun m : ℕ =>
      ((m : ℂ) + a) ^ (-s) - (((m : ℂ) + 1) ^ (-s))) = remainder 0 s a := by
    funext m
    rw [remainder, taylorPoly_zero]
    push_cast
    rfl
  rw [← heq, hsub]
  rw [show (∑' m : ℕ, ((m : ℂ) + a) ^ (-s)) = HurwitzZetaShift.hzeta s a by rfl]
  have hb : (∑' m : ℕ, ((m : ℂ) + 1) ^ (-s)) = riemannZeta s := by
    simpa only [Nat.cast_add, Nat.cast_one] using base_tsum_eq_riemannZeta hs
  rw [hb]
  ring

/-- **Agreement with the classical convergence branch.** -/
theorem continuedHzeta_eq_hzeta {s a : ℂ} (hs : 1 < s.re) :
    continuedHzeta s a = HurwitzZetaShift.hzeta s a := by
  rw [continuedHzeta, regularizationOrder_eq_zero (lt_trans (by norm_num) hs)]
  exact continuedAt_zero_eq_hzeta hs

end HurwitzZetaContinuation
