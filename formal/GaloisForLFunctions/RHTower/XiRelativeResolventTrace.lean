/-
# The centered, regulator-independent relative resolvent trace of Xi

The genus-one factor attached to a nonzero centered zero `a` contributes

`logDeriv (E₁(z/a)) = a⁻¹ - (a-z)⁻¹ = -z/(a(a-z))`.

The subtraction at the functional-equation centre improves the unsummable first-order resolvent
to inverse-square size.  Since the centered Xi divisor is inverse-square summable, the resulting
series is absolutely summable over the multiplicity-copy index, without choosing an enumeration,
prime cutoff, or regulator path.  The unconditional Hadamard factorization then identifies its
sum with `logDeriv XiC`.

This is a target-side theorem: it identifies the exact relative trace a source construction must
produce.  It does not manufacture an operator with the Xi zeros as spectrum and is not itself an
RH proof.
-/
import GaloisForLFunctions.RHTower.XiHadamardGrowth
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn

open Complex Metric Function Filter Topology

namespace RHTower

noncomputable section

/-- Logarithmic derivative of one rescaled genus-one factor. -/
theorem logDeriv_weierstrassE1_div {a z : ℂ} (ha : a ≠ 0) (hz : z ≠ a) :
    logDeriv (fun w : ℂ => weierstrassE1 (w / a)) z =
      -z / (a * (a - z)) := by
  have hlin : HasDerivAt (fun w : ℂ => w / a) (1 / a) z := by
    simpa [one_div] using (hasDerivAt_id z).div_const a
  have hone : 1 - z / a ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hz
    field_simp [ha] at h ⊢
  have hfac : weierstrassE1 (z / a) ≠ 0 := by
    rw [weierstrassE1]
    exact mul_ne_zero hone (Complex.exp_ne_zero _)
  have hE : HasDerivAt weierstrassE1
      (-(z / a) * Complex.exp (z / a)) (z / a) := by
    rw [weierstrassE1]
    convert ((hasDerivAt_const (x := z / a) (c := (1 : ℂ))).sub
      (hasDerivAt_id (z / a))).mul (Complex.hasDerivAt_exp (z / a)) using 1
    ring
  have hcomp := hE.comp z hlin
  rw [logDeriv_apply, hcomp.deriv]
  rw [weierstrassE1]
  field_simp [ha, hone, Complex.exp_ne_zero]
  ring

/-- The centered resolvent subtraction has inverse-square size and is absolutely summable over
the actual Xi divisor with exact multiplicity. -/
theorem summable_xi_relativeResolventTerms (z : ℂ) :
    Summable (fun q : XiZeroCopy =>
      -z / (xiSpectralPoint q * (xiSpectralPoint q - z))) := by
  let a : XiZeroCopy → ℂ := xiSpectralPoint
  let S : ℝ := 2 * ‖z‖ + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have hbase : Summable (fun q : XiZeroCopy => 1 / ‖a q‖ ^ 2) :=
    xiSpectralPoint_inv_sq_summable
  have hev : ∀ᶠ q in cofinite, S ≤ ‖a q‖ := by
    have htend := hbase.tendsto_cofinite_zero
    have hlt : ∀ᶠ q in cofinite, 1 / ‖a q‖ ^ 2 < 1 / S ^ 2 :=
      htend.eventually_lt_const (by positivity)
    filter_upwards [hlt] with q hq
    have haq : 0 < ‖a q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    have hsq : S ^ 2 < ‖a q‖ ^ 2 :=
      lt_of_one_div_lt_one_div (pow_pos haq 2) hq
    exact le_of_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq)
  refine (hbase.mul_left (2 * ‖z‖)).of_norm_bounded_eventually ?_
  filter_upwards [hev] with q hq
  have haz : ‖z‖ ≤ ‖a q‖ / 2 := by
    dsimp [S] at hq
    linarith
  have hdiff : ‖a q‖ / 2 ≤ ‖a q - z‖ := by
    have hrev := norm_sub_norm_le (a q) z
    linarith
  have ha0 : 0 < ‖a q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hd0 : 0 < ‖a q - z‖ := lt_of_lt_of_le (half_pos ha0) hdiff
  rw [norm_div, norm_neg, norm_mul]
  change ‖z‖ / (‖a q‖ * ‖a q - z‖) ≤ 2 * ‖z‖ * (1 / ‖a q‖ ^ 2)
  have hden : ‖a q‖ ^ 2 / 2 ≤ ‖a q‖ * ‖a q - z‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hdiff (norm_nonneg (a q))]
  by_cases hz0 : ‖z‖ = 0
  · simp [hz0]
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz0)
    rw [div_le_iff₀ (mul_pos ha0 hd0)]
    field_simp
    nlinarith

/-- The centered relative resolvent term, written as the difference of two resolvents. -/
def xiRelativeResolventTerm (z : ℂ) (q : XiZeroCopy) : ℂ :=
  (xiSpectralPoint q)⁻¹ - (xiSpectralPoint q - z)⁻¹

/-- The regulator-independent target relative trace.  The `tsum` is unconditional, hence carries
no choice of zero enumeration or exhaustion. -/
def xiRelativeResolventTrace (z : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, xiRelativeResolventTerm z q

theorem summable_xiRelativeResolventTerm {z : ℂ} (hz : XiC z ≠ 0) :
    Summable (xiRelativeResolventTerm z) := by
  apply (summable_xi_relativeResolventTerms z).congr
  intro q
  rw [xiRelativeResolventTerm]
  have ha := xiSpectralPoint_ne_zero q
  have hzq : z ≠ xiSpectralPoint q := by
    intro h
    exact hz ((XiC_eq_zero_iff_exists_xiZeroCopy z).mpr ⟨q, h.symm⟩)
  have haz : xiSpectralPoint q - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzq)
  field_simp
  ring

/-- Logarithmic derivative of the canonical product as the absolutely summable centered relative
resolvent trace. -/
theorem logDeriv_xiCanonicalProduct_eq_relativeResolventTrace
    {z : ℂ} (hz : XiC z ≠ 0) :
    logDeriv xiCanonicalProduct z = xiRelativeResolventTrace z := by
  have hza (q : XiZeroCopy) : z ≠ xiSpectralPoint q := by
    intro h
    apply hz
    exact (XiC_eq_zero_iff_exists_xiZeroCopy z).mpr ⟨q, h.symm⟩
  have hfac (q : XiZeroCopy) :
      weierstrassE1 (z / xiSpectralPoint q) ≠ 0 := by
    rw [weierstrassE1]
    apply mul_ne_zero
    · rw [sub_ne_zero]
      intro h
      apply hza q
      field_simp [xiSpectralPoint_ne_zero q] at h ⊢
    · exact Complex.exp_ne_zero _
  have hsum : Summable (fun q : XiZeroCopy =>
      logDeriv (fun w : ℂ => weierstrassE1 (w / xiSpectralPoint q)) z) := by
    apply (summable_xi_relativeResolventTerms z).congr
    intro q
    exact (logDeriv_weierstrassE1_div
      (xiSpectralPoint_ne_zero q) (hza q)).symm
  have hprod : xiCanonicalProduct z ≠ 0 := by
    intro hzero
    exact hz ((xiCanonicalProduct_eq_zero_iff_XiC_eq_zero z).mp hzero)
  have hlog := logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z)
    hfac (by intro q; fun_prop) hsum
    xiCanonicalProduct_hasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn hprod
  rw [xiRelativeResolventTrace]
  calc
    logDeriv xiCanonicalProduct z =
        ∑' q : XiZeroCopy,
          -z / (xiSpectralPoint q * (xiSpectralPoint q - z)) := by
      simpa only [xiCanonicalProduct, canonicalProductE1Indexed] using hlog
    _ = ∑' q : XiZeroCopy, xiRelativeResolventTerm z q := by
      apply tsum_congr
      intro q
      have ha := xiSpectralPoint_ne_zero q
      have haz : xiSpectralPoint q - z ≠ 0 := by
        exact sub_ne_zero.mpr (Ne.symm (hza q))
      rw [xiRelativeResolventTerm]
      field_simp
      ring

/-- **Exact target identity.**  The centered Xi logarithmic derivative is the canonical relative
resolvent trace.  The subtraction, convergence, and equality are unconditional and contain no
cutoff path. -/
theorem logDeriv_XiC_eq_relativeResolventTrace {z : ℂ} (hz : XiC z ≠ 0) :
    logDeriv XiC z = xiRelativeResolventTrace z := by
  rw [XiC_eq_constant_mul_canonicalProduct]
  change logDeriv (fun w => XiC 0 * xiCanonicalProduct w) z = _
  rw [logDeriv_const_mul z (XiC 0) XiC_zero_ne]
  exact logDeriv_xiCanonicalProduct_eq_relativeResolventTrace hz

end

end RHTower
