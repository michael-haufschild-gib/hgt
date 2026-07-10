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
    intro hzero
    have hdiv : z / a = 1 := (sub_eq_zero.mp hzero).symm
    apply hz
    calc
      z = z / a * a := (div_mul_cancel₀ z ha).symm
      _ = 1 * a := by rw [hdiv]
      _ = a := one_mul a
  have hfac : weierstrassE1 (z / a) ≠ 0 := by
    rw [weierstrassE1]
    exact mul_ne_zero hone (Complex.exp_ne_zero _)
  have hE : HasDerivAt weierstrassE1
      (-(z / a) * Complex.exp (z / a)) (z / a) := by
    have hraw := ((hasDerivAt_const (x := z / a) (c := (1 : ℂ))).sub
      (hasDerivAt_id (z / a))).mul (Complex.hasDerivAt_exp (z / a))
    convert hraw using 1
    simp
    ring
  have hderiv : deriv (fun w : ℂ => weierstrassE1 (w / a)) z =
      (-(z / a) * Complex.exp (z / a)) * (1 / a) := by
    simpa only [Function.comp_apply] using (hE.comp z hlin).deriv
  rw [logDeriv_apply, hderiv, weierstrassE1]
  have hden : (1 - z / a) * Complex.exp (z / a) ≠ 0 :=
    mul_ne_zero hone (Complex.exp_ne_zero _)
  have haz : a - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  rw [div_eq_iff hden]
  field_simp [ha, haz]

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
  rw [inv_eq_one_div]
  field_simp [ha, haz]
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
    · intro hzero
      have hdiv : z / xiSpectralPoint q = 1 := (sub_eq_zero.mp hzero).symm
      apply hza q
      calc
        z = z / xiSpectralPoint q * xiSpectralPoint q :=
          (div_mul_cancel₀ z (xiSpectralPoint_ne_zero q)).symm
        _ = 1 * xiSpectralPoint q := by rw [hdiv]
        _ = xiSpectralPoint q := one_mul _
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
    hfac (by
      intro q
      simp only [weierstrassE1]
      fun_prop) hsum
    xiCanonicalProduct_hasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn hprod
  rw [xiRelativeResolventTrace]
  calc
    logDeriv xiCanonicalProduct z =
        ∑' q : XiZeroCopy,
          logDeriv (fun w : ℂ => weierstrassE1 (w / xiSpectralPoint q)) z := by
      simpa only [xiCanonicalProduct, canonicalProductE1Indexed] using hlog
    _ =
        ∑' q : XiZeroCopy,
          -z / (xiSpectralPoint q * (xiSpectralPoint q - z)) := by
      apply tsum_congr
      intro q
      exact logDeriv_weierstrassE1_div
        (xiSpectralPoint_ne_zero q) (hza q)
    _ = ∑' q : XiZeroCopy, xiRelativeResolventTerm z q := by
      apply tsum_congr
      intro q
      have ha := xiSpectralPoint_ne_zero q
      have haz : xiSpectralPoint q - z ≠ 0 := by
        exact sub_ne_zero.mpr (Ne.symm (hza q))
      rw [xiRelativeResolventTerm]
      rw [inv_eq_one_div]
      field_simp [ha, haz]
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

/-- The inverse square of the centered spectral coordinate, indexed with the exact multiplicity
of the Xi divisor. -/
def xiZeroCopyReciprocalSquare (q : XiZeroCopy) : ℂ :=
  (xiSpectralPoint q)⁻¹ ^ 2

theorem xiZeroCopyReciprocalSquare_eq (q : XiZeroCopy) :
    xiZeroCopyReciprocalSquare q = xiCentralReciprocalSquare (q.1 : ℂ) := by
  rw [xiZeroCopyReciprocalSquare, xiCentralReciprocalSquare, xiSpectralPoint]
  have hb : (q.1 : ℂ) - 1 / 2 ≠ 0 := sub_ne_zero.mpr (xi_divisor_support_ne_half q.1)
  field_simp [hb, Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring

theorem summable_xiZeroCopyReciprocalSquare :
    Summable xiZeroCopyReciprocalSquare := by
  refine Summable.of_norm_bounded xiSpectralPoint_inv_sq_summable (fun q => ?_)
  simp [xiZeroCopyReciprocalSquare, norm_pow, norm_inv, one_div, inv_pow]

/-- The reciprocal-square resolvent term obtained after pairing a centered zero with its
functional-equation reflection. -/
def xiReciprocalSquareResolventTerm (z : ℂ) (q : XiZeroCopy) : ℂ :=
  xiZeroCopyReciprocalSquare q /
    (1 - z ^ 2 * xiZeroCopyReciprocalSquare q)

theorem pair_xiRelativeResolventTerm (z : ℂ) (q : XiZeroCopy)
    (hzp : z ≠ xiSpectralPoint q) (hzn : z ≠ -xiSpectralPoint q) :
    xiRelativeResolventTerm z q +
      xiRelativeResolventTerm z (xiZeroCopyReflectEquiv q) =
        -2 * z * xiReciprocalSquareResolventTerm z q := by
  have ha := xiSpectralPoint_ne_zero q
  have hp : xiSpectralPoint q - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzp)
  have hn : -xiSpectralPoint q - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzn)
  have hapz : xiSpectralPoint q + z ≠ 0 := by
    intro h
    apply hzn
    linear_combination h
  have hsq : xiSpectralPoint q ^ 2 - z ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hapz hp
  rw [xiRelativeResolventTerm, xiRelativeResolventTerm,
    xiSpectralPoint_reflect, xiReciprocalSquareResolventTerm,
    xiZeroCopyReciprocalSquare]
  field_simp [ha, hp, hn, hsq]
  ring

theorem summable_xiReciprocalSquareResolventTerm {z : ℂ} (hz : XiC z ≠ 0) :
    Summable (xiReciprocalSquareResolventTerm z) := by
  by_cases hz0 : z = 0
  · subst z
    apply summable_xiZeroCopyReciprocalSquare.congr
    intro q
    simp [xiReciprocalSquareResolventTerm]
  · have hR := summable_xiRelativeResolventTerm hz
    have hRref : Summable (fun q =>
        xiRelativeResolventTerm z (xiZeroCopyReflectEquiv q)) :=
      (xiZeroCopyReflectEquiv.summable_iff).mpr hR
    have hpair := hR.add hRref
    have hscale := hpair.mul_left ((-2 * z)⁻¹)
    apply hscale.congr
    intro q
    have hzp : z ≠ xiSpectralPoint q := by
      intro h
      exact hz ((XiC_eq_zero_iff_exists_xiZeroCopy z).mpr ⟨q, h.symm⟩)
    have hzn : z ≠ -xiSpectralPoint q := by
      intro h
      exact hz ((XiC_eq_zero_iff_exists_xiZeroCopy z).mpr
        ⟨xiZeroCopyReflectEquiv q, by rw [xiSpectralPoint_reflect, ← h]⟩)
    rw [pair_xiRelativeResolventTerm z q hzp hzn]
    field_simp [hz0]

/-- **Paired target identity.**  Reflection symmetry converts the centered relative resolvent into
the reciprocal-square resolvent whose Taylor coefficients are the central reciprocal moments.
This is an identity of the Xi divisor; it is not an operator-spectrum assertion. -/
theorem xiRelativeResolventTrace_eq_reciprocalSquareResolvent
    {z : ℂ} (hz : XiC z ≠ 0) :
    xiRelativeResolventTrace z =
      -z * ∑' q : XiZeroCopy, xiReciprocalSquareResolventTerm z q := by
  by_cases hz0 : z = 0
  · subst z
    simp [xiRelativeResolventTrace, xiRelativeResolventTerm]
  · have hR := summable_xiRelativeResolventTerm hz
    have hRref : Summable (fun q =>
        xiRelativeResolventTerm z (xiZeroCopyReflectEquiv q)) :=
      (xiZeroCopyReflectEquiv.summable_iff).mpr hR
    have hg := summable_xiReciprocalSquareResolventTerm hz
    have hreindex : (∑' q, xiRelativeResolventTerm z (xiZeroCopyReflectEquiv q)) =
        xiRelativeResolventTrace z := by
      rw [xiRelativeResolventTrace]
      exact xiZeroCopyReflectEquiv.tsum_eq (xiRelativeResolventTerm z)
    have hpair :
        (∑' q, (xiRelativeResolventTerm z q +
          xiRelativeResolventTerm z (xiZeroCopyReflectEquiv q))) =
          -2 * z * ∑' q, xiReciprocalSquareResolventTerm z q := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro q
      have hzp : z ≠ xiSpectralPoint q := by
        intro h
        exact hz ((XiC_eq_zero_iff_exists_xiZeroCopy z).mpr ⟨q, h.symm⟩)
      have hzn : z ≠ -xiSpectralPoint q := by
        intro h
        exact hz ((XiC_eq_zero_iff_exists_xiZeroCopy z).mpr
          ⟨xiZeroCopyReflectEquiv q, by rw [xiSpectralPoint_reflect, ← h]⟩)
      exact pair_xiRelativeResolventTerm z q hzp hzn
    rw [hR.tsum_add hRref, hreindex] at hpair
    change xiRelativeResolventTrace z + xiRelativeResolventTrace z = _ at hpair
    rw [← two_mul] at hpair
    calc
      xiRelativeResolventTrace z =
          (-2 * z * ∑' q, xiReciprocalSquareResolventTerm z q) / 2 := by
        rw [← hpair]
        ring
      _ = -z * ∑' q, xiReciprocalSquareResolventTerm z q := by ring

/-- Every coefficient of the reciprocal-square resolvent is absolutely summable over the
multiplicity-copy Xi divisor. -/
theorem summable_xiZeroCopyReciprocalSquare_pow (n : ℕ) :
    Summable (fun q : XiZeroCopy => xiZeroCopyReciprocalSquare q ^ (n + 1)) := by
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
  constructor
  · intro ρ
    exact (hasSum_fintype _).summable
  · have hweighted := (xi_central_reciprocal_moment_summable n).norm
    apply hweighted.congr
    intro ρ
    rw [tsum_fintype]
    simp only [xiZeroCopyReciprocalSquare_eq, norm_pow, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnonneg : 0 ≤ (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) :=
      le_of_lt (xi_divisor_pos_on_support ρ)
    have hcast :
        (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)).toNat : ℝ) =
          ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by exact_mod_cast hnonneg)]
    rw [norm_pow, hcast]

/-- The coefficient sum of the paired relative resolvent is exactly the existing central
reciprocal moment, with divisor multiplicity retained and no enumeration chosen. -/
theorem tsum_xiZeroCopyReciprocalSquare_pow (n : ℕ) :
    (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q ^ (n + 1)) =
      xiCentralReciprocalMoment n := by
  have hcopy := summable_xiZeroCopyReciprocalSquare_pow n
  rw [hcopy.tsum_sigma]
  rw [xiCentralReciprocalMoment]
  apply tsum_congr
  intro ρ
  rw [tsum_fintype]
  simp only [xiZeroCopyReciprocalSquare_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hnonneg : 0 ≤ (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) :=
    le_of_lt (xi_divisor_pos_on_support ρ)
  have hcastR :
      (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)).toNat : ℝ) =
        ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  have hcast :
      (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)).toNat : ℂ) =
        ((((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ)) : ℂ) := by
    exact_mod_cast hcastR
  rw [hcast]

end

end RHTower
