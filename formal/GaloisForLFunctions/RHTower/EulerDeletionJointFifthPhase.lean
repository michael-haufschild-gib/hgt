import GaloisForLFunctions.RHTower.EulerDeletionJointProductSharpness
import GaloisForLFunctions.RHTower.EulerDeletionPowerSumRemainder
import GaloisForLFunctions.RHTower.ZetaPartialSumStrip
import GaloisForLFunctions.RHTower.PrimeLogIncommensuratePhaseClock
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Actual joint deletion product: complex fifth-word asymptotic

Complete-block averaging isolates the exact phase-bearing fifth-order source.
Its full absolutely summable correction is retained. The actual source product has
an explicit complex-power counterterm, with a logarithmic branch at one fifth.
Below that line its phase-normalized leading term is nonzero. On the remaining
boundary, the injective two-prime phase clock excludes convergence. Thus the fixed
literal matrix source converges exactly when the real part exceeds one fifth.

All statements follow from symbolic finite identities and analytic limits. No zero
premise, numerical certificate, or new axiom is used. This boundary is nonselective
in the right half of the critical strip and supplies no RH implication.
-/

open Filter Topology
open scoped BigOperators Matrix.Norms.Operator
namespace RHTower.DeletionJointSharpness
open GaloisForLFunctions.HTGeometry.NoncommutativeAbel
noncomputable section
local instance : TopologicalSpace A := (inferInstance : NormedRing A).toUniformSpace.toTopologicalSpace

/-- Difference between the first source weight and its complete six-term block average. -/
def strideCorrection (w : ℂ) (k : ℕ) : ℂ :=
  arithmeticDirichletWeight w (6*k) -
    (∑ j ∈ Finset.range 6, arithmeticDirichletWeight w (6*k+j))/6

/-- Full within-block averaging correction is absolutely summable on the positive half-plane. -/
theorem strideCorrection_summable {w : ℂ} (hw : 0 < w.re) :
    Summable (fun k => ‖strideCorrection w k‖) := by
  have hj (j : ℕ) : Summable (fun k =>
      ‖arithmeticDirichletWeight w (6*k+j) - arithmeticDirichletWeight w (6*k)‖) :=
    DeletionJointProduct.summable_stride_difference
      (arithmeticDirichletWeight_summable_variation hw) j
  have hc : Summable (fun k => ∑ j ∈ Finset.range 6,
      ‖arithmeticDirichletWeight w (6*k+j) - arithmeticDirichletWeight w (6*k)‖) :=
    by
      suffices ∀ n : ℕ, Summable (fun k => ∑ j ∈ Finset.range n,
          ‖arithmeticDirichletWeight w (6*k+j) - arithmeticDirichletWeight w (6*k)‖) from this 6
      intro n
      induction n with
      | zero => simp
      | succ n ih => simpa only [Finset.sum_range_succ] using ih.add (hj n)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hc.div_const 6)
  intro k
  have he : strideCorrection w k =
      -(∑ j ∈ Finset.range 6,
        (arithmeticDirichletWeight w (6*k+j) - arithmeticDirichletWeight w (6*k)))/6 := by
    simp [strideCorrection, Finset.sum_sub_distrib]
    ring
  rw [he, norm_div, norm_neg]
  norm_num only [Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right (norm_sum_le _ _) (by norm_num)

/-- Exact complete-block regrouping before any passage to a limit. -/
theorem stride_sum_decomposition (w : ℂ) (N : ℕ) :
    ∑ k ∈ Finset.range N, arithmeticDirichletWeight w (6*k) =
      (∑ n ∈ Finset.range (6*N), arithmeticDirichletWeight w n)/6 +
        ∑ k ∈ Finset.range N, strideCorrection w k := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ, Nat.mul_succ]
    rw [ih]
    simp only [strideCorrection, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, Nat.add_zero]
    ring

/-- The exact surviving coefficient is the fifth dilate of the complex exponent. -/
theorem fifthCoefficient_eq_weight (s : ℂ) (k : ℕ) :
    fifthCoefficient s k = arithmeticDirichletWeight (5*s) (6*k)/60 := by
  unfold fifthCoefficient arithmeticDirichletWeight
  rw [← Complex.cpow_nat_mul]
  congr 2
  ring

/-- The full scalar asymptotic retains both the ordinary zeta value and averaging correction. -/
theorem tendsto_stride_sum_sub_power {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    Tendsto (fun N => (∑ k ∈ Finset.range N, arithmeticDirichletWeight w (6*k)) -
      (6*(N:ℂ))^(1-w)/(6*(1-w))) atTop
      (nhds (riemannZeta w/6 + ∑' k, strideCorrection w k)) := by
  have hp := (tendsto_sum_cpow_sub_pow hw hw1).comp
    (DeletionJointProduct.stride_tendsto 0)
  simp only [Function.comp_def, Nat.add_zero, sum_Icc_eq_sum_range_succ] at hp
  simp only [Nat.cast_mul, Nat.cast_ofNat, Complex.ofReal_mul,
    Complex.ofReal_natCast, Complex.ofReal_ofNat] at hp
  have hd := (strideCorrection_summable hw).of_norm.hasSum.tendsto_sum_nat
  convert (hp.div_const 6).add hd using 1
  · funext N
    rw [stride_sum_decomposition]
    simp only [arithmeticDirichletWeight, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev]
    ring

/-- Every actual complete source prefix has an explicit complex power counterterm. -/
theorem sourceProduct_power_asymptotic {s : ℂ} (hs : 0 < s.re) (hs1 : 5*s ≠ 1) :
    ∃ V : A, Tendsto (orderedProduct (correctedBlock s)) atTop (nhds V) ∧
      Tendsto (fun N => orderedProduct
        (DeletionJointProduct.sourceFactor generatorX generatorY s) (6*N) +
          ((6*(N:ℂ))^(1-5*s)/(360*(1-5*s))) • topWord) atTop
        (nhds (V - ((riemannZeta (5*s)/6 + ∑' k, strideCorrection (5*s) k)/60) • topWord)) := by
  obtain ⟨V,hV⟩ := correctedProduct_converges hs
  refine ⟨V,hV,?_⟩
  have hw : 0 < (5*s).re := by simp; linarith
  have hp := ((tendsto_stride_sum_sub_power hw hs1).div_const 60).smul_const topWord
  convert hV.sub hp using 1
  funext N
  rw [DeletionJointProduct.sourceProduct_six_mul]
  change orderedProduct (actualBlock s) N + _ = _
  rw [actualProduct_decomposition]
  simp only [fifthCoefficient_eq_weight]
  rw [← Finset.sum_div]
  simp only [div_eq_mul_inv, mul_inv_rev]
  module


/-- The actual source has a nonzero phase-normalized leading term below the one-fifth line. -/
theorem sourceProduct_scaled_limit {s : ℂ} (hs : 0 < s.re) (hs' : s.re < (1:ℝ)/5) :
    Tendsto (fun N : ℕ => ((6*(N:ℂ))^(5*s-1)) • orderedProduct
      (DeletionJointProduct.sourceFactor generatorX generatorY s) (6*N)) atTop
      (nhds (-(1/(360*(1-5*s))) • topWord)) := by
  have hs1 : 5*s ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  obtain ⟨V,_,hV⟩ := sourceProduct_power_asymptotic hs hs1
  have hz : (5*s-1).re < 0 := by simp; linarith
  have ha := (DeletionMixedRefinement.tendsto_nat_cpow_zero hz).comp
    (DeletionJointProduct.stride_tendsto 0)
  simp only [Function.comp_def, Nat.add_zero, Nat.cast_mul, Nat.cast_ofNat] at ha
  have ht := (ha.smul hV).sub_const ((1/(360*(1-5*s))) • topWord)
  simp only [zero_smul, zero_sub, ← neg_smul] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (6*(N:ℂ)) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    exact_mod_cast (by omega : N ≠ 0)
  have he : ((6*(N:ℂ))^(5*s-1)) *
      ((6*(N:ℂ))^(1-5*s)/(360*(1-5*s))) = 1/(360*(1-5*s)) := by
    rw [← mul_div_assoc, ← Complex.cpow_add _ _ hn]
    rw [show (5*s-1)+(1-5*s) = (0:ℂ) by ring, Complex.cpow_zero]
  simp only [smul_add, smul_smul, he, add_sub_cancel_right]

/-- Complex divergence below the line follows from a nonzero exact scaled source limit. -/
theorem sourceProduct_not_convergent_of_re_lt {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < (1:ℝ)/5) :
    ¬ ∃ U : A, Tendsto
      (orderedProduct (DeletionJointProduct.sourceFactor generatorX generatorY s))
      atTop (nhds U) := by
  rintro ⟨U,hU⟩
  have hz : (5*s-1).re < 0 := by simp; linarith
  have ha := (DeletionMixedRefinement.tendsto_nat_cpow_zero hz).comp
    (DeletionJointProduct.stride_tendsto 0)
  have hP := hU.comp (DeletionJointProduct.stride_tendsto 0)
  simp only [Function.comp_def, Nat.add_zero, Nat.cast_mul, Nat.cast_ofNat] at ha hP
  have hzero := ha.smul hP
  simp only [zero_smul] at hzero
  have he := tendsto_nhds_unique (sourceProduct_scaled_limit hs hs') hzero
  have hh := congrArg (fun M : A => M 0 5) he
  simp only [Matrix.smul_apply, smul_eq_mul, topWord_entry, mul_one, Matrix.zero_apply,
    neg_eq_zero, one_div, inv_eq_zero] at hh
  have hs1 : 1-5*s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  exact (mul_ne_zero (by norm_num : (360:ℂ) ≠ 0) hs1) hh

/-- Complete-block harmonic asymptotic retains the full absolutely summable correction. -/
theorem tendsto_stride_sum_sub_log :
    Tendsto (fun N => (∑ k ∈ Finset.range N, arithmeticDirichletWeight 1 (6*k)) -
      (Real.log (6*(N:ℝ)):ℂ)/6) atTop
      (nhds ((Real.eulerMascheroniConstant:ℂ)/6 + ∑' k, strideCorrection 1 k)) := by
  have he (N : ℕ) : (∑ n ∈ Finset.range N, arithmeticDirichletWeight 1 n) =
      ((harmonic N : ℝ):ℂ) := by
    simp [arithmeticDirichletWeight, harmonic, Complex.cpow_neg_one]
  have hp := Real.tendsto_harmonic_sub_log.ofReal.comp
    (DeletionJointProduct.stride_tendsto 0)
  simp only [Function.comp_def, Nat.add_zero, Nat.cast_mul, Nat.cast_ofNat,
    Complex.ofReal_sub] at hp
  have hd := (strideCorrection_summable (w := 1) (by norm_num)).of_norm.hasSum.tendsto_sum_nat
  convert (hp.div_const 6).add hd using 1
  funext N
  rw [stride_sum_decomposition, he]
  ring

/-- The exceptional real parameter has its exact logarithmic source counterterm. -/
theorem sourceProduct_log_asymptotic :
    ∃ V : A, Tendsto (orderedProduct (correctedBlock (1/5))) atTop (nhds V) ∧
      Tendsto (fun N => orderedProduct
        (DeletionJointProduct.sourceFactor generatorX generatorY (1/5)) (6*N) +
          ((Real.log (6*(N:ℝ)):ℂ)/360) • topWord) atTop
        (nhds (V - (((Real.eulerMascheroniConstant:ℂ)/6 +
          ∑' k, strideCorrection 1 k)/60) • topWord)) := by
  obtain ⟨V,hV⟩ := correctedProduct_converges (s := 1/5) (by norm_num)
  refine ⟨V,hV,?_⟩
  have hp := (tendsto_stride_sum_sub_log.div_const 60).smul_const topWord
  convert hV.sub hp using 1
  funext N
  rw [DeletionJointProduct.sourceProduct_six_mul]
  change orderedProduct (actualBlock (1/5)) N + _ = _
  rw [actualProduct_decomposition]
  simp only [fifthCoefficient_eq_weight]
  norm_num only [show (5:ℂ)*(1/5) = 1 by norm_num]
  rw [← Finset.sum_div]
  module


/-- A nonconstant logarithmic unit phase cannot converge along the complete source cutoffs. -/
theorem six_nat_cpow_not_convergent {z : ℂ} (hz : z.re = 0) (hz0 : z ≠ 0) :
    ¬ ∃ L : ℂ, Tendsto (fun N : ℕ => (6*(N:ℂ))^z) atTop (nhds L) := by
  rintro ⟨L,hL⟩
  have hnorm : ‖L‖ = 1 := by
    apply tendsto_nhds_unique hL.norm
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [show 6*(N:ℂ) = ((6*N:ℕ):ℂ) by push_cast; rfl,
      Complex.norm_natCast_cpow_of_pos (by omega : 0 < 6*N), hz, Real.rpow_zero]
  have hL0 : L ≠ 0 := by intro h; simp [h] at hnorm
  have hp (p : ℕ) (hp : 1 ≤ p) : (p:ℂ)^z = 1 := by
    have hd : Tendsto (fun N : ℕ => p*N) atTop atTop := by
      apply tendsto_atTop_mono (f := fun N : ℕ => N) _ tendsto_id
      intro N
      simpa using Nat.mul_le_mul_right N hp
    have he (N : ℕ) : (6*((p*N:ℕ):ℂ))^z = (p:ℂ)^z * (6*(N:ℂ))^z := by
      have h := Complex.natCast_mul_natCast_cpow p (6*N) z
      push_cast at h ⊢
      convert h using 1
      congr 1
      ring
    have ht : Tendsto (fun N : ℕ => (p:ℂ)^z * (6*(N:ℂ))^z) atTop (nhds L) := by
      simpa only [Function.comp_def, he] using hL.comp hd
    have hh := tendsto_nhds_unique (hL.const_mul ((p:ℂ)^z)) ht
    apply mul_right_cancel₀ hL0
    simpa only [one_mul] using hh
  have hphase (p : ℕ) (hp' : 1 ≤ p) :
      HTGeometry.phaseClockValue (Real.log p) z.im = 1 := by
    have hn : (p:ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    have he : z = (z.im:ℂ)*Complex.I := by
      apply Complex.ext <;> simp [hz]
    have hh := hp p hp'
    rw [Complex.cpow_def_of_ne_zero hn, ← Complex.natCast_log, he] at hh
    simpa only [HTGeometry.phaseClockValue, Complex.ofReal_mul, mul_assoc] using hh
  have ht : z.im = 0 := primeLogPhaseClockPair_two_three_injective (by
    change (HTGeometry.phaseClockValue (Real.log (2:ℕ)) z.im,
      HTGeometry.phaseClockValue (Real.log (3:ℕ)) z.im) = _
    rw [hphase 2 (by omega), hphase 3 (by omega)]
    simp [primeLogPhaseClockPair, HTGeometry.phaseClockPair, HTGeometry.phaseClockValue])
  apply hz0
  exact Complex.ext (by simpa using hz) (by simpa using ht)

private def phaseReadout : A →ₗ[ℂ] ℂ where
  toFun M := M 0 5
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Oscillatory boundary parameters fail to converge, even though their power term is bounded. -/
theorem sourceProduct_not_convergent_on_complex_boundary {s : ℂ}
    (hs : s.re = (1:ℝ)/5) (hs1 : 5*s ≠ 1) :
    ¬ ∃ U : A, Tendsto
      (orderedProduct (DeletionJointProduct.sourceFactor generatorX generatorY s))
      atTop (nhds U) := by
  rintro ⟨U,hU⟩
  obtain ⟨V,_,hV⟩ := sourceProduct_power_asymptotic (by linarith) hs1
  have hP := hU.comp (DeletionJointProduct.stride_tendsto 0)
  simp only [Function.comp_def, Nat.add_zero] at hP
  have hc : Continuous phaseReadout := phaseReadout.continuous_of_finiteDimensional
  have ht := ((hc.tendsto _).comp (hV.sub hP)).const_mul (360*(1-5*s))
  have hs0 : 1-5*s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have he (N : ℕ) : (360*(1-5*s)) * phaseReadout
      ((orderedProduct (DeletionJointProduct.sourceFactor generatorX generatorY s) (6*N) +
        ((6*(N:ℂ))^(1-5*s)/(360*(1-5*s))) • topWord) -
      orderedProduct (DeletionJointProduct.sourceFactor generatorX generatorY s) (6*N)) =
      (6*(N:ℂ))^(1-5*s) := by
    simp only [add_sub_cancel_left, phaseReadout, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.smul_apply, smul_eq_mul, topWord_entry, mul_one]
    field_simp
  simp only [Function.comp_def, he] at ht
  apply six_nat_cpow_not_convergent (z := 1-5*s) (by simp [hs]) hs0
  exact ⟨_,ht⟩

/-- Full positive-half-plane convergence classification for the fixed literal six-coordinate source. -/
theorem positive_halfPlane_convergence_iff (s : {z : ℂ // 0 < z.re}) :
    (∃ U : A, Tendsto
      (orderedProduct (DeletionJointProduct.sourceFactor generatorX generatorY s.val))
      atTop (nhds U)) ↔ (1:ℝ)/5 < s.val.re := by
  constructor
  · intro h
    by_contra hn
    have hle := le_of_not_gt hn
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact sourceProduct_not_convergent_of_re_lt s.property hlt h
    · by_cases h1 : 5*s.val = 1
      · have hs : s.val = ((1/5:ℝ):ℂ) := by push_cast; linear_combination h1/5
        rw [hs] at h
        exact oneFifth_sourceProduct_not_convergent h
      · exact sourceProduct_not_convergent_on_complex_boundary heq h1 h
  · intro hs
    obtain ⟨U,_,hU⟩ := DeletionJointProduct.sourceProduct_converges_to_unit
      generatorX generatorY hs
    exact ⟨U,hU⟩

end
end RHTower.DeletionJointSharpness
