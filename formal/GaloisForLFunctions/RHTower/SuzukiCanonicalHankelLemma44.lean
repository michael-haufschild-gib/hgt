import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelCompressionBridge
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenvalue
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Suzuki (2012), Lemma 4.4

For `omega > 1/2` and `a > 1`, Suzuki's literal finite Hankel section annihilates the inner
interval `L²(0,1/a)`, strictly contracts every nonzero vector, has operator norm strictly below
one, and hence `1 ± H_{omega,a}` are invertible.

The strict step uses the exact compression identity and Lemma 4.3: equality in the projection
contraction would make the global Hankel output supported in `[1/a,a]`, contradicting Suzuki's
compact-output obstruction.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-! ## Part (i): the inner interval is killed -/

/-- Canonical inclusion of a smaller physical interval into a larger one by positive-ray zero
extension followed by restriction. -/
def suzukiPhysicalIntervalInclusion (b a : ℝ) :
    IntervalL2 0 b →L[ℂ] IntervalL2 0 a :=
  suzukiPositiveIntervalRestriction a ∘L
    (suzukiPhysicalIntervalPositiveIsometry b).toContinuousLinearMap

theorem suzukiPhysicalIntervalInclusion_ae (b a : ℝ)
    (f : IntervalL2 0 b) :
    suzukiPhysicalIntervalInclusion b a f =ᵐ[volume]
      fun x : ClosedInterval 0 a =>
        suzukiPhysicalIntervalPositiveL2 f (x : ℝ) :=
  suzukiPositiveIntervalRestriction_value_ae
    (suzukiPhysicalIntervalPositiveL2 f)

/-- **Suzuki (2012), Lemma 4.4(i).**  The literal finite Hankel section kills every source
supported in `(0,1/a)`. -/
theorem suzuki2012_lemma_four_four_i
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a)
    (f : IntervalL2 0 (1 / a)) :
    suzukiCompressedHankelOperator omega a homega
        (suzukiPhysicalIntervalInclusion (1 / a) a f) = 0 := by
  apply Lp.ext
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 a → ℝ)
      (volume : Measure (ClosedInterval 0 a))
      ((volume : Measure ℝ).restrict (Icc 0 a)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hinputWhole := (ae_restrict_iff' measurableSet_Ioi).mp
    (suzukiPhysicalIntervalPositiveL2_ae f)
  have hinputSub := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae hinputWhole)
  have hneSub := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (volume.ae_ne (0 : ℝ)))
  filter_upwards [suzukiCompressedHankelOperator_coeFn omega a homega
      (by linarith) (suzukiPhysicalIntervalInclusion (1 / a) a f),
    Lp.coeFn_zero ℂ 2 (volume : Measure (ClosedInterval 0 a))] with x hout hzero
  rw [hout, hzero]
  have hinclusion := suzukiPhysicalIntervalInclusion_ae (1 / a) a f
  have hintegrand :
      (fun y : ClosedInterval 0 a =>
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiPhysicalIntervalInclusion (1 / a) a f y) =ᵐ[volume]
        fun _ => 0 := by
    filter_upwards [hinclusion, hinputSub, hneSub] with y hinc hinput hne
    rw [hinc]
    have hypos : 0 < (y : ℝ) := lt_of_le_of_ne y.property.1 (Ne.symm hne)
    rw [hinput hypos]
    by_cases hy : (y : ℝ) ≤ 1 / a
    · have hxy : (x : ℝ) * (y : ℝ) ≤ 1 := by
        calc
          (x : ℝ) * (y : ℝ) ≤ a * (1 / a) :=
            mul_le_mul x.property.2 hy hypos.le (by linarith)
          _ = 1 := by field_simp
      rw [suzukiSourceHFinite, if_neg (not_lt_of_ge hxy), zero_mul]
    · have hnot : (y : ℝ) ∉ Icc 0 (1 / a) := fun hyIcc => hy hyIcc.2
      rw [suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem f hnot, mul_zero]
  rw [integral_congr_ae hintegrand]
  simp

/-! ## Part (ii): strict vector contraction -/

theorem norm_suzukiCompressedHankelOperator_apply_le
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 0 < a)
    (f : IntervalL2 0 a) :
    ‖suzukiCompressedHankelOperator omega a homega f‖ ≤ ‖f‖ := by
  rw [← suzukiCanonicalPositiveHankelCompression_eq_compressedHankel homega ha]
  let E := suzukiPhysicalIntervalPositiveIsometry a
  let R := suzukiPositiveIntervalRestriction a
  let H := suzukiCanonicalPositiveHankelUnitary omega
    (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega)
  change ‖R (H (E f))‖ ≤ ‖f‖
  calc
    ‖R (H (E f))‖ ≤ ‖H (E f)‖ :=
      norm_suzukiPositiveIntervalRestriction_le a (H (E f))
    _ = ‖E f‖ := H.norm_map (E f)
    _ = ‖f‖ := E.norm_map f

/-- Equality in the finite-section contraction forces the source to vanish. -/
theorem eq_zero_of_norm_suzukiCompressedHankelOperator_eq
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a)
    {f : IntervalL2 0 a}
    (hnorm : ‖suzukiCompressedHankelOperator omega a homega f‖ = ‖f‖) :
    f = 0 := by
  let E := suzukiPhysicalIntervalPositiveIsometry a
  let R := suzukiPositiveIntervalRestriction a
  let H := suzukiCanonicalPositiveHankelUnitary omega
    (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega)
  let u : SuzukiPositiveL2 := E f
  let v : SuzukiPositiveL2 := H u
  let q : SoninL2 := suzukiPositiveLogUnitary u
  let p : SoninL2 := suzukiPositiveLogUnitary v
  have hcompression : suzukiCompressedHankelOperator omega a homega f = R v := by
    rw [← suzukiCanonicalPositiveHankelCompression_eq_compressedHankel homega (by linarith)]
    rfl
  have hRv : ‖R v‖ = ‖v‖ := by
    calc
      ‖R v‖ = ‖f‖ := by rw [← hnorm, hcompression]
      _ = ‖u‖ := (E.norm_map f).symm
      _ = ‖v‖ := (H.norm_map u).symm
  have hvFixed : E (R v) = v :=
    suzukiPhysicalInterval_extension_restriction_eq_of_norm_eq a v hRv
  have hqUpper : logHalflineCutoff (Real.log a) q = q :=
    logHalflineCutoff_suzukiPhysicalIntervalPositive (by linarith) f
  have hpEq : p = suzukiCanonicalLogHankelUnitary omega
      (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega) q := by
    exact suzukiPositiveLogUnitary_canonicalHankel omega
      (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega) u
  have hpLower : logLowerHalflineCutoff (-Real.log a) p = p := by
    rw [hpEq]
    exact suzukiCanonicalLogHankelUnitary_maps_upper_to_reflected_lower
      homega q hqUpper
  have hpUpper : logHalflineCutoff (Real.log a) p = p := by
    have hfixed := logHalflineCutoff_suzukiPhysicalIntervalPositive
      (a := a) (by linarith) (R v)
    rw [hvFixed] at hfixed
    exact hfixed
  have hpCompact : suzukiCutoff (Real.log a) p = p :=
    suzukiCutoff_eq_self_of_logHalfline_fixed hpUpper hpLower
  have hlogNonneg : 0 ≤ Real.log a := (Real.log_pos ha).le
  have h43 := suzuki2012_lemma_four_three homega hlogNonneg q hqUpper
    (by rw [← hpEq]; exact hpCompact)
  have hqZero : q = 0 := h43.2
  have huZero : u = 0 := by
    apply suzukiPositiveLogUnitary.injective
    simpa only [q, map_zero] using hqZero
  apply E.injective
  simpa only [u, map_zero] using huZero

/-- **Suzuki (2012), Lemma 4.4(ii).**  Every nonzero vector is strictly contracted. -/
theorem suzuki2012_lemma_four_four_ii
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a)
    {f : IntervalL2 0 a} (hf : f ≠ 0) :
    ‖suzukiCompressedHankelOperator omega a homega f‖ < ‖f‖ := by
  apply lt_of_le_of_ne
  · exact norm_suzukiCompressedHankelOperator_apply_le homega (by linarith) f
  · intro heq
    exact hf (eq_zero_of_norm_suzukiCompressedHankelOperator_eq homega ha heq)

/-! ## Part (iii): uniform operator gap and resolvents -/

/-- **Suzuki (2012), Lemma 4.4(iii).** -/
theorem suzuki2012_lemma_four_four_iii
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a) :
    ‖suzukiCompressedHankelOperator omega a homega‖ < 1 := by
  let T := suzukiCompressedHankelOperator omega a homega
  change ‖T‖ < 1
  by_cases hT : T = 0
  · rw [hT, norm_zero]
    exact zero_lt_one
  · have hcpt : IsCompactOperator T :=
      (suzukiCompressedHankelOperator_isHilbertSchmidt omega a homega).isCompactOperator
    have hsym : T.toLinearMap.IsSymmetric :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (suzukiCompressedHankelOperator_isSelfAdjoint omega a homega)
    obtain ⟨μ, x, hμ, hx, heig⟩ :=
      ContinuousLinearMap.exists_unit_eigenvector_norm hcpt hsym hT
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hx
      norm_num at hx
    have hstrict := suzuki2012_lemma_four_four_ii homega ha hx0
    have hTx : ‖T x‖ = |μ| := by
      rw [heig, norm_smul, Complex.norm_real, Real.norm_eq_abs, hx, mul_one]
    rw [hTx, hμ, hx] at hstrict
    exact hstrict

/-- The negative resolvent is invertible. -/
theorem suzuki2012_lemma_four_four_one_sub_isUnit
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a) :
    IsUnit (1 - suzukiCompressedHankelOperator omega a homega) :=
  isUnit_one_sub_of_norm_lt_one
    (suzuki2012_lemma_four_four_iii homega ha)

/-- The positive resolvent is invertible. -/
theorem suzuki2012_lemma_four_four_one_add_isUnit
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a) :
    IsUnit (1 + suzukiCompressedHankelOperator omega a homega) := by
  rw [← sub_neg_eq_add]
  apply isUnit_one_sub_of_norm_lt_one
  rw [norm_neg]
  exact suzuki2012_lemma_four_four_iii homega ha

/-- **Suzuki (2012), Lemma 4.4, exact bundled form.** -/
theorem suzuki2012_lemma_four_four
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a) :
    (∀ f : IntervalL2 0 (1 / a),
      suzukiCompressedHankelOperator omega a homega
          (suzukiPhysicalIntervalInclusion (1 / a) a f) = 0) ∧
    (∀ f : IntervalL2 0 a, f ≠ 0 →
      ‖suzukiCompressedHankelOperator omega a homega f‖ < ‖f‖) ∧
    ‖suzukiCompressedHankelOperator omega a homega‖ < 1 ∧
    IsUnit (1 - suzukiCompressedHankelOperator omega a homega) ∧
    IsUnit (1 + suzukiCompressedHankelOperator omega a homega) := by
  exact ⟨suzuki2012_lemma_four_four_i homega ha,
    fun _ hf => suzuki2012_lemma_four_four_ii homega ha hf,
    suzuki2012_lemma_four_four_iii homega ha,
    suzuki2012_lemma_four_four_one_sub_isUnit homega ha,
    suzuki2012_lemma_four_four_one_add_isUnit homega ha⟩

end RHTower
