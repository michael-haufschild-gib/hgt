import GaloisForLFunctions.RHTower.SoninPrimePolarGroundNuclear
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Faithful native ground recovery through an actual Fourier column

The exact dilation/parity transfer of cutoff monomials identifies a narrow
constant-input Fourier column with a norm-convergent operator series whose
constant term is the identity. A sufficiently narrow physical input makes
this series invertible. It commutes with every original prime–polar source,
so one fixed bounded map recovers every native ground tail from the square
time-band operator. Genuine nuclear admission therefore cannot hide a
non-admitted ground source. Arithmetic ground cancellation remains open.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RHTower
attribute [local instance] Measure.Subtype.measureSpace

private theorem parity_zero : soninParityMultiplier 0 = 1 := by
  simp only [soninParityMultiplier, pow_zero, one_smul]
  abel

private def groundDegreeTransport (n : ℕ) : SoninL2 →L[ℂ] SoninL2 :=
  soninParityMultiplier n ∘L soninMonomialTransfer n

private theorem groundDegreeTransport_zero : groundDegreeTransport 0 = 1 := by
  simp only [groundDegreeTransport, parity_zero, soninMonomialTransfer,
    Nat.cast_zero, zero_smul, sub_zero]
  ext f
  rfl

private theorem norm_groundDegreeTransport_le (n : ℕ) : ‖groundDegreeTransport n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖soninParityMultiplier n (soninMonomialTransfer n f)‖ ≤ 1*‖f‖
  rw [norm_soninParityMultiplier, one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := soninMonomialTransfer_energy n f
  have hp : 0 ≤ (n:ℝ)*((n:ℝ)+1)*
      ‖soninDilationResolvent ((n:ℝ)+1/2) (by positivity) f‖^2 := by positivity
  linarith

private def unitIntervalMoment (n : ℕ) : ℂ :=
  (1+(-1:ℂ)^n) / (2*((n+1:ℕ):ℂ))

private theorem unitIntervalMoment_zero : unitIntervalMoment 0 = 1 := by
  simp [unitIntervalMoment]

private theorem norm_unitIntervalMoment_le (n : ℕ) : ‖unitIntervalMoment n‖ ≤ 1 := by
  rw [unitIntervalMoment, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
  apply (div_le_one (by positivity : (0:ℝ) < 2*((n+1:ℕ):ℝ))).mpr
  have h := norm_add_le (1:ℂ) ((-1:ℂ)^n)
  simp only [norm_one, norm_pow, norm_neg, one_pow] at h
  have hn : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
  linarith

private def groundColumnTerm (z : ℂ) (n : ℕ) : SoninL2 →L[ℂ] SoninL2 :=
  ((n.factorial:ℂ)⁻¹ * z^n * unitIntervalMoment n) • groundDegreeTransport n

private theorem groundColumnTerm_zero (z : ℂ) : groundColumnTerm z 0 = 1 := by
  simp [groundColumnTerm, unitIntervalMoment_zero, groundDegreeTransport_zero]

private theorem norm_groundColumnTerm_le (z : ℂ) (n : ℕ) :
    ‖groundColumnTerm z n‖ ≤ ‖z‖^n := by
  have hf : ‖(n.factorial:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    have hn : (1:ℝ) ≤ (n.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos n
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hn
  rw [groundColumnTerm, norm_smul, norm_mul, norm_mul, norm_pow]
  calc
    _ ≤ (1 * ‖z‖^n * 1) * 1 := by
      gcongr
      · exact norm_unitIntervalMoment_le n
      · exact norm_groundDegreeTransport_le n
    _ = _ := by ring

private theorem groundColumnTerm_summable (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (groundColumnTerm z) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_groundColumnTerm_le z)
    (summable_geometric_of_lt_one (norm_nonneg z) hz)

/-- Dilation and parity transport of the normalized constant Fourier column. -/
def soninGroundColumnOperator (z : ℂ) : SoninL2 →L[ℂ] SoninL2 :=
  ∑' n, groundColumnTerm z n

private theorem norm_groundColumnOperator_sub_one (z : ℂ) (hz : ‖z‖ < 1) :
    ‖soninGroundColumnOperator z - 1‖ ≤ ‖z‖/(1-‖z‖) := by
  have h := (groundColumnTerm_summable z hz).tsum_eq_zero_add
  have he : soninGroundColumnOperator z - 1 = ∑' n, groundColumnTerm z (n+1) := by
    rw [soninGroundColumnOperator, h, groundColumnTerm_zero]
    abel
  rw [he]
  have hg : HasSum (fun n : ℕ => ‖z‖^(n+1)) (‖z‖/(1-‖z‖)) := by
    simpa only [pow_succ, div_eq_mul_inv, mul_comm] using
      (hasSum_geometric_of_lt_one (norm_nonneg z) hz).mul_right ‖z‖
  exact tsum_of_norm_bounded hg (fun n => norm_groundColumnTerm_le z (n+1))

/-- An actual small Fourier probe has an invertible full physical transport. -/
theorem isUnit_soninGroundColumnOperator (z : ℂ) (hz : ‖z‖ < 1/2) :
    IsUnit (soninGroundColumnOperator z) := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hnorm : ‖soninGroundColumnOperator z - 1‖ < 1 :=
    (norm_groundColumnOperator_sub_one z hz1).trans_lt
      ((div_lt_one (by linarith : 0 < 1-‖z‖)).mpr (by linarith))
  have h := isUnit_one_sub_of_norm_lt_one (x := 1-soninGroundColumnOperator z)
    (by rwa [norm_sub_rev])
  simpa only [sub_sub_cancel] using h


private theorem cutoffMonomial_real_smul (r : ℝ) (f : SoninL2) :
    r • f = (r:ℂ) • f := by
  simpa only [one_smul, Complex.real_smul, mul_one] using (smul_assoc r (1:ℂ) f).symm

private theorem monomial_pairing_ground (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    (complexMulBilinear.lpPairing
      (volume : Measure (ClosedInterval (-b) b)) 2 2
      (ContinuousMap.toLp 2 volume ℂ (intervalMonomialContinuous (-b) b n)))
      (restrictToClosedInterval (-b) b (soninCutoffMonomial b 0)) =
        2*(b:ℂ)^(n+1)*unitIntervalMoment n := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  have hmp : MeasurePreserving ((↑) : ClosedInterval (-b) b → ℝ)
      (volume : Measure (ClosedInterval (-b) b))
      ((volume : Measure ℝ).restrict (Icc (-b) b)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hground := hmp.quasiMeasurePreserving.ae
    ((soninCutoffMonomial_ae b 0).restrict)
  have he : (∫ y : ClosedInterval (-b) b,
      complexMulBilinear
        ((ContinuousMap.toLp 2 volume ℂ (intervalMonomialContinuous (-b) b n)) y)
        ((restrictToClosedInterval (-b) b (soninCutoffMonomial b 0)) y)) =
      ∫ y : ClosedInterval (-b) b, ((y:ℝ):ℂ)^n := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := (2:ENNReal)) (𝕜 := ℂ)
      (volume : Measure (ClosedInterval (-b) b)) (intervalMonomialContinuous (-b) b n),
      restrictToClosedInterval_coeFn (-b) b (soninCutoffMonomial b 0), hground]
      with y hv hr hg
    rw [hv, hr, hg, Set.indicator_of_mem (show (y:ℝ) ∈ centralInterval b from y.property)]
    change ((y:ℝ):ℂ)^n * ((y:ℝ):ℂ)^0 = _
    rw [pow_zero, mul_one]
  rw [he, integral_subtype measurableSet_Icc (fun y : ℝ => (y:ℂ)^n)]
  simp_rw [← Complex.ofReal_pow]
  rw [integral_complex_ofReal, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_self hb), integral_pow]
  unfold unitIntervalMoment
  push_cast
  rw [neg_pow, pow_succ]
  have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp [hn]
  ring

private theorem groundColumn_fourier_term (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (n : ℕ) :
    fullTimeBandFourierTaylorTerm (-a) a (-b) b (neg_le_self ha) n
      (soninCutoffMonomial b 0) =
    (2*(b:ℂ)) • groundColumnTerm
      (((-(2*Real.pi):ℝ):ℂ)*Complex.I*(a:ℂ)*(b:ℂ)) n
      (soninCutoffMonomial a 0) := by
  rw [fullTimeBandFourierTaylorTerm, fourierPhaseTaylorTerm_eq_tensor,
    fullRectangleKernelOperatorMap_tensor_apply,
    fullFourierTaylorOutput_eq_cutoffMonomial a ha n]
  simp only [ContinuousLinearMap.comp_apply]
  change _ • (_ • soninCutoffMonomial a n) = _
  rw [monomial_pairing_ground b hb n, soninMonomialTransfer_cutoff a ha n,
    cutoffMonomial_real_smul]
  simp only [groundColumnTerm, groundDegreeTransport, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, smul_smul, Complex.ofReal_pow]
  congr 1
  rw [mul_pow, mul_pow, mul_pow, pow_succ]
  ring

/-- The actual rectangular Fourier column is the ground transport series. -/
theorem soninGroundColumnOperator_fourier (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hz : ‖(((-(2*Real.pi):ℝ):ℂ)*Complex.I*(a:ℂ)*(b:ℂ))‖ < 1) :
    fullTimeBandFourier (-a) a (-b) b (neg_le_self ha) (soninCutoffMonomial b 0) =
      (2*(b:ℂ)) • soninGroundColumnOperator
        (((-(2*Real.pi):ℝ):ℂ)*Complex.I*(a:ℂ)*(b:ℂ)) (soninCutoffMonomial a 0) := by
  have hf := (ContinuousLinearMap.apply ℂ SoninL2 (soninCutoffMonomial b 0)).hasSum
    (hasSum_fullTimeBandFourierTaylorTerm (-a) a (-b) b (neg_le_self ha))
  have hg := ((ContinuousLinearMap.apply ℂ SoninL2 (soninCutoffMonomial a 0)).hasSum
    (groundColumnTerm_summable _ hz).hasSum).const_smul (2*(b:ℂ))
  apply HasSum.unique hf
  exact hg.congr_fun (fun n => groundColumn_fourier_term a b ha hb n)

private theorem groundDegreeTransport_dilation (n : ℕ) (t : ℝ) (f : SoninL2) :
    groundDegreeTransport n (rayDilate (Real.exp t) f) =
      rayDilate (Real.exp t) (groundDegreeTransport n f) := by
  change soninParityMultiplier n (soninMonomialTransfer n (rayDilate (Real.exp t) f)) = _
  rw [soninMonomialTransfer_dilation]
  simp only [rayDilate_of_pos (Real.exp_pos t)]
  exact soninParityMultiplier_dilation n _ (Real.exp_pos t) _

private theorem groundColumnOperator_dilation (z : ℂ) (hz : ‖z‖ < 1)
    (t : ℝ) (f : SoninL2) :
    soninGroundColumnOperator z (rayDilate (Real.exp t) f) =
      rayDilate (Real.exp t) (soninGroundColumnOperator z f) := by
  have h := groundColumnTerm_summable z hz
  have hleft := (ContinuousLinearMap.apply ℂ SoninL2 (rayDilate (Real.exp t) f)).hasSum h.hasSum
  have hright := (dilationCLM (Real.exp t) (Real.exp_pos t)).hasSum
    ((ContinuousLinearMap.apply ℂ SoninL2 f).hasSum h.hasSum)
  apply HasSum.unique hleft
  simp only [rayDilate_of_pos (Real.exp_pos t)]
  apply hright.congr_fun
  intro n
  change groundColumnTerm z n (dilationCLM (Real.exp t) (Real.exp_pos t) f) =
    dilationCLM (Real.exp t) (Real.exp_pos t) (groundColumnTerm z n f)
  simp only [groundColumnTerm, _root_.smul_apply, map_smul]
  apply congrArg _
  simpa only [rayDilate_of_pos (Real.exp_pos t), dilationCLM_apply] using groundDegreeTransport_dilation n t f

private theorem groundColumnOperator_native (z : ℂ) (hz : ‖z‖ < 1)
    (P Q : Finset Nat.Primes) (c R S : ℝ) (hc : 0 < c) (f : SoninL2) :
    soninGroundColumnOperator z (soninPrimePolarSymmetricTail P Q c R S hc f) =
      soninPrimePolarSymmetricTail P Q c R S hc (soninGroundColumnOperator z f) := by
  simp only [soninPrimePolarSymmetricTail, _root_.sub_apply,
    _root_.add_apply, map_sub, map_add]
  rw [soninPrimePolarSourceOperator_commutes _ (groundColumnOperator_dilation z hz),
    soninPrimePolarSourceOperator_commutes _ (groundColumnOperator_dilation z hz),
    soninPrimePolarSourceOperator_commutes _ (groundColumnOperator_dilation z hz),
    soninPrimePolarSourceOperator_commutes _ (groundColumnOperator_dilation z hz)]

private theorem cutoff_ground_of_le (a b : ℝ) (hba : b ≤ a) :
    indicatorCutoff (Icc (-a) a) measurableSet_Icc (soninCutoffMonomial b 0) =
      soninCutoffMonomial b 0 := by
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (Icc (-a) a) measurableSet_Icc (soninCutoffMonomial b 0),
    soninCutoffMonomial_ae b 0] with x hc hg
  rw [hc]
  by_cases hx : x ∈ Icc (-a) a
  · rw [Set.indicator_of_mem hx]
  · have hxb : x ∉ centralInterval b := by
      intro h
      apply hx
      exact ⟨le_trans (neg_le_neg hba) h.1, le_trans h.2 hba⟩
    rw [Set.indicator_of_notMem hx, hg, Set.indicator_of_notMem hxb]

private theorem square_fourier_ground (a b : ℝ) (ha : 0 ≤ a) (hba : b ≤ a) :
    fullTimeBandFourier (-a) a (-a) a (neg_le_self ha) (soninCutoffMonomial b 0) =
      fullTimeBandFourier (-a) a (-b) b (neg_le_self ha) (soninCutoffMonomial b 0) := by
  rw [fullTimeBandFourier_eq_cutoffFourierCutoff,
    fullTimeBandFourier_eq_cutoffFourierCutoff]
  simp only [cutoffFourierCutoff, ContinuousLinearMap.comp_apply]
  rw [cutoff_ground_of_le a b hba, cutoff_ground_of_le b b le_rfl]

private theorem exists_narrow_ground_probe (a : ℝ) (ha : 0 < a) :
    ∃ b : ℝ, 0 < b ∧ b ≤ a ∧
      ‖(((-(2*Real.pi):ℝ):ℂ)*Complex.I*(a:ℂ)*(b:ℂ))‖ < 1/2 := by
  obtain ⟨b, hb, hba⟩ := exists_between
    (lt_min ha (one_div_pos.mpr (by positivity : 0 < 4*Real.pi*a)))
  refine ⟨b, hb, (lt_min_iff.mp hba).1.le, ?_⟩
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 4*Real.pi*a)).mp
    (lt_min_iff.mp hba).2
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    Complex.norm_I, mul_one, abs_of_pos ha, abs_of_pos hb,
    abs_of_pos (by positivity : 0 < 2*Real.pi)]
  nlinarith

/-- A fixed actual square Fourier column faithfully recovers every original
native symmetric prime–polar ground tail, through one bounded physical map. -/
theorem soninPrimePolar_ground_recovery (a : ℝ) (ha : 0 < a) :
    ∃ b : ℝ, 0 < b ∧ b ≤ a ∧ ∃ V : SoninL2 →L[ℂ] SoninL2,
      ∀ (P Q : Finset Nat.Primes) (c R S : ℝ) (hc : 0 < c),
        V (soninPrimePolarSymmetricTail P Q c R S hc
          (fullTimeBandFourier (-a) a (-a) a (neg_le_self ha.le)
            (soninCutoffMonomial b 0))) =
        soninPrimePolarSymmetricTail P Q c R S hc (soninCutoffMonomial a 0) := by
  obtain ⟨b, hb, hba, hz⟩ := exists_narrow_ground_probe a ha
  let z : ℂ := (((-(2*Real.pi):ℝ):ℂ)*Complex.I*(a:ℂ)*(b:ℂ))
  let A := soninGroundColumnOperator z
  let V : SoninL2 →L[ℂ] SoninL2 := (2*(b:ℂ))⁻¹ • Ring.inverse A
  refine ⟨b, hb, hba, V, ?_⟩
  intro P Q c R S hc
  have hunit : IsUnit A := isUnit_soninGroundColumnOperator z hz
  have hz1 : ‖z‖ < 1 := by change ‖z‖ < 1/2 at hz; linarith
  have hcol := soninGroundColumnOperator_fourier a b ha.le hb.le hz1
  rw [square_fourier_ground a b ha.le hba, hcol, map_smul,
    ← groundColumnOperator_native z hz1 P Q c R S hc]
  change (2*(b:ℂ))⁻¹ • (Ring.inverse A ((2*(b:ℂ)) • A _)) = _
  rw [map_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (ne_of_gt (mul_pos (by norm_num : (0:ℝ)<2) hb))),
    one_smul]
  exact congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T
    (soninPrimePolarSymmetricTail P Q c R S hc (soninCutoffMonomial a 0)))
    (Ring.inverse_mul_cancel A hunit)

/-- The genuine nuclear tail controls its ground column as well. Together
with `soninPrimePolar_timeBand_ground_nuclear`, this gives equivalence of
native ground and square time-band nuclear admission, with fixed constants. -/
theorem soninPrimePolar_ground_le_timeBand_nuclear (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q : Finset Nat.Primes) (c R S : ℝ) (hc : 0 < c),
      ‖soninPrimePolarSymmetricTail P Q c R S hc (soninCutoffMonomial a 0)‖ ≤
        C * ‖soninPrimePolarTimeBandTail a (-a) a ha P Q c R S hc‖ := by
  obtain ⟨b, hb, hba, V, hV⟩ := soninPrimePolar_ground_recovery a ha
  refine ⟨1+‖V‖*‖soninCutoffMonomial b 0‖, by positivity, ?_⟩
  intro P Q c R S hc
  let T := soninPrimePolarTimeBandTail a (-a) a ha P Q c R S hc
  let f := soninCutoffMonomial b 0
  calc
    _ = ‖V ((T : SoninL2 →L[ℂ] SoninL2) f)‖ := congrArg norm (hV P Q c R S hc).symm
    _ ≤ ‖V‖ * (‖(T : SoninL2 →L[ℂ] SoninL2)‖*‖f‖) :=
      (V.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((T : SoninL2 →L[ℂ] SoninL2).le_opNorm f) (norm_nonneg V))
    _ ≤ ‖V‖ * (‖T‖*‖f‖) := by
      gcongr
      exact T.norm_coe_le
    _ ≤ (1+‖V‖*‖f‖)*‖T‖ := by nlinarith [norm_nonneg T]

end RHTower
