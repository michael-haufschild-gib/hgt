import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.GaussianDualArithmeticBound
import GaloisForLFunctions.HTGeometry.GaussianThetaTail
import GaloisForLFunctions.LatticeSectionTheory.TheKunnethRiemannRoch

/-!
# Gaussian arithmetic height uniformly in the conductor

An explicit logarithmic decay schedule controls the actual finite Gaussian
height error simultaneously for every arithmetic quotient class. Dual integer
rounding and Poisson summation remove the conductor-sized error term.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open ArithmeticDegenerationTheory HTGeometry.IntegerLatticePoisson

private theorem divisorScalarTheta_sub_one_le {a : ℝ} (ha : Real.pi ≤ a) :
    divisorScalarTheta a - 1 ≤ 4 * Real.exp (-a) := by
  have he : divisorScalarTheta a = ArithmeticOrientationGeometry.thetaSum (a/Real.pi) := by
    unfold divisorScalarTheta ArithmeticOrientationGeometry.thetaSum
    apply tsum_congr
    intro z
    congr 1
    field_simp
  have hu : 1 ≤ a/Real.pi := (le_div_iff₀ Real.pi_pos).mpr (by simpa using ha)
  have h := LatticeSectionTheory.thetaSum_sub_one_le hu
  rw [← he] at h
  have hx : -Real.pi * (a/Real.pi) = -a := by field_simp
  simpa only [hx] using h

private theorem pow_mul_one_sub_le_one {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    (1+x)^d * (1-(d : ℝ)*x) ≤ 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc
      _ = (1+x)^d * (1-(d : ℝ)*x) - ((d : ℝ)+1)*x^2*(1+x)^d := by
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ (1+x)^d * (1-(d : ℝ)*x) := sub_le_self _ (by positivity)
      _ ≤ 1 := ih

private theorem pow_sub_one_le_two_mul {x : ℝ} (hx : 0 ≤ x) (d : ℕ)
    (hsmall : (d : ℝ)*x ≤ 1/2) : (1+x)^d - 1 ≤ 2*(d : ℝ)*x := by
  have hu : 0 ≤ (d : ℝ)*x := mul_nonneg (Nat.cast_nonneg d) hx
  have hp : 0 < 1-(d : ℝ)*x := by linarith only [hsmall]
  apply le_of_mul_le_mul_right _ hp
  calc
    ((1+x)^d-1)*(1-(d : ℝ)*x) =
        (1+x)^d*(1-(d : ℝ)*x) - (1-(d : ℝ)*x) := by ring
    _ ≤ 1-(1-(d : ℝ)*x) := sub_le_sub_right (pow_mul_one_sub_le_one hx d) _
    _ ≤ (2*(d : ℝ)*x)*(1-(d : ℝ)*x) := by
      have h := mul_le_mul_of_nonneg_left hsmall hu
      nlinarith only [h]

/-- A uniform exponential tail bound for the actual dual divisor lattice. -/
theorem divisorGaussianDual_tail_bound (N : ℕ) (hN : 1 ≤ N) {a : ℝ}
    (ha : Real.pi ≤ a) (hsmall : 4*((N : ℝ)+1)*Real.exp (-a) ≤ 1/2) :
    gaussianLatticeSum (inverseAdjointEquiv (divisorGaussianLattice N hN)) (2*a) - 1 ≤
      8*((N : ℝ)+1)*Real.exp (-a) := by
  have ha0 := Real.pi_pos.trans_le ha
  have hθ := divisorScalarTheta_sub_one_le ha
  have hθ0 : 0 ≤ divisorScalarTheta a := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  have hp := pow_le_pow_left₀ hθ0 (show divisorScalarTheta a ≤ 1+4*Real.exp (-a) by
    linarith only [hθ]) (N+1)
  have hs : ((N+1 : ℕ) : ℝ)*(4*Real.exp (-a)) ≤ 1/2 := by
    push_cast
    nlinarith only [hsmall]
  have hpow := pow_sub_one_le_two_mul (by positivity : 0 ≤ 4*Real.exp (-a)) (N+1) hs
  have hb := divisorGaussianDual_theta_le N hN (mul_pos (by norm_num : (0 : ℝ)<2) ha0)
  rw [show 2*a/2=a by ring] at hb
  push_cast at hpow
  linarith only [hb, hp, hpow]

/-- A positive scalar Gaussian contains its unit zero term. -/
private theorem divisorScalarTheta_pos {a : ℝ} (ha : 0 < a) : 0 < divisorScalarTheta a := by
  have hs : Summable (fun z : ℤ => Real.exp (-a*(z : ℝ)^2)) := by
    simpa only [pow_zero, one_mul] using
      summable_one_add_natAbs_pow_mul_exp_neg_int_sq 0 ha
  have h := hs.le_tsum 0 (fun _ _ => (Real.exp_pos _).le)
  have h1 : 1 ≤ divisorScalarTheta a := by simpa [divisorScalarTheta] using h
  exact zero_lt_one.trans_le h1

/-- The free normal count is the scalar Gaussian at its actual normal metric. -/
theorem divisorNormalTheta_eq_scalar (N : ℕ) (t : ℝ) :
    divisorNormalTheta N t = divisorScalarTheta (t/divisorSquarefreeCount N) := by
  unfold divisorNormalTheta divisorScalarTheta
  apply tsum_congr
  intro z
  unfold divisorNormalGaussianWeight
  congr 1
  ring

/-- Removing the normal energy leaves exactly a ratio of two full-lattice counts. -/
theorem divisorSectionLogHeight_error_eq_log_ratio (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {t : ℝ} (ht : 0 < t) :
    divisorSectionLogHeight N hN c t -
        t*(divisorSectionChargeEquiv N hN c : ℝ)^2/divisorSquarefreeCount N =
      Real.log (gaussianAffineLatticeSum (divisorGaussianLattice N hN) t 0) -
        Real.log (gaussianAffineLatticeSum (divisorGaussianLattice N hN) t
          (divisorGaussianShift N hN c)) := by
  have hq : (0 : ℝ) < divisorSquarefreeCount N := by
    exact_mod_cast divisorSquarefreeCount_pos N hN
  have hn : 0 < divisorNormalTheta N t := by
    rw [divisorNormalTheta_eq_scalar]
    exact divisorScalarTheta_pos (div_pos ht hq)
  have hl (d : DivisorSectionClass N hN) :
      Real.log (gaussianAffineLatticeSum (divisorGaussianLattice N hN) t
        (divisorGaussianShift N hN d)) = Real.log (divisorNormalTheta N t) +
          t*(divisorSectionChargeEquiv N hN d : ℝ)^2/divisorSquarefreeCount N +
            Real.log (divisorSectionTheta N hN d t) := by
    rw [gaussianAffineLatticeSum, divisorGaussianLattice_section_factor N hN d ht,
      Real.log_mul (mul_pos hn (Real.exp_pos _)).ne' (divisorSectionTheta_pos N hN d ht).ne',
      Real.log_mul hn.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hz : divisorGaussianShift N hN 0 = 0 := by simp [divisorGaussianShift]
  rw [← hz, hl 0, hl c]
  simp only [_root_.map_zero, Int.cast_zero, zero_pow (by omega : 2 ≠ 0), mul_zero,
    zero_div, add_zero, divisorSectionLogHeight]
  ring

/-- Exponential finite-count error, uniform over all arithmetic classes and conductors. -/
theorem divisorSectionLogHeight_exponential_error (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) {a : ℝ} (ha : Real.pi ≤ a)
    (hsmall : 8*((N : ℝ)+1)*Real.exp (-a) ≤ 1/2) :
    divisorSectionLogHeight N hN c (Real.pi^2/(2*a)) -
        (Real.pi^2/(2*a))*(divisorSectionChargeEquiv N hN c : ℝ)^2/divisorSquarefreeCount N ≤
      32*((N : ℝ)+1)*Real.exp (-a) := by
  have ha0 := Real.pi_pos.trans_le ha
  have ht : 0 < Real.pi^2/(2*a) := div_pos (sq_pos_of_pos Real.pi_pos) (by positivity)
  have hd := divisorGaussianDual_tail_bound N hN ha (by linarith only [hsmall])
  have he : Real.pi^2/(Real.pi^2/(2*a)) = 2*a := by field_simp [Real.pi_ne_zero, ha0.ne']
  have h := gaussianAffineLatticeSum_log_ratio_le_four (divisorGaussianLattice N hN) ht
    (by positivity : 0 ≤ 8*((N : ℝ)+1)*Real.exp (-a)) hsmall
    (by rw [he]; linarith only [hd]) (divisorGaussianShift N hN c)
  rw [← divisorSectionLogHeight_error_eq_log_ratio N hN c ht] at h
  linarith only [h]

/-- The dual decay schedule compensates for the growing number of integer coordinates. -/
def divisorUniformDualRate (N : ℕ) : ℝ := Real.pi + 2*Real.log (4*((N : ℝ)+1))

/-- The corresponding rate for the actual arithmetic Gaussian count. -/
def divisorUniformGaussianRate (N : ℕ) : ℝ := Real.pi^2/(2*divisorUniformDualRate N)

theorem divisorUniformDualRate_ge_pi (N : ℕ) : Real.pi ≤ divisorUniformDualRate N := by
  have h : 1 ≤ 4*((N : ℝ)+1) := by nlinarith only [Nat.cast_nonneg (α := ℝ) N]
  have hl := Real.log_nonneg h
  unfold divisorUniformDualRate
  linarith only [hl]

theorem divisorUniformGaussianRate_pos (N : ℕ) : 0 < divisorUniformGaussianRate N := by
  have ha := Real.pi_pos.trans_le (divisorUniformDualRate_ge_pi N)
  exact div_pos (sq_pos_of_pos Real.pi_pos) (mul_pos (by norm_num) ha)

private theorem divisorUniformDualRate_exp_identity (N : ℕ) :
    (4*((N : ℝ)+1))^2 * Real.exp (-divisorUniformDualRate N) = Real.exp (-Real.pi) := by
  have hu : 0 < 4*((N : ℝ)+1) := by positivity
  have hx : -divisorUniformDualRate N = -Real.pi -
      (Real.log (4*((N : ℝ)+1)) + Real.log (4*((N : ℝ)+1))) := by
    unfold divisorUniformDualRate
    ring
  rw [hx, Real.exp_sub, Real.exp_add, Real.exp_log hu]
  field_simp [hu.ne']

private theorem divisorUniformDualRate_budget (N : ℕ) :
    16*((N : ℝ)+1)^2 * Real.exp (-divisorUniformDualRate N) ≤ 1 := by
  have h := divisorUniformDualRate_exp_identity N
  have he : Real.exp (-Real.pi) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr Real.pi_pos.le)
  nlinarith only [h, he]

private theorem divisorUniformDualRate_small (N : ℕ) :
    8*((N : ℝ)+1)*Real.exp (-divisorUniformDualRate N) ≤ 1/2 := by
  have hn := Nat.cast_nonneg (α := ℝ) N
  have he := (Real.exp_pos (-divisorUniformDualRate N)).le
  have hx : (N : ℝ)+1 ≤ ((N : ℝ)+1)^2 := by nlinarith only [hn, sq_nonneg (N : ℝ)]
  have hmul := mul_le_mul_of_nonneg_right hx he
  have hb := divisorUniformDualRate_budget N
  nlinarith only [hmul, hb]

/-- A single explicit rate gives vanishing height error simultaneously for every quotient class. -/
theorem divisorSectionLogHeight_uniform_error (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    0 ≤ divisorSectionLogHeight N hN c (divisorUniformGaussianRate N) -
        divisorUniformGaussianRate N*(divisorSectionChargeEquiv N hN c : ℝ)^2/
          divisorSquarefreeCount N ∧
    divisorSectionLogHeight N hN c (divisorUniformGaussianRate N) -
        divisorUniformGaussianRate N*(divisorSectionChargeEquiv N hN c : ℝ)^2/
          divisorSquarefreeCount N ≤ 2/((N : ℝ)+1) := by
  refine ⟨(divisorSectionLogHeight_positive_error N hN c
    (divisorUniformGaussianRate_pos N)).1, ?_⟩
  have h := divisorSectionLogHeight_exponential_error N hN c
    (divisorUniformDualRate_ge_pi N) (divisorUniformDualRate_small N)
  refine h.trans ?_
  apply (le_div_iff₀ (by positivity : 0 < (N : ℝ)+1)).mpr
  have hb := divisorUniformDualRate_budget N
  nlinarith only [hb]

/-- The original integer gluing class has the same uniform approximation to its signed displacement. -/
theorem divisorGluingClass_uniform_error (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ divisorSectionLogHeight N hN (divisorGluingClass N hN) (divisorUniformGaussianRate N) -
        divisorUniformGaussianRate N*divisorTransverseDistance N (integerGluingRealColumn N)^2 ∧
    divisorSectionLogHeight N hN (divisorGluingClass N hN) (divisorUniformGaussianRate N) -
        divisorUniformGaussianRate N*divisorTransverseDistance N (integerGluingRealColumn N)^2 ≤
      2/((N : ℝ)+1) := by
  rw [← divisorGluingClass_tateHeight N hN, divisorSectionTateHeight_eq]
  simpa only [mul_div_assoc] using
    divisorSectionLogHeight_uniform_error N hN (divisorGluingClass N hN)

/-- Dividing the actual finite count by its rate approximates the gluing height across conductors. -/
theorem divisorGluingClass_uniform_normalized_error (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ divisorSectionLogHeight N hN (divisorGluingClass N hN) (divisorUniformGaussianRate N) /
        divisorUniformGaussianRate N - divisorTransverseDistance N (integerGluingRealColumn N)^2 ∧
    divisorSectionLogHeight N hN (divisorGluingClass N hN) (divisorUniformGaussianRate N) /
        divisorUniformGaussianRate N - divisorTransverseDistance N (integerGluingRealColumn N)^2 ≤
      4*divisorUniformDualRate N/(Real.pi^2*((N : ℝ)+1)) := by
  have ht := divisorUniformGaussianRate_pos N
  have ha := Real.pi_pos.trans_le (divisorUniformDualRate_ge_pi N)
  have h := divisorGluingClass_uniform_error N hN
  have he :
      divisorSectionLogHeight N hN (divisorGluingClass N hN) (divisorUniformGaussianRate N) /
        divisorUniformGaussianRate N - divisorTransverseDistance N (integerGluingRealColumn N)^2 =
      (divisorSectionLogHeight N hN (divisorGluingClass N hN) (divisorUniformGaussianRate N) -
        divisorUniformGaussianRate N*divisorTransverseDistance N (integerGluingRealColumn N)^2) /
          divisorUniformGaussianRate N := by field_simp [ht.ne']
  rw [he]
  refine ⟨div_nonneg h.1 ht.le, (div_le_div_of_nonneg_right h.2 ht.le).trans_eq ?_⟩
  unfold divisorUniformGaussianRate
  have hd : (N : ℝ)+1 ≠ 0 := ne_of_gt (by positivity)
  field_simp [Real.pi_ne_zero, ha.ne', hd]
  ring

#print axioms divisorGaussianDual_tail_bound
#print axioms divisorNormalTheta_eq_scalar
#print axioms divisorSectionLogHeight_error_eq_log_ratio
#print axioms divisorSectionLogHeight_exponential_error
#print axioms divisorUniformDualRate_ge_pi
#print axioms divisorUniformGaussianRate_pos
#print axioms divisorSectionLogHeight_uniform_error
#print axioms divisorGluingClass_uniform_error
#print axioms divisorGluingClass_uniform_normalized_error

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
