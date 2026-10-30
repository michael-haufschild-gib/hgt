import GaloisForLFunctions.CompletedArithmeticForms.HyperbolicClock
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGaussianHankelRH
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The sharp affine-Gamma cone of the nonlinear theta clock

A bounded quadratic Gaussian density identifies the complete signed Hankel cone
of adjacent Gamma moments with its two nonnegative coefficients. The literal
inverse-hyperbolic first-atom clock lies in this cone exactly when its source
shape is at least three. Below that boundary mixed positivity fails although
every individual signed even moment is nonnegative.
-/

noncomputable section

open MeasureTheory Set Matrix Finset
open scoped ENNReal

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

private def clockGaussian (y : ℝ) : ℝ := Real.exp (-(1 / 16) * y ^ 2)

private theorem integrable_pow_mul_clockGaussian (n : ℕ) :
    Integrable (fun y : ℝ => y ^ n * clockGaussian y) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 16) (by norm_num)
    (s := (n : ℝ)) (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith only [hn])
  simpa only [Real.rpow_natCast, clockGaussian] using h

private theorem hasDerivAt_clockGaussian (y : ℝ) :
    HasDerivAt clockGaussian (-(y / 8) * clockGaussian y) y := by
  convert (((hasDerivAt_id y).pow 2).const_mul (-(1 / 16 : ℝ))).exp using 1
  · rfl
  · dsimp only [id, Pi.pow_apply]
    unfold clockGaussian
    ring

private theorem integral_pow_add_two_mul_clockGaussian (n : ℕ) :
    (∫ y : ℝ, y ^ (n + 2) * clockGaussian y) =
      8 * ((n : ℝ) + 1) * ∫ y : ℝ, y ^ n * clockGaussian y := by
  have hu : ∀ y ∈ tsupport (fun y : ℝ => -8 * clockGaussian y),
      HasDerivAt (fun y : ℝ => y ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * y ^ n) y := by
    intro y _
    simpa using hasDerivAt_pow (n + 1) y
  have hv : ∀ y ∈ tsupport (fun y : ℝ => y ^ (n + 1)),
      HasDerivAt (fun y : ℝ => -8 * clockGaussian y) (y * clockGaussian y) y := by
    intro y _
    exact ((hasDerivAt_clockGaussian y).const_mul (-8)).congr_deriv (by ring)
  have h1 : Integrable ((fun y : ℝ => y ^ (n + 1)) * fun y => y * clockGaussian y) :=
    (integrable_pow_mul_clockGaussian (n + 2)).congr
      (Filter.Eventually.of_forall fun y => by simp only [Pi.mul_apply]; ring)
  have h2 : Integrable ((fun y : ℝ => ((n + 1 : ℕ) : ℝ) * y ^ n) *
      fun y => -8 * clockGaussian y) :=
    ((integrable_pow_mul_clockGaussian n).const_mul (-8 * ((n + 1 : ℕ) : ℝ))).congr
      (Filter.Eventually.of_forall fun y => by simp only [Pi.mul_apply]; ring)
  have h3 : Integrable ((fun y : ℝ => y ^ (n + 1)) * fun y => -8 * clockGaussian y) :=
    ((integrable_pow_mul_clockGaussian (n + 1)).const_mul (-8)).congr
      (Filter.Eventually.of_forall fun y => by simp only [Pi.mul_apply]; ring)
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable hu hv h1 h2 h3
  have e1 : (∫ y : ℝ, y ^ (n + 1) * (y * clockGaussian y)) =
      ∫ y : ℝ, y ^ (n + 2) * clockGaussian y := by
    congr 1
    funext y
    ring
  have e2 : (∫ y : ℝ, ((n + 1 : ℕ) : ℝ) * y ^ n * (-8 * clockGaussian y)) =
      -(8 * ((n : ℝ) + 1) * ∫ y : ℝ, y ^ n * clockGaussian y) := by
    rw [← integral_const_mul, ← integral_neg]
    congr 1
    funext y
    push_cast
    ring
  rw [e1, e2, neg_neg] at h
  exact h

private def clockGaussianMass : ℝ := ∫ y : ℝ, clockGaussian y

private theorem clockGaussianMass_pos : 0 < clockGaussianMass := by
  unfold clockGaussianMass clockGaussian
  rw [integral_gaussian]
  positivity

private theorem integral_even_pow_mul_clockGaussian (k : ℕ) :
    (∫ y : ℝ, y ^ (2 * k) * clockGaussian y) = clockGaussianMass * gaussianMoment k := by
  induction k with
  | zero => simp [clockGaussianMass, gaussianMoment]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by omega,
      integral_pow_add_two_mul_clockGaussian, ih]
    simp only [gaussianMoment, pow_succ, gammaShapeMoment_succ]
    push_cast
    ring

private theorem integral_odd_pow_mul_clockGaussian (k : ℕ) :
    (∫ y : ℝ, y ^ (2 * k + 1) * clockGaussian y) = 0 := by
  have h := integral_neg_eq_self (fun y : ℝ => y ^ (2 * k + 1) * clockGaussian y) volume
  have he : (fun y : ℝ => (-y) ^ (2 * k + 1) * clockGaussian (-y)) =
      fun y => -(y ^ (2 * k + 1) * clockGaussian y) := by
    funext y
    have hp : (-y) ^ (2 * k + 1) = -(y ^ (2 * k + 1)) := by
      calc
        _ = ((-y) ^ 2) ^ k * (-y) := by rw [pow_succ, pow_mul]
        _ = -((y ^ 2) ^ k * y) := by rw [neg_sq]; ring
        _ = _ := by rw [← pow_mul y 2 k, pow_succ y (2 * k)]
    simp only [clockGaussian, neg_sq, hp, neg_mul]
  rw [he, integral_neg] at h
  linarith only [h]

/-- The adjacent-Gamma even moments with both signed coefficients visible. -/
def affineGammaMoment (a b : ℝ) (k : ℕ) : ℝ :=
  a * gaussianMoment k + b * gaussianMoment (k + 1)

/-- The bounded density representing the complete odd-zero affine-Gamma sequence. -/
def affineGammaDensity (a b y : ℝ) : ℝ :=
  (a + b * y ^ 2) * Real.exp (-(1 / 32) * y ^ 2)

theorem continuous_affineGammaDensity (a b : ℝ) : Continuous (affineGammaDensity a b) := by
  unfold affineGammaDensity
  fun_prop

theorem abs_affineGammaDensity_le (a b y : ℝ) :
    |affineGammaDensity a b y| ≤ |a| + 32 * |b| := by
  have hexp : Real.exp (-(1 / 32 : ℝ) * y ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg y])
  have hpoly : y ^ 2 * Real.exp (-(1 / 32 : ℝ) * y ^ 2) ≤ 32 := by
    have hbase := Real.add_one_le_exp ((1 / 32 : ℝ) * y ^ 2)
    have hmul := mul_le_mul_of_nonneg_right hbase
      (Real.exp_pos (-(1 / 32 : ℝ) * y ^ 2)).le
    have he : Real.exp ((1 / 32 : ℝ) * y ^ 2) *
        Real.exp (-(1 / 32 : ℝ) * y ^ 2) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1
      ring
    rw [he] at hmul
    nlinarith only [hmul, (Real.exp_pos (-(1 / 32 : ℝ) * y ^ 2)).le]
  calc
    |affineGammaDensity a b y| =
        |a + b * y ^ 2| * Real.exp (-(1 / 32 : ℝ) * y ^ 2) := by
      rw [affineGammaDensity, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ (|a| + |b| * y ^ 2) * Real.exp (-(1 / 32 : ℝ) * y ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have h := _root_.abs_add_le a (b * y ^ 2)
      rw [_root_.abs_mul, abs_of_nonneg (sq_nonneg y)] at h
      exact h
    _ = |a| * Real.exp (-(1 / 32 : ℝ) * y ^ 2) +
        |b| * (y ^ 2 * Real.exp (-(1 / 32 : ℝ) * y ^ 2)) := by ring
    _ ≤ |a| + 32 * |b| := by
      have h1 := mul_le_mul_of_nonneg_left hexp (abs_nonneg a)
      have h2 := mul_le_mul_of_nonneg_left hpoly (abs_nonneg b)
      nlinarith only [h1, h2]

theorem affineGammaDensity_memLp_top (a b tau : ℝ) :
    MemLp (affineGammaDensity a b) ∞ (gaussianWindowMeasure tau) := by
  apply memLp_top_of_bound (continuous_affineGammaDensity a b).aestronglyMeasurable
    (|a| + 32 * |b|)
  exact Filter.Eventually.of_forall fun y => by
    simpa only [Real.norm_eq_abs] using abs_affineGammaDensity_le a b y

private theorem weightedMoment_affineGammaDensity (a b : ℝ) (n : ℕ) :
    weightedMoment (gaussianWindowMeasure (1 / 32)) (affineGammaDensity a b) n =
      clockGaussianMass * evenMomentSequence (affineGammaMoment a b) n := by
  have hpoint (y : ℝ) :
      Real.exp (-(1 / 32) * y ^ 2) * (y ^ n * affineGammaDensity a b y) =
        a * (y ^ n * clockGaussian y) + b * (y ^ (n + 2) * clockGaussian y) := by
    unfold affineGammaDensity clockGaussian
    calc
      _ = y ^ n * (a + b * y ^ 2) *
          (Real.exp (-(1 / 32) * y ^ 2) * Real.exp (-(1 / 32) * y ^ 2)) := by ring
      _ = y ^ n * (a + b * y ^ 2) * Real.exp (-(1 / 16) * y ^ 2) := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ = _ := by ring
  rw [weightedMoment, gaussianWindowMeasure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, hpoint]
  rw [integral_add ((integrable_pow_mul_clockGaussian n).const_mul a)
    ((integrable_pow_mul_clockGaussian (n + 2)).const_mul b),
    integral_const_mul, integral_const_mul]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    rw [show n = 2 * k by omega,
      show 2 * k + 2 = 2 * (k + 1) by omega, evenMomentSequence_even,
      integral_even_pow_mul_clockGaussian, integral_even_pow_mul_clockGaussian]
    unfold affineGammaMoment
    ring
  · obtain ⟨k, hk⟩ := ho
    rw [show n = 2 * k + 1 by omega,
      show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega, evenMomentSequence_odd,
      integral_odd_pow_mul_clockGaussian, integral_odd_pow_mul_clockGaussian]
    ring

private theorem completeHankelCone_const_mul_iff {c : ℝ} (hc : 0 < c) (s : ℕ → ℝ) :
    CompleteHankelCone (fun n => c * s n) ↔ CompleteHankelCone s := by
  have he (N : ℕ) (v : Fin N → ℝ) :
      (∑ i : Fin N, ∑ j : Fin N, v i * v j * (c * s (i.val + j.val))) =
        c * ∑ i : Fin N, ∑ j : Fin N, v i * v j * s (i.val + j.val) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    exact sum_congr rfl fun j _ => by ring
  constructor
  · intro h N v
    have hh := h N v
    rw [he] at hh
    rw [mul_comm c] at hh
    exact nonneg_of_mul_nonneg_left hh hc
  · intro h N v
    rw [he]
    exact mul_nonneg hc.le (h N v)

private theorem completeHankelCone_iff_finiteHankel_posSemidef (s : ℕ → ℝ) :
    CompleteHankelCone s ↔ ∀ N, (finiteHankelMatrix s N).PosSemidef := by
  have he (N : ℕ) (v : Fin N → ℝ) :
      star v ⬝ᵥ finiteHankelMatrix s N *ᵥ v =
        ∑ i : Fin N, ∑ j : Fin N, v i * v j * s (i.val + j.val) := by
    simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum, finiteHankelMatrix]
    apply sum_congr rfl
    intro i _
    exact sum_congr rfl fun j _ => by ring
  constructor
  · intro h N
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun v => (he N v).symm ▸ h N v⟩
    rw [Matrix.IsHermitian]
    ext i j
    simp [finiteHankelMatrix, Nat.add_comm]
  · intro h N v
    rw [← he N v]
    exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp (h N)).2 v

/-- The sign of a quadratic Gaussian density is exactly the sign of both coefficients. -/
theorem affineGammaDensity_nonneg_iff (a b : ℝ) :
    (∀ y, 0 ≤ affineGammaDensity a b y) ↔ 0 ≤ a ∧ 0 ≤ b := by
  constructor
  · intro h
    have ha : 0 ≤ a := by simpa only [affineGammaDensity, zero_pow (by omega : 2 ≠ 0),
      mul_zero, add_zero, Real.exp_zero, mul_one] using h 0
    refine ⟨ha, ?_⟩
    by_contra hb
    have hb' : b < 0 := lt_of_not_ge hb
    let y : ℝ := Real.sqrt ((|a| + 1) / (-b))
    have hsq : y ^ 2 = (|a| + 1) / (-b) :=
      Real.sq_sqrt (div_nonneg (by positivity) (neg_pos.mpr hb').le)
    have he : a + b * y ^ 2 = a - |a| - 1 := by
      rw [hsq]
      field_simp [hb'.ne]
      ring
    have hneg : affineGammaDensity a b y < 0 := by
      unfold affineGammaDensity
      rw [he]
      exact mul_neg_of_neg_of_pos (by linarith only [le_abs_self a]) (Real.exp_pos _)
    exact (not_le_of_gt hneg) (h y)
  · rintro ⟨ha, hb⟩ y
    exact mul_nonneg (add_nonneg ha (mul_nonneg hb (sq_nonneg y))) (Real.exp_pos _).le

/-- The complete affine-Gamma cone has exactly two nonnegative coefficient directions. -/
theorem affineGamma_completeHankelCone_iff (a b : ℝ) :
    CompleteHankelCone (evenMomentSequence (affineGammaMoment a b)) ↔ 0 ≤ a ∧ 0 ≤ b := by
  letI := gaussianWindowMeasure_finite (by norm_num : (0 : ℝ) < 1 / 32)
  have h := completeHankelCone_weightedMoment_iff
    (gaussianWindowMeasure_hasEntireExponentialMoments (by norm_num : (0 : ℝ) < 1 / 32))
    (affineGammaDensity a b) (continuous_affineGammaDensity a b)
    (affineGammaDensity_memLp_top a b (1 / 32))
  have he : weightedMoment (gaussianWindowMeasure (1 / 32)) (affineGammaDensity a b) =
      fun n => clockGaussianMass * evenMomentSequence (affineGammaMoment a b) n :=
    funext (weightedMoment_affineGammaDensity a b)
  rw [he, completeHankelCone_const_mul_iff clockGaussianMass_pos,
    affineGammaDensity_nonneg_iff] at h
  exact h

/-- All mixed heads are nonnegative exactly in the closed coefficient quadrant. -/
theorem affineGamma_all_head_posSemidef_iff (a b : ℝ) :
    (∀ N, (finiteHankelMatrix (evenMomentSequence (affineGammaMoment a b)) N).PosSemidef) ↔
      0 ≤ a ∧ 0 ≤ b :=
  (completeHankelCone_iff_finiteHankel_posSemidef _).symm.trans
    (affineGamma_completeHankelCone_iff a b)

private theorem affineGamma_shifted_head_eq (a b : ℝ) (N s : ℕ) :
    finiteHankelMatrix (fun k => affineGammaMoment a b (k + s)) N =
      a • gaussianShiftedHead N s + b • gaussianShiftedHead N (s + 1) := by
  ext i j
  simp only [finiteHankelMatrix, affineGammaMoment, gaussianShiftedHead,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Nat.add_assoc]

theorem affineGamma_shifted_head_posDef {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a + b) (N s : ℕ) :
    (finiteHankelMatrix (fun k => affineGammaMoment a b (k + s)) N).PosDef := by
  rw [affineGamma_shifted_head_eq]
  rcases lt_or_eq_of_le ha with ha' | ha'
  · exact ((gaussianShiftedHead_posDef N s).smul ha').add_posSemidef
      ((gaussianShiftedHead_posDef N (s + 1)).posSemidef.smul hb)
  · rw [← ha', zero_smul, zero_add]
    exact (gaussianShiftedHead_posDef N (s + 1)).smul (by linarith only [hab, ha'])

/-- Every nonzero member of the closed coefficient cone is strict in every finite rank. -/
theorem affineGamma_all_head_posDef_iff (a b : ℝ) :
    (∀ N, (finiteHankelMatrix (evenMomentSequence (affineGammaMoment a b)) N).PosDef) ↔
      0 ≤ a ∧ 0 ≤ b ∧ 0 < a + b := by
  constructor
  · intro h
    obtain ⟨ha, hb⟩ := (affineGamma_all_head_posSemidef_iff a b).mp fun N => (h N).posSemidef
    refine ⟨ha, hb, ?_⟩
    have hp := (Matrix.posDef_iff_dotProduct_mulVec.mp (h 1)).2
      (x := fun _ => (1 : ℝ)) (by intro hz; have hh := congrFun hz 0; norm_num at hh)
    have hp' : 0 < a + 8 * b := by
      norm_num [dotProduct, Matrix.mulVec, finiteHankelMatrix, evenMomentSequence,
        affineGammaMoment, gaussianMoment, gammaShapeMoment] at hp
      linarith only [hp]
    linarith only [ha, hb, hp']
  · rintro ⟨ha, hb, hab⟩ N
    rw [finiteHankelMatrix_evenMomentSequence_posDef_iff]
    exact ⟨affineGamma_shifted_head_posDef ha hb hab ((N + 1) / 2) 0,
      affineGamma_shifted_head_posDef ha hb hab (N / 2) 1⟩

private theorem firstAtomGaussianClockSignedJet_eq_affineGamma (x : ℝ) :
    firstAtomGaussianClockSignedJet x = fun n => firstAtomClockAmplitude x *
      evenMomentSequence (affineGammaMoment (firstAtomClockShape x - 3) (3 / 8)) n := by
  rw [firstAtomGaussianClockSignedJet_eq_evenMomentSequence]
  funext n
  unfold evenMomentSequence
  split_ifs
  · exact firstAtomGaussianClockProfile_signed_even_jet x (n / 2)
  · ring

/-- Exact all-rank sign boundary of the literal nonlinear first-atom clock. -/
theorem firstAtomGaussianClock_all_head_posSemidef_iff (x : ℝ) :
    (∀ N, (finiteHankelMatrix (firstAtomGaussianClockSignedJet x) N).PosSemidef) ↔
      3 ≤ firstAtomClockShape x := by
  rw [← completeHankelCone_iff_finiteHankel_posSemidef,
    firstAtomGaussianClockSignedJet_eq_affineGamma,
    completeHankelCone_const_mul_iff (firstAtomClockAmplitude_pos x),
    affineGamma_completeHankelCone_iff]
  constructor
  · exact fun h => sub_nonneg.mp h.1
  · intro h
    exact ⟨sub_nonneg.mpr h, by norm_num⟩

/-- At the exact boundary the adjacent shifted Gamma component remains strict. -/
theorem firstAtomGaussianClock_all_head_posDef_iff (x : ℝ) :
    (∀ N, (finiteHankelMatrix (firstAtomGaussianClockSignedJet x) N).PosDef) ↔
      3 ≤ firstAtomClockShape x := by
  constructor
  · intro h
    exact (firstAtomGaussianClock_all_head_posSemidef_iff x).mp fun N => (h N).posSemidef
  · exact fun h N => firstAtomGaussianClockSignedHead_posDef h N

/-- Every individual signed even clock moment is nonnegative at every source center. -/
theorem firstAtomGaussianClockMoment_nonneg (x : ℝ) (k : ℕ) :
    0 ≤ firstAtomGaussianClockMoment x k := by
  rw [firstAtomGaussianClockMoment, firstAtomGaussianClockProfile_signed_even_jet_eq]
  have hgamma : 0 < gaussianMoment k := by
    unfold gaussianMoment
    exact mul_pos (by positivity) (gammaShapeMoment_pos (by norm_num) k)
  exact mul_nonneg (mul_pos (firstAtomClockAmplitude_pos x) hgamma).le
    (add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg k)))

/-- Positive individual moments do not remove the finite mixed obstruction below the sharp shape. -/
theorem firstAtomGaussianClock_mixed_failure_of_shape_lt_three {x : ℝ}
    (hx : firstAtomClockShape x < 3) :
    (∀ k, 0 ≤ firstAtomGaussianClockMoment x k) ∧
      ∃ N, ¬ (finiteHankelMatrix (firstAtomGaussianClockSignedJet x) N).PosSemidef := by
  refine ⟨firstAtomGaussianClockMoment_nonneg x, ?_⟩
  apply not_forall.mp
  intro h
  exact (not_le_of_gt hx) ((firstAtomGaussianClock_all_head_posSemidef_iff x).mp h)

#print axioms affineGamma_completeHankelCone_iff
#print axioms affineGamma_all_head_posSemidef_iff
#print axioms affineGamma_all_head_posDef_iff
#print axioms firstAtomGaussianClock_all_head_posSemidef_iff
#print axioms firstAtomGaussianClock_all_head_posDef_iff
#print axioms firstAtomGaussianClock_mixed_failure_of_shape_lt_three

end GaloisForLFunctions.CompletedArithmeticForms
