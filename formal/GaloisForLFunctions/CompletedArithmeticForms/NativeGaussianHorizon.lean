import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomMixedHorizon
import GaloisForLFunctions.CompletedArithmeticForms.NativeTailReserve

/-!
# Joint rank and center bounds for the complete native theta source

The infinite theta remainder has an explicit factorial cost after Gaussian
normalization. Together with the analytic first-atom estimate and the full Gaussian
inverse, it gives a finite mixed-head positivity horizon depending explicitly on rank.
-/

noncomputable section

open Finset Matrix

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- Uniform Gaussian error numerator for all complete-source moment orders through `L`. -/
def nativeGaussianErrorNumerator (L : ℕ) : ℝ :=
  ((2 * L).factorial : ℝ) * firstAtomGaussianErrorConstant +
    27 * (24 : ℝ) ^ (2 * L) * (Real.exp (3 * Real.pi) / 399) * ((L + 1).factorial : ℝ)

theorem nativeGaussianErrorNumerator_nonneg (L : ℕ) : 0 ≤ nativeGaussianErrorNumerator L := by
  have hD := firstAtomGaussianErrorConstant_pos
  unfold nativeGaussianErrorNumerator
  positivity

private theorem likelihood_weight_le_factorial (L : ℕ) (x : ℝ) :
    thetaCuspSingleAtomReflectionScale 1 x ^ L * regimeOneLikelihoodScale x ≤
      (Real.exp (3 * Real.pi) / 399) * ((L + 1).factorial : ℝ) /
        thetaCuspSingleAtomReflectionScale 1 x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq : 0 < q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hpower := _root_.RHTower.pow_mul_exp_neg_le_factorial (L + 1) hq.le
  have he : Real.exp (-(3 * q)) ≤ Real.exp (-q) := Real.exp_le_exp.mpr (by linarith only [hq])
  have hweight : q ^ (L + 1) * regimeOneLikelihoodScale x ≤
      (Real.exp (3 * Real.pi) / 399) * ((L + 1).factorial : ℝ) := by
    rw [regimeOneLikelihoodScale_eq]
    calc
      _ = (Real.exp (3 * Real.pi) / 399) * (q ^ (L + 1) * Real.exp (-(3 * q))) := by
        dsimp only [q]
        ring
      _ ≤ (Real.exp (3 * Real.pi) / 399) * (q ^ (L + 1) * Real.exp (-q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (pow_nonneg hq.le _)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpower (by positivity)
  apply (le_div_iff₀ hq).mpr
  calc
    _ = q ^ (L + 1) * regimeOneLikelihoodScale x := by rw [pow_succ]; ring
    _ ≤ _ := hweight

/-- The complete infinite theta remainder has an explicit reciprocal-scale cost through any order. -/
theorem nativeScaledEvenJet_firstAtom_error_le_through {L k : ℕ} (hk : k ≤ L) {x : ℝ}
    (hq : ((2 * L : ℕ) : ℝ) + 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet k x - thetaCuspFirstAtomScaledEvenJet k x| ≤
      (27 * (24 : ℝ) ^ (2 * L) * (Real.exp (3 * Real.pi) / 399) * ((L + 1).factorial : ℝ)) /
        thetaCuspSingleAtomReflectionScale 1 x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq6 : 6 ≤ q := by dsimp [q]; linarith only [hq, (Nat.cast_nonneg (2 * L) : (0 : ℝ) ≤ (2 * L : ℕ))]
  have hq1 : 1 ≤ q := by linarith only [hq6]
  have hq0 : 0 ≤ q := by linarith only [hq6]
  have hx : 0 < x := regimeOne_pos_of_six_le hq6
  have hkr : ((2 * k : ℕ) : ℝ) ≤ ((2 * L : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left 2 hk
  have he := abs_thetaCuspNativeScaledEvenJet_sub_first_le_effective k hx
    (by linarith only [hq, hkr])
  have h24 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 24) (Nat.mul_le_mul_left 2 hk)
  have hp := pow_le_pow_right₀ hq1 hk
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul h24 hp (pow_nonneg hq0 k) (by positivity)) (regimeOneLikelihoodScale_pos x).le
  have hw := likelihood_weight_le_factorial L x
  calc
    _ ≤ 27 * (24 : ℝ) ^ (2 * k) * q ^ k * regimeOneLikelihoodScale x := he
    _ ≤ 27 * (24 : ℝ) ^ (2 * L) * (q ^ L * regimeOneLikelihoodScale x) := by
      nlinarith only [hm]
    _ ≤ 27 * (24 : ℝ) ^ (2 * L) *
        ((Real.exp (3 * Real.pi) / 399) * ((L + 1).factorial : ℝ) / q) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by dsimp only [q]; ring

/-- A simultaneous Gaussian estimate for every complete native moment through the requested order. -/
theorem nativeScaledEvenJet_gaussian_error_le_through {L k : ℕ} (hk : k ≤ L) {x : ℝ}
    (hq : ((2 * L : ℕ) : ℝ) + 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet k x - gaussianMoment k| ≤
      nativeGaussianErrorNumerator L / thetaCuspSingleAtomReflectionScale 1 x := by
  have hq3 : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    linarith only [hq, (Nat.cast_nonneg (2 * L) : (0 : ℝ) ≤ (2 * L : ℕ))]
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq3]
  have hf : ((2 * k).factorial : ℝ) ≤ ((2 * L).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.mul_le_mul_left 2 hk)
  have hfirst := (firstAtomScaledEvenJet_gaussian_error_le hq3 k).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hf firstAtomGaussianErrorConstant_pos.le) hqp.le)
  have htail := nativeScaledEvenJet_firstAtom_error_le_through hk hq
  calc
    _ ≤ |thetaCuspNativeScaledEvenJet k x - thetaCuspFirstAtomScaledEvenJet k x| +
        |thetaCuspFirstAtomScaledEvenJet k x - gaussianMoment k| := abs_sub_le _ _ _
    _ ≤ _ := by
      unfold nativeGaussianErrorNumerator
      rw [add_div]
      linarith only [hfirst, htail]

/-- Relative inverse-trace numerator, including the complete theta remainder. -/
def nativeMixedErrorNumerator (N s : ℕ) : ℝ :=
  (N : ℝ) * gaussianInverseTrace N s * nativeGaussianErrorNumerator (s + 2 * N)

theorem nativeMixedErrorNumerator_nonneg (N s : ℕ) : 0 ≤ nativeMixedErrorNumerator N s := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (gaussianInverseTrace_nonneg N s))
    (nativeGaussianErrorNumerator_nonneg _)

private theorem nativeBalancedHead_entry_error_le {x : ℝ} (N s : ℕ)
    (hq : ((2 * (s + 2 * N) : ℕ) : ℝ) + 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (i j : Fin N) :
    |finiteHankelMatrix (nativeBalancedMoment s x) N i j - gaussianShiftedHead N s i j| ≤
      nativeGaussianErrorNumerator (s + 2 * N) / thetaCuspSingleAtomReflectionScale 1 x :=
  nativeScaledEvenJet_gaussian_error_le_through (by omega : i.val + j.val + s ≤ s + 2 * N) hq

/-- Explicit relative control of the complete native head, uniform on its rank-dependent scale ray. -/
theorem nativeBalancedHead_relative_error_le {x : ℝ} (N s : ℕ)
    (hq : ((2 * (s + 2 * N) : ℕ) : ℝ) + 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (finiteHankelMatrix (nativeBalancedMoment s x) N - gaussianShiftedHead N s) *ᵥ v| ≤
      (nativeMixedErrorNumerator N s / thetaCuspSingleAtomReflectionScale 1 x) *
        (v ⬝ᵥ gaussianShiftedHead N s *ᵥ v) := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have he := relative_error_le_inverseTrace (gaussianShiftedHead_posDef N s)
    (div_nonneg (nativeGaussianErrorNumerator_nonneg _) hqp.le)
    (nativeBalancedHead_entry_error_le N s hq) v
  convert he using 1
  dsimp [nativeMixedErrorNumerator, gaussianInverseTrace]
  ring

/-- An explicit payment leaves half of the full Gaussian form in the complete native source. -/
theorem nativeBalancedHead_half_posDef_of_scale {x : ℝ} (N s : ℕ)
    (hq : ((2 * (s + 2 * N) : ℕ) : ℝ) + 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hscale : 2 * nativeMixedErrorNumerator N s < thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix (nativeBalancedMoment s x) N -
      (1 / 2 : ℝ) • gaussianShiftedHead N s).PosDef := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hA : (finiteHankelMatrix (nativeBalancedMoment s x) N).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [finiteHankelMatrix, Nat.add_comm]
  apply half_relative_posDef_of_inverseTrace (gaussianShiftedHead_posDef N s) hA
    (div_nonneg (nativeGaussianErrorNumerator_nonneg _) hqp.le)
    (nativeBalancedHead_entry_error_le N s hq)
  have he : (N : ℝ) * (nativeGaussianErrorNumerator (s + 2 * N) /
      thetaCuspSingleAtomReflectionScale 1 x) * (gaussianShiftedHead N s)⁻¹.trace =
      nativeMixedErrorNumerator N s / thetaCuspSingleAtomReflectionScale 1 x := by
    dsimp [nativeMixedErrorNumerator, gaussianInverseTrace]
    ring
  rw [he, div_lt_iff₀ hqp]
  linarith only [hscale]

/-- Positive source mass and scale identify the balanced estimate with the literal native head. -/
theorem nativeShiftedHead_posDef_of_scale {x : ℝ} (N s : ℕ)
    (hq : ((2 * (s + 2 * N) : ℕ) : ℝ) + 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hscale : 2 * nativeMixedErrorNumerator N s < thetaCuspSingleAtomReflectionScale 1 x) :
    (nativeShiftedMatrix N s x).PosDef := by
  have hhalf := nativeBalancedHead_half_posDef_of_scale N s hq hscale
  have hG := (gaussianShiftedHead_posDef N s).smul (by norm_num : (0 : ℝ) < 1 / 2)
  have hA : (finiteHankelMatrix (nativeBalancedMoment s x) N).PosDef := by
    simpa only [sub_add_cancel] using hhalf.add hG
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let D : Matrix (Fin N) (Fin N) ℝ := diagonal (fun i => f * q ^ i.val)
  have hq3 : 3 ≤ q := by
    dsimp [q]
    linarith only [hq, (Nat.cast_nonneg (2 * (s + 2 * N)) : (0 : ℝ) ≤ (2 * (s + 2 * N) : ℕ))]
  have hqp : 0 < q := by linarith only [hq3]
  have hf : f ≠ 0 := by
    intro h
    have hp := firstAtom_mass_pos hq3
    change 0 < f ^ 2 at hp
    rw [h, zero_pow (by omega : (2 : ℕ) ≠ 0)] at hp
    exact lt_irrefl 0 hp
  have hD : Function.Injective D.mulVec := by
    intro v w h
    funext i
    have hi := congrFun h i
    simp only [D, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (mul_ne_zero hf (pow_ne_zero _ hqp.ne')) hi
  have he : nativeShiftedMatrix N s x =
      q ^ s • (Dᴴ * finiteHankelMatrix (nativeBalancedMoment s x) N * D) := by
    ext i j
    simp only [D, diagonal_conjTranspose, star_trivial, diagonal_mul, mul_diagonal,
      Matrix.smul_apply, smul_eq_mul, nativeShiftedMatrix, finiteHankelMatrix,
      nativeBalancedMoment, thetaCuspNativeScaledEvenJet]
    change _ = q ^ s * (f * q ^ i.val *
      (_ / (f ^ 2 * q ^ (i.val + j.val + s))) * (f * q ^ j.val))
    rw [pow_add, pow_add]
    field_simp [hf, hqp.ne']
    ring
  rw [he]
  exact (hA.conjTranspose_mul_mul_same hD).smul (pow_pos hqp s)

/-- A single physical scale pays both parity blocks and their complete-source analytic domains. -/
def nativeMixedScale (N : ℕ) : ℝ :=
  ((2 * (N + 1) + 6 : ℕ) : ℝ) +
    2 * (nativeMixedErrorNumerator ((N + 1) / 2) 0 + nativeMixedErrorNumerator (N / 2) 1)

theorem nativeMixedScale_base_le (N : ℕ) :
    ((2 * (N + 1) + 6 : ℕ) : ℝ) ≤ nativeMixedScale N := by
  unfold nativeMixedScale
  linarith only [nativeMixedErrorNumerator_nonneg ((N + 1) / 2) 0,
    nativeMixedErrorNumerator_nonneg (N / 2) 1]

/-- The complete native full signed head is strictly positive throughout an explicit scale ray. -/
theorem nativeSignedHead_posDef_of_scale (N : ℕ) {x : ℝ}
    (hscale : nativeMixedScale N ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix (thetaCuspNativeSignedJet x) N).PosDef := by
  have hbase := (nativeMixedScale_base_le N).trans hscale
  have hdomain (M s : ℕ) (hM : s + 2 * M ≤ N + 1) :
      ((2 * (s + 2 * M) : ℕ) : ℝ) + 6 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    have h : ((2 * (s + 2 * M) : ℕ) : ℝ) + 6 ≤ ((2 * (N + 1) + 6 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left 2 hM) 6
    exact h.trans hbase
  have hbpos : (0 : ℝ) < ((2 * (N + 1) + 6 : ℕ) : ℝ) := by positivity
  have he : 2 * nativeMixedErrorNumerator ((N + 1) / 2) 0 <
      thetaCuspSingleAtomReflectionScale 1 x := by
    unfold nativeMixedScale at hscale
    linarith only [hscale, hbpos, nativeMixedErrorNumerator_nonneg (N / 2) 1]
  have ho : 2 * nativeMixedErrorNumerator (N / 2) 1 <
      thetaCuspSingleAtomReflectionScale 1 x := by
    unfold nativeMixedScale at hscale
    linarith only [hscale, hbpos, nativeMixedErrorNumerator_nonneg ((N + 1) / 2) 0]
  rw [thetaCuspNativeSignedJet_eq_evenMomentSequence,
    finiteHankelMatrix_evenMomentSequence_posDef_iff]
  exact ⟨nativeShiftedHead_posDef_of_scale ((N + 1) / 2) 0
      (hdomain _ _ (by omega)) he,
    nativeShiftedHead_posDef_of_scale (N / 2) 1 (hdomain _ _ (by omega)) ho⟩

/-- Explicit center horizon for the complete native signed head at the given rank. -/
def nativeMixedHorizon (N : ℕ) : ℝ :=
  max 0 (Real.log (nativeMixedScale N / Real.pi) / 2)

/-- A simultaneous rank–center positivity statement for the untruncated native theta source. -/
theorem nativeSignedHead_posDef_of_horizon (N : ℕ) {x : ℝ}
    (hx : nativeMixedHorizon N ≤ x) :
    (finiteHankelMatrix (thetaCuspNativeSignedJet x) N).PosDef := by
  have hQ : 0 < nativeMixedScale N := lt_of_lt_of_le (by positivity) (nativeMixedScale_base_le N)
  have hxlog : Real.log (nativeMixedScale N / Real.pi) ≤ 2 * x := by
    have h := (le_max_right 0 (Real.log (nativeMixedScale N / Real.pi) / 2)).trans hx
    linarith only [h]
  have he := Real.exp_le_exp.mpr hxlog
  rw [Real.exp_log (div_pos hQ Real.pi_pos)] at he
  have hm := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  apply nativeSignedHead_posDef_of_scale N
  simpa only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one,
    mul_div_cancel₀ _ Real.pi_ne_zero] using hm

#print axioms nativeScaledEvenJet_firstAtom_error_le_through
#print axioms nativeScaledEvenJet_gaussian_error_le_through
#print axioms nativeBalancedHead_relative_error_le
#print axioms nativeBalancedHead_half_posDef_of_scale
#print axioms nativeSignedHead_posDef_of_scale
#print axioms nativeSignedHead_posDef_of_horizon

end GaloisForLFunctions.CompletedArithmeticForms
