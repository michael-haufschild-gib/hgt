import GaloisForLFunctions.RHTower.ModularLambdaWindingLog
import GaloisForLFunctions.RHTower.RepCosetOrthogonality
import GaloisForLFunctions.RHTower.ModularInvariantHeight
import GaloisForLFunctions.RHTower.RepPointPairSmallEigenCriterion
import GaloisForLFunctions.RHTower.HolomorphicHyperbolicMeanValue

/-!
# The test field on the cyclic cover `Γ_N`

`Γ_N = windingSubgroup N` is the kernel of the winding character `Γ(2) → ℤ/N` (exponent sum of
`A = T²` in the free basis `A, B` of `Γ(2)/±1`).  With `ℓ = log λ` the logarithm of the modular
lambda function, `ℓ(γτ) = ℓ(τ) + 2πi·w(γ)` for `γ ∈ Γ(2)`, so the phase `e^{i Im ℓ / N}` is
`Γ_N`-invariant and picks up `e^{−2πi/N}` under `A⁻¹`.  The test function is

  `f_{N,L}(z) = e^{i Im ℓ(z)/N} c_L(z)`,  `c_L = ramp_L ∘ Y`,

where `Y` is the invariant height and `ramp_L(t) = clamp(2 − log t / log L)` is `1` below `L` and `0`
above `L²`.  Its coset lift is a continuous equivariant field, square-integrable, pointwise
orthogonal to the invariant vectors (`A` normalizes `Γ_N`), with `‖F(z)‖² = [SL(2,ℤ) : Γ_N] c_L(z)²`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped MatrixGroups InnerProductSpace

namespace GaloisForLFunctions.RHTower.NonvacuousWitness

open GaloisForLFunctions.HTGeometry RepPointPair RepCoset ModularLambdaWinding

noncomputable section

/-! ## The ramp and the cusp cutoff -/

/-- The logarithmic ramp: `1` for `t ≤ L`, `0` for `t ≥ L²`. -/
def logRamp (L t : ℝ) : ℝ := min 1 (max 0 (2 - Real.log t / Real.log L))

theorem logRamp_nonneg (L t : ℝ) : 0 ≤ logRamp L t := le_min zero_le_one (le_max_left _ _)

theorem logRamp_le_one (L t : ℝ) : logRamp L t ≤ 1 := min_le_left _ _

/-- The cusp cutoff `c_L(z) = ramp_L(Y(z))`. -/
def cuspRamp (L : ℝ) (z : ℍ) : ℝ := logRamp L (invHeight z)

theorem cuspRamp_smul (L : ℝ) (B : SL(2, ℤ)) (z : ℍ) : cuspRamp L (B • z) = cuspRamp L z := by
  rw [cuspRamp, cuspRamp, invHeight_smul]

theorem continuous_cuspRamp (L : ℝ) : Continuous (cuspRamp L) := by
  unfold cuspRamp logRamp
  have hlog : Continuous fun z => Real.log (invHeight z) :=
    continuous_invHeight.log fun z => (invHeight_pos z).ne'
  fun_prop

/-! ## The test function -/

/-- The test function `f_{N,L}(z) = e^{i Im ℓ(z)/N} c_L(z)`. -/
def testFun (N : ℕ) (L : ℝ) (z : ℍ) : ℂ :=
  Complex.exp ((((lambdaLog z).im / N : ℝ) : ℂ) * Complex.I) * (cuspRamp L z : ℂ)

theorem continuous_lambdaLog_coe : Continuous fun z : ℍ => lambdaLog z :=
  continuousOn_lambdaLog.comp_continuous UpperHalfPlane.continuous_coe fun z => z.im_pos

theorem continuous_testFun (N : ℕ) (L : ℝ) : Continuous (testFun N L) := by
  unfold testFun
  have h1 : Continuous fun z : ℍ => (lambdaLog z).im :=
    Complex.continuous_im.comp continuous_lambdaLog_coe
  have h2 := continuous_cuspRamp L
  fun_prop

theorem cuspRamp_nonneg (L : ℝ) (z : ℍ) : 0 ≤ cuspRamp L z := logRamp_nonneg _ _

theorem cuspRamp_le_one (L : ℝ) (z : ℍ) : cuspRamp L z ≤ 1 := logRamp_le_one _ _

theorem norm_testFun (N : ℕ) (L : ℝ) (z : ℍ) : ‖testFun N L z‖ = cuspRamp L z := by
  rw [testFun, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (cuspRamp_nonneg L z)]

/-- The phase factor is unchanged by a shift of `Im ℓ` by `2πNk`. -/
theorem exp_im_shift (N : ℕ) [NeZero N] (a : ℝ) (k : ℤ) :
    Complex.exp ((((a + 2 * Real.pi * (N * k : ℤ)) / N : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((a / N : ℝ) : ℂ) * Complex.I) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  rw [show (((a + 2 * Real.pi * (N * k : ℤ)) / N : ℝ) : ℂ) * Complex.I =
      ((a / N : ℝ) : ℂ) * Complex.I + (k : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast
    field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **`Γ_N`-invariance of the test function.** -/
theorem testFun_smul (N : ℕ) [NeZero N] (L : ℝ) {g : SL(2, ℤ)} (hg : g ∈ windingSubgroup N)
    (z : ℍ) : testFun N L (g • z) = testFun N L z := by
  obtain ⟨hg2, k, hk⟩ := mem_windingSubgroup.1 hg
  unfold testFun
  rw [cuspRamp_smul, lambdaLog_smul hg2 z, hk]
  congr 1
  have him : (lambdaLog (z : ℂ) + 2 * Real.pi * Complex.I * (((N : ℤ) * k : ℤ) : ℂ)).im =
      (lambdaLog z).im + 2 * Real.pi * (N * k : ℤ) := by
    simp [Complex.add_im, Complex.mul_im]
  rw [him, exp_im_shift N]

/-- **The character of `A = T²`**: `f(A⁻¹ z) = e^{−2πi/N} f(z)`. -/
theorem testFun_sanovA_inv (N : ℕ) (L : ℝ) (z : ℍ) :
    testFun N L (sanovA⁻¹ • z) =
      Complex.exp (((-(2 * Real.pi) / N : ℝ) : ℂ) * Complex.I) * testFun N L z := by
  have hA : sanovA⁻¹ ∈ Gamma 2 := (Gamma 2).inv_mem sanovA_mem
  have hw : Multiplicative.toAdd (gammaTwoWinding ⟨sanovA⁻¹, hA⟩) = -1 := by
    have : (⟨sanovA⁻¹, hA⟩ : Gamma 2) = (⟨sanovA, sanovA_mem⟩ : Gamma 2)⁻¹ := rfl
    rw [this, map_inv, gammaTwoWinding_sanovA]
    rfl
  unfold testFun
  rw [cuspRamp_smul, lambdaLog_smul hA z, hw, ← mul_assoc, ← Complex.exp_add]
  congr 2
  have him : (lambdaLog (z : ℂ) + 2 * Real.pi * Complex.I * (((-1 : ℤ)) : ℂ)).im =
      (lambdaLog z).im - 2 * Real.pi := by
    simp [Complex.add_im, Complex.mul_im]
    ring
  rw [him]
  push_cast
  ring

/-- `A = T²` normalizes `Γ_N`. -/
theorem sanovA_conj_mem (N : ℕ) {γ : SL(2, ℤ)} (hγ : γ ∈ windingSubgroup N) :
    sanovA⁻¹ * γ * sanovA ∈ windingSubgroup N ∧ sanovA * γ * sanovA⁻¹ ∈ windingSubgroup N := by
  obtain ⟨hγ2, hk⟩ := mem_windingSubgroup.1 hγ
  have hA := sanovA_mem
  have hA' : sanovA⁻¹ ∈ Gamma 2 := (Gamma 2).inv_mem hA
  have h1 : sanovA⁻¹ * γ * sanovA ∈ Gamma 2 :=
    (Gamma 2).mul_mem ((Gamma 2).mul_mem hA' hγ2) hA
  have h2 : sanovA * γ * sanovA⁻¹ ∈ Gamma 2 :=
    (Gamma 2).mul_mem ((Gamma 2).mul_mem hA hγ2) hA'
  refine ⟨mem_windingSubgroup.2 ⟨h1, ?_⟩, mem_windingSubgroup.2 ⟨h2, ?_⟩⟩
  · have e : (⟨sanovA⁻¹ * γ * sanovA, h1⟩ : Gamma 2) =
        (⟨sanovA, hA⟩ : Gamma 2)⁻¹ * ⟨γ, hγ2⟩ * ⟨sanovA, hA⟩ := rfl
    have hc : gammaTwoWinding ⟨sanovA⁻¹ * γ * sanovA, h1⟩ = gammaTwoWinding ⟨γ, hγ2⟩ := by
      rw [e, map_mul, map_mul, map_inv, mul_comm _ (gammaTwoWinding ⟨γ, hγ2⟩), mul_assoc,
        inv_mul_cancel, mul_one]
    rw [hc]
    exact hk
  · have e : (⟨sanovA * γ * sanovA⁻¹, h2⟩ : Gamma 2) =
        (⟨sanovA, hA⟩ : Gamma 2) * ⟨γ, hγ2⟩ * (⟨sanovA, hA⟩ : Gamma 2)⁻¹ := rfl
    have hc : gammaTwoWinding ⟨sanovA * γ * sanovA⁻¹, h2⟩ = gammaTwoWinding ⟨γ, hγ2⟩ := by
      rw [e, map_mul, map_mul, map_inv, mul_comm (gammaTwoWinding ⟨sanovA, hA⟩), mul_assoc,
        mul_inv_cancel, mul_one]
    rw [hc]
    exact hk


/-! ## The test field -/

/-- The character value `ω = e^{−2πi/N}` is not `1` for `N ≥ 2`. -/
theorem exp_neg_two_pi_div_ne_one {N : ℕ} (hN : 2 ≤ N) :
    Complex.exp (((-(2 * Real.pi) / N : ℝ) : ℂ) * Complex.I) ≠ 1 := by
  rw [Ne, Complex.exp_eq_one_iff]
  rintro ⟨n, hn⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hre : -(2 * Real.pi) / N = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa [Complex.mul_im] using this
  have hpi := Real.pi_pos
  have h1 : (n : ℝ) = -1 / N := by
    field_simp at hre ⊢
    nlinarith
  have h2 : -1 < (n : ℝ) ∧ (n : ℝ) < 0 := by
    rw [h1]
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    constructor
    · rw [lt_div_iff₀ hNpos]; linarith
    · exact div_neg_of_neg_of_pos (by norm_num) hNpos
  have h3 : -1 < n ∧ n < 0 := ⟨by exact_mod_cast h2.1, by exact_mod_cast h2.2⟩
  omega

variable (N : ℕ) [NeZero N] (L : ℝ)

/-- **The test field** `F_{N,L} = ` coset lift of `f_{N,L}` along `Γ_N`. -/
def testField (z : ℍ) : EuclideanSpace ℂ (SL(2, ℤ) ⧸ windingSubgroup N) :=
  cosetLift (testFun N L) z

omit [NeZero N] in
theorem testField_apply (z : ℍ) (q : SL(2, ℤ) ⧸ windingSubgroup N) :
    testField N L z q = testFun N L ((Quotient.out q)⁻¹ • z) := rfl

omit [NeZero N] in
theorem continuous_testField : Continuous (testField N L) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun q => ?_)
  exact (continuous_testFun N L).comp (continuous_smul_int _)

theorem isEquivariant_testField : IsEquivariant (cosetRep (windingSubgroup N)) (testField N L) :=
  isEquivariant_cosetLift fun _ hγ z => testFun_smul N L hγ z

theorem norm_sq_testField (z : ℍ) :
    ‖testField N L z‖ ^ 2 = Fintype.card (SL(2, ℤ) ⧸ windingSubgroup N) * cuspRamp L z ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [testField_apply, norm_testFun, cuspRamp_smul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem memLp_testField : MemLp (testField N L) 2 cellMeasure := by
  refine MemLp.of_bound (continuous_testField N L).aestronglyMeasurable
    (Real.sqrt (Fintype.card (SL(2, ℤ) ⧸ windingSubgroup N))) (Eventually.of_forall fun z => ?_)
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_testField]
  refine Real.sqrt_le_sqrt ?_
  have h0 := cuspRamp_nonneg L z
  have h1 := cuspRamp_le_one L z
  have : cuspRamp L z ^ 2 ≤ 1 := by nlinarith
  calc (Fintype.card (SL(2, ℤ) ⧸ windingSubgroup N) : ℝ) * cuspRamp L z ^ 2
      ≤ (Fintype.card (SL(2, ℤ) ⧸ windingSubgroup N) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
    _ = _ := mul_one _

/-- **The test field is pointwise orthogonal to the invariant vectors** (`N ≥ 2`). -/
theorem inner_testField_eq_zero (hN : 2 ≤ N) (z : ℍ)
    (c : EuclideanSpace ℂ (SL(2, ℤ) ⧸ windingSubgroup N))
    (hc : ∀ B, cosetRep (windingSubgroup N) B c = c) : ⟪c, testField N L z⟫_ℂ = 0 :=
  inner_cosetLift_eq_zero (fun _ hγ z => testFun_smul N L hγ z)
    (fun _ hγ => (sanovA_conj_mem N hγ).1) (fun _ hγ => (sanovA_conj_mem N hγ).2)
    (exp_neg_two_pi_div_ne_one hN) (testFun_sanovA_inv N L) z hc

/-- On the modular cell the cutoff is `1` below height `L`. -/
theorem cuspRamp_eq_one {L : ℝ} (hL : 1 < L) {z : ℍ} (hz : z ∈ fd) (hzL : z.im ≤ L) :
    cuspRamp L z = 1 := by
  rw [cuspRamp, invHeight_eq_of_mem_fd hz, logRamp]
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hle : Real.log z.im ≤ Real.log L := Real.log_le_log z.im_pos hzL
  have : 1 ≤ 2 - Real.log z.im / Real.log L := by
    have : Real.log z.im / Real.log L ≤ 1 := (div_le_one hlogL).2 hle
    linarith
  rw [max_eq_right (by linarith), min_eq_left this]

end

end GaloisForLFunctions.RHTower.NonvacuousWitness
