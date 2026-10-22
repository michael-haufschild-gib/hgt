import GaloisForLFunctions.HTGeometry.HermiteOrthogonality
import GaloisForLFunctions.RHTower.CCM.CCMMetaplecticJacobiRigidity
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.OfAssociative

/-!
# The metaplectic oscillator triple on the Hermite core

On `𝓢(ℝ, ℂ)`, with `x` the coordinate multiplication and `∂` the derivative, the operators

`H = x ∂ + 1/2`,   `E = -iπ x²`,   `F = -(i/4π) ∂²`

form an `sl₂`-triple, `[H,E] = 2E`, `[H,F] = -2F`, `[E,F] = H`; the only input is the canonical
relation `∂ x = 1 + x ∂`.  This is the infinitesimal metaplectic (oscillator) representation of
`sl₂(ℝ)` for the Fourier normalization `e^{-2πixξ}`.

With the ladder operators `A = 2πx - ∂`, `B = 2πx + ∂` the three elements used by
Connes--Consani--Moscovici are

* `J = (8π)⁻¹ (A² + B²) = i(E + F) = πx² + ∂²/(4π)`,
* `N = (8π)⁻¹ A B = (i/2)(E - F) - 1/4`,
* `[J, N] = (8π)⁻¹ (B² - A²) = H`.

On the `L²`-normalized Hermite functions `ĥ_k` one has `A ĥ_k = α_k ĥ_{k+1}`,
`B ĥ_{k+1} = α_k ĥ_k`, `B ĥ_0 = 0` with `α_k = 2π √((k+1)/π)`.  Hence on the even functions
`ĥ_{2n}`, `N` is the number operator and `J` is the Jacobi operator with zero diagonal and
off-diagonal coefficients `a_n = √((2n+1)(2n+2))/2`, the metaplectic coefficients of
`CCMMetaplecticJacobiRigidity`.
-/

noncomputable section

open Complex MeasureTheory GaloisForLFunctions
open scoped SchwartzMap Real

namespace RHTower

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Commutator identities in an associative algebra -/

section RingIdentities

variable {R : Type*} [Ring R] [Algebra ℂ R]

omit [Algebra ℂ R] in
theorem ccmCanonical_commutator_xd_xx (M D : R) (r : D * M = 1 + M * D) :
    M * D * (M * M) - M * M * (M * D) = 2 • (M * M) := by
  calc M * D * (M * M) - M * M * (M * D) = M * (D * M) * M - M * M * (M * D) := by noncomm_ring
    _ = M * (1 + M * D) * M - M * M * (M * D) := by rw [r]
    _ = M * M + M * M * (D * M) - M * M * (M * D) := by noncomm_ring
    _ = M * M + M * M * (1 + M * D) - M * M * (M * D) := by rw [r]
    _ = 2 • (M * M) := by noncomm_ring

omit [Algebra ℂ R] in
theorem ccmCanonical_commutator_xd_dd (M D : R) (r : D * M = 1 + M * D) :
    M * D * (D * D) - D * D * (M * D) = -(2 • (D * D)) := by
  calc M * D * (D * D) - D * D * (M * D) = M * D * (D * D) - D * (D * M) * D := by noncomm_ring
    _ = M * D * (D * D) - D * (1 + M * D) * D := by rw [r]
    _ = M * D * (D * D) - (D * D + (D * M) * D * D) := by noncomm_ring
    _ = M * D * (D * D) - (D * D + (1 + M * D) * D * D) := by rw [r]
    _ = -(2 • (D * D)) := by noncomm_ring

omit [Algebra ℂ R] in
theorem ccmCanonical_commutator_xx_dd (M D : R) (r : D * M = 1 + M * D) :
    M * M * (D * D) - D * D * (M * M) = -(2 • (1 : R)) - 4 • (M * D) := by
  calc M * M * (D * D) - D * D * (M * M) = M * M * (D * D) - D * (D * M) * M := by noncomm_ring
    _ = M * M * (D * D) - D * (1 + M * D) * M := by rw [r]
    _ = M * M * (D * D) - (D * M + (D * M) * (D * M)) := by noncomm_ring
    _ = M * M * (D * D) - ((1 + M * D) + (1 + M * D) * (1 + M * D)) := by rw [r]
    _ = M * M * (D * D) - (2 • 1 + 3 • (M * D) + M * (D * M) * D) := by noncomm_ring
    _ = M * M * (D * D) - (2 • 1 + 3 • (M * D) + M * (1 + M * D) * D) := by rw [r]
    _ = -(2 • (1 : R)) - 4 • (M * D) := by noncomm_ring

/-- Shifting by a scalar does not change a commutator. -/
theorem ccmCommutator_add_smul_one (X Y : R) (c : ℂ) :
    (X + c • 1) * Y - Y * (X + c • 1) = X * Y - Y * X := by
  simp only [add_mul, mul_add, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  abel

theorem ccmCommutator_smul_smul (X Y : R) (a b : ℂ) :
    (a • X) * (b • Y) - (b • Y) * (a • X) = (a * b) • (X * Y - Y * X) := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm b a, ← smul_sub]

theorem ccmCommutator_smul_right (X Y : R) (b : ℂ) :
    X * (b • Y) - (b • Y) * X = b • (X * Y - Y * X) := by
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]

/-- For ladder operators with `B A = A B + k`, `[A² + B², A B] = 2k (B² - A²)`. -/
theorem ccmLadder_commutator_sumSq_mul (A B : R) (k : ℂ) (r : B * A = A * B + k • 1) :
    (A * A + B * B) * (A * B) - A * B * (A * A + B * B) = (2 * k) • (B * B - A * A) := by
  have h1 : A * B * (A * A) = A * A * (A * B) + (2 * k) • (A * A) := by
    calc A * B * (A * A) = A * (B * A) * A := by noncomm_ring
      _ = A * (A * B + k • 1) * A := by rw [r]
      _ = A * A * (B * A) + k • (A * A) := by
        simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, mul_assoc]
      _ = A * A * (A * B + k • 1) + k • (A * A) := by rw [r]
      _ = A * A * (A * B) + (2 * k) • (A * A) := by
        simp only [mul_add, mul_smul_comm, mul_one]
        rw [two_mul, add_smul]
        abel
  have h2 : B * B * (A * B) = A * B * (B * B) + (2 * k) • (B * B) := by
    calc B * B * (A * B) = B * (B * A) * B := by noncomm_ring
      _ = B * (A * B + k • 1) * B := by rw [r]
      _ = (B * A) * B * B + k • (B * B) := by
        simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, mul_assoc]
      _ = (A * B + k • 1) * B * B + k • (B * B) := by rw [r]
      _ = A * B * (B * B) + (2 * k) • (B * B) := by
        simp only [add_mul, smul_mul_assoc, one_mul, mul_assoc]
        rw [two_mul, add_smul]
        abel
  have hsplit : (A * A + B * B) * (A * B) - A * B * (A * A + B * B) =
      A * A * (A * B) + B * B * (A * B) - A * B * (A * A) - A * B * (B * B) := by
    noncomm_ring
  rw [hsplit, h1, h2, smul_sub]
  abel

end RingIdentities

/-! ## The canonical relation and the oscillator triple -/

/-- The canonical relation `∂ x = 1 + x ∂` on `𝓢(ℝ, ℂ)`. -/
theorem ccmOscillator_deriv_mul_mulX :
    derivSCLM * mulXCLM = 1 + mulXCLM * derivSCLM := by
  ext1 f
  rw [mul_apply_eq_comp, add_apply, one_apply_eq_self, mul_apply_eq_comp]
  exact derivSCLM_mulXCLM f

/-- Dilation generator `H = x ∂ + 1/2`. -/
def ccmOscillatorH : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := mulXCLM * derivSCLM + (2⁻¹ : ℂ) • 1

/-- `E = -iπ x²`. -/
def ccmOscillatorE : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := (-((π : ℂ) * I)) • (mulXCLM * mulXCLM)

/-- `F = -(i/4π) ∂²`. -/
def ccmOscillatorF : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := (-(I / (4 * π))) • (derivSCLM * derivSCLM)

/-- `H` is nonzero: on the Gaussian it takes the value `1/2` at the origin. -/
theorem ccmOscillatorH_ne_zero : ccmOscillatorH ≠ 0 := by
  intro h
  have h0 := congrArg (fun T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) => T gaussianSchwartz 0) h
  simp only [ccmOscillatorH, add_apply, mul_apply_eq_comp, smul_apply, one_apply_eq_self,
    zero_apply, mulXCLM_apply, gaussianSchwartz_apply] at h0
  simp [gaussReal] at h0

/-- **The oscillator `sl₂`-triple.**  `(H, E, F)` satisfies `[E,F] = H`, `[H,E] = 2E`,
`[H,F] = -2F` on `𝓢(ℝ, ℂ)`. -/
theorem ccmOscillator_isSl2Triple : IsSl2Triple ccmOscillatorH ccmOscillatorE ccmOscillatorF := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have r := ccmOscillator_deriv_mul_mulX
  refine ⟨ccmOscillatorH_ne_zero, ?_, ?_, ?_⟩
  · rw [Ring.lie_def, ccmOscillatorE, ccmOscillatorF, ccmOscillatorH, ccmCommutator_smul_smul,
      ccmCanonical_commutator_xx_dd _ _ r]
    have hc : (-((π : ℂ) * I)) * (-(I / (4 * π))) = -(1 / 4 : ℂ) := by
      have e : (-((π : ℂ) * I)) * (-(I / (4 * π))) = (I * I) * ((π : ℂ) / (4 * π)) := by ring
      rw [e, I_mul_I, show (π : ℂ) / (4 * π) = 1 / 4 by field_simp]
      ring
    rw [hc, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]
    module
  · rw [Ring.lie_def, ccmOscillatorE, ccmOscillatorH, ccmCommutator_add_smul_one,
      ccmCommutator_smul_right, ccmCanonical_commutator_xd_xx _ _ r, smul_comm]
  · rw [Ring.lie_def, ccmOscillatorF, ccmOscillatorH, ccmCommutator_add_smul_one,
      ccmCommutator_smul_right, ccmCanonical_commutator_xd_dd _ _ r, smul_neg, smul_comm]

/-! ## The CCM elements `J`, `N` and their commutator -/

/-- The CCM Jacobi element `J = (8π)⁻¹ (A² + B²)` with `A = 2πx - ∂`, `B = 2πx + ∂`. -/
def ccmOscillatorJacobi : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  ((8 * π : ℂ))⁻¹ • (creationCLM * creationCLM + annihilationCLM * annihilationCLM)

/-- The CCM number element `N = (8π)⁻¹ A B`. -/
def ccmOscillatorNumber : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  ((8 * π : ℂ))⁻¹ • (creationCLM * annihilationCLM)

theorem ccmOscillator_creation_eq :
    creationCLM = (2 * (π : ℂ)) • mulXCLM - derivSCLM := rfl

theorem ccmOscillator_annihilation_eq :
    annihilationCLM = (2 * (π : ℂ)) • mulXCLM + derivSCLM := rfl

/-- `B A = A B + 4π` as an operator identity. -/
theorem ccmOscillator_annihilation_mul_creation :
    annihilationCLM * creationCLM = creationCLM * annihilationCLM + (4 * (π : ℂ)) • 1 := by
  ext1 f
  have h := annihilationCLM_creationCLM_sub f
  rw [sub_eq_iff_eq_add] at h
  rw [mul_apply_eq_comp, add_apply, mul_apply_eq_comp, smul_apply, one_apply_eq_self, h,
    add_comm]

/-- **`J = i(E + F) = πx² + ∂²/(4π)`.** -/
theorem ccmOscillatorJacobi_eq : ccmOscillatorJacobi = I • (ccmOscillatorE + ccmOscillatorF) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hE : I * -((π : ℂ) * I) = π := by
    have e : I * -((π : ℂ) * I) = -(I * I) * π := by ring
    rw [e, I_mul_I]
    ring
  have hF : I * -(I / (4 * (π : ℂ))) = (4 * π : ℂ)⁻¹ := by
    have e : I * -(I / (4 * (π : ℂ))) = -(I * I) * (4 * π : ℂ)⁻¹ := by ring
    rw [e, I_mul_I]
    ring
  rw [ccmOscillatorJacobi, ccmOscillatorE, ccmOscillatorF]
  conv_rhs => rw [smul_add, smul_smul, smul_smul, hE, hF]
  rw [ccmOscillator_creation_eq, ccmOscillator_annihilation_eq]
  simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_add, smul_sub]
  match_scalars <;> field_simp <;> ring

/-- **`N = (i/2)(E - F) - 1/4`**, using `∂ x = 1 + x ∂`. -/
theorem ccmOscillatorNumber_eq :
    ccmOscillatorNumber = (I / 2) • (ccmOscillatorE - ccmOscillatorF) - (4⁻¹ : ℂ) • 1 := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hE : I / 2 * -((π : ℂ) * I) = π / 2 := by
    have e : I / 2 * -((π : ℂ) * I) = -(I * I) * (π / 2) := by ring
    rw [e, I_mul_I]
    ring
  have hF : I / 2 * -(I / (4 * (π : ℂ))) = (8 * π : ℂ)⁻¹ := by
    have e : I / 2 * -(I / (4 * (π : ℂ))) = -(I * I) * (8 * π : ℂ)⁻¹ := by ring
    rw [e, I_mul_I]
    ring
  rw [ccmOscillatorNumber, ccmOscillatorE, ccmOscillatorF]
  conv_rhs => rw [smul_sub, smul_smul, smul_smul, hE, hF]
  rw [ccmOscillator_creation_eq, ccmOscillator_annihilation_eq]
  simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_add, smul_sub, ccmOscillator_deriv_mul_mulX]
  match_scalars <;> field_simp <;> ring

/-- `B² - A² = 8π x ∂ + 4π`. -/
theorem ccmOscillator_annihilationSq_sub_creationSq :
    annihilationCLM * annihilationCLM - creationCLM * creationCLM =
      (8 * (π : ℂ)) • (mulXCLM * derivSCLM) + (4 * (π : ℂ)) • 1 := by
  rw [ccmOscillator_creation_eq, ccmOscillator_annihilation_eq]
  simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    ccmOscillator_deriv_mul_mulX, smul_add]
  match_scalars <;> ring

/-- **`[J, N] = H`**: the CCM commutator is the dilation generator `x ∂ + 1/2`. -/
theorem ccmOscillator_lie_jacobi_number :
    ⁅ccmOscillatorJacobi, ccmOscillatorNumber⁆ = ccmOscillatorH := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Ring.lie_def, ccmOscillatorJacobi, ccmOscillatorNumber, ccmCommutator_smul_smul,
    ccmLadder_commutator_sumSq_mul _ _ _ ccmOscillator_annihilation_mul_creation,
    ccmOscillator_annihilationSq_sub_creationSq, ccmOscillatorH, smul_smul, smul_add, smul_smul,
    smul_smul]
  match_scalars <;> field_simp <;> ring

/-! ## The normalized Hermite functions -/

/-- `L²`-norm of the `k`-th Hermite function. -/
def ccmHermiteNorm (k : ℕ) : ℝ := ‖(hermiteSchwartz k).toLp 2 volume‖

theorem ccmHermiteNorm_pos (k : ℕ) : 0 < ccmHermiteNorm k :=
  norm_pos_iff.mpr (hermiteSchwartz_toLp_ne_zero k)

theorem ccmHermiteNorm_sq_succ (k : ℕ) :
    ccmHermiteNorm (k + 1) ^ 2 = ((k : ℝ) + 1) / π * ccmHermiteNorm k ^ 2 := by
  have h1 := inner_hermiteSchwartz_toLp (k + 1) (k + 1)
  have h0 := inner_hermiteSchwartz_toLp k k
  rw [inner_self_eq_norm_sq_to_K] at h1 h0
  rw [schwartzPair_hermiteSchwartz_self_succ, ← h0] at h1
  unfold ccmHermiteNorm
  have h2 : ((‖(hermiteSchwartz (k + 1)).toLp 2 volume‖ ^ 2 : ℝ) : ℂ) =
      ((((k : ℝ) + 1) / π * ‖(hermiteSchwartz k).toLp 2 volume‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact h1
  exact_mod_cast h2

/-- Ratio `ρ_k = √((k+1)/π)` of consecutive Hermite norms. -/
def ccmHermiteRatio (k : ℕ) : ℝ := Real.sqrt (((k : ℝ) + 1) / π)

theorem ccmHermiteRatio_pos (k : ℕ) : 0 < ccmHermiteRatio k := by
  unfold ccmHermiteRatio
  apply Real.sqrt_pos.mpr
  positivity

theorem ccmHermiteRatio_sq (k : ℕ) : ccmHermiteRatio k ^ 2 = ((k : ℝ) + 1) / π := by
  unfold ccmHermiteRatio
  rw [Real.sq_sqrt (by positivity)]

theorem ccmHermiteNorm_succ (k : ℕ) :
    ccmHermiteNorm (k + 1) = ccmHermiteRatio k * ccmHermiteNorm k := by
  have h := ccmHermiteNorm_sq_succ k
  rw [← ccmHermiteRatio_sq, ← mul_pow] at h
  exact (pow_left_inj₀ (ccmHermiteNorm_pos _).le
    (mul_pos (ccmHermiteRatio_pos k) (ccmHermiteNorm_pos k)).le two_ne_zero).mp h

/-- `L²`-normalized Hermite function `ĥ_k` as a Schwartz map. -/
def ccmHermiteUnit (k : ℕ) : 𝓢(ℝ, ℂ) := ((ccmHermiteNorm k : ℂ))⁻¹ • hermiteSchwartz k

/-- Ladder coefficient `α_k = 2π √((k+1)/π)`. -/
def ccmHermiteLadder (k : ℕ) : ℝ := 2 * π * ccmHermiteRatio k

/-- `A ĥ_k = α_k ĥ_{k+1}`. -/
theorem creationCLM_ccmHermiteUnit (k : ℕ) :
    creationCLM (ccmHermiteUnit k) = (ccmHermiteLadder k : ℂ) • ccmHermiteUnit (k + 1) := by
  have hN := ccmHermiteNorm_pos k
  have hρ := ccmHermiteRatio_pos k
  rw [ccmHermiteUnit, map_smul, creationCLM_hermiteSchwartz, ccmHermiteUnit, smul_smul,
    smul_smul, ccmHermiteNorm_succ, ccmHermiteLadder]
  congr 1
  have hN' : (ccmHermiteNorm k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have hρ' : (ccmHermiteRatio k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  push_cast
  field_simp

/-- `B ĥ_{k+1} = α_k ĥ_k`. -/
theorem annihilationCLM_ccmHermiteUnit_succ (k : ℕ) :
    annihilationCLM (ccmHermiteUnit (k + 1)) = (ccmHermiteLadder k : ℂ) • ccmHermiteUnit k := by
  have hN := ccmHermiteNorm_pos k
  have hρ := ccmHermiteRatio_pos k
  have hsq := ccmHermiteRatio_sq k
  rw [ccmHermiteUnit, map_smul, annihilationCLM_hermiteSchwartz, ccmHermiteUnit, smul_smul,
    smul_smul, ccmHermiteNorm_succ, ccmHermiteLadder]
  congr 1
  have hN' : (ccmHermiteNorm k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have hρ' : (ccmHermiteRatio k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hk : ((k : ℂ) + 1) = (π : ℂ) * (ccmHermiteRatio k : ℂ) ^ 2 := by
    have : ((k : ℝ) + 1) = π * ccmHermiteRatio k ^ 2 := by
      rw [hsq]; field_simp
    exact_mod_cast this
  push_cast
  rw [hk]
  field_simp

/-- `B ĥ_0 = 0`. -/
theorem annihilationCLM_ccmHermiteUnit_zero : annihilationCLM (ccmHermiteUnit 0) = 0 := by
  rw [ccmHermiteUnit, map_smul, annihilationCLM_hermiteSchwartz_zero, smul_zero]

/-- The metaplectic Jacobi coefficient as `(8π)⁻¹ α_{2n} α_{2n+1}`. -/
theorem ccmHermiteLadder_even_mul (n : ℕ) :
    ((8 * π : ℝ))⁻¹ * (ccmHermiteLadder (2 * n) * ccmHermiteLadder (2 * n + 1)) =
      (ccmMetaplecticJacobiCoefficient n : ℝ) := by
  have hπ : 0 < π := Real.pi_pos
  have hl : 0 ≤ ((8 * π : ℝ))⁻¹ * (ccmHermiteLadder (2 * n) * ccmHermiteLadder (2 * n + 1)) := by
    unfold ccmHermiteLadder
    have := ccmHermiteRatio_pos (2 * n)
    have := ccmHermiteRatio_pos (2 * n + 1)
    positivity
  refine (pow_left_inj₀ hl (ccmMetaplecticJacobiCoefficient n).coe_nonneg
    two_ne_zero).mp ?_
  rw [ccmMetaplecticJacobiCoefficient_sq]
  simp only [mul_pow, ccmHermiteLadder, ccmHermiteRatio_sq]
  push_cast
  field_simp
  ring

/-- The number coefficient `(8π)⁻¹ α_{2n+1}² = n + 1`. -/
theorem ccmHermiteLadder_odd_sq (n : ℕ) :
    ((8 * π : ℝ))⁻¹ * (ccmHermiteLadder (2 * n + 1) * ccmHermiteLadder (2 * n + 1)) =
      (n : ℝ) + 1 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [← pow_two, ccmHermiteLadder, mul_pow, ccmHermiteRatio_sq]
  push_cast
  field_simp
  ring

/-- **`J` is the CCM Jacobi operator on the even Hermite functions**, left endpoint. -/
theorem ccmOscillatorJacobi_hermiteUnit_zero :
    ccmOscillatorJacobi (ccmHermiteUnit 0) =
      ((ccmMetaplecticJacobiCoefficient 0 : ℝ) : ℂ) • ccmHermiteUnit 2 := by
  rw [ccmOscillatorJacobi, smul_apply, add_apply,
    mul_apply_eq_comp, mul_apply_eq_comp, annihilationCLM_ccmHermiteUnit_zero, map_zero,
    add_zero, creationCLM_ccmHermiteUnit, map_smul, creationCLM_ccmHermiteUnit, smul_smul,
    smul_smul, ← ccmHermiteLadder_even_mul 0]
  push_cast
  ring_nf

/-- **`J` is the CCM Jacobi operator on the even Hermite functions**, interior indices:
`J ĥ_{2n+2} = a_n ĥ_{2n} + a_{n+1} ĥ_{2n+4}`. -/
theorem ccmOscillatorJacobi_hermiteUnit_succ (n : ℕ) :
    ccmOscillatorJacobi (ccmHermiteUnit (2 * (n + 1))) =
      ((ccmMetaplecticJacobiCoefficient n : ℝ) : ℂ) • ccmHermiteUnit (2 * n) +
        ((ccmMetaplecticJacobiCoefficient (n + 1) : ℝ) : ℂ) •
          ccmHermiteUnit (2 * (n + 1) + 2) := by
  have e1 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
  have e2 : 2 * (n + 1) + 1 = 2 * (n + 1) + 1 := rfl
  rw [ccmOscillatorJacobi, smul_apply, add_apply,
    mul_apply_eq_comp, mul_apply_eq_comp, creationCLM_ccmHermiteUnit, map_smul,
    creationCLM_ccmHermiteUnit, smul_smul]
  rw [show ccmHermiteUnit (2 * (n + 1)) = ccmHermiteUnit ((2 * n + 1) + 1) by rw [e1],
    annihilationCLM_ccmHermiteUnit_succ, map_smul, annihilationCLM_ccmHermiteUnit_succ, smul_smul,
    smul_add, smul_smul, smul_smul, ← ccmHermiteLadder_even_mul n,
    ← ccmHermiteLadder_even_mul (n + 1)]
  rw [show 2 * (n + 1) + 1 + 1 = 2 * (n + 1) + 2 from rfl]
  push_cast
  rw [add_comm]
  congr 2
  ring

/-- **`N` is the number operator on the even Hermite functions:** `N ĥ_{2n} = n ĥ_{2n}`. -/
theorem ccmOscillatorNumber_hermiteUnit (n : ℕ) :
    ccmOscillatorNumber (ccmHermiteUnit (2 * n)) = (n : ℂ) • ccmHermiteUnit (2 * n) := by
  cases n with
  | zero =>
    rw [ccmOscillatorNumber, smul_apply, mul_apply_eq_comp, mul_zero,
      annihilationCLM_ccmHermiteUnit_zero, map_zero, smul_zero, Nat.cast_zero, zero_smul]
  | succ n =>
    rw [ccmOscillatorNumber, smul_apply, mul_apply_eq_comp,
      show 2 * (n + 1) = (2 * n + 1) + 1 by ring, annihilationCLM_ccmHermiteUnit_succ, map_smul,
      creationCLM_ccmHermiteUnit, smul_smul, smul_smul]
    congr 1
    have h := ccmHermiteLadder_odd_sq n
    have h' : ((8 * π : ℂ))⁻¹ * ((ccmHermiteLadder (2 * n + 1) : ℂ) *
        (ccmHermiteLadder (2 * n + 1) : ℂ)) = (n : ℂ) + 1 := by
      exact_mod_cast h
    push_cast
    rw [← h']
    ring

/-- The even normalized Hermite functions are even. -/
theorem ccmHermiteUnit_even (n : ℕ) (x : ℝ) :
    ccmHermiteUnit (2 * n) (-x) = ccmHermiteUnit (2 * n) x := by
  simp only [ccmHermiteUnit, smul_apply, hermiteSchwartz_even]

end RHTower
