import GaloisForLFunctions.HTGeometry.BuresWasserstein.LyapunovFormPositivity
import GaloisForLFunctions.HTGeometry.FiniteDimensionalOperatorAlbertiLaw
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeQuantum
import Mathlib.Analysis.InnerProductSpace.StarOrder

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

/-!
# Bures–Lyapunov conservative–dissipative evolution

Schaffer–Exl (arXiv:2609.04530) supplies the conservative–dissipative
architecture. The corpus's Bures–Wasserstein Lyapunov-solved form supplies
a distinct, coercive damping operator. Anchors `1 + B†B` and Hamiltonians
`A + A†` discharge positivity and self-adjointness without assumptions.
The actual matrix-exponential flow has an exact Hilbert–Schmidt energy law
and an explicit inverse-cubic exponential decay rate.
-/
open scoped Ring InnerProductSpace NNReal
open ContinuousLinearMap
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance : TopologicalSpace (E →L[ℂ] E) :=
  (inferInstance : NormedAddCommGroup (E →L[ℂ] E)).toUniformSpace.toTopologicalSpace

/-- Strictly positive anchor constructed from an unrestricted raw operator. -/
def buresAnchor (B : E →L[ℂ] E) : E →L[ℂ] E := 1 + star B * B

theorem buresAnchor_positive (B : E →L[ℂ] E) : IsStrictlyPositive (buresAnchor B) := by
  exact (isStrictlyPositive_one (A := E →L[ℂ] E)).add_nonneg (star_mul_self_nonneg B)

/-- Inverse-Lyapunov damping from the Bures–Wasserstein quadratic form. -/
def buresDamping (B X : E →L[ℂ] E) : E →L[ℂ] E :=
  (buresAnchor B)⁻¹ʳ * X * ((buresAnchor B)⁻¹ʳ * (buresAnchor B)⁻¹ʳ) +
    ((buresAnchor B)⁻¹ʳ * (buresAnchor B)⁻¹ʳ) * X * (buresAnchor B)⁻¹ʳ

theorem buresDamping_power (B X : E →L[ℂ] E) :
    RCLike.re (hsInner (buresDamping B X) X) =
      hsNormSq (((buresAnchor B) ^ (-(1/2) : ℝ)) ∘L X ∘L (buresAnchor B)⁻¹ʳ) +
      hsNormSq ((buresAnchor B)⁻¹ʳ ∘L X ∘L ((buresAnchor B) ^ (-(1/2) : ℝ))) :=
  BuresWasserstein.re_hsInner_lyapunovSolution (buresAnchor_positive B)
    (RHTower.finiteDimensional_isHilbertSchmidt X)

theorem buresDamping_lyapunov (B X : E →L[ℂ] E) :
    (buresAnchor B * buresAnchor B) * buresDamping B X *
        (buresAnchor B * buresAnchor B) = buresAnchor B * X + X * buresAnchor B :=
  BuresWasserstein.lyapunov_solution (buresAnchor_positive B)

/-- The canonical anchor has a spectral upper bound determined by the raw coefficient. -/
theorem buresAnchor_upper (B : E →L[ℂ] E) :
    buresAnchor B ≤ (1 + ‖B‖ ^ 2) • (1 : E →L[ℂ] E) := by
  have hb := CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := B)
  rw [Algebra.algebraMap_eq_smul_one] at hb
  simpa only [buresAnchor, add_smul, one_smul, add_comm] using add_le_add_left hb 1

/-- A strict damping rate, with no spectral or positivity premise. -/
theorem buresDamping_coercive (B X : E →L[ℂ] E) :
    (2 * ((1 + ‖B‖ ^ 2)⁻¹ * ((1 + ‖B‖ ^ 2)⁻¹ * (1 + ‖B‖ ^ 2)⁻¹))) * hsNormSq X ≤
      RCLike.re (hsInner (buresDamping B X) X) := by
  exact BuresWasserstein.re_hsInner_lyapunovSolution_lower (buresAnchor_positive B)
    (RHTower.finiteDimensional_isHilbertSchmidt X)
    (by positivity) (buresAnchor_upper B)

/-- Operator and finite matrix Hilbert–Schmidt pairings coincide under the existing star equivalence. -/
theorem finiteOperatorMatrix_hsInner (S T : E →L[ℂ] E) :
    hsInner S T = QuantumAlg.hsInner (RHTower.finiteOperatorMatrixEquiv S)
      (RHTower.finiteOperatorMatrixEquiv T) := by
  have h := opTrace_comp_eq_hsInner S.adjoint T
  rw [adjoint_adjoint] at h
  rw [← h, RHTower.opTrace_eq_finiteOperatorMatrix_trace]
  change Matrix.trace (RHTower.finiteOperatorMatrixEquiv (star S * T)) = _
  rw [map_mul, map_star]
  rfl

/-- A Hamiltonian commutator constructed from an arbitrary raw coefficient. -/
def buresConservative (A X : E →L[ℂ] E) : E →L[ℂ] E :=
  Complex.I • ringCommutator (A + star A) X

theorem buresConservative_power (A X : E →L[ℂ] E) :
    RCLike.re (hsInner (buresConservative A X) X) = 0 := by
  rw [finiteOperatorMatrix_hsInner]
  simp only [buresConservative, map_smul, ringCommutator, map_sub, map_mul,
    map_add, map_star]
  change (QuantumAlg.hsInner (Complex.I • ringCommutator
    (hermitianPart (RHTower.finiteOperatorMatrixEquiv A))
    (RHTower.finiteOperatorMatrixEquiv X)) (RHTower.finiteOperatorMatrixEquiv X)).re = 0
  rw [QuantumAlg.hsInner_conj_symm, Complex.conj_re,
    QuantumAlg.hsInner_smul_right, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, commutator_expectation_im]
  ring

/-- Bures–Lyapunov damping and Hamiltonian motion share one conservative–dissipative field. -/
def buresField (A B X : E →L[ℂ] E) : E →L[ℂ] E :=
  buresConservative A X + (-1 : ℂ) • buresDamping B X

theorem buresField_power (A B X : E →L[ℂ] E) :
    RCLike.re (hsInner (buresField A B X) X) =
      -(hsNormSq (((buresAnchor B) ^ (-(1/2) : ℝ)) ∘L X ∘L (buresAnchor B)⁻¹ʳ) +
        hsNormSq ((buresAnchor B)⁻¹ʳ ∘L X ∘L ((buresAnchor B) ^ (-(1/2) : ℝ)))) := by
  rw [buresField, hsInner_add_left (RHTower.finiteDimensional_isHilbertSchmidt _)
      (RHTower.finiteDimensional_isHilbertSchmidt _) (RHTower.finiteDimensional_isHilbertSchmidt _),
    hsInner_smul_left]
  simp only [map_add, map_neg, map_one, neg_one_mul, buresConservative_power, zero_add]
  rw [buresDamping_power]

theorem buresField_power_nonpos (A B X : E →L[ℂ] E) :
    RCLike.re (hsInner (buresField A B X) X) ≤ 0 := by
  rw [buresField_power]
  exact neg_nonpos.mpr (add_nonneg (hsNormSq_nonneg _) (hsNormSq_nonneg _))

/-- The conservative term leaves the quantitative Bures damping rate unchanged. -/
theorem buresField_coercive (A B X : E →L[ℂ] E) :
    RCLike.re (hsInner (buresField A B X) X) ≤
      -((2 * ((1 + ‖B‖ ^ 2)⁻¹ * ((1 + ‖B‖ ^ 2)⁻¹ * (1 + ‖B‖ ^ 2)⁻¹))) *
        hsNormSq X) := by
  rw [buresField_power, ← buresDamping_power]
  exact neg_le_neg (buresDamping_coercive B X)

/-- There are no nonzero lossless states for this inverse-Lyapunov damping. -/
theorem buresField_lossless_iff (A B X : E →L[ℂ] E) :
    RCLike.re (hsInner (buresField A B X) X) = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hb := buresField_coercive A B X
    have hp : 0 < 2 * ((1 + ‖B‖ ^ 2)⁻¹ *
        ((1 + ‖B‖ ^ 2)⁻¹ * (1 + ‖B‖ ^ 2)⁻¹)) := by positivity
    have hz : hsNormSq X = 0 := by
      have hn := hsNormSq_nonneg X
      rw [h] at hb
      nlinarith
    exact (hsNormSq_eq_zero_iff (RHTower.finiteDimensional_isHilbertSchmidt X)).mp hz
  · rintro rfl
    simp [buresField, buresConservative, buresDamping, ringCommutator, hsInner]

/-- The constructed flow field has exactly one stationary state. -/
theorem buresField_eq_zero_iff (A B X : E →L[ℂ] E) : buresField A B X = 0 ↔ X = 0 := by
  constructor
  · intro h
    apply (buresField_lossless_iff A B X).mp
    rw [h]
    simp [hsInner]
  · rintro rfl
    simp [buresField, buresConservative, buresDamping, ringCommutator]

/-- The finite operator space realized with its Hilbert–Schmidt Hilbert geometry. -/
def finiteOperatorHilbertEquiv : (E →L[ℂ] E) ≃L[ℂ]
    FiniteMatrixHilbert (Fin (Module.finrank ℂ E)) :=
  (RHTower.finiteOperatorMatrixEquiv.toAlgEquiv.toLinearEquiv.trans finiteMatrixHilbertEquiv).toContinuousLinearEquiv

theorem finiteOperatorHilbert_inner (S T : E →L[ℂ] E) :
    ⟪finiteOperatorHilbertEquiv S, finiteOperatorHilbertEquiv T⟫_ℂ = hsInner S T := by
  change ⟪finiteMatrixHilbertEquiv (RHTower.finiteOperatorMatrixEquiv S),
    finiteMatrixHilbertEquiv (RHTower.finiteOperatorMatrixEquiv T)⟫_ℂ = _
  rw [inner_finiteMatrixHilbertEquiv_eq_hsInner, finiteOperatorMatrix_hsInner]

theorem finiteOperatorHilbert_norm_sq (X : E →L[ℂ] E) :
    ‖finiteOperatorHilbertEquiv X‖ ^ 2 = hsNormSq X := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), finiteOperatorHilbert_inner]
  exact hsInner_self_re (RHTower.finiteDimensional_isHilbertSchmidt X)

/-- The constructed field as a continuous linear operator on operator space. -/
def buresGenerator (A B : E →L[ℂ] E) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E) :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℂ) {
    toFun := buresField A B
    map_add' X Y := by
      simp only [buresField, buresConservative, buresDamping, ringCommutator,
        mul_add, add_mul, smul_add, smul_sub]
      abel
    map_smul' c X := by
      simp only [buresField, buresConservative, buresDamping, ringCommutator,
        mul_smul_comm, smul_mul_assoc, smul_sub, smul_add, RingHom.id_apply, smul_comm c]
  }).restrictScalars ℝ

/-- Actual global Bures–Lyapunov evolution. -/
def buresFlow (A B X : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  letI : NormedRing ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) := ContinuousLinearMap.toNormedRing
  (NormedSpace.exp (t • buresGenerator A B) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) X

theorem hasDerivAt_buresFlow (A B X : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (buresFlow A B X) (buresField A B (buresFlow A B X t)) t := by
  have hd := (hasDerivAt_exp_smul_const' (buresGenerator A B) t).clm_apply
    (hasDerivAt_const t X)
  convert hd using 1 <;> first
    | rfl
    | (simp only [buresFlow, mul_apply_eq_comp, map_zero, add_zero]; rfl)

theorem hasDerivAt_buresFlow_energy (A B X : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (fun s => hsNormSq (buresFlow A B X s))
      (2 * RCLike.re (hsInner (buresField A B (buresFlow A B X t))
        (buresFlow A B X t))) t := by
  have hd := (finiteOperatorHilbertEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_buresFlow A B X t)
  have he := hd.norm_sq
  change HasDerivAt (fun s => ‖finiteOperatorHilbertEquiv (buresFlow A B X s)‖ ^ 2)
    (2 * ⟪finiteOperatorHilbertEquiv (buresFlow A B X t),
      finiteOperatorHilbertEquiv (buresField A B (buresFlow A B X t))⟫_ℝ) t at he
  have hi (Y Z : FiniteMatrixHilbert (Fin (Module.finrank ℂ E))) :
      ⟪Y, Z⟫_ℝ = RCLike.re ⟪Y, Z⟫_ℂ := by
    simp only [PiLp.inner_apply, map_sum, real_inner_eq_re_inner ℂ]
  simp only [finiteOperatorHilbert_norm_sq, hi, finiteOperatorHilbert_inner] at he
  rw [hsInner_conj_symm] at he
  simpa only [RCLike.conj_re] using he

theorem buresFlow_energy_antitone (A B X : E →L[ℂ] E) :
    Antitone (fun t => hsNormSq (buresFlow A B X t)) := by
  apply antitone_of_deriv_nonpos
  · exact fun t => (hasDerivAt_buresFlow_energy A B X t).differentiableAt
  · intro t
    rw [(hasDerivAt_buresFlow_energy A B X t).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (buresField_power_nonpos _ _ _)

/-- The explicit inverse-cubic coercive rate of the Bures damping. -/
def buresDecayRate (B : E →L[ℂ] E) : ℝ :=
  2 * ((1 + ‖B‖ ^ 2)⁻¹ * ((1 + ‖B‖ ^ 2)⁻¹ * (1 + ‖B‖ ^ 2)⁻¹))

omit [FiniteDimensional ℂ E] in
theorem buresDecayRate_pos (B : E →L[ℂ] E) : 0 < buresDecayRate B := by
  unfold buresDecayRate
  positivity

/-- An integrating factor turns coercivity into a monotone quantity along the actual flow. -/
theorem buresFlow_scaled_energy_antitone (A B X : E →L[ℂ] E) :
    Antitone (fun t : ℝ => Real.exp (2 * buresDecayRate B * t) * hsNormSq (buresFlow A B X t)) := by
  have hd (t : ℝ) : HasDerivAt
      (fun s : ℝ => Real.exp (2 * buresDecayRate B * s) * hsNormSq (buresFlow A B X s))
      (Real.exp (2 * buresDecayRate B * t) * (2 * buresDecayRate B) * hsNormSq (buresFlow A B X t) +
        Real.exp (2 * buresDecayRate B * t) *
          (2 * RCLike.re (hsInner (buresField A B (buresFlow A B X t)) (buresFlow A B X t)))) t := by
    convert (((hasDerivAt_id t).const_mul (2 * buresDecayRate B)).exp).mul
      (hasDerivAt_buresFlow_energy A B X t) using 1 <;> first | rfl | simp only [id_eq, mul_one]
  apply antitone_of_deriv_nonpos
  · exact fun t => (hd t).differentiableAt
  · intro t
    rw [(hd t).deriv]
    have hb := buresField_coercive A B (buresFlow A B X t)
    change RCLike.re (hsInner (buresField A B (buresFlow A B X t))
      (buresFlow A B X t)) ≤ -(buresDecayRate B * hsNormSq (buresFlow A B X t)) at hb
    have hn : 2 * buresDecayRate B * hsNormSq (buresFlow A B X t) +
        2 * RCLike.re (hsInner (buresField A B (buresFlow A B X t)) (buresFlow A B X t)) ≤ 0 := by
      linarith
    have h := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (2 * buresDecayRate B * t)).le hn
    convert h using 1 <;> first | rfl | ring

/-- Quantitative Hilbert–Schmidt decay for every nonnegative time. -/
theorem buresFlow_energy_decay (A B X : E →L[ℂ] E) (t : ℝ≥0) :
    hsNormSq (buresFlow A B X t) ≤
      Real.exp (-(2 * buresDecayRate B) * (t : ℝ)) * hsNormSq X := by
  have h := buresFlow_scaled_energy_antitone A B X t.coe_nonneg
  have hzero : Real.exp (2 * buresDecayRate B * 0) * hsNormSq (buresFlow A B X 0) =
      hsNormSq X := by simp [buresFlow]
  dsimp only at h
  rw [hzero] at h
  have he : Real.exp (-(2 * buresDecayRate B) * (t : ℝ)) *
      Real.exp (2 * buresDecayRate B * (t : ℝ)) = 1 := by
    rw [← Real.exp_add]
    rw [show -(2 * buresDecayRate B) * (t : ℝ) + 2 * buresDecayRate B * (t : ℝ) = 0 by ring, Real.exp_zero]
  calc
    hsNormSq (buresFlow A B X t) = Real.exp (-(2 * buresDecayRate B) * (t : ℝ)) *
        (Real.exp (2 * buresDecayRate B * (t : ℝ)) * hsNormSq (buresFlow A B X t)) := by
      rw [← mul_assoc, he, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

end
end GaloisForLFunctions.HTGeometry.SchafferExl
