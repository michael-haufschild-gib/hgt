import GaloisForLFunctions.HTGeometry.ObserverProfileStability
import GaloisForLFunctions.HTGeometry.ObserverVisibleLocalTimeDimension

/-!
# Invisible coefficient directions preserve the observer's ray exactly

The observer-action map `T_Φ(x) = (I - |Φ⟩⟨Φ|) H(x) Φ` of a real-linear Hermitian
dictionary has a kernel `F_Φ`, the *invisible* coefficient directions.  This file
proves the exact global consequence of membership in that kernel: the generated
Schrödinger evolution multiplies the initial vector by a single unit-modulus
scalar for every time, so the projective ray is preserved exactly and the
endpoint is prepared by the identity circuit.

The chain is:

* `pow_mulVec_of_eigenvector` — powers act on an eigenvector by powers of the
  eigenvalue;
* `exp_mulVec_of_eigenvector` — the matrix exponential acts on an eigenvector by
  the scalar exponential (proved from the exponential series, with the norm
  requirement hidden inside the proof, as in `Mathlib`'s matrix-exponential file);
* `unitaryEvolution_mulVec_of_eigenvector` — the phase form for a real eigenvalue;
* `unitaryEvolution_generatorCombination_mulVec_of_invisible` — a coefficient
  vector killed by the realified observer action generates a pure phase on `Φ`.

No genericity, commutativity, integrability, spectral, or Lie-closure hypothesis
is used, and the conclusion is global in time rather than first order.
-/

open Matrix NormedSpace

namespace QuantumAlg

variable {d : Type*} [Fintype d] [DecidableEq d] {M : ℕ}

section Exponential

/-- Powers of a matrix act on an eigenvector by the corresponding power of the
eigenvalue. -/
theorem pow_mulVec_of_eigenvector {A : Matrix d d ℂ} {ψ : d → ℂ} {c : ℂ}
    (h : A *ᵥ ψ = c • ψ) (k : ℕ) : (A ^ k) *ᵥ ψ = c ^ k • ψ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul,
        pow_succ, mul_comm]

/-- Evaluation of a matrix against a fixed vector, as an additive monoid
homomorphism.  This is the transport used to push the exponential series through
`mulVec`. -/
def mulVecHom (ψ : d → ℂ) : Matrix d d ℂ →+ (d → ℂ) where
  toFun M := M *ᵥ ψ
  map_zero' := by simp
  map_add' A B := Matrix.add_mulVec A B ψ

omit [DecidableEq d] in
@[simp] theorem mulVecHom_apply (ψ : d → ℂ) (A : Matrix d d ℂ) :
    mulVecHom ψ A = A *ᵥ ψ := rfl

omit [DecidableEq d] in
theorem continuous_mulVecHom (ψ : d → ℂ) : Continuous (mulVecHom (d := d) ψ) := by
  apply continuous_pi
  intro i
  simp only [mulVecHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct]
  fun_prop

open scoped Matrix.Norms.Operator in
/-- **Exponential eigenvector law.**  The matrix exponential acts on an
eigenvector by the scalar exponential of the eigenvalue.  The choice of matrix
norm is hidden inside the proof, so the statement is norm-free. -/
theorem exp_mulVec_of_eigenvector {A : Matrix d d ℂ} {ψ : d → ℂ} {c : ℂ}
    (h : A *ᵥ ψ = c • ψ) :
    (NormedSpace.exp A) *ᵥ ψ = Complex.exp c • ψ := by
  have hA : HasSum (fun k : ℕ => ((k.factorial : ℂ))⁻¹ • A ^ k) (NormedSpace.exp A) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have hmap := hA.map (mulVecHom (d := d) ψ) (continuous_mulVecHom ψ)
  have hrw : (fun k : ℕ => (mulVecHom (d := d) ψ) (((k.factorial : ℂ))⁻¹ • A ^ k))
      = fun k : ℕ => (((k.factorial : ℂ))⁻¹ * c ^ k) • ψ := by
    funext k
    simp only [mulVecHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.smul_mulVec,
      pow_mulVec_of_eigenvector h k, smul_smul]
  have hc : HasSum (fun k : ℕ => ((k.factorial : ℂ))⁻¹ * c ^ k) (Complex.exp c) := by
    have := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c
    simpa [smul_eq_mul, Complex.exp_eq_exp_ℂ] using this
  have hc2 : HasSum (fun k : ℕ => (((k.factorial : ℂ))⁻¹ * c ^ k) • ψ)
      (Complex.exp c • ψ) := hc.smul_const ψ
  rw [Function.comp_def] at hmap
  simp only [hrw] at hmap
  exact hmap.unique hc2

end Exponential

section RayPreservation

open GaloisForLFunctions.HTGeometry

/-- **Exact ray preservation.**  If the initial vector is an eigenvector of the
generator with a real eigenvalue, the Schrödinger evolution multiplies it by the
corresponding phase at every time. -/
theorem unitaryEvolution_mulVec_of_eigenvector {H : Matrix d d ℂ} {ψ : d → ℂ} {α : ℝ}
    (h : H *ᵥ ψ = (α : ℂ) • ψ) (s : ℝ) :
    unitaryEvolution H s *ᵥ ψ = Complex.exp (-(Complex.I * (s * α))) • ψ := by
  unfold unitaryEvolution
  refine exp_mulVec_of_eigenvector ?_
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec, h]
  funext i
  simp [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

/-- The scalar produced by ray preservation has modulus one. -/
theorem norm_exp_neg_I_mul_real (s α : ℝ) :
    ‖Complex.exp (-(Complex.I * (s * α)))‖ = 1 := by
  have : -(Complex.I * ((s : ℂ) * (α : ℂ))) = ((-(s * α) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

omit [Fintype d] [DecidableEq d] in
/-- A real-coefficient combination of Hermitian generators is Hermitian. -/
theorem generatorCombination_conjTranspose {h : Fin M → Matrix d d ℂ}
    (hh : ∀ a, (h a)ᴴ = h a) (x : Fin M → ℝ) :
    (generatorCombination h x)ᴴ = generatorCombination h x := by
  simp only [generatorCombination, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hh a]
  simp

omit [DecidableEq d] in
/-- The expectation of a real-coefficient combination of Hermitian generators is
real: it equals the coercion of its own real part. -/
theorem expval_generatorCombination_ofReal_re {ψ : d → ℂ} {h : Fin M → Matrix d d ℂ}
    (hh : ∀ a, (h a)ᴴ = h a) (x : Fin M → ℝ) :
    ((expval ψ (generatorCombination h x)).re : ℂ)
      = expval ψ (generatorCombination h x) :=
  Complex.conj_eq_iff_re.mp
    (expval_conj_self_of_isHermitian (generatorCombination_conjTranspose hh x))

/-- **Invisible directions are exact zero-gate carriers.**  A coefficient vector
in the kernel of the realified observer action generates an evolution which acts
on the initial vector by a single phase, for every time. -/
theorem unitaryEvolution_generatorCombination_mulVec_of_invisible
    {ψ : d → ℂ} {h : Fin M → Matrix d d ℂ} (hh : ∀ a, (h a)ᴴ = h a)
    {x : Fin M → ℝ} (hx : centeredRealification ψ h *ᵥ x = 0) (s : ℝ) :
    unitaryEvolution (generatorCombination h x) s *ᵥ ψ
      = Complex.exp
          (-(Complex.I * (s * (expval ψ (generatorCombination h x)).re))) • ψ := by
  have heig : generatorCombination h x *ᵥ ψ
      = (((expval ψ (generatorCombination h x)).re : ℝ) : ℂ) • ψ := by
    rw [expval_generatorCombination_ofReal_re hh x]
    exact (centeredRealification_mulVec_eq_zero_iff_eigenvector ψ h x).mp hx
  exact unitaryEvolution_mulVec_of_eigenvector heig s

omit [DecidableEq d] in
/-- The expectation of a Hermitian operator is the coercion of its real part. -/
theorem expval_ofReal_re {ψ : d → ℂ} {H : Matrix d d ℂ} (hH : Hᴴ = H) :
    ((expval ψ H).re : ℂ) = expval ψ H :=
  Complex.conj_eq_iff_re.mp (expval_conj_self_of_isHermitian hH)

/-- **Ray preservation from a vanishing centered action.**  A Hermitian generator
whose centered action on the state vanishes evolves the state by a phase. -/
theorem exists_unit_phase_unitaryEvolution_of_centered_eq_zero
    {H : Matrix d d ℂ} (hH : Hᴴ = H) {ψ : d → ℂ} (hc : centered ψ H = 0) (s : ℝ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ unitaryEvolution H s *ᵥ ψ = z • ψ := by
  have heig : H *ᵥ ψ = (((expval ψ H).re : ℝ) : ℂ) • ψ := by
    rw [expval_ofReal_re hH]
    exact (centered_eq_zero_iff ψ H).mp hc
  exact ⟨_, norm_exp_neg_I_mul_real s (expval ψ H).re,
    unitaryEvolution_mulVec_of_eigenvector heig s⟩

/-- Projective form of the previous theorem: the endpoint of an invisible
coefficient direction is a unit-modulus multiple of the initial vector, so the
initial ray is exactly preserved for all time. -/
theorem exists_unit_phase_unitaryEvolution_of_invisible
    {ψ : d → ℂ} {h : Fin M → Matrix d d ℂ} (hh : ∀ a, (h a)ᴴ = h a)
    {x : Fin M → ℝ} (hx : centeredRealification ψ h *ᵥ x = 0) (s : ℝ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ unitaryEvolution (generatorCombination h x) s *ᵥ ψ = z • ψ :=
  ⟨_, norm_exp_neg_I_mul_real s (expval ψ (generatorCombination h x)).re,
    unitaryEvolution_generatorCombination_mulVec_of_invisible hh hx s⟩

end RayPreservation

section Dimension

omit [DecidableEq d] in
/-- **Visible/invisible dimension split.**  The invisible carrier is the kernel of
the realified observer action, and its dimension is the ambient coefficient count
minus the observer-visible local-time dimension. -/
theorem finrank_ker_centeredRealification_add_rank (ψ : d → ℂ)
    (h : Fin M → Matrix d d ℂ) :
    Module.finrank ℝ
        (LinearMap.ker (Matrix.mulVecLin (centeredRealification ψ h)))
      + (centeredRealification ψ h).rank = M := by
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (Matrix.mulVecLin (centeredRealification ψ h))
  rw [Matrix.rank]
  simpa [add_comm] using hrn

end Dimension

end QuantumAlg

namespace QuantumAlg

section LinearForm

variable {d : Type*} [Fintype d]

/-- The centered observer action as a complex-linear map on operators. -/
noncomputable def centeredLinear (ψ : d → ℂ) : Matrix d d ℂ →ₗ[ℂ] (d → ℂ) where
  toFun A := centered ψ A
  map_add' A B := centered_add ψ A B
  map_smul' c A := by
    show centered ψ (c • A) = c • centered ψ A
    rw [centered, centered, Matrix.smul_mulVec, expval_smul, smul_sub, smul_smul,
      smul_eq_mul]

@[simp] theorem centeredLinear_apply (ψ : d → ℂ) (A : Matrix d d ℂ) :
    centeredLinear ψ A = centered ψ A := rfl

end LinearForm

end QuantumAlg
