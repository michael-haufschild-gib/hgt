import GaloisForLFunctions.HTGeometry.FiniteReporterGramFisher

/-!
# Transport of invisible directions in Gram information

The null-space rotation mechanism in arXiv:2609.07645, equations (9), (16), and
(17), applies to any changing linear observation map. The exact energy change
contains an interference term and the squared norm of the map increment.
A rank-one rotating panel has constant trace and determinant, yet a formerly
invisible direction acquires precisely the squared sine of the rotation angle.
-/

open scoped InnerProductSpace BigOperators
noncomputable section
namespace HTGeometry

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

/-- Exact energy transport; no blind-direction or small-change assumption is needed. -/
theorem observation_energy_transport (A B : X →ₗ[ℂ] Y) (x : X) :
    ‖B x‖ ^ (2 : ℕ) = ‖A x‖ ^ (2 : ℕ) +
      2 * (inner ℂ (A x) ((B - A) x)).re + ‖(B - A) x‖ ^ (2 : ℕ) := by
  have h := norm_add_sq (𝕜 := ℂ) (A x) ((B - A) x)
  simpa only [LinearMap.sub_apply, add_sub_cancel, RCLike.re_to_complex] using h

/-- Common invisible directions are exactly old invisible directions killed by the increment. -/
theorem observation_common_kernel (A B : X →ₗ[ℂ] Y) :
    LinearMap.ker A ⊓ LinearMap.ker B =
      LinearMap.ker A ⊓ LinearMap.ker (B - A) := by
  ext x
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨ha, by rw [hb, ha, sub_self]⟩
  · rintro ⟨ha, hab⟩
    exact ⟨ha, by simpa [ha] using hab⟩

/-- A complete criterion for preserving every old null direction. -/
theorem observation_kernel_preservation_iff (A B : X →ₗ[ℂ] Y) :
    LinearMap.ker A ≤ LinearMap.ker B ↔
      LinearMap.ker A ≤ LinearMap.ker (B - A) := by
  constructor <;> intro h x hx
  · change B x - A x = 0
    rw [show B x = 0 from h hx, show A x = 0 from hx, sub_self]
  · have he : B x - A x = 0 := h hx
    simpa [show A x = 0 from hx] using he

/-- The energy transport law acts on actual synthesized derivative-clock packets. -/
theorem finiteDerivativeReporter_energy_transport
    (n : ℕ) (f : ℂ → ℂ)
    (A B : (ℂ → ℂ) →ₗ[ℂ] Y) (c : Fin n → ℂ) :
    ‖finiteDerivativeReporterMap n f B c‖ ^ (2 : ℕ) =
      ‖finiteDerivativeReporterMap n f A c‖ ^ (2 : ℕ) +
      2 * (inner ℂ (finiteDerivativeReporterMap n f A c)
        (finiteDerivativeReporterMap n f (B - A) c)).re +
      ‖finiteDerivativeReporterMap n f (B - A) c‖ ^ (2 : ℕ) := by
  exact observation_energy_transport A B (finiteDerivativeReporterPacket c f)

/-- A rotating rank-one real observation panel. -/
def rotatingObservation (t : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := Real.cos t * x 0 + Real.sin t * x 1
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Unit null direction of the panel at angle `t`. -/
def rotatingNullDirection (t : ℝ) : Fin 2 → ℝ := ![-Real.sin t, Real.cos t]

/-- Actual Gram information matrix of the two scalar observation channels. -/
def rotatingInformation (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.gram ℝ ![Real.cos t, Real.sin t]

/-- The exact principal-angle law for an old null direction under the new panel. -/
theorem rotatingObservation_null_transport (s t : ℝ) :
    rotatingObservation t (rotatingNullDirection s) = Real.sin (t - s) := by
  simp only [rotatingObservation, rotatingNullDirection, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sin_sub]
  ring

/-- Every panel has an explicitly constructed null direction. -/
theorem rotatingObservation_null (t : ℝ) :
    rotatingObservation t (rotatingNullDirection t) = 0 := by
  rw [rotatingObservation_null_transport, sub_self, Real.sin_zero]

/-- Information rank does not detect this rotation: its trace is always one. -/
theorem rotatingInformation_trace (t : ℝ) :
    (rotatingInformation t).trace = 1 := by
  simpa [rotatingInformation, Matrix.trace, Matrix.diag, Matrix.gram_apply,
    Fin.sum_univ_two, RCLike.inner_apply, pow_two] using Real.cos_sq_add_sin_sq t

/-- Every information matrix remains singular throughout the rotation. -/
theorem rotatingInformation_det (t : ℝ) :
    (rotatingInformation t).det = 0 := by
  simp [rotatingInformation, Matrix.det_fin_two, Matrix.gram_apply, RCLike.inner_apply]
  ring

/-- Constant eigenvalues: the information matrix is an idempotent rank-one projector. -/
theorem rotatingInformation_idempotent (t : ℝ) :
    rotatingInformation t * rotatingInformation t = rotatingInformation t := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [rotatingInformation, Matrix.mul_apply, Matrix.gram_apply,
      Fin.sum_univ_two, RCLike.inner_apply]
    nlinarith [Real.cos_sq_add_sin_sq t,
      congrArg (fun z : ℝ => z * (Real.sin t * Real.cos t))
        (Real.cos_sq_add_sin_sq t)]

/-- Exact activation energy, also valid for finite rotations. -/
theorem rotatingObservation_null_energy (s t : ℝ) :
    ‖rotatingObservation t (rotatingNullDirection s)‖ ^ (2 : ℕ) = Real.sin (t - s) ^ (2 : ℕ) := by
  rw [rotatingObservation_null_transport, Real.norm_eq_abs, sq_abs]

/-- A quarter turn activates the entire old unit null direction. -/
theorem rotatingObservation_quarter_turn (t : ℝ) :
    ‖rotatingObservation (t + Real.pi / 2) (rotatingNullDirection t)‖ ^ (2 : ℕ) = 1 := by
  rw [rotatingObservation_null_energy]
  simp only [add_sub_cancel_left, Real.sin_pi_div_two, one_pow]

/-- The matrix quadratic form equals the squared physical readout. -/
theorem rotatingInformation_quadratic (t : ℝ) (x : Fin 2 → ℝ) :
    (∑ i, ∑ j, x i * rotatingInformation t i j * x j) =
      rotatingObservation t x ^ (2 : ℕ) := by
  simp [rotatingInformation, rotatingObservation, Fin.sum_univ_two,
    Matrix.gram_apply, RCLike.inner_apply]
  ring

/-- Its information energy is nonnegative for every perturbation. -/
theorem rotatingInformation_nonnegative (t : ℝ) (x : Fin 2 → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * rotatingInformation t i j * x j := by
  rw [rotatingInformation_quadratic]
  exact sq_nonneg _

end HTGeometry
