import GaloisForLFunctions.HTGeometry.CausalRayPolarityNonselection
import GaloisForLFunctions.HTGeometry.HiggsMechanism

/-!
# Abelian Higgs mechanisms

Two premise-free `U(1)` models are formalized.

* One complex scalar with Mexican-hat potential has zero set exactly one gauge orbit and trivial
  vacuum stabilizer: the usual completely broken Abelian mechanism.
* The corpus's existing complex Higgs doublet has the same radial potential and complete breaking
  at the north vacuum, but its zero set contains a second gauge-inequivalent vacuum.  The existing
  phase-invariant Lorentz outer-square record distinguishes those vacua.  Thus phase `U(1)` alone
  leaves genuine vacuum moduli in the doublet carrier.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## One complex scalar -/

/-- Mexican-hat potential at unit radius for one complex scalar. -/
def complexAbelianHiggsPotential (z : ℂ) : ℝ :=
  (Complex.normSq z - 1) ^ 2

/-- Complex scalar potential is invariant under `U(1)`. -/
theorem complexAbelianHiggsPotential_gaugeInvariant (u : Circle) (z : ℂ) :
    complexAbelianHiggsPotential (u • z) = complexAbelianHiggsPotential z := by
  have hu : Complex.normSq (u : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Circle.norm_coe]
    norm_num
  change complexAbelianHiggsPotential ((u : ℂ) * z) = complexAbelianHiggsPotential z
  rw [complexAbelianHiggsPotential, complexAbelianHiggsPotential, Complex.normSq_mul, hu, one_mul]

/-- Unit scalar is a zero-energy vacuum. -/
theorem complexAbelianHiggsPotential_one : complexAbelianHiggsPotential 1 = 0 := by
  norm_num [complexAbelianHiggsPotential, Complex.normSq]

/-- Complex scalar potential is nonnegative. -/
theorem complexAbelianHiggsPotential_nonneg (z : ℂ) :
    0 ≤ complexAbelianHiggsPotential z :=
  sq_nonneg _

/-- Standard unit-radius Abelian Higgs mechanism. -/
def complexAbelianHiggsMechanism : HiggsMechanism Circle ℂ where
  vacuum := 1
  potential := complexAbelianHiggsPotential
  gauge_invariant := complexAbelianHiggsPotential_gaugeInvariant
  vacuum_zero := complexAbelianHiggsPotential_one
  potential_nonneg := complexAbelianHiggsPotential_nonneg

/-- `U(1)` symmetry is completely broken at scalar vacuum `1`. -/
theorem complexAbelianHiggs_unbroken_eq_bot :
    complexAbelianHiggsMechanism.unbroken = ⊥ := by
  ext u
  rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    change (u : ℂ) * 1 = 1 at h
    rw [mul_one] at h
    exact Subtype.ext h
  · intro hu
    have hu1 : u = 1 := by simpa using hu
    rw [hu1]
    exact one_smul _ _

/-- Zero-energy scalar configurations are exactly unit-norm configurations. -/
theorem complexAbelianHiggsPotential_eq_zero_iff (z : ℂ) :
    complexAbelianHiggsPotential z = 0 ↔ Complex.normSq z = 1 := by
  rw [complexAbelianHiggsPotential, sq_eq_zero_iff, sub_eq_zero]

/-- Scalar vacuum manifold is exactly one `U(1)` gauge orbit. -/
theorem complexAbelianHiggs_mem_vacuumOrbit_iff (z : ℂ) :
    z ∈ complexAbelianHiggsMechanism.vacuumOrbit ↔ Complex.normSq z = 1 := by
  rw [HiggsMechanism.vacuumOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨u, rfl⟩
    have hu : Complex.normSq (u : ℂ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Circle.norm_coe]
      norm_num
    change Complex.normSq ((u : ℂ) * 1) = 1
    rw [Complex.normSq_mul, hu]
    norm_num [Complex.normSq]
  · intro hz
    have hnorm : ‖z‖ = 1 := by
      rw [Complex.normSq_eq_norm_sq] at hz
      nlinarith [norm_nonneg z]
    let u : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hnorm⟩
    refine ⟨u, ?_⟩
    change (u : ℂ) * 1 = z
    simp [u]

/-! ## Existing complex Higgs doublet -/

/-- Hermitian norm square of the corpus's two-component Higgs spinor. -/
def abelianHiggsSpinorNormSq (H : Fin 2 → ℂ) : ℝ :=
  Complex.normSq (H 0) + Complex.normSq (H 1)

/-- Radial Mexican-hat potential on the existing Higgs-spinor carrier. -/
def abelianHiggsSpinorPotential (H : Fin 2 → ℂ) : ℝ :=
  (abelianHiggsSpinorNormSq H - 1) ^ 2

/-- North-pole Higgs-spinor vacuum. -/
def abelianHiggsSpinorVacuum : Fin 2 → ℂ :=
  ![1, 0]

/-- Orthogonal zero-energy spinor used to detect residual vacuum moduli. -/
def abelianHiggsSpinorOrthogonalVacuum : Fin 2 → ℂ :=
  ![0, 1]

/-- Higgs-spinor norm square is invariant under common phase. -/
theorem abelianHiggsSpinorNormSq_gaugeInvariant (u : Circle) (H : Fin 2 → ℂ) :
    abelianHiggsSpinorNormSq (u • H) = abelianHiggsSpinorNormSq H := by
  have hu : Complex.normSq (u : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Circle.norm_coe]
    norm_num
  change Complex.normSq ((u : ℂ) * H 0) + Complex.normSq ((u : ℂ) * H 1) =
    Complex.normSq (H 0) + Complex.normSq (H 1)
  rw [Complex.normSq_mul, Complex.normSq_mul, hu]
  ring

/-- Higgs-spinor Mexican-hat potential is `U(1)`-invariant. -/
theorem abelianHiggsSpinorPotential_gaugeInvariant (u : Circle) (H : Fin 2 → ℂ) :
    abelianHiggsSpinorPotential (u • H) = abelianHiggsSpinorPotential H := by
  rw [abelianHiggsSpinorPotential, abelianHiggsSpinorPotential,
    abelianHiggsSpinorNormSq_gaugeInvariant]

/-- North-pole spinor has zero potential. -/
theorem abelianHiggsSpinorPotential_vacuum :
    abelianHiggsSpinorPotential abelianHiggsSpinorVacuum = 0 := by
  norm_num [abelianHiggsSpinorPotential, abelianHiggsSpinorNormSq,
    abelianHiggsSpinorVacuum, Complex.normSq]

/-- Higgs-spinor Mexican-hat potential is nonnegative. -/
theorem abelianHiggsSpinorPotential_nonneg (H : Fin 2 → ℂ) :
    0 ≤ abelianHiggsSpinorPotential H :=
  sq_nonneg _

/-- `U(1)` mechanism on the corpus's existing Higgs-spinor carrier. -/
def abelianHiggsSpinorMechanism : HiggsMechanism Circle (Fin 2 → ℂ) where
  vacuum := abelianHiggsSpinorVacuum
  potential := abelianHiggsSpinorPotential
  gauge_invariant := abelianHiggsSpinorPotential_gaugeInvariant
  vacuum_zero := abelianHiggsSpinorPotential_vacuum
  potential_nonneg := abelianHiggsSpinorPotential_nonneg

/-- Common-phase symmetry is completely broken at north-pole spinor. -/
theorem abelianHiggsSpinor_unbroken_eq_bot :
    abelianHiggsSpinorMechanism.unbroken = ⊥ := by
  change MulAction.stabilizer Circle abelianHiggsSpinorVacuum = ⊥
  ext u
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h0 := congrFun h 0
    change (u : ℂ) * 1 = 1 at h0
    rw [mul_one] at h0
    exact Subtype.ext h0
  · intro hu
    have hu1 : u = 1 := by simpa using hu
    rw [hu1]
    exact one_smul _ _

/-- Orthogonal spinor is another zero-energy vacuum. -/
theorem abelianHiggsSpinorOrthogonalVacuum_zero :
    abelianHiggsSpinorPotential abelianHiggsSpinorOrthogonalVacuum = 0 := by
  norm_num [abelianHiggsSpinorPotential, abelianHiggsSpinorNormSq,
    abelianHiggsSpinorOrthogonalVacuum, Complex.normSq]

/-- Orthogonal zero-energy spinor is not gauge-equivalent to selected north vacuum. -/
theorem abelianHiggsSpinorOrthogonalVacuum_not_mem_orbit :
    abelianHiggsSpinorOrthogonalVacuum ∉ abelianHiggsSpinorMechanism.vacuumOrbit := by
  rw [HiggsMechanism.vacuumOrbit, MulAction.mem_orbit_iff]
  rintro ⟨u, hu⟩
  have h0 := congrFun hu 0
  change (u : ℂ) * 1 = 0 at h0
  rw [mul_one] at h0
  have hnorm := Circle.norm_coe u
  rw [h0] at hnorm
  norm_num at hnorm

/-- Existing Lorentz outer-square record is invariant under Abelian gauge action. -/
theorem abelianHiggsSpinorEventMatrix_gaugeInvariant (u : Circle) (H : Fin 2 → ℂ) :
    higgsSpinorEventMatrix (u • H) = higgsSpinorEventMatrix H := by
  apply higgsSpinorEventMatrix_phase_invariant (u : ℂ) H
  have hstar : star (u : ℂ) = ((u⁻¹ : Circle) : ℂ) :=
    (Circle.coe_inv_eq_conj u).symm
  rw [hstar, Circle.coe_inv]
  exact mul_inv_cancel₀ (Circle.coe_ne_zero u)

/-- Gauge-invariant outer-square record distinguishes two zero-energy vacuum orbits. -/
theorem abelianHiggsSpinorVacuum_records_ne :
    higgsSpinorEventMatrix abelianHiggsSpinorVacuum ≠
      higgsSpinorEventMatrix abelianHiggsSpinorOrthogonalVacuum := by
  simpa [abelianHiggsSpinorVacuum, abelianHiggsSpinorOrthogonalVacuum,
    causalPolarityNorthSpinor, causalSpinFlip] using
    higgsSpinorEventMatrix_causalSpinFlip_ne_at_north

end GaloisForLFunctions.HTGeometry
