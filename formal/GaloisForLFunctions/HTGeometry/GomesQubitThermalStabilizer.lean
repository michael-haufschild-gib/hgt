import GaloisForLFunctions.HTGeometry.GomesQubitOrbitTransport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# The orbit Gram and stabilizers of the actual qubit Gibbs carrier

Applies the mass-kernel/stabilizer construction of Gomes, arXiv:2509.25276v7,
to the corpus's normalized qubit density. Its actual commutator energy certifies
the thermal Gram. Normalization preserves the entire commutant and Gram kernel,
while nonzero parameter scaling preserves symmetry and zero scaling restores it.
The exact characteristic polynomial has transverse value `tanh(radius)^2 / 4`,
strictly below one quarter for every finite carrier.

The tensor-reconstruction problem in arXiv:2607.24901 remains sharp after this
bounded nonlinear normalization: the thermal Gram determines both Hamiltonian
parameters up to simultaneous sign, with no further loss. The full Gibbs state
is maximally mixed, and its Gram vanishes, exactly at the zero Hamiltonian.
All statements include the degenerate carrier and zero thermal scaling.
-/

set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Coefficient of the Hamiltonian in the actual normalized qubit density. -/
def gomesQubitThermalScale (b t : ℝ) : ℝ := Real.tanh (qubitRadius b t)/qubitRadius b t/2

/-- The thermal tangent coefficient vanishes only at the zero Hamiltonian. -/
theorem gomesQubitThermalScale_zero_iff (b t : ℝ) :
    gomesQubitThermalScale b t = 0 ↔ b = 0 ∧ t = 0 := by
  have hc : Real.cosh (qubitRadius b t) ≠ 0 := (Real.cosh_pos (qubitRadius b t)).ne'
  simpa [gomesQubitThermalScale,Real.tanh_eq_sinh_div_cosh,div_eq_zero_iff,
    Real.sinh_eq_zero,hc] using gomesQubitRadius_zero_iff b t

/-- Every actual Gibbs commutator is the corresponding Hamiltonian commutator times one real scalar. -/
theorem gomesQubitDensity_commutator (b t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    qubitDensity b t*A-A*qubitDensity b t =
      (gomesQubitThermalScale b t : ℂ) • (qubitHamiltonian b t*A-A*qubitHamiltonian b t) := by
  rw [gomesQubitDensity_closed]
  simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_add,Matrix.add_mul,
    Matrix.mul_one,Matrix.one_mul,smul_add,smul_sub,smul_smul]
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,gomesQubitThermalScale]
  push_cast
  ring

/-- Normalization preserves the entire commutant, including at the maximally mixed origin. -/
theorem gomesQubitDensity_commutes_iff (b t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    qubitDensity b t*A = A*qubitDensity b t ↔ qubitHamiltonian b t*A = A*qubitHamiltonian b t := by
  constructor
  · intro h
    have hz := sub_eq_zero.mpr h
    rw [gomesQubitDensity_commutator,smul_eq_zero] at hz
    rcases hz with hc | hh
    · have hcR : gomesQubitThermalScale b t = 0 := Complex.ofReal_eq_zero.mp hc
      obtain ⟨rfl,rfl⟩ := (gomesQubitThermalScale_zero_iff b t).mp hcR
      simp [qubitHamiltonian]
    · exact sub_eq_zero.mp hh
  · intro h
    apply sub_eq_zero.mp
    rw [gomesQubitDensity_commutator,sub_eq_zero.mpr h,smul_zero]

/-- Simultaneously scaling coupling and bias scales the actual Hamiltonian. -/
theorem gomesQubitHamiltonian_scale (beta b t : ℝ) :
    qubitHamiltonian (beta*b) (beta*t) = (beta : ℂ) • qubitHamiltonian b t := by
  simp only [qubitHamiltonian,smul_add,smul_smul,Complex.ofReal_mul]

/-- A nonzero thermal scaling preserves all symmetry directions; zero scaling restores the full commutant. -/
theorem gomesQubitDensity_scaled_commutes (beta b t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    qubitDensity (beta*b) (beta*t)*A = A*qubitDensity (beta*b) (beta*t) ↔
      beta = 0 ∨ qubitHamiltonian b t*A = A*qubitHamiltonian b t := by
  rw [gomesQubitDensity_commutes_iff]
  conv_lhs => rw [← sub_eq_zero]
  rw [gomesQubitHamiltonian_scale,Matrix.smul_mul,Matrix.mul_smul,← smul_sub,smul_eq_zero]
  simp only [Complex.ofReal_eq_zero,sub_eq_zero]

/-- The complete symmetry-restoration locus of the thermal qubit carrier. -/
theorem gomesQubitDensity_scaled_full_stabilizer (beta b t : ℝ) :
    (∀ x : Fin 3 → ℝ, qubitDensity (beta*b) (beta*t)*gomesPauliCarrier x =
      gomesPauliCarrier x*qubitDensity (beta*b) (beta*t)) ↔ beta = 0 ∨ (b = 0 ∧ t = 0) := by
  simp only [gomesQubitDensity_scaled_commutes]
  by_cases hb : beta = 0
  · simp [hb]
  · simp only [hb,false_or]
    exact gomesQubitHamiltonian_full_stabilizer b t

/-- The normalized adjoint Gram of the actual thermal density carrier. -/
def gomesQubitDensityMass (b t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (gomesQubitThermalScale b t)^2 • gomesPauliAdjointMass ![b,0,t]

/-- The declared thermal Gram is certified by the actual density commutator energy. -/
theorem gomesQubitDensityMass_commutator_energy (b t : ℝ) (x : Fin 3 → ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      Complex.normSq ((qubitDensity b t*gomesPauliCarrier x-gomesPauliCarrier x*qubitDensity b t) i j)) =
        8*(x ⬝ᵥ (gomesQubitDensityMass b t *ᵥ x)) := by
  rw [gomesQubitDensity_commutator,← gomesQubitHamiltonian_carrier]
  simp only [Matrix.smul_apply,smul_eq_mul,Complex.normSq_mul,Complex.normSq_ofReal]
  simp_rw [← Finset.mul_sum]
  rw [gomesPauliAdjointMass_commutator_energy]
  simp [gomesQubitDensityMass,Matrix.smul_mulVec,dotProduct_smul]
  ring

/-- The thermal Gram and the original Hamiltonian Gram have exactly the same kernel. -/
theorem gomesQubitDensityMass_kernel (b t : ℝ) (x : Fin 3 → ℝ) :
    gomesQubitDensityMass b t *ᵥ x = 0 ↔ gomesPauliAdjointMass ![b,0,t] *ᵥ x = 0 := by
  rw [gomesQubitDensityMass,Matrix.smul_mulVec,smul_eq_zero]
  constructor
  · rintro (h | h)
    · have hs : gomesQubitThermalScale b t = 0 := by nlinarith [sq_nonneg (gomesQubitThermalScale b t)]
      obtain ⟨rfl,rfl⟩ := (gomesQubitThermalScale_zero_iff b t).mp hs
      have hv : (![0,0,0] : Fin 3 → ℝ) = 0 := by ext i; fin_cases i <;> simp
      rw [hv]
      simp [gomesPauliAdjointMass]
    · exact h
  · exact Or.inr

/-- The thermal massless directions are precisely stabilizers of the actual Gibbs state. -/
theorem gomesQubitDensityMass_kernel_iff_commutes (b t : ℝ) (x : Fin 3 → ℝ) :
    gomesQubitDensityMass b t *ᵥ x = 0 ↔
      qubitDensity b t*gomesPauliCarrier x = gomesPauliCarrier x*qubitDensity b t := by
  rw [gomesQubitDensityMass_kernel,gomesQubitHamiltonian_mass_kernel,gomesQubitDensity_commutes_iff]

/-- Thermal normalization converts the squared radius to an exact hyperbolic scale. -/
theorem gomesQubitThermalScale_radius (b t : ℝ) :
    (gomesQubitThermalScale b t)^2*(b^2+t^2) = Real.tanh (qubitRadius b t)^2/4 := by
  have hr2 : qubitRadius b t ^ 2 = b^2+t^2 := by
    simpa [qubitRadius,add_comm] using Real.sq_sqrt (add_nonneg (sq_nonneg t) (sq_nonneg b))
  by_cases hr : qubitRadius b t = 0
  · obtain ⟨rfl,rfl⟩ := (gomesQubitRadius_zero_iff b t).mp hr
    simp [gomesQubitThermalScale,qubitRadius]
  · rw [← hr2]
    dsimp [gomesQubitThermalScale]
    field_simp
    ring

/-- The full thermal Gram characteristic polynomial, with the degenerate case included. -/
theorem gomesQubitDensityMass_characteristic (b t mu : ℝ) :
    Matrix.det (mu • (1 : Matrix (Fin 3) (Fin 3) ℝ)-gomesQubitDensityMass b t) =
      mu*(mu-Real.tanh (qubitRadius b t)^2/4)^2 := by
  rw [← gomesQubitThermalScale_radius]
  simp [gomesQubitDensityMass,gomesPauliAdjointMass,Matrix.det_fin_three,
    Matrix.vecMulVec,dotProduct,Fin.sum_univ_three]
  ring

/-- The thermal Gram scale is uniformly below one quarter at every finite carrier. -/
theorem gomesQubitDensityMass_spectral_bound (b t : ℝ) :
    0 ≤ Real.tanh (qubitRadius b t)^2/4 ∧ Real.tanh (qubitRadius b t)^2/4 < 1/4 := by
  constructor
  · positivity
  · linarith [Real.tanh_sq_lt_one (qubitRadius b t)]

/-- The full thermal Gram trace records the squared radial polarization. -/
theorem gomesQubitDensityMass_trace (b t : ℝ) :
    Matrix.trace (gomesQubitDensityMass b t) = Real.tanh (qubitRadius b t)^2/2 := by
  rw [gomesQubitDensityMass,Matrix.trace_smul,gomesPauliAdjointMass_trace]
  simp [dotProduct,Fin.sum_univ_three]
  have h := gomesQubitThermalScale_radius b t
  nlinarith

/-- Thermal normalization adds no reconstruction ambiguity beyond simultaneous Hamiltonian sign. -/
theorem gomesQubitDensityMass_reconstruction (b t c s : ℝ) :
    gomesQubitDensityMass b t = gomesQubitDensityMass c s ↔
      (b = c ∧ t = s) ∨ (b = -c ∧ t = -s) := by
  constructor
  · intro h
    have ht := congrArg Matrix.trace h
    rw [gomesQubitDensityMass_trace,gomesQubitDensityMass_trace] at ht
    have hb : 0 ≤ Real.tanh (qubitRadius b t) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr (Real.sqrt_nonneg _)) (Real.cosh_pos _).le
    have hc : 0 ≤ Real.tanh (qubitRadius c s) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr (Real.sqrt_nonneg _)) (Real.cosh_pos _).le
    have hr : qubitRadius b t = qubitRadius c s :=
      Real.tanh_injective (by nlinarith)
    have hk : gomesQubitThermalScale b t = gomesQubitThermalScale c s := by
      simp only [gomesQubitThermalScale,hr]
    by_cases hz : gomesQubitThermalScale c s = 0
    · obtain ⟨rfl,rfl⟩ := (gomesQubitThermalScale_zero_iff c s).mp hz
      have hbt := (gomesQubitRadius_zero_iff b t).mp (hr.trans (by simp [qubitRadius]))
      exact Or.inl hbt
    · unfold gomesQubitDensityMass at h
      rw [hk] at h
      have hm := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ =>
        ((gomesQubitThermalScale c s)^2)⁻¹ • A) h
      have hh : gomesPauliAdjointMass ![b,0,t] = gomesPauliAdjointMass ![c,0,s] := by
        simpa [smul_smul,hz] using hm
      exact (gomesQubitMass_reconstruction b t c s).mp hh
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · have hk : gomesQubitThermalScale (-c) (-s) = gomesQubitThermalScale c s := by
        simp [gomesQubitThermalScale,qubitRadius]
      have hm := (gomesQubitMass_reconstruction (-c) (-s) c s).mpr (Or.inr ⟨rfl,rfl⟩)
      simp only [gomesQubitDensityMass,hk,hm]

/-- The thermal orbit Gram vanishes exactly at the zero Hamiltonian. -/
theorem gomesQubitDensityMass_zero_iff (b t : ℝ) :
    gomesQubitDensityMass b t = 0 ↔ b = 0 ∧ t = 0 := by
  have hz : gomesQubitDensityMass 0 0 = 0 := by
    simp [gomesQubitDensityMass,gomesQubitThermalScale,qubitRadius]
  rw [← hz,gomesQubitDensityMass_reconstruction]
  simp

/-- The full Gibbs carrier is maximally mixed exactly at the zero Hamiltonian. -/
theorem gomesQubitDensity_maximally_mixed_iff (b t : ℝ) :
    qubitDensity b t = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔ b = 0 ∧ t = 0 := by
  have hz : qubitDensity 0 0 = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp [gomesQubitDensity_closed,qubitRadius,qubitHamiltonian]
  rw [← hz,gomesQubitDensity_reconstruction]

end GaloisForLFunctions.HTGeometry
