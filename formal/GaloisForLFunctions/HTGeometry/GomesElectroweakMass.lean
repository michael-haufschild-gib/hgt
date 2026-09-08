import GaloisForLFunctions.HTGeometry.ElectroweakHiggsMechanism

/-!
# Mass geometry of the quaternionic electroweak action

The positive-form kernel argument of Gomes, arXiv:2509.25276v7, Lemma 1,
applies to the existing left-quaternion/right-circle action at its vacuum `1`.
The four coordinates of an event quaternion label two charged directions and
two neutral directions. The coupling-weighted infinitesimal action has one
neutral cancellation direction. Its Gram operator has the charged eigenvalue
`g²`, neutral eigenvalue `g² + h²`, and the exact zero mode, including all
zero-coupling degeneracies. These are algebraic mass coefficients; no choice
of kinetic or vacuum normalization is implicit.
-/

open scoped Quaternion RealInnerProductSpace

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Coupling-weighted infinitesimal left action. -/
def electroweakLeftGenerator (g : ℝ) (x : EventQuaternion) : EventQuaternion :=
  ⟨0, g * x.imJ, g * x.re, g * x.imI⟩

/-- Oppositely charged infinitesimal right-circle action. -/
def electroweakRightGenerator (h : ℝ) (x : EventQuaternion) : EventQuaternion :=
  ⟨0, -(h * x.imK), 0, 0⟩

/-- Infinitesimal displacement of the existing quaternionic vacuum. -/
def electroweakVacuumDisplacement (g h : ℝ) (x : EventQuaternion) : EventQuaternion :=
  electroweakLeftGenerator g x * quaternionHiggsVacuum +
    quaternionHiggsVacuum * electroweakRightGenerator h x

/-- Squared vacuum displacement, the unnormalized Higgs mass quadratic form. -/
def electroweakMassEnergy (g h : ℝ) (x : EventQuaternion) : ℝ :=
  Quaternion.normSq (electroweakVacuumDisplacement g h x)

/-- Gram operator of the coupling-weighted vacuum displacement. -/
def electroweakMassOperator (g h : ℝ) : EventQuaternion →ₗ[ℝ] EventQuaternion where
  toFun x := ⟨g^2 * x.re, g^2 * x.imI,
    g * (g * x.imJ - h * x.imK), -h * (g * x.imJ - h * x.imK)⟩
  map_add' x y := by
    ext <;> simp <;> ring
  map_smul' c x := by
    ext <;> simp <;> ring

/-- Neutral massive direction without dividing by the coupling norm. -/
def electroweakNeutralMassive (g h : ℝ) : EventQuaternion := ⟨0, 0, g, -h⟩

/-- Neutral cancellation direction without dividing by the coupling norm. -/
def electroweakPhotonDirection (g h : ℝ) : EventQuaternion := ⟨0, 0, h, g⟩

theorem electroweakVacuumDisplacement_coordinates (g h : ℝ) (x : EventQuaternion) :
    electroweakVacuumDisplacement g h x =
      ⟨0, g * x.imJ - h * x.imK, g * x.re, g * x.imI⟩ := by
  ext <;> simp [electroweakVacuumDisplacement, electroweakLeftGenerator,
    electroweakRightGenerator, quaternionHiggsVacuum, sub_eq_add_neg]

/-- Positive-form kernel equals the annihilator of the actual vacuum. -/
theorem electroweakMassEnergy_eq_zero_iff (g h : ℝ) (x : EventQuaternion) :
    electroweakMassEnergy g h x = 0 ↔ electroweakVacuumDisplacement g h x = 0 :=
  Quaternion.normSq_eq_zero

theorem electroweakMassEnergy_nonneg (g h : ℝ) (x : EventQuaternion) :
    0 ≤ electroweakMassEnergy g h x := Quaternion.normSq_nonneg

/-- Charged squares and the one neutral square give the entire energy. -/
theorem electroweakMassEnergy_eq (g h : ℝ) (x : EventQuaternion) :
    electroweakMassEnergy g h x =
      g^2 * (x.re^2 + x.imI^2) + (g * x.imJ - h * x.imK)^2 := by
  rw [electroweakMassEnergy, electroweakVacuumDisplacement_coordinates]
  simp only [Quaternion.normSq_def']
  ring

/-- Every degenerate coupling is included in the exact kernel classification. -/
theorem electroweakMassEnergy_kernel (g h : ℝ) (x : EventQuaternion) :
    electroweakMassEnergy g h x = 0 ↔
      g * x.re = 0 ∧ g * x.imI = 0 ∧ g * x.imJ = h * x.imK := by
  rw [electroweakMassEnergy_eq_zero_iff, electroweakVacuumDisplacement_coordinates,
    Quaternion.ext_iff]
  change (0 = 0 ∧ g * x.imJ - h * x.imK = 0 ∧
    g * x.re = 0 ∧ g * x.imI = 0) ↔ _
  simp only [true_and, sub_eq_zero]
  tauto

/-- The displayed linear map is the Gram operator, rather than merely a spectrum ansatz. -/
theorem electroweakMassOperator_gram (g h : ℝ) (x y : EventQuaternion) :
    inner ℝ x (electroweakMassOperator g h y) =
      inner ℝ (electroweakVacuumDisplacement g h x)
        (electroweakVacuumDisplacement g h y) := by
  rw [electroweakVacuumDisplacement_coordinates,
    electroweakVacuumDisplacement_coordinates]
  simp [Quaternion.inner_def, electroweakMassOperator]
  ring

/-- The mass operator is symmetric. -/
theorem electroweakMassOperator_symmetric (g h : ℝ) (x y : EventQuaternion) :
    inner ℝ x (electroweakMassOperator g h y) =
      inner ℝ (electroweakMassOperator g h x) y := by
  calc
    _ = inner ℝ (electroweakVacuumDisplacement g h x)
        (electroweakVacuumDisplacement g h y) := electroweakMassOperator_gram g h x y
    _ = inner ℝ (electroweakVacuumDisplacement g h y)
        (electroweakVacuumDisplacement g h x) := real_inner_comm _ _
    _ = inner ℝ y (electroweakMassOperator g h x) :=
      (electroweakMassOperator_gram g h y x).symm
    _ = _ := real_inner_comm _ _

/-- First charged direction has eigenvalue `g²`. -/
theorem electroweakMassOperator_charged_one (g h : ℝ) :
    electroweakMassOperator g h 1 = g^2 • (1 : EventQuaternion) := by
  ext <;> simp [electroweakMassOperator]

/-- Second charged direction has the same eigenvalue `g²`. -/
theorem electroweakMassOperator_charged_I (g h : ℝ) :
    electroweakMassOperator g h quaternionGaugeIValue = g^2 • quaternionGaugeIValue := by
  ext <;> simp [electroweakMassOperator, quaternionGaugeIValue]

/-- The massive neutral direction has eigenvalue `g² + h²`. -/
theorem electroweakMassOperator_neutral (g h : ℝ) :
    electroweakMassOperator g h (electroweakNeutralMassive g h) =
      (g^2 + h^2) • electroweakNeutralMassive g h := by
  ext <;> simp [electroweakMassOperator, electroweakNeutralMassive] <;> ring

/-- The cancellation direction is exactly massless for every coupling. -/
theorem electroweakMassOperator_photon (g h : ℝ) :
    electroweakMassOperator g h (electroweakPhotonDirection g h) = 0 := by
  ext <;> simp [electroweakMassOperator, electroweakPhotonDirection, mul_comm]

/-- The two neutral directions are orthogonal even at degenerate couplings. -/
theorem electroweakNeutral_orthogonal (g h : ℝ) :
    inner ℝ (electroweakNeutralMassive g h) (electroweakPhotonDirection g h) = 0 := by
  simp [Quaternion.inner_def, electroweakNeutralMassive, electroweakPhotonDirection]
  ring

/-- Division-free neutral resolution: massive and photon coordinates recover the whole plane. -/
theorem electroweakNeutral_resolution (g h z b : ℝ) :
    (g*z - h*b) • electroweakNeutralMassive g h +
      (h*z + g*b) • electroweakPhotonDirection g h =
        (g^2 + h^2) • (⟨0, 0, z, b⟩ : EventQuaternion) := by
  ext <;> simp [electroweakNeutralMassive, electroweakPhotonDirection] <;> ring

/-- Kernel of the operator equals kernel of the vacuum action. -/
theorem electroweakMassOperator_eq_zero_iff (g h : ℝ) (x : EventQuaternion) :
    electroweakMassOperator g h x = 0 ↔ electroweakMassEnergy g h x = 0 := by
  constructor
  · intro hx
    have hh := electroweakMassOperator_gram g h x x
    rw [hx, inner_zero_right, Quaternion.inner_self] at hh
    exact hh.symm
  · intro hx
    obtain ⟨ha, hb, hc⟩ := (electroweakMassEnergy_kernel g h x).mp hx
    ext <;> simp [electroweakMassOperator, hc, pow_two, mul_assoc, ha, hb]

/-- The full residual subgroup is the already constructed diagonal circle. -/
theorem electroweak_unbroken_iff_residual (u : ElectroweakGaugeGroup) :
    u ∈ electroweakHiggsMechanism.unbroken ↔ u = electroweakResidual u.2 := by
  constructor
  · intro hu
    rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff] at hu
    change (u.1.1 : EventQuaternion) * 1 *
      (((u.2 : Circle) : ℂ) : EventQuaternion) = 1 at hu
    apply Prod.ext
    · apply Subtype.ext
      change (u.1.1 : EventQuaternion) = (((u.2⁻¹ : Circle) : ℂ) : EventQuaternion)
      have hz : (((u.2 : Circle) : ℂ) : EventQuaternion) *
          (((u.2⁻¹ : Circle) : ℂ) : EventQuaternion) = 1 := by
        rw [← Quaternion.coeComplex_mul]
        simp
      calc
        _ = (u.1.1 : EventQuaternion) *
          ((((u.2 : Circle) : ℂ) : EventQuaternion) *
            (((u.2⁻¹ : Circle) : ℂ) : EventQuaternion)) := by rw [hz, mul_one]
        _ = _ := by
          have he := congrArg (fun q : EventQuaternion => q *
            (((u.2⁻¹ : Circle) : ℂ) : EventQuaternion)) hu
          simpa only [mul_one, one_mul, mul_assoc] using he
    · rfl
  · intro hu
    rw [hu]
    exact electroweakResidual_mem_unbroken _

/-- The three mass coefficients annihilate the operator by an exact cubic identity. -/
theorem electroweakMassOperator_cubic (g h : ℝ) (x : EventQuaternion) :
    electroweakMassOperator g h (electroweakMassOperator g h
        (electroweakMassOperator g h x)) -
      (2*g^2 + h^2) • electroweakMassOperator g h (electroweakMassOperator g h x) +
      (g^2 * (g^2 + h^2)) • electroweakMassOperator g h x = 0 := by
  ext <;> simp [electroweakMassOperator] <;> ring

/-- The physical vacuum scale adds an exact all-massless branch at zero scale. -/
theorem electroweak_scaled_mass_kernel (v g h : ℝ) (x : EventQuaternion) :
    2 * v^2 * electroweakMassEnergy g h x = 0 ↔
      v = 0 ∨ electroweakVacuumDisplacement g h x = 0 := by
  rw [mul_eq_zero, mul_eq_zero, sq_eq_zero_iff,
    electroweakMassEnergy_eq_zero_iff]
  simp only [two_ne_zero, false_or]

/-- The entire neutral norm is recovered by the massive and cancellation coordinates. -/
theorem electroweakNeutral_energy_resolution (g h z b : ℝ) :
    (g*z - h*b)^2 + (h*z + g*b)^2 = (g^2 + h^2) * (z^2 + b^2) := by
  ring

/-- The neutral massive and massless coordinates form a complete spectral list. -/
theorem electroweakMassOperator_eigenvalues (g h μ : ℝ) :
    (∃ x : EventQuaternion, x ≠ 0 ∧ electroweakMassOperator g h x = μ • x) ↔
      μ = 0 ∨ μ = g^2 ∨ μ = g^2 + h^2 := by
  constructor
  · rintro ⟨x, hx, he⟩
    have hc := electroweakMassOperator_cubic g h x
    rw [he, map_smul, he, map_smul, map_smul, he] at hc
    have hf : (μ * (μ - g^2) * (μ - (g^2+h^2))) • x = 0 := by
      convert hc using 1
      module
    have hz := (smul_eq_zero.mp hf).resolve_right hx
    rcases mul_eq_zero.mp hz with hz | hz
    · rcases mul_eq_zero.mp hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inl (sub_eq_zero.mp hz))
    · exact Or.inr (Or.inr (sub_eq_zero.mp hz))
  · rintro (rfl | rfl | rfl)
    · by_cases hc : g = 0 ∧ h = 0
      · rcases hc with ⟨rfl, rfl⟩
        refine ⟨1, one_ne_zero, ?_⟩
        simpa using electroweakMassOperator_charged_one 0 0
      · refine ⟨electroweakPhotonDirection g h, ?_, ?_⟩
        · intro hz
          apply hc
          have he := Quaternion.ext_iff.mp hz
          exact ⟨he.2.2.2, he.2.2.1⟩
        · simpa using electroweakMassOperator_photon g h
    · exact ⟨1, one_ne_zero, electroweakMassOperator_charged_one g h⟩
    · by_cases hc : g = 0 ∧ h = 0
      · rcases hc with ⟨rfl, rfl⟩
        refine ⟨1, one_ne_zero, ?_⟩
        simpa using electroweakMassOperator_charged_one 0 0
      · refine ⟨electroweakNeutralMassive g h, ?_, electroweakMassOperator_neutral g h⟩
        intro hz
        apply hc
        have he := Quaternion.ext_iff.mp hz
        exact ⟨he.2.2.1, neg_eq_zero.mp he.2.2.2⟩

/-- Exact first-order expansion of the left/right action; the remainder is quadratic. -/
theorem electroweakVacuumDisplacement_action_expansion (g h t : ℝ) (x : EventQuaternion) :
    (1 + t • electroweakLeftGenerator g x) * quaternionHiggsVacuum *
      (1 + t • electroweakRightGenerator h x) =
    quaternionHiggsVacuum + t • electroweakVacuumDisplacement g h x +
      t^2 • (electroweakLeftGenerator g x * quaternionHiggsVacuum *
        electroweakRightGenerator h x) := by
  simp only [electroweakVacuumDisplacement, quaternionHiggsVacuum,
    add_mul, mul_add, one_mul, mul_one, smul_add, smul_mul_assoc,
    mul_smul_comm, smul_smul, pow_two]
  abel

end GaloisForLFunctions.HTGeometry
