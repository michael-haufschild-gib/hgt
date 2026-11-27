import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.MarkedMass
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-! # A marked reflection on the orbit of one fixed Hamiltonian -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

private theorem reflection_mul (B V : unitaryGroup I ℂ) (M : Finset I) :
    reflection (B*V) M = B.val * reflection V M * star B.val := by
  change (B.val*V.val)*diagonal _*star (B.val*V.val)=B.val*(V.val*diagonal _*star V.val)*star B.val
  rw [star_mul]
  simp only [mul_assoc]

private theorem evolution_error (H : selfAdjoint (Mat I)) (C : unitaryGroup I ℂ) (M : Finset I)
    (t : ℝ) (z : ℂ) (hz : ‖z‖=1) :
    let B := H.2.isHermitian.eigenvectorUnitary
    ∃ f : I → ℂ, (∀ i, ‖f i‖=1) ∧
      ‖z • unitaryEvolution H.val t-reflection C M‖ = ‖diagonal f-reflection (B⁻¹*C) M‖ := by
  intro B
  let φ i := Complex.exp (-(Complex.I * ((t:ℂ)*(H.2.isHermitian.eigenvalues i:ℂ))))
  refine ⟨z • φ,fun i => ?_,?_⟩
  · change ‖z*Complex.exp _‖=1
    rw [norm_mul,hz,one_mul,Complex.norm_exp]
    simp [Complex.mul_re,Complex.mul_im]
  · have he : reflection C M = B.val*reflection (B⁻¹*C) M*star B.val := by
      rw [←reflection_mul,mul_inv_cancel_left]
    rw [unitaryEvolution_spectral H.2.isHermitian,he,Matrix.diagonal_smul]
    change ‖z • (B.val*diagonal φ*star B.val)-_‖=_
    rw [←Matrix.smul_mul,←Matrix.mul_smul,←Matrix.sub_mul,←Matrix.mul_sub,l2_opNorm_unitary_conj_eq B.property]

/-- Any nonempty marked subspace visited below distance √2 carries
nearly all the mass of at least one energy level. -/
theorem marked_at_every_date (H : selfAdjoint (Mat I)) (C : unitaryGroup I ℂ) (M : Finset I)
    (hm : M.Nonempty) (t : ℝ) (z : ℂ) (hz : ‖z‖=1) :
    let e := ‖z • unitaryEvolution H.val t-reflection C M‖
    Real.sqrt 2 ≤ e ∨ ∃ i, 1-e^2/4 ≤ rowWeight (H.2.isHermitian.eigenvectorUnitary⁻¹*C) M i := by
  intro e
  obtain ⟨f,hf,he⟩ := evolution_error H C M t z hz
  change e=_ at he
  rw [he]
  exact marked_witness _ M hm f hf

/-- At every physical date a projective fit to a marked ray either has
error at least √2 or forces a large eigenstate overlap with that ray. -/
theorem ray_at_every_date (H : selfAdjoint (Mat I)) (C : unitaryGroup I ℂ) (j : I)
    (t : ℝ) (z : ℂ) (hz : ‖z‖=1) :
    let e := ‖z • unitaryEvolution H.val t-reflection C {j}‖
    Real.sqrt 2 ≤ e ∨ ∃ i, 1-e^2/4 ≤ ‖((H.2.isHermitian.eigenvectorUnitary⁻¹*C).val) i j‖^2 := by
  simpa only [rowWeight,sum_singleton] using
    marked_at_every_date H C {j} (singleton_nonempty _) t z hz

/-- For any marked ray, error one tenth requires squared fidelity at
least 399/400 with one eigenstate of the fixed Hamiltonian. -/
theorem tenth_ray_witness (H : selfAdjoint (Mat I)) (C : unitaryGroup I ℂ) (j : I)
    (t : ℝ) (z : ℂ) (hz : ‖z‖=1) :
    1/10 < ‖z • unitaryEvolution H.val t-reflection C {j}‖ ∨
      ∃ i, 399/400 ≤ ‖((H.2.isHermitian.eigenvectorUnitary⁻¹*C).val) i j‖^2 := by
  let e := ‖z • unitaryEvolution H.val t-reflection C {j}‖
  by_cases h : 1/10 < e
  · exact Or.inl h
  right
  rcases ray_at_every_date H C j t z hz with hlarge | ⟨i,hi⟩
  · have hh : (1/10:ℝ) < Real.sqrt 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
    exact (h (hh.trans_le hlarge)).elim
  · have hs := pow_le_pow_left₀ (show 0≤e from norm_nonneg _) (le_of_not_gt h) 2
    exact ⟨i,le_trans (by change (399/400:ℝ) ≤ 1-e^2/4; linarith only [hs]) hi⟩

/-- The closest projective physical date to a marked minority sector
has distance √2. Time zero with scalar i realizes the minimum. -/
theorem least_physical_distance (H : selfAdjoint (Mat I)) (C : unitaryGroup I ℂ) (M : Finset I)
    (hm : M.Nonempty) (half : ∀ i, rowWeight (H.2.isHermitian.eigenvectorUnitary⁻¹*C) M i≤1/2) :
    IsLeast {r : ℝ | ∃ (t : ℝ) (z : ℂ), ‖z‖=1 ∧ r=‖z • unitaryEvolution H.val t-reflection C M‖}
      (Real.sqrt 2) := by
  have hfloor (t : ℝ) (z : ℂ) (hz : ‖z‖=1) : Real.sqrt 2 ≤ ‖z • unitaryEvolution H.val t-reflection C M‖ := by
    obtain ⟨f,hf,he⟩ := evolution_error H C M t z hz
    exact he.symm ▸ marked_minority_floor _ M hm half f hf
  refine ⟨⟨0,Complex.I,Complex.norm_I,le_antisymm (hfloor _ _ Complex.norm_I) ?_⟩,?_⟩
  · simpa only [unitaryEvolution,zero_smul,NormedSpace.exp_zero,smul_one_eq_diagonal_const] using
      imaginary_distance_le C M
  · rintro r ⟨t,z,hz,rfl⟩
    exact hfloor t z hz

#print axioms tenth_ray_witness
#print axioms least_physical_distance
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections
