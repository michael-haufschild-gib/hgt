import GaloisForLFunctions.RepresentationLifting.Spinor.GordonIdentities

/-!
# Complete Dirac matrix decomposition

Pauli coordinates in the four Weyl blocks yield the full scalar, pseudoscalar, vector,
axial-vector and bivector decomposition for the existing gamma matrices. The construction
provides coefficients for every complex spinor matrix. Mean-momentum bivector contraction
has an exact mass-shell defect and reduces to a transfer scalar on Lorentz orbits.
-/

open scoped BigOperators Matrix
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.RepresentationLifting.Spinor
noncomputable section
abbrev WeylBlock := Matrix (Fin 2) (Fin 2) ℂ
abbrev SpinMatrix := Matrix HLSDiracSpinor HLSDiracSpinor ℂ

/-- Coordinates of an arbitrary Weyl block in the identity and three Pauli matrices. -/
def weylCoordinates (A : WeylBlock) : Fin 4 → ℂ :=
  ![(A 0 0 + A 1 1) / 2, (A 0 1 + A 1 0) / 2,
    Complex.I * (A 0 1 - A 1 0) / 2, (A 0 0 - A 1 1) / 2]

theorem weylCoordinates_reconstruct (A : WeylBlock) :
    ∑ μ, weylCoordinates A μ • hlsWeylSigma μ = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four, weylCoordinates, hlsWeylSigma,
      smul_eq_mul] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- Explicit scalar, pseudoscalar, vector, axial-vector and six bivector synthesis. -/
def diracSynthesis (s p : ℂ) (v a : Fin 4 → ℂ) (e b : Fin 3 → ℂ) : SpinMatrix :=
  s • 1 + p • hlsWeylGammaFive +
    (∑ μ, v μ • hlsWeylGamma μ) +
    (∑ μ, a μ • (hlsWeylGamma μ * hlsWeylGammaFive)) +
    e 0 • hlsDiracBivector 0 1 + e 1 • hlsDiracBivector 0 2 +
    e 2 • hlsDiracBivector 0 3 + b 0 • hlsDiracBivector 2 3 +
    b 1 • hlsDiracBivector 3 1 + b 2 • hlsDiracBivector 1 2

private theorem synthesis_blocks (s p : ℂ) (v a : Fin 4 → ℂ) (e b : Fin 3 → ℂ) :
    diracSynthesis s p v a e b = Matrix.fromBlocks
      (∑ μ, (![s - p, b 0 - Complex.I * e 0, b 1 - Complex.I * e 1,
        b 2 - Complex.I * e 2] : Fin 4 → ℂ) μ • hlsWeylSigma μ)
      (∑ μ, (v μ + a μ) • hlsWeylSigma μ)
      (∑ μ, (![v 0 - a 0, -v 1 + a 1, -v 2 + a 2, -v 3 + a 3] : Fin 4 → ℂ) μ • hlsWeylSigma μ)
      (∑ μ, (![s + p, b 0 + Complex.I * e 0, b 1 + Complex.I * e 1,
        b 2 + Complex.I * e 2] : Fin 4 → ℂ) μ • hlsWeylSigma μ) := by
  simp only [diracSynthesis, Fin.sum_univ_four, hlsDiracBivector, hlsWeylGamma,
    hlsWeylGammaFive, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [hlsWeylSigma, hlsWeylBarSigma,
      Matrix.smul_apply, smul_eq_mul] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- Every spinor matrix has the full sixteen-component Dirac decomposition. -/
theorem diracSynthesis_surjective :
    ∀ M : SpinMatrix, ∃ s p v a e b, diracSynthesis s p v a e b = M := by
  intro M
  let A := weylCoordinates (fun i j => M (Sum.inl i) (Sum.inl j))
  let B := weylCoordinates (fun i j => M (Sum.inl i) (Sum.inr j))
  let C := weylCoordinates (fun i j => M (Sum.inr i) (Sum.inl j))
  let D := weylCoordinates (fun i j => M (Sum.inr i) (Sum.inr j))
  refine ⟨(A 0 + D 0) / 2, (D 0 - A 0) / 2,
    ![(B 0 + C 0) / 2, (B 1 - C 1) / 2, (B 2 - C 2) / 2, (B 3 - C 3) / 2],
    ![(B 0 - C 0) / 2, (B 1 + C 1) / 2, (B 2 + C 2) / 2, (B 3 + C 3) / 2],
    ![Complex.I * (A 1 - D 1) / 2, Complex.I * (A 2 - D 2) / 2,
      Complex.I * (A 3 - D 3) / 2],
    ![(A 1 + D 1) / 2, (A 2 + D 2) / 2, (A 3 + D 3) / 2], ?_⟩
  rw [synthesis_blocks]
  have hA : (![ (A 0 + D 0) / 2 - (D 0 - A 0) / 2,
      (A 1 + D 1) / 2 - Complex.I * (Complex.I * (A 1 - D 1) / 2),
      (A 2 + D 2) / 2 - Complex.I * (Complex.I * (A 2 - D 2) / 2),
      (A 3 + D 3) / 2 - Complex.I * (Complex.I * (A 3 - D 3) / 2)] : Fin 4 → ℂ) = A := by
    ext i; fin_cases i <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hA]
  have hdiag : ∀ x y : ℂ, (x + y) / 2 + (y - x) / 2 = y := by intros; ring
  have hcross : ∀ x y : ℂ, (x + y) / 2 + Complex.I * (Complex.I * (x - y) / 2) = y := by
    intros; ring_nf; simp [Complex.I_sq] <;> ring
  have hD : (![ (A 0 + D 0) / 2 + (D 0 - A 0) / 2,
      (A 1 + D 1) / 2 + Complex.I * (Complex.I * (A 1 - D 1) / 2),
      (A 2 + D 2) / 2 + Complex.I * (Complex.I * (A 2 - D 2) / 2),
      (A 3 + D 3) / 2 + Complex.I * (Complex.I * (A 3 - D 3) / 2)] : Fin 4 → ℂ) = D := by
    ext i; fin_cases i <;> simp [hdiag, hcross]
  rw [hD]
  have hB : (fun μ : Fin 4 =>
      (![ (B 0 + C 0) / 2, (B 1 - C 1) / 2, (B 2 - C 2) / 2, (B 3 - C 3) / 2] : Fin 4 → ℂ) μ +
      (![ (B 0 - C 0) / 2, (B 1 + C 1) / 2, (B 2 + C 2) / 2, (B 3 + C 3) / 2] : Fin 4 → ℂ) μ) = B := by
    ext i; fin_cases i <;> simp <;> ring
  simp_rw [show ∀ μ, _ = B μ from congrFun hB]
  have hC : (![ (B 0 + C 0) / 2 - (B 0 - C 0) / 2,
      -((B 1 - C 1) / 2) + (B 1 + C 1) / 2,
      -((B 2 - C 2) / 2) + (B 2 + C 2) / 2,
      -((B 3 - C 3) / 2) + (B 3 + C 3) / 2] : Fin 4 → ℂ) = C := by
    ext i; fin_cases i <;> simp <;> ring
  rw [hC]
  rw [weylCoordinates_reconstruct, weylCoordinates_reconstruct,
    weylCoordinates_reconstruct, weylCoordinates_reconstruct]
  ext i j
  cases i <;> cases j <;> rfl


/-- Contracting a bivector with twice the mean momentum leaves a transfer scalar on shell.
The off-shell error is exactly the difference of the two mass-shell defects. -/
theorem bivectorMean_residual (m : ℝ) (p q : HLSMinkowskiVector) (μ : Fin 4) :
    diracNumerator m q * (bivectorContract (p + q) μ -
      (Complex.I * (hlsMinkowskiCoordinateSign μ * (q μ - p μ) : ℝ)) • 1) *
        diracNumerator m p =
      (Complex.I * (hlsMinkowskiForm p - m ^ 2 : ℝ)) •
        (diracNumerator m q * hlsWeylGamma μ) -
      (Complex.I * (hlsMinkowskiForm q - m ^ 2 : ℝ)) •
        (hlsWeylGamma μ * diracNumerator m p) := by
  have hp := gamma_slash_anticommutator p μ
  have hq := gamma_slash_anticommutator q μ
  have hsum : momentumSlash (p + q) = momentumSlash p + momentumSlash q := by
    simp only [momentumSlash, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
  have hb : bivectorContract (p + q) μ -
      (Complex.I * (hlsMinkowskiCoordinateSign μ * (q μ - p μ) : ℝ)) • 1 =
      Complex.I • (hlsWeylGamma μ * momentumSlash p - momentumSlash q * hlsWeylGamma μ) := by
    rw [bivectorContract_eq, hsum]
    have hs : (Complex.I * (hlsMinkowskiCoordinateSign μ * (q μ - p μ) : ℝ)) • (1 : DiracMatrix) =
        (Complex.I / 2) •
          ((2 * (hlsMinkowskiCoordinateSign μ * q μ : ℝ) : ℂ) • 1 -
            (2 * (hlsMinkowskiCoordinateSign μ * p μ : ℝ) : ℂ) • 1) := by
      push_cast; module
    rw [hs, ← hp, ← hq]
    simp only [mul_add, add_mul]
    module
  rw [hb, diracNumerator, diracNumerator]
  have hid (x y g : DiracMatrix) :
      (y + (m : ℂ) • 1) * (g * x - y * g) * (x + (m : ℂ) • 1) =
        (y + (m : ℂ) • 1) * g * (x * x - (m : ℂ) ^ 2 • 1) -
          (y * y - (m : ℂ) ^ 2 • 1) * g * (x + (m : ℂ) • 1) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, mul_assoc]
    module
  rw [mul_smul_comm, smul_mul_assoc, hid, momentumSlash_square, momentumSlash_square]
  simp only [← sub_smul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul,
    mul_one, one_mul, Complex.ofReal_sub, Complex.ofReal_pow]

/-- The mean-momentum tensor reduction on explicit Lorentz orbits, including zero mass. -/
theorem bivectorMean_lorentzOrbit (m : ℝ) (g h : hlsLorentzGroup) (μ : Fin 4) :
    diracNumerator m (h.1 (hlsRestMomentum m)) *
      bivectorContract (g.1 (hlsRestMomentum m) + h.1 (hlsRestMomentum m)) μ *
        diracNumerator m (g.1 (hlsRestMomentum m)) =
      (Complex.I * (hlsMinkowskiCoordinateSign μ *
        (h.1 (hlsRestMomentum m) μ - g.1 (hlsRestMomentum m) μ) : ℝ)) •
          (diracNumerator m (h.1 (hlsRestMomentum m)) *
            diracNumerator m (g.1 (hlsRestMomentum m))) := by
  have hh := bivectorMean_residual m (g.1 (hlsRestMomentum m))
    (h.1 (hlsRestMomentum m)) μ
  rw [hlsLorentz_preserves_minkowski, hlsLorentz_preserves_minkowski,
    hlsRestMomentum_mass_shell, sub_self] at hh
  simp only [Complex.ofReal_zero, mul_zero, zero_smul, sub_self, mul_sub, sub_mul,
    mul_smul_comm, smul_mul_assoc, mul_one] at hh
  simpa only [mul_sub] using sub_eq_zero.mp hh

#print axioms bivectorMean_residual
#print axioms bivectorMean_lorentzOrbit
#print axioms weylCoordinates_reconstruct
#print axioms diracSynthesis_surjective

end
end GaloisForLFunctions.RepresentationLifting.Spinor
