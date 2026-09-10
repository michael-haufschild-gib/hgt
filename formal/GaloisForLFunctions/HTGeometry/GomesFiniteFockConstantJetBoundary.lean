import GaloisForLFunctions.HTGeometry.GomesFiniteFockExtraAutomorphisms

/-!
# The sharp low-dimensional boundary for finite Fock Taylor reconstruction

Constant preservation observes exactly one symbol coefficient. In dimension two,
this condition and clock commutation do reconstruct the Taylor family. The
quadratic-shear theorem proves the precise failure from dimension three onward.
-/

noncomputable section
open Matrix Polynomial
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The action of every finite Fock symmetry on constants is its zeroth symbol coefficient. -/
theorem gomesFiniteFockPolynomialHom_constant (n : ℕ) (p : ℂ[X]) (a : ℂ) :
    gomesFiniteFockPolynomialHom (n + 1) p *ᵥ (a • coordVec 0) =
      p.coeff 0 • (a • coordVec 0) := by
  rw [Matrix.mulVec_smul]
  funext i
  change a * (gomesFiniteFockPolynomialHom (n + 1) p *ᵥ coordVec 0) i = _
  change a * (gomesFiniteFockPolynomialHom (n + 1) p *ᵥ coordVec (0 : Fin (n + 1)).val) i = _
  rw [fockMatrix_mulVec_coord, gomesFiniteFockPolynomialHom_apply]
  simp only [Fin.val_zero, Nat.le_zero, Nat.zero_sub, Pi.smul_apply, smul_eq_mul, coordVec]
  by_cases hi : i.val = 0 <;> simp [hi, mul_comm]

/-- Fixing the constant jets is exactly the single normalization p(0)=1. -/
theorem gomesFiniteFockPolynomialHom_fixes_constants_iff (n : ℕ) (p : ℂ[X]) :
    (∀ a : ℂ, gomesFiniteFockPolynomialHom (n + 1) p *ᵥ (a • coordVec 0) = a • coordVec 0) ↔
      p.coeff 0 = 1 := by
  constructor
  · intro h
    have hh := congrArg (fun x : Fin (n + 1) → ℂ => x 0) (h 1)
    rw [gomesFiniteFockPolynomialHom_constant] at hh
    simpa [coordVec] using hh
  · intro h a
    rw [gomesFiniteFockPolynomialHom_constant, h, one_smul]

/-- In dimension two, constant-preserving clock symmetries are exactly the actual Taylor family. -/
theorem gomesFiniteFock_twoJet_taylor_iff (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (Commute M (fockShiftMatrix 2) ∧ ∀ a : ℂ, M *ᵥ (a • coordVec 0) = a • coordVec 0) ↔
      ∃ z : ℂ, M = fockTaylorMatrix 2 z := by
  constructor
  · rintro ⟨hM, hconstant⟩
    obtain ⟨p, rfl⟩ := (gomesFiniteFock_commute_iff_polynomial 2 M).mp hM
    have hp := (gomesFiniteFockPolynomialHom_fixes_constants_iff 1 p).mp hconstant
    refine ⟨p.coeff 1, ?_⟩
    rw [← gomesFiniteFockTaylorSymbol_matrix]
    apply (gomesFiniteFockPolynomialHom_eq_iff 2 _ _).mpr
    intro j
    rw [gomesFiniteFockTaylorSymbol, gomesFiniteFockCoefficientPolynomial_coeff]
    fin_cases j <;> simp [hp]
  · rintro ⟨z, rfl⟩
    rw [← gomesFiniteFockTaylorSymbol_matrix]
    constructor
    · exact (gomesFiniteFockCommutant_mem_iff _ _).mp (gomesFiniteFockPolynomialHom_mem _ _)
    · apply (gomesFiniteFockPolynomialHom_fixes_constants_iff 1 _).mpr
      change (gomesFiniteFockCoefficientPolynomial 2 _).coeff (0 : Fin 2).val = _
      rw [gomesFiniteFockCoefficientPolynomial_coeff]
      simp

/-- The Taylor parameter is unique whenever the two-jet reconstruction succeeds. -/
theorem gomesFiniteFock_twoJet_unique_taylor_iff (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (Commute M (fockShiftMatrix 2) ∧ ∀ a : ℂ, M *ᵥ (a • coordVec 0) = a • coordVec 0) ↔
      ∃! z : ℂ, M = fockTaylorMatrix 2 z := by
  rw [gomesFiniteFock_twoJet_taylor_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, hz, ?_⟩
    intro w hw
    exact (fockTaylorMatrix_faithful 0 w z).mp (hw.symm.trans hz)
  · rintro ⟨z, hz, _⟩
    exact ⟨z, hz⟩

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
