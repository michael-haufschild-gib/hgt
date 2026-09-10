import GaloisForLFunctions.HTGeometry.GomesFiniteFockPolynomialSymbol

/-!
# Every finite Fock symmetry is a polynomial in the actual clock

A finite coefficient vector reconstructs a polynomial symbol. Cyclicity of the
top jet proves that these symbols exhaust the entire matrix commutant, including
the zero-dimensional case. Equality of symbols is precisely equality of their
coefficients below the horizon.
-/

noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The polynomial with a prescribed finite list of coefficients. -/
def gomesFiniteFockCoefficientPolynomial (N : ℕ) (c : Fin N → ℂ) : ℂ[X] :=
  ∑ i : Fin N, Polynomial.monomial i.val (c i)

/-- Every coefficient below the horizon is recovered exactly. -/
theorem gomesFiniteFockCoefficientPolynomial_coeff (N : ℕ) (c : Fin N → ℂ) (j : Fin N) :
    (gomesFiniteFockCoefficientPolynomial N c).coeff j.val = c j := by
  simp only [gomesFiniteFockCoefficientPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  have he (i : Fin N) : i.val = j.val ↔ i = j := Fin.ext_iff.symm
  simp only [he]
  simp

/-- In positive dimensions, a polynomial reconstructed from the observed top column recovers the symmetry. -/
theorem gomesFiniteFockSymbol_reconstruct (n : ℕ) (E : gomesFiniteFockCommutant (n + 1)) :
    gomesFiniteFockSymbolHom (n + 1)
      (gomesFiniteFockCoefficientPolynomial (n + 1) (fun k => (E.val *ᵥ coordVec n) k.rev)) = E := by
  apply gomesFiniteFockCommutant_top_injective n
  funext i
  change (gomesFiniteFockPolynomialHom (n + 1) _ *ᵥ coordVec n) i = _
  rw [gomesFiniteFockPolynomialHom_top, gomesFiniteFockCoefficientPolynomial_coeff,
    Fin.rev_involutive]

/-- Polynomial symbols exhaust the actual full clock commutant, including dimension zero. -/
theorem gomesFiniteFockSymbolHom_surjective (N : ℕ) :
    Function.Surjective (gomesFiniteFockSymbolHom N) := by
  cases N with
  | zero =>
    intro E
    exact ⟨0, Subsingleton.elim _ _⟩
  | succ n =>
    intro E
    exact ⟨_, gomesFiniteFockSymbol_reconstruct n E⟩

/-- The full matrix commutation problem has an unconditional polynomial-symbol classification. -/
theorem gomesFiniteFock_commute_iff_polynomial (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ) :
    Commute M (fockShiftMatrix N) ↔ ∃ p : ℂ[X], gomesFiniteFockPolynomialHom N p = M := by
  constructor
  · intro h
    let E : gomesFiniteFockCommutant N := ⟨M, (gomesFiniteFockCommutant_mem_iff N M).mpr h⟩
    obtain ⟨p, hp⟩ := gomesFiniteFockSymbolHom_surjective N E
    exact ⟨p, congrArg Subtype.val hp⟩
  · rintro ⟨p, rfl⟩
    exact (gomesFiniteFockCommutant_mem_iff _ _).mp (gomesFiniteFockPolynomialHom_mem N p)

/-- Matrix equality records exactly the polynomial coefficients below the finite horizon. -/
theorem gomesFiniteFockPolynomialHom_eq_iff (N : ℕ) (p q : ℂ[X]) :
    gomesFiniteFockPolynomialHom N p = gomesFiniteFockPolynomialHom N q ↔
      ∀ j : Fin N, p.coeff j.val = q.coeff j.val := by
  constructor
  · intro h j
    let z : Fin N := ⟨0, Nat.zero_lt_of_lt j.isLt⟩
    have hh := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M z j) h
    simpa [gomesFiniteFockPolynomialHom_apply, z] using hh
  · intro h
    apply Matrix.ext
    intro i j
    rw [gomesFiniteFockPolynomialHom_apply, gomesFiniteFockPolynomialHom_apply]
    by_cases hij : i.val ≤ j.val
    · rw [if_pos hij, if_pos hij]
      exact h ⟨j.val - i.val, (Nat.sub_le _ _).trans_lt j.isLt⟩
    · rw [if_neg hij, if_neg hij]

/-- Unique finite coefficient vectors classify every commuting matrix. -/
theorem gomesFiniteFock_commute_iff_unique_symbol (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ) :
    Commute M (fockShiftMatrix N) ↔
      ∃! c : Fin N → ℂ, gomesFiniteFockPolynomialHom N (gomesFiniteFockCoefficientPolynomial N c) = M := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := (gomesFiniteFock_commute_iff_polynomial N M).mp h
    refine ⟨fun j => p.coeff j.val, ?_, ?_⟩
    · rw [← hp]
      apply (gomesFiniteFockPolynomialHom_eq_iff N _ _).mpr
      exact gomesFiniteFockCoefficientPolynomial_coeff N _
    · intro c hc
      have hh := (gomesFiniteFockPolynomialHom_eq_iff N _ _).mp (hc.trans hp.symm)
      funext j
      simpa only [gomesFiniteFockCoefficientPolynomial_coeff] using hh j
  · rintro ⟨c, hc, _⟩
    exact (gomesFiniteFock_commute_iff_polynomial N M).mpr ⟨_, hc⟩

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
