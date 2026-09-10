import GaloisForLFunctions.HTGeometry.GomesFiniteFockTruncatedKernel
import GaloisForLFunctions.HTGeometry.TruncatedArcCoordinates

/-!
# The full finite Fock symmetry algebra is the existing truncated arc algebra

This is an equivalence with the corpus's literal geometric algebra C[t]/(t^(n+1)),
not a newly postulated carrier. The clock variable, matrix entries, and top-jet
observations all have exact formulas under the equivalence.
-/

noncomputable section
open Matrix Polynomial
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The polynomial clock map descends to the existing geometric truncated arc algebra. -/
def gomesFiniteFockArcHom (n : ℕ) : TruncatedArcAlgebra ℂ n →ₐ[ℂ] gomesFiniteFockCommutant (n + 1) :=
  Ideal.Quotient.liftₐ (truncatedArcIdeal ℂ n) (gomesFiniteFockSymbolHom (n + 1)) (by
    intro p hp
    apply Subtype.ext
    change gomesFiniteFockPolynomialHom (n + 1) p = 0
    apply (gomesFiniteFockPolynomialHom_zero_iff _ _).mpr
    exact Ideal.mem_span_singleton.mp hp)

/-- The quotient map acts by the already classified actual polynomial symbol. -/
theorem gomesFiniteFockArcHom_mk (n : ℕ) (p : ℂ[X]) :
    gomesFiniteFockArcHom n (Ideal.Quotient.mk (truncatedArcIdeal ℂ n) p) =
      gomesFiniteFockSymbolHom (n + 1) p := rfl

/-- Every existing truncated-arc coefficient is detected by the actual finite clock. -/
theorem gomesFiniteFockArcHom_injective (n : ℕ) : Function.Injective (gomesFiniteFockArcHom n) := by
  intro a b h
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply (truncatedArcLinearEquiv ℂ n).injective
  funext j
  rw [truncatedArcLinearEquiv_mk_apply, truncatedArcLinearEquiv_mk_apply]
  exact (gomesFiniteFockPolynomialHom_eq_iff (n + 1) p q).mp (congrArg Subtype.val h) j

/-- Every actual matrix symmetry comes from the existing geometric truncated arc algebra. -/
theorem gomesFiniteFockArcHom_surjective (n : ℕ) : Function.Surjective (gomesFiniteFockArcHom n) := by
  intro E
  obtain ⟨p, hp⟩ := gomesFiniteFockSymbolHom_surjective (n + 1) E
  exact ⟨Ideal.Quotient.mk (truncatedArcIdeal ℂ n) p, hp⟩

/-- Exact algebra equivalence between existing truncated arcs and all finite Fock clock symmetries. -/
def gomesFiniteFockArcEquiv (n : ℕ) : TruncatedArcAlgebra ℂ n ≃ₐ[ℂ] gomesFiniteFockCommutant (n + 1) :=
  AlgEquiv.ofBijective (gomesFiniteFockArcHom n)
    ⟨gomesFiniteFockArcHom_injective n, gomesFiniteFockArcHom_surjective n⟩

/-- Polynomial classes become the transposed Toeplitz matrices already present in the corpus. -/
theorem gomesFiniteFockArcEquiv_mk (n : ℕ) (p : ℂ[X]) :
    (gomesFiniteFockArcEquiv n (Ideal.Quotient.mk (truncatedArcIdeal ℂ n) p)).val =
      (toeplitz (n + 1) p).transpose := rfl

/-- The geometric arc parameter acts as the literal Fock derivative clock. -/
theorem gomesFiniteFockArcEquiv_variable (n : ℕ) :
    (gomesFiniteFockArcEquiv n (Ideal.Quotient.mk (truncatedArcIdeal ℂ n) X)).val =
      fockShiftMatrix (n + 1) :=
  gomesFiniteFockPolynomialHom_X (n + 1)

/-- The full top-jet observation is the reverse of the existing geometric coefficient chart. -/
theorem gomesFiniteFockArcEquiv_top (n : ℕ) (a : TruncatedArcAlgebra ℂ n) (i : Fin (n + 1)) :
    ((gomesFiniteFockArcEquiv n a).val *ᵥ coordVec n) i = truncatedArcLinearEquiv ℂ n a i.rev := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [truncatedArcLinearEquiv_mk_apply]
  exact gomesFiniteFockPolynomialHom_top n p i

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
