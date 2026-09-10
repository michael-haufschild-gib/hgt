import GaloisForLFunctions.HTGeometry.GomesFiniteFockAlgebraGeneration
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Exact finite Fock evaluation of arbitrary formal power series

Truncation becomes multiplicative after the actual finite clock is substituted.
This constructs a genuine algebra homomorphism from all formal series, retaining
the zero-dimensional case and the exact finite coefficient observation law.
-/

noncomputable section
open Matrix Polynomial
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The actual clock does not distinguish a polynomial from its truncation at the jet horizon. -/
theorem gomesFiniteFockPolynomialHom_trunc_coe (N : ℕ) (p : ℂ[X]) :
    gomesFiniteFockPolynomialHom N (PowerSeries.trunc N (p : PowerSeries ℂ)) =
      gomesFiniteFockPolynomialHom N p := by
  apply (gomesFiniteFockPolynomialHom_eq_iff N _ _).mpr
  intro j
  rw [PowerSeries.coeff_trunc, if_pos j.isLt, Polynomial.coeff_coe]

/-- Arbitrary formal series evaluated at the literal finite Fock clock. -/
def gomesFiniteFockFormalHom (N : ℕ) : PowerSeries ℂ →ₐ[ℂ] Matrix (Fin N) (Fin N) ℂ where
  toFun F := gomesFiniteFockPolynomialHom N (PowerSeries.trunc N F)
  map_zero' := by rw [map_zero, map_zero]
  map_one' := by
    cases N with
    | zero => exact Subsingleton.elim _ _
    | succ n => rw [PowerSeries.trunc_one, map_one]
  map_add' F G := by rw [map_add, map_add]
  map_mul' F G := by
    calc
      gomesFiniteFockPolynomialHom N (PowerSeries.trunc N (F * G)) =
          gomesFiniteFockPolynomialHom N
            (PowerSeries.trunc N ((PowerSeries.trunc N F : PowerSeries ℂ) *
              (PowerSeries.trunc N G : PowerSeries ℂ))) := by
                rw [PowerSeries.trunc_trunc_mul_trunc]
      _ = gomesFiniteFockPolynomialHom N (PowerSeries.trunc N F * PowerSeries.trunc N G) := by
        rw [← Polynomial.coe_mul, gomesFiniteFockPolynomialHom_trunc_coe]
      _ = _ := map_mul _ _ _
  commutes' a := by
    change gomesFiniteFockPolynomialHom N (PowerSeries.trunc N (PowerSeries.C a)) = _
    cases N with
    | zero => exact Subsingleton.elim _ _
    | succ n =>
      rw [PowerSeries.trunc_C]
      exact (gomesFiniteFockPolynomialHom (n + 1)).commutes a

/-- Formal evaluation extends the already classified polynomial clock map. -/
theorem gomesFiniteFockFormalHom_coe (N : ℕ) (p : ℂ[X]) :
    gomesFiniteFockFormalHom N (p : PowerSeries ℂ) = gomesFiniteFockPolynomialHom N p :=
  gomesFiniteFockPolynomialHom_trunc_coe N p

/-- The formal variable is the literal finite Fock derivative. -/
theorem gomesFiniteFockFormalHom_X (N : ℕ) :
    gomesFiniteFockFormalHom N PowerSeries.X = fockShiftMatrix N := by
  rw [← Polynomial.coe_X, gomesFiniteFockFormalHom_coe, gomesFiniteFockPolynomialHom_X]

/-- Every matrix entry is an exact formal coefficient below the horizon. -/
theorem gomesFiniteFockFormalHom_apply (N : ℕ) (F : PowerSeries ℂ) (i j : Fin N) :
    gomesFiniteFockFormalHom N F i j =
      if i.val ≤ j.val then PowerSeries.coeff (j.val - i.val) F else 0 := by
  change gomesFiniteFockPolynomialHom N (PowerSeries.trunc N F) i j = _
  rw [gomesFiniteFockPolynomialHom_apply, PowerSeries.coeff_trunc,
    if_pos ((Nat.sub_le _ _).trans_lt j.isLt)]

/-- Formal evaluation identifies precisely the coefficient lists below the finite horizon. -/
theorem gomesFiniteFockFormalHom_eq_iff (N : ℕ) (F G : PowerSeries ℂ) :
    gomesFiniteFockFormalHom N F = gomesFiniteFockFormalHom N G ↔
      ∀ j : Fin N, PowerSeries.coeff j.val F = PowerSeries.coeff j.val G := by
  change gomesFiniteFockPolynomialHom N _ = gomesFiniteFockPolynomialHom N _ ↔ _
  rw [gomesFiniteFockPolynomialHom_eq_iff]
  simp only [PowerSeries.coeff_trunc, Fin.is_lt, if_true]

/-- Every formal series yields an actual clock symmetry. -/
theorem gomesFiniteFockFormalHom_mem (N : ℕ) (F : PowerSeries ℂ) :
    gomesFiniteFockFormalHom N F ∈ gomesFiniteFockCommutant N :=
  gomesFiniteFockPolynomialHom_mem N _

/-- Formal clock symbols with codomain the complete actual symmetry algebra. -/
def gomesFiniteFockFormalSymbolHom (N : ℕ) : PowerSeries ℂ →ₐ[ℂ] gomesFiniteFockCommutant N :=
  (gomesFiniteFockFormalHom N).codRestrict _ (gomesFiniteFockFormalHom_mem N)

/-- Formal symbols exhaust the complete matrix commutant without analytic convergence hypotheses. -/
theorem gomesFiniteFockFormalSymbolHom_surjective (N : ℕ) :
    Function.Surjective (gomesFiniteFockFormalSymbolHom N) := by
  intro E
  obtain ⟨p, hp⟩ := gomesFiniteFockSymbolHom_surjective N E
  refine ⟨(p : PowerSeries ℂ), ?_⟩
  apply Subtype.ext
  change gomesFiniteFockFormalHom N (p : PowerSeries ℂ) = E.val
  rw [gomesFiniteFockFormalHom_coe]
  exact congrArg Subtype.val hp

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
