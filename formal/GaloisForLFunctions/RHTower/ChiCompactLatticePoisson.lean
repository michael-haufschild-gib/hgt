import GaloisForLFunctions.HTGeometry.IntegerLatticePoisson

/-!
# Three-dimensional lattice Poisson identities

The compact-support and normally convergent periodization formulas are the
three-dimensional instances of integer-lattice Poisson summation.
-/

noncomputable section
open MeasureTheory

namespace RHTower.BAGTrace.FullPoisson

abbrev X := Fin 3 → ℝ
abbrev Z := Fin 3 → ℤ
abbrev T := UnitAddTorus (Fin 3)

def ip (n : Z) : X := fun i => (n i : ℝ)
def q (x : X) : T := fun i => (x i : UnitAddCircle)

/-- Poisson summation for compactly supported functions with summable Fourier coefficients. -/
theorem poisson {f : X → ℂ} (hc : Continuous f) (hf : HasCompactSupport f)
    (hs : Summable (fun k : Z => ∫ x, UnitAddTorus.mFourier (-k) (q x) * f x)) :
    (∑' k : Z, ∫ x, UnitAddTorus.mFourier (-k) (q x) * f x) =
      ∑' n : Z, f (ip n) :=
  GaloisForLFunctions.HTGeometry.IntegerLatticePoisson.poisson hc hf hs

/-- Poisson summation under absolute normal periodization. -/
theorem poisson_of_summable_translates {f : X → ℂ} (hc : Continuous f) (hf : Integrable f)
    (hn : ∀ R : ℝ, 0 ≤ R → ∃ u : Z → ℝ, Summable u ∧
      ∀ x : X, ‖x‖ ≤ R → ∀ n : Z, ‖f (x + ip n)‖ ≤ u n)
    (hs : Summable (fun k : Z => ∫ x, UnitAddTorus.mFourier (-k) (q x) * f x)) :
    (∑' k : Z, ∫ x, UnitAddTorus.mFourier (-k) (q x) * f x) =
      ∑' n : Z, f (ip n) :=
  GaloisForLFunctions.HTGeometry.IntegerLatticePoisson.poisson_of_summable_translates hc hf hn hs

end RHTower.BAGTrace.FullPoisson
