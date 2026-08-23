import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Calculus-level dispersive PDE interfaces

These structures package actual time and space derivatives.  Equation predicates therefore cannot
be inhabited by writing down an arbitrary residual tuple: every derivative slot carries its
`HasDerivAt` certificate.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE

/-- Real scalar evolution with three certified spatial derivatives. -/
structure RealEvolutionJet3 where
  u : ℝ → ℝ → ℝ
  ut : ℝ → ℝ → ℝ
  ux : ℝ → ℝ → ℝ
  uxx : ℝ → ℝ → ℝ
  uxxx : ℝ → ℝ → ℝ
  hasDerivAt_time : ∀ (t x : ℝ), HasDerivAt (fun s => u s x) (ut t x) t
  hasDerivAt_space : ∀ (t x : ℝ), HasDerivAt (u t) (ux t x) x
  hasDerivAt_space_one : ∀ (t x : ℝ), HasDerivAt (ux t) (uxx t x) x
  hasDerivAt_space_two : ∀ (t x : ℝ), HasDerivAt (uxx t) (uxxx t x) x

/-- Real scalar evolution with five certified spatial derivatives. -/
structure RealEvolutionJet5 extends RealEvolutionJet3 where
  uxxxx : ℝ → ℝ → ℝ
  uxxxxx : ℝ → ℝ → ℝ
  hasDerivAt_space_three : ∀ (t x : ℝ), HasDerivAt (toRealEvolutionJet3.uxxx t) (uxxxx t x) x
  hasDerivAt_space_four : ∀ (t x : ℝ), HasDerivAt (uxxxx t) (uxxxxx t x) x

/-- Complex scalar evolution with two certified spatial derivatives. -/
structure ComplexEvolutionJet2 where
  u : ℝ → ℝ → ℂ
  ut : ℝ → ℝ → ℂ
  ux : ℝ → ℝ → ℂ
  uxx : ℝ → ℝ → ℂ
  hasDerivAt_time : ∀ (t x : ℝ), HasDerivAt (fun s : ℝ => u s x) (ut t x) t
  hasDerivAt_space : ∀ (t x : ℝ), HasDerivAt (u t) (ux t x) x
  hasDerivAt_space_one : ∀ (t x : ℝ), HasDerivAt (ux t) (uxx t x) x

/-- Two-dimensional real evolution with the derivatives used by expanded KP. -/
structure RealEvolutionJetKP where
  u : ℝ → ℝ → ℝ → ℝ
  ut : ℝ → ℝ → ℝ → ℝ
  ux : ℝ → ℝ → ℝ → ℝ
  uxx : ℝ → ℝ → ℝ → ℝ
  uxxx : ℝ → ℝ → ℝ → ℝ
  uxxxx : ℝ → ℝ → ℝ → ℝ
  utx : ℝ → ℝ → ℝ → ℝ
  uy : ℝ → ℝ → ℝ → ℝ
  uyy : ℝ → ℝ → ℝ → ℝ
  hasDerivAt_time : ∀ t x y, HasDerivAt (fun s => u s x y) (ut t x y) t
  hasDerivAt_space : ∀ t x y, HasDerivAt (fun z => u t z y) (ux t x y) x
  hasDerivAt_space_one : ∀ t x y, HasDerivAt (fun z => ux t z y) (uxx t x y) x
  hasDerivAt_space_two : ∀ t x y, HasDerivAt (fun z => uxx t z y) (uxxx t x y) x
  hasDerivAt_space_three : ∀ t x y, HasDerivAt (fun z => uxxx t z y) (uxxxx t x y) x
  hasDerivAt_time_space : ∀ t x y, HasDerivAt (fun z => ut t z y) (utx t x y) x
  hasDerivAt_transverse : ∀ t x y, HasDerivAt (fun z => u t x z) (uy t x y) y
  hasDerivAt_transverse_one : ∀ t x y, HasDerivAt (fun z => uy t x z) (uyy t x y) y

/-- Real modulation jet for the second-order Shrira--Pesenson equation. -/
structure ShriraPesensonJet where
  s : ℝ → ℝ → ℝ
  sT : ℝ → ℝ → ℝ
  sTT : ℝ → ℝ → ℝ
  sY : ℝ → ℝ → ℝ
  sYY : ℝ → ℝ → ℝ
  sYT : ℝ → ℝ → ℝ
  sTY : ℝ → ℝ → ℝ
  sTYY : ℝ → ℝ → ℝ
  hasDerivAt_time : ∀ T Y, HasDerivAt (fun t => s t Y) (sT T Y) T
  hasDerivAt_time_one : ∀ T Y, HasDerivAt (fun t => sT t Y) (sTT T Y) T
  hasDerivAt_transverse : ∀ T Y, HasDerivAt (s T) (sY T Y) Y
  hasDerivAt_transverse_one : ∀ T Y, HasDerivAt (sY T) (sYY T Y) Y
  hasDerivAt_transverse_time : ∀ T Y, HasDerivAt (fun t => sY t Y) (sYT T Y) T
  hasDerivAt_time_transverse : ∀ T Y, HasDerivAt (sT T) (sTY T Y) Y
  hasDerivAt_time_transverse_one : ∀ T Y, HasDerivAt (sTY T) (sTYY T Y) Y
  mixed_eq : ∀ T Y, sYT T Y = sTY T Y

/-- Korteweg--De Vries equation `uₜ + 6uuₓ + uₓₓₓ = 0`. -/
def SolvesKdV (J : RealEvolutionJet3) : Prop :=
  ∀ t x, J.ut t x + 6 * J.u t x * J.ux t x + J.uxxx t x = 0

/-- Potential KdV equation `φₜ + 3φₓ² + φₓₓₓ = 0`. -/
def SolvesPotentialKdV (J : RealEvolutionJet3) : Prop :=
  ∀ t x, J.ut t x + 3 * J.ux t x ^ 2 + J.uxxx t x = 0

/-- Modified KdV equation `uₜ - 6u²uₓ + uₓₓₓ = 0`. -/
def SolvesModifiedKdV (J : RealEvolutionJet3) : Prop :=
  ∀ t x, J.ut t x - 6 * J.u t x ^ 2 * J.ux t x + J.uxxx t x = 0

/-- Linear Airy equation, the linearized KdV flow. -/
def SolvesAiry (J : RealEvolutionJet3) : Prop :=
  ∀ t x, J.ut t x + J.uxxx t x = 0

/-- Integer-scaled Kawahara equation `uₜ + uuₓ + 52uₓₓₓ - uₓₓₓₓₓ = 0`. -/
def SolvesScaledKawahara (J : RealEvolutionJet5) : Prop :=
  ∀ t x, J.ut t x + J.u t x * J.ux t x + 52 * J.uxxx t x - J.uxxxxx t x = 0

/-- Linear Kawahara equation `uₜ + uₓₓₓ - uₓₓₓₓₓ = 0`. -/
def SolvesLinearKawahara (J : RealEvolutionJet5) : Prop :=
  ∀ t x, J.ut t x + J.uxxx t x - J.uxxxxx t x = 0

/-- Expanded KP equation `(uₜ + 6uuₓ + uₓₓₓ)ₓ + 3σuᵧᵧ = 0`. -/
def SolvesKP (σ : ℝ) (J : RealEvolutionJetKP) : Prop :=
  ∀ t x y, J.utx t x y + 6 * J.ux t x y ^ 2
    + 6 * J.u t x y * J.uxx t x y + J.uxxxx t x y + 3 * σ * J.uyy t x y = 0

/-- Truncated Shrira--Pesenson transverse-modulation equation.

`S_TT + α S_YY + ε(-β S_TYY + γ₁ S_Y S_YT + γ₂ S_T S_YY) = 0`.
-/
def SolvesShriraPesenson (α β γ₁ γ₂ ε : ℝ) (J : ShriraPesensonJet) : Prop :=
  ∀ T Y, J.sTT T Y + α * J.sYY T Y
    + ε * (-β * J.sTYY T Y + γ₁ * J.sY T Y * J.sYT T Y
      + γ₂ * J.sT T Y * J.sYY T Y) = 0

/-- Focusing cubic NLS `iψₜ + ψₓₓ + 2|ψ|²ψ = 0`. -/
def SolvesFocusingNLS (J : ComplexEvolutionJet2) : Prop :=
  ∀ t x, Complex.I * J.ut t x + J.uxx t x
    + ((2 * ‖J.u t x‖ ^ 2 : ℝ) : ℂ) * J.u t x = 0

/-- Defocusing cubic NLS `iψₜ + ψₓₓ - 2|ψ|²ψ = 0`. -/
def SolvesDefocusingNLS (J : ComplexEvolutionJet2) : Prop :=
  ∀ t x, Complex.I * J.ut t x + J.uxx t x
    - ((2 * ‖J.u t x‖ ^ 2 : ℝ) : ℂ) * J.u t x = 0

/-- A scalar field travels rigidly with speed `c`. -/
def IsTravelingWave (c : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, u t x = u 0 (x - c * t)

/-- A two-dimensional field is a line wave when it is independent of the transverse coordinate. -/
def IsLineWave (u : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ t x y, u t x y = u t x 0

end GaloisForLFunctions.HTGeometry.DispersivePDE
