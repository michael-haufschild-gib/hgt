import GaloisForLFunctions.HTGeometry.ImotoKovasznayFlow
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Taylor--Green fields and exact multiscale interactions

Equations (9)--(13) of Singh--Suresh--Gupta, arXiv:2608.29895, realized
in the existing derivative-certified Navier--Stokes jet type. The decaying
family solves the unsteady momentum equations. Two-mode mixtures remain
incompressible, while their exact vorticity-advection residual detects the
difference of the squared spatial frequencies. The velocity also has an
exact two-feature Kolmogorov--Arnold representation.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry


/-- A translated sine mode of arbitrary real spatial frequency. -/
def taylorGreenSin (k d x : ℝ) : ℝ := Real.sin (k * (x - d))

/-- The corresponding cosine mode. -/
def taylorGreenCos (k d x : ℝ) : ℝ := Real.cos (k * (x - d))

theorem hasDerivAt_taylorGreenSin (k d x : ℝ) :
    HasDerivAt (taylorGreenSin k d) (k * taylorGreenCos k d x) x := by
  have h := (Real.hasDerivAt_sin (k * (x - d))).comp x
    (((hasDerivAt_id x).sub_const d).const_mul k)
  unfold taylorGreenSin taylorGreenCos
  exact h.congr_deriv (by ring)

theorem hasDerivAt_taylorGreenCos (k d x : ℝ) :
    HasDerivAt (taylorGreenCos k d) (-k * taylorGreenSin k d x) x := by
  have h := (Real.hasDerivAt_cos (k * (x - d))).comp x
    (((hasDerivAt_id x).sub_const d).const_mul k)
  unfold taylorGreenCos taylorGreenSin
  exact h.congr_deriv (by ring)

theorem taylorGreenSin_sq_add_cos_sq (k d x : ℝ) :
    taylorGreenSin k d x ^ 2 + taylorGreenCos k d x ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq _

/-- Taylor--Green modes as an actual derivative-certified corpus Navier--Stokes jet.
The pressure differs from the usual double-cosine form only by a constant. -/
def taylorGreenJet (k A dx dy : ℝ) : SteadyNavierStokesJet2 where
  u := fun x y => A * taylorGreenSin k dx x * taylorGreenCos k dy y
  v := fun x y => -A * taylorGreenCos k dx x * taylorGreenSin k dy y
  p := fun x y => -A ^ 2 / 2 *
    (taylorGreenSin k dx x ^ 2 + taylorGreenSin k dy y ^ 2)
  ux := fun x y => A * k * taylorGreenCos k dx x * taylorGreenCos k dy y
  uy := fun x y => -A * k * taylorGreenSin k dx x * taylorGreenSin k dy y
  vx := fun x y => A * k * taylorGreenSin k dx x * taylorGreenSin k dy y
  vy := fun x y => -A * k * taylorGreenCos k dx x * taylorGreenCos k dy y
  px := fun x _y => -A ^ 2 * k * taylorGreenSin k dx x * taylorGreenCos k dx x
  py := fun _x y => -A ^ 2 * k * taylorGreenSin k dy y * taylorGreenCos k dy y
  uxx := fun x y => -k ^ 2 * (A * taylorGreenSin k dx x * taylorGreenCos k dy y)
  uyy := fun x y => -k ^ 2 * (A * taylorGreenSin k dx x * taylorGreenCos k dy y)
  vxx := fun x y => -k ^ 2 * (-A * taylorGreenCos k dx x * taylorGreenSin k dy y)
  vyy := fun x y => -k ^ 2 * (-A * taylorGreenCos k dx x * taylorGreenSin k dy y)
  hasDerivAt_u_x := by
    intro x y
    exact (((hasDerivAt_taylorGreenSin k dx x).const_mul A).mul_const
      (taylorGreenCos k dy y)).congr_deriv (by ring)
  hasDerivAt_u_y := by
    intro x y
    exact ((hasDerivAt_taylorGreenCos k dy y).const_mul
      (A * taylorGreenSin k dx x)).congr_deriv (by ring)
  hasDerivAt_v_x := by
    intro x y
    exact (((hasDerivAt_taylorGreenCos k dx x).const_mul (-A)).mul_const
      (taylorGreenSin k dy y)).congr_deriv (by ring)
  hasDerivAt_v_y := by
    intro x y
    exact ((hasDerivAt_taylorGreenSin k dy y).const_mul
      (-A * taylorGreenCos k dx x)).congr_deriv (by ring)
  hasDerivAt_p_x := by
    intro x y
    exact ((((hasDerivAt_taylorGreenSin k dx x).pow 2).add_const
      (taylorGreenSin k dy y ^ 2)).const_mul (-A ^ 2 / 2)).congr_deriv (by ring)
  hasDerivAt_p_y := by
    intro x y
    exact ((((hasDerivAt_taylorGreenSin k dy y).pow 2).const_add
      (taylorGreenSin k dx x ^ 2)).const_mul (-A ^ 2 / 2)).congr_deriv (by ring)
  hasDerivAt_ux_x := by
    intro x y
    exact (((hasDerivAt_taylorGreenCos k dx x).const_mul (A * k)).mul_const
      (taylorGreenCos k dy y)).congr_deriv (by ring)
  hasDerivAt_uy_y := by
    intro x y
    exact ((hasDerivAt_taylorGreenSin k dy y).const_mul
      (-A * k * taylorGreenSin k dx x)).congr_deriv (by ring)
  hasDerivAt_vx_x := by
    intro x y
    exact (((hasDerivAt_taylorGreenSin k dx x).const_mul (A * k)).mul_const
      (taylorGreenSin k dy y)).congr_deriv (by ring)
  hasDerivAt_vy_y := by
    intro x y
    exact ((hasDerivAt_taylorGreenCos k dy y).const_mul
      (-A * k * taylorGreenCos k dx x)).congr_deriv (by ring)

/-- Incompressibility holds for every amplitude, frequency, and translation. -/
theorem taylorGreenJet_divergence (k A dx dy x y : ℝ) :
    (taylorGreenJet k A dx dy).ux x y + (taylorGreenJet k A dx dy).vy x y = 0 := by
  simp only [taylorGreenJet]
  ring

/-- The pressure exactly cancels horizontal convective acceleration. -/
theorem taylorGreenJet_horizontal_euler (k A dx dy x y : ℝ) :
    let J := taylorGreenJet k A dx dy
    J.u x y * J.ux x y + J.v x y * J.uy x y + J.px x y = 0 := by
  dsimp [taylorGreenJet]
  linear_combination A ^ 2 * k * taylorGreenSin k dx x * taylorGreenCos k dx x *
    (taylorGreenSin_sq_add_cos_sq k dy y)

/-- The pressure exactly cancels vertical convective acceleration. -/
theorem taylorGreenJet_vertical_euler (k A dx dy x y : ℝ) :
    let J := taylorGreenJet k A dx dy
    J.u x y * J.vx x y + J.v x y * J.vy x y + J.py x y = 0 := by
  dsimp [taylorGreenJet]
  linear_combination A ^ 2 * k * taylorGreenSin k dy y * taylorGreenCos k dy y *
    (taylorGreenSin_sq_add_cos_sq k dx x)

/-- A new exact family inhabits the corpus's existing incompressible-flow predicate. -/
theorem taylorGreenJet_solves_euler (k A dx dy : ℝ) :
    SolvesSteadyIncompressibleNavierStokes 0 (taylorGreenJet k A dx dy) := by
  refine ⟨taylorGreenJet_divergence k A dx dy, ?_, ?_⟩
  · intro x y
    simpa using taylorGreenJet_horizontal_euler k A dx dy x y
  · intro x y
    simpa using taylorGreenJet_vertical_euler k A dx dy x y

/-- Vorticity of an arbitrary shifted Taylor--Green mode. -/
theorem taylorGreenJet_vorticity (k A dx dy x y : ℝ) :
    (taylorGreenJet k A dx dy).vx x y - (taylorGreenJet k A dx dy).uy x y =
      2 * A * k * taylorGreenSin k dx x * taylorGreenSin k dy y := by
  simp only [taylorGreenJet]
  ring

/-- Exact viscous residual of a frozen Taylor--Green field. -/
theorem taylorGreenJet_viscous_residual (nu k A dx dy x y : ℝ) :
    let J := taylorGreenJet k A dx dy
    (J.u x y * J.ux x y + J.v x y * J.uy x y + J.px x y -
      nu * (J.uxx x y + J.uyy x y) = 2 * nu * k ^ 2 * J.u x y) ∧
    (J.u x y * J.vx x y + J.v x y * J.vy x y + J.py x y -
      nu * (J.vxx x y + J.vyy x y) = 2 * nu * k ^ 2 * J.v x y) := by
  dsimp only
  rw [taylorGreenJet_horizontal_euler, taylorGreenJet_vertical_euler]
  constructor <;> dsimp [taylorGreenJet] <;> ring

/-- Exact two-feature Kolmogorov--Arnold representation of the horizontal velocity. -/
theorem taylorGreenJet_u_KAN (k A dx dy x y : ℝ) :
    (taylorGreenJet k A dx dy).u x y =
      A / 2 * (Real.sin (k * (x - dx) + k * (y - dy)) +
        Real.sin (k * (x - dx) - k * (y - dy))) := by
  simp only [taylorGreenJet, taylorGreenSin, taylorGreenCos, Real.sin_add, Real.sin_sub]
  ring

/-- The vertical velocity uses the same two univariate sine features. -/
theorem taylorGreenJet_v_KAN (k A dx dy x y : ℝ) :
    (taylorGreenJet k A dx dy).v x y =
      A / 2 * (Real.sin (k * (x - dx) - k * (y - dy)) -
        Real.sin (k * (x - dx) + k * (y - dy))) := by
  simp only [taylorGreenJet, taylorGreenSin, taylorGreenCos, Real.sin_add, Real.sin_sub]
  ring

/-- The decaying Taylor--Green solution, equation (9), with arbitrary frequency and translation. -/
def taylorGreenEvolution (nu k dx dy t : ℝ) : SteadyNavierStokesJet2 :=
  taylorGreenJet k (Real.exp (-2 * nu * k ^ 2 * t)) dx dy

theorem hasDerivAt_taylorGreenEvolution_u (nu k dx dy t x y : ℝ) :
    HasDerivAt (fun s => (taylorGreenEvolution nu k dx dy s).u x y)
      (-2 * nu * k ^ 2 * (taylorGreenEvolution nu k dx dy t).u x y) t := by
  have h := (Real.hasDerivAt_exp (-2 * nu * k ^ 2 * t)).comp t
    ((hasDerivAt_id t).const_mul (-2 * nu * k ^ 2))
  exact ((h.mul_const (taylorGreenSin k dx x)).mul_const
    (taylorGreenCos k dy y)).congr_deriv (by dsimp [taylorGreenEvolution, taylorGreenJet]; ring)

theorem hasDerivAt_taylorGreenEvolution_v (nu k dx dy t x y : ℝ) :
    HasDerivAt (fun s => (taylorGreenEvolution nu k dx dy s).v x y)
      (-2 * nu * k ^ 2 * (taylorGreenEvolution nu k dx dy t).v x y) t := by
  have h := (Real.hasDerivAt_exp (-2 * nu * k ^ 2 * t)).comp t
    ((hasDerivAt_id t).const_mul (-2 * nu * k ^ 2))
  exact ((h.neg.mul_const (taylorGreenCos k dx x)).mul_const
    (taylorGreenSin k dy y)).congr_deriv (by dsimp [taylorGreenEvolution, taylorGreenJet]; ring)

/-- Both unsteady Navier--Stokes momentum equations hold with literal time derivatives. -/
theorem taylorGreenEvolution_momentum (nu k dx dy t x y : ℝ) :
    let J := taylorGreenEvolution nu k dx dy t
    (deriv (fun s => (taylorGreenEvolution nu k dx dy s).u x y) t +
      J.u x y * J.ux x y + J.v x y * J.uy x y + J.px x y -
        nu * (J.uxx x y + J.uyy x y) = 0) ∧
    (deriv (fun s => (taylorGreenEvolution nu k dx dy s).v x y) t +
      J.u x y * J.vx x y + J.v x y * J.vy x y + J.py x y -
        nu * (J.vxx x y + J.vyy x y) = 0) := by
  dsimp only
  rw [(hasDerivAt_taylorGreenEvolution_u nu k dx dy t x y).deriv,
    (hasDerivAt_taylorGreenEvolution_v nu k dx dy t x y).deriv]
  have h := taylorGreenJet_viscous_residual nu k
    (Real.exp (-2 * nu * k ^ 2 * t)) dx dy x y
  change _ ∧ _ at h
  constructor <;> dsimp only [taylorGreenEvolution] <;> linarith [h.1, h.2]

/-- Two spatial scales, with a translated second mode as in equations (11)--(12). -/
def taylorGreenBlendU (beta k l dx dy x y : ℝ) : ℝ :=
  beta * (taylorGreenJet k 1 0 0).u x y +
    (1 - beta) * (taylorGreenJet l 1 dx dy).u x y

def taylorGreenBlendV (beta k l dx dy x y : ℝ) : ℝ :=
  beta * (taylorGreenJet k 1 0 0).v x y +
    (1 - beta) * (taylorGreenJet l 1 dx dy).v x y

/-- Vorticity is linear even though material advection is quadratic. -/
def taylorGreenBlendVorticity (beta k l dx dy x y : ℝ) : ℝ :=
  2 * beta * k * taylorGreenSin k 0 x * taylorGreenSin k 0 y +
    2 * (1 - beta) * l * taylorGreenSin l dx x * taylorGreenSin l dy y

theorem taylorGreenBlend_divergence (beta k l dx dy x y : ℝ) :
    deriv (fun z => taylorGreenBlendU beta k l dx dy z y) x +
      deriv (taylorGreenBlendV beta k l dx dy x) y = 0 := by
  have hu := ((taylorGreenJet k 1 0 0).hasDerivAt_u_x x y).const_mul beta
  have hu' := ((taylorGreenJet l 1 dx dy).hasDerivAt_u_x x y).const_mul (1 - beta)
  have hv := ((taylorGreenJet k 1 0 0).hasDerivAt_v_y x y).const_mul beta
  have hv' := ((taylorGreenJet l 1 dx dy).hasDerivAt_v_y x y).const_mul (1 - beta)
  unfold taylorGreenBlendU taylorGreenBlendV
  rw [(hu.fun_add hu').deriv, (hv.fun_add hv').deriv]
  dsimp [taylorGreenJet]
  ring

theorem taylorGreenBlend_vorticity_eq (beta k l dx dy x y : ℝ) :
    deriv (fun z => taylorGreenBlendV beta k l dx dy z y) x -
      deriv (taylorGreenBlendU beta k l dx dy x) y =
        taylorGreenBlendVorticity beta k l dx dy x y := by
  have hv := ((taylorGreenJet k 1 0 0).hasDerivAt_v_x x y).const_mul beta
  have hv' := ((taylorGreenJet l 1 dx dy).hasDerivAt_v_x x y).const_mul (1 - beta)
  have hu := ((taylorGreenJet k 1 0 0).hasDerivAt_u_y x y).const_mul beta
  have hu' := ((taylorGreenJet l 1 dx dy).hasDerivAt_u_y x y).const_mul (1 - beta)
  unfold taylorGreenBlendV taylorGreenBlendU
  rw [(hv.fun_add hv').deriv, (hu.fun_add hu').deriv]
  dsimp [taylorGreenJet, taylorGreenBlendVorticity]
  ring

/-- The interaction of two exact modes is governed by their Laplacian eigenvalue difference. -/
theorem taylorGreenBlend_vorticity_advection (beta k l dx dy x y : ℝ) :
    taylorGreenBlendU beta k l dx dy x y *
        deriv (fun z => taylorGreenBlendVorticity beta k l dx dy z y) x +
      taylorGreenBlendV beta k l dx dy x y *
        deriv (taylorGreenBlendVorticity beta k l dx dy x) y =
      2 * beta * (1 - beta) * (l ^ 2 - k ^ 2) *
        (taylorGreenSin k 0 x * taylorGreenCos k 0 y *
            taylorGreenCos l dx x * taylorGreenSin l dy y -
          taylorGreenCos k 0 x * taylorGreenSin k 0 y *
            taylorGreenSin l dx x * taylorGreenCos l dy y) := by
  have hx := (((hasDerivAt_taylorGreenSin k 0 x).const_mul (2 * beta * k)).mul_const
    (taylorGreenSin k 0 y)).fun_add
    (((hasDerivAt_taylorGreenSin l dx x).const_mul (2 * (1 - beta) * l)).mul_const
      (taylorGreenSin l dy y))
  have hy := ((hasDerivAt_taylorGreenSin k 0 y).const_mul
    (2 * beta * k * taylorGreenSin k 0 x)).fun_add
    ((hasDerivAt_taylorGreenSin l dy y).const_mul
      (2 * (1 - beta) * l * taylorGreenSin l dx x))
  unfold taylorGreenBlendVorticity
  rw [hx.deriv, hy.deriv]
  dsimp [taylorGreenBlendU, taylorGreenBlendV, taylorGreenJet]
  ring

end GaloisForLFunctions.HTGeometry
