import GaloisForLFunctions.HTGeometry.TaylorGreenFluidApplications

/-!
# Exact viscoelastic forcing of Taylor--Green fields

Equations (18)--(19) of arXiv:2608.29895 evaluated with actual derivatives.
Frozen fields require viscosity forcing independently of memory time.
The unsteady Navier--Stokes solution has an additional explicit material
memory residual. Both statements have concrete nonzero point evaluations.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Horizontal acceleration plus pressure gradient of a steady certified jet. -/
def steadyEulerAccelerationX (J : SteadyNavierStokesJet2) (x y : ℝ) : ℝ :=
  J.u x y * J.ux x y + J.v x y * J.uy x y + J.px x y

def steadyEulerAccelerationY (J : SteadyNavierStokesJet2) (x y : ℝ) : ℝ :=
  J.u x y * J.vx x y + J.v x y * J.vy x y + J.py x y

/-- The actual stationary GHD residual from equation (18), including material memory. -/
def steadyViscoelasticResidualX (nu tau : ℝ) (J : SteadyNavierStokesJet2) (x y : ℝ) : ℝ :=
  steadyEulerAccelerationX J x y + tau *
    (J.u x y * deriv (fun z => steadyEulerAccelerationX J z y) x +
      J.v x y * deriv (steadyEulerAccelerationX J x) y) -
        nu * (J.uxx x y + J.uyy x y)

def steadyViscoelasticResidualY (nu tau : ℝ) (J : SteadyNavierStokesJet2) (x y : ℝ) : ℝ :=
  steadyEulerAccelerationY J x y + tau *
    (J.u x y * deriv (fun z => steadyEulerAccelerationY J z y) x +
      J.v x y * deriv (steadyEulerAccelerationY J x) y) -
        nu * (J.vxx x y + J.vyy x y)

/-- The frozen Taylor--Green benchmark needs exactly viscous forcing, independently of memory time. -/
theorem taylorGreen_steadyViscoelastic_forcing (nu tau k A dx dy x y : ℝ) :
    steadyViscoelasticResidualX nu tau (taylorGreenJet k A dx dy) x y =
        2 * nu * k ^ 2 * (taylorGreenJet k A dx dy).u x y ∧
    steadyViscoelasticResidualY nu tau (taylorGreenJet k A dx dy) x y =
        2 * nu * k ^ 2 * (taylorGreenJet k A dx dy).v x y := by
  have hx : steadyEulerAccelerationX (taylorGreenJet k A dx dy) = fun _ _ => 0 := by
    funext x y
    exact taylorGreenJet_horizontal_euler k A dx dy x y
  have hy : steadyEulerAccelerationY (taylorGreenJet k A dx dy) = fun _ _ => 0 := by
    funext x y
    exact taylorGreenJet_vertical_euler k A dx dy x y
  simp only [steadyViscoelasticResidualX, steadyViscoelasticResidualY, hx, hy,
    deriv_const, mul_zero, add_zero, zero_sub]
  constructor <;> dsimp [taylorGreenJet] <;> ring

/-- A concrete exact point distinguishes the frozen benchmark from an unforced solution. -/
theorem taylorGreen_frozen_residual_at_quarter (tau : ℝ) :
    steadyViscoelasticResidualX 1 tau (taylorGreenJet 1 1 0 0) (Real.pi / 2) 0 = 2 := by
  rw [(taylorGreen_steadyViscoelastic_forcing 1 tau 1 1 0 0 (Real.pi / 2) 0).1]
  simp [taylorGreenJet, taylorGreenSin, taylorGreenCos]

theorem taylorGreen_frozen_not_unforced (tau : ℝ) :
    ¬ ∀ x y, steadyViscoelasticResidualX 1 tau (taylorGreenJet 1 1 0 0) x y = 0 := by
  intro h
  have hbad := h (Real.pi / 2) 0
  rw [taylorGreen_frozen_residual_at_quarter] at hbad
  exact two_ne_zero hbad

/-- Material derivative of an actual time-dependent scalar field. -/
def fluidMaterialDerivative (J : ℝ → SteadyNavierStokesJet2)
    (f : ℝ → ℝ → ℝ → ℝ) (t x y : ℝ) : ℝ :=
  deriv (fun s => f s x y) t + (J t).u x y * deriv (fun z => f t z y) x +
    (J t).v x y * deriv (f t x) y

/-- Full horizontal material acceleration and pressure. -/
def unsteadyEulerAccelerationX (J : ℝ → SteadyNavierStokesJet2) (t x y : ℝ) : ℝ :=
  deriv (fun s => (J s).u x y) t + steadyEulerAccelerationX (J t) x y

def unsteadyViscoelasticResidualX (nu tau : ℝ) (J : ℝ → SteadyNavierStokesJet2)
    (t x y : ℝ) : ℝ :=
  unsteadyEulerAccelerationX J t x y +
    tau * fluidMaterialDerivative J (unsteadyEulerAccelerationX J) t x y -
      nu * ((J t).uxx x y + (J t).uyy x y)

theorem unsteadyEulerAccelerationX_taylorGreen (nu k dx dy t x y : ℝ) :
    unsteadyEulerAccelerationX (taylorGreenEvolution nu k dx dy) t x y =
      -2 * nu * k ^ 2 * (taylorGreenEvolution nu k dx dy t).u x y := by
  unfold unsteadyEulerAccelerationX
  rw [(hasDerivAt_taylorGreenEvolution_u nu k dx dy t x y).deriv]
  have he := taylorGreenJet_horizontal_euler k
    (Real.exp (-2 * nu * k ^ 2 * t)) dx dy x y
  change steadyEulerAccelerationX (taylorGreenEvolution nu k dx dy t) x y = 0 at he
  rw [he, add_zero]

/-- Exact memory forcing for the decaying Navier--Stokes solution. -/
theorem taylorGreen_unsteadyViscoelastic_forcing (nu tau k dx dy t x y : ℝ) :
    unsteadyViscoelasticResidualX nu tau (taylorGreenEvolution nu k dx dy) t x y =
      tau * (4 * nu ^ 2 * k ^ 4 * (taylorGreenEvolution nu k dx dy t).u x y +
        2 * nu * k ^ 2 * (taylorGreenEvolution nu k dx dy t).px x y) := by
  have he : unsteadyEulerAccelerationX (taylorGreenEvolution nu k dx dy) =
      fun t x y => -2 * nu * k ^ 2 * (taylorGreenEvolution nu k dx dy t).u x y := by
    funext t x y
    exact unsteadyEulerAccelerationX_taylorGreen nu k dx dy t x y
  have ht := (hasDerivAt_taylorGreenEvolution_u nu k dx dy t x y).const_mul (-2 * nu * k ^ 2)
  have hx := ((taylorGreenEvolution nu k dx dy t).hasDerivAt_u_x x y).const_mul
    (-2 * nu * k ^ 2)
  have hy := ((taylorGreenEvolution nu k dx dy t).hasDerivAt_u_y x y).const_mul
    (-2 * nu * k ^ 2)
  unfold unsteadyViscoelasticResidualX fluidMaterialDerivative
  rw [he, ht.deriv, hx.deriv, hy.deriv]
  have hE := taylorGreenJet_horizontal_euler k
    (Real.exp (-2 * nu * k ^ 2 * t)) dx dy x y
  dsimp only [taylorGreenEvolution, taylorGreenJet] at hE ⊢
  linear_combination (-2 * tau * nu * k ^ 2) * hE

/-- An exact nonzero memory residual survives where ordinary Navier--Stokes is satisfied. -/
theorem taylorGreen_evolving_memory_at_quarter (tau : ℝ) :
    unsteadyViscoelasticResidualX 1 tau (taylorGreenEvolution 1 1 0 0) 0 (Real.pi / 2) 0 =
      4 * tau := by
  rw [taylorGreen_unsteadyViscoelastic_forcing]
  simp [taylorGreenEvolution, taylorGreenJet, taylorGreenSin, taylorGreenCos, mul_comm]

/-- Full vertical material acceleration and pressure. -/
def unsteadyEulerAccelerationY (J : ℝ → SteadyNavierStokesJet2) (t x y : ℝ) : ℝ :=
  deriv (fun s => (J s).v x y) t + steadyEulerAccelerationY (J t) x y

def unsteadyViscoelasticResidualY (nu tau : ℝ) (J : ℝ → SteadyNavierStokesJet2)
    (t x y : ℝ) : ℝ :=
  unsteadyEulerAccelerationY J t x y +
    tau * fluidMaterialDerivative J (unsteadyEulerAccelerationY J) t x y -
      nu * ((J t).vxx x y + (J t).vyy x y)

theorem unsteadyEulerAccelerationY_taylorGreen (nu k dx dy t x y : ℝ) :
    unsteadyEulerAccelerationY (taylorGreenEvolution nu k dx dy) t x y =
      -2 * nu * k ^ 2 * (taylorGreenEvolution nu k dx dy t).v x y := by
  unfold unsteadyEulerAccelerationY
  rw [(hasDerivAt_taylorGreenEvolution_v nu k dx dy t x y).deriv]
  have he := taylorGreenJet_vertical_euler k
    (Real.exp (-2 * nu * k ^ 2 * t)) dx dy x y
  change steadyEulerAccelerationY (taylorGreenEvolution nu k dx dy t) x y = 0 at he
  rw [he, add_zero]

/-- The vertical material-memory forcing completes the exact vector GHD residual. -/
theorem taylorGreen_unsteadyViscoelastic_forcing_y (nu tau k dx dy t x y : ℝ) :
    unsteadyViscoelasticResidualY nu tau (taylorGreenEvolution nu k dx dy) t x y =
      tau * (4 * nu ^ 2 * k ^ 4 * (taylorGreenEvolution nu k dx dy t).v x y +
        2 * nu * k ^ 2 * (taylorGreenEvolution nu k dx dy t).py x y) := by
  have he : unsteadyEulerAccelerationY (taylorGreenEvolution nu k dx dy) =
      fun t x y => -2 * nu * k ^ 2 * (taylorGreenEvolution nu k dx dy t).v x y := by
    funext t x y
    exact unsteadyEulerAccelerationY_taylorGreen nu k dx dy t x y
  have ht := (hasDerivAt_taylorGreenEvolution_v nu k dx dy t x y).const_mul (-2 * nu * k ^ 2)
  have hx := ((taylorGreenEvolution nu k dx dy t).hasDerivAt_v_x x y).const_mul
    (-2 * nu * k ^ 2)
  have hy := ((taylorGreenEvolution nu k dx dy t).hasDerivAt_v_y x y).const_mul
    (-2 * nu * k ^ 2)
  unfold unsteadyViscoelasticResidualY fluidMaterialDerivative
  rw [he, ht.deriv, hx.deriv, hy.deriv]
  have hE := taylorGreenJet_vertical_euler k
    (Real.exp (-2 * nu * k ^ 2 * t)) dx dy x y
  dsimp only [taylorGreenEvolution, taylorGreenJet] at hE ⊢
  linear_combination (-2 * tau * nu * k ^ 2) * hE

/-- A concrete decaying vortex solves unforced GHD everywhere exactly at zero memory time. -/
theorem taylorGreen_unforced_memory_iff (tau : ℝ) :
    (∀ t x y,
      unsteadyViscoelasticResidualX 1 tau (taylorGreenEvolution 1 1 0 0) t x y = 0 ∧
      unsteadyViscoelasticResidualY 1 tau (taylorGreenEvolution 1 1 0 0) t x y = 0) ↔
      tau = 0 := by
  constructor
  · intro h
    have hx := (h 0 (Real.pi / 2) 0).1
    rw [taylorGreen_evolving_memory_at_quarter] at hx
    linarith
  · rintro rfl t x y
    rw [taylorGreen_unsteadyViscoelastic_forcing, taylorGreen_unsteadyViscoelastic_forcing_y]
    simp

end GaloisForLFunctions.HTGeometry
