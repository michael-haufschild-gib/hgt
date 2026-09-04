import GaloisForLFunctions.HTGeometry.TanhSubstitution

/-!
# Exact Kovasznay flow from arXiv:2609.03768
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def kovasznayFrequency : ℝ := 2 * Real.pi

def kovasznayLambda : ℝ :=
  1 / 2 - Real.sqrt (1 / 4 + kovasznayFrequency ^ 2)

theorem kovasznayLambda_relation :
    kovasznayLambda ^ 2 - kovasznayLambda - kovasznayFrequency ^ 2 = 0 := by
  have hs : Real.sqrt (1 / 4 + kovasznayFrequency ^ 2) ^ 2 =
      1 / 4 + kovasznayFrequency ^ 2 := Real.sq_sqrt (by positivity)
  rw [kovasznayLambda]
  nlinarith

def kovasznayU (x y : ℝ) : ℝ :=
  1 - Real.exp (kovasznayLambda * x) * Real.cos (kovasznayFrequency * y)

def kovasznayV (x y : ℝ) : ℝ :=
  kovasznayLambda / kovasznayFrequency * Real.exp (kovasznayLambda * x) *
    Real.sin (kovasznayFrequency * y)

def kovasznayP (x _y : ℝ) : ℝ :=
  (1 / 2) * (1 - Real.exp (2 * kovasznayLambda * x))

def kovasznayUx (x y : ℝ) : ℝ :=
  -kovasznayLambda * Real.exp (kovasznayLambda * x) * Real.cos (kovasznayFrequency * y)

def kovasznayUy (x y : ℝ) : ℝ :=
  kovasznayFrequency * Real.exp (kovasznayLambda * x) * Real.sin (kovasznayFrequency * y)

def kovasznayVx (x y : ℝ) : ℝ :=
  kovasznayLambda ^ 2 / kovasznayFrequency * Real.exp (kovasznayLambda * x) *
    Real.sin (kovasznayFrequency * y)

def kovasznayVy (x y : ℝ) : ℝ :=
  kovasznayLambda * Real.exp (kovasznayLambda * x) * Real.cos (kovasznayFrequency * y)

def kovasznayPx (x _y : ℝ) : ℝ :=
  -kovasznayLambda * Real.exp (2 * kovasznayLambda * x)

def kovasznayPy (_x _y : ℝ) : ℝ := 0

def kovasznayUxx (x y : ℝ) : ℝ :=
  -kovasznayLambda ^ 2 * Real.exp (kovasznayLambda * x) *
    Real.cos (kovasznayFrequency * y)

def kovasznayUyy (x y : ℝ) : ℝ :=
  kovasznayFrequency ^ 2 * Real.exp (kovasznayLambda * x) *
    Real.cos (kovasznayFrequency * y)

def kovasznayVxx (x y : ℝ) : ℝ :=
  kovasznayLambda ^ 3 / kovasznayFrequency * Real.exp (kovasznayLambda * x) *
    Real.sin (kovasznayFrequency * y)

def kovasznayVyy (x y : ℝ) : ℝ :=
  -kovasznayLambda * kovasznayFrequency * Real.exp (kovasznayLambda * x) *
    Real.sin (kovasznayFrequency * y)

structure SteadyNavierStokesJet2 where
  u : ℝ → ℝ → ℝ
  v : ℝ → ℝ → ℝ
  p : ℝ → ℝ → ℝ
  ux : ℝ → ℝ → ℝ
  uy : ℝ → ℝ → ℝ
  vx : ℝ → ℝ → ℝ
  vy : ℝ → ℝ → ℝ
  px : ℝ → ℝ → ℝ
  py : ℝ → ℝ → ℝ
  uxx : ℝ → ℝ → ℝ
  uyy : ℝ → ℝ → ℝ
  vxx : ℝ → ℝ → ℝ
  vyy : ℝ → ℝ → ℝ
  hasDerivAt_u_x : ∀ x y, HasDerivAt (fun z => u z y) (ux x y) x
  hasDerivAt_u_y : ∀ x y, HasDerivAt (u x) (uy x y) y
  hasDerivAt_v_x : ∀ x y, HasDerivAt (fun z => v z y) (vx x y) x
  hasDerivAt_v_y : ∀ x y, HasDerivAt (v x) (vy x y) y
  hasDerivAt_p_x : ∀ x y, HasDerivAt (fun z => p z y) (px x y) x
  hasDerivAt_p_y : ∀ x y, HasDerivAt (p x) (py x y) y
  hasDerivAt_ux_x : ∀ x y, HasDerivAt (fun z => ux z y) (uxx x y) x
  hasDerivAt_uy_y : ∀ x y, HasDerivAt (uy x) (uyy x y) y
  hasDerivAt_vx_x : ∀ x y, HasDerivAt (fun z => vx z y) (vxx x y) x
  hasDerivAt_vy_y : ∀ x y, HasDerivAt (vy x) (vyy x y) y

def SolvesSteadyIncompressibleNavierStokes (nu : ℝ) (J : SteadyNavierStokesJet2) : Prop :=
  (∀ x y, J.ux x y + J.vy x y = 0) ∧
  (∀ x y, J.u x y * J.ux x y + J.v x y * J.uy x y + J.px x y -
    nu * (J.uxx x y + J.uyy x y) = 0) ∧
  (∀ x y, J.u x y * J.vx x y + J.v x y * J.vy x y + J.py x y -
    nu * (J.vxx x y + J.vyy x y) = 0)

def kovasznayJet : SteadyNavierStokesJet2 where
  u := kovasznayU
  v := kovasznayV
  p := kovasznayP
  ux := kovasznayUx
  uy := kovasznayUy
  vx := kovasznayVx
  vy := kovasznayVy
  px := kovasznayPx
  py := kovasznayPy
  uxx := kovasznayUxx
  uyy := kovasznayUyy
  vxx := kovasznayVxx
  vyy := kovasznayVyy
  hasDerivAt_u_x := by
    intro x y
    unfold kovasznayU kovasznayUx
    have hlin := (hasDerivAt_id x).const_mul kovasznayLambda
    have hE := (Real.hasDerivAt_exp (kovasznayLambda * x)).comp x hlin
    exact ((hasDerivAt_const x (1 : ℝ)).sub
      (hE.mul_const (Real.cos (kovasznayFrequency * y)))).congr_deriv (by ring)
  hasDerivAt_u_y := by
    intro x y
    unfold kovasznayU kovasznayUy
    have hlin := (hasDerivAt_id y).const_mul kovasznayFrequency
    have hC := (Real.hasDerivAt_cos (kovasznayFrequency * y)).comp y hlin
    exact ((hasDerivAt_const y (1 : ℝ)).sub
      (hC.const_mul (Real.exp (kovasznayLambda * x)))).congr_deriv (by ring)
  hasDerivAt_v_x := by
    intro x y
    unfold kovasznayV kovasznayVx
    have hlin := (hasDerivAt_id x).const_mul kovasznayLambda
    have hE := (Real.hasDerivAt_exp (kovasznayLambda * x)).comp x hlin
    exact ((hE.const_mul (kovasznayLambda / kovasznayFrequency)).mul_const
      (Real.sin (kovasznayFrequency * y))).congr_deriv (by ring)
  hasDerivAt_v_y := by
    intro x y
    unfold kovasznayV kovasznayVy
    have hlin := (hasDerivAt_id y).const_mul kovasznayFrequency
    have hS := (Real.hasDerivAt_sin (kovasznayFrequency * y)).comp y hlin
    have h := hS.const_mul
      (kovasznayLambda / kovasznayFrequency * Real.exp (kovasznayLambda * x))
    apply h.congr_deriv
    field_simp [kovasznayFrequency, Real.pi_ne_zero]
  hasDerivAt_p_x := by
    intro x y
    unfold kovasznayP kovasznayPx
    have hlin := (hasDerivAt_id x).const_mul (2 * kovasznayLambda)
    have hE := (Real.hasDerivAt_exp (2 * kovasznayLambda * x)).comp x hlin
    exact (((hasDerivAt_const x (1 : ℝ)).sub hE).const_mul (1 / 2)).congr_deriv (by ring)
  hasDerivAt_p_y := by
    intro x y
    change HasDerivAt (fun _ : ℝ => (1 / 2) *
      (1 - Real.exp (2 * kovasznayLambda * x))) 0 y
    exact hasDerivAt_const y _
  hasDerivAt_ux_x := by
    intro x y
    unfold kovasznayUx kovasznayUxx
    have hlin := (hasDerivAt_id x).const_mul kovasznayLambda
    have hE := (Real.hasDerivAt_exp (kovasznayLambda * x)).comp x hlin
    exact ((hE.const_mul (-kovasznayLambda)).mul_const
      (Real.cos (kovasznayFrequency * y))).congr_deriv (by ring)
  hasDerivAt_uy_y := by
    intro x y
    unfold kovasznayUy kovasznayUyy
    have hlin := (hasDerivAt_id y).const_mul kovasznayFrequency
    have hS := (Real.hasDerivAt_sin (kovasznayFrequency * y)).comp y hlin
    exact (hS.const_mul
      (kovasznayFrequency * Real.exp (kovasznayLambda * x))).congr_deriv (by ring)
  hasDerivAt_vx_x := by
    intro x y
    unfold kovasznayVx kovasznayVxx
    have hlin := (hasDerivAt_id x).const_mul kovasznayLambda
    have hE := (Real.hasDerivAt_exp (kovasznayLambda * x)).comp x hlin
    exact ((hE.const_mul (kovasznayLambda ^ 2 / kovasznayFrequency)).mul_const
      (Real.sin (kovasznayFrequency * y))).congr_deriv (by ring)
  hasDerivAt_vy_y := by
    intro x y
    unfold kovasznayVy kovasznayVyy
    have hlin := (hasDerivAt_id y).const_mul kovasznayFrequency
    have hC := (Real.hasDerivAt_cos (kovasznayFrequency * y)).comp y hlin
    exact (hC.const_mul
      (kovasznayLambda * Real.exp (kovasznayLambda * x))).congr_deriv (by ring)

theorem kovasznay_solves_reynolds_one :
    SolvesSteadyIncompressibleNavierStokes 1 kovasznayJet := by
  have hw : kovasznayFrequency ≠ 0 := by
    unfold kovasznayFrequency
    positivity
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    simp [kovasznayJet, kovasznayUx, kovasznayVy]
  · intro x y
    simp only [kovasznayJet]
    rw [kovasznayU, kovasznayV, kovasznayUx, kovasznayUy, kovasznayPx,
      kovasznayUxx, kovasznayUyy]
    have htrig := Real.sin_sq_add_cos_sq (kovasznayFrequency * y)
    have hlam := kovasznayLambda_relation
    rw [show 2 * kovasznayLambda * x =
      kovasznayLambda * x + kovasznayLambda * x by ring, Real.exp_add]
    calc
      (1 - Real.exp (kovasznayLambda * x) * Real.cos (kovasznayFrequency * y)) *
            (-kovasznayLambda * Real.exp (kovasznayLambda * x) *
              Real.cos (kovasznayFrequency * y)) +
          (kovasznayLambda / kovasznayFrequency * Real.exp (kovasznayLambda * x) *
              Real.sin (kovasznayFrequency * y)) *
            (kovasznayFrequency * Real.exp (kovasznayLambda * x) *
              Real.sin (kovasznayFrequency * y)) +
          -kovasznayLambda *
              (Real.exp (kovasznayLambda * x) * Real.exp (kovasznayLambda * x)) -
          1 *
            (-kovasznayLambda ^ 2 * Real.exp (kovasznayLambda * x) *
                Real.cos (kovasznayFrequency * y) +
              kovasznayFrequency ^ 2 * Real.exp (kovasznayLambda * x) *
                Real.cos (kovasznayFrequency * y)) =
          Real.exp (kovasznayLambda * x) * Real.cos (kovasznayFrequency * y) *
              (kovasznayLambda ^ 2 - kovasznayLambda - kovasznayFrequency ^ 2) +
            kovasznayLambda * Real.exp (kovasznayLambda * x) ^ 2 *
              (Real.sin (kovasznayFrequency * y) ^ 2 +
                Real.cos (kovasznayFrequency * y) ^ 2 - 1) := by
            field_simp [hw]
            ring
      _ = 0 := by rw [hlam, htrig]; ring
  · intro x y
    simp only [kovasznayJet]
    rw [kovasznayU, kovasznayV, kovasznayVx, kovasznayVy, kovasznayPy,
      kovasznayVxx, kovasznayVyy]
    have hlam := kovasznayLambda_relation
    calc
      (1 - Real.exp (kovasznayLambda * x) * Real.cos (kovasznayFrequency * y)) *
            (kovasznayLambda ^ 2 / kovasznayFrequency *
              Real.exp (kovasznayLambda * x) * Real.sin (kovasznayFrequency * y)) +
          (kovasznayLambda / kovasznayFrequency * Real.exp (kovasznayLambda * x) *
              Real.sin (kovasznayFrequency * y)) *
            (kovasznayLambda * Real.exp (kovasznayLambda * x) *
              Real.cos (kovasznayFrequency * y)) +
          0 - 1 *
            (kovasznayLambda ^ 3 / kovasznayFrequency *
                Real.exp (kovasznayLambda * x) * Real.sin (kovasznayFrequency * y) +
              -kovasznayLambda * kovasznayFrequency *
                Real.exp (kovasznayLambda * x) * Real.sin (kovasznayFrequency * y)) =
          -(kovasznayLambda / kovasznayFrequency * Real.exp (kovasznayLambda * x) *
            Real.sin (kovasznayFrequency * y)) *
              (kovasznayLambda ^ 2 - kovasznayLambda - kovasznayFrequency ^ 2) := by
            field_simp [hw]
            ring
      _ = 0 := by rw [hlam]; ring

end

end GaloisForLFunctions.HTGeometry
