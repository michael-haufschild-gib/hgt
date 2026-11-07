import GaloisForLFunctions.BlackHoleRingdown.TheMetricOfTheModularHorizon

/-!
# The lift of any modular wave

Any solution `F(τ, x, y)` of the modular wave equation `F_ττ = y²(F_xx + F_yy) + F/4`, twice differentiable
in `τ`, lifts to solutions of the conformally coupled wave equation of the massless topological black hole:
`e^{-τ/2} F/r` with Neumann data at the AdS boundary and `tanh(x_*) e^{-3τ/2} F/r` with Dirichlet data, where
`τ = t - log(2 cosh x_*)`. If `F` is `SL₂(ℤ)`-invariant, so are the lifts.

Nothing about the spectral content of `F` enters, so this applies to Eisenstein packets, to the image field of
a pulse, to cusp forms, and to their sums.
-/

open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower

/-- A solution of the modular wave equation on the chart `y > 0`. -/
structure IsModularWave (F : ℝ → ℝ → ℝ → ℂ) : Prop where
  diff : ∀ x y : ℝ, 0 < y → Differentiable ℝ fun τ => F τ x y
  diff2 : ∀ x y : ℝ, 0 < y → Differentiable ℝ (deriv fun τ => F τ x y)
  wave : ∀ τ x y : ℝ, 0 < y → deriv (deriv fun s => F s x y) τ =
    (y : ℂ) ^ 2 * (deriv (deriv fun q => F τ q y) x + deriv (deriv fun q => F τ x q) y) + F τ x y / 4

theorem IsModularWave.add {F G : ℝ → ℝ → ℝ → ℂ} (hF : IsModularWave F) (hG : IsModularWave G)
    (hFx : ∀ τ y : ℝ, 0 < y → Differentiable ℝ fun q => F τ q y)
    (hFx2 : ∀ τ y : ℝ, 0 < y → Differentiable ℝ (deriv fun q => F τ q y))
    (hFy : ∀ τ x y : ℝ, 0 < y → ∀ᶠ q in 𝓝 y, DifferentiableAt ℝ (fun q' => F τ x q') q)
    (hFy2 : ∀ τ x y : ℝ, 0 < y → DifferentiableAt ℝ (deriv fun q => F τ x q) y)
    (hGx : ∀ τ y : ℝ, 0 < y → Differentiable ℝ fun q => G τ q y)
    (hGx2 : ∀ τ y : ℝ, 0 < y → Differentiable ℝ (deriv fun q => G τ q y))
    (hGy : ∀ τ x y : ℝ, 0 < y → ∀ᶠ q in 𝓝 y, DifferentiableAt ℝ (fun q' => G τ x q') q)
    (hGy2 : ∀ τ x y : ℝ, 0 < y → DifferentiableAt ℝ (deriv fun q => G τ x q) y) :
    IsModularWave fun τ x y => F τ x y + G τ x y := by
  have htime : ∀ x y : ℝ, 0 < y → (deriv fun τ => F τ x y + G τ x y) =
      fun τ => deriv (fun s => F s x y) τ + deriv (fun s => G s x y) τ := fun x y hy => by
    funext τ
    exact deriv_fun_add (hF.diff x y hy τ) (hG.diff x y hy τ)
  refine ⟨fun x y hy => (hF.diff x y hy).add (hG.diff x y hy), fun x y hy => ?_, fun τ x y hy => ?_⟩
  · rw [htime x y hy]
    exact (hF.diff2 x y hy).add (hG.diff2 x y hy)
  · have hxx : (deriv fun q => F τ q y + G τ q y) =
        fun q => deriv (fun q' => F τ q' y) q + deriv (fun q' => G τ q' y) q := by
      funext q
      exact deriv_fun_add (hFx τ y hy q) (hGx τ y hy q)
    have hyy : (deriv fun q => F τ x q + G τ x q) =ᶠ[𝓝 y]
        fun q => deriv (fun q' => F τ x q') q + deriv (fun q' => G τ x q') q := by
      filter_upwards [hFy τ x y hy, hGy τ x y hy] with q h1 h2
      exact deriv_fun_add h1 h2
    rw [htime x y hy, deriv_fun_add (hF.diff2 x y hy τ) (hG.diff2 x y hy τ), hxx, hyy.deriv_eq,
      deriv_fun_add (hFx2 τ y hy x) (hGx2 τ y hy x), deriv_fun_add (hFy2 τ x y hy) (hGy2 τ x y hy),
      hF.wave τ x y hy, hG.wave τ x y hy]
    ring

/-- The Neumann radial profile of a modular wave. -/
def neumannWave (F : ℝ → ℝ → ℝ → ℂ) (t X x y : ℝ) : ℂ := neumannLift (fun τ => F τ x y) t X

/-- The Dirichlet radial profile of a modular wave. -/
def dirichletWave (F : ℝ → ℝ → ℝ → ℂ) (t X x y : ℝ) : ℂ := dirichletLift (fun τ => F τ x y) t X

section Lift

variable {F : ℝ → ℝ → ℝ → ℂ} (hF : IsModularWave F) {t r x y : ℝ} (hr : 1 < r) (hy : 0 < y)

include hF hr hy

/-- **The Neumann lift of any modular wave solves the wave equation of the metric.** -/
theorem neumannWave_metric_wave :
    metricWaveOperator (conformalScalar (neumannWave F)) t r x y -
      (1 / 6 : ℂ) * (D4BMBackground.jet (r : ℂ) (y : ℂ)).scalar *
        conformalScalar (neumannWave F) t r x y = 0 := by
  have hf : ∀ τ, HasDerivAt (fun s => F s x y) (deriv (fun s => F s x y) τ) τ :=
    fun τ => (hF.diff x y hy τ).hasDerivAt
  have hf₁ : ∀ τ, HasDerivAt (deriv fun s => F s x y)
      (deriv (deriv fun s => F s x y) τ) τ := fun τ => (hF.diff2 x y hy τ).hasDerivAt
  have hc := conformalCoupling_eq hr hy
  rw [metricWaveOperator_eq _ hr hy]
  have hmain := blackHoleWaveOperator_conformalScalar (neumannWave F) (t := t) (x := x) hr hy
    (Eventually.of_forall fun X => differentiableAt_neumannLift_space hf t X)
    (differentiableAt_deriv_neumannLift_space hf hf₁ t _)
  set X := tortoise r with hX
  have hlift := neumannLift_modular_wave hf hf₁ (L := fun τ => (y : ℂ) ^ 2 *
    (deriv (deriv fun q => F τ q y) x + deriv (deriv fun q => F τ x q) y))
    (fun τ => hF.wave τ x y hy) t X
  set c := Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t X : ℂ)) with hcdef
  have hsx : (fun ξ => neumannWave F t X ξ y) =
      fun ξ => c * F (hyperboloidalTime t X) ξ y := rfl
  have hsy : (fun η => neumannWave F t X x η) =
      fun η => c * F (hyperboloidalTime t X) x η := rfl
  have hdx : deriv (deriv fun ξ => neumannWave F t X ξ y) x =
      c * deriv (deriv fun q => F (hyperboloidalTime t X) q y) x := by
    rw [hsx]
    have h1 : (deriv fun ξ => c * F (hyperboloidalTime t X) ξ y) =
        fun ξ => c * deriv (fun q => F (hyperboloidalTime t X) q y) ξ :=
      funext fun ξ => deriv_const_mul_field _
    rw [h1, deriv_const_mul_field]
  have hdy : deriv (deriv fun η => neumannWave F t X x η) y =
      c * deriv (deriv fun q => F (hyperboloidalTime t X) x q) y := by
    rw [hsy]
    have h1 : (deriv fun η => c * F (hyperboloidalTime t X) x η) =
        fun η => c * deriv (fun q => F (hyperboloidalTime t X) x q) η :=
      funext fun η => deriv_const_mul_field _
    rw [h1, deriv_const_mul_field]
  rw [hdx, hdy] at hmain
  have hX1 : (deriv (deriv fun X' => neumannWave F t X' x y) X) =
      deriv (deriv (neumannLift (fun τ => F τ x y) t)) X := rfl
  have hT1 : (deriv (deriv fun s => neumannWave F s X x y) t) =
      deriv (deriv fun s => neumannLift (fun τ => F τ x y) s X) t := rfl
  rw [hX1, hT1] at hmain
  have hcancel : deriv (deriv (neumannLift (fun τ => F τ x y) t)) X -
      deriv (deriv fun s => neumannLift (fun τ => F τ x y) s X) t =
      -((1 - (Real.tanh X : ℂ) ^ 2) * neumannLift (fun τ => (y : ℂ) ^ 2 *
        (deriv (deriv fun q => F τ q y) x + deriv (deriv fun q => F τ x q) y)) t X) := by
    rw [← hlift]
    ring
  rw [hcancel] at hmain
  have hzero : blackHoleWaveOperator (conformalScalar (neumannWave F)) t r x y +
      2 * conformalScalar (neumannWave F) t r x y = 0 := by
    rw [hmain]
    simp only [neumannLift, dampedProfile, ← hcdef]
    push_cast
    ring
  linear_combination hzero + conformalScalar (neumannWave F) t r x y * hc

/-- **The Dirichlet lift of any modular wave solves the wave equation of the metric.** -/
theorem dirichletWave_metric_wave :
    metricWaveOperator (conformalScalar (dirichletWave F)) t r x y -
      (1 / 6 : ℂ) * (D4BMBackground.jet (r : ℂ) (y : ℂ)).scalar *
        conformalScalar (dirichletWave F) t r x y = 0 := by
  have hf : ∀ τ, HasDerivAt (fun s => F s x y) (deriv (fun s => F s x y) τ) τ :=
    fun τ => (hF.diff x y hy τ).hasDerivAt
  have hf₁ : ∀ τ, HasDerivAt (deriv fun s => F s x y)
      (deriv (deriv fun s => F s x y) τ) τ := fun τ => (hF.diff2 x y hy τ).hasDerivAt
  have hc := conformalCoupling_eq hr hy
  rw [metricWaveOperator_eq _ hr hy]
  have hmain := blackHoleWaveOperator_conformalScalar (dirichletWave F) (t := t) (x := x) hr hy
    (Eventually.of_forall fun X => differentiableAt_dirichletLift_space hf t X)
    (differentiableAt_deriv_dirichletLift_space hf hf₁ t _)
  set X := tortoise r with hX
  have hlift := dirichletLift_modular_wave hf hf₁ (L := fun τ => (y : ℂ) ^ 2 *
    (deriv (deriv fun q => F τ q y) x + deriv (deriv fun q => F τ x q) y))
    (fun τ => hF.wave τ x y hy) t X
  set c : ℂ := (Real.tanh X : ℂ) * Complex.exp (-(3 / 2 : ℂ) * (hyperboloidalTime t X : ℂ)) with hcdef
  have hsx : (fun ξ => dirichletWave F t X ξ y) =
      fun ξ => c * F (hyperboloidalTime t X) ξ y := by
    funext ξ
    simp only [dirichletWave, dirichletLift, dampedProfile, hcdef]
    ring
  have hsy : (fun η => dirichletWave F t X x η) =
      fun η => c * F (hyperboloidalTime t X) x η := by
    funext η
    simp only [dirichletWave, dirichletLift, dampedProfile, hcdef]
    ring
  have hdx : deriv (deriv fun ξ => dirichletWave F t X ξ y) x =
      c * deriv (deriv fun q => F (hyperboloidalTime t X) q y) x := by
    rw [hsx]
    have h1 : (deriv fun ξ => c * F (hyperboloidalTime t X) ξ y) =
        fun ξ => c * deriv (fun q => F (hyperboloidalTime t X) q y) ξ :=
      funext fun ξ => deriv_const_mul_field _
    rw [h1, deriv_const_mul_field]
  have hdy : deriv (deriv fun η => dirichletWave F t X x η) y =
      c * deriv (deriv fun q => F (hyperboloidalTime t X) x q) y := by
    rw [hsy]
    have h1 : (deriv fun η => c * F (hyperboloidalTime t X) x η) =
        fun η => c * deriv (fun q => F (hyperboloidalTime t X) x q) η :=
      funext fun η => deriv_const_mul_field _
    rw [h1, deriv_const_mul_field]
  rw [hdx, hdy] at hmain
  have hX1 : (deriv (deriv fun X' => dirichletWave F t X' x y) X) =
      deriv (deriv (dirichletLift (fun τ => F τ x y) t)) X := rfl
  have hT1 : (deriv (deriv fun s => dirichletWave F s X x y) t) =
      deriv (deriv fun s => dirichletLift (fun τ => F τ x y) s X) t := rfl
  rw [hX1, hT1] at hmain
  have hcancel : deriv (deriv (dirichletLift (fun τ => F τ x y) t)) X -
      deriv (deriv fun s => dirichletLift (fun τ => F τ x y) s X) t =
      -((1 - (Real.tanh X : ℂ) ^ 2) * dirichletLift (fun τ => (y : ℂ) ^ 2 *
        (deriv (deriv fun q => F τ q y) x + deriv (deriv fun q => F τ x q) y)) t X) := by
    rw [← hlift]
    ring
  rw [hcancel] at hmain
  have hzero : blackHoleWaveOperator (conformalScalar (dirichletWave F)) t r x y +
      2 * conformalScalar (dirichletWave F) t r x y = 0 := by
    rw [hmain]
    simp only [dirichletLift, dampedProfile]
    rw [hcdef]
    push_cast
    ring
  linear_combination hzero + conformalScalar (dirichletWave F) t r x y * hc

end Lift

/-- Invariance descends to the Neumann lift. -/
theorem neumannWave_smul {F : ℝ → ℝ → ℝ → ℂ}
    (hinv : ∀ (τ : ℝ) (γ : SL(2, ℤ)) (z : ℍ), F τ (γ • z : ℍ).re (γ • z : ℍ).im = F τ z.re z.im)
    (t r : ℝ) (γ : SL(2, ℤ)) (z : ℍ) :
    conformalScalar (neumannWave F) t r (γ • z : ℍ).re (γ • z : ℍ).im =
      conformalScalar (neumannWave F) t r z.re z.im := by
  simp only [conformalScalar, neumannWave, neumannLift, dampedProfile]
  rw [hinv]

/-- Invariance descends to the Dirichlet lift. -/
theorem dirichletWave_smul {F : ℝ → ℝ → ℝ → ℂ}
    (hinv : ∀ (τ : ℝ) (γ : SL(2, ℤ)) (z : ℍ), F τ (γ • z : ℍ).re (γ • z : ℍ).im = F τ z.re z.im)
    (t r : ℝ) (γ : SL(2, ℤ)) (z : ℍ) :
    conformalScalar (dirichletWave F) t r (γ • z : ℍ).re (γ • z : ℍ).im =
      conformalScalar (dirichletWave F) t r z.re z.im := by
  simp only [conformalScalar, dirichletWave, dirichletLift, dampedProfile]
  rw [hinv]

end GaloisForLFunctions.BlackHoleRingdown

end
