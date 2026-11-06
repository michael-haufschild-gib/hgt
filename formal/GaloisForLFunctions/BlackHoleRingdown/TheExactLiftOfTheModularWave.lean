import GaloisForLFunctions.HTGeometry.QNMPoschlTeller

/-!
# The exact lift of the modular wave equation to the black hole

On the massless topological AdS black hole with tortoise coordinate `x` and hyperboloidal time
`τ = t - log(2 cosh x)`, a time profile `f` lifts to two radial profiles:

`e^{-τ/2} f(τ)` and `tanh(x) e^{-3τ/2} f(τ)`.

Both obey `ψ_tt - ψ_xx = sech²(x) · lift(f'' - f/4)`, with no condition on `f`. So every solution
of the modular wave equation `𝓕_ττ = Δ𝓕 + 𝓕/4` on the horizon gives an exact solution of the radial
equation `ψ_tt - ψ_xx = sech²(x) Δψ`.

The first lift has vanishing normal derivative at the AdS boundary `x = 0`, and the second vanishes
there. Both are regular on the future horizon, because `τ = v - log(2r/(r+1))` is smooth through
`r = 1` at fixed ingoing time `v = t + x`.

The last section is the reduction from the metric. For the conformally coupled scalar `F = ψ/r` the
divergence-form operator `□ + 2` of `-f dt² + dr²/f + r²(dx² + dy²)/y²` equals
`(r f)⁻¹ (ψ_{**} - ψ_tt + sech²(x_*) y² (ψ_xx + ψ_yy))`.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open HTGeometry

/-- Hyperboloidal time. -/
def hyperboloidalTime (t x : ℝ) : ℝ := t - qnmHyperboloidalHeight x

/-- The damped profile `e^{-Dτ} f(τ)`. -/
def dampedProfile (D : ℂ) (f : ℝ → ℂ) (τ : ℝ) : ℂ := Complex.exp (-D * (τ : ℂ)) * f τ

/-- The Neumann lift `e^{-τ/2} f(τ)`, of radial decay `1/2`. -/
def neumannLift (f : ℝ → ℂ) (t x : ℝ) : ℂ := dampedProfile (1 / 2) f (hyperboloidalTime t x)

/-- The Dirichlet lift `tanh(x) e^{-3τ/2} f(τ)`, of radial decay `3/2`. -/
def dirichletLift (f : ℝ → ℂ) (t x : ℝ) : ℂ :=
  (Real.tanh x : ℂ) * dampedProfile (3 / 2) f (hyperboloidalTime t x)

/-! ### Damped time profiles -/

/-- Differentiating a damped profile replaces `f` by `f' - D f`. -/
theorem hasDerivAt_dampedProfile (D : ℂ) {f f₁ : ℝ → ℂ} {τ : ℝ} (hf : HasDerivAt f (f₁ τ) τ) :
    HasDerivAt (dampedProfile D f) (dampedProfile D (fun s => f₁ s - D * f s) τ) τ := by
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (-D * (s : ℂ)))
      (Complex.exp (-D * (τ : ℂ)) * (-D)) τ := by
    have h := ((hasDerivAt_id τ).ofReal_comp.const_mul (-D)).cexp
    simpa using h
  have h := hexp.mul hf
  refine h.congr_deriv ?_
  simp only [dampedProfile]
  ring

/-! ### Slices -/

section Slices

variable {G G₁ G₂ : ℝ → ℂ}

theorem hasDerivAt_hyperboloidalTime_space (t x : ℝ) :
    HasDerivAt (hyperboloidalTime t) (-Real.tanh x) x :=
  (hasDerivAt_qnmHyperboloidalHeight x).const_sub t

theorem hasDerivAt_hyperboloidalTime_time (t x : ℝ) :
    HasDerivAt (fun s => hyperboloidalTime s x) 1 t :=
  (hasDerivAt_id' t).sub_const (qnmHyperboloidalHeight x)

theorem hasDerivAt_time_slice (hG : ∀ τ, HasDerivAt G (G₁ τ) τ) (t x : ℝ) :
    HasDerivAt (fun s => G (hyperboloidalTime s x)) (G₁ (hyperboloidalTime t x)) t := by
  have h := (hG (hyperboloidalTime t x)).scomp t (hasDerivAt_hyperboloidalTime_time t x)
  simpa [Function.comp_def] using h

theorem hasDerivAt_space_slice (hG : ∀ τ, HasDerivAt G (G₁ τ) τ) (t x : ℝ) :
    HasDerivAt (fun y => G (hyperboloidalTime t y))
      (-(Real.tanh x : ℂ) * G₁ (hyperboloidalTime t x)) x := by
  have h := (hG (hyperboloidalTime t x)).scomp x (hasDerivAt_hyperboloidalTime_space t x)
  refine (h.congr_deriv ?_)
  rw [Complex.real_smul]
  push_cast
  ring

theorem hasDerivAt_tanh_complex (x : ℝ) :
    HasDerivAt (fun y : ℝ => (Real.tanh y : ℂ)) ((1 - (Real.tanh x : ℂ) ^ 2)) x := by
  have h := (qnm_hasDerivAt_tanh x).ofReal_comp
  refine h.congr_deriv ?_
  push_cast
  rfl

/-- The second time derivative of a slice. -/
theorem deriv_deriv_time_slice (hG : ∀ τ, HasDerivAt G (G₁ τ) τ)
    (hG₁ : ∀ τ, HasDerivAt G₁ (G₂ τ) τ) (t x : ℝ) :
    deriv (deriv fun s => G (hyperboloidalTime s x)) t = G₂ (hyperboloidalTime t x) := by
  have h : (deriv fun s => G (hyperboloidalTime s x)) = fun s => G₁ (hyperboloidalTime s x) :=
    funext fun s => (hasDerivAt_time_slice hG s x).deriv
  rw [h]
  exact (hasDerivAt_time_slice hG₁ t x).deriv

/-- The second space derivative of a slice. -/
theorem deriv_deriv_space_slice (hG : ∀ τ, HasDerivAt G (G₁ τ) τ)
    (hG₁ : ∀ τ, HasDerivAt G₁ (G₂ τ) τ) (t x : ℝ) :
    deriv (deriv fun y => G (hyperboloidalTime t y)) x =
      -(1 - (Real.tanh x : ℂ) ^ 2) * G₁ (hyperboloidalTime t x) +
        (Real.tanh x : ℂ) ^ 2 * G₂ (hyperboloidalTime t x) := by
  have h : (deriv fun y => G (hyperboloidalTime t y)) =
      fun y => -(Real.tanh y : ℂ) * G₁ (hyperboloidalTime t y) :=
    funext fun y => (hasDerivAt_space_slice hG t y).deriv
  rw [h]
  have hneg : HasDerivAt (fun y : ℝ => -(Real.tanh y : ℂ)) (-(1 - (Real.tanh x : ℂ) ^ 2)) x :=
    (hasDerivAt_tanh_complex x).neg
  have h2 : HasDerivAt (fun y : ℝ => -(Real.tanh y : ℂ) * G₁ (hyperboloidalTime t y))
      (-(1 - (Real.tanh x : ℂ) ^ 2) * G₁ (hyperboloidalTime t x) +
        -(Real.tanh x : ℂ) * (-(Real.tanh x : ℂ) * G₂ (hyperboloidalTime t x))) x :=
    hneg.mul (hasDerivAt_space_slice hG₁ t x)
  refine h2.deriv.trans ?_
  ring

/-- The second space derivative of `tanh(x) G(τ)`. -/
theorem deriv_deriv_tanh_mul_space_slice (hG : ∀ τ, HasDerivAt G (G₁ τ) τ)
    (hG₁ : ∀ τ, HasDerivAt G₁ (G₂ τ) τ) (t x : ℝ) :
    deriv (deriv fun y => (Real.tanh y : ℂ) * G (hyperboloidalTime t y)) x =
      (1 - (Real.tanh x : ℂ) ^ 2) * (Real.tanh x : ℂ) *
          (-2 * G (hyperboloidalTime t x) - 3 * G₁ (hyperboloidalTime t x)) +
        (Real.tanh x : ℂ) ^ 3 * G₂ (hyperboloidalTime t x) := by
  have h : (deriv fun y => (Real.tanh y : ℂ) * G (hyperboloidalTime t y)) =
      fun y => (1 - (Real.tanh y : ℂ) ^ 2) * G (hyperboloidalTime t y) -
        (Real.tanh y : ℂ) ^ 2 * G₁ (hyperboloidalTime t y) := by
    funext y
    have h1 := (hasDerivAt_tanh_complex y).mul (hasDerivAt_space_slice hG t y)
    refine h1.deriv.trans ?_
    ring
  rw [h]
  have hT := hasDerivAt_tanh_complex x
  have hS : HasDerivAt (fun y : ℝ => 1 - (Real.tanh y : ℂ) ^ 2)
      (-(2 * (Real.tanh x : ℂ) * (1 - (Real.tanh x : ℂ) ^ 2))) x := by
    have := (hT.pow 2).const_sub (1 : ℂ)
    refine this.congr_deriv ?_
    push_cast
    ring
  have hT2 : HasDerivAt (fun y : ℝ => (Real.tanh y : ℂ) ^ 2)
      (2 * (Real.tanh x : ℂ) * (1 - (Real.tanh x : ℂ) ^ 2)) x := by
    have := hT.pow 2
    refine this.congr_deriv ?_
    push_cast
    ring
  have h2 := (hS.mul (hasDerivAt_space_slice hG t x)).sub
    (hT2.mul (hasDerivAt_space_slice hG₁ t x))
  refine h2.deriv.trans ?_
  ring

end Slices

/-! ### The lift theorems -/

/-- **The Neumann lift.**  For any twice differentiable profile,
`ψ_tt - ψ_xx = sech²(x) · lift(f'' - f/4)`. -/
theorem neumannLift_wave {f f₁ f₂ : ℝ → ℂ} (hf : ∀ τ, HasDerivAt f (f₁ τ) τ)
    (hf₁ : ∀ τ, HasDerivAt f₁ (f₂ τ) τ) (t x : ℝ) :
    deriv (deriv fun s => neumannLift f s x) t - deriv (deriv (neumannLift f t)) x =
      ((1 - (Real.tanh x : ℂ) ^ 2)) * neumannLift (fun τ => f₂ τ - f τ / 4) t x := by
  set G := dampedProfile (1 / 2) f with hGdef
  set G₁ := dampedProfile (1 / 2) (fun s => f₁ s - (1 / 2) * f s) with hG₁def
  set G₂ := dampedProfile (1 / 2) (fun s => (f₂ s - (1 / 2) * f₁ s) - (1 / 2) * (f₁ s - (1 / 2) * f s))
    with hG₂def
  have hG : ∀ τ, HasDerivAt G (G₁ τ) τ := fun τ => hasDerivAt_dampedProfile _ (hf τ)
  have hG₁ : ∀ τ, HasDerivAt G₁ (G₂ τ) τ := fun τ =>
    hasDerivAt_dampedProfile _ ((hf₁ τ).sub ((hf τ).const_mul (1 / 2 : ℂ)))
  have htime : deriv (deriv fun s => neumannLift f s x) t = G₂ (hyperboloidalTime t x) :=
    deriv_deriv_time_slice hG hG₁ t x
  have hspace : deriv (deriv (neumannLift f t)) x =
      -(1 - (Real.tanh x : ℂ) ^ 2) * G₁ (hyperboloidalTime t x) +
        (Real.tanh x : ℂ) ^ 2 * G₂ (hyperboloidalTime t x) :=
    deriv_deriv_space_slice hG hG₁ t x
  rw [htime, hspace, neumannLift]
  simp only [hG₁def, hG₂def, dampedProfile]
  ring

/-- **The Dirichlet lift.**  For any twice differentiable profile,
`ψ_tt - ψ_xx = sech²(x) · lift(f'' - f/4)`. -/
theorem dirichletLift_wave {f f₁ f₂ : ℝ → ℂ} (hf : ∀ τ, HasDerivAt f (f₁ τ) τ)
    (hf₁ : ∀ τ, HasDerivAt f₁ (f₂ τ) τ) (t x : ℝ) :
    deriv (deriv fun s => dirichletLift f s x) t - deriv (deriv (dirichletLift f t)) x =
      ((1 - (Real.tanh x : ℂ) ^ 2)) * dirichletLift (fun τ => f₂ τ - f τ / 4) t x := by
  set G := dampedProfile (3 / 2) f with hGdef
  set G₁ := dampedProfile (3 / 2) (fun s => f₁ s - (3 / 2) * f s) with hG₁def
  set G₂ := dampedProfile (3 / 2) (fun s => (f₂ s - (3 / 2) * f₁ s) - (3 / 2) * (f₁ s - (3 / 2) * f s))
    with hG₂def
  have hG : ∀ τ, HasDerivAt G (G₁ τ) τ := fun τ => hasDerivAt_dampedProfile _ (hf τ)
  have hG₁ : ∀ τ, HasDerivAt G₁ (G₂ τ) τ := fun τ =>
    hasDerivAt_dampedProfile _ ((hf₁ τ).sub ((hf τ).const_mul (3 / 2 : ℂ)))
  have htimeFun : (fun s => dirichletLift f s x) =
      fun s => (Real.tanh x : ℂ) * G (hyperboloidalTime s x) := rfl
  have htime : deriv (deriv fun s => dirichletLift f s x) t =
      (Real.tanh x : ℂ) * G₂ (hyperboloidalTime t x) := by
    rw [htimeFun]
    have hd : (deriv fun s => (Real.tanh x : ℂ) * G (hyperboloidalTime s x)) =
        fun s => (Real.tanh x : ℂ) * G₁ (hyperboloidalTime s x) :=
      funext fun s => ((hasDerivAt_time_slice hG s x).const_mul _).deriv
    rw [hd]
    exact ((hasDerivAt_time_slice hG₁ t x).const_mul _).deriv
  have hspace := deriv_deriv_tanh_mul_space_slice hG hG₁ t x
  have hspaceFun : dirichletLift f t = fun y => (Real.tanh y : ℂ) * G (hyperboloidalTime t y) := rfl
  rw [htime, hspaceFun, hspace, dirichletLift]
  simp only [hG₁def, hG₂def, hGdef, dampedProfile]
  ring

/-- **The modular wave equation lifts.**  If `f'' = L + f/4` along the profile, the Neumann lift obeys
`ψ_tt - ψ_xx = sech²(x) · lift(L)`. -/
theorem neumannLift_modular_wave {f f₁ f₂ L : ℝ → ℂ} (hf : ∀ τ, HasDerivAt f (f₁ τ) τ)
    (hf₁ : ∀ τ, HasDerivAt f₁ (f₂ τ) τ) (hwave : ∀ τ, f₂ τ = L τ + f τ / 4) (t x : ℝ) :
    deriv (deriv fun s => neumannLift f s x) t - deriv (deriv (neumannLift f t)) x =
      ((1 - (Real.tanh x : ℂ) ^ 2)) * neumannLift L t x := by
  rw [neumannLift_wave hf hf₁]
  congr 2
  funext τ
  rw [hwave]
  ring

/-- **The modular wave equation lifts.**  If `f'' = L + f/4` along the profile, the Dirichlet lift
obeys `ψ_tt - ψ_xx = sech²(x) · lift(L)`. -/
theorem dirichletLift_modular_wave {f f₁ f₂ L : ℝ → ℂ} (hf : ∀ τ, HasDerivAt f (f₁ τ) τ)
    (hf₁ : ∀ τ, HasDerivAt f₁ (f₂ τ) τ) (hwave : ∀ τ, f₂ τ = L τ + f τ / 4) (t x : ℝ) :
    deriv (deriv fun s => dirichletLift f s x) t - deriv (deriv (dirichletLift f t)) x =
      ((1 - (Real.tanh x : ℂ) ^ 2)) * dirichletLift L t x := by
  rw [dirichletLift_wave hf hf₁]
  congr 2
  funext τ
  rw [hwave]
  ring

/-! ### Boundary data -/

/-- The Dirichlet lift vanishes at the AdS boundary. -/
theorem dirichletLift_boundary (f : ℝ → ℂ) (t : ℝ) : dirichletLift f t 0 = 0 := by
  simp [dirichletLift]

/-- The Neumann lift has vanishing normal derivative at the AdS boundary. -/
theorem neumannLift_normalDerivative {f f₁ : ℝ → ℂ} (hf : ∀ τ, HasDerivAt f (f₁ τ) τ) (t : ℝ) :
    deriv (neumannLift f t) 0 = 0 := by
  have hG : ∀ τ, HasDerivAt (dampedProfile (1 / 2) f)
      (dampedProfile (1 / 2) (fun s => f₁ s - (1 / 2) * f s) τ) τ :=
    fun τ => hasDerivAt_dampedProfile _ (hf τ)
  have h := (hasDerivAt_space_slice hG t 0).deriv
  have hfun : neumannLift f t =
      fun y => dampedProfile (1 / 2) f (hyperboloidalTime t y) := rfl
  rw [hfun, h]
  simp

/-! ### The tortoise coordinate -/

/-- The tortoise coordinate `x_*(r) = ½ log((r-1)/(r+1))` of the lapse `r² - 1`. -/
def tortoise (r : ℝ) : ℝ := 1 / 2 * Real.log ((r - 1) / (r + 1))

theorem tortoise_neg {r : ℝ} (hr : 1 < r) : tortoise r < 0 := by
  have h : (r - 1) / (r + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hpos : 0 < (r - 1) / (r + 1) := div_pos (by linarith) (by linarith)
  have := Real.log_neg hpos h
  rw [tortoise]
  linarith

/-- `dx_*/dr = 1/(r² - 1)`. -/
theorem hasDerivAt_tortoise {r : ℝ} (hr : 1 < r) : HasDerivAt tortoise ((r ^ 2 - 1)⁻¹) r := by
  have h1 : r - 1 ≠ 0 := by linarith
  have h2 : r + 1 ≠ 0 := by linarith
  have hq : HasDerivAt (fun ρ : ℝ => (ρ - 1) / (ρ + 1))
      ((1 * (r + 1) - (r - 1) * 1) / (r + 1) ^ 2) r :=
    ((hasDerivAt_id r).sub_const 1).div ((hasDerivAt_id r).add_const 1) h2
  have hlog := (hq.log (div_ne_zero h1 h2)).const_mul (1 / 2 : ℝ)
  refine hlog.congr_deriv ?_
  have h3 : r ^ 2 - 1 ≠ 0 := by
    have : r ^ 2 - 1 = (r - 1) * (r + 1) := by ring
    rw [this]
    exact mul_ne_zero h1 h2
  field_simp
  ring

/-- `e^{2x_*} = (r-1)/(r+1)`. -/
theorem exp_two_mul_tortoise {r : ℝ} (hr : 1 < r) :
    Real.exp (2 * tortoise r) = (r - 1) / (r + 1) := by
  have hpos : 0 < (r - 1) / (r + 1) := div_pos (by linarith) (by linarith)
  rw [tortoise, show 2 * (1 / 2 * Real.log ((r - 1) / (r + 1))) = Real.log ((r - 1) / (r + 1)) by
    ring, Real.exp_log hpos]

/-- `2 cosh x_* = (2r/(r+1)) e^{-x_*}`. -/
theorem two_mul_cosh_tortoise {r : ℝ} (hr : 1 < r) :
    2 * Real.cosh (tortoise r) = 2 * r / (r + 1) * Real.exp (-tortoise r) := by
  have h := exp_two_mul_tortoise hr
  have hsplit : Real.exp (2 * tortoise r) = Real.exp (tortoise r) * Real.exp (tortoise r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE : Real.exp (tortoise r) * Real.exp (-tortoise r) = 1 := by
    rw [← Real.exp_add]
    simp
  have h1 : Real.exp (tortoise r) = (r - 1) / (r + 1) * Real.exp (-tortoise r) := by
    rw [← h, hsplit, mul_assoc, hE, mul_one]
  have h2 : r + 1 ≠ 0 := by linarith
  rw [Real.cosh_eq, h1]
  field_simp
  ring

/-- **Regularity on the future horizon.**  `τ = (t + x_*) - log(2r/(r+1))`, and the logarithm is smooth
through `r = 1`. -/
theorem hyperboloidalTime_tortoise (t : ℝ) {r : ℝ} (hr : 1 < r) :
    hyperboloidalTime t (tortoise r) = (t + tortoise r) - Real.log (2 * r / (r + 1)) := by
  have hpos : 0 < 2 * r / (r + 1) := by
    have : 0 < r := by linarith
    positivity
  rw [hyperboloidalTime, qnmHyperboloidalHeight, two_mul_cosh_tortoise hr,
    Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- `sech²(x_*) = (r²-1)/r²`. -/
theorem one_sub_tanh_sq_tortoise {r : ℝ} (hr : 1 < r) :
    1 - Real.tanh (tortoise r) ^ 2 = (r ^ 2 - 1) / r ^ 2 := by
  rw [qnm_tanh_barrier_eq_cosh]
  have hc := two_mul_cosh_tortoise hr
  have hc' : Real.cosh (tortoise r) = r / (r + 1) * Real.exp (-tortoise r) := by
    have h2 : r + 1 ≠ 0 := by linarith
    field_simp at hc ⊢
    linarith
  have hsq : Real.exp (-tortoise r) ^ 2 = (r + 1) / (r - 1) := by
    have h := exp_two_mul_tortoise hr
    rw [← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * -tortoise r = -(2 * tortoise r) := by
      push_cast
      ring
    rw [this, Real.exp_neg, h, inv_div]
  have hr0 : r ≠ 0 := by linarith
  have h1 : r - 1 ≠ 0 := by linarith
  have h2 : r + 1 ≠ 0 := by linarith
  have hcsq : Real.cosh (tortoise r) ^ 2 = r ^ 2 / ((r - 1) * (r + 1)) := by
    rw [hc', mul_pow, hsq]
    field_simp
  rw [hcsq]
  field_simp
  ring

/-! ### The wave operator of the metric -/

/-- The divergence-form operator `ρ⁻¹ ∂ᵢ(ρ Gⁱⁱ ∂ᵢ F)` of
`-(r²-1) dt² + dr²/(r²-1) + r²(dx² + dy²)/y²` in the chart `(t, r, x, y)`, where `ρ = r²/y²`. -/
def blackHoleWaveOperator (F : ℝ → ℝ → ℝ → ℝ → ℂ) (t r x y : ℝ) : ℂ :=
  ((y ^ 2 / r ^ 2 : ℝ) : ℂ) *
    (deriv (fun s => ((r ^ 2 / y ^ 2 * (-(r ^ 2 - 1)⁻¹) : ℝ) : ℂ) * deriv (fun s' => F s' r x y) s) t +
      deriv (fun ρ => ((ρ ^ 2 / y ^ 2 * (ρ ^ 2 - 1) : ℝ) : ℂ) * deriv (fun ρ' => F t ρ' x y) ρ) r +
      deriv (fun ξ => ((r ^ 2 / y ^ 2 * (y ^ 2 / r ^ 2) : ℝ) : ℂ) * deriv (fun ξ' => F t r ξ' y) ξ) x +
      deriv (fun η => ((r ^ 2 / η ^ 2 * (η ^ 2 / r ^ 2) : ℝ) : ℂ) * deriv (fun η' => F t r x η') η) y)

/-- The conformally coupled scalar built from a radial profile: `F = ψ(t, x_*(r), x, y)/r`. -/
def conformalScalar (ψ : ℝ → ℝ → ℝ → ℝ → ℂ) (t r x y : ℝ) : ℂ :=
  ψ t (tortoise r) x y / (r : ℂ)

/-- **Reduction from the metric.**  The conformally coupled wave operator `□ + 2` of the black hole,
applied to `F = ψ/r`, is the radial operator with potential `sech²(x_*)` times the horizon Laplacian. -/
theorem blackHoleWaveOperator_conformalScalar (ψ : ℝ → ℝ → ℝ → ℝ → ℂ) {t r x y : ℝ} (hr : 1 < r)
    (hy : 0 < y)
    (hg : ∀ᶠ X in 𝓝 (tortoise r), DifferentiableAt ℝ (fun X' => ψ t X' x y) X)
    (hg₂ : DifferentiableAt ℝ (deriv fun X' => ψ t X' x y) (tortoise r)) :
    blackHoleWaveOperator (conformalScalar ψ) t r x y + 2 * conformalScalar ψ t r x y =
      ((r * (r ^ 2 - 1) : ℝ) : ℂ)⁻¹ *
        (deriv (deriv fun X' => ψ t X' x y) (tortoise r) -
          deriv (deriv fun s => ψ s (tortoise r) x y) t +
          ((1 - Real.tanh (tortoise r) ^ 2 : ℝ) : ℂ) * ((y ^ 2 : ℝ) : ℂ) *
            (deriv (deriv fun ξ => ψ t (tortoise r) ξ y) x +
              deriv (deriv fun η => ψ t (tortoise r) x η) y)) := by
  have hr0 : r ≠ 0 := by linarith
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
  have hy0 : y ≠ 0 := hy.ne'
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0
  have hf : r ^ 2 - 1 ≠ 0 := by nlinarith
  have hfC : ((r : ℂ) ^ 2 - 1) ≠ 0 := by
    have : ((r ^ 2 - 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hf
    simpa using this
  set X := tortoise r with hXdef
  set g : ℝ → ℂ := fun X' => ψ t X' x y with hgdef
  -- the time term
  have hT : deriv (fun s => ((r ^ 2 / y ^ 2 * (-(r ^ 2 - 1)⁻¹) : ℝ) : ℂ) *
        deriv (fun s' => conformalScalar ψ s' r x y) s) t =
      ((r ^ 2 / y ^ 2 * (-(r ^ 2 - 1)⁻¹) : ℝ) : ℂ) *
        (deriv (deriv fun s => ψ s X x y) t / (r : ℂ)) := by
    have hd : (deriv fun s' => conformalScalar ψ s' r x y) =
        fun s => deriv (fun s' => ψ s' X x y) s / (r : ℂ) := by
      funext s
      exact deriv_div_const _
    rw [hd, deriv_const_mul_field]
    congr 1
    exact deriv_div_const _
  -- the horizontal term
  have hX' : deriv (fun ξ => ((r ^ 2 / y ^ 2 * (y ^ 2 / r ^ 2) : ℝ) : ℂ) *
        deriv (fun ξ' => conformalScalar ψ t r ξ' y) ξ) x =
      deriv (deriv fun ξ => ψ t X ξ y) x / (r : ℂ) := by
    have hc : ((r ^ 2 / y ^ 2 * (y ^ 2 / r ^ 2) : ℝ) : ℂ) = 1 := by
      have : r ^ 2 / y ^ 2 * (y ^ 2 / r ^ 2) = 1 := by
        field_simp
      rw [this]
      simp
    have hd : (deriv fun ξ' => conformalScalar ψ t r ξ' y) =
        fun ξ => deriv (fun ξ' => ψ t X ξ' y) ξ / (r : ℂ) := by
      funext ξ
      exact deriv_div_const _
    rw [hc, hd]
    simp only [one_mul]
    exact deriv_div_const _
  -- the vertical term
  have hY' : deriv (fun η => ((r ^ 2 / η ^ 2 * (η ^ 2 / r ^ 2) : ℝ) : ℂ) *
        deriv (fun η' => conformalScalar ψ t r x η') η) y =
      deriv (deriv fun η => ψ t X x η) y / (r : ℂ) := by
    have hd : (deriv fun η' => conformalScalar ψ t r x η') =
        fun η => deriv (fun η' => ψ t X x η') η / (r : ℂ) := by
      funext η
      exact deriv_div_const _
    have hev : (fun η => ((r ^ 2 / η ^ 2 * (η ^ 2 / r ^ 2) : ℝ) : ℂ) *
          deriv (fun η' => conformalScalar ψ t r x η') η) =ᶠ[𝓝 y]
        fun η => deriv (fun η' => ψ t X x η') η / (r : ℂ) := by
      filter_upwards [lt_mem_nhds hy] with η hη
      have hη0 : η ≠ 0 := hη.ne'
      have : r ^ 2 / η ^ 2 * (η ^ 2 / r ^ 2) = 1 := by
        field_simp
      rw [this, hd]
      simp
    rw [hev.deriv_eq]
    exact deriv_div_const _
  -- the radial term
  have hR : deriv (fun ρ => ((ρ ^ 2 / y ^ 2 * (ρ ^ 2 - 1) : ℝ) : ℂ) *
        deriv (fun ρ' => conformalScalar ψ t ρ' x y) ρ) r =
      ((y ^ 2 : ℝ) : ℂ)⁻¹ * ((r : ℂ) * deriv (deriv g) X / ((r : ℂ) ^ 2 - 1) - 2 * (r : ℂ) * g X) := by
    have hcont : ContinuousAt tortoise r := (hasDerivAt_tortoise hr).continuousAt
    have hev : (fun ρ => ((ρ ^ 2 / y ^ 2 * (ρ ^ 2 - 1) : ℝ) : ℂ) *
          deriv (fun ρ' => conformalScalar ψ t ρ' x y) ρ) =ᶠ[𝓝 r]
        fun ρ => ((y ^ 2 : ℝ) : ℂ)⁻¹ *
          ((ρ : ℂ) * deriv g (tortoise ρ) - ((ρ ^ 2 - 1 : ℝ) : ℂ) * g (tortoise ρ)) := by
      filter_upwards [lt_mem_nhds hr, hcont.eventually hg] with ρ hρ hgρ
      have hρ0 : ρ ≠ 0 := by linarith
      have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0
      have hfρ : ρ ^ 2 - 1 ≠ 0 := by nlinarith
      have hfρC : ((ρ : ℂ) ^ 2 - 1) ≠ 0 := by
        have : ((ρ ^ 2 - 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hfρ
        simpa using this
      have hcomp : HasDerivAt (fun ρ' => g (tortoise ρ'))
          (((ρ ^ 2 - 1)⁻¹ : ℝ) • deriv g (tortoise ρ)) ρ :=
        hgρ.hasDerivAt.scomp ρ (hasDerivAt_tortoise hρ)
      have hdiv := hcomp.div (hasDerivAt_id ρ).ofReal_comp hρC
      have hF : deriv (fun ρ' => conformalScalar ψ t ρ' x y) ρ =
          ((((ρ ^ 2 - 1)⁻¹ : ℝ) • deriv g (tortoise ρ)) * (ρ : ℂ) - g (tortoise ρ) * ((1 : ℝ) : ℂ)) /
            (ρ : ℂ) ^ 2 :=
        hdiv.deriv
      rw [hF, Complex.real_smul]
      push_cast
      have hyC2 : (y : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hyC
      field_simp
    rw [hev.deriv_eq]
    have hgX : HasDerivAt g (deriv g X) (tortoise r) := (hg.self_of_nhds).hasDerivAt
    have hgX₂ : HasDerivAt (deriv g) (deriv (deriv g) X) (tortoise r) := hg₂.hasDerivAt
    have hcompr : HasDerivAt (fun ρ' => g (tortoise ρ'))
        (((r ^ 2 - 1)⁻¹ : ℝ) • deriv g X) r :=
      hgX.scomp r (hasDerivAt_tortoise hr)
    have hcomp₂ : HasDerivAt (fun ρ' => deriv g (tortoise ρ'))
        (((r ^ 2 - 1)⁻¹ : ℝ) • deriv (deriv g) X) r :=
      hgX₂.scomp r (hasDerivAt_tortoise hr)
    have hid : HasDerivAt (fun ρ : ℝ => (ρ : ℂ)) 1 r := (hasDerivAt_id r).ofReal_comp
    have hf1 : HasDerivAt (fun ρ : ℝ => ((ρ ^ 2 - 1 : ℝ) : ℂ)) (2 * (r : ℂ)) r := by
      have := ((hasDerivAt_id r).pow 2).sub_const (1 : ℝ) |>.ofReal_comp
      refine this.congr_deriv ?_
      push_cast
      simp
    have hmain := ((hid.mul hcomp₂).sub (hf1.mul hcompr)).const_mul (((y ^ 2 : ℝ) : ℂ)⁻¹)
    refine hmain.deriv.trans ?_
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    field_simp
    ring
  rw [blackHoleWaveOperator, hT, hR, hX', hY', conformalScalar]
  have hsech : ((1 - Real.tanh X ^ 2 : ℝ) : ℂ) = ((r : ℂ) ^ 2 - 1) / (r : ℂ) ^ 2 := by
    rw [hXdef, one_sub_tanh_sq_tortoise hr]
    push_cast
    rfl
  rw [hsech]
  push_cast
  field_simp
  ring

end GaloisForLFunctions.BlackHoleRingdown

end
