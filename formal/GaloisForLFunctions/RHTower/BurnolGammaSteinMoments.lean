import GaloisForLFunctions.RHTower.BurnolGammaSteinCollarKernel

/-!
# Exact moments of the Gamma-sewn collar kernels

The substitution `z = C e^{-2u}` turns the logarithmic line into the positive ray with Jacobian
`2z`, so every collar moment against a power of `e^{-u}` becomes a Gamma integral in `z`.  All the
moments needed for the prime-two collar are cubic in `z`, so a single master identity evaluates
them:

`∫_ℝ 2z (e^{-z} z^{s-1} P(z)) du = c₀ Γ(s) + c₁ Γ(s+1) + c₂ Γ(s+2) + c₃ Γ(s+3)`.

Its four instances are the archimedean normalization `∫ γ φ = 1`, the transverse Bockstein moment
`∫ κ_ε φ = ε(1+ε)²/2` — in particular the exact annihilation `∫ κ_* φ = 0` of the stable
first-wall mode and the unit gain `2 ∫ κ̇ φ = 1` — and the exact negative total mass
`∫ κ_n = -2^{-n/2} Γ_ℝ(1/2)/16` of every depth kernel.
-/

open Real Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

/-! ## The dyadic substitution -/

theorem range_burnolCollarScale {C : ℝ} (hC : 0 < C) :
    Set.range (fun u : ℝ => C * Real.exp (-2 * u)) = Ioi 0 := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact mul_pos hC (Real.exp_pos _)
  · intro hz
    refine ⟨-(1 / 2) * Real.log (z / C), ?_⟩
    have hzC : 0 < z / C := div_pos hz hC
    rw [show (-2 : ℝ) * (-(1 / 2) * Real.log (z / C)) = Real.log (z / C) by ring,
      Real.exp_log hzC]
    field_simp

/-- **The dyadic substitution.**  With `z = C e^{-2u}` the logarithmic line becomes the positive
ray and the Jacobian is `2z`. -/
theorem integral_burnolCollarSubstitution {C : ℝ} (hC : 0 < C) (F : ℝ → ℝ) :
    (∫ z in Ioi (0 : ℝ), F z) =
      ∫ u : ℝ, (2 * (C * Real.exp (-2 * u))) * F (C * Real.exp (-2 * u)) := by
  have hderiv : ∀ u ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun u : ℝ => C * Real.exp (-2 * u))
        (-2 * (C * Real.exp (-2 * u))) Set.univ u := by
    intro u _
    have hlin : HasDerivAt (fun v : ℝ => -2 * v) (-2 : ℝ) u := by
      simpa using (hasDerivAt_id u).const_mul (-2 : ℝ)
    have := (hlin.exp.const_mul C).congr_deriv (by ring :
      C * (Real.exp (-2 * u) * (-2)) = -2 * (C * Real.exp (-2 * u)))
    exact this.hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => C * Real.exp (-2 * u)) Set.univ := by
    intro u _ v _ huv
    have h := mul_left_cancel₀ (ne_of_gt hC) huv
    have := Real.exp_eq_exp.mp h
    linarith
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := fun u : ℝ => C * Real.exp (-2 * u)) (f' := fun u => -2 * (C * Real.exp (-2 * u)))
    (s := Set.univ) MeasurableSet.univ hderiv hinj F
  rw [Set.image_univ, range_burnolCollarScale hC] at hcov
  rw [hcov, MeasureTheory.integral_univ]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with u
  rw [smul_eq_mul, abs_of_nonpos (by positivity : -2 * (C * Real.exp (-2 * u)) ≤ 0)]
  ring

/-! ## Gamma monomials -/

theorem integrableOn_burnolGammaMonomial {s : ℝ} (hs : 0 < s) (k : ℕ) :
    IntegrableOn (fun z : ℝ => Real.exp (-z) * z ^ (s - 1) * z ^ k) (Ioi 0) volume := by
  refine (Real.GammaIntegral_convergent (s := s + (k : ℝ)) (by positivity)).congr_fun ?_
    measurableSet_Ioi
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  rw [mul_assoc, ← Real.rpow_natCast z k, ← Real.rpow_add hzpos]
  congr 2
  ring

theorem integral_burnolGammaMonomial {s : ℝ} (hs : 0 < s) (k : ℕ) :
    (∫ z in Ioi (0 : ℝ), Real.exp (-z) * z ^ (s - 1) * z ^ k) = Real.Gamma (s + (k : ℝ)) := by
  have hcongr : EqOn (fun z : ℝ => Real.exp (-z) * z ^ (s - 1) * z ^ k)
      (fun z : ℝ => Real.exp (-z) * z ^ ((s + (k : ℝ)) - 1)) (Ioi 0) := by
    intro z hz
    have hzpos : (0 : ℝ) < z := hz
    simp only
    rw [mul_assoc, ← Real.rpow_natCast z k, ← Real.rpow_add hzpos]
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    ← Real.Gamma_eq_integral (by positivity : (0 : ℝ) < s + (k : ℝ))]

/-- Cubic Gamma moment. -/
theorem integral_burnolGammaCubic {s : ℝ} (hs : 0 < s) (c₀ c₁ c₂ c₃ : ℝ) :
    (∫ z in Ioi (0 : ℝ), Real.exp (-z) * z ^ (s - 1) *
        (c₀ + c₁ * z + c₂ * z ^ 2 + c₃ * z ^ 3)) =
      c₀ * Real.Gamma s + c₁ * Real.Gamma (s + 1) + c₂ * Real.Gamma (s + 2) +
        c₃ * Real.Gamma (s + 3) := by
  have e0 := (integrableOn_burnolGammaMonomial hs 0).const_mul c₀
  have e1 := (integrableOn_burnolGammaMonomial hs 1).const_mul c₁
  have e2 := (integrableOn_burnolGammaMonomial hs 2).const_mul c₂
  have e3 := (integrableOn_burnolGammaMonomial hs 3).const_mul c₃
  have hsplit : EqOn (fun z : ℝ => Real.exp (-z) * z ^ (s - 1) *
        (c₀ + c₁ * z + c₂ * z ^ 2 + c₃ * z ^ 3))
      (fun z : ℝ => (c₀ * (Real.exp (-z) * z ^ (s - 1) * z ^ 0) +
        c₁ * (Real.exp (-z) * z ^ (s - 1) * z ^ 1) +
        c₂ * (Real.exp (-z) * z ^ (s - 1) * z ^ 2)) +
        c₃ * (Real.exp (-z) * z ^ (s - 1) * z ^ 3)) (Ioi 0) := by
    intro z _
    simp only [pow_zero, pow_one, mul_one]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit,
    integral_add (((e0.add e1).add e2)) e3, integral_add (e0.add e1) e2, integral_add e0 e1,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_burnolGammaMonomial hs 0, integral_burnolGammaMonomial hs 1,
    integral_burnolGammaMonomial hs 2, integral_burnolGammaMonomial hs 3]
  norm_num

/-! ## Half-integer and quarter-integer Gamma values -/

theorem burnolGamma_half_add_one : Real.Gamma (1 / 2 + 1) = 1 / 2 * Real.sqrt π := by
  rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]

theorem burnolGamma_half_add_two : Real.Gamma (1 / 2 + 2) = 3 / 4 * Real.sqrt π := by
  rw [show (1 / 2 + 2 : ℝ) = (1 / 2 + 1) + 1 by ring, Real.Gamma_add_one (by norm_num),
    burnolGamma_half_add_one]
  ring

theorem burnolGamma_half_add_three : Real.Gamma (1 / 2 + 3) = 15 / 8 * Real.sqrt π := by
  rw [show (1 / 2 + 3 : ℝ) = (1 / 2 + 2) + 1 by ring, Real.Gamma_add_one (by norm_num),
    burnolGamma_half_add_two]
  ring

theorem burnolGamma_quarter_add_one :
    Real.Gamma (5 / 4 + 1) = 5 / 4 * Real.Gamma (5 / 4) :=
  Real.Gamma_add_one (by norm_num)

theorem burnolGamma_quarter_add_two :
    Real.Gamma (5 / 4 + 2) = 45 / 16 * Real.Gamma (5 / 4) := by
  rw [show (5 / 4 + 2 : ℝ) = (5 / 4 + 1) + 1 by ring, Real.Gamma_add_one (by norm_num),
    burnolGamma_quarter_add_one]
  ring

end RHTower
