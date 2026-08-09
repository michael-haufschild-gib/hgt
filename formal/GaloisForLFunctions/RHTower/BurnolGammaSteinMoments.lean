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
    show C * Real.exp (-2 * (-(1 / 2) * Real.log (z / C))) = z
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
  rw [hcov, MeasureTheory.setIntegral_univ]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with u
  have hneg : -2 * (C * Real.exp (-2 * u)) ≤ 0 := by
    have : 0 < C * Real.exp (-2 * u) := by positivity
    linarith
  rw [smul_eq_mul, abs_of_nonpos hneg]
  ring

/-! ## Gamma monomials -/

theorem integrableOn_burnolGammaMonomial {s : ℝ} (hs : 0 < s) (k : ℕ) :
    IntegrableOn (fun z : ℝ => Real.exp (-z) * z ^ (s - 1) * z ^ k) (Ioi 0) volume := by
  refine (Real.GammaIntegral_convergent (s := s + (k : ℝ)) (by positivity)).congr_fun ?_
    measurableSet_Ioi
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  show Real.exp (-z) * z ^ (s + (k : ℝ) - 1) = Real.exp (-z) * z ^ (s - 1) * z ^ k
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
  have e0 : IntegrableOn (fun z : ℝ => c₀ * (Real.exp (-z) * z ^ (s - 1) * z ^ 0))
      (Ioi 0) volume := (integrableOn_burnolGammaMonomial hs 0).const_mul c₀
  have e1 : IntegrableOn (fun z : ℝ => c₁ * (Real.exp (-z) * z ^ (s - 1) * z ^ 1))
      (Ioi 0) volume := (integrableOn_burnolGammaMonomial hs 1).const_mul c₁
  have e2 : IntegrableOn (fun z : ℝ => c₂ * (Real.exp (-z) * z ^ (s - 1) * z ^ 2))
      (Ioi 0) volume := (integrableOn_burnolGammaMonomial hs 2).const_mul c₂
  have e3 : IntegrableOn (fun z : ℝ => c₃ * (Real.exp (-z) * z ^ (s - 1) * z ^ 3))
      (Ioi 0) volume := (integrableOn_burnolGammaMonomial hs 3).const_mul c₃
  have e01 : IntegrableOn (fun z : ℝ => c₀ * (Real.exp (-z) * z ^ (s - 1) * z ^ 0) +
      c₁ * (Real.exp (-z) * z ^ (s - 1) * z ^ 1)) (Ioi 0) volume := e0.add e1
  have e012 : IntegrableOn (fun z : ℝ => c₀ * (Real.exp (-z) * z ^ (s - 1) * z ^ 0) +
      c₁ * (Real.exp (-z) * z ^ (s - 1) * z ^ 1) +
      c₂ * (Real.exp (-z) * z ^ (s - 1) * z ^ 2)) (Ioi 0) volume := e01.add e2
  have hsplit : EqOn (fun z : ℝ => Real.exp (-z) * z ^ (s - 1) *
        (c₀ + c₁ * z + c₂ * z ^ 2 + c₃ * z ^ 3))
      (fun z : ℝ => c₀ * (Real.exp (-z) * z ^ (s - 1) * z ^ 0) +
        c₁ * (Real.exp (-z) * z ^ (s - 1) * z ^ 1) +
        c₂ * (Real.exp (-z) * z ^ (s - 1) * z ^ 2) +
        c₃ * (Real.exp (-z) * z ^ (s - 1) * z ^ 3)) (Ioi 0) := by
    intro z _
    simp only [pow_zero, pow_one, mul_one]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit,
    MeasureTheory.integral_add e012 e3, MeasureTheory.integral_add e01 e2,
    MeasureTheory.integral_add e0 e1,
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

/-! ## The master moment identity -/

theorem burnolRexp_rpow (x a : ℝ) : Real.exp x ^ a = Real.exp (x * a) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]

theorem burnolCollarScale_rpow {C : ℝ} (hC : 0 < C) (u a : ℝ) :
    (C * Real.exp (-2 * u)) ^ a = C ^ a * Real.exp (-2 * u * a) := by
  rw [Real.mul_rpow hC.le (Real.exp_pos _).le, burnolRexp_rpow]

theorem burnolCollarScale_mul_rpow {C : ℝ} (hC : 0 < C) (s u : ℝ) :
    (C * Real.exp (-2 * u)) * (C * Real.exp (-2 * u)) ^ (s - 1) =
      C ^ s * Real.exp (-2 * u * s) := by
  have hx : (0 : ℝ) < C * Real.exp (-2 * u) := by positivity
  nth_rewrite 1 [← Real.rpow_one (C * Real.exp (-2 * u))]
  rw [← Real.rpow_add hx, show (1 : ℝ) + (s - 1) = s by ring, burnolCollarScale_rpow hC]

/-- **The master moment identity.**  Every cubic collar moment is a Gamma combination. -/
theorem integral_burnolCollarMoment {C : ℝ} (hC : 0 < C) {s : ℝ} (hs : 0 < s)
    (A c₀ c₁ c₂ c₃ : ℝ) (G : ℝ → ℝ)
    (hG : ∀ u : ℝ, G u = A * (2 * (C ^ s * Real.exp (-2 * u * s)) *
        Real.exp (-(C * Real.exp (-2 * u))) *
        (c₀ + c₁ * (C * Real.exp (-2 * u)) + c₂ * (C * Real.exp (-2 * u)) ^ 2 +
          c₃ * (C * Real.exp (-2 * u)) ^ 3))) :
    (∫ u : ℝ, G u) = A * (c₀ * Real.Gamma s + c₁ * Real.Gamma (s + 1) +
      c₂ * Real.Gamma (s + 2) + c₃ * Real.Gamma (s + 3)) := by
  have hG' : ∀ u : ℝ, G u = A * ((2 * (C * Real.exp (-2 * u))) *
      (Real.exp (-(C * Real.exp (-2 * u))) * (C * Real.exp (-2 * u)) ^ (s - 1) *
        (c₀ + c₁ * (C * Real.exp (-2 * u)) + c₂ * (C * Real.exp (-2 * u)) ^ 2 +
          c₃ * (C * Real.exp (-2 * u)) ^ 3))) := by
    intro u
    rw [hG u]
    congr 1
    rw [show (2 : ℝ) * (C * Real.exp (-2 * u)) *
        (Real.exp (-(C * Real.exp (-2 * u))) * (C * Real.exp (-2 * u)) ^ (s - 1) *
          (c₀ + c₁ * (C * Real.exp (-2 * u)) + c₂ * (C * Real.exp (-2 * u)) ^ 2 +
            c₃ * (C * Real.exp (-2 * u)) ^ 3)) =
        2 * ((C * Real.exp (-2 * u)) * (C * Real.exp (-2 * u)) ^ (s - 1)) *
          Real.exp (-(C * Real.exp (-2 * u))) *
          (c₀ + c₁ * (C * Real.exp (-2 * u)) + c₂ * (C * Real.exp (-2 * u)) ^ 2 +
            c₃ * (C * Real.exp (-2 * u)) ^ 3) by ring,
      burnolCollarScale_mul_rpow hC]
  rw [funext hG', MeasureTheory.integral_const_mul,
    ← integral_burnolCollarSubstitution hC
      (fun z => Real.exp (-z) * z ^ (s - 1) * (c₀ + c₁ * z + c₂ * z ^ 2 + c₃ * z ^ 3)),
    integral_burnolGammaCubic hs c₀ c₁ c₂ c₃]

theorem burnolPi_rpow_half : π ^ ((1 : ℝ) / 2) = Real.sqrt π := (Real.sqrt_eq_rpow π).symm

/-! ## The four exact collar moments -/

/-- Every depth-zero collar profile pairs with the stable mode through the same master
integrand. -/
theorem burnolCollarProfile_mul_mode (P u : ℝ) :
    (1 / 2 * burnolCollarGamma u * P) * Real.exp (-u / 2) =
      (1 / (2 * Real.sqrt π)) * (2 * (π ^ ((1 : ℝ) / 2) * Real.exp (-2 * u * ((1 : ℝ) / 2))) *
        Real.exp (-(π * Real.exp (-2 * u))) * P) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hs : Real.sqrt π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpi)
  have hexp : Real.exp (-u / 2) * Real.exp (-u / 2) = Real.exp (-2 * u * ((1 : ℝ) / 2)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [burnolCollarGamma_apply, burnolPi_rpow_half, ← hexp]
  field_simp

/-- **The archimedean normalization `∫ γ φ = 1`.** -/
theorem integral_burnolCollarGamma_mul_mode :
    (∫ u : ℝ, burnolCollarGamma u * Real.exp (-u / 2)) = 1 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hs : Real.sqrt π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpi)
  have hpoint : ∀ u : ℝ, burnolCollarGamma u * Real.exp (-u / 2) =
      (1 / (2 * Real.sqrt π)) * (2 * (π ^ ((1 : ℝ) / 2) * Real.exp (-2 * u * ((1 : ℝ) / 2))) *
        Real.exp (-(π * Real.exp (-2 * u))) *
        (2 + 0 * (π * Real.exp (-2 * u)) + 0 * (π * Real.exp (-2 * u)) ^ 2 +
          0 * (π * Real.exp (-2 * u)) ^ 3)) := by
    intro u
    rw [← burnolCollarProfile_mul_mode
      (2 + 0 * (π * Real.exp (-2 * u)) + 0 * (π * Real.exp (-2 * u)) ^ 2 +
        0 * (π * Real.exp (-2 * u)) ^ 3) u]
    ring
  rw [integral_burnolCollarMoment hpi (by norm_num : (0 : ℝ) < 1 / 2) _ 2 0 0 0 _ hpoint,
    Real.Gamma_one_half_eq]
  field_simp
  ring

/-- **The exact transverse Bockstein moment `∫ κ_ε φ = ε(1+ε)²/2`.** -/
theorem integral_burnolCollarKernelDeformed_mul_mode (ε : ℝ) :
    (∫ u : ℝ, burnolCollarKernelDeformed ε u * Real.exp (-u / 2)) =
      1 / 2 * ε * (1 + ε) ^ 2 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hs : Real.sqrt π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpi)
  have hpoint : ∀ u : ℝ, burnolCollarKernelDeformed ε u * Real.exp (-u / 2) =
      (1 / (2 * Real.sqrt π)) * (2 * (π ^ ((1 : ℝ) / 2) * Real.exp (-2 * u * ((1 : ℝ) / 2))) *
        Real.exp (-(π * Real.exp (-2 * u))) *
        ((ε ^ 3 - ε ^ 2) + (6 * ε ^ 2 - 16 * ε + 12) * (π * Real.exp (-2 * u)) +
          (12 * ε - 28) * (π * Real.exp (-2 * u)) ^ 2 +
          8 * (π * Real.exp (-2 * u)) ^ 3)) := by
    intro u
    rw [← burnolCollarProfile_mul_mode
      ((ε ^ 3 - ε ^ 2) + (6 * ε ^ 2 - 16 * ε + 12) * (π * Real.exp (-2 * u)) +
        (12 * ε - 28) * (π * Real.exp (-2 * u)) ^ 2 +
        8 * (π * Real.exp (-2 * u)) ^ 3) u,
      burnolCollarKernelDeformed_apply, burnolCollarZ_zero]
  rw [integral_burnolCollarMoment hpi (by norm_num : (0 : ℝ) < 1 / 2) _
    (ε ^ 3 - ε ^ 2) (6 * ε ^ 2 - 16 * ε + 12) (12 * ε - 28) 8 _ hpoint,
    Real.Gamma_one_half_eq, burnolGamma_half_add_one, burnolGamma_half_add_two,
    burnolGamma_half_add_three]
  field_simp
  ring

/-- **The completed collar kernel annihilates the stable first-wall mode.** -/
theorem integral_burnolCollarKernel_mul_mode :
    (∫ u : ℝ, burnolCollarKernel 0 u * Real.exp (-u / 2)) = 0 := by
  have h := integral_burnolCollarKernelDeformed_mul_mode 0
  rw [funext (fun u => congrArg (fun x : ℝ => x * Real.exp (-u / 2))
    (burnolCollarKernelDeformed_zero u))] at h
  rw [h]
  ring

/-- **Unit gain of the transverse Bockstein reader.** -/
theorem integral_burnolBocksteinKernel_mul_mode :
    2 * (∫ u : ℝ, burnolBocksteinKernel u * Real.exp (-u / 2)) = 1 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hs : Real.sqrt π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpi)
  have hpoint : ∀ u : ℝ, burnolBocksteinKernel u * Real.exp (-u / 2) =
      (1 / (2 * Real.sqrt π)) * (2 * (π ^ ((1 : ℝ) / 2) * Real.exp (-2 * u * ((1 : ℝ) / 2))) *
        Real.exp (-(π * Real.exp (-2 * u))) *
        (0 + (-16) * (π * Real.exp (-2 * u)) + 12 * (π * Real.exp (-2 * u)) ^ 2 +
          0 * (π * Real.exp (-2 * u)) ^ 3)) := by
    intro u
    rw [← burnolCollarProfile_mul_mode
      (0 + (-16) * (π * Real.exp (-2 * u)) + 12 * (π * Real.exp (-2 * u)) ^ 2 +
        0 * (π * Real.exp (-2 * u)) ^ 3) u,
      burnolBocksteinKernel, burnolCollarZ_zero]
    ring
  rw [integral_burnolCollarMoment hpi (by norm_num : (0 : ℝ) < 1 / 2) _ 0 (-16) 12 0 _ hpoint,
    Real.Gamma_one_half_eq, burnolGamma_half_add_one, burnolGamma_half_add_two,
    burnolGamma_half_add_three]
  field_simp
  ring

/-! ## The exact negative mass of every depth kernel -/

/-- The real archimedean factor `Γ_ℝ(1/2) = π^{-1/4} Γ(1/4)`. -/
def burnolArchimedeanHalf : ℝ := π ^ (-(1 : ℝ) / 4) * Real.Gamma (1 / 4)

theorem burnolArchimedeanHalf_pos : 0 < burnolArchimedeanHalf := by
  have h1 : 0 < π ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos Real.pi_pos _
  have h2 : 0 < Real.Gamma (1 / 4 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  exact mul_pos h1 h2

theorem burnolDepthScale_pos (n : ℕ) : (0 : ℝ) < π * 4 ^ n := by positivity

/-- The depth-`n` profile pairs with the master integrand at exponent `5/4`. -/
theorem burnolDepthProfile_mul (n : ℕ) (P u : ℝ) :
    4 * Real.exp (-u / 2) * Real.exp (-((π * 4 ^ n) * Real.exp (-2 * u))) *
        ((π * 4 ^ n) * Real.exp (-2 * u)) * P =
      2 * (π * 4 ^ n) ^ (-(1 : ℝ) / 4) *
        (2 * ((π * 4 ^ n) ^ ((5 : ℝ) / 4) * Real.exp (-2 * u * ((5 : ℝ) / 4))) *
          Real.exp (-((π * 4 ^ n) * Real.exp (-2 * u))) * P) := by
  have hC : (0 : ℝ) < π * 4 ^ n := burnolDepthScale_pos n
  have hpow : (π * 4 ^ n) ^ (-(1 : ℝ) / 4) * (π * 4 ^ n) ^ ((5 : ℝ) / 4) = π * 4 ^ n := by
    rw [← Real.rpow_add hC, show (-(1 : ℝ) / 4 + (5 : ℝ) / 4) = 1 by ring, Real.rpow_one]
  have hexp : Real.exp (-u / 2) * Real.exp (-2 * u) = Real.exp (-2 * u * ((5 : ℝ) / 4)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [show (2 : ℝ) * (π * 4 ^ n) ^ (-(1 : ℝ) / 4) *
        (2 * ((π * 4 ^ n) ^ ((5 : ℝ) / 4) * Real.exp (-2 * u * ((5 : ℝ) / 4))) *
          Real.exp (-((π * 4 ^ n) * Real.exp (-2 * u))) * P) =
      4 * ((π * 4 ^ n) ^ (-(1 : ℝ) / 4) * (π * 4 ^ n) ^ ((5 : ℝ) / 4)) *
        Real.exp (-2 * u * ((5 : ℝ) / 4)) *
        Real.exp (-((π * 4 ^ n) * Real.exp (-2 * u))) * P from by ring, hpow, ← hexp]
  ring

theorem burnolDepthScale_rpow_neg_quarter (n : ℕ) :
    (π * 4 ^ n) ^ (-(1 : ℝ) / 4) = π ^ (-(1 : ℝ) / 4) * (2 : ℝ) ^ (-(n : ℝ) / 2) := by
  have hfour : ((4 : ℝ) ^ n) ^ (-(1 : ℝ) / 4) = (2 : ℝ) ^ (-(n : ℝ) / 2) := by
    rw [show (4 : ℝ) ^ n = (2 : ℝ) ^ (2 * n) by rw [pow_mul]; norm_num,
      ← Real.rpow_natCast (2 : ℝ) (2 * n), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  rw [Real.mul_rpow Real.pi_pos.le (by positivity), hfour]

/-- **The exact negative total mass of every depth kernel.** -/
theorem integral_burnolCollarKernel_depth (n : ℕ) :
    (∫ u : ℝ, burnolCollarKernel n u) =
      -((2 : ℝ) ^ (-(n : ℝ) / 2) / 16) * burnolArchimedeanHalf := by
  have hC : (0 : ℝ) < π * 4 ^ n := burnolDepthScale_pos n
  have hpoint : ∀ u : ℝ, burnolCollarKernel n u =
      2 * (π * 4 ^ n) ^ (-(1 : ℝ) / 4) *
        (2 * ((π * 4 ^ n) ^ ((5 : ℝ) / 4) * Real.exp (-2 * u * ((5 : ℝ) / 4))) *
          Real.exp (-((π * 4 ^ n) * Real.exp (-2 * u))) *
          (3 + (-7) * ((π * 4 ^ n) * Real.exp (-2 * u)) +
            2 * ((π * 4 ^ n) * Real.exp (-2 * u)) ^ 2 +
            0 * ((π * 4 ^ n) * Real.exp (-2 * u)) ^ 3)) := by
    intro u
    rw [← burnolDepthProfile_mul n
      (3 + (-7) * ((π * 4 ^ n) * Real.exp (-2 * u)) +
        2 * ((π * 4 ^ n) * Real.exp (-2 * u)) ^ 2 +
        0 * ((π * 4 ^ n) * Real.exp (-2 * u)) ^ 3) u,
      burnolCollarKernel, burnolCollarZ]
    ring
  rw [integral_burnolCollarMoment hC (by norm_num : (0 : ℝ) < 5 / 4) _ 3 (-7) 2 0 _ hpoint,
    burnolGamma_quarter_add_one, burnolGamma_quarter_add_two,
    show ((5 : ℝ) / 4 + 3) = (5 / 4 + 2) + 1 by ring, Real.Gamma_add_one (by norm_num),
    burnolGamma_quarter_add_two,
    show (5 : ℝ) / 4 = 1 / 4 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    burnolDepthScale_rpow_neg_quarter, burnolArchimedeanHalf]
  ring

/-- Every depth kernel has strictly negative total mass. -/
theorem integral_burnolCollarKernel_depth_neg (n : ℕ) :
    (∫ u : ℝ, burnolCollarKernel n u) < 0 := by
  rw [integral_burnolCollarKernel_depth]
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (-(n : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have h2 := burnolArchimedeanHalf_pos
  nlinarith

end RHTower
