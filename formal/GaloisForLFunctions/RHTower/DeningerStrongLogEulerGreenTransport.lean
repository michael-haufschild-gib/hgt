import GaloisForLFunctions.RHTower.DeningerMeyerHalfDensityL1Completion

/-!
# The Euler Green inverse transports the half-density seminorm

On the all-weight logarithmic target the Euler defect `Δ_L g = g - T_{-L} g` is injective, because
an `L`-periodic element decays at `+∞` and so vanishes.  Its image `K_L = Δ_L H` therefore carries
a Green inverse `G_L`, and the half-density quotient seminorm pulls back along it to a seminorm

`r_L(h) = p̄_{1/2}(G_L h)`

on `K_L`.  Composing with `Δ_L` returns the quotient seminorm exactly, so `r_L` kills the Poisson
boundary, is invariant under the centered flow, is independent of `L`, has the transported radical,
and is bounded below by every critical Xi evaluation.

* `deningerStrongLogDefect` : the Euler defect on the all-weight target.
* `deningerStrongLogDefect_injective` : **it is injective.**
* `deningerStrongLogGreen` : the Green inverse `G_L`.
* `deningerStrongLogRelativeSeminorm` : **`r_L = p̄_{1/2} ∘ G_L`.**
* `deningerStrongLogRelativeSeminorm_defect` : **`r_L(Δ_L g) = p̄_{1/2}([g])`.**
* `deningerStrongLogRelativeSeminorm_centeredFlow` : **it is flow invariant.**
* `deningerStrongLogRelativeSeminorm_independent` : **it does not depend on `L`.**
* `deningerStrongLogRelativeSeminorm_eq_zero_setOf` : **its radical, transported.**
* `norm_xiSupportEvaluation_le_strongLogRelativeSeminorm` : **it is nonzero.**
-/

namespace RHTower

open Filter Topology

noncomputable section

/-! ## The all-weight target vanishes at `+∞` -/

/-- An all-weight cochain tends to zero at `+∞`. -/
theorem deningerMeyerStrongLogDecay_tendsto_zero_atTop {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) : Tendsto g atTop (𝓝 0) := by
  have hO : g =O[atTop] fun t : ℝ => Real.exp t ^ (-1 : ℝ) := by
    have := hg.decayTop 0 1
    rwa [iteratedDeriv_zero] at this
  refine hO.trans_tendsto ?_
  have hfun : (fun t : ℝ => Real.exp t ^ (-1 : ℝ)) = fun t : ℝ => (Real.exp t)⁻¹ := by
    funext t
    rw [Real.rpow_neg (Real.exp_pos t).le, Real.rpow_one]
  rw [hfun]
  exact Real.tendsto_exp_atTop.inv_tendsto_atTop

/-- A periodic all-weight cochain vanishes. -/
theorem deningerMeyerStrongLogDecay_eq_zero_of_periodic {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) {L : ℝ} (hL : 0 < L)
    (hper : ∀ t : ℝ, g t = g (t + L)) : g = 0 := by
  funext t
  have hstep : ∀ n : ℕ, g t = g (t + (n : ℝ) * L) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have hshift : t + (k : ℝ) * L + L = t + ((k : ℕ) + 1 : ℝ) * L := by ring
      rw [ih, hper (t + (k : ℝ) * L), hshift]
      push_cast
      ring_nf
  have hto : Tendsto (fun n : ℕ => t + (n : ℝ) * L) atTop atTop := by
    refine tendsto_atTop_add_const_left _ t ?_
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hL
  have hlim : Tendsto (fun n : ℕ => g (t + (n : ℝ) * L)) atTop (𝓝 0) :=
    (deningerMeyerStrongLogDecay_tendsto_zero_atTop hg).comp hto
  have hconst : Tendsto (fun _ : ℕ => g t) atTop (𝓝 (g t)) := tendsto_const_nhds
  have hcongr : (fun n : ℕ => g (t + (n : ℝ) * L)) = fun _ : ℕ => g t :=
    funext fun n => (hstep n).symm
  rw [hcongr] at hlim
  exact tendsto_nhds_unique hconst hlim

/-! ## The Euler defect and its Green inverse -/

/-- **The Euler defect on the all-weight target**, `Δ_L g = g - T_{-L} g`. -/
def deningerStrongLogDefect (L : ℝ) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget :=
  LinearMap.id - deningerMeyerStrongLogFlow (-L)

@[simp]
theorem deningerStrongLogDefect_apply (L : ℝ) (g : DeningerMeyerStrongLogTarget) (t : ℝ) :
    ((deningerStrongLogDefect L g : DeningerMeyerStrongLogTarget) : ℝ → ℂ) t
      = (g : ℝ → ℂ) t - (g : ℝ → ℂ) (t + L) := by
  have hshift : t - -L = t + L := by ring
  show (g : ℝ → ℂ) t - (g : ℝ → ℂ) (t - -L) = _
  rw [hshift]

/-- **The Euler defect is injective** for a positive period. -/
theorem deningerStrongLogDefect_injective {L : ℝ} (hL : 0 < L) :
    Function.Injective (deningerStrongLogDefect L) := by
  have hzero : ∀ g : DeningerMeyerStrongLogTarget, deningerStrongLogDefect L g = 0 → g = 0 := by
    intro g hg
    refine Subtype.ext (deningerMeyerStrongLogDecay_eq_zero_of_periodic g.2 hL fun t => ?_)
    have hval := congrArg
      (fun u : DeningerMeyerStrongLogTarget => (u : ℝ → ℂ) t) hg
    rw [deningerStrongLogDefect_apply] at hval
    have : (g : ℝ → ℂ) t - (g : ℝ → ℂ) (t + L) = 0 := hval
    linear_combination (norm := ring_nf) this
  intro a b hab
  have hsub : deningerStrongLogDefect L (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.1 (hzero _ hsub)

/-- **The Green inverse** of the Euler defect on its image `K_L = Δ_L H`. -/
def deningerStrongLogGreen {L : ℝ} (hL : 0 < L) :
    DeningerMeyerStrongLogTarget ≃ₗ[ℂ] ↥(LinearMap.range (deningerStrongLogDefect L)) :=
  LinearEquiv.ofInjective _ (deningerStrongLogDefect_injective hL)

@[simp]
theorem deningerStrongLogGreen_symm_apply {L : ℝ} (hL : 0 < L)
    (g : DeningerMeyerStrongLogTarget) :
    (deningerStrongLogGreen hL).symm (deningerStrongLogGreen hL g) = g :=
  (deningerStrongLogGreen hL).symm_apply_apply g

/-! ## The transported half-density seminorm -/

/-- **`r_L = p̄_{1/2} ∘ G_L`**, the half-density quotient seminorm carried to the Euler sector by
the Green inverse. -/
def deningerStrongLogRelativeSeminorm {L : ℝ} (hL : 0 < L) :
    Seminorm ℂ ↥(LinearMap.range (deningerStrongLogDefect L)) :=
  deningerMeyerHalfDensityCohomologySeminorm.comp
    ((Submodule.mkQ (LinearMap.range deningerMeyerStrongLogSumLM)).comp
      (deningerStrongLogGreen hL).symm.toLinearMap)

@[simp]
theorem deningerStrongLogRelativeSeminorm_apply {L : ℝ} (hL : 0 < L)
    (h : ↥(LinearMap.range (deningerStrongLogDefect L))) :
    deningerStrongLogRelativeSeminorm hL h
      = deningerMeyerHalfDensityCohomologySeminorm
        (Submodule.Quotient.mk ((deningerStrongLogGreen hL).symm h)) := rfl

/-- **`r_L(Δ_L g) = p̄_{1/2}([g])`.**  This is the defining transport identity. -/
theorem deningerStrongLogRelativeSeminorm_defect {L : ℝ} (hL : 0 < L)
    (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogRelativeSeminorm hL (deningerStrongLogGreen hL g)
      = deningerMeyerHalfDensityCohomologySeminorm (Submodule.Quotient.mk g) := by
  rw [deningerStrongLogRelativeSeminorm_apply, deningerStrongLogGreen_symm_apply]

/-- **`r_L` kills the Euler image of the Poisson boundary.**  This is `B_p = Δ_p Z(H_∩)`. -/
theorem deningerStrongLogRelativeSeminorm_boundary {L : ℝ} (hL : 0 < L) (f : DeningerMeyerCap) :
    deningerStrongLogRelativeSeminorm hL
        (deningerStrongLogGreen hL (deningerMeyerStrongLogSumLM f)) = 0 := by
  rw [deningerStrongLogRelativeSeminorm_defect, deningerMeyerStrongLog_boundary_class_zero,
    map_zero]

/-- **The Euler defect commutes with the centered flow.** -/
theorem deningerStrongLogDefect_centeredFlow (L a : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogDefect L (deningerMeyerStrongLogCenteredFlow a g)
      = deningerMeyerStrongLogCenteredFlow a (deningerStrongLogDefect L g) := by
  refine Subtype.ext (funext fun t => ?_)
  rw [deningerStrongLogDefect_apply, deningerMeyerStrongLogCenteredFlow_apply,
    deningerMeyerStrongLogCenteredFlow_apply, deningerMeyerStrongLogCenteredFlow_apply,
    deningerStrongLogDefect_apply]
  have hshift : t + L - a = t - a + L := by ring
  rw [hshift]
  ring

/-- **`r_L` is invariant under the centered flow `V_a = e^{-a/2}T_a`.** -/
theorem deningerStrongLogRelativeSeminorm_centeredFlow {L : ℝ} (hL : 0 < L) (a : ℝ)
    (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogRelativeSeminorm hL
        (deningerStrongLogGreen hL (deningerMeyerStrongLogCenteredFlow a g))
      = deningerStrongLogRelativeSeminorm hL (deningerStrongLogGreen hL g) := by
  rw [deningerStrongLogRelativeSeminorm_defect, deningerStrongLogRelativeSeminorm_defect,
    ← deningerMeyerStrongLogCenteredCohomologyFlow_mk,
    deningerMeyerHalfDensityCohomologySeminorm_centeredFlow]

/-- **The value does not depend on the auxiliary period.** -/
theorem deningerStrongLogRelativeSeminorm_independent {L L' : ℝ} (hL : 0 < L) (hL' : 0 < L')
    (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogRelativeSeminorm hL (deningerStrongLogGreen hL g)
      = deningerStrongLogRelativeSeminorm hL' (deningerStrongLogGreen hL' g) := by
  rw [deningerStrongLogRelativeSeminorm_defect, deningerStrongLogRelativeSeminorm_defect]

/-- **The radical of `r_L`, transported.**  A cochain of the Euler sector is `r_L`-null exactly when
its Green preimage is `p̄_{1/2}`-null. -/
theorem deningerStrongLogRelativeSeminorm_eq_zero_setOf {L : ℝ} (hL : 0 < L) :
    {h : ↥(LinearMap.range (deningerStrongLogDefect L)) |
        deningerStrongLogRelativeSeminorm hL h = 0}
      = deningerStrongLogGreen hL ''
        {g : DeningerMeyerStrongLogTarget |
          deningerMeyerHalfDensityCohomologySeminorm (Submodule.Quotient.mk g) = 0} := by
  ext h
  constructor
  · intro hh
    refine ⟨(deningerStrongLogGreen hL).symm h, ?_, (deningerStrongLogGreen hL).apply_symm_apply h⟩
    simpa [deningerStrongLogRelativeSeminorm_apply] using hh
  · rintro ⟨g, hg, rfl⟩
    show deningerStrongLogRelativeSeminorm hL (deningerStrongLogGreen hL g) = 0
    rw [deningerStrongLogRelativeSeminorm_defect]
    exact hg

/-- **Every critical Xi evaluation is bounded by `r_L`**, so `r_L` is not the zero seminorm. -/
theorem norm_xiSupportEvaluation_le_strongLogRelativeSeminorm {L : ℝ} (hL : 0 < L)
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re = 1 / 2)
    (g : DeningerMeyerStrongLogTarget) :
    ‖deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ : DeningerArithmeticJetIndex rho)
        (Submodule.Quotient.mk g)‖
      ≤ deningerStrongLogRelativeSeminorm hL (deningerStrongLogGreen hL g) := by
  rw [deningerStrongLogRelativeSeminorm_defect]
  exact norm_deningerMeyerXiSupportEvaluation_le_halfDensityCohomology rho hrho _

end

end RHTower
