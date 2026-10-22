import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonStrongSolution

/-!
# Uniqueness of the strong `L²` solution, by the energy method

A strong solution of `⟨D⟩⁻²∂ₜ²u = -u` carries a conserved quantity that needs no more derivatives
than the equation itself provides:

`F(t) = ‖⟨D⟩⁻¹∂ₜu(t)‖² + ‖u(t)‖²`.

Differentiating it produces `2 Re⟪⟨D⟩⁻¹∂ₜu, ⟨D⟩⁻¹∂ₜ²u⟫ + 2 Re⟪u, ∂ₜu⟫`, and moving one `⟨D⟩⁻¹`
across the inner product — legitimate because the symbol `⟨ξ⟩⁻¹` is real, so the operator is
self-adjoint — turns the first term into `2 Re⟪∂ₜu, ⟨D⟩⁻²∂ₜ²u⟫ = -2 Re⟪∂ₜu, u⟫`, which cancels the
second. So `F` is constant, and a solution with vanishing Cauchy data vanishes.

This is the energy method of the card, run in `L²` rather than pointwise: no support hypothesis, no
integration by parts, no domination — only the self-adjointness of one bounded operator.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Self-adjointness of the inverse frequency -/

/-- **`⟨D⟩⁻¹` is self-adjoint on `L²`**, its symbol being real. -/
theorem inner_kgFreqInvOp (f g : Lp ℂ 2 (volume : Measure E)) :
    inner ℂ (kgFreqInvOp f) g = inner ℂ f (kgFreqInvOp g) := by
  rw [kgFreqInvOp_eq]
  refine inner_fourierMulCLM_real _ _ _ (fun ξ => ?_) f g
  show (starRingEnd ℂ) ((((kgFreq ξ)⁻¹ : ℝ) : ℂ)) = (((kgFreq ξ)⁻¹ : ℝ) : ℂ)
  exact Complex.conj_ofReal _

/-! ## Two calculus helpers -/

/-- A bounded operator carries a differentiable curve to a differentiable curve. -/
theorem hasDerivAt_clm {x : ℝ → Lp ℂ 2 (volume : Measure E)} {x' : Lp ℂ 2 (volume : Measure E)} {t : ℝ}
    (T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) (h : HasDerivAt x x' t) :
    HasDerivAt (fun s => T (x s)) (T x') t :=
  (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h

/-- The squared norm of a differentiable curve in a Hilbert space is differentiable. -/
theorem hasDerivAt_norm_sq {x : ℝ → Lp ℂ 2 (volume : Measure E)} {x' : Lp ℂ 2 (volume : Measure E)} {t : ℝ}
    (h : HasDerivAt x x' t) :
    HasDerivAt (fun s => ‖x s‖ ^ (2 : ℕ))
      (RCLike.re (inner ℂ (x t) x' + inner ℂ x' (x t))) t := by
  have hi := HasDerivAt.inner ℂ h h
  have hre := (RCLike.reCLM (K := ℂ)).hasFDerivAt.comp_hasDerivAt t hi
  refine hre.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun s => norm_sq_eq_re_inner (𝕜 := ℂ) (x s)

/-! ## Strong solutions and their energy -/

/-- A **strong solution** of the free Klein–Gordon equation: a field, its velocity and its
acceleration, each the derivative of the previous, satisfying `⟨D⟩⁻²(∂ₜ²u) = -u`. -/
def SolvesKG (u v a : ℝ → Lp ℂ 2 (volume : Measure E)) : Prop :=
  (∀ t : ℝ, HasDerivAt u (v t) t) ∧ (∀ t : ℝ, HasDerivAt v (a t) t) ∧
    (∀ t : ℝ, kgFreqInvOp (kgFreqInvOp (a t)) = -(u t))

/-- The conserved energy of a strong solution. -/
def kgStrongEnergy (u v : ℝ → Lp ℂ 2 (volume : Measure E)) (t : ℝ) : ℝ :=
  ‖kgFreqInvOp (v t)‖ ^ (2 : ℕ) + ‖u t‖ ^ (2 : ℕ)

theorem kgStrongEnergy_nonneg (u v : ℝ → Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    0 ≤ kgStrongEnergy u v t :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **The energy of a strong solution has vanishing derivative.** -/
theorem hasDerivAt_kgStrongEnergy {u v a : ℝ → Lp ℂ 2 (volume : Measure E)} (h : SolvesKG u v a) (t : ℝ) :
    HasDerivAt (kgStrongEnergy u v) 0 t := by
  obtain ⟨hu, hv, heq⟩ := h
  have hA : HasDerivAt (fun s => kgFreqInvOp (v s)) (kgFreqInvOp (a t)) t :=
    hasDerivAt_clm _ (hv t)
  have h1 := hasDerivAt_norm_sq hA
  have h2 := hasDerivAt_norm_sq (hu t)
  have hsum := h1.add h2
  have hzero : RCLike.re (inner ℂ (kgFreqInvOp (v t)) (kgFreqInvOp (a t))
        + inner ℂ (kgFreqInvOp (a t)) (kgFreqInvOp (v t)))
      + RCLike.re (inner ℂ (u t) (v t) + inner ℂ (v t) (u t)) = 0 := by
    have hcross : inner ℂ (kgFreqInvOp (E := E) (v t)) (kgFreqInvOp (a t))
        = -inner ℂ (v t) (u t) := by
      rw [inner_kgFreqInvOp, heq t, inner_neg_right]
    have hswap1 : inner ℂ (kgFreqInvOp (E := E) (a t)) (kgFreqInvOp (v t))
        = (starRingEnd ℂ) (inner ℂ (kgFreqInvOp (E := E) (v t)) (kgFreqInvOp (a t))) :=
      (inner_conj_symm _ _).symm
    have hswap2 : inner ℂ (v t) (u t)
        = (starRingEnd ℂ) (inner ℂ (u t) (v t)) := (inner_conj_symm _ _).symm
    rw [hcross, hswap1, hcross, hswap2]
    simp only [map_neg, RCLike.conj_conj, RCLike.re_to_complex, Complex.add_re,
      Complex.neg_re, Complex.conj_re]
    ring
  rw [hzero] at hsum
  exact hsum

/-- **The energy of a strong solution is constant.** -/
theorem kgStrongEnergy_const {u v a : ℝ → Lp ℂ 2 (volume : Measure E)} (h : SolvesKG u v a) (t s : ℝ) :
    kgStrongEnergy u v t = kgStrongEnergy u v s := by
  refine is_const_of_deriv_eq_zero (𝕜 := ℝ) (fun x => (hasDerivAt_kgStrongEnergy h x).differentiableAt)
    (fun x => (hasDerivAt_kgStrongEnergy h x).deriv) t s

/-! ## Uniqueness -/

/-- **A strong solution with vanishing Cauchy data vanishes.** -/
theorem eq_zero_of_solvesKG {u v a : ℝ → Lp ℂ 2 (volume : Measure E)} (h : SolvesKG u v a)
    (hu0 : u 0 = 0) (hv0 : v 0 = 0) (t : ℝ) : u t = 0 := by
  have hconst := kgStrongEnergy_const h t 0
  have hzero : kgStrongEnergy u v 0 = 0 := by
    rw [kgStrongEnergy, hu0, hv0, map_zero, norm_zero]
    norm_num
  rw [hzero] at hconst
  have hle : ‖u t‖ ^ (2 : ℕ) ≤ 0 := by
    have h1 : (0 : ℝ) ≤ ‖kgFreqInvOp (E := E) (v t)‖ ^ (2 : ℕ) := sq_nonneg _
    have h2 : ‖kgFreqInvOp (E := E) (v t)‖ ^ (2 : ℕ) + ‖u t‖ ^ (2 : ℕ) = 0 := hconst
    linarith
  have : ‖u t‖ = 0 := by
    have hnn : (0 : ℝ) ≤ ‖u t‖ := norm_nonneg _
    nlinarith
  exact norm_eq_zero.mp this

/-- The strong solutions of the free equation form a vector space: differences are solutions. -/
theorem SolvesKG.sub {u₁ v₁ a₁ u₂ v₂ a₂ : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h₁ : SolvesKG u₁ v₁ a₁) (h₂ : SolvesKG u₂ v₂ a₂) :
    SolvesKG (fun t => u₁ t - u₂ t) (fun t => v₁ t - v₂ t) (fun t => a₁ t - a₂ t) := by
  obtain ⟨hu₁, hv₁, he₁⟩ := h₁
  obtain ⟨hu₂, hv₂, he₂⟩ := h₂
  refine ⟨fun t => (hu₁ t).sub (hu₂ t), fun t => (hv₁ t).sub (hv₂ t), fun t => ?_⟩
  rw [map_sub, map_sub, he₁ t, he₂ t, neg_sub_neg, neg_sub]

/-- **Uniqueness for the strong Cauchy problem.** Two strong solutions of the free Klein–Gordon
equation with the same field and velocity at time zero agree at every time. -/
theorem eq_of_solvesKG {u₁ v₁ a₁ u₂ v₂ a₂ : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h₁ : SolvesKG u₁ v₁ a₁) (h₂ : SolvesKG u₂ v₂ a₂)
    (hu0 : u₁ 0 = u₂ 0) (hv0 : v₁ 0 = v₂ 0) (t : ℝ) : u₁ t = u₂ t := by
  have hsub := h₁.sub h₂
  have h0 := eq_zero_of_solvesKG hsub (by simp [hu0]) (by simp [hv0]) t
  exact sub_eq_zero.mp h0

/-! ## The class is inhabited -/

/-- **The free field is a strong solution.** So the uniqueness statement is about a nonempty class,
and the constructed field is *the* solution of its Cauchy problem. -/
theorem solvesKG_kgFreeField (f h : Lp ℂ 2 (volume : Measure E)) :
    SolvesKG (kgFreeField f h) (kgFreeVelocity f h)
      (fun t => -(kgCosOp t f) + -(kgSinOp t h)) :=
  ⟨hasDerivAt_kgFreeField f h, hasDerivAt_kgFreeVelocity f h, fun t => by
    have hkg := kgFreeField_kleinGordon f h t
    rwa [deriv_deriv_kgFreeField] at hkg⟩

/-- **Well-posedness of the strong Cauchy problem for the free Klein–Gordon equation.** -/
theorem eq_kgFreeField_of_solvesKG {u v a : ℝ → Lp ℂ 2 (volume : Measure E)} (h : SolvesKG u v a)
    (f g : Lp ℂ 2 (volume : Measure E)) (hu0 : u 0 = kgFreqInvOp (kgFreqInvOp f))
    (hv0 : v 0 = kgFreqInvOp g) (t : ℝ) : u t = kgFreeField f g t :=
  eq_of_solvesKG h (solvesKG_kgFreeField f g)
    (by rw [hu0, kgFreeField_zero]) (by rw [hv0, kgFreeVelocity_zero]) t

end GaloisForLFunctions.HTGeometry
