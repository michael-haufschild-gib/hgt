import GaloisForLFunctions.RHTower.CirclePhaseFourierMomentIntegral
import GaloisForLFunctions.HTGeometry.ZeroDivisorCount

/-!
# Relative index of a boundary phase = zeros inside the disc

Let `F` be holomorphic on a neighbourhood of a closed disc `closedBall c R` and zero-free on the
circle `|z - c| = t`, `0 < t < R`.  Its boundary phase `u(x) = F(γ x) / |F(γ x)|`, with
`γ x = c + t e^{2πix}`, is a smooth unimodular `1`-periodic function.  With `P` the Hardy
projection on `L²(ℝ/ℤ)` and `U = M_u`:

`ind(U† P U, P) = dim(Ran U†PU ∩ Ker P) - dim(Ran P ∩ Ker U†PU) = #{zeros of F in |z - c| < t}`,

counted with multiplicity.  Equivalently the Toeplitz compression `P M_u P` has Fredholm index
`-#zeros`, and `Tr (U†PU - P)³ = #zeros`.

Proof: the relative index is `(2πi)⁻¹ ∫₀¹ \bar u u'`
(`SmoothCircleFunction.relativeIndex_toPhase_eq_integral`).  With `g = F ∘ γ` and `h = |g|`,
`\bar u u' = g'/g - h'/h`; the second term integrates to `log h(1) - log h(0) = 0`, and the first
is the contour integral of `F'/F`, which the argument principle evaluates.  Classical
(Gohberg–Krein); no novelty claim.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral Metric
open scoped Real ContDiff

namespace RHTower

/-- A function holomorphic on a neighbourhood of a closed disc, zero-free on an inner circle. -/
structure DiscArgumentDatum where
  c : ℂ
  t : ℝ
  R : ℝ
  U : Set ℂ
  F : ℂ → ℂ
  t_pos : 0 < t
  t_lt_R : t < R
  isOpen : IsOpen U
  closedBall_subset : closedBall c R ⊆ U
  differentiableOn : DifferentiableOn ℂ F U
  ne_zero : ∀ ζ ∈ sphere c t, F ζ ≠ 0

namespace DiscArgumentDatum

variable (D : DiscArgumentDatum)

/-- The boundary circle, parametrized by `ℝ/ℤ`. -/
def boundary (x : ℝ) : ℂ := circleMap D.c D.t (2 * π * x)

/-- Boundary values of `F`. -/
def value (x : ℝ) : ℂ := D.F (D.boundary x)

/-- Boundary modulus of `F`. -/
def modulus (x : ℝ) : ℝ := ‖D.value x‖

/-- The boundary phase `F / |F|`. -/
def phase (x : ℝ) : ℂ := D.value x * ((D.modulus x : ℝ) : ℂ)⁻¹

theorem boundary_mem_sphere (x : ℝ) : D.boundary x ∈ sphere D.c D.t :=
  circleMap_mem_sphere _ D.t_pos.le _

theorem boundary_mem_U (x : ℝ) : D.boundary x ∈ D.U := by
  apply D.closedBall_subset
  exact sphere_subset_closedBall.trans (closedBall_subset_closedBall D.t_lt_R.le)
    (D.boundary_mem_sphere x)

theorem value_ne_zero (x : ℝ) : D.value x ≠ 0 := D.ne_zero _ (D.boundary_mem_sphere x)

theorem modulus_pos (x : ℝ) : 0 < D.modulus x := norm_pos_iff.mpr (D.value_ne_zero x)

theorem periodic_boundary : Function.Periodic D.boundary 1 := by
  intro x
  simp only [boundary, mul_add, mul_one]
  exact periodic_circleMap D.c D.t _

theorem periodic_value : Function.Periodic D.value 1 := fun x => by
  simp only [value, D.periodic_boundary x]

theorem periodic_modulus : Function.Periodic D.modulus 1 := fun x => by
  simp only [modulus, D.periodic_value x]

theorem periodic_phase : Function.Periodic D.phase 1 := fun x => by
  simp only [phase, D.periodic_value x, D.periodic_modulus x]

theorem norm_phase (x : ℝ) : ‖D.phase x‖ = 1 := by
  rw [phase, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (D.modulus_pos x), modulus, mul_inv_cancel₀ (norm_ne_zero_iff.mpr
      (D.value_ne_zero x))]

theorem hasDerivAt_boundary (x : ℝ) :
    HasDerivAt D.boundary ((2 * π) • (circleMap 0 D.t (2 * π * x) * I)) x := by
  have hlin : HasDerivAt (fun y : ℝ => 2 * π * y) (2 * π) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * π)
  exact (hasDerivAt_circleMap D.c D.t (2 * π * x)).scomp x hlin

theorem differentiableAt_F (x : ℝ) : DifferentiableAt ℂ D.F (D.boundary x) :=
  (D.differentiableOn _ (D.boundary_mem_U x)).differentiableAt
    (D.isOpen.mem_nhds (D.boundary_mem_U x))

theorem hasDerivAt_value (x : ℝ) :
    HasDerivAt D.value
      (deriv D.F (D.boundary x) * ((2 * π) • (circleMap 0 D.t (2 * π * x) * I))) x :=
  (D.differentiableAt_F x).hasDerivAt.comp x (D.hasDerivAt_boundary x)

theorem contDiff_value : ContDiff ℝ ∞ D.value := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hF : ContDiffAt ℂ ∞ D.F (D.boundary x) :=
    (D.differentiableOn.contDiffOn D.isOpen).contDiffAt
      (D.isOpen.mem_nhds (D.boundary_mem_U x))
  have hb : ContDiffAt ℝ ∞ D.boundary x :=
    ((contDiff_circleMap D.c D.t).comp (contDiff_const.mul contDiff_id)).contDiffAt
  exact (hF.restrict_scalars ℝ).comp x hb

theorem contDiff_modulus : ContDiff ℝ ∞ D.modulus := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (D.contDiff_value.contDiffAt).norm ℂ (D.value_ne_zero x)

theorem contDiff_phase : ContDiff ℝ ∞ D.phase := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hm : ContDiffAt ℝ ∞ (fun y => ((D.modulus y : ℝ) : ℂ)) x :=
    (ofRealCLM.contDiff.comp D.contDiff_modulus).contDiffAt
  have hinv : ContDiffAt ℝ ∞ (fun y => ((D.modulus y : ℝ) : ℂ))⁻¹ x :=
    hm.inv (ofReal_ne_zero.mpr (D.modulus_pos x).ne')
  exact D.contDiff_value.contDiffAt.mul hinv

/-- The boundary phase as a smooth circle function. -/
def smoothPhase : SmoothCircleFunction where
  f := D.phase
  f' := deriv D.phase
  f'' := deriv (deriv D.phase)
  periodic := D.periodic_phase
  hasDerivAt x := ((D.contDiff_phase.differentiable (by simp)) x).hasDerivAt
  hasDerivAt' x :=
    (((D.contDiff_phase.iterate_deriv 1).differentiable (by simp)) x).hasDerivAt
  continuous'' := (D.contDiff_phase.iterate_deriv 2).continuous

/-- The boundary phase as a circle phase. -/
def circlePhase : CCMCirclePhase := D.smoothPhase.toPhase D.norm_phase

/-- `\bar u u' = g'/g - h'/h`. -/
theorem conj_phase_mul_deriv (x : ℝ) :
    starRingEnd ℂ (D.phase x) * deriv D.phase x =
      deriv D.F (D.boundary x) * ((2 * π) • (circleMap 0 D.t (2 * π * x) * I)) / D.value x -
        ((deriv D.modulus x / D.modulus x : ℝ) : ℂ) := by
  have hg := D.hasDerivAt_value x
  have hh : HasDerivAt D.modulus (deriv D.modulus x) x :=
    ((D.contDiff_modulus.differentiable (by simp)) x).hasDerivAt
  have hhC : HasDerivAt (fun y => ((D.modulus y : ℝ) : ℂ)) ((deriv D.modulus x : ℝ) : ℂ) x :=
    hh.ofReal_comp
  have hne : ((D.modulus x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (D.modulus_pos x).ne'
  have hinv := hhC.inv hne
  have hprod := hg.mul hinv
  have hphase : D.phase = D.value * (fun y => ((D.modulus y : ℝ) : ℂ))⁻¹ := by
    funext y; rfl
  rw [hphase, hprod.deriv]
  have hg0 := D.value_ne_zero x
  have hconj : starRingEnd ℂ (D.value x) = ((D.modulus x : ℝ) : ℂ) ^ 2 / D.value x := by
    rw [eq_div_iff hg0, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, modulus]
    push_cast
    ring
  simp only [Pi.mul_apply, Pi.inv_apply, map_mul, map_inv₀, Complex.conj_ofReal, hconj]
  push_cast
  field_simp
  ring

theorem integral_modulus_logDeriv :
    ∫ x in (0 : ℝ)..1, ((deriv D.modulus x / D.modulus x : ℝ) : ℂ) = 0 := by
  rw [intervalIntegral.integral_ofReal]
  have hcont : Continuous fun x => deriv D.modulus x / D.modulus x :=
    (D.contDiff_modulus.continuous_deriv (by simp)).div D.contDiff_modulus.continuous
      fun x => (D.modulus_pos x).ne'
  have hlog : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y => Real.log (D.modulus y)) (deriv D.modulus x / D.modulus x) x :=
    fun x _ => (((D.contDiff_modulus.differentiable (by simp)) x).hasDerivAt).log
      (D.modulus_pos x).ne'
  rw [integral_eq_sub_of_hasDerivAt hlog (hcont.intervalIntegrable 0 1)]
  have h10 : D.modulus 1 = D.modulus 0 := by simpa using D.periodic_modulus 0
  rw [h10, sub_self, ofReal_zero]

theorem integral_value_logDeriv :
    ∫ x in (0 : ℝ)..1,
        deriv D.F (D.boundary x) * ((2 * π) • (circleMap 0 D.t (2 * π * x) * I)) / D.value x =
      ∮ z in C(D.c, D.t), logDeriv D.F z := by
  set φ : ℝ → ℂ := fun θ => deriv (circleMap D.c D.t) θ • logDeriv D.F (circleMap D.c D.t θ)
    with hφ
  have hpt : ∀ x : ℝ,
      deriv D.F (D.boundary x) * ((2 * π) • (circleMap 0 D.t (2 * π * x) * I)) / D.value x =
        (2 * π : ℝ) • φ (2 * π * x) := by
    intro x
    simp only [hφ, deriv_circleMap, logDeriv_apply, value, boundary, real_smul, smul_eq_mul]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_smul, intervalIntegral.integral_comp_mul_left φ
    (by positivity : (2 * π : ℝ) ≠ 0), smul_smul, mul_inv_cancel₀ (by positivity), one_smul,
    mul_zero, mul_one, circleIntegral]

/-- **The winding integral of the boundary phase is the contour integral of `F'/F`.** -/
theorem integral_conj_phase_mul_deriv :
    ∫ x in (0 : ℝ)..1, starRingEnd ℂ (D.phase x) * deriv D.phase x =
      ∮ z in C(D.c, D.t), logDeriv D.F z := by
  have hcont1 : Continuous fun x => starRingEnd ℂ (D.phase x) * deriv D.phase x :=
    (Complex.continuous_conj.comp D.contDiff_phase.continuous).mul
      (D.contDiff_phase.continuous_deriv (by simp))
  have hcont2 : Continuous fun x => ((deriv D.modulus x / D.modulus x : ℝ) : ℂ) :=
    continuous_ofReal.comp ((D.contDiff_modulus.continuous_deriv (by simp)).div
      D.contDiff_modulus.continuous fun x => (D.modulus_pos x).ne')
  have hsum : ∀ x : ℝ,
      deriv D.F (D.boundary x) * ((2 * π) • (circleMap 0 D.t (2 * π * x) * I)) / D.value x =
        starRingEnd ℂ (D.phase x) * deriv D.phase x +
          ((deriv D.modulus x / D.modulus x : ℝ) : ℂ) := by
    intro x
    rw [D.conj_phase_mul_deriv x]
    ring
  rw [← D.integral_value_logDeriv]
  simp_rw [hsum]
  rw [intervalIntegral.integral_add (hcont1.intervalIntegrable 0 1)
    (hcont2.intervalIntegrable 0 1), D.integral_modulus_logDeriv, add_zero]

/-- **Gohberg–Krein index theorem for a boundary phase.**  The relative index of the pair
`(U† P U, P)`, `U` multiplication by `F/|F|` on the circle `|z - c| = t`, is the number of zeros of
`F` inside the circle, with multiplicity. -/
theorem relativeIndex_eq_zeroCount :
    ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball D.c D.t) ∧
      (∀ z ∈ ball D.c D.t, D.F z = 0 ↔ z ∈ Z) ∧
      restrictedProjectionRelativeIndex D.circlePhase.datum.conjugateProjection
          D.circlePhase.datum.projection =
        ∑ ρ ∈ Z, (GaloisForLFunctions.HTGeometry.zeroMult D.F ρ : ℤ) := by
  obtain ⟨Z, hZball, hZzero, hint⟩ :=
    GaloisForLFunctions.HTGeometry.exists_zeroSet_circleIntegral_logDeriv D.t_pos D.t_lt_R
      D.isOpen D.closedBall_subset D.differentiableOn D.ne_zero
  refine ⟨Z, hZball, hZzero, ?_⟩
  have h := D.smoothPhase.relativeIndex_toPhase_eq_integral D.norm_phase
  change ((restrictedProjectionRelativeIndex D.circlePhase.datum.conjugateProjection
      D.circlePhase.datum.projection : ℤ) : ℂ) =
    (2 * π * I)⁻¹ * ∫ x in (0 : ℝ)..1, starRingEnd ℂ (D.phase x) * deriv D.phase x at h
  rw [D.integral_conj_phase_mul_deriv, hint] at h
  have hpi : (2 * π * I : ℂ) ≠ 0 := by
    have := Real.pi_ne_zero
    simp [this, I_ne_zero]
  rw [← mul_assoc, inv_mul_cancel₀ hpi, one_mul] at h
  exact_mod_cast h

/-- The cubic trace of the boundary-phase pair counts the zeros inside the circle. -/
theorem opTrace_cubicDefect_eq_zeroCount :
    ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball D.c D.t) ∧
      (∀ z ∈ ball D.c D.t, D.F z = 0 ↔ z ∈ Z) ∧
      ContinuousLinearMap.opTrace (restrictedProjectionCubicDefect
          D.circlePhase.datum.conjugateProjection D.circlePhase.datum.projection) =
        ∑ ρ ∈ Z, (GaloisForLFunctions.HTGeometry.zeroMult D.F ρ : ℂ) := by
  obtain ⟨Z, hZball, hZzero, hidx⟩ := D.relativeIndex_eq_zeroCount
  refine ⟨Z, hZball, hZzero, ?_⟩
  rw [D.circlePhase.datum.opTrace_cubicDefect_eq_relativeIndex, hidx]
  push_cast
  rfl

end DiscArgumentDatum

end RHTower
