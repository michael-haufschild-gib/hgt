import GaloisForLFunctions.RHTower.XiRightDiscPhaseIndexRiemannHypothesis
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenvalue
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-!
# Hankel seams of holomorphic boundary phases

Let `(P, U)` be a restricted-unitary datum with conjugate projection `R = U† P U`.

* **Abstract seam law.**  The adjoint Hankel seam `(1 − P) U† P` is Hilbert–Schmidt, and it is a
  strict contraction as soon as `Ran R ∩ Ker P = 0`.  If its norm were one, the compact positive
  operator `S = seam† seam` would attain the eigenvalue one.  The eigenvector `x` then has
  `P x = x`, and `y = U† x` is a unit vector in `Ran R ∩ Ker P`.
* **Coburn injectivity for holomorphic phases.**  For the boundary phase `u = F/|F|` of a function
  holomorphic near a closed disc and zero-free on its circle, `P M_u` is injective on `Ran P`.
  The boundary values `g = F ∘ γ` have no negative Fourier modes (Cauchy), so `M_g` preserves
  `Ran P`.  Write `g = s² u` with `s = |g|^{1/2}`.  If `P M_u f = 0` with `P f = f`, then
  `‖M_s M_u f‖² = ⟪M_u f, M_g f⟫ = 0`, hence `f = 0`.

Consequences:
* the forward seam `(1 − P) U P` of every holomorphic boundary phase is a strict contraction;
* the adjoint seam contracts exactly when the disc contains no zero.

For `xi` on discs strictly right of the critical line this gives
`riemannHypothesis_iff_forall_xiRightDisc_adjointSeam_lt_one`: RH holds iff every such adjoint seam
is a strict contraction.  Classical Toeplitz theory (Coburn, Gohberg–Krein); no novelty claim.
-/

noncomputable section

open Complex MeasureTheory Metric ContinuousLinearMap
open scoped Real InnerProductSpace

namespace RHTower

/-! ## The abstract seam law -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Pythagoras for an orthogonal projection. -/
theorem norm_sq_eq_add_of_orthogonalProjection (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (hPadj : adjoint P = P) (y : H) : ‖y‖ ^ 2 = ‖P y‖ ^ 2 + ‖y - P y‖ ^ 2 := by
  have hPP : P (P y) = P y := by
    have := congrArg (fun T : H →L[ℂ] H => T y) hP.eq
    simpa [mul_apply_eq_comp] using this
  have hself : inner ℂ (P y) y = inner ℂ y (P y) :=
    calc inner ℂ (P y) y = inner ℂ (adjoint P y) y := by rw [hPadj]
      _ = inner ℂ y (P y) := adjoint_inner_left _ _ _
  have hPPi : inner ℂ (P y) (P y) = inner ℂ y (P y) :=
    calc inner ℂ (P y) (P y) = inner ℂ (adjoint P y) (P y) := by rw [hPadj]
      _ = inner ℂ y (P (P y)) := adjoint_inner_left _ _ _
      _ = inner ℂ y (P y) := by rw [hPP]
  have horth : inner ℂ (P y) (y - P y) = 0 := by
    rw [inner_sub_right, hself, hPPi, sub_self]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P y) (y - P y) horth
  rw [add_sub_cancel] at h
  nlinarith [h]

/-- **Seam law.**  If `Ran R ∩ Ker P = 0`, the adjoint Hankel seam is a strict contraction. -/
theorem RestrictedUnitaryDatum.norm_adjointHankelSeam_lt_one (D : RestrictedUnitaryDatum H)
    (hker : ∀ y : H, D.conjugateProjection y = y → D.projection y = 0 → y = 0) :
    ‖D.adjointHankelSeam‖ < 1 := by
  set P := D.projection with hPdef
  set U := D.unitary with hUdef
  set Hs := D.adjointHankelSeam with hHsdef
  have hPadj : adjoint P = P := D.projection_adjoint
  have hUU : ∀ w : H, U (adjoint U w) = w := fun w => by
    have := congrArg (fun T : H →L[ℂ] H => T w) D.unitary_mul_adjoint
    simpa [mul_apply_eq_comp] using this
  have hiso : ∀ w : H, ‖adjoint U w‖ = ‖w‖ := by
    intro w
    have hsq : ‖adjoint U w‖ ^ 2 = ‖w‖ ^ 2 := by
      rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, adjoint_inner_left, hUU]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
  have hproj := norm_sq_eq_add_of_orthogonalProjection P D.projection_idempotent hPadj
  have hPle : ∀ y : H, ‖P y‖ ≤ ‖y‖ := fun y => by
    have := hproj y
    nlinarith [norm_nonneg (P y), norm_nonneg y, sq_nonneg ‖y - P y‖]
  have hQle : ∀ y : H, ‖y - P y‖ ≤ ‖y‖ := fun y => by
    have := hproj y
    nlinarith [norm_nonneg (y - P y), norm_nonneg y, sq_nonneg ‖P y‖]
  have hHs_apply : ∀ x : H, Hs x = adjoint U (P x) - P (adjoint U (P x)) := by
    intro x
    change ((1 - P) * adjoint U * P) x = _
    simp [mul_apply_eq_comp, sub_apply]
  have hle : ‖Hs‖ ≤ 1 := by
    refine opNorm_le_bound _ zero_le_one fun x => ?_
    rw [hHs_apply, one_mul]
    calc ‖adjoint U (P x) - P (adjoint U (P x))‖ ≤ ‖adjoint U (P x)‖ := hQle _
      _ = ‖P x‖ := hiso _
      _ ≤ ‖x‖ := hPle x
  by_contra hnot
  push Not at hnot
  have hHs1 : ‖Hs‖ = 1 := le_antisymm hle hnot
  set S : H →L[ℂ] H := adjoint Hs ∘L Hs with hSdef
  have hcS : IsCompactOperator S :=
    D.adjointHankelSeam_isHilbertSchmidt.isCompactOperator.clm_comp (adjoint Hs)
  have hsym : (S : H →ₗ[ℂ] H).IsSymmetric := by
    intro x y
    change inner ℂ (adjoint Hs (Hs x)) y = inner ℂ x (adjoint Hs (Hs y))
    rw [adjoint_inner_left, adjoint_inner_right]
  have hSnorm : ‖S‖ = 1 := by
    rw [hSdef, norm_adjoint_comp_self, hHs1, mul_one]
  have hS0 : S ≠ 0 := by
    intro h
    rw [h, norm_zero] at hSnorm
    exact zero_ne_one hSnorm
  obtain ⟨μ, x, hμ, hx1, hSx⟩ := exists_unit_eigenvector_norm hcS hsym hS0
  have hinner : inner ℂ x (S x) = ((‖Hs x‖ ^ 2 : ℝ) : ℂ) := by
    change inner ℂ x (adjoint Hs (Hs x)) = _
    rw [adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hinner' : inner ℂ x (S x) = (μ : ℂ) := by
    rw [hSx, inner_smul_right, inner_self_eq_norm_sq_to_K, hx1]
    simp
  have hμeq : μ = ‖Hs x‖ ^ 2 := by
    have := hinner'.symm.trans hinner
    exact_mod_cast this
  have hμpos : 0 ≤ μ := by rw [hμeq]; positivity
  rw [hSnorm, abs_of_nonneg hμpos] at hμ
  have hHsx : ‖Hs x‖ ^ 2 = 1 := by rw [← hμeq, hμ]
  set y := adjoint U (P x) with hydef
  have hy_le : ‖y‖ ≤ 1 := by rw [hydef, hiso, ← hx1]; exact hPle x
  have hHsy : Hs x = y - P y := hHs_apply x
  have hproj_y := hproj y
  rw [← hHsy, hHsx] at hproj_y
  have hy_sq : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
  have hPy0 : ‖P y‖ = 0 := by nlinarith [norm_nonneg (P y)]
  have hy1 : ‖y‖ = 1 := by nlinarith [norm_nonneg y, norm_nonneg (P y)]
  have hPx1 : ‖P x‖ = 1 := by
    have h := hiso (P x)
    rw [← hydef, hy1] at h
    exact h.symm
  have hproj_x := hproj x
  rw [hx1, hPx1] at hproj_x
  have hxPx : x - P x = 0 := by
    have : ‖x - P x‖ = 0 := by nlinarith [norm_nonneg (x - P x)]
    exact norm_eq_zero.mp this
  have hPx : P x = x := (sub_eq_zero.mp hxPx).symm
  have hRy : D.conjugateProjection y = y := by
    change (adjoint U * P * U) y = y
    simp only [mul_apply_eq_comp]
    rw [hydef, hUU, hPx, hPx]
  have hy0 := hker y hRy (norm_eq_zero.mp hPy0)
  rw [hy0, norm_zero] at hy1
  exact zero_ne_one hy1

end Abstract

/-! ## Circle multipliers -/

/-- A continuous circle function as a bounded symbol. -/
def continuousCircleSymbol (g : AddCircle (1 : ℝ) → ℂ) (hg : Continuous g) :
    CCMCircleBoundedSymbol where
  toFun := g
  bound := max (Classical.choose (isCompact_univ.exists_bound_of_continuousOn hg.continuousOn)) 0
  bound_nonneg := le_max_right _ _
  measurable := hg.measurable
  norm_le z := (Classical.choose_spec (isCompact_univ.exists_bound_of_continuousOn
    hg.continuousOn) z (Set.mem_univ z)).trans (le_max_left _ _)

theorem ccmCircleMultiplier_coeFn (a : CCMCircleBoundedSymbol) (f : CCMCircleL2) :
    ((ccmCircleMultiplier a f : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun z => a.toFun z * (f : AddCircle (1 : ℝ) → ℂ) z :=
  lpBoundedMulCLM_coeFn _ _ _ f

/-- Multipliers compose by pointwise multiplication of their symbols. -/
theorem ccmCircleMultiplier_mul_eq (a b c : CCMCircleBoundedSymbol)
    (h : ∀ z, a.toFun z * b.toFun z = c.toFun z) :
    ccmCircleMultiplier a * ccmCircleMultiplier b = ccmCircleMultiplier c := by
  ext1 f
  apply Lp.ext
  change ((ccmCircleMultiplier a (ccmCircleMultiplier b f) : CCMCircleL2) :
    AddCircle (1 : ℝ) → ℂ) =ᵐ[_] _
  filter_upwards [ccmCircleMultiplier_coeFn a (ccmCircleMultiplier b f),
    ccmCircleMultiplier_coeFn b f, ccmCircleMultiplier_coeFn c f] with z h1 h2 h3
  rw [h1, h2, h3, ← mul_assoc, h z]

/-- A multiplier by the constant symbol one is the identity. -/
theorem ccmCircleMultiplier_eq_one (c : CCMCircleBoundedSymbol) (h : ∀ z, c.toFun z = 1) :
    ccmCircleMultiplier c = 1 := by
  ext1 f
  apply Lp.ext
  filter_upwards [ccmCircleMultiplier_coeFn c f] with z h1
  rw [h1, h z, one_mul]
  rfl

/-- A symbol without negative Fourier modes maps the Hardy space into itself. -/
theorem one_sub_hardy_mul_multiplier_mul_hardy_eq_zero (a : CCMCircleBoundedSymbol)
    (ha : ∀ n : ℤ, n < 0 → fourierCoeff a.toFun n = 0) :
    (1 - ccmCircleHardyProjection) * ccmCircleMultiplier a * ccmCircleHardyProjection = 0 := by
  have hdense : Dense ((Submodule.span ℂ (Set.range
      (fourierBasis (T := (1 : ℝ))))) : Set CCMCircleL2) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
      (fourierBasis (T := (1 : ℝ))).dense_span]
    rfl
  apply ContinuousLinearMap.ext_on hdense
  rintro _ ⟨j, rfl⟩
  rw [coe_fourierBasis]
  simp only [mul_apply_eq_comp, zero_apply,
    ccmCircleHardyProjection_fourierLp]
  by_cases hj : 0 ≤ j
  · rw [if_pos hj]
    apply (fourierBasis (T := (1 : ℝ))).repr.injective
    ext l
    rw [map_zero, HilbertBasis.repr_apply_apply, coe_fourierBasis,
      inner_fourierLp_one_sub_ccmCircleHardyProjection]
    by_cases hl : l < 0
    · rw [if_pos hl, GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff,
        ccmCircleMultiplier_fourierCoeff, ha _ (by omega)]
      rfl
    · rw [if_neg hl]
      rfl
  · rw [if_neg hj, map_zero, map_zero]

/-! ## Coburn injectivity for holomorphic boundary phases -/

namespace DiscArgumentDatum

variable (D : DiscArgumentDatum)

/-- **Boundary values of a holomorphic function have no negative Fourier modes** (Cauchy). -/
theorem fourierCoeff_circleLift_value_of_neg {n : ℤ} (hn : n < 0) :
    fourierCoeff (circleLift D.value) n = 0 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -n - 1 := ⟨(-n - 1).toNat, by omega⟩
  set φ : ℝ → ℂ := fun θ =>
    Complex.exp (((m + 1 : ℕ) : ℂ) * (θ * I)) * D.F (circleMap D.c D.t θ) with hφdef
  have hsubU : closedBall D.c D.t ⊆ D.U :=
    (closedBall_subset_closedBall D.t_lt_R.le).trans D.closedBall_subset
  have hcauchy : (∮ z in C(D.c, D.t), D.F z * (z - D.c) ^ m) = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable D.t_pos.le
      Set.countable_empty
    · exact (D.differentiableOn.continuousOn.mono hsubU).mul
        ((continuous_id.sub continuous_const).pow m).continuousOn
    · intro z hz
      have hzU : z ∈ D.U := hsubU (ball_subset_closedBall hz.1)
      exact ((D.differentiableOn z hzU).differentiableAt (D.isOpen.mem_nhds hzU)).mul
        ((differentiableAt_id.sub (differentiableAt_const _)).pow m)
  have hcirc : (∮ z in C(D.c, D.t), D.F z * (z - D.c) ^ m) =
      I * (D.t : ℂ) ^ (m + 1) * ∫ θ in (0 : ℝ)..2 * π, φ θ := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hφdef, deriv_circleMap, circleMap_sub_center, smul_eq_mul]
    rw [circleMap_zero, show ((m + 1 : ℕ) : ℂ) * (θ * I) = ((m + 1 : ℕ) : ℂ) * ((θ : ℂ) * I) by
      rfl, Complex.exp_nat_mul]
    ring
  have hφint : ∫ θ in (0 : ℝ)..2 * π, φ θ = 0 := by
    have hne : I * (D.t : ℂ) ^ (m + 1) ≠ 0 :=
      mul_ne_zero I_ne_zero (pow_ne_zero _ (ofReal_ne_zero.mpr D.t_pos.ne'))
    rw [hcauchy] at hcirc
    exact (mul_eq_zero.mp hcirc.symm).resolve_left hne
  rw [fourierCoeff_circleLift]
  have hpt : ∀ x : ℝ, fourier (-n) (x : AddCircle (1 : ℝ)) * D.value x = φ (2 * π * x) := by
    intro x
    rw [fourier_coe_apply]
    simp only [hφdef, value, boundary]
    congr 1
    congr 1
    have hmC : ((m + 1 : ℕ) : ℂ) = ((-n : ℤ) : ℂ) := by
      rw [show ((-n : ℤ)) = ((m + 1 : ℕ) : ℤ) by push_cast; omega]
      push_cast
      ring
    rw [hmC]
    push_cast
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_comp_mul_left φ (by positivity : (2 * π : ℝ) ≠ 0), mul_zero,
    mul_one, hφint, smul_zero]

/-- The boundary values as a bounded symbol. -/
def valueSymbol : CCMCircleBoundedSymbol :=
  continuousCircleSymbol (circleLift D.value)
    (continuous_circleLift D.periodic_value D.contDiff_value.continuous)

theorem circleLift_value_ne_zero (z : AddCircle (1 : ℝ)) : circleLift D.value z ≠ 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [circleLift_coe D.periodic_value]
  exact D.value_ne_zero x

/-- `|g|^{1/2}` as a real bounded symbol. -/
def sqrtModulusSymbol : CCMCircleBoundedSymbol :=
  continuousCircleSymbol (fun z => ((Real.sqrt ‖circleLift D.value z‖ : ℝ) : ℂ))
    (continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_circleLift D.periodic_value D.contDiff_value.continuous).norm))

/-- `|g|^{-1/2}` as a bounded symbol. -/
def invSqrtModulusSymbol : CCMCircleBoundedSymbol :=
  continuousCircleSymbol (fun z => (((Real.sqrt ‖circleLift D.value z‖)⁻¹ : ℝ) : ℂ))
    (continuous_ofReal.comp ((Real.continuous_sqrt.comp
      (continuous_circleLift D.periodic_value D.contDiff_value.continuous).norm).inv₀
        fun z => (Real.sqrt_pos.mpr (norm_pos_iff.mpr (D.circleLift_value_ne_zero z))).ne'))

theorem circlePhase_toFun : D.circlePhase.toFun = circleLift D.phase := rfl

theorem continuous_sqrtModulus :
    Continuous fun z : AddCircle (1 : ℝ) => ((Real.sqrt ‖circleLift D.value z‖ : ℝ) : ℂ) :=
  continuous_ofReal.comp (Real.continuous_sqrt.comp
    (continuous_circleLift D.periodic_value D.contDiff_value.continuous).norm)

/-- `|g|^{1/2} u` as a bounded symbol. -/
def sqrtPhaseSymbol : CCMCircleBoundedSymbol :=
  continuousCircleSymbol
    (fun z => ((Real.sqrt ‖circleLift D.value z‖ : ℝ) : ℂ) * circleLift D.phase z)
    (D.continuous_sqrtModulus.mul
      (continuous_circleLift D.periodic_phase D.contDiff_phase.continuous))

theorem circleLift_phase_eq (z : AddCircle (1 : ℝ)) :
    circleLift D.phase z = circleLift D.value z * ((‖circleLift D.value z‖ : ℝ) : ℂ)⁻¹ := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [circleLift_coe D.periodic_phase, circleLift_coe D.periodic_value]
  rfl

theorem value_eq_sqrt_mul_sqrt_mul_phase (z : AddCircle (1 : ℝ)) :
    D.sqrtModulusSymbol.toFun z * (D.sqrtModulusSymbol.toFun z * D.circlePhase.toFun z) =
      D.valueSymbol.toFun z := by
  change ((Real.sqrt ‖circleLift D.value z‖ : ℝ) : ℂ) *
      (((Real.sqrt ‖circleLift D.value z‖ : ℝ) : ℂ) * circleLift D.phase z) =
    circleLift D.value z
  rw [D.circleLift_phase_eq, ← mul_assoc, ← ofReal_mul,
    Real.mul_self_sqrt (norm_nonneg _)]
  have hne : ((‖circleLift D.value z‖ : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (D.circleLift_value_ne_zero z))
  field_simp

theorem invSqrt_mul_sqrt (z : AddCircle (1 : ℝ)) :
    D.invSqrtModulusSymbol.toFun z * D.sqrtModulusSymbol.toFun z = 1 := by
  change (((Real.sqrt ‖circleLift D.value z‖)⁻¹ : ℝ) : ℂ) *
    ((Real.sqrt ‖circleLift D.value z‖ : ℝ) : ℂ) = 1
  rw [← ofReal_mul, inv_mul_cancel₀
    (Real.sqrt_pos.mpr (norm_pos_iff.mpr (D.circleLift_value_ne_zero z))).ne', ofReal_one]

/-- **Coburn injectivity.**  `P M_u` is injective on the Hardy space for a holomorphic phase. -/
theorem hardy_phase_injective (f : CCMCircleL2) (hf : ccmCircleHardyProjection f = f)
    (hPu : ccmCircleHardyProjection (D.circlePhase.multiplier f) = 0) : f = 0 := by
  set P := ccmCircleHardyProjection
  set Mu := D.circlePhase.multiplier
  set Ms := ccmCircleMultiplier D.sqrtModulusSymbol
  set Mg := ccmCircleMultiplier D.valueSymbol
  set v := Mu f with hvdef
  have hMg : Mg = Ms * (Ms * Mu) := by
    change Mg = Ms * (Ms * ccmCircleMultiplier
      D.circlePhase.toTraceSymbol.toCCMCircleBoundedSymbol)
    rw [ccmCircleMultiplier_mul_eq _ _ D.sqrtPhaseSymbol (fun z => rfl),
      ccmCircleMultiplier_mul_eq _ _ D.valueSymbol
        (fun z => D.value_eq_sqrt_mul_sqrt_mul_phase z)]
  have hHardy := one_sub_hardy_mul_multiplier_mul_hardy_eq_zero D.valueSymbol
    (fun n hn => D.fourierCoeff_circleLift_value_of_neg hn)
  have hMgf : P (Mg f) = Mg f := by
    have h := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T f) hHardy
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self,
      zero_apply] at h
    change Mg (P f) - P (Mg (P f)) = 0 at h
    rw [hf] at h
    exact (sub_eq_zero.mp h).symm
  have hPadj : adjoint P = P := ccmCircleHardyProjection_adjoint
  have hzero : inner ℂ v (Mg f) = 0 :=
    calc inner ℂ v (Mg f) = inner ℂ v (P (Mg f)) := by rw [hMgf]
      _ = inner ℂ v (adjoint P (Mg f)) := by rw [hPadj]
      _ = inner ℂ (P v) (Mg f) := adjoint_inner_right _ _ _
      _ = 0 := by rw [hPu, inner_zero_left]
  have hsqrt_real : ∀ z, (starRingEnd ℂ) (D.sqrtModulusSymbol.toFun z) =
      D.sqrtModulusSymbol.toFun z := fun z => Complex.conj_ofReal _
  have hMs_sym : ∀ a b : CCMCircleL2, inner ℂ (Ms a) b = inner ℂ a (Ms b) :=
    lpBoundedMulCLM_inner_real _ _ _ hsqrt_real
  have hnorm : inner ℂ v (Mg f) = ((‖Ms v‖ ^ 2 : ℝ) : ℂ) := by
    rw [hMg]
    change inner ℂ v (Ms (Ms (Mu f))) = _
    rw [← hvdef, ← hMs_sym, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hnorm] at hzero
  have hMsv : Ms v = 0 := by
    have : ‖Ms v‖ ^ 2 = 0 := by exact_mod_cast hzero
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  have hv : v = 0 := by
    have hinv := ccmCircleMultiplier_mul_eq D.invSqrtModulusSymbol D.sqrtModulusSymbol
      (continuousCircleSymbol (fun _ => 1) continuous_const) D.invSqrt_mul_sqrt
    rw [ccmCircleMultiplier_eq_one (continuousCircleSymbol (fun _ => 1) continuous_const)
      (fun _ => rfl)] at hinv
    have := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T v) hinv
    simp only [mul_apply_eq_comp, one_apply_eq_self] at this
    rw [← this]
    change ccmCircleMultiplier D.invSqrtModulusSymbol (Ms v) = 0
    rw [hMsv, map_zero]
  have hback := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T f)
    D.circlePhase.conjMultiplier_mul_multiplier
  simp only [mul_apply_eq_comp, one_apply_eq_self] at hback
  rw [← hback]
  change D.circlePhase.conjMultiplier v = 0
  rw [hv, map_zero]

/-- `Ran P ∩ Ker R = 0` for a holomorphic phase. -/
theorem ker_conjugate_inf_range_projection_trivial (f : CCMCircleL2)
    (hf : D.circlePhase.datum.projection f = f)
    (hRf : D.circlePhase.datum.conjugateProjection f = 0) : f = 0 := by
  apply D.hardy_phase_injective f hf
  have h : adjoint D.circlePhase.multiplier
      (ccmCircleHardyProjection (D.circlePhase.multiplier f)) = 0 := hRf
  have hU := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T
      (ccmCircleHardyProjection (D.circlePhase.multiplier f)))
    D.circlePhase.datum.unitary_mul_adjoint
  simp only [mul_apply_eq_comp, one_apply_eq_self] at hU
  rw [← hU]
  change D.circlePhase.multiplier (adjoint D.circlePhase.multiplier
    (ccmCircleHardyProjection (D.circlePhase.multiplier f))) = 0
  rw [h, map_zero]

/-- **The forward seam of a holomorphic phase always contracts.** -/
theorem norm_forwardHankelSeam_lt_one :
    ‖D.circlePhase.datum.forwardHankelSeam‖ < 1 := by
  have h := D.circlePhase.datum.adjointDatum.norm_adjointHankelSeam_lt_one ?_
  · have heq : D.circlePhase.datum.adjointDatum.adjointHankelSeam =
        D.circlePhase.datum.forwardHankelSeam := by
      change (1 - D.circlePhase.datum.projection) *
          adjoint (adjoint D.circlePhase.datum.unitary) * D.circlePhase.datum.projection = _
      rw [adjoint_adjoint]
      rfl
    rwa [heq] at h
  · intro y hy hPy
    set U := D.circlePhase.datum.unitary
    set P := D.circlePhase.datum.projection
    have hUU : ∀ w, U (adjoint U w) = w := fun w => by
      have := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T w)
        D.circlePhase.datum.unitary_mul_adjoint
      simpa [mul_apply_eq_comp] using this
    have hUaU : ∀ w, adjoint U (U w) = w := fun w => by
      have := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T w)
        D.circlePhase.datum.adjoint_mul_unitary
      simpa [mul_apply_eq_comp] using this
    have hy' : U (P (adjoint U y)) = y := by
      have : (adjoint (adjoint U) * P * adjoint U) y = y := hy
      simpa [mul_apply_eq_comp, adjoint_adjoint] using this
    set z := adjoint U y with hzdef
    have hPz : P z = z := by
      have := congrArg (adjoint U) hy'
      rw [hUaU] at this
      exact this
    have hz0 : z = 0 := by
      apply D.hardy_phase_injective z hPz
      change P (U z) = 0
      rw [hzdef, hUU]
      exact hPy
    rw [← hUU y, ← hzdef, hz0, map_zero]

end DiscArgumentDatum

/-! ## The exact route-1 equivalence for `xi` -/

/-- Under RH the adjoint seam of the `xi` boundary phase contracts on every right disc. -/
theorem xiDisc_adjointSeam_lt_one_of_riemannHypothesis (hRH : RiemannHypothesis)
    (c : ℂ) (t : ℝ) (ht : 0 < t) (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0)
    (hright : ∀ z ∈ closedBall c t, 1 / 2 < z.re) :
    ‖(xiDiscDatum c t ht hne).circlePhase.datum.adjointHankelSeam‖ < 1 := by
  set D := (xiDiscDatum c t ht hne).circlePhase.datum with hD
  apply D.norm_adjointHankelSeam_lt_one
  intro y hRy hPy
  have hidx := xiDiscRelativeIndex_eq_zero_of_riemannHypothesis hRH c t ht hne hright
  unfold xiDiscRelativeIndex at hidx
  rw [← hD, D.relativeIndex_eq_intersection_finrank_sub] at hidx
  have hbot : LinearMap.range (D.projection : CCMCircleL2 →ₗ[ℂ] CCMCircleL2) ⊓
      LinearMap.ker (D.conjugateProjection : CCMCircleL2 →ₗ[ℂ] CCMCircleL2) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_inf, mem_range_restrictedProjection_iff_apply_eq _
      D.projection_idempotent, LinearMap.mem_ker] at hf
    rw [Submodule.mem_bot]
    exact (xiDiscDatum c t ht hne).ker_conjugate_inf_range_projection_trivial f hf.1 hf.2
  rw [hbot, finrank_bot, Nat.cast_zero, sub_zero, Nat.cast_eq_zero] at hidx
  have hfin : FiniteDimensional ℂ ↥(LinearMap.range
      (D.conjugateProjection : CCMCircleL2 →ₗ[ℂ] CCMCircleL2) ⊓
        LinearMap.ker (D.projection : CCMCircleL2 →ₗ[ℂ] CCMCircleL2)) := by
    rw [← eigenspace_restrictedProjectionDisplacement_one_eq_range_inf_ker _ _
      D.conjugateProjection_idempotent D.projection_idempotent
      D.conjugateProjection_adjoint D.projection_adjoint]
    exact ContinuousLinearMap.finite_dimensional_eigenspace
      D.displacement_isHilbertSchmidt.isCompactOperator 1 one_ne_zero
  have hbot' := Submodule.finrank_eq_zero.mp hidx
  have hmem : y ∈ LinearMap.range (D.conjugateProjection : CCMCircleL2 →ₗ[ℂ] CCMCircleL2) ⊓
      LinearMap.ker (D.projection : CCMCircleL2 →ₗ[ℂ] CCMCircleL2) := by
    rw [Submodule.mem_inf, mem_range_restrictedProjection_iff_apply_eq _
      D.conjugateProjection_idempotent, LinearMap.mem_ker]
    exact ⟨hRy, hPy⟩
  rw [hbot', Submodule.mem_bot] at hmem
  exact hmem

/-- **RH as adjoint-seam contraction.**  The Riemann hypothesis holds if and only if, on every
circle bounding a closed disc strictly right of the critical line and avoiding the zeros of
`xi`, the adjoint Hankel seam `(1 − P) U† P` of the `xi` boundary phase is a strict contraction. -/
theorem riemannHypothesis_iff_forall_xiRightDisc_adjointSeam_lt_one :
    RiemannHypothesis ↔
      ∀ (c : ℂ) (t : ℝ) (ht : 0 < t) (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0),
        (∀ z ∈ closedBall c t, 1 / 2 < z.re) →
          ‖(xiDiscDatum c t ht hne).circlePhase.datum.adjointHankelSeam‖ < 1 :=
  ⟨fun hRH c t ht hne hright =>
      xiDisc_adjointSeam_lt_one_of_riemannHypothesis hRH c t ht hne hright,
    riemannHypothesis_of_forall_xiRightDisc_adjointSeam_lt_one⟩

end RHTower
