import Mathlib
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator

/-!
# Duhamel source response of a cyclic dissipative source

A cyclic dissipative source on a finite-dimensional complex Hilbert space `H` is a self-adjoint
operator `L` with `Re ⟨x, L x⟩ > 0` for `x ≠ 0` and a vector `v` whose orbit `Lⁿ v` spans `H`
`(SR.1)`–`(SR.2)`.  Its semigroup is `S_t = exp(-t L)`, its orbit `x(t) = S_t v` `(SR.3)`, and an
intervention `K` has the first source response `Y_K(t) = -∫₀ᵗ S_{t-s} K S_s v ds` `(SR.4)`.

* Coercivity: `Re ⟨x, L x⟩ ≥ c ‖x‖²` for some `c > 0` (compactness of the unit sphere), hence the
  decay `‖S_t y‖ ≤ e^{-ct} ‖y‖` for `t ≥ 0` (the derivative of `e^{2ct} ‖S_t y‖²` is `≤ 0`).
* **`(SR.7)`–`(SR.8)`.**  `Y_K` is the derivative at `ε = 0` of `exp(-t(L + εK)) v`, by the exact
  Duhamel identity `x_ε(t) - x(t) = -ε ∫₀ᵗ S_{t-s} K x_ε(s) ds`, and it is the unique solution of
  `Y' + L Y = -K x`, `Y(0) = 0`.
* **`(SR.9)`.**  The orbit `{x(t) : 0 ≤ t ≤ T}` spans `H` (a vector orthogonal to it is orthogonal
  to every `Lⁿ v`, by repeated differentiation), so `K x(t) = -Y_K'(t) - L Y_K(t)` reconstructs `K`
  from its response on `[0, T]`.
* **`(SR.10)`–`(SR.11)`.**  The response work `W_T(K) = ∫₀ᵀ ‖Y_K‖²` is coercive:
  `W_T(K) ≥ c_T ‖K‖²_HS`; vanishing work forces vanishing interventions and work sublevels are
  compact.
-/

open Filter Topology Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- The rational scalar structure used by the exponential series. -/
abbrev operatorRatAlgebra (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NormedAlgebra ℚ (H →L[ℂ] H) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

attribute [local instance] operatorRatAlgebra

/-- A cyclic dissipative source `(SR.1)`–`(SR.2)`. -/
structure CyclicSource (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The generator. -/
  L : H →L[ℂ] H
  isSelfAdjoint : IsSelfAdjoint L
  pos : ∀ x : H, x ≠ 0 → 0 < RCLike.re ⟪x, L x⟫_ℂ
  /-- The marked cyclic vector. -/
  v : H
  cyclic : Submodule.span ℂ (Set.range fun n : ℕ => (L ^ n) v) = ⊤

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
/-- The product rule for a real path of complex operators applied to a real path of vectors. -/
theorem hasDerivAt_operator_apply {c : ℝ → H →L[ℂ] H} {c' : H →L[ℂ] H} {u : ℝ → H} {u' : H}
    {t : ℝ} (hc : HasDerivAt c c' t) (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => c s (u s)) (c' (u t) + c t u') t := by
  have hcR : HasDerivAt (fun s => (c s).restrictScalars ℝ) (c'.restrictScalars ℝ) t :=
    (ContinuousLinearMap.restrictScalarsL ℂ H H ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hc
  exact hcR.clm_apply hu

omit [FiniteDimensional ℂ H] in
/-- **Exponential decay**: a coercive generator `Re ⟨y, A y⟩ ≥ c ‖y‖²` gives
`‖exp(-tA) y‖ ≤ e^{-ct} ‖y‖` for `t ≥ 0`. -/
theorem norm_exp_neg_le (A : H →L[ℂ] H) {c : ℝ}
    (hcoer : ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ) {t : ℝ} (ht : 0 ≤ t) (y : H) :
    ‖NormedSpace.exp (t • -A) y‖ ≤ Real.exp (-(c * t)) * ‖y‖ := by
  set E : ℝ → H := fun s => NormedSpace.exp (s • -A) y
  set f : ℝ → ℝ := fun s => Real.exp (2 * c * s) * ‖E s‖ ^ 2
  have hyd : ∀ s, HasDerivAt E (-A (E s)) s := fun s => by
    have h := hasDerivAt_operator_apply (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-A) s)
      (hasDerivAt_const s y)
    simpa [E, mul_apply_eq_comp] using h
  have hfd : ∀ s, HasDerivAt f (Real.exp (2 * c * s) * (2 * c * ‖E s‖ ^ 2 -
      2 * RCLike.re ⟪E s, A (E s)⟫_ℂ)) s := by
    intro s
    have h1 : HasDerivAt (fun s => Real.exp (2 * c * s)) (Real.exp (2 * c * s) * (2 * c)) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 * c)).exp
    have h2 : HasDerivAt (fun s => ‖E s‖ ^ 2) (2 * RCLike.re ⟪E s, -A (E s)⟫_ℂ) s := by
      have hi := (hyd s).inner ℂ (hyd s)
      have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hi
      have hfun : (fun s => ‖E s‖ ^ 2) = fun s => Complex.reCLM ⟪E s, E s⟫_ℂ := by
        funext s
        rw [Complex.reCLM_apply, ← RCLike.re_to_complex, inner_self_eq_norm_sq]
      rw [hfun]
      refine hre.congr_deriv ?_
      rw [Complex.reCLM_apply, Complex.add_re, ← inner_conj_symm (-A (E s)) (E s),
        Complex.conj_re, RCLike.re_to_complex]
      ring
    refine (h1.mul h2).congr_deriv ?_
    rw [inner_neg_right, map_neg]
    ring
  have hanti : AntitoneOn f (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (continuous_iff_continuousAt.mpr fun s => (hfd s).continuousAt).continuousOn
      (fun s _ => (hfd s).differentiableAt.differentiableWithinAt) fun s _ => ?_
    rw [(hfd s).deriv]
    have := hcoer (E s)
    have he := Real.exp_pos (2 * c * s)
    nlinarith
  have h0 : f 0 = ‖y‖ ^ 2 := by simp [f, E]
  have hle := hanti (self_mem_Ici) ht ht
  rw [h0] at hle
  have he : 0 < Real.exp (2 * c * t) := Real.exp_pos _
  have hsq : ‖E t‖ ^ 2 ≤ (Real.exp (-(c * t)) * ‖y‖) ^ 2 := by
    have hexp : Real.exp (-(c * t)) ^ 2 = (Real.exp (2 * c * t))⁻¹ := by
      rw [sq, ← Real.exp_add, ← Real.exp_neg]
      ring_nf
    rw [mul_pow, hexp, inv_mul_eq_div, le_div_iff₀ he, mul_comm]
    exact hle
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

omit [CompleteSpace H] in
/-- **Coercivity in finite dimension**: a positive definite operator satisfies
`Re ⟨x, A x⟩ ≥ c ‖x‖²` for some `c > 0` (minimum of the form on the compact unit sphere). -/
theorem exists_coercive_of_pos (A : H →L[ℂ] H)
    (hpos : ∀ x : H, x ≠ 0 → 0 < RCLike.re ⟪x, A x⟫_ℂ) :
    ∃ c > 0, ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, A y⟫_ℂ := by
  by_cases hH : Nontrivial H
  · have hcpt : IsCompact (Metric.sphere (0 : H) 1) := isCompact_sphere 0 1
    have hne : (Metric.sphere (0 : H) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
    have hcont : ContinuousOn (fun y : H => RCLike.re ⟪y, A y⟫_ℂ) (Metric.sphere 0 1) :=
      (RCLike.continuous_re.comp (continuous_id.inner A.continuous)).continuousOn
    obtain ⟨y₀, hy₀, hmin⟩ := hcpt.exists_isMinOn hne hcont
    have hy₀ne : y₀ ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hy₀
      exact norm_ne_zero_iff.mp (by rw [hy₀]; exact one_ne_zero)
    refine ⟨_, hpos y₀ hy₀ne, fun y => ?_⟩
    by_cases hy : y = 0
    · simp [hy]
    have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
    set u : H := (‖y‖⁻¹ : ℂ) • y
    have hu : u ∈ Metric.sphere (0 : H) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ hny.ne']
    have h := hmin hu
    simp only [mem_setOf_eq] at h
    have hscale : RCLike.re ⟪u, A u⟫_ℂ = ‖y‖⁻¹ ^ 2 * RCLike.re ⟪y, A y⟫_ℂ := by
      simp only [u, map_smul, inner_smul_left, inner_smul_right]
      rw [map_inv₀, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
        RCLike.re_to_complex, Complex.re_ofReal_mul, RCLike.re_to_complex]
      ring
    rw [hscale] at h
    have hy2 : 0 < ‖y‖ ^ 2 := by positivity
    calc RCLike.re ⟪y₀, A y₀⟫_ℂ * ‖y‖ ^ 2
        ≤ ‖y‖⁻¹ ^ 2 * RCLike.re ⟪y, A y⟫_ℂ * ‖y‖ ^ 2 := by gcongr
      _ = RCLike.re ⟪y, A y⟫_ℂ := by field_simp
  · have hsub : Subsingleton H := not_nontrivial_iff_subsingleton.mp hH
    exact ⟨1, one_pos, fun y => by simp [Subsingleton.elim y 0]⟩

namespace CyclicSource

variable (σ : CyclicSource H)

/-- The semigroup `S_t = exp(-t L)` `(SR.3)`. -/
def S (t : ℝ) : H →L[ℂ] H := NormedSpace.exp (t • -σ.L)

/-- The orbit `x(t) = S_t v` `(SR.3)`. -/
def x (t : ℝ) : H := σ.S t σ.v

omit [FiniteDimensional ℂ H] in
theorem S_zero : σ.S 0 = 1 := by simp [S]

omit [FiniteDimensional ℂ H] in
theorem S_add (t s : ℝ) : σ.S (t + s) = σ.S t * σ.S s := by
  rw [S, S, S, add_smul]
  exact NormedSpace.exp_add_of_commute ((Commute.refl (-σ.L)).smul_left t |>.smul_right s)

omit [FiniteDimensional ℂ H] in
theorem S_mul_S_neg (t : ℝ) : σ.S t * σ.S (-t) = 1 := by
  rw [← S_add, add_neg_cancel, S_zero]

omit [FiniteDimensional ℂ H] in
theorem S_neg_mul_S (t : ℝ) : σ.S (-t) * σ.S t = 1 := by
  rw [← S_add, neg_add_cancel, S_zero]

omit [FiniteDimensional ℂ H] in
theorem commute_L_S (t : ℝ) : Commute σ.L (σ.S t) :=
  (((Commute.refl σ.L).neg_right).smul_right t).exp_right

omit [FiniteDimensional ℂ H] in
theorem hasDerivAt_S (t : ℝ) : HasDerivAt σ.S (-σ.L * σ.S t) t := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-σ.L) t
  exact h

omit [FiniteDimensional ℂ H] in
theorem hasDerivAt_x (t : ℝ) : HasDerivAt σ.x (-σ.L (σ.x t)) t := by
  show HasDerivAt (fun s => σ.S s σ.v) _ t
  have h := hasDerivAt_operator_apply (σ.hasDerivAt_S t) (hasDerivAt_const t σ.v)
  simpa [x, mul_apply_eq_comp] using h

omit [FiniteDimensional ℂ H] in
theorem continuous_S : Continuous σ.S :=
  continuous_iff_continuousAt.mpr fun t => (σ.hasDerivAt_S t).continuousAt

omit [FiniteDimensional ℂ H] in
theorem continuous_x : Continuous σ.x :=
  continuous_iff_continuousAt.mpr fun t => (σ.hasDerivAt_x t).continuousAt

/-- **Coercivity of the generator**: `Re ⟨x, L x⟩ ≥ c ‖x‖²` for some `c > 0`. -/
theorem exists_coercive : ∃ c > 0, ∀ y : H, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, σ.L y⟫_ℂ :=
  exists_coercive_of_pos σ.L σ.pos

/-- **Exponential decay** of the semigroup. -/
theorem exists_decay : ∃ c > 0, ∀ t ≥ 0, ∀ y : H, ‖σ.S t y‖ ≤ Real.exp (-(c * t)) * ‖y‖ := by
  obtain ⟨c, hc, hcoer⟩ := σ.exists_coercive
  exact ⟨c, hc, fun t ht y => norm_exp_neg_le σ.L hcoer ht y⟩

omit [FiniteDimensional ℂ H] in
theorem hasDerivAt_S_neg (t : ℝ) : HasDerivAt (fun s => σ.S (-s)) (σ.L * σ.S (-t)) t := by
  have h := (σ.hasDerivAt_S (-t)).scomp t (hasDerivAt_neg t)
  refine h.congr_deriv ?_
  simp

omit [FiniteDimensional ℂ H] in
theorem hasDerivAt_S_sub (t s : ℝ) : HasDerivAt (fun r => σ.S (t - r)) (σ.L * σ.S (t - s)) s := by
  have h := (σ.hasDerivAt_S (t - s)).scomp s ((hasDerivAt_const s t).sub (hasDerivAt_id s))
  refine h.congr_deriv ?_
  simp

omit [FiniteDimensional ℂ H] in
theorem S_apply_S_neg (t : ℝ) (y : H) : σ.S t (σ.S (-t) y) = y := by
  have h := congrArg (fun A : H →L[ℂ] H => A y) (σ.S_mul_S_neg t)
  simpa [mul_apply_eq_comp] using h

omit [FiniteDimensional ℂ H] in
theorem S_neg_apply_S (t : ℝ) (y : H) : σ.S (-t) (σ.S t y) = y := by
  have h := congrArg (fun A : H →L[ℂ] H => A y) (σ.S_neg_mul_S t)
  simpa [mul_apply_eq_comp] using h

omit [FiniteDimensional ℂ H] in
theorem L_S_apply (t : ℝ) (y : H) : σ.L (σ.S t y) = σ.S t (σ.L y) := by
  have h := congrArg (fun A : H →L[ℂ] H => A y) (σ.commute_L_S t).eq
  simpa [mul_apply_eq_comp] using h

omit [FiniteDimensional ℂ H] in
theorem x_zero : σ.x 0 = σ.v := by simp [x, S_zero]

/-! ### The first source response -/

/-- The first source response `Y_K(t) = -∫₀ᵗ S_{t-s} K S_s v ds` `(SR.4)`. -/
def response (K : H →L[ℂ] H) (t : ℝ) : H := -∫ s in (0 : ℝ)..t, σ.S (t - s) (K (σ.x s))

omit [FiniteDimensional ℂ H] in
theorem continuous_responseIntegrand (K : H →L[ℂ] H) :
    Continuous fun s => σ.S (-s) (K (σ.x s)) :=
  (σ.continuous_S.comp continuous_neg).clm_apply (K.continuous.comp σ.continuous_x)

omit [FiniteDimensional ℂ H] in
/-- `Y_K(t) = -S_t ∫₀ᵗ S_{-s} K x(s) ds`. -/
theorem response_eq (K : H →L[ℂ] H) (t : ℝ) :
    σ.response K t = -σ.S t (∫ s in (0 : ℝ)..t, σ.S (-s) (K (σ.x s))) := by
  rw [response]
  congr 1
  rw [show (σ.S t) (∫ s in (0 : ℝ)..t, σ.S (-s) (K (σ.x s))) =
      ((σ.S t).restrictScalars ℝ) (∫ s in (0 : ℝ)..t, σ.S (-s) (K (σ.x s))) from rfl,
    ← ((σ.S t).restrictScalars ℝ).intervalIntegral_comp_comm
      ((σ.continuous_responseIntegrand K).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [sub_eq_add_neg, S_add, mul_apply_eq_comp]

omit [FiniteDimensional ℂ H] in
theorem response_zero (K : H →L[ℂ] H) : σ.response K 0 = 0 := by simp [response]

/-- **`(SR.8)`: the response equation** `Y' + L Y = -K x`. -/
theorem hasDerivAt_response (K : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (σ.response K) (-σ.L (σ.response K t) - K (σ.x t)) t := by
  have hF : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, σ.S (-s) (K (σ.x s)))
      (σ.S (-t) (K (σ.x t))) t :=
    intervalIntegral.integral_hasDerivAt_right
      ((σ.continuous_responseIntegrand K).intervalIntegrable _ _)
      ((σ.continuous_responseIntegrand K).stronglyMeasurableAtFilter _ _)
      ((σ.continuous_responseIntegrand K).continuousAt)
  have h := (hasDerivAt_operator_apply (σ.hasDerivAt_S t) hF).neg
  rw [show σ.response K = fun t => -σ.S t (∫ s in (0 : ℝ)..t, σ.S (-s) (K (σ.x s))) from
    funext (σ.response_eq K)]
  refine h.congr_deriv ?_
  rw [σ.S_apply_S_neg]
  simp only [mul_apply_eq_comp, neg_apply, map_neg, neg_neg]
  abel

theorem continuous_response (K : H →L[ℂ] H) : Continuous (σ.response K) :=
  continuous_iff_continuousAt.mpr fun t => (σ.hasDerivAt_response K t).continuousAt

/-- **`(SR.8)`: uniqueness.**  `Y_K` is the only solution of `Y' + L Y = -K x`, `Y(0) = 0`. -/
theorem response_unique (K : H →L[ℂ] H) {Z : ℝ → H}
    (hZ : ∀ t, HasDerivAt Z (-σ.L (Z t) - K (σ.x t)) t) (hZ0 : Z 0 = 0) :
    Z = σ.response K := by
  set W : ℝ → H := fun t => Z t - σ.response K t
  have hW : ∀ t, HasDerivAt W (-σ.L (W t)) t := fun t => by
    refine ((hZ t).sub (σ.hasDerivAt_response K t)).congr_deriv ?_
    simp only [W, map_sub]
    abel
  set D : ℝ → H := fun t => σ.S (-t) (W t)
  have hD : ∀ t, HasDerivAt D 0 t := fun t => by
    refine (hasDerivAt_operator_apply (σ.hasDerivAt_S_neg t) (hW t)).congr_deriv ?_
    simp only [mul_apply_eq_comp, map_neg]
    rw [← σ.L_S_apply]
    abel
  have hconst := is_const_of_deriv_eq_zero (fun t => (hD t).differentiableAt)
    (fun t => (hD t).deriv)
  funext t
  have h := hconst t 0
  simp only [D, W, neg_zero, S_zero, one_apply_eq_self, hZ0, σ.response_zero,
    sub_zero] at h
  have := congrArg (σ.S t) h
  rw [σ.S_apply_S_neg, map_zero] at this
  exact sub_eq_zero.mp this

/-! ### `(SR.7)`: Duhamel generation -/

/-- The perturbed orbit `x_ε(t) = exp(-t(L + εK)) v`. -/
def perturbedOrbit (K : H →L[ℂ] H) (ε t : ℝ) : H := NormedSpace.exp (t • -(σ.L + ε • K)) σ.v

omit [FiniteDimensional ℂ H] in
theorem perturbedOrbit_zero (K : H →L[ℂ] H) (t : ℝ) : σ.perturbedOrbit K 0 t = σ.x t := by
  simp [perturbedOrbit, x, S]

omit [FiniteDimensional ℂ H] in
theorem hasDerivAt_perturbedOrbit_time (K : H →L[ℂ] H) (ε s : ℝ) :
    HasDerivAt (σ.perturbedOrbit K ε) (-(σ.L + ε • K) (σ.perturbedOrbit K ε s)) s := by
  have h := hasDerivAt_operator_apply (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-(σ.L + ε • K)) s)
    (hasDerivAt_const s σ.v)
  refine h.congr_deriv ?_
  simp [perturbedOrbit, mul_apply_eq_comp]

omit [FiniteDimensional ℂ H] in
theorem continuous_perturbedOrbit (K : H →L[ℂ] H) :
    Continuous fun p : ℝ × ℝ => σ.perturbedOrbit K p.1 p.2 := by
  unfold perturbedOrbit
  have hexp : Continuous fun p : ℝ × ℝ => NormedSpace.exp (p.2 • -(σ.L + p.1 • K)) :=
    NormedSpace.exp_continuous.comp (continuous_snd.smul (continuous_const.add
      (continuous_fst.smul continuous_const)).neg)
  exact hexp.clm_apply continuous_const

omit [FiniteDimensional ℂ H] in
/-- **The exact Duhamel identity** `x_ε(t) - x(t) = -ε ∫₀ᵗ S_{t-s} K x_ε(s) ds`. -/
theorem duhamel (K : H →L[ℂ] H) (ε t : ℝ) :
    σ.perturbedOrbit K ε t - σ.x t =
      -ε • ∫ s in (0 : ℝ)..t, σ.S (t - s) (K (σ.perturbedOrbit K ε s)) := by
  set φ : ℝ → H := fun s => σ.S (t - s) (σ.perturbedOrbit K ε s)
  have hφ : ∀ s, HasDerivAt φ (-ε • σ.S (t - s) (K (σ.perturbedOrbit K ε s))) s := fun s => by
    refine (hasDerivAt_operator_apply (σ.hasDerivAt_S_sub t s)
      (σ.hasDerivAt_perturbedOrbit_time K ε s)).congr_deriv ?_
    simp only [mul_apply_eq_comp]
    rw [σ.L_S_apply]
    simp only [add_apply, smul_apply, map_neg, map_add, ContinuousLinearMap.map_smul_of_tower]
    rw [neg_smul]
    abel
  have hcont : Continuous fun s => σ.S (t - s) (K (σ.perturbedOrbit K ε s)) :=
    (σ.continuous_S.comp (continuous_const.sub continuous_id)).clm_apply
      (K.continuous.comp ((σ.continuous_perturbedOrbit K).comp
        (continuous_const.prodMk continuous_id)))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hφ s)
    ((hcont.const_smul (-ε)).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_smul] at hftc
  rw [hftc]
  simp only [φ, sub_self, sub_zero, S_zero, one_apply_eq_self]
  rw [show σ.perturbedOrbit K ε 0 = σ.v by simp [perturbedOrbit]]
  rfl

omit [FiniteDimensional ℂ H] in
/-- **`(SR.7)`: the response is generated by the source.**  `∂_ε x_ε(t)|_{ε=0} = Y_K(t)`. -/
theorem hasDerivAt_perturbedOrbit (K : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (fun ε => σ.perturbedOrbit K ε t) (σ.response K t) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  set I : ℝ → H := fun ε => ∫ s in (0 : ℝ)..t, σ.S (t - s) (K (σ.perturbedOrbit K ε s))
  have hI : Continuous I := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun ε s => σ.S (t - s) (K (σ.perturbedOrbit K ε s))) ?_ 0 t
    exact (σ.continuous_S.comp (continuous_const.sub continuous_snd)).clm_apply
      (K.continuous.comp (σ.continuous_perturbedOrbit K))
  have hI0 : -I 0 = σ.response K t := by
    simp only [I, response, perturbedOrbit_zero]
  have hlim : Tendsto (fun ε => -I ε) (𝓝[≠] 0) (𝓝 (σ.response K t)) := by
    rw [← hI0]
    exact (hI.neg.tendsto 0).mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [slope_def_module, σ.perturbedOrbit_zero, sub_zero, σ.duhamel, smul_smul, mul_neg,
    inv_mul_cancel₀ (show ε ≠ 0 from hε), neg_one_smul]

/-! ### `(SR.9)`: the orbit spans and the response reconstructs -/

omit [FiniteDimensional ℂ H] in
theorem hasDerivAt_inner_Lpow_x (z : H) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun t => ⟪z, (σ.L ^ n) (σ.x t)⟫_ℂ) (-⟪z, (σ.L ^ (n + 1)) (σ.x t)⟫_ℂ) t := by
  have h1 : HasDerivAt (fun t => (σ.L ^ n) (σ.x t)) ((σ.L ^ n) (-σ.L (σ.x t))) t :=
    ((σ.L ^ n).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (σ.hasDerivAt_x t)
  have h2 := ((innerSL ℂ z).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
  refine h2.congr_deriv ?_
  simp [pow_succ, mul_apply_eq_comp]

/-- **`(SR.9)`: the orbit `{x(t) : 0 < t < T}` spans `H`.** -/
theorem span_orbit_Ioo {T : ℝ} (hT : 0 < T) : Submodule.span ℂ (σ.x '' Ioo 0 T) = ⊤ := by
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro z hz
  have horth : ∀ t ∈ Ioo 0 T, ⟪z, σ.x t⟫_ℂ = 0 := fun t ht => by
    have := (Submodule.mem_orthogonal _ _).mp hz _ (Submodule.subset_span ⟨t, ht, rfl⟩)
    rw [← inner_conj_symm, this, map_zero]
  have hall : ∀ n : ℕ, ∀ t ∈ Ioo 0 T, ⟪z, (σ.L ^ n) (σ.x t)⟫_ℂ = 0 := by
    intro n
    induction n with
    | zero => intro t ht; simpa using horth t ht
    | succ n ih =>
        intro t ht
        have hloc : (fun t => ⟪z, (σ.L ^ n) (σ.x t)⟫_ℂ) =ᶠ[𝓝 t] fun _ => 0 := by
          filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
          exact ih s hs
        have h0 : HasDerivAt (fun t => ⟪z, (σ.L ^ n) (σ.x t)⟫_ℂ) 0 t :=
          (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq hloc
        exact neg_eq_zero.mp ((σ.hasDerivAt_inner_Lpow_x z n t).unique h0)
  have hzero : ∀ n : ℕ, ⟪z, (σ.L ^ n) σ.v⟫_ℂ = 0 := by
    intro n
    have hcont : Continuous fun t => ⟪z, (σ.L ^ n) (σ.x t)⟫_ℂ :=
      continuous_const.inner ((σ.L ^ n).continuous.comp σ.continuous_x)
    have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have hev : (fun t => ⟪z, (σ.L ^ n) (σ.x t)⟫_ℂ) =ᶠ[𝓝[>] 0] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhdsGT hT] with t ht
      exact hall n t ht
    have := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)
    rwa [σ.x_zero] at this
  have hz' : z ∈ (Submodule.span ℂ (Set.range fun n : ℕ => (σ.L ^ n) σ.v))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨n, rfl⟩ := hu
        rw [← inner_conj_symm, hzero n, map_zero]
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  rwa [σ.cyclic, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at hz'

/-- The orbit on `[0, T]` spans `H` `(SR.9)`. -/
theorem span_orbit {T : ℝ} (hT : 0 < T) : Submodule.span ℂ (σ.x '' Icc 0 T) = ⊤ :=
  top_unique ((σ.span_orbit_Ioo hT).symm.le.trans
    (Submodule.span_mono (image_mono Ioo_subset_Icc_self)))

/-- **`(SR.9)`: finitely many orbit values form a basis.** -/
theorem exists_orbit_basis {T : ℝ} (hT : 0 < T) :
    ∃ (d : ℕ) (τ : Fin d → ℝ), (∀ i, τ i ∈ Icc 0 T) ∧ LinearIndependent ℂ (fun i => σ.x (τ i)) ∧
      Submodule.span ℂ (Set.range fun i => σ.x (τ i)) = ⊤ := by
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℂ (σ.x '' Icc 0 T)
  haveI : Finite b := hbli.finite
  set e : Fin (Nat.card b) ≃ b := (Finite.equivFin b).symm
  have hch : ∀ i, ∃ t, t ∈ Icc 0 T ∧ σ.x t = (e i : H) := fun i => hbsub (e i).2
  choose τ hτ hτx using hch
  have hfun : (fun i => σ.x (τ i)) = Subtype.val ∘ e := funext fun i => hτx i
  refine ⟨Nat.card b, τ, hτ, ?_, ?_⟩
  · rw [hfun]
    exact hbli.comp e e.injective
  · rw [hfun, Set.range_comp, e.range_eq_univ, Set.image_univ, Subtype.range_coe, hbspan,
      σ.span_orbit hT]

/-- **`(SR.9)`: reconstruction.**  `K x(t) = -Y_K'(t) - L Y_K(t)`. -/
theorem reconstruction (K : H →L[ℂ] H) (t : ℝ) :
    K (σ.x t) = -deriv (σ.response K) t - σ.L (σ.response K t) := by
  rw [(σ.hasDerivAt_response K t).deriv]
  abel

/-! ### The response operator and complete reconstruction -/

/-- The integrand `K ↦ S_{t-s} K x(s)` of the response, as an operator in `K`. -/
def responseKernel (t s : ℝ) : (H →L[ℂ] H) →L[ℂ] H :=
  (σ.S (t - s)).comp (ContinuousLinearMap.apply ℂ H (σ.x s))

omit [FiniteDimensional ℂ H] in
theorem continuous_responseKernel : Continuous fun p : ℝ × ℝ => σ.responseKernel p.1 p.2 :=
  (σ.continuous_S.comp (continuous_fst.sub continuous_snd)).clm_comp
    ((ContinuousLinearMap.apply ℂ H).continuous.comp (σ.continuous_x.comp continuous_snd))

/-- The response operator `K ↦ Y_K(t)` `(SR.5)`. -/
def responseCLM (t : ℝ) : (H →L[ℂ] H) →L[ℂ] H := -∫ s in (0 : ℝ)..t, σ.responseKernel t s

omit [FiniteDimensional ℂ H] in
theorem responseCLM_apply (t : ℝ) (K : H →L[ℂ] H) : σ.responseCLM t K = σ.response K t := by
  have hint : IntervalIntegrable (fun s => σ.responseKernel t s) volume 0 t :=
    (σ.continuous_responseKernel.comp (continuous_const.prodMk continuous_id)).intervalIntegrable
      _ _
  rw [responseCLM, neg_apply, ContinuousLinearMap.intervalIntegral_apply hint]
  rfl

omit [FiniteDimensional ℂ H] in
theorem continuous_responseCLM : Continuous σ.responseCLM := by
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (f := fun t s => σ.responseKernel t s) (a₀ := 0) σ.continuous_responseKernel
    continuous_id
  exact h.neg

omit [FiniteDimensional ℂ H] in
theorem response_add (K K' : H →L[ℂ] H) (t : ℝ) :
    σ.response (K + K') t = σ.response K t + σ.response K' t := by
  rw [← responseCLM_apply, ← responseCLM_apply, ← responseCLM_apply, map_add]

omit [FiniteDimensional ℂ H] in
theorem response_sub (K K' : H →L[ℂ] H) (t : ℝ) :
    σ.response (K - K') t = σ.response K t - σ.response K' t := by
  rw [← responseCLM_apply, ← responseCLM_apply, ← responseCLM_apply, map_sub]

omit [FiniteDimensional ℂ H] in
theorem response_smul (a : ℂ) (K : H →L[ℂ] H) (t : ℝ) :
    σ.response (a • K) t = a • σ.response K t := by
  rw [← responseCLM_apply, ← responseCLM_apply, map_smul]

/-- **`(SR.9)`: complete intervention reconstruction.**  An intervention whose response vanishes on
an interval `(0, T)` is zero. -/
theorem eq_zero_of_response_eq_zero {T : ℝ} (hT : 0 < T) {K : H →L[ℂ] H}
    (h : ∀ t ∈ Ioo 0 T, σ.response K t = 0) : K = 0 := by
  have hK : ∀ t ∈ Ioo 0 T, K (σ.x t) = 0 := by
    intro t ht
    have hloc : σ.response K =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact h s hs
    have h0 : HasDerivAt (σ.response K) 0 t :=
      (hasDerivAt_const t (0 : H)).congr_of_eventuallyEq hloc
    have := (σ.hasDerivAt_response K t).unique h0
    rw [h t ht, map_zero, neg_zero, zero_sub, neg_eq_zero] at this
    exact this
  have hspan : ∀ y ∈ Submodule.span ℂ (σ.x '' Ioo 0 T), K y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨t, ht, rfl⟩ := hy
        exact hK t ht
    | zero => exact map_zero K
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, ha, smul_zero]
  rw [σ.span_orbit_Ioo hT] at hspan
  exact ContinuousLinearMap.ext fun y => hspan y Submodule.mem_top

/-- The response map `K ↦ Y_K|_{(0,T)}` is injective `(SR.9)`. -/
theorem response_injective {T : ℝ} (hT : 0 < T) {K K' : H →L[ℂ] H}
    (h : ∀ t ∈ Ioo 0 T, σ.response K t = σ.response K' t) : K = K' :=
  sub_eq_zero.mp (σ.eq_zero_of_response_eq_zero hT fun t ht => by
    rw [response_sub, h t ht, sub_self])

/-! ### `(SR.10)`–`(SR.11)`: positive response work -/

/-- The response work `W_T(K) = ∫₀ᵀ ‖Y_K(t)‖²` `(SR.5)`. -/
def responseWork (T : ℝ) (K : H →L[ℂ] H) : ℝ := ∫ t in (0 : ℝ)..T, ‖σ.response K t‖ ^ 2

omit [FiniteDimensional ℂ H] in
theorem continuous_responseWork (T : ℝ) : Continuous (σ.responseWork T) := by
  have hjoint : Continuous fun p : (H →L[ℂ] H) × ℝ => ‖σ.response p.1 p.2‖ ^ 2 := by
    have : Continuous fun p : (H →L[ℂ] H) × ℝ => σ.responseCLM p.2 p.1 :=
      (σ.continuous_responseCLM.comp continuous_snd).clm_apply continuous_fst
    simp_rw [responseCLM_apply] at this
    exact this.norm.pow 2
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun K t => ‖σ.response K t‖ ^ 2) hjoint 0 T

omit [FiniteDimensional ℂ H] in
theorem responseWork_smul (T : ℝ) (a : ℂ) (K : H →L[ℂ] H) :
    σ.responseWork T (a • K) = ‖a‖ ^ 2 * σ.responseWork T K := by
  rw [responseWork, responseWork, ← intervalIntegral.integral_const_mul]
  congr 1
  funext t
  rw [response_smul, norm_smul, mul_pow]

omit [FiniteDimensional ℂ H] in
theorem responseWork_nonneg {T : ℝ} (hT : 0 ≤ T) (K : H →L[ℂ] H) : 0 ≤ σ.responseWork T K :=
  intervalIntegral.integral_nonneg hT fun _ _ => sq_nonneg _

/-- **The response work is positive definite.** -/
theorem responseWork_pos {T : ℝ} (hT : 0 < T) {K : H →L[ℂ] H} (hK : K ≠ 0) :
    0 < σ.responseWork T K := by
  refine lt_of_le_of_ne (σ.responseWork_nonneg hT.le K) fun h0 => hK ?_
  have hcont : Continuous fun t => ‖σ.response K t‖ ^ 2 := (σ.continuous_response K).norm.pow 2
  have hae := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun t => sq_nonneg ‖σ.response K t‖)
    (hcont.intervalIntegrable 0 T)).mp h0.symm
  have hae' : (fun t => ‖σ.response K t‖ ^ 2) =ᵐ[volume.restrict (Ioo 0 T)] 0 := by
    have hsub : Ioo 0 T ⊆ Ioc 0 T ∪ Ioc T 0 := fun t ht => Or.inl ⟨ht.1, ht.2.le⟩
    exact ae_restrict_of_ae_restrict_of_subset hsub hae
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hcont.continuousOn
    continuousOn_const
  refine σ.eq_zero_of_response_eq_zero hT fun t ht => ?_
  have := heq ht
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    norm_eq_zero] at this
  exact this

/-- **`(SR.10)`: coercivity of the response work** in operator norm. -/
theorem exists_responseWork_coercive {T : ℝ} (hT : 0 < T) :
    ∃ c > 0, ∀ K : H →L[ℂ] H, c * ‖K‖ ^ 2 ≤ σ.responseWork T K := by
  by_cases hne : (Metric.sphere (0 : H →L[ℂ] H) 1).Nonempty
  · obtain ⟨K₀, hK₀, hmin⟩ := (isCompact_sphere (0 : H →L[ℂ] H) 1).exists_isMinOn hne
      (σ.continuous_responseWork T).continuousOn
    have hK₀ne : K₀ ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hK₀
      exact norm_ne_zero_iff.mp (by rw [hK₀]; exact one_ne_zero)
    refine ⟨_, σ.responseWork_pos hT hK₀ne, fun K => ?_⟩
    by_cases hK : K = 0
    · simp [hK, responseWork_nonneg _ hT.le]
    have hnK : 0 < ‖K‖ := norm_pos_iff.mpr hK
    have hu : (‖K‖⁻¹ : ℂ) • K ∈ Metric.sphere (0 : H →L[ℂ] H) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ hnK.ne']
    have h := hmin hu
    simp only [mem_setOf_eq] at h
    rw [responseWork_smul, norm_inv, Complex.norm_real, norm_norm] at h
    have hK2 : 0 < ‖K‖ ^ 2 := by positivity
    calc σ.responseWork T K₀ * ‖K‖ ^ 2 ≤ ‖K‖⁻¹ ^ 2 * σ.responseWork T K * ‖K‖ ^ 2 := by gcongr
      _ = σ.responseWork T K := by field_simp
  · refine ⟨1, one_pos, fun K => ?_⟩
    have hK : K = 0 := by
      by_contra hK
      exact hne ⟨(‖K‖⁻¹ : ℂ) • K, by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, norm_norm,
          inv_mul_cancel₀ (norm_pos_iff.mpr hK).ne']⟩
    simp [hK, responseWork_nonneg _ hT.le]

/-- Every operator on a finite-dimensional space is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_of_finiteDimensional (K : H →L[ℂ] H) :
    ContinuousLinearMap.IsHilbertSchmidt K := by
  haveI : Finite (exists_hilbertBasis ℂ H).choose :=
    (ContinuousLinearMap.hsBasis ℂ H).orthonormal.linearIndependent.finite
  exact Summable.of_finite

/-- The Hilbert–Schmidt square norm is at most `dim · ‖K‖²` in finite dimension. -/
theorem hsNormSq_le (K : H →L[ℂ] H) :
    K.hsNormSq ≤ Module.finrank ℂ H * ‖K‖ ^ 2 := by
  set b := stdOrthonormalBasis ℂ H
  rw [ContinuousLinearMap.hsNormSq_eq (isHilbertSchmidt_of_finiteDimensional K) b.toHilbertBasis,
    tsum_fintype]
  calc ∑ i, ‖K (b.toHilbertBasis i)‖ ^ 2 ≤ ∑ _i : Fin (Module.finrank ℂ H), ‖K‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        calc ‖K (b.toHilbertBasis i)‖ ≤ ‖K‖ * ‖b.toHilbertBasis i‖ := K.le_opNorm _
          _ = ‖K‖ := by rw [OrthonormalBasis.coe_toHilbertBasis, b.orthonormal.1 i, mul_one]
    _ = Module.finrank ℂ H * ‖K‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **`(SR.10)`: source-generated positive work.**  `W_T(K) ≥ c_T ‖K‖²_HS`. -/
theorem exists_responseWork_coercive_hs {T : ℝ} (hT : 0 < T) :
    ∃ c > 0, ∀ K : H →L[ℂ] H, c * K.hsNormSq ≤ σ.responseWork T K := by
  obtain ⟨c, hc, hcoer⟩ := σ.exists_responseWork_coercive hT
  refine ⟨c / (Module.finrank ℂ H + 1), by positivity, fun K => ?_⟩
  have h1 := hsNormSq_le K
  have h2 : K.hsNormSq ≤ (Module.finrank ℂ H + 1) * ‖K‖ ^ 2 := by nlinarith [sq_nonneg ‖K‖]
  calc c / (Module.finrank ℂ H + 1) * K.hsNormSq ≤
      c / (Module.finrank ℂ H + 1) * ((Module.finrank ℂ H + 1) * ‖K‖ ^ 2) := by gcongr
    _ = c * ‖K‖ ^ 2 := by field_simp
    _ ≤ σ.responseWork T K := hcoer K

/-- **`(SR.11)`: vanishing response work forces vanishing interventions.** -/
theorem tendsto_zero_of_responseWork {T : ℝ} (hT : 0 < T) {K : ℕ → H →L[ℂ] H}
    (hK : Tendsto (fun n => σ.responseWork T (K n)) atTop (𝓝 0)) :
    Tendsto K atTop (𝓝 0) := by
  obtain ⟨c, hc, hcoer⟩ := σ.exists_responseWork_coercive hT
  have hsq : Tendsto (fun n => ‖K n‖ ^ 2) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n => σ.responseWork T (K n) / c) atTop (𝓝 0) := by
      simpa using hK.div_const c
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hdiv
    rw [le_div_iff₀ hc]
    linarith [hcoer (K n)]
  have hnorm : Tendsto (fun n => ‖K n‖) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- **Compact work sublevels.** -/
theorem isCompact_responseWork_le {T : ℝ} (hT : 0 < T) (M : ℝ) :
    IsCompact {K : H →L[ℂ] H | σ.responseWork T K ≤ M} := by
  obtain ⟨c, hc, hcoer⟩ := σ.exists_responseWork_coercive hT
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (σ.continuous_responseWork T) continuous_const) ?_
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨Real.sqrt (max M 0 / c), fun K hK => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hK' : c * ‖K‖ ^ 2 ≤ max M 0 := (hcoer K).trans (hK.trans (le_max_left _ _))
  have : ‖K‖ ^ 2 ≤ max M 0 / c := by rw [le_div_iff₀ hc]; linarith
  exact Real.le_sqrt_of_sq_le this

end CyclicSource

end GaloisForLFunctions.HTGeometry
