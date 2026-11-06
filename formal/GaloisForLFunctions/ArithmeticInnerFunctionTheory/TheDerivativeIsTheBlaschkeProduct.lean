import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheInnerFieldOfZeta
import GaloisForLFunctions.HTGeometry.EntireZeroFactorization
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheDerivativeReadsTheBlaschkeFactor

/-!
# The derivative at a zero is the Blaschke product of the other zeros

For a simple zero `ρ` of `ζ` with `b = Re ρ − ½ > 0` the normalised derivative is

`N(ρ) = 2b (|ρ − 1|/|ρ|) |ζ′(ρ)| exp(−∫ P_ρ log |ζ|)`.

**Theorem** (`hasSum_and_normalDerivative_eq`). `N(ρ) = exp(−Σ_{a ≠ ρ} m_a G(ρ, a)) = Π_{a ≠ ρ} ϱ(ρ, a)^{m_a}`,
the sum over all other zeros in `Re s > ½`, convergent, with multiplicity.

The inequality with a finite product is the finite form of this. The equality means that all negative moments of
`N` are exponential moments of the Green potential of the zero configuration: no further analytic input stands between
them. Also `N(ρ) ≤ 1`, with equality iff `ρ` is the only right zero (`normalDerivative_eq_one_iff`), and for a
non-real `ρ` the conjugate zero already forces `N(ρ) ≤ ϱ(ρ, ρ̄)` (`normalDerivative_le_hyperbolicRatio_conj`).

The general form (`IsFactored.hasSum_poissonJensen_at_zero`) holds at a zero of any multiplicity of any datum: dividing
`E(z) = (z − ρ)^m g(z)` by the Blaschke factor `((z − ρ)/(z + ρ̄ − 1))^m` leaves `g(z)(z + ρ̄ − 1)^m`, of the same
growth, with the same modulus on the line, nonzero at `ρ`, and bounded below on the ray, so that the Poisson–Jensen
identity applies at `ρ`.
-/

open Complex Metric Filter Topology MeasureTheory Set
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

/-- `E(z) ((z + ρ̄ − 1)/(z − ρ))^m`, written without the singularity at `ρ`. -/
def removedZero (g : ℂ → ℂ) (ρ : ℂ) (m : ℕ) (z : ℂ) : ℂ := g z * (z + conj ρ - 1) ^ m

/-- A factored datum: `E = (z − ρ)^m g`, `g(ρ) ≠ 0`, with `E` bounded below on the ray through `ρ`. -/
structure IsFactored (E g : ℂ → ℂ) (ρ : ℂ) (m : ℕ) : Prop where
  datum : IsHalfPlaneDatum E
  diff : Differentiable ℂ g
  fac : ∀ z, E z = (z - ρ) ^ m * g z
  re_gt : 1 / 2 < ρ.re
  ne0 : g ρ ≠ 0
  ray : ∃ c σ₁ : ℝ, 0 < c ∧ ∀ σ : ℝ, σ₁ ≤ σ → c ≤ ‖E ((σ : ℂ) + (ρ.im : ℂ) * I)‖

variable {E g : ℂ → ℂ} {ρ : ℂ} {m : ℕ}

theorem add_conj_sub_one (ρ : ℂ) : ρ + conj ρ - 1 = ((2 * (ρ.re - 1 / 2) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re, Complex.ofReal_re]
    ring
  · simp

theorem removed_ne_of_re {z : ℂ} (hρ : 1 / 2 < ρ.re) (hz : 1 / 2 < z.re) : z + conj ρ - 1 ≠ 0 :=
  ne_zero_of_half_lt_re hρ hz

theorem removed_centre :
    removedZero g ρ m ρ = g ρ * ((2 * (ρ.re - 1 / 2) : ℝ) : ℂ) ^ m := by
  rw [removedZero, add_conj_sub_one]

namespace IsFactored

variable (h : IsFactored E g ρ m)

include h

theorem diff_removed : Differentiable ℂ (removedZero g ρ m) := by
  unfold removedZero
  have := h.diff
  fun_prop

theorem isHalfPlaneDatum_removed : IsHalfPlaneDatum (removedZero g ρ m) := by
  refine ⟨h.diff_removed, ?_⟩
  obtain ⟨K, hK1, hK⟩ := h.datum.growth
  have hb : 0 ≤ 2 * (ρ.re - 1 / 2) := by have := h.re_gt; linarith
  obtain ⟨Ω, hΩ⟩ := (isCompact_closedBall ρ 1).exists_bound_of_continuousOn
    h.diff_removed.continuous.continuousOn
  set R : ℝ := (1 + 2 * (ρ.re - 1 / 2)) ^ m with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (by linarith)
  have hKR : 1 ≤ K * R := one_le_mul_of_one_le_of_one_le hK1 hR1
  refine ⟨|Ω| + K * R, by linarith [abs_nonneg Ω], fun z hz => ?_⟩
  have hs1 : (1 : ℝ) ≤ (‖z‖ + 2) ^ 2 := by nlinarith [norm_nonneg z]
  have hs0 : (0 : ℝ) ≤ (‖z‖ + 2) ^ 2 := by positivity
  have hC0 : 0 ≤ |Ω| + K * R := by linarith [abs_nonneg Ω]
  by_cases h1 : ‖z - ρ‖ ≤ 1
  · have hmem : z ∈ closedBall ρ 1 := by rwa [mem_closedBall, dist_eq_norm]
    calc ‖removedZero g ρ m z‖ ≤ |Ω| := (hΩ z hmem).trans (le_abs_self _)
      _ ≤ (|Ω| + K * R) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hs1 hC0
  · have h1' : 1 < ‖z - ρ‖ := not_le.mp h1
    have hq : ‖z + conj ρ - 1‖ ≤ (1 + 2 * (ρ.re - 1 / 2)) * ‖z - ρ‖ := by
      have e : z + conj ρ - 1 = (z - ρ) + ((2 * (ρ.re - 1 / 2) : ℝ) : ℂ) := by
        rw [← add_conj_sub_one]
        ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hb]
      nlinarith
    have hF : ‖removedZero g ρ m z‖ ≤ R * ‖E z‖ := by
      rw [removedZero, norm_mul, norm_pow, h.fac z, norm_mul, norm_pow, hR]
      calc ‖g z‖ * ‖z + conj ρ - 1‖ ^ m
          ≤ ‖g z‖ * ((1 + 2 * (ρ.re - 1 / 2)) * ‖z - ρ‖) ^ m := by gcongr
        _ = _ := by rw [mul_pow]; ring
    calc ‖removedZero g ρ m z‖ ≤ R * (K * (‖z‖ + 2) ^ 2) :=
          hF.trans (mul_le_mul_of_nonneg_left (hK z hz) (by positivity))
      _ = K * R * (‖z‖ + 2) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg Ω]) hs0

/-- On the line the removed function has the modulus of `E`. -/
theorem norm_removed_line (τ : ℝ) : ‖removedZero g ρ m (1 / 2 + τ * I)‖ = ‖E (1 / 2 + τ * I)‖ := by
  have e : (1 / 2 + τ * I : ℂ) + conj ρ - 1 = -conj ((1 / 2 + τ * I : ℂ) - ρ) := by
    apply Complex.ext
    · simp
      ring
    · simp
      ring
  rw [removedZero, norm_mul, norm_pow, e, norm_neg, Complex.norm_conj, h.fac, norm_mul, norm_pow,
    mul_comm]

theorem isCentre_removed : IsCentre (removedZero g ρ m) ρ := by
  have hρ := h.re_gt
  have hb : (2 * (ρ.re - 1 / 2) : ℝ) ≠ 0 := by linarith
  refine ⟨hρ, ?_, ?_⟩
  · rw [removed_centre]
    exact mul_ne_zero h.ne0 (pow_ne_zero m (by exact_mod_cast hb))
  · obtain ⟨c, σ₁, hc, hray⟩ := h.ray
    refine ⟨c, max σ₁ (ρ.re + 1), hc, fun σ hσ => ?_⟩
    have hσ1 := (le_max_left _ _).trans hσ
    have hσ2 := (le_max_right _ _).trans hσ
    set s : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I with hs
    have hre : s.re = σ := by simp [hs]
    have hsh : 1 / 2 < s.re := by rw [hre]; linarith
    have hle : ‖s - ρ‖ ≤ ‖s + conj ρ - 1‖ := (norm_sub_lt_norm_add_conj hρ hsh).le
    have hE : ‖E s‖ ≤ ‖removedZero g ρ m s‖ := by
      rw [removedZero, norm_mul, norm_pow, h.fac s, norm_mul, norm_pow, mul_comm]
      gcongr
    exact (hray σ hσ1).trans hE

theorem removed_eq_zero_iff {a : ℂ} (ha : 1 / 2 < a.re) (hne : a ≠ ρ) :
    removedZero g ρ m a = 0 ↔ E a = 0 := by
  have h1 := pow_ne_zero m (removed_ne_of_re (ρ := ρ) h.re_gt ha)
  have h2 := pow_ne_zero m (sub_ne_zero.mpr hne)
  rw [removedZero, h.fac a, mul_eq_zero, mul_eq_zero]
  simp [h1, h2]

theorem order_removed {a : ℂ} (ha : 1 / 2 < a.re) (hne : a ≠ ρ) :
    analyticOrderAt (removedZero g ρ m) a = analyticOrderAt E a := by
  have hga : AnalyticAt ℂ g a := h.diff.analyticAt a
  have hq : AnalyticAt ℂ (fun z => (z + conj ρ - 1) ^ m) a := by fun_prop
  have hp : AnalyticAt ℂ (fun z => (z - ρ) ^ m) a := by fun_prop
  have h1 : analyticOrderAt (fun z => (z + conj ρ - 1) ^ m) a = 0 :=
    hq.analyticOrderAt_eq_zero.mpr (pow_ne_zero m (removed_ne_of_re (ρ := ρ) h.re_gt ha))
  have h2 : analyticOrderAt (fun z => (z - ρ) ^ m) a = 0 :=
    hp.analyticOrderAt_eq_zero.mpr (pow_ne_zero m (sub_ne_zero.mpr hne))
  have e1 : removedZero g ρ m = g * fun z => (z + conj ρ - 1) ^ m := rfl
  have e2 : E = (fun z => (z - ρ) ^ m) * g := by
    funext z
    exact h.fac z
  rw [e1, analyticOrderAt_mul hga hq, h1, add_zero]
  conv_rhs => rw [e2]
  rw [analyticOrderAt_mul hp hga, h2, zero_add]

/-- **The Poisson–Jensen identity at a zero.** The Green potential at `ρ` of the other zeros is
`∫ log |E| P_ρ − log ((2b)^m |g(ρ)|)`. -/
theorem hasSum_poissonJensen_at_zero :
    HasSum (fun a : {a : RightZeros E // (a : ℂ) ≠ ρ} =>
        (analyticOrderNatAt E (a : RightZeros E) : ℝ) * greenKernel ρ (a : RightZeros E))
      ((∫ τ : ℝ, Real.log ‖E (1 / 2 + τ * I)‖ * halfPlanePoissonKernel ρ τ) -
        Real.log (‖g ρ‖ * (2 * (ρ.re - 1 / 2)) ^ m)) := by
  have hρ := h.re_gt
  obtain ⟨-, hsum⟩ := hasSum_poissonJensen h.isHalfPlaneDatum_removed h.isCentre_removed
  have hval : (∫ τ : ℝ, Real.log ‖removedZero g ρ m (1 / 2 + τ * I)‖ * halfPlanePoissonKernel ρ τ) -
      Real.log ‖removedZero g ρ m ρ‖ =
      (∫ τ : ℝ, Real.log ‖E (1 / 2 + τ * I)‖ * halfPlanePoissonKernel ρ τ) -
        Real.log (‖g ρ‖ * (2 * (ρ.re - 1 / 2)) ^ m) := by
    simp only [h.norm_removed_line]
    rw [removed_centre, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [hval] at hsum
  have hne0 : removedZero g ρ m ρ ≠ 0 := h.isCentre_removed.ne0
  let e : RightZeros (removedZero g ρ m) ≃ {a : RightZeros E // (a : ℂ) ≠ ρ} :=
    { toFun := fun a =>
        have hne : (a : ℂ) ≠ ρ := fun he => hne0 (by have h0 := a.2.1; rwa [he] at h0)
        ⟨⟨a, (h.removed_eq_zero_iff a.2.2 hne).mp a.2.1, a.2.2⟩, hne⟩
      invFun := fun a => ⟨a, (h.removed_eq_zero_iff (a : RightZeros E).2.2 a.2).mpr
        (a : RightZeros E).2.1, (a : RightZeros E).2.2⟩
      left_inv := fun a => rfl
      right_inv := fun a => rfl }
  have ht := e.symm.hasSum_iff.mpr hsum
  have hf : ((fun a : RightZeros (removedZero g ρ m) =>
      (analyticOrderNatAt (removedZero g ρ m) a : ℝ) * greenKernel ρ a) ∘ e.symm) =
      fun a : {a : RightZeros E // (a : ℂ) ≠ ρ} =>
        (analyticOrderNatAt E (a : RightZeros E) : ℝ) * greenKernel ρ (a : RightZeros E) := by
    funext a
    change (analyticOrderNatAt (removedZero g ρ m) (a : RightZeros E) : ℝ) *
      greenKernel ρ (a : RightZeros E) = _
    have ho := h.order_removed (a : RightZeros E).2.2 a.2
    simp only [analyticOrderNatAt, ho]
  rw [hf] at ht
  exact ht

end IsFactored

/-! ### The zeta function -/

/-- The factorization of `(s − 1)ζ(s)` at a right zero. -/
theorem exists_isFactored_zetaEntire (ρ : ZetaRightZero) :
    ∃ g : ℂ → ℂ, IsFactored zetaEntire g ρ (analyticOrderNatAt riemannZeta ρ) := by
  have hρ1 := ρ.ne_one
  have hne : analyticOrderAt zetaEntire ρ ≠ ⊤ := by
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
      (fun z _ => differentiable_zetaEntire.analyticAt z) isPreconnected_univ (mem_univ (1 : ℂ))
      (mem_univ _) ?_
    rw [(differentiable_zetaEntire.analyticAt 1).analyticOrderAt_eq_zero.mpr zetaEntire_one_ne_zero]
    exact ENat.zero_ne_top
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hne
  have hdn : analyticOrderNatAt riemannZeta ρ = d := by
    rw [← analyticOrderNatAt_zetaEntire hρ1, analyticOrderNatAt, ← hd]
    rfl
  obtain ⟨g, hg, hg0, hfac⟩ := GaloisForLFunctions.HTGeometry.exists_entire_factor_of_analyticOrder
    differentiable_zetaEntire (c := (ρ : ℂ)) (d := d) hd.symm
  rw [hdn]
  obtain ⟨c, σ₁, hc, hray⟩ := (isCentre_zetaEntire (w := 1) (by norm_num) zetaEntire_one_ne_zero).ray
  refine ⟨g, isHalfPlaneDatum_zetaEntire, hg, hfac, ρ.2.2, hg0, 1 / 4, 2, by norm_num, fun σ hσ => ?_⟩
  set s : ℂ := (σ : ℂ) + ((ρ : ℂ).im : ℂ) * I with hs
  have hre : s.re = σ := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  rw [zetaEntire_eq hs1, norm_mul]
  have h1 : 1 ≤ ‖s - 1‖ := by
    have h := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, Complex.one_re, hre, abs_of_nonneg (by linarith)] at h
    linarith
  have h2 := norm_riemannZeta_ge_of_two_le_re (s := s) (by rw [hre]; exact hσ)
  nlinarith [norm_nonneg (riemannZeta s)]

/-- The other right zeros of `ζ`. -/
abbrev OtherZero (ρ : ZetaRightZero) := {a : ZetaRightZero // (a : ℂ) ≠ ρ}

/-- The Green potential at `ρ` of the other right zeros, with value in the leading coefficient. -/
theorem hasSum_green_at_zero {ρ : ZetaRightZero} {g : ℂ → ℂ}
    (h : IsFactored zetaEntire g ρ (analyticOrderNatAt riemannZeta ρ)) :
    HasSum (fun a : OtherZero ρ => zeroMult a * greenKernel ρ a)
      ((∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel ρ τ) +
        Real.log ‖(ρ : ℂ)‖ - Real.log (‖g ρ‖ * (2 * ((ρ : ℂ).re - 1 / 2)) ^
          (analyticOrderNatAt riemannZeta ρ))) := by
  have hs := h.hasSum_poissonJensen_at_zero
  rw [(integral_log_zetaEntire_poisson ρ.2.2).2] at hs
  let e : {a : RightZeros zetaEntire // (a : ℂ) ≠ ρ} ≃ OtherZero ρ :=
    { toFun := fun a => ⟨rightZerosEquiv a, a.2⟩
      invFun := fun a => ⟨rightZerosEquiv.symm a, a.2⟩
      left_inv := fun a => rfl
      right_inv := fun a => rfl }
  have ht := e.symm.hasSum_iff.mpr hs
  have hf : ((fun a : {a : RightZeros zetaEntire // (a : ℂ) ≠ ρ} =>
      (analyticOrderNatAt zetaEntire (a : RightZeros zetaEntire) : ℝ) *
        greenKernel ρ (a : RightZeros zetaEntire)) ∘ e.symm) =
      fun a : OtherZero ρ => zeroMult a * greenKernel ρ a := by
    funext a
    change (analyticOrderNatAt zetaEntire (a : ZetaRightZero) : ℝ) * greenKernel ρ (a : ZetaRightZero) = _
    rw [analyticOrderNatAt_zetaEntire (a : ZetaRightZero).ne_one, zeroMult]
  rw [hf] at ht
  exact ht

theorem deriv_zetaEntire_of_zero {ρ : ℂ} (hρ : ρ ≠ 1) (h0 : riemannZeta ρ = 0) :
    deriv zetaEntire ρ = (ρ - 1) * deriv riemannZeta ρ := by
  have hev : zetaEntire =ᶠ[𝓝 ρ] fun s => (s - 1) * riemannZeta s := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hρ] with s hs
    exact zetaEntire_eq hs
  have hd : HasDerivAt (fun s => (s - 1) * riemannZeta s)
      (1 * riemannZeta ρ + (ρ - 1) * deriv riemannZeta ρ) ρ :=
    ((hasDerivAt_id' ρ).sub_const 1).fun_mul (differentiableAt_riemannZeta hρ).hasDerivAt
  rw [hev.deriv_eq, hd.deriv, h0]
  simp

/-- **The derivative law.** At a simple right zero `ρ`, `N(ρ)` is the Blaschke product of all the
other right zeros, with multiplicity: the potential converges and `N(ρ) = exp (−potential)`. -/
theorem hasSum_and_normalDerivative_eq {ρ : ZetaRightZero}
    (hs : analyticOrderNatAt riemannZeta ρ = 1) :
    Summable (fun a : OtherZero ρ => zeroMult a * greenKernel ρ a) ∧
      MultiscaleMollifiedZetaField.normalDerivative ρ =
        Real.exp (-∑' a : OtherZero ρ, zeroMult a * greenKernel ρ a) := by
  obtain ⟨g, hg⟩ := exists_isFactored_zetaEntire ρ
  rw [hs] at hg
  have hsum := hasSum_green_at_zero (ρ := ρ) (g := g) (by rw [hs]; exact hg)
  rw [hs, pow_one] at hsum
  refine ⟨hsum.summable, ?_⟩
  rw [hsum.tsum_eq]
  have hρ1 := ρ.ne_one
  have hρ0 : (ρ : ℂ) ≠ 0 := by
    intro h
    have := ρ.2.2
    rw [h] at this
    simp at this
    linarith
  have hgρ : g ρ = deriv zetaEntire ρ := by
    have hd : HasDerivAt zetaEntire (g ρ) ρ := by
      have hg1 : HasDerivAt (fun z => (z - (ρ : ℂ)) * g z) (1 * g ρ + ((ρ : ℂ) - ρ) * deriv g ρ) ρ :=
        ((hasDerivAt_id (ρ : ℂ)).sub_const _).mul (hg.diff.differentiableAt.hasDerivAt)
      have e : (fun z => (z - (ρ : ℂ)) * g z) = zetaEntire := by
        funext z
        rw [hg.fac z, pow_one]
      rw [e] at hg1
      simpa using hg1
    exact hd.deriv.symm
  have hderiv : g ρ = ((ρ : ℂ) - 1) * deriv riemannZeta ρ := by
    rw [hgρ, deriv_zetaEntire_of_zero hρ1 ρ.2.1]
  have hg0 : g ρ ≠ 0 := hg.ne0
  have hb : 0 < 2 * ((ρ : ℂ).re - 1 / 2) := by have := ρ.2.2; linarith
  have hgn : ‖g ρ‖ = ‖(ρ : ℂ) - 1‖ * ‖deriv riemannZeta ρ‖ := by rw [hderiv, norm_mul]
  have hgpos : 0 < ‖g ρ‖ := norm_pos_iff.mpr hg0
  have hn0 : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.mpr hρ0
  have hpoisson : (∫ u : ℝ, MultiscaleMollifiedZetaField.zeroPoisson ρ u *
      Real.log ‖riemannZeta (MultiscaleMollifiedZetaField.linePoint u)‖) =
      ∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel ρ τ := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [MultiscaleMollifiedZetaField.zeroPoisson, GaloisForLFunctions.HTGeometry.halfPlanePoisson,
      halfPlanePoissonKernel, MultiscaleMollifiedZetaField.linePoint]
    ring
  rw [MultiscaleMollifiedZetaField.normalDerivative, hpoisson]
  set J : ℝ := ∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel ρ τ
  have e : -(J + Real.log ‖(ρ : ℂ)‖ - Real.log (‖g ρ‖ * (2 * ((ρ : ℂ).re - 1 / 2)))) =
      Real.log (‖g ρ‖ * (2 * ((ρ : ℂ).re - 1 / 2)) / ‖(ρ : ℂ)‖) - J := by
    rw [Real.log_div (by positivity) hn0.ne']
    ring
  rw [e, Real.exp_sub, Real.exp_log (by positivity), hgn, Real.exp_neg]
  field_simp

/-- The Green kernel is minus the logarithm of the pseudo-hyperbolic ratio. -/
theorem greenKernel_eq_neg_log_hyperbolicRatio {ρ a : ℂ} (hρa : ρ ≠ a) (hρ : 1 / 2 < ρ.re)
    (ha : 1 / 2 < a.re) :
    greenKernel ρ a = -Real.log (MultiscaleMollifiedZetaField.hyperbolicRatio ρ a) := by
  have h1 : ‖a + conj ρ - 1‖ = ‖ρ + conj a - 1‖ := by
    have e : a + conj ρ - 1 = conj (ρ + conj a - 1) := by
      simp only [map_sub, map_add, Complex.conj_conj, map_one]
      ring
    rw [e, Complex.norm_conj]
  have h2 : ‖a - ρ‖ = ‖ρ - a‖ := norm_sub_rev _ _
  have hn1 : 0 < ‖ρ - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hρa)
  have hn2 : 0 < ‖ρ + conj a - 1‖ := norm_pos_iff.mpr (ne_zero_of_half_lt_re ha hρ)
  rw [greenKernel, h1, h2, MultiscaleMollifiedZetaField.hyperbolicRatio,
    Real.log_div hn2.ne' hn1.ne', Real.log_div hn1.ne' hn2.ne']
  ring

/-- `N(ρ) ≤ 1` at a simple right zero. -/
theorem normalDerivative_le_one {ρ : ZetaRightZero} (hs : analyticOrderNatAt riemannZeta ρ = 1) :
    MultiscaleMollifiedZetaField.normalDerivative ρ ≤ 1 := by
  obtain ⟨hsum, he⟩ := hasSum_and_normalDerivative_eq hs
  rw [he]
  refine Real.exp_le_one_iff.mpr (neg_nonpos.mpr (tsum_nonneg fun a => ?_))
  exact mul_nonneg (zeroMult_pos a).le (greenKernel_pos ρ.2.2 (a : ZetaRightZero).2.2 a.2).le

/-- `N(ρ) = 1` iff `ρ` is the only right zero. -/
theorem normalDerivative_eq_one_iff {ρ : ZetaRightZero} (hs : analyticOrderNatAt riemannZeta ρ = 1) :
    MultiscaleMollifiedZetaField.normalDerivative ρ = 1 ↔ IsEmpty (OtherZero ρ) := by
  obtain ⟨hsum, he⟩ := hasSum_and_normalDerivative_eq hs
  have hnn : ∀ a : OtherZero ρ, 0 ≤ zeroMult a * greenKernel ρ a := fun a =>
    mul_nonneg (zeroMult_pos a).le (greenKernel_pos ρ.2.2 (a : ZetaRightZero).2.2 a.2).le
  rw [he, Real.exp_eq_one_iff, neg_eq_zero]
  constructor
  · intro h0
    refine ⟨fun a => ?_⟩
    have hpos : 0 < zeroMult a * greenKernel ρ a :=
      mul_pos (zeroMult_pos a) (greenKernel_pos ρ.2.2 (a : ZetaRightZero).2.2 a.2)
    have hle := hsum.le_tsum a fun b _ => hnn b
    rw [h0] at hle
    exact absurd hle (not_le.mpr hpos)
  · intro hemp
    exact tsum_empty

/-- A non-real zero sees its conjugate: `N(ρ) ≤ ϱ(ρ, ρ̄)`. -/
theorem normalDerivative_le_hyperbolicRatio_conj {ρ : ZetaRightZero}
    (hs : analyticOrderNatAt riemannZeta ρ = 1) (him : (ρ : ℂ).im ≠ 0) :
    MultiscaleMollifiedZetaField.normalDerivative ρ ≤
      MultiscaleMollifiedZetaField.hyperbolicRatio ρ (conj (ρ : ℂ)) := by
  obtain ⟨hsum, he⟩ := hasSum_and_normalDerivative_eq hs
  have hconj : conj (ρ : ℂ) ≠ ρ := by
    intro h
    apply him
    have := congrArg Complex.im h
    simp at this
    linarith
  have hzero : riemannZeta (conj (ρ : ℂ)) = 0 := by
    rw [riemannZeta_conj, ρ.2.1, map_zero]
  let c : OtherZero ρ := ⟨⟨conj (ρ : ℂ), hzero, by simpa using ρ.2.2⟩, hconj⟩
  have hnn : ∀ a : OtherZero ρ, 0 ≤ zeroMult a * greenKernel ρ a := fun a =>
    mul_nonneg (zeroMult_pos a).le (greenKernel_pos ρ.2.2 (a : ZetaRightZero).2.2 a.2).le
  have hle := hsum.le_tsum c fun a _ => hnn a
  have hm : 1 ≤ zeroMult (c : ZetaRightZero) := by
    have hp := zeroMult_pos (c : ZetaRightZero)
    rw [zeroMult] at hp ⊢
    exact_mod_cast (Nat.cast_pos.mp hp : 0 < _)
  have hG : 0 < greenKernel ρ (c : ZetaRightZero) :=
    greenKernel_pos ρ.2.2 (c : ZetaRightZero).2.2 c.2
  have hc1 : greenKernel ρ (conj (ρ : ℂ)) ≤ ∑' a : OtherZero ρ, zeroMult a * greenKernel ρ a := by
    refine le_trans ?_ hle
    change greenKernel ρ (c : ZetaRightZero) ≤ zeroMult (c : ZetaRightZero) * greenKernel ρ (c : ZetaRightZero)
    nlinarith
  rw [he]
  have hne : (ρ : ℂ) ≠ conj (ρ : ℂ) := fun h => hconj h.symm
  have hG' := greenKernel_eq_neg_log_hyperbolicRatio hne ρ.2.2 (by simpa using ρ.2.2)
  have hrat : 0 < MultiscaleMollifiedZetaField.hyperbolicRatio ρ (conj (ρ : ℂ)) := by
    rw [MultiscaleMollifiedZetaField.hyperbolicRatio]
    exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
      (norm_pos_iff.mpr (ne_zero_of_half_lt_re (by simpa using ρ.2.2) ρ.2.2))
  rw [← Real.exp_log hrat]
  refine Real.exp_le_exp.mpr ?_
  linarith

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
