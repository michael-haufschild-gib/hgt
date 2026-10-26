import GaloisForLFunctions.ArithmeticPositiveDuality.TheIntegerSuccessorForcesTheHeckeWeight

/-!
# A continuous archimedean spectrum is seen by the successor

An atomic archimedean dilation part `Σ_k c_k u^{iγ_k}` admits only blind successors
(`successor_blind_of_atomic_archimedean`): `φ(x ↦ x + b)` is constant on `b ≠ 0`. This file shows
that the atoms are what makes the successor blind.

**Theorem** (`successor_sees_autocorrelation`). For every nonzero continuous compactly supported
`H : ℝ → ℂ` there is a positive-definite `φ` on `Aff(ℚ)` whose dilation part is the
autocorrelation of `H`,
`φ(x ↦ ux) = ∫ H(x + log u) H̄(x) dx` for `u > 0`,
and whose successor `b ↦ φ(x ↦ x + b)` is not constant on `b ≠ 0`.

The autocorrelation of `H` is the archimedean correlation with spectral density `|Ĥ|²`, so every
such absolutely continuous dilation spectrum carries successor information, while no atomic one
does. The state is a vector state of the real `ax + b` group restricted to `Aff(ℚ)`:
`φ(x ↦ ux + b) = ∫ e^{i b eˣ} H(x + log u) H̄(x) dx` for `u > 0` and `0` for `u < 0`, which is
`⟨π(u, b)h, h⟩` for `(π(u, b)h)(t) = u^{1/2} e^{ibt} h(ut)` on `L²(0, ∞)` and
`h(t) = t^{−1/2} H(log t)`, written in the coordinate `t = eˣ`. Its successor
`b ↦ ∫ e^{i b eˣ}|H(x)|² dx` tends to `‖H‖²` as `b → 0`; were it constant off `0`, the integrand
`(1 − cos(b eˣ))|H(x)|²` would vanish for all rational `b ≠ 0`, which fails where `H ≠ 0`.
-/

open Complex MeasureTheory Filter Topology
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The affine maps `x ↦ ux + b` of positive slope. -/
def posAffine : Subgroup AffineGroupQ where
  carrier := {g | 0 < affSlope g}
  one_mem' := by simp only [Set.mem_setOf_eq, affSlope_one, zero_lt_one]
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_setOf_eq, affSlope_mul] at *
    exact mul_pos hg hh
  inv_mem' {g} hg := by
    simp only [Set.mem_setOf_eq, affSlope_inv] at *
    exact inv_pos.mpr hg

variable {H : ℝ → ℂ}

/-- The vector `x ↦ e^{i b eˣ} H(x + log u)` of `x ↦ ux + b`, in the coordinate `t = eˣ`. -/
def realAffVec (H : ℝ → ℂ) (g : AffineGroupQ) (x : ℝ) : ℂ :=
  cexp (I * ((affShift g : ℝ) : ℂ) * (Real.exp x : ℂ)) * H (x + Real.log (affSlope g))

/-- The vector state of the real `ax + b` group, on maps of positive slope. -/
def realAffState (H : ℝ → ℂ) (g : AffineGroupQ) : ℂ :=
  ∫ x, cexp (I * ((affShift g : ℝ) : ℂ) * (Real.exp x : ℂ)) * H (x + Real.log (affSlope g)) *
    conj (H x)

/-- The coefficient identity `φ(g⁻¹h) = ⟨v_h, v_g⟩` on maps of positive slope: substitute
`x ↦ x + log u_g`. -/
theorem realAffState_inv_mul {g h : AffineGroupQ} (hg : 0 < affSlope g) (hh : 0 < affSlope h) :
    realAffState H (g⁻¹ * h) = ∫ x, conj (realAffVec H g x) * realAffVec H h x := by
  have hu : (0 : ℝ) < affSlope g := by exact_mod_cast hg
  have hv : (0 : ℝ) < affSlope h := by exact_mod_cast hh
  have hslope : ((affSlope (g⁻¹ * h) : ℚ) : ℝ) = (affSlope g : ℝ)⁻¹ * affSlope h := by
    rw [affSlope_mul, affSlope_inv]; push_cast; ring
  have hshift : ((affShift (g⁻¹ * h) : ℚ) : ℝ) = (affShift h - affShift g) / affSlope g := by
    rw [affShift_mul, affSlope_inv, affShift_inv]; push_cast; ring
  have hu' : ((affSlope g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  rw [realAffState]
  conv_lhs => rw [← integral_add_right_eq_self _ (Real.log (affSlope g))]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [realAffVec, hslope, hshift]
  rw [Real.log_mul (inv_pos.mpr hu).ne' hv.ne', Real.log_inv, Real.exp_add, Real.exp_log hu,
    show x + Real.log (affSlope g) + (-Real.log (affSlope g) + Real.log (affSlope h)) =
      x + Real.log (affSlope h) by ring]
  have hexp : cexp (I * (((affShift h - affShift g) / affSlope g : ℝ) : ℂ) *
      ((Real.exp x * affSlope g : ℝ) : ℂ)) =
      conj (cexp (I * ((affShift g : ℝ) : ℂ) * (Real.exp x : ℂ))) *
        cexp (I * ((affShift h : ℝ) : ℂ) * (Real.exp x : ℂ)) := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_div,
      Complex.ofReal_sub, Complex.ofReal_mul]
    field_simp
    ring
  rw [hexp, map_mul]
  ring

theorem continuous_realAffVec (hH : Continuous H) (g : AffineGroupQ) :
    Continuous (realAffVec H g) := by
  unfold realAffVec
  fun_prop

theorem hasCompactSupport_realAffVec (hHc : HasCompactSupport H) (g : AffineGroupQ) :
    HasCompactSupport (realAffVec H g) := by
  have : realAffVec H g = (fun x => cexp (I * ((affShift g : ℝ) : ℂ) * (Real.exp x : ℂ))) *
      (H ∘ Homeomorph.addRight (Real.log (affSlope g))) := by
    funext x; rfl
  rw [this]
  exact (hHc.comp_homeomorph _).mul_left

/-- The vector state is positive definite on maps of positive slope: its Gram form is
`∫ |Σ_b c_b v_b|²`. -/
theorem isPosDefOnGroup_realAffState (hH : Continuous H) (hHc : HasCompactSupport H) :
    IsPosDefOnGroup fun g : posAffine => realAffState H g := by
  intro N x c
  have hint : ∀ a b : Fin N, Integrable fun t =>
      star (c a) * (conj (realAffVec H (x a) t) * realAffVec H (x b) t) * c b := fun a b =>
    ((((Complex.continuous_conj.comp (continuous_realAffVec hH (x a))).mul
      (continuous_realAffVec hH (x b))).integrable_of_hasCompactSupport
      (hasCompactSupport_realAffVec hHc (x b)).mul_left).const_mul _).mul_const _
  set V : ℝ → ℂ := fun t => ∑ b, c b * realAffVec H (x b) t
  refine ⟨∫ t, ‖V t‖ ^ 2, integral_nonneg fun t => sq_nonneg _, ?_⟩
  calc ∑ a, ∑ b, star (c a) * realAffState H (((x a)⁻¹ * x b : posAffine) : AffineGroupQ) * c b
      = ∑ a, ∑ b, ∫ t, star (c a) * (conj (realAffVec H (x a) t) * realAffVec H (x b) t) * c b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [integral_mul_const, integral_const_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          realAffState_inv_mul (x a).2 (x b).2]
    _ = ∫ t, ∑ a, ∑ b, star (c a) * (conj (realAffVec H (x a) t) * realAffVec H (x b) t) * c b := by
        rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
        exact Finset.sum_congr rfl fun a _ => (integral_finsetSum _ fun b _ => hint a b).symm
    _ = ∫ t, ((‖V t‖ ^ 2 : ℝ) : ℂ) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        dsimp only
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
        simp only [V, map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul, Complex.star_def]
        ring
    _ = ((∫ t, ‖V t‖ ^ 2 : ℝ) : ℂ) := integral_ofReal

/-- The real `ax + b` state on `Aff(ℚ)`: the vector state on positive slopes, zero on negative
ones. -/
def realAffPosDef (H : ℝ → ℂ) : AffineGroupQ → ℂ :=
  extendFromSubgroup posAffine fun g => realAffState H g

theorem isPosDefOnGroup_realAffPosDef (hH : Continuous H) (hHc : HasCompactSupport H) :
    IsPosDefOnGroup (realAffPosDef H) :=
  isPosDefOnGroup_extendFromSubgroup (isPosDefOnGroup_realAffState hH hHc)

/-- Its dilation part is the autocorrelation of `H` in `log u`. -/
theorem realAffPosDef_dilation (u : ℚˣ) (hu : 0 < (u : ℚ)) :
    realAffPosDef H (dilation u) = ∫ x, H (x + Real.log (u : ℚ)) * conj (H x) := by
  have hmem : dilation u ∈ posAffine := by
    show 0 < affSlope (dilation u)
    rw [affSlope_dilation]; exact hu
  rw [realAffPosDef, extendFromSubgroup, dif_pos hmem]
  show realAffState H (dilation u) = _
  rw [realAffState]
  simp only [affShift_dilation, affSlope_dilation, Rat.cast_zero, Complex.ofReal_zero, mul_zero,
    zero_mul, Complex.exp_zero, one_mul]

/-- Its successor is `b ↦ ∫ e^{i b eˣ}|H(x)|² dx`. -/
theorem realAffPosDef_translation (b : ℚ) :
    realAffPosDef H (translation b) =
      ∫ x, cexp (I * ((b : ℝ) : ℂ) * (Real.exp x : ℂ)) * ((‖H x‖ ^ 2 : ℝ) : ℂ) := by
  have hmem : translation b ∈ posAffine := by
    show 0 < affSlope (translation b)
    rw [affSlope_translation]; exact one_pos
  rw [realAffPosDef, extendFromSubgroup, dif_pos hmem]
  show realAffState H (translation b) = _
  rw [realAffState]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [affShift_translation, affSlope_translation, Rat.cast_one, Real.log_one, add_zero]
  rw [show ∀ z w : ℂ, z * w * conj w = z * ((‖w‖ ^ 2 : ℝ) : ℂ) from fun z w => by
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]]

/-- **A continuous archimedean spectrum is seen by the successor.** The autocorrelation of a
nonzero `H ∈ C_c(ℝ)` is the dilation part of a positive-definite state on `Aff(ℚ)` whose successor
is not constant on `b ≠ 0`. -/
theorem successor_sees_autocorrelation (hH : Continuous H) (hHc : HasCompactSupport H)
    {x₀ : ℝ} (hx₀ : H x₀ ≠ 0) :
    ∃ φ : AffineGroupQ → ℂ, IsPosDefOnGroup φ ∧
      (∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∫ x, H (x + Real.log (u : ℚ)) * conj (H x)) ∧
      ¬ ∃ α : ℂ, ∀ b : ℚ, b ≠ 0 → φ (translation b) = α := by
  refine ⟨realAffPosDef H, isPosDefOnGroup_realAffPosDef hH hHc,
    fun u hu => realAffPosDef_dilation u hu, ?_⟩
  rintro ⟨α, hα⟩
  set w : ℝ → ℝ := fun x => ‖H x‖ ^ 2
  have hwc : Continuous w := hH.norm.pow 2
  have hws : HasCompactSupport w := hHc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  have hwi : Integrable w := hwc.integrable_of_hasCompactSupport hws
  have hw0 : ∀ x, 0 ≤ w x := fun x => sq_nonneg _
  set S : ℝ → ℂ := fun β => ∫ x, cexp (I * (β : ℂ) * (Real.exp x : ℂ)) * (w x : ℂ)
  have hSb : ∀ b : ℚ, b ≠ 0 → S b = α := fun b hb => by
    rw [← hα b hb, realAffPosDef_translation]
  have hbound : ∀ β : ℝ, ∀ x, ‖cexp (I * (β : ℂ) * (Real.exp x : ℂ)) * (w x : ℂ)‖ = w x := by
    intro β x
    rw [norm_mul, show I * (β : ℂ) * (Real.exp x : ℂ) = ((β * Real.exp x : ℝ) : ℂ) * I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (hw0 x)]
  have hSi : ∀ β : ℝ, Integrable fun x => cexp (I * (β : ℂ) * (Real.exp x : ℂ)) * (w x : ℂ) :=
    fun β => hwi.mono' (((by fun_prop : Continuous fun x : ℝ =>
      cexp (I * (β : ℂ) * (Real.exp x : ℂ))).mul (continuous_ofReal.comp hwc)).aestronglyMeasurable)
      (Eventually.of_forall fun x => (hbound β x).le)
  -- `S` is continuous at `0`, so `α = S 0 = ‖H‖²`.
  have hlim : Tendsto (fun n : ℕ => S ((1 : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 (S 0)) := by
    simp only [S]
    refine tendsto_integral_of_dominated_convergence w (fun n => (hSi _).aestronglyMeasurable) hwi
      (fun n => Eventually.of_forall fun x => (hbound _ x).le) (Eventually.of_forall fun x => ?_)
    have hc : Continuous fun β : ℝ => cexp (I * (β : ℂ) * (Real.exp x : ℂ)) * (w x : ℂ) := by
      fun_prop
    exact (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hα0 : S 0 = α := by
    refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun n => ?_)
    have hb : ((1 : ℚ) / ((n : ℚ) + 1)) ≠ 0 := by positivity
    rw [← hSb _ hb]
    exact congrArg S (by simp)
  -- Real parts: `∫ (1 − cos(b eˣ)) w = 0` for rational `b ≠ 0`.
  have hcos : ∀ b : ℚ, b ≠ 0 → Real.cos ((b : ℝ) * Real.exp x₀) = 1 := by
    intro b hb
    by_contra hne
    set f : ℝ → ℝ := fun x => (1 - Real.cos ((b : ℝ) * Real.exp x)) * w x
    have hcosc : Continuous fun x => Real.cos ((b : ℝ) * Real.exp x) :=
      Real.continuous_cos.comp (continuous_const.mul Real.continuous_exp)
    have hf : 0 < ∫ x, f x :=
      Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x₀)
        ((continuous_const.sub hcosc).mul hwc)
        (hws.mul_left (f := fun x => 1 - Real.cos ((b : ℝ) * Real.exp x)))
        (fun x => mul_nonneg (by linarith [Real.cos_le_one ((b : ℝ) * Real.exp x)]) (hw0 x))
        (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hne)) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx₀)))
    have hre : ∀ β : ℝ, (S β).re = ∫ x, Real.cos (β * Real.exp x) * w x := by
      intro β
      show (∫ x, cexp (I * (β : ℂ) * (Real.exp x : ℂ)) * (w x : ℂ)).re = _
      rw [← RCLike.re_eq_complex_re, ← integral_re (hSi β)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      rw [RCLike.re_eq_complex_re, show I * (β : ℂ) * (Real.exp x : ℂ) =
        ((β * Real.exp x : ℝ) : ℂ) * I by push_cast; ring, Complex.re_mul_ofReal,
        Complex.exp_ofReal_mul_I_re]
    have heq : (S b).re = (S 0).re := by rw [hSb b hb, hα0]
    rw [hre, hre] at heq
    simp only [zero_mul, Real.cos_zero, one_mul] at heq
    have hcosi : Integrable fun x => Real.cos ((b : ℝ) * Real.exp x) * w x :=
      hwi.mono' (hcosc.mul hwc).aestronglyMeasurable (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 x)]
        exact mul_le_of_le_one_left (hw0 x) (Real.abs_cos_le_one _))
    have h1 : ∫ x, f x = ∫ x, (w x - Real.cos ((b : ℝ) * Real.exp x) * w x) :=
      integral_congr_ae (Eventually.of_forall fun x => by simp only [f]; ring)
    rw [h1, integral_sub hwi hcosi, heq, sub_self] at hf
    exact lt_irrefl _ hf
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp (by simpa using hcos 1 one_ne_zero)
  have hk0 : (k : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hk
    exact (Real.exp_pos x₀).ne' hk.symm
  have h4 : ((1 : ℚ) / (4 * k)) ≠ 0 := by
    have : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
    exact div_ne_zero one_ne_zero (mul_ne_zero four_ne_zero this)
  have := hcos _ h4
  rw [show (((1 : ℚ) / (4 * k) : ℚ) : ℝ) * Real.exp x₀ = π / 2 by
    rw [← hk]; push_cast; field_simp; ring, Real.cos_pi_div_two] at this
  exact zero_ne_one this

end GaloisForLFunctions.ArithmeticPositiveDuality
