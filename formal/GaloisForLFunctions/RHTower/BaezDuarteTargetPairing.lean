import GaloisForLFunctions.RHTower.BaezDuarteGram
import GaloisForLFunctions.RHTower.NymanBeurlingCriterion

/-!
# The Báez-Duarte pairing with the target, in closed form

The least-squares problem behind the Nyman--Beurling criterion has two data: the Gram matrix of the
generators (`BaezDuarteGram`) and the vector of their pairings with the target.  This file evaluates the
second **exactly and unconditionally**:

`⟪bdGen θ, bdTarget⟫ = −θ log θ`,  and  `‖bdTarget‖ = 1`.

The evaluation is elementary — no zeta function and, notably, no Euler--Mascheroni constant.  Writing
`g(v) = {v}·v^{-2}`, the dilation identity `∫_{u>1} g(θu) du = θ^{-1}∫_{v>θ} g` turns the pairing into

`θ·(∫_{v>θ} g − ∫_{v>1} g) = θ·∫_θ^1 {v}v^{-2} dv = θ·∫_θ^1 v^{-1} dv = −θ log θ`,

and the divergent-looking constant `∫_1^∞ {v}v^{-2}dv = 1 − γ` cancels between the two terms before it is
ever needed.  That cancellation is the whole point of Báez-Duarte's normalisation `{θ/t} − θ{1/t}`.

Two immediate consequences: the target is a unit vector, so the Báez-Duarte distances live in `[0,1]`; and
Cauchy--Schwarz gives the unconditional lower bound `θ|log θ| ≤ ‖bdGen θ‖` on the Gram diagonal.
-/

open MeasureTheory Set Complex
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-! ## The target is a unit vector -/

theorem bdTargetFun_eq_ofReal (u : ℝ) : bdTargetFun u = ((u⁻¹ : ℝ) : ℂ) := by
  rw [bdTargetFun, ← Complex.ofReal_inv]

theorem inner_bdTarget_self : inner ℂ bdTarget bdTarget = ((1 : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  have hcongr : ∀ᵐ u ∂bdMeasure,
      inner ℂ ((bdTarget : ℝ → ℂ) u) ((bdTarget : ℝ → ℂ) u) = ((u ^ (-2 : ℝ) : ℝ) : ℂ) := by
    filter_upwards [memLp_bdTargetFun.coeFn_toLp, ae_restrict_mem measurableSet_Ioi] with u hu hu1
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu1)
    rw [bdTarget, hu, bdTargetFun_eq_ofReal, RCLike.inner_apply, Complex.conj_ofReal,
      ← Complex.ofReal_mul]
    congr 1
    rw [← inv_sq_eq_rpow hu0, sq]
  rw [integral_congr_ae hcongr, integral_complex_ofReal,
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos]
  norm_num

/-- **The Nyman--Beurling target is a unit vector**, so every Báez-Duarte distance lies in `[0,1]`. -/
theorem norm_bdTarget : ‖bdTarget‖ = 1 := by
  have h : (RCLike.re (inner ℂ bdTarget bdTarget) : ℝ) = ‖bdTarget‖ ^ 2 :=
    inner_self_eq_norm_sq _
  rw [inner_bdTarget_self] at h
  have h1 : ‖bdTarget‖ ^ 2 = 1 := by
    rw [← h]
    show ((1 : ℝ) : ℂ).re = 1
    exact Complex.ofReal_re _
  nlinarith [norm_nonneg bdTarget, h1]

/-! ## The pairing kernel and its dilation -/

/-- `g(v) = {v}·v^{-2}`: the kernel whose dilation identity carries the pairing. -/
def fractInvSq (v : ℝ) : ℝ := Int.fract v * (v⁻¹) ^ 2

theorem measurable_fractInvSq : Measurable fractInvSq :=
  measurable_fract.mul ((measurable_id.inv).pow_const 2)

theorem norm_fractInvSq_le {v : ℝ} (hv : 0 < v) : ‖fractInvSq v‖ ≤ (v⁻¹) ^ 2 := by
  rw [fractInvSq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Int.fract_nonneg v),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (v⁻¹) ^ 2)]
  calc Int.fract v * (v⁻¹) ^ 2 ≤ 1 * (v⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right (Int.fract_lt_one v).le (by positivity)
    _ = (v⁻¹) ^ 2 := one_mul _

/-- The kernel is integrable on every ray `v > c` with `c > 0`. -/
theorem integrableOn_fractInvSq_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn fractInvSq (Ioi c) := by
  refine Integrable.mono' (g := fun v => v ^ (-2 : ℝ))
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hc)
    measurable_fractInvSq.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : (0 : ℝ) < v := lt_trans hc (mem_Ioi.mp hv) |>.trans_le le_rfl
  rw [← inv_sq_eq_rpow hv0]
  exact norm_fractInvSq_le hv0

/-- **The dilation identity.**  Scaling the argument of the kernel rescales its ray integral. -/
theorem integral_Ioi_one_fractInvSq_dilate {θ : ℝ} (hθ0 : 0 < θ) :
    (∫ u in Ioi (1 : ℝ), Int.fract (θ * u) * (u⁻¹) ^ 2)
      = θ * ∫ v in Ioi θ, fractInvSq v := by
  have hkey := integral_comp_mul_left_Ioi fractInvSq 1 hθ0
  rw [mul_one] at hkey
  have hpt : (∫ u in Ioi (1 : ℝ), fractInvSq (θ * u))
      = θ⁻¹ * ∫ v in Ioi θ, fractInvSq v := by
    rw [hkey, smul_eq_mul]
  have hcongr : ∀ u ∈ Ioi (1 : ℝ),
      Int.fract (θ * u) * (u⁻¹) ^ 2 = θ ^ 2 * fractInvSq (θ * u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
    have hθne : θ ≠ 0 := ne_of_gt hθ0
    have hune : u ≠ 0 := ne_of_gt hu0
    rw [fractInvSq]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul, hpt]
  field_simp

/-- The head of the ray integral, where the fractional part is the identity. -/
theorem integral_Ioc_fractInvSq {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (∫ v in Ioc θ 1, fractInvSq v) = -Real.log θ := by
  have hcongr : ∀ v ∈ Ioo θ 1, fractInvSq v = v⁻¹ := by
    intro v hv
    have hv0 : (0 : ℝ) < v := lt_trans hθ0 hv.1
    have hfr : Int.fract v = v := Int.fract_eq_self.mpr ⟨hv0.le, hv.2⟩
    rw [fractInvSq, hfr, sq]
    field_simp
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hcongr, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hθ1, integral_inv_of_pos hθ0 one_pos]
  rw [one_div, Real.log_inv]

/-! ## The pairing -/

/-- **The Báez-Duarte pairing with the target.**  Elementary, exact, and free of the Euler constant:
the tail `∫_1^∞ {v}v^{-2}dv` cancels between the two terms. -/
theorem integral_bdGenReal_mul_inv {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (∫ u in Ioi (1 : ℝ), bdGenReal θ u * u⁻¹) = -(θ * Real.log θ) := by
  have hsplit : ∀ u ∈ Ioi (1 : ℝ), bdGenReal θ u * u⁻¹
      = Int.fract (θ * u) * (u⁻¹) ^ 2 - θ * (Int.fract u * (u⁻¹) ^ 2) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
    have hune : u ≠ 0 := ne_of_gt hu0
    rw [bdGenReal, sq]
    field_simp
  have hI1 : IntegrableOn (fun u : ℝ => Int.fract (θ * u) * (u⁻¹) ^ 2) (Ioi 1) := by
    refine Integrable.mono' (g := fun v => v ^ (-2 : ℝ))
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos)
      ((measurable_fract.comp (measurable_const_mul θ)).mul
        ((measurable_id.inv).pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
    rw [← inv_sq_eq_rpow hu0, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Int.fract_nonneg _), abs_of_nonneg (by positivity : (0:ℝ) ≤ (u⁻¹) ^ 2)]
    calc Int.fract (θ * u) * (u⁻¹) ^ 2 ≤ 1 * (u⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right (Int.fract_lt_one _).le (by positivity)
      _ = (u⁻¹) ^ 2 := one_mul _
  have hI2 : IntegrableOn (fun u : ℝ => Int.fract u * (u⁻¹) ^ 2) (Ioi 1) := by
    refine (integrableOn_fractInvSq_Ioi one_pos).congr_fun (fun u _ => ?_) measurableSet_Ioi
    rw [fractInvSq]
  have hdisj : Disjoint (Ioc θ 1) (Ioi 1) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ hx2
    exact absurd (mem_Ioi.mp hx2) (not_lt.mpr hx1)
  have hunion : Ioc θ 1 ∪ Ioi 1 = Ioi θ := Set.Ioc_union_Ioi_eq_Ioi hθ1
  have hray : (∫ v in Ioi θ, fractInvSq v)
      = (∫ v in Ioc θ 1, fractInvSq v) + ∫ v in Ioi (1:ℝ), fractInvSq v := by
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioi
      ((integrableOn_fractInvSq_Ioi hθ0).mono_set (by rw [← hunion]; exact Set.subset_union_left))
      ((integrableOn_fractInvSq_Ioi hθ0).mono_set (by rw [← hunion]; exact Set.subset_union_right))
  have htail : (∫ u in Ioi (1:ℝ), Int.fract u * (u⁻¹) ^ 2) = ∫ v in Ioi (1:ℝ), fractInvSq v := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    rw [fractInvSq]
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_sub hI1 (hI2.const_mul θ),
    integral_const_mul, integral_Ioi_one_fractInvSq_dilate hθ0, hray,
    integral_Ioc_fractInvSq hθ0 hθ1, htail]
  ring

/-- The pairing on the carrier: `⟪bdGen θ, bdTarget⟫ = −θ log θ`. -/
theorem inner_bdGen_bdTarget {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    inner ℂ (bdGen θ) bdTarget = ((-(θ * Real.log θ) : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def, ← integral_bdGenReal_mul_inv hθ0 hθ1, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_bdGenFun θ).coeFn_toLp, memLp_bdTargetFun.coeFn_toLp] with u hu1 hu2
  rw [bdGen, bdTarget, hu1, hu2, bdGenFun_eq_ofReal, bdTargetFun_eq_ofReal, RCLike.inner_apply,
    Complex.conj_ofReal, ← Complex.ofReal_mul]
  ring_nf

/-- **An unconditional lower bound on the Gram diagonal.**  Cauchy--Schwarz against the unit target. -/
theorem norm_bdGen_lower {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    θ * |Real.log θ| ≤ ‖bdGen θ‖ := by
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (bdGen θ) bdTarget
  rw [inner_bdGen_bdTarget hθ0 hθ1, norm_bdTarget, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos hθ0] at hcs
  exact hcs

/-- The Gram diagonal in the same normalisation: `(θ log θ)² ≤ bdGram θ θ`. -/
theorem sq_le_bdGram_self {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (θ * Real.log θ) ^ 2 ≤ bdGram θ θ := by
  have h := norm_bdGen_lower hθ0 hθ1
  have h2 : (θ * |Real.log θ|) ^ 2 ≤ ‖bdGen θ‖ ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) h 2
  rw [bdGram_self]
  calc (θ * Real.log θ) ^ 2 = (θ * |Real.log θ|) ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs]
    _ ≤ ‖bdGen θ‖ ^ 2 := h2

/-! ## The one-generator distance -/

theorem bdGen_ne_zero {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) : bdGen θ ≠ 0 := by
  intro h
  have hlow := norm_bdGen_lower hθ0 hθ1.le
  rw [h, norm_zero] at hlow
  have hlog : Real.log θ < 0 := Real.log_neg hθ0 hθ1
  have : 0 < θ * |Real.log θ| := by
    refine mul_pos hθ0 ?_
    rw [abs_of_neg hlog]
    linarith
  linarith

/-- **The exact distance to a single generator line.**  With the target a unit vector and the pairing
`−θ log θ`, the best approximation by multiples of one generator leaves exactly
`1 − (θ log θ)²/‖bdGen θ‖²`.  This is the `N = 1` case of the Báez-Duarte least-squares quantity, and the
first *upper* bound on a Báez-Duarte distance in this file. -/
theorem exists_norm_sq_sub_smul_bdGen {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ c : ℂ, ‖bdTarget - c • bdGen θ‖ ^ 2
      = 1 - (θ * Real.log θ) ^ 2 / ‖bdGen θ‖ ^ 2 := by
  have hne : bdGen θ ≠ 0 := bdGen_ne_zero hθ0 hθ1
  have hnpos : (0 : ℝ) < ‖bdGen θ‖ := norm_pos_iff.mpr hne
  set m : ℝ := -(θ * Real.log θ) with hm
  refine ⟨((m / ‖bdGen θ‖ ^ 2 : ℝ) : ℂ), ?_⟩
  have hinner : inner ℂ bdTarget (((m / ‖bdGen θ‖ ^ 2 : ℝ) : ℂ) • bdGen θ)
      = ((m / ‖bdGen θ‖ ^ 2 : ℝ) : ℂ) * ((m : ℝ) : ℂ) := by
    rw [inner_smul_right]
    congr 1
    rw [← inner_conj_symm, inner_bdGen_bdTarget hθ0 hθ1.le, Complex.conj_ofReal, hm]
  rw [norm_sub_sq (𝕜 := ℂ), hinner, norm_bdTarget, norm_smul, Complex.norm_real,
    Real.norm_eq_abs]
  have hre : RCLike.re (((m / ‖bdGen θ‖ ^ 2 : ℝ) : ℂ) * ((m : ℝ) : ℂ))
      = m / ‖bdGen θ‖ ^ 2 * m := by
    rw [← Complex.ofReal_mul]
    show ((m / ‖bdGen θ‖ ^ 2 * m : ℝ) : ℂ).re = m / ‖bdGen θ‖ ^ 2 * m
    exact Complex.ofReal_re _
  rw [hre]
  have habs : |m / ‖bdGen θ‖ ^ 2| * ‖bdGen θ‖ = |m| / ‖bdGen θ‖ := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < ‖bdGen θ‖ ^ 2)]
    field_simp
  rw [habs]
  have hmsq : m ^ 2 = (θ * Real.log θ) ^ 2 := by rw [hm]; ring
  have habs2 : (|m| / ‖bdGen θ‖) ^ 2 = m ^ 2 / ‖bdGen θ‖ ^ 2 := by
    rw [div_pow, sq_abs]
  rw [habs2, hmsq]
  field_simp
  ring

/-- **A single-generator sufficient condition for the Riemann hypothesis.**  If Cauchy--Schwarz against the
target is saturated by one generator — that is, if `‖bdGen θ‖` attains its lower bound `θ|log θ|` — then the
target lies on that generator's line, hence in the closed span, hence the Riemann hypothesis holds.

This is the `N = 1`, and therefore weakest, instance of the criterion.  The later finite-family
obstruction proves that this equality always fails (`norm_bdGen_lower_strict_of_lt_one` in
`FiniteFamilyObstruction`), so this declaration is retained only as the exact saturation interface.
Its content is to identify the ratio `θ|log θ| / ‖bdGen θ‖`, i.e. the Gram diagonal `bdGram θ θ`, that
the many-generator quantitative problem generalizes. -/
theorem riemannHypothesis_of_norm_bdGen_eq {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (h : ‖bdGen θ‖ = θ * |Real.log θ|) : RiemannHypothesis := by
  have hne : bdGen θ ≠ 0 := bdGen_ne_zero hθ0 hθ1
  have hnpos : (0 : ℝ) < ‖bdGen θ‖ := norm_pos_iff.mpr hne
  obtain ⟨c, hc⟩ := exists_norm_sq_sub_smul_bdGen hθ0 hθ1
  have hsq : (θ * Real.log θ) ^ 2 = ‖bdGen θ‖ ^ 2 := by
    rw [h, mul_pow, mul_pow, sq_abs]
  rw [hsq, div_self (by positivity : ‖bdGen θ‖ ^ 2 ≠ 0), sub_self] at hc
  have hzero : bdTarget - c • bdGen θ = 0 := by
    have : ‖bdTarget - c • bdGen θ‖ = 0 := by
      nlinarith [norm_nonneg (bdTarget - c • bdGen θ), hc]
    exact norm_eq_zero.mp this
  have hmem : bdTarget ∈
      Submodule.span ℂ (Set.range (fun i : bdIndex => bdGen i.1)) := by
    have hval : bdTarget = c • bdGen θ := by
      rw [← sub_eq_zero]
      exact hzero
    rw [hval]
    refine Submodule.smul_mem _ c (Submodule.subset_span ?_)
    exact ⟨⟨θ, hθ0, hθ1.le⟩, rfl⟩
  exact riemannHypothesis_of_bdTarget_mem_closedSpan
    (Submodule.le_topologicalClosure _ hmem)

end RHTower

end
