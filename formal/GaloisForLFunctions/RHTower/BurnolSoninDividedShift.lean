import GaloisForLFunctions.RHTower.SoninDilationContinuity
import GaloisForLFunctions.RHTower.BurnolSoninProjectedEvaluationTransport

/-!
# The divided-shift operators of the extended Sonine space

For a point `ρ` of the open right half of the critical strip the two operators

```text
(A_ρ f)(t) = ∫_1^∞ u^(-ρ) f(u t) du,     (C_ρ f)(t) = ∫_0^(1 : ℕ) u^(ρ-1) f(u t) du
```

are bounded on `L²(0,∞)`; they are the Bochner integrals of the normalized dilation group against
the characters `u^(-ρ-1/2)` and `u^(ρ-3/2)`.  On the Mellin side they are multiplication by
`1/(ρ-w)` and `1/(w+ρ-1)`, so the cosine transform exchanges them.  Both norms are bounded by
`1/(Re ρ - 1/2)`, which is exactly the reciprocal distance from `ρ` to the critical line.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Normalized dilation of the even carrier, extended by zero to non-positive scales. -/
def evenRayDilate (v : ℝ) (f : evenSubspace) : evenSubspace :=
  if h : 0 < v then evenDilationCLM v h f else 0

theorem evenRayDilate_of_pos {v : ℝ} (hv : 0 < v) (f : evenSubspace) :
    evenRayDilate v f = evenDilationCLM v hv f := dif_pos hv

theorem coe_evenRayDilate {v : ℝ} (hv : 0 < v) (f : evenSubspace) :
    ((evenRayDilate v f : evenSubspace) : SoninL2) = rayDilate v (f : SoninL2) := by
  rw [evenRayDilate_of_pos hv, rayDilate_of_pos hv, coe_evenDilationCLM_apply]

@[simp] theorem norm_evenRayDilate {v : ℝ} (hv : 0 < v) (f : evenSubspace) :
    ‖evenRayDilate v f‖ = ‖f‖ := by
  rw [evenRayDilate_of_pos hv]
  exact norm_evenDilationCLM_apply v hv f

theorem evenRayDilate_ae {v : ℝ} (hv : 0 < v) (f : evenSubspace) :
    (((evenRayDilate v f : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun t : ℝ => (Real.sqrt v : ℂ) * ((f : evenSubspace) : SoninL2) (v * t) := by
  rw [coe_evenRayDilate hv]
  exact rayDilate_ae hv _

theorem continuousOn_evenRayDilate (f : evenSubspace) :
    ContinuousOn (fun v : ℝ => evenRayDilate v f) (Ioi (0 : ℝ)) := by
  intro v₀ hv₀
  have h := continuousOn_rayDilate (f : SoninL2) v₀ hv₀
  rw [ContinuousWithinAt, Metric.tendsto_nhds] at h ⊢
  intro ε hε
  filter_upwards [h ε hε, self_mem_nhdsWithin] with v hv hvpos
  have hvpos' : 0 < v := hvpos
  have hv₀pos : 0 < v₀ := hv₀
  rw [dist_eq_norm] at hv ⊢
  have hcoe : ‖evenRayDilate v f - evenRayDilate v₀ f‖ =
      ‖rayDilate v (f : SoninL2) - rayDilate v₀ (f : SoninL2)‖ := by
    have hsub : ((evenRayDilate v f - evenRayDilate v₀ f : evenSubspace) : SoninL2) =
        rayDilate v (f : SoninL2) - rayDilate v₀ (f : SoninL2) := by
      rw [Submodule.coe_sub, coe_evenRayDilate hvpos', coe_evenRayDilate hv₀pos]
    rw [← hsub]
    rfl
  rw [hcoe]
  exact hv

/-! ## The two dilation characters -/

/-- Forward divided-shift character. -/
def burnolShiftWeight (ρ : ℂ) (u : ℝ) : ℂ := (u : ℂ) ^ (-ρ - 1 / 2)

/-- Reflected divided-shift character. -/
def burnolCoShiftWeight (ρ : ℂ) (u : ℝ) : ℂ := (u : ℂ) ^ (ρ - 3 / 2)

theorem norm_burnolShiftWeight {u : ℝ} (hu : 0 < u) (ρ : ℂ) :
    ‖burnolShiftWeight ρ u‖ = u ^ (-ρ.re - 1 / 2) := by
  rw [burnolShiftWeight, Complex.norm_cpow_eq_rpow_re_of_pos hu]
  norm_num

theorem norm_burnolCoShiftWeight {u : ℝ} (hu : 0 < u) (ρ : ℂ) :
    ‖burnolCoShiftWeight ρ u‖ = u ^ (ρ.re - 3 / 2) := by
  rw [burnolCoShiftWeight, Complex.norm_cpow_eq_rpow_re_of_pos hu]
  norm_num

theorem continuousOn_burnolShiftWeight (ρ : ℂ) :
    ContinuousOn (burnolShiftWeight ρ) (Ioi (0 : ℝ)) := by
  intro u hu
  refine ContinuousAt.continuousWithinAt ?_
  refine (Complex.continuousAt_ofReal_cpow_const u (-ρ - 1 / 2) ?_)
  exact Or.inr (ne_of_gt hu)

theorem continuousOn_burnolCoShiftWeight (ρ : ℂ) :
    ContinuousOn (burnolCoShiftWeight ρ) (Ioi (0 : ℝ)) := by
  intro u hu
  refine ContinuousAt.continuousWithinAt ?_
  refine (Complex.continuousAt_ofReal_cpow_const u (ρ - 3 / 2) ?_)
  exact Or.inr (ne_of_gt hu)

/-! ## Integrability of the two dilation integrands -/

theorem integrable_burnolShift_integrand {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (f : evenSubspace) :
    IntegrableOn (fun u : ℝ => burnolShiftWeight ρ u • evenRayDilate u f) (Ioi (1 : ℝ)) := by
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => burnolShiftWeight ρ u • evenRayDilate u f)
      (volume.restrict (Ioi (1 : ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have h1 : ContinuousOn (burnolShiftWeight ρ) (Ioi (1 : ℝ)) :=
      (continuousOn_burnolShiftWeight ρ).mono (Ioi_subset_Ioi zero_le_one)
    have h2 : ContinuousOn (fun v : ℝ => evenRayDilate v f) (Ioi (1 : ℝ)) :=
      (continuousOn_evenRayDilate f).mono (Ioi_subset_Ioi zero_le_one)
    exact h1.smul h2
  have hbound : IntegrableOn (fun u : ℝ => u ^ (-ρ.re - 1 / 2) * ‖f‖) (Ioi (1 : ℝ)) := by
    apply Integrable.mul_const
    exact (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by linarith)
  refine Integrable.mono' hbound hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  rw [norm_smul, norm_burnolShiftWeight hu0, norm_evenRayDilate hu0]

theorem integrable_burnolCoShift_integrand {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (f : evenSubspace) :
    IntegrableOn (fun u : ℝ => burnolCoShiftWeight ρ u • evenRayDilate u f)
      (Ioo (0 : ℝ) 1) := by
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => burnolCoShiftWeight ρ u • evenRayDilate u f)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    have h1 : ContinuousOn (burnolCoShiftWeight ρ) (Ioo (0 : ℝ) 1) :=
      (continuousOn_burnolCoShiftWeight ρ).mono Ioo_subset_Ioi_self
    have h2 : ContinuousOn (fun v : ℝ => evenRayDilate v f) (Ioo (0 : ℝ) 1) :=
      (continuousOn_evenRayDilate f).mono Ioo_subset_Ioi_self
    exact h1.smul h2
  have hbound : IntegrableOn (fun u : ℝ => u ^ (ρ.re - 3 / 2) * ‖f‖) (Ioo (0 : ℝ) 1) := by
    apply Integrable.mul_const
    have hint : IntervalIntegrable (fun u : ℝ => u ^ (ρ.re - 3 / 2)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hint
    exact hint
  refine Integrable.mono' hbound hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  rw [norm_smul, norm_burnolCoShiftWeight hu.1, norm_evenRayDilate hu.1]

/-! ## The two operators -/

/-- Forward divided shift: Mellin multiplication by `1/(ρ - w)`. -/
def burnolShift (ρ : ℂ) (f : evenSubspace) : evenSubspace :=
  ∫ u in Ioi (1 : ℝ), burnolShiftWeight ρ u • evenRayDilate u f

/-- Reflected divided shift: Mellin multiplication by `1/(w + ρ - 1)`. -/
def burnolCoShift (ρ : ℂ) (f : evenSubspace) : evenSubspace :=
  ∫ u in Ioo (0 : ℝ) 1, burnolCoShiftWeight ρ u • evenRayDilate u f

theorem norm_burnolShift_le {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (f : evenSubspace) :
    ‖burnolShift ρ f‖ ≤ ‖f‖ / (ρ.re - 1 / 2) := by
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have heq : ∀ u ∈ Ioi (1 : ℝ),
      ‖burnolShiftWeight ρ u • evenRayDilate u f‖ = u ^ (-ρ.re - 1 / 2) * ‖f‖ := by
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    rw [norm_smul, norm_burnolShiftWeight hu0, norm_evenRayDilate hu0]
  rw [setIntegral_congr_fun measurableSet_Ioi heq]
  rw [integral_mul_const, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
  rw [Real.one_rpow]
  have hne : ρ.re - 1 / 2 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hkey : -(1 : ℝ) / (-ρ.re - 1 / 2 + 1) * ‖f‖ = ‖f‖ / (ρ.re - 1 / 2) := by
    rw [show -ρ.re - 1 / 2 + 1 = -(ρ.re - 1 / 2) by ring]
    field_simp
  rw [hkey]

theorem norm_burnolCoShift_le {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (f : evenSubspace) :
    ‖burnolCoShift ρ f‖ ≤ ‖f‖ / (ρ.re - 1 / 2) := by
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have heq : ∀ u ∈ Ioo (0 : ℝ) 1,
      ‖burnolCoShiftWeight ρ u • evenRayDilate u f‖ = u ^ (ρ.re - 3 / 2) * ‖f‖ := by
    intro u hu
    rw [norm_smul, norm_burnolCoShiftWeight hu.1, norm_evenRayDilate hu.1]
  rw [setIntegral_congr_fun measurableSet_Ioo heq, integral_mul_const]
  have hI : (∫ u in Ioo (0 : ℝ) 1, u ^ (ρ.re - 3 / 2)) = 1 / (ρ.re - 1 / 2) := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (show (-1 : ℝ) < ρ.re - 3 / 2 by linarith)),
      Real.one_rpow, Real.zero_rpow (by intro h; linarith),
      show ρ.re - 3 / 2 + 1 = ρ.re - 1 / 2 by ring]
    ring
  rw [hI, div_mul_eq_mul_div, one_mul]


/-! ## Pulling continuous functionals through the two integrals -/

theorem inner_burnolShift {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (g f : evenSubspace) :
    ⟪g, burnolShift ρ f⟫_ℂ =
      ∫ u in Ioi (1 : ℝ), burnolShiftWeight ρ u * ⟪g, evenRayDilate u f⟫_ℂ := by
  have h := ContinuousLinearMap.integral_comp_comm (innerSL ℂ g)
    (integrable_burnolShift_integrand hρ f)
  simp only [coe_innerSL_apply] at h
  rw [show ⟪g, burnolShift ρ f⟫_ℂ =
    ∫ u in Ioi (1 : ℝ), ⟪g, burnolShiftWeight ρ u • evenRayDilate u f⟫_ℂ from h.symm]
  apply integral_congr_ae
  filter_upwards with u
  exact inner_smul_right g (evenRayDilate u f) (burnolShiftWeight ρ u)

theorem inner_burnolCoShift {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (g f : evenSubspace) :
    ⟪g, burnolCoShift ρ f⟫_ℂ =
      ∫ u in Ioo (0 : ℝ) 1, burnolCoShiftWeight ρ u * ⟪g, evenRayDilate u f⟫_ℂ := by
  have h := ContinuousLinearMap.integral_comp_comm (innerSL ℂ g)
    (integrable_burnolCoShift_integrand hρ f)
  simp only [coe_innerSL_apply] at h
  rw [show ⟪g, burnolCoShift ρ f⟫_ℂ =
    ∫ u in Ioo (0 : ℝ) 1, ⟪g, burnolCoShiftWeight ρ u • evenRayDilate u f⟫_ℂ from h.symm]
  apply integral_congr_ae
  filter_upwards with u
  exact inner_smul_right g (evenRayDilate u f) (burnolCoShiftWeight ρ u)

/-! ## Ray inversion -/

theorem integral_Ioi_one_eq_integral_Ioo_inv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : ℝ → E) :
    (∫ u in Ioi (1 : ℝ), G u) = ∫ v in Ioo (0 : ℝ) 1, (v ^ (-2 : ℝ)) • G v⁻¹ := by
  have key := integral_comp_rpow_Ioi ((Ioi (1 : ℝ)).indicator G) (p := (-1 : ℝ)) (by norm_num)
  have hrhs : (∫ y in Ioi (0 : ℝ), (Ioi (1 : ℝ)).indicator G y) = ∫ u in Ioi (1 : ℝ), G u := by
    rw [setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  have hind : (∫ x in Ioi (0 : ℝ),
        (Ioo (0 : ℝ) 1).indicator (fun v : ℝ => (v ^ (-2 : ℝ)) • G v⁻¹) x) =
      ∫ v in Ioo (0 : ℝ) 1, (v ^ (-2 : ℝ)) • G v⁻¹ := by
    rw [setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Ioo_subset_Ioi_self]
  have hlhs : (∫ x in Ioi (0 : ℝ),
        (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • (Ioi (1 : ℝ)).indicator G (x ^ (-1 : ℝ))) =
      ∫ v in Ioo (0 : ℝ) 1, (v ^ (-2 : ℝ)) • G v⁻¹ := by
    rw [← hind]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := hx
    dsimp only
    rw [Real.rpow_neg_one]
    by_cases hlt : x < 1
    · have hmem : x⁻¹ ∈ Ioi (1 : ℝ) := by
        rw [mem_Ioi]
        exact one_lt_inv_iff₀.mpr ⟨hx0, hlt⟩
      rw [Set.indicator_of_mem hmem,
        Set.indicator_of_mem (show x ∈ Ioo (0:ℝ) 1 from ⟨hx0, hlt⟩)]
      norm_num
    · have hmem : x⁻¹ ∉ Ioi (1 : ℝ) := by
        rw [mem_Ioi, not_lt]
        exact inv_le_one_of_one_le₀ (not_lt.mp hlt)
      rw [Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem (show x ∉ Ioo (0:ℝ) 1 from fun h => hlt h.2)]
      simp
  rw [← hrhs, ← key, hlhs]

/-! ## The cosine transform exchanges the two divided shifts -/

theorem evenFourierTransform_eq_soninCosineUnitary (f : evenSubspace) :
    evenFourierTransform f = soninCosineUnitary f := by
  apply Subtype.ext
  rw [coe_evenFourierTransform_apply, coe_soninCosineUnitary]

theorem soninCosineUnitary_evenRayDilate {v : ℝ} (hv : 0 < v) (f : evenSubspace) :
    soninCosineUnitary (evenRayDilate v f) = evenRayDilate v⁻¹ (soninCosineUnitary f) := by
  rw [evenRayDilate_of_pos hv, evenRayDilate_of_pos (inv_pos.mpr hv),
    soninCosineUnitary_evenDilation v hv f]

theorem inner_soninCosineUnitary_right (x y : evenSubspace) :
    ⟪x, soninCosineUnitary y⟫_ℂ = ⟪soninCosineUnitary x, y⟫_ℂ := by
  calc ⟪x, soninCosineUnitary y⟫_ℂ
      = ⟪soninCosineUnitary x, soninCosineUnitary (soninCosineUnitary y)⟫_ℂ :=
        (soninCosineUnitary.inner_map_map x (soninCosineUnitary y)).symm
    _ = ⟪soninCosineUnitary x, y⟫_ℂ := by rw [soninCosineUnitary_involutive]

/-- **The cosine transform exchanges the forward and reflected divided shifts.** -/
theorem soninCosineUnitary_burnolShift {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (f : evenSubspace) :
    soninCosineUnitary (burnolShift ρ f) = burnolCoShift ρ (soninCosineUnitary f) := by
  apply ext_inner_left ℂ
  intro g
  rw [inner_soninCosineUnitary_right g (burnolShift ρ f),
    inner_burnolShift hρ (soninCosineUnitary g) f, inner_burnolCoShift hρ g]
  rw [integral_Ioi_one_eq_integral_Ioo_inv
    (fun u : ℝ => burnolShiftWeight ρ u * ⟪soninCosineUnitary g, evenRayDilate u f⟫_ℂ)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro v hv
  dsimp only
  have hv0 : 0 < v := hv.1
  have hvinv : 0 < v⁻¹ := inv_pos.mpr hv0
  have hinner : ⟪soninCosineUnitary g, evenRayDilate v⁻¹ f⟫_ℂ =
      ⟪g, evenRayDilate v (soninCosineUnitary f)⟫_ℂ := by
    rw [← soninCosineUnitary.inner_map_map (soninCosineUnitary g) (evenRayDilate v⁻¹ f),
      soninCosineUnitary_involutive, soninCosineUnitary_evenRayDilate hvinv, inv_inv]
  rw [hinner]
  have hweight : (v ^ (-2 : ℝ) : ℝ) • (burnolShiftWeight ρ v⁻¹ *
      ⟪g, evenRayDilate v (soninCosineUnitary f)⟫_ℂ) =
      burnolCoShiftWeight ρ v * ⟪g, evenRayDilate v (soninCosineUnitary f)⟫_ℂ := by
    rw [Complex.real_smul, ← mul_assoc]
    congr 1
    rw [burnolShiftWeight, burnolCoShiftWeight]
    have hvne : ((v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hv0
    have harg : Complex.arg ((v : ℝ) : ℂ) ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hv0.le]
      exact fun h => Real.pi_ne_zero h.symm
    have hinvcpow : (((v⁻¹ : ℝ)) : ℂ) ^ (-ρ - 1 / 2) = ((v : ℝ) : ℂ) ^ (ρ + 1 / 2) := by
      rw [show (((v⁻¹ : ℝ)) : ℂ) = (((v : ℝ) : ℂ))⁻¹ by push_cast; ring,
        Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
      congr 1
      ring
    rw [hinvcpow, Complex.ofReal_cpow hv0.le, ← Complex.cpow_add _ _ hvne]
    congr 1
    push_cast
    ring
  exact hweight

/-! ## Pointwise form of the forward divided shift -/

/-- Globally measurable form of the forward divided-shift kernel. -/
def burnolShiftKernel (ρ : ℂ) (u : ℝ) : ℂ := Complex.exp ((Real.log u : ℂ) * (-ρ))

theorem burnolShiftKernel_eq_cpow {u : ℝ} (hu : 0 < u) (ρ : ℂ) :
    burnolShiftKernel ρ u = (u : ℂ) ^ (-ρ) := by
  rw [burnolShiftKernel, Complex.cpow_def_of_ne_zero
    (by exact_mod_cast ne_of_gt hu : ((u : ℝ) : ℂ) ≠ 0), ← Complex.ofReal_log hu.le]

theorem norm_burnolShiftKernel {u : ℝ} (hu : 0 < u) (ρ : ℂ) :
    ‖burnolShiftKernel ρ u‖ = u ^ (-ρ.re) := by
  rw [burnolShiftKernel_eq_cpow hu, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.neg_re]

theorem measurable_burnolShiftKernel (ρ : ℂ) : Measurable (burnolShiftKernel ρ) := by
  apply Complex.measurable_exp.comp
  exact (Complex.measurable_ofReal.comp Real.measurable_log).mul measurable_const

theorem burnolShiftKernel_mul_sqrt {u : ℝ} (hu : 0 < u) (ρ : ℂ) :
    burnolShiftWeight ρ u * (Real.sqrt u : ℂ) = burnolShiftKernel ρ u := by
  rw [burnolShiftKernel_eq_cpow hu, burnolShiftWeight]
  have hune : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
  have hsq : ((Real.sqrt u : ℝ) : ℂ) = ((u : ℝ) : ℂ) ^ ((1 : ℂ) / 2) := by
    rw [show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hu.le]
    norm_cast
    exact Real.sqrt_eq_rpow u
  rw [hsq, ← Complex.cpow_add _ _ hune]
  congr 1
  ring

/-- The pointwise forward divided shift of a function on the line. -/
def burnolShiftFun (ρ : ℂ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ u in Ioi (1 : ℝ), burnolShiftKernel ρ u * F (u * t)

theorem stronglyMeasurable_burnolShiftIntegrand (ρ : ℂ) {F : ℝ → ℂ}
    (hF : StronglyMeasurable F) :
    StronglyMeasurable (fun p : ℝ × ℝ => burnolShiftKernel ρ p.2 * F (p.2 * p.1)) := by
  refine StronglyMeasurable.mul ?_ ?_
  · exact ((measurable_burnolShiftKernel ρ).comp measurable_snd).stronglyMeasurable
  · exact hF.comp_measurable (measurable_snd.mul measurable_fst)

theorem stronglyMeasurable_burnolShiftIntegrand_swap (ρ : ℂ) {F : ℝ → ℂ}
    (hF : StronglyMeasurable F) :
    StronglyMeasurable (fun q : ℝ × ℝ => burnolShiftKernel ρ q.1 * F (q.1 * q.2)) := by
  refine StronglyMeasurable.mul ?_ ?_
  · exact ((measurable_burnolShiftKernel ρ).comp measurable_fst).stronglyMeasurable
  · exact hF.comp_measurable (measurable_fst.mul measurable_snd)

/-- Squared mass of a dilated representative. -/
theorem integral_norm_sq_dilate {u : ℝ} (hu : 0 < u) (f : evenSubspace) :
    (∫ t : ℝ, ‖(((f : evenSubspace) : SoninL2) : ℝ → ℂ) (u * t)‖ ^ 2) = ‖f‖ ^ 2 / u := by
  have hnorm : ‖((evenDilationCLM u hu f : evenSubspace) : SoninL2)‖ = ‖f‖ :=
    norm_evenDilationCLM_apply u hu f
  have hsq := norm_sq_lp_eq_integral_norm_sq ((evenDilationCLM u hu f : evenSubspace) : SoninL2)
  rw [hnorm] at hsq
  have hae : (∫ t : ℝ, ‖(((evenDilationCLM u hu f : evenSubspace) : SoninL2) : ℝ → ℂ) t‖ ^ 2) =
      ∫ t : ℝ, u * ‖(((f : evenSubspace) : SoninL2) : ℝ → ℂ) (u * t)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [evenRayDilate_ae hu f] with t ht
    rw [show (((evenDilationCLM u hu f : evenSubspace) : SoninL2) : ℝ → ℂ) t =
      (((evenRayDilate u f : evenSubspace) : SoninL2) : ℝ → ℂ) t by
        rw [evenRayDilate_of_pos hu]]
    rw [ht, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg u), mul_pow, Real.sq_sqrt hu.le]
  rw [hae, integral_const_mul] at hsq
  field_simp at hsq ⊢
  linarith [hsq]

/-! ## Product integrability of the divided-shift integrand -/

theorem memLp_dilate_representative {u : ℝ} (hu : 0 < u) (f : evenSubspace) :
    MemLp (fun t : ℝ => (((f : evenSubspace) : SoninL2) : ℝ → ℂ) (u * t)) 2 volume := by
  have hmem : MemLp (((evenRayDilate u f : evenSubspace) : SoninL2) : ℝ → ℂ) 2 volume :=
    Lp.memLp _
  have hsc : ((Real.sqrt u : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hu)
  refine (memLp_congr_ae ?_).mp (hmem.const_mul (((Real.sqrt u : ℝ) : ℂ))⁻¹)
  filter_upwards [evenRayDilate_ae hu f] with t ht
  rw [ht, ← mul_assoc, inv_mul_cancel₀ hsc, one_mul]

theorem integrableOn_dilate_representative {u : ℝ} (hu : 0 < u) (f : evenSubspace)
    {s : Set ℝ} (hsfin : volume s ≠ ⊤) :
    IntegrableOn (fun t : ℝ => (((f : evenSubspace) : SoninL2) : ℝ → ℂ) (u * t)) s volume := by
  haveI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hsfin
  exact ((memLp_dilate_representative hu f).restrict s).integrable (by norm_num)

theorem setIntegral_norm_dilate_le {u : ℝ} (hu : 0 < u) (f : evenSubspace)
    {s : Set ℝ} (hs : MeasurableSet s) (hsfin : volume s ≠ ⊤) :
    (∫ t in s, ‖(((f : evenSubspace) : SoninL2) : ℝ → ℂ) (u * t)‖) ≤
      u ^ (-(1 : ℝ) / 2) * ((volume.real s + ‖f‖ ^ 2) / 2) := by
  set F : ℝ → ℂ := (((f : evenSubspace) : SoninL2) : ℝ → ℂ) with hF
  have hsq : Integrable (fun t : ℝ => ‖F (u * t)‖ ^ 2) volume := by
    have := memLp_dilate_representative hu f
    exact (memLp_two_iff_integrable_sq_norm this.aestronglyMeasurable).mp this
  have hsqInt : (∫ t : ℝ, ‖F (u * t)‖ ^ 2) = ‖f‖ ^ 2 / u := integral_norm_sq_dilate hu f
  have hAM : ∀ t : ℝ, ‖F (u * t)‖ ≤
      (u ^ (-(1:ℝ)/2) + u ^ ((1:ℝ)/2) * ‖F (u * t)‖ ^ 2) / 2 := by
    intro t
    have hp : (0:ℝ) < u ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hu _
    have hkey : 0 ≤ (u ^ (-(1:ℝ)/4) - u ^ ((1:ℝ)/4) * ‖F (u * t)‖) ^ 2 := sq_nonneg _
    have hprod : u ^ (-(1:ℝ)/4) * u ^ ((1:ℝ)/4) = 1 := by
      rw [← Real.rpow_add hu]
      norm_num
    have hsq1 : (u ^ (-(1:ℝ)/4)) ^ 2 = u ^ (-(1:ℝ)/2) := by
      rw [← Real.rpow_natCast (u ^ (-(1:ℝ)/4)) 2, ← Real.rpow_mul hu.le]
      norm_num
    have hsq2 : (u ^ ((1:ℝ)/4)) ^ 2 = u ^ ((1:ℝ)/2) := by
      rw [← Real.rpow_natCast (u ^ ((1:ℝ)/4)) 2, ← Real.rpow_mul hu.le]
      norm_num
    nlinarith [hkey, hprod, hsq1, hsq2, norm_nonneg (F (u * t))]
  have hint1 : IntegrableOn (fun t : ℝ => ‖F (u * t)‖) s volume :=
    (integrableOn_dilate_representative hu f hsfin).norm
  have hsqres : IntegrableOn (fun t : ℝ => ‖F (u * t)‖ ^ 2) s volume := hsq.restrict
  have hbound : IntegrableOn
      (fun t : ℝ => (u ^ (-(1:ℝ)/2) + u ^ ((1:ℝ)/2) * ‖F (u * t)‖ ^ 2) / 2) s volume := by
    haveI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hsfin
    exact ((integrable_const _).add (hsqres.const_mul _)).div_const 2
  have hle : (∫ t in s, ‖F (u * t)‖) ≤
      ∫ t in s, (u ^ (-(1:ℝ)/2) + u ^ ((1:ℝ)/2) * ‖F (u * t)‖ ^ 2) / 2 :=
    setIntegral_mono_on hint1 hbound hs (fun t _ => hAM t)
  refine le_trans hle ?_
  have hsqle : (∫ t in s, ‖F (u * t)‖ ^ 2) ≤ ‖f‖ ^ 2 / u := by
    rw [← hsqInt]
    exact setIntegral_le_integral hsq (Filter.Eventually.of_forall fun t => sq_nonneg _)
  have hupow : u ^ ((1:ℝ)/2) / u = u ^ (-(1:ℝ)/2) := by
    have h1 : u ^ (-(1:ℝ)/2) * u ^ (1:ℝ) = u ^ ((1:ℝ)/2) := by
      rw [← Real.rpow_add hu]
      norm_num
    rw [Real.rpow_one] at h1
    rw [div_eq_iff (ne_of_gt hu)]
    exact h1.symm
  have hsplit : (∫ t in s, (u ^ (-(1:ℝ)/2) + u ^ ((1:ℝ)/2) * ‖F (u * t)‖ ^ 2) / 2) =
      (u ^ (-(1:ℝ)/2) * volume.real s +
        u ^ ((1:ℝ)/2) * ∫ t in s, ‖F (u * t)‖ ^ 2) / 2 := by
    haveI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hsfin
    rw [integral_div, integral_add (integrable_const _) (hsqres.const_mul _),
      integral_const_mul, setIntegral_const, smul_eq_mul]
    ring
  rw [hsplit]
  have h2 : u ^ ((1:ℝ)/2) * (∫ t in s, ‖F (u * t)‖ ^ 2) ≤ u ^ (-(1:ℝ)/2) * ‖f‖ ^ 2 := by
    calc u ^ ((1:ℝ)/2) * (∫ t in s, ‖F (u * t)‖ ^ 2)
        ≤ u ^ ((1:ℝ)/2) * (‖f‖ ^ 2 / u) :=
          mul_le_mul_of_nonneg_left hsqle (le_of_lt (Real.rpow_pos_of_pos hu _))
      _ = u ^ (-(1:ℝ)/2) * ‖f‖ ^ 2 := by
          rw [← hupow]
          ring
  nlinarith [h2]

/-- Product integrability of the divided-shift integrand over a finite-measure slab. -/
theorem integrable_burnolShiftIntegrand_prod {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (f : evenSubspace)
    {s : Set ℝ} (hs : MeasurableSet s) (hsfin : volume s ≠ ⊤) :
    Integrable (fun p : ℝ × ℝ => burnolShiftKernel ρ p.2 *
        (((f : evenSubspace) : SoninL2) : ℝ → ℂ) (p.2 * p.1))
      ((volume.restrict s).prod (volume.restrict (Ioi (1 : ℝ)))) := by
  set F : ℝ → ℂ := (((f : evenSubspace) : SoninL2) : ℝ → ℂ) with hFdef
  have hFm : StronglyMeasurable F := Lp.stronglyMeasurable _
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => burnolShiftKernel ρ p.2 * F (p.2 * p.1))
      ((volume.restrict s).prod (volume.restrict (Ioi (1 : ℝ)))) :=
    (stronglyMeasurable_burnolShiftIntegrand ρ hFm).aestronglyMeasurable
  rw [integrable_prod_iff' hmeas]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    exact (integrableOn_dilate_representative hu0 f hsfin).const_mul _
  · have hswap : StronglyMeasurable
        (fun q : ℝ × ℝ => ‖burnolShiftKernel ρ q.1 * F (q.1 * q.2)‖) :=
      (stronglyMeasurable_burnolShiftIntegrand_swap ρ hFm).norm
    have hmeasint : StronglyMeasurable
        (fun u : ℝ => ∫ t in s, ‖burnolShiftKernel ρ u * F (u * t)‖) :=
      hswap.integral_prod_right'
    set C : ℝ := (volume.real s + ‖f‖ ^ 2) / 2 with hC
    have hC0 : 0 ≤ C := by
      have : 0 ≤ volume.real s := ENNReal.toReal_nonneg
      positivity
    have hboundint : IntegrableOn (fun u : ℝ => u ^ (-ρ.re - 1 / 2) * C) (Ioi (1 : ℝ)) := by
      apply Integrable.mul_const
      exact (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by linarith)
    refine Integrable.mono' hboundint hmeasint.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    have hnn : 0 ≤ ∫ t in s, ‖burnolShiftKernel ρ u * F (u * t)‖ :=
      setIntegral_nonneg hs fun t _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hpull : (∫ t in s, ‖burnolShiftKernel ρ u * F (u * t)‖) =
        u ^ (-ρ.re) * ∫ t in s, ‖F (u * t)‖ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun hs
      intro t _
      dsimp only
      rw [norm_mul, norm_burnolShiftKernel hu0]
    rw [hpull]
    have hkey := setIntegral_norm_dilate_le hu0 f hs hsfin
    have hupos : (0:ℝ) < u ^ (-ρ.re) := Real.rpow_pos_of_pos hu0 _
    have hsplit : u ^ (-ρ.re - 1 / 2) = u ^ (-ρ.re) * u ^ (-(1:ℝ)/2) := by
      rw [← Real.rpow_add hu0]
      congr 1
      ring
    rw [hsplit, mul_assoc]
    exact mul_le_mul_of_nonneg_left hkey hupos.le

/-- The pointwise divided shift is integrable on every finite-measure slab. -/
theorem integrableOn_burnolShiftFun {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (f : evenSubspace)
    {s : Set ℝ} (hs : MeasurableSet s) (hsfin : volume s ≠ ⊤) :
    IntegrableOn (burnolShiftFun ρ (((f : evenSubspace) : SoninL2) : ℝ → ℂ)) s volume :=
  (integrable_burnolShiftIntegrand_prod hρ f hs hsfin).integral_prod_left

/-! ## Identification of the divided shift with its pointwise integral -/

theorem evenProjection_eq_self_of_mem {y : SoninL2} (hy : y ∈ evenSubspace) :
    evenProjection y = y := by
  obtain ⟨z, hz⟩ := hy
  have hzz : evenProjection z = y := hz
  have hid := evenProjection_idempotent
  rw [isIdempotentElem_iff] at hid
  rw [← hzz]
  calc evenProjection (evenProjection z) = (evenProjection * evenProjection) z := rfl
    _ = evenProjection z := by rw [hid]

theorem inner_indicatorConstLp_eq_setIntegral {s : Set ℝ} (hs : MeasurableSet s)
    (hsfin : volume s ≠ ⊤) (y : SoninL2) :
    ⟪(indicatorConstLp 2 hs hsfin (1 : ℂ)), y⟫_ℂ = ∫ t in s, (y : ℝ → ℂ) t := by
  rw [MeasureTheory.L2.inner_def, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [(indicatorConstLp_coeFn :
    ((indicatorConstLp 2 hs hsfin (1 : ℂ) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      s.indicator fun _ => (1 : ℂ))] with t ht
  rw [ht]
  by_cases h : t ∈ s
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- The even indicator test vector of a finite-measure set. -/
def evenIndicatorTest {s : Set ℝ} (hs : MeasurableSet s) (hsfin : volume s ≠ ⊤) :
    evenSubspace :=
  ⟨evenProjection (indicatorConstLp 2 hs hsfin (1 : ℂ)), ⟨_, rfl⟩⟩

theorem inner_evenIndicatorTest {s : Set ℝ} (hs : MeasurableSet s) (hsfin : volume s ≠ ⊤)
    (y : evenSubspace) :
    ⟪evenIndicatorTest hs hsfin, y⟫_ℂ =
      ∫ t in s, (((y : evenSubspace) : SoninL2) : ℝ → ℂ) t := by
  rw [← inner_indicatorConstLp_eq_setIntegral hs hsfin ((y : evenSubspace) : SoninL2)]
  have hy : evenProjection ((y : evenSubspace) : SoninL2) = ((y : evenSubspace) : SoninL2) :=
    evenProjection_eq_self_of_mem y.property
  have hsym : ⟪evenProjection (indicatorConstLp 2 hs hsfin (1 : ℂ)),
      ((y : evenSubspace) : SoninL2)⟫_ℂ =
      ⟪indicatorConstLp 2 hs hsfin (1 : ℂ),
        evenProjection ((y : evenSubspace) : SoninL2)⟫_ℂ :=
    evenProjection_symmetric _ _
  change ⟪evenProjection (indicatorConstLp 2 hs hsfin (1 : ℂ)),
    ((y : evenSubspace) : SoninL2)⟫_ℂ = _
  rw [hsym, hy]

theorem setIntegral_burnolShift {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (f : evenSubspace)
    {s : Set ℝ} (hs : MeasurableSet s) (hsfin : volume s ≠ ⊤) :
    (∫ t in s, (((burnolShift ρ f : evenSubspace) : SoninL2) : ℝ → ℂ) t) =
      ∫ t in s, burnolShiftFun ρ (((f : evenSubspace) : SoninL2) : ℝ → ℂ) t := by
  set F : ℝ → ℂ := (((f : evenSubspace) : SoninL2) : ℝ → ℂ) with hFdef
  rw [← inner_evenIndicatorTest hs hsfin (burnolShift ρ f),
    inner_burnolShift hρ (evenIndicatorTest hs hsfin) f]
  have hstep : ∀ u ∈ Ioi (1 : ℝ),
      burnolShiftWeight ρ u * ⟪evenIndicatorTest hs hsfin, evenRayDilate u f⟫_ℂ =
        ∫ t in s, burnolShiftKernel ρ u * F (u * t) := by
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    rw [inner_evenIndicatorTest hs hsfin (evenRayDilate u f)]
    have hcongr : (∫ t in s, (((evenRayDilate u f : evenSubspace) : SoninL2) : ℝ → ℂ) t) =
        ∫ t in s, (Real.sqrt u : ℂ) * F (u * t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (evenRayDilate_ae hu0 f)] with t ht
      rw [ht]
    rw [hcongr, ← integral_const_mul]
    apply setIntegral_congr_fun hs
    intro t _
    dsimp only
    rw [← mul_assoc, burnolShiftKernel_mul_sqrt hu0]
  rw [setIntegral_congr_fun measurableSet_Ioi hstep]
  exact (integral_integral_swap
    (integrable_burnolShiftIntegrand_prod hρ f hs hsfin)).symm

/-- **The forward divided shift is the pointwise divided-shift integral.** -/
theorem coe_burnolShift_ae {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (f : evenSubspace) :
    (((burnolShift ρ f : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      burnolShiftFun ρ (((f : evenSubspace) : SoninL2) : ℝ → ℂ) := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
  · intro s hs hsfin
    haveI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hsfin.ne
    exact ((Lp.memLp ((burnolShift ρ f : evenSubspace) : SoninL2)).restrict s).integrable
      (by norm_num)
  · intro s hs hsfin
    exact integrableOn_burnolShiftFun hρ f hs hsfin.ne
  · intro s hs hsfin
    exact setIntegral_burnolShift hρ f hs hsfin.ne

/-! ## The head laws -/

theorem integrableOn_burnolShiftIntegrand_slice {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (f : evenSubspace)
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => burnolShiftKernel ρ u *
      (((f : evenSubspace) : SoninL2) : ℝ → ℂ) (u * t)) (Ioi (1 : ℝ)) volume := by
  set F : ℝ → ℂ := (((f : evenSubspace) : SoninL2) : ℝ → ℂ) with hFdef
  have hFm : StronglyMeasurable F := Lp.stronglyMeasurable _
  have hmeas : AEStronglyMeasurable (fun u : ℝ => burnolShiftKernel ρ u * F (u * t))
      (volume.restrict (Ioi (1 : ℝ))) := by
    refine (StronglyMeasurable.mul ?_ ?_).aestronglyMeasurable
    · exact (measurable_burnolShiftKernel ρ).stronglyMeasurable
    · exact hFm.comp_measurable (measurable_id.mul_const t)
  have hsq : Integrable (fun u : ℝ => ‖F (u * t)‖ ^ 2) volume := by
    have hmem : MemLp (fun u : ℝ => F (u * t)) 2 volume := by
      have := memLp_dilate_representative ht f
      refine (memLp_congr_ae ?_).mp this
      filter_upwards with u
      rw [mul_comm]
    exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  have hbound : IntegrableOn
      (fun u : ℝ => u ^ (-ρ.re - 1 / 2) / 2 + ‖F (u * t)‖ ^ 2 / 2) (Ioi (1 : ℝ)) volume := by
    refine Integrable.add ?_ ?_
    · exact ((integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by linarith)).div_const 2
    · exact hsq.restrict.div_const 2
  refine Integrable.mono' hbound hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  rw [norm_mul, norm_burnolShiftKernel hu0]
  set B : ℝ := ‖F (u * t)‖ with hB
  set lam : ℝ := u ^ (ρ.re - 1 / 2) with hlam
  have hlampos : 0 < lam := Real.rpow_pos_of_pos hu0 _
  have hlamge : 1 ≤ lam := Real.one_le_rpow hu1 (by linarith)
  have hsq2 : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlampos.le
  have hspos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlampos
  have hAB : u ^ (-ρ.re) * B ≤ ((u ^ (-ρ.re)) ^ 2 * lam + B ^ 2 / lam) / 2 := by
    have hid : ((u ^ (-ρ.re)) ^ 2 * lam + B ^ 2 / lam) / 2 - u ^ (-ρ.re) * B
        = (u ^ (-ρ.re) * lam - B) ^ 2 / (2 * lam) := by
      field_simp
      ring
    have hnn : (0 : ℝ) ≤ (u ^ (-ρ.re) * lam - B) ^ 2 / (2 * lam) := by positivity
    rw [← hid] at hnn
    linarith
  have hfirst : (u ^ (-ρ.re)) ^ 2 * lam = u ^ (-ρ.re - 1 / 2) := by
    have h1 : (u ^ (-ρ.re)) ^ 2 = u ^ (-ρ.re * 2) := by
      rw [← Real.rpow_natCast (u ^ (-ρ.re)) 2, ← Real.rpow_mul hu0.le]
      norm_num
    rw [h1, hlam, ← Real.rpow_add hu0]
    congr 1
    ring
  have hsecond : B ^ 2 / lam ≤ B ^ 2 := by
    rw [div_le_iff₀ hlampos]
    nlinarith [sq_nonneg B, hlamge]
  rw [hfirst] at hAB
  linarith [hAB, hsecond]

theorem ofReal_div_cpow {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    (((x / y : ℝ)) : ℂ) ^ z = ((x : ℝ) : ℂ) ^ z * (((y : ℝ) : ℂ) ^ z)⁻¹ := by
  have hxy : (0 : ℝ) < x / y := div_pos hx hy
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hxy),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hx),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hy),
    ← Complex.ofReal_log hxy.le, ← Complex.ofReal_log hx.le, ← Complex.ofReal_log hy.le,
    Real.log_div (ne_of_gt hx) (ne_of_gt hy)]
  rw [← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integral_Ioc_ofReal_cpow_of_le {p q : ℝ} (hpq : p ≤ q) {z : ℂ}
    (hz : -1 < z.re) :
    (∫ u in Ioc p q, ((u : ℝ) : ℂ) ^ z) =
      (((q : ℝ) : ℂ) ^ (z + 1) - ((p : ℝ) : ℂ) ^ (z + 1)) / (z + 1) := by
  rw [← intervalIntegral.integral_of_le hpq]
  exact integral_cpow (Or.inl hz)

theorem integral_Ioo_ofReal_cpow {q : ℝ} (hq : 0 < q) {z : ℂ} (hz : -1 < z.re) :
    (∫ u in Ioo (0 : ℝ) q, ((u : ℝ) : ℂ) ^ z) = ((q : ℝ) : ℂ) ^ (z + 1) / (z + 1) := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hq.le, integral_cpow (Or.inl hz)]
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hzeq : z = -1 := by linear_combination h
    rw [hzeq] at hz
    norm_num at hz
  rw [Complex.ofReal_zero, Complex.zero_cpow hz1]
  ring

/-- **Head law for the forward divided shift.**  On the aperture head the divided shift of a
head-constant vector is again constant, provided the uncompleted Mellin value at `ρ` vanishes. -/
theorem burnolShiftFun_head_eq {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1)
    {a : ℝ} (ha : 0 < a) (f : evenSubspace) {c : ℂ}
    (hc : ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) a → (((f : evenSubspace) : SoninL2) : ℝ → ℂ) s = c)
    (hint : IntegrableOn (fun s : ℝ =>
      (((f : evenSubspace) : SoninL2) : ℝ → ℂ) s * ((s : ℂ) ^ (-ρ))) (Ioi (0 : ℝ)) volume)
    (hvanish : (∫ s in Ioi (0 : ℝ),
      (((f : evenSubspace) : SoninL2) : ℝ → ℂ) s * ((s : ℂ) ^ (-ρ))) = 0)
    {t : ℝ} (ht0 : 0 < t) (hta : t < a) :
    burnolShiftFun ρ (((f : evenSubspace) : SoninL2) : ℝ → ℂ) t = -c / (1 - ρ) := by
  set F : ℝ → ℂ := (((f : evenSubspace) : SoninL2) : ℝ → ℂ) with hFdef
  set R : ℝ := a / t with hRdef
  have hR1 : 1 < R := (one_lt_div ht0).mpr hta
  have hRpos : 0 < R := lt_trans zero_lt_one hR1
  have hRt : t * R = a := by
    rw [hRdef]
    field_simp
  have hznegre : (-1 : ℝ) < (-ρ).re := by
    rw [Complex.neg_re]; linarith
  have hone_sub : (1 : ℂ) - ρ ≠ 0 := by
    intro h
    have : ρ = 1 := by linear_combination -h
    rw [this] at hρ1
    norm_num at hρ1
  have hslice := integrableOn_burnolShiftIntegrand_slice hρ f ht0
  have hunion : Ioo (1 : ℝ) R ∪ Ici R = Ioi (1 : ℝ) := Ioo_union_Ici_eq_Ioi hR1
  have hdisj : Disjoint (Ioo (1 : ℝ) R) (Ici R) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx' (not_le.mpr hx.2)
  have hsplit : burnolShiftFun ρ F t =
      (∫ u in Ioo (1 : ℝ) R, burnolShiftKernel ρ u * F (u * t)) +
        ∫ u in Ici R, burnolShiftKernel ρ u * F (u * t) := by
    rw [burnolShiftFun, ← hunion]
    exact setIntegral_union hdisj measurableSet_Ici
      (hslice.mono_set (by rw [← hunion]; exact subset_union_left))
      (hslice.mono_set (by rw [← hunion]; exact subset_union_right))
  -- head piece
  have hcshift : ∀ᵐ u ∂volume, t * u ∈ Ioo (0 : ℝ) a → F (t * u) = c := by
    exact ((realMul_quasiMeasurePreserving t ht0.ne').tendsto_ae).eventually hc
  have hA : (∫ u in Ioo (1 : ℝ) R, burnolShiftKernel ρ u * F (u * t)) =
      c * ((((R : ℝ)) : ℂ) ^ ((1 : ℂ) - ρ) - 1) / ((1 : ℂ) - ρ) := by
    have hcongr : (∫ u in Ioo (1 : ℝ) R, burnolShiftKernel ρ u * F (u * t)) =
        ∫ u in Ioo (1 : ℝ) R, ((u : ℂ) ^ (-ρ)) * c := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo,
        ae_restrict_of_ae hcshift] with u hu hval
      have hu0 : 0 < u := lt_trans zero_lt_one hu.1
      have hmem : t * u ∈ Ioo (0 : ℝ) a := by
        constructor
        · positivity
        · calc t * u < t * R := by exact mul_lt_mul_of_pos_left hu.2 ht0
            _ = a := hRt
      rw [burnolShiftKernel_eq_cpow hu0, mul_comm u t, hval hmem]
    rw [hcongr, integral_mul_const, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      integral_Ioc_ofReal_cpow_of_le hR1.le hznegre]
    rw [Complex.ofReal_one, Complex.one_cpow]
    ring_nf
  -- tail piece
  have hB : (∫ u in Ici R, burnolShiftKernel ρ u * F (u * t)) =
      ((t : ℂ) ^ (ρ - 1)) * ∫ x in Ioi a, F x * ((x : ℂ) ^ (-ρ)) := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    have hsub := integral_comp_mul_left_Ioi
      (fun x : ℝ => burnolShiftKernel ρ (x / t) * F x) R ht0
    have hlhs : (∫ u in Ioi R, burnolShiftKernel ρ u * F (u * t)) =
        ∫ u in Ioi R, burnolShiftKernel ρ ((t * u) / t) * F (t * u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      dsimp only
      rw [mul_comm t u, mul_div_cancel_right₀ _ (ne_of_gt ht0)]
    rw [hlhs, hsub, hRt]
    have hker : ∀ x ∈ Ioi a, burnolShiftKernel ρ (x / t) * F x =
        ((t : ℂ) ^ ρ) * (F x * ((x : ℂ) ^ (-ρ))) := by
      intro x hx
      have hx0 : 0 < x := lt_trans ha hx
      have htpow : ((((t : ℝ)) : ℂ) ^ (-ρ))⁻¹ = (((t : ℝ)) : ℂ) ^ ρ := by
        rw [Complex.cpow_neg, inv_inv]
      rw [burnolShiftKernel_eq_cpow (div_pos hx0 ht0), ofReal_div_cpow hx0 ht0, htpow]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hker, integral_const_mul]
    have htne : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
    have hpow : ((t : ℂ) ^ ρ) = (t : ℂ) * ((t : ℂ) ^ (ρ - 1)) := by
      nth_rewrite 2 [show ((t : ℝ) : ℂ) = ((t : ℝ) : ℂ) ^ (1 : ℂ) from (Complex.cpow_one _).symm]
      rw [← Complex.cpow_add _ _ htne]
      congr 1
      ring
    rw [hpow, real_smul, Complex.ofReal_inv]
    field_simp
  -- tail Mellin mass
  have hunion2 : Ioo (0 : ℝ) a ∪ Ici a = Ioi (0 : ℝ) := Ioo_union_Ici_eq_Ioi ha
  have hdisj2 : Disjoint (Ioo (0 : ℝ) a) (Ici a) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx' (not_le.mpr hx.2)
  have hheadmass : (∫ s in Ioo (0 : ℝ) a, F s * ((s : ℂ) ^ (-ρ))) =
      c * (((a : ℝ) : ℂ) ^ ((1 : ℂ) - ρ)) / ((1 : ℂ) - ρ) := by
    have hcongr : (∫ s in Ioo (0 : ℝ) a, F s * ((s : ℂ) ^ (-ρ))) =
        ∫ s in Ioo (0 : ℝ) a, ((s : ℂ) ^ (-ρ)) * c := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hc] with s hs hval
      rw [hval hs]
      ring
    rw [hcongr, integral_mul_const, integral_Ioo_ofReal_cpow ha hznegre]
    ring_nf
  have htailmass : (∫ x in Ioi a, F x * ((x : ℂ) ^ (-ρ))) =
      -(c * (((a : ℝ) : ℂ) ^ ((1 : ℂ) - ρ)) / ((1 : ℂ) - ρ)) := by
    have hsum : (∫ s in Ioi (0 : ℝ), F s * ((s : ℂ) ^ (-ρ))) =
        (∫ s in Ioo (0 : ℝ) a, F s * ((s : ℂ) ^ (-ρ))) +
          ∫ s in Ici a, F s * ((s : ℂ) ^ (-ρ)) := by
      rw [← hunion2]
      exact setIntegral_union hdisj2 measurableSet_Ici
        (hint.mono_set (by rw [← hunion2]; exact subset_union_left))
        (hint.mono_set (by rw [← hunion2]; exact subset_union_right))
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi] at hsum
    rw [hvanish, hheadmass] at hsum
    linear_combination -hsum
  rw [hsplit, hA, hB, htailmass]
  have hRpow : (((R : ℝ)) : ℂ) ^ ((1 : ℂ) - ρ) =
      (((a : ℝ)) : ℂ) ^ ((1 : ℂ) - ρ) * ((t : ℂ) ^ (ρ - 1)) := by
    rw [hRdef, ofReal_div_cpow ha ht0]
    congr 1
    rw [← Complex.cpow_neg]
    congr 1
    ring
  rw [hRpow]
  field_simp
  ring

/-! ## Pointwise form and head law of the reflected divided shift -/

/-- Globally measurable form of the reflected divided-shift kernel. -/
def burnolCoShiftKernel (ρ : ℂ) (u : ℝ) : ℂ := Complex.exp ((Real.log u : ℂ) * (ρ - 1))

theorem burnolCoShiftKernel_eq_cpow {u : ℝ} (hu : 0 < u) (ρ : ℂ) :
    burnolCoShiftKernel ρ u = (u : ℂ) ^ (ρ - 1) := by
  rw [burnolCoShiftKernel, Complex.cpow_def_of_ne_zero
    (by exact_mod_cast ne_of_gt hu : ((u : ℝ) : ℂ) ≠ 0), ← Complex.ofReal_log hu.le]

theorem norm_burnolCoShiftKernel {u : ℝ} (hu : 0 < u) (ρ : ℂ) :
    ‖burnolCoShiftKernel ρ u‖ = u ^ (ρ.re - 1) := by
  rw [burnolCoShiftKernel_eq_cpow hu, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.sub_re]
  norm_num

theorem measurable_burnolCoShiftKernel (ρ : ℂ) : Measurable (burnolCoShiftKernel ρ) := by
  apply Complex.measurable_exp.comp
  exact (Complex.measurable_ofReal.comp Real.measurable_log).mul measurable_const

theorem burnolCoShiftKernel_mul_sqrt {u : ℝ} (hu : 0 < u) (ρ : ℂ) :
    burnolCoShiftWeight ρ u * (Real.sqrt u : ℂ) = burnolCoShiftKernel ρ u := by
  rw [burnolCoShiftKernel_eq_cpow hu, burnolCoShiftWeight]
  have hune : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
  have hsq : ((Real.sqrt u : ℝ) : ℂ) = ((u : ℝ) : ℂ) ^ ((1 : ℂ) / 2) := by
    rw [show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hu.le]
    norm_cast
    exact Real.sqrt_eq_rpow u
  rw [hsq, ← Complex.cpow_add _ _ hune]
  congr 1
  ring

/-- The pointwise reflected divided shift of a function on the line. -/
def burnolCoShiftFun (ρ : ℂ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ u in Ioo (0 : ℝ) 1, burnolCoShiftKernel ρ u * F (u * t)

theorem stronglyMeasurable_burnolCoShiftIntegrand (ρ : ℂ) {F : ℝ → ℂ}
    (hF : StronglyMeasurable F) :
    StronglyMeasurable (fun p : ℝ × ℝ => burnolCoShiftKernel ρ p.2 * F (p.2 * p.1)) := by
  refine StronglyMeasurable.mul ?_ ?_
  · exact ((measurable_burnolCoShiftKernel ρ).comp measurable_snd).stronglyMeasurable
  · exact hF.comp_measurable (measurable_snd.mul measurable_fst)

theorem stronglyMeasurable_burnolCoShiftIntegrand_swap (ρ : ℂ) {F : ℝ → ℂ}
    (hF : StronglyMeasurable F) :
    StronglyMeasurable (fun q : ℝ × ℝ => burnolCoShiftKernel ρ q.1 * F (q.1 * q.2)) := by
  refine StronglyMeasurable.mul ?_ ?_
  · exact ((measurable_burnolCoShiftKernel ρ).comp measurable_fst).stronglyMeasurable
  · exact hF.comp_measurable (measurable_fst.mul measurable_snd)

/-- Product integrability of the reflected divided-shift integrand over a finite-measure slab. -/
theorem integrable_burnolCoShiftIntegrand_prod {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (f : evenSubspace)
    {s : Set ℝ} (hs : MeasurableSet s) (hsfin : volume s ≠ ⊤) :
    Integrable (fun p : ℝ × ℝ => burnolCoShiftKernel ρ p.2 *
        (((f : evenSubspace) : SoninL2) : ℝ → ℂ) (p.2 * p.1))
      ((volume.restrict s).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  set F : ℝ → ℂ := (((f : evenSubspace) : SoninL2) : ℝ → ℂ) with hFdef
  have hFm : StronglyMeasurable F := Lp.stronglyMeasurable _
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => burnolCoShiftKernel ρ p.2 * F (p.2 * p.1))
      ((volume.restrict s).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    (stronglyMeasurable_burnolCoShiftIntegrand ρ hFm).aestronglyMeasurable
  rw [integrable_prod_iff' hmeas]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact (integrableOn_dilate_representative hu.1 f hsfin).const_mul _
  · have hswap : StronglyMeasurable
        (fun q : ℝ × ℝ => ‖burnolCoShiftKernel ρ q.1 * F (q.1 * q.2)‖) :=
      (stronglyMeasurable_burnolCoShiftIntegrand_swap ρ hFm).norm
    have hmeasint : StronglyMeasurable
        (fun u : ℝ => ∫ t in s, ‖burnolCoShiftKernel ρ u * F (u * t)‖) :=
      hswap.integral_prod_right'
    set C : ℝ := (volume.real s + ‖f‖ ^ 2) / 2 with hC
    have hboundint : IntegrableOn (fun u : ℝ => u ^ (ρ.re - 3 / 2) * C) (Ioo (0 : ℝ) 1) volume := by
      apply Integrable.mul_const
      have hint : IntervalIntegrable (fun u : ℝ => u ^ (ρ.re - 3 / 2)) volume 0 1 :=
        intervalIntegral.intervalIntegrable_rpow' (by linarith)
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hint
      exact hint
    refine Integrable.mono' hboundint hmeasint.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hu0 : 0 < u := hu.1
    have hnn : 0 ≤ ∫ t in s, ‖burnolCoShiftKernel ρ u * F (u * t)‖ :=
      setIntegral_nonneg hs fun t _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hpull : (∫ t in s, ‖burnolCoShiftKernel ρ u * F (u * t)‖) =
        u ^ (ρ.re - 1) * ∫ t in s, ‖F (u * t)‖ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun hs
      intro t _
      dsimp only
      rw [norm_mul, norm_burnolCoShiftKernel hu0]
    rw [hpull]
    have hkey := setIntegral_norm_dilate_le hu0 f hs hsfin
    have hupos : (0:ℝ) < u ^ (ρ.re - 1) := Real.rpow_pos_of_pos hu0 _
    have hsplit : u ^ (ρ.re - 3 / 2) = u ^ (ρ.re - 1) * u ^ (-(1:ℝ)/2) := by
      rw [← Real.rpow_add hu0]
      congr 1
      ring
    rw [hsplit, mul_assoc]
    exact mul_le_mul_of_nonneg_left hkey hupos.le

theorem integrableOn_burnolCoShiftFun {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (f : evenSubspace)
    {s : Set ℝ} (hs : MeasurableSet s) (hsfin : volume s ≠ ⊤) :
    IntegrableOn (burnolCoShiftFun ρ (((f : evenSubspace) : SoninL2) : ℝ → ℂ)) s volume :=
  (integrable_burnolCoShiftIntegrand_prod hρ f hs hsfin).integral_prod_left

theorem setIntegral_burnolCoShift {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (f : evenSubspace)
    {s : Set ℝ} (hs : MeasurableSet s) (hsfin : volume s ≠ ⊤) :
    (∫ t in s, (((burnolCoShift ρ f : evenSubspace) : SoninL2) : ℝ → ℂ) t) =
      ∫ t in s, burnolCoShiftFun ρ (((f : evenSubspace) : SoninL2) : ℝ → ℂ) t := by
  set F : ℝ → ℂ := (((f : evenSubspace) : SoninL2) : ℝ → ℂ) with hFdef
  rw [← inner_evenIndicatorTest hs hsfin (burnolCoShift ρ f),
    inner_burnolCoShift hρ (evenIndicatorTest hs hsfin) f]
  have hstep : ∀ u ∈ Ioo (0 : ℝ) 1,
      burnolCoShiftWeight ρ u * ⟪evenIndicatorTest hs hsfin, evenRayDilate u f⟫_ℂ =
        ∫ t in s, burnolCoShiftKernel ρ u * F (u * t) := by
    intro u hu
    have hu0 : 0 < u := hu.1
    rw [inner_evenIndicatorTest hs hsfin (evenRayDilate u f)]
    have hcongr : (∫ t in s, (((evenRayDilate u f : evenSubspace) : SoninL2) : ℝ → ℂ) t) =
        ∫ t in s, (Real.sqrt u : ℂ) * F (u * t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (evenRayDilate_ae hu0 f)] with t ht
      rw [ht]
    rw [hcongr, ← integral_const_mul]
    apply setIntegral_congr_fun hs
    intro t _
    dsimp only
    rw [← mul_assoc, burnolCoShiftKernel_mul_sqrt hu0]
  rw [setIntegral_congr_fun measurableSet_Ioo hstep]
  exact (integral_integral_swap
    (integrable_burnolCoShiftIntegrand_prod hρ f hs hsfin)).symm

/-- **The reflected divided shift is the pointwise reflected divided-shift integral.** -/
theorem coe_burnolCoShift_ae {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (f : evenSubspace) :
    (((burnolCoShift ρ f : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      burnolCoShiftFun ρ (((f : evenSubspace) : SoninL2) : ℝ → ℂ) := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
  · intro s hs hsfin
    haveI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hsfin.ne
    exact ((Lp.memLp ((burnolCoShift ρ f : evenSubspace) : SoninL2)).restrict s).integrable
      (by norm_num)
  · intro s hs hsfin
    exact integrableOn_burnolCoShiftFun hρ f hs hsfin.ne
  · intro s hs hsfin
    exact setIntegral_burnolCoShift hρ f hs hsfin.ne

/-- **Head law for the reflected divided shift.**  It is unconditional. -/
theorem burnolCoShiftFun_head_eq {ρ : ℂ} (hρ : 1 / 2 < ρ.re)
    {a : ℝ} (_haha : 0 < a) (f : evenSubspace) {c : ℂ}
    (hc : ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) a → (((f : evenSubspace) : SoninL2) : ℝ → ℂ) s = c)
    {t : ℝ} (ht0 : 0 < t) (hta : t < a) :
    burnolCoShiftFun ρ (((f : evenSubspace) : SoninL2) : ℝ → ℂ) t = c / ρ := by
  set F : ℝ → ℂ := (((f : evenSubspace) : SoninL2) : ℝ → ℂ) with hFdef
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h] at hρ
    norm_num at hρ
  have hzre : (-1 : ℝ) < (ρ - 1).re := by
    rw [Complex.sub_re]
    norm_num
    linarith
  have hcshift : ∀ᵐ u ∂volume, t * u ∈ Ioo (0 : ℝ) a → F (t * u) = c :=
    ((realMul_quasiMeasurePreserving t ht0.ne').tendsto_ae).eventually hc
  have hcongr : burnolCoShiftFun ρ F t = ∫ u in Ioo (0 : ℝ) 1, ((u : ℂ) ^ (ρ - 1)) * c := by
    rw [burnolCoShiftFun]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae hcshift] with u hu hval
    have hu0 : 0 < u := hu.1
    have hmem : t * u ∈ Ioo (0 : ℝ) a := by
      constructor
      · positivity
      · calc t * u < t * 1 := by exact mul_lt_mul_of_pos_left hu.2 ht0
          _ = t := mul_one t
          _ < a := hta
    rw [burnolCoShiftKernel_eq_cpow hu0, mul_comm u t, hval hmem]
  rw [hcongr, integral_mul_const, integral_Ioo_ofReal_cpow one_pos hzre]
  rw [Complex.ofReal_one, Complex.one_cpow]
  rw [show ρ - 1 + 1 = ρ by ring]
  ring

/-! ## Invariance of the extended Sonine space -/

/-- **The forward divided shift preserves the extended Sonine space at an annihilated point.** -/
theorem burnolShift_mem_soninExtendedSpace {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1)
    {a : ℝ} (ha : 0 < a) {g : evenSubspace} (hg : g ∈ soninExtendedSpace a)
    (hvanish : (∫ s in Ioi (0 : ℝ),
      (((g : evenSubspace) : SoninL2) : ℝ → ℂ) s * soninMellinKernel ρ s) = 0) :
    burnolShift ρ g ∈ soninExtendedSpace a := by
  obtain ⟨hhead, hcoshead⟩ := mem_soninExtendedSpace.mp hg
  obtain ⟨c, hc⟩ := hhead
  obtain ⟨d, hd⟩ := hcoshead
  have hcae : ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) a →
      (((g : evenSubspace) : SoninL2) : ℝ → ℂ) s = c := by
    rw [← ae_restrict_iff' measurableSet_Ioo]
    exact hc
  have hdae : ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) a →
      (((soninCosineUnitary g : evenSubspace) : SoninL2) : ℝ → ℂ) s = d := by
    rw [← ae_restrict_iff' measurableSet_Ioo]
    exact hd
  have hint : IntegrableOn (fun s : ℝ =>
      (((g : evenSubspace) : SoninL2) : ℝ → ℂ) s * ((s : ℂ) ^ (-ρ))) (Ioi (0 : ℝ)) volume :=
    integrableOn_extendedSonin_mul_mellinKernel hρ hρ1 ha ⟨g, hg⟩
  refine mem_soninExtendedSpace.mpr ⟨⟨-c / (1 - ρ), ?_⟩, ⟨d / ρ, ?_⟩⟩
  · filter_upwards [ae_restrict_of_ae (coe_burnolShift_ae hρ g),
      ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [ht]
    exact burnolShiftFun_head_eq hρ hρ1 ha g hcae hint hvanish hmem.1 hmem.2
  · rw [soninCosineUnitary_burnolShift hρ]
    filter_upwards [ae_restrict_of_ae (coe_burnolCoShift_ae hρ (soninCosineUnitary g)),
      ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [ht]
    exact burnolCoShiftFun_head_eq hρ ha (soninCosineUnitary g) hdae hmem.1 hmem.2

/-! ## The Mellin multiplier -/

theorem dilate_mellinKernel {u t : ℝ} (hu : 0 < u) (ht : 0 < t) (v : ℂ) :
    soninMellinKernel v t = ((u : ℂ) ^ v) * soninMellinKernel v (u * t) := by
  have hune : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
  have htne : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  rw [soninMellinKernel, soninMellinKernel, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hu.le ht.le, ← mul_assoc]
  rw [show ((u : ℝ) : ℂ) ^ v * (((u : ℝ) : ℂ) ^ (-v)) = 1 by
    rw [← Complex.cpow_add _ _ hune]; norm_num]
  rw [one_mul]

theorem integrableOn_dilate_mellinKernel {u : ℝ} (hu : 0 < u) {v : ℂ} {F : ℝ → ℂ}
    (hF : IntegrableOn (fun s : ℝ => F s * soninMellinKernel v s) (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun t : ℝ => F (u * t) * soninMellinKernel v t) (Ioi (0 : ℝ)) volume := by
  have hcomp : IntegrableOn
      (fun t : ℝ => F (u * t) * soninMellinKernel v (u * t)) (Ioi (0 : ℝ)) volume := by
    have hkey := (integrableOn_Ioi_comp_mul_left_iff
      (fun s : ℝ => F s * soninMellinKernel v s) 0 hu).mpr (by rwa [mul_zero])
    exact hkey
  have := hcomp.const_mul ((u : ℂ) ^ v)
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mpr this
  intro t ht
  have ht0 : 0 < t := ht
  dsimp only
  rw [dilate_mellinKernel hu ht0 v]
  ring

theorem integral_dilate_mellinKernel {u : ℝ} (hu : 0 < u) {v : ℂ} {F : ℝ → ℂ} :
    (∫ t in Ioi (0 : ℝ), F (u * t) * soninMellinKernel v t) =
      ((u : ℂ) ^ (v - 1)) * ∫ x in Ioi (0 : ℝ), F x * soninMellinKernel v x := by
  have hcongr : (∫ t in Ioi (0 : ℝ), F (u * t) * soninMellinKernel v t) =
      ∫ t in Ioi (0 : ℝ), ((u : ℂ) ^ v) *
        ((fun s : ℝ => F s * soninMellinKernel v s) (u * t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    dsimp only
    rw [dilate_mellinKernel hu ht0 v]
    ring
  rw [hcongr, integral_const_mul,
    integral_comp_mul_left_Ioi (fun s : ℝ => F s * soninMellinKernel v s) 0 hu, mul_zero]
  have hune : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
  have hpow : ((u : ℂ) ^ v) = (u : ℂ) * ((u : ℂ) ^ (v - 1)) := by
    nth_rewrite 2 [show ((u : ℝ) : ℂ) = ((u : ℝ) : ℂ) ^ (1 : ℂ) from (Complex.cpow_one _).symm]
    rw [← Complex.cpow_add _ _ hune]
    congr 1
    ring
  rw [hpow, real_smul, Complex.ofReal_inv]
  field_simp

theorem burnolShiftKernel_eq_mellinKernel {t : ℝ} (ht : 0 < t) (v : ℂ) :
    burnolShiftKernel v t = soninMellinKernel v t := by
  rw [burnolShiftKernel_eq_cpow ht, soninMellinKernel]

/-- **Mellin multiplier of the forward divided shift.**  On the strip strictly to the left of
`Re ρ` the divided shift multiplies the uncompleted Mellin transform by `1/(ρ - v)`. -/
theorem integral_burnolShiftFun_mellinKernel {ρ v : ℂ} (_hρhρ : 1 / 2 < ρ.re)
    (hvlo : 1 / 2 < v.re) (hvhi : v.re < 1) (hvρ : v.re < ρ.re)
    {a : ℝ} (ha : 0 < a) {g : evenSubspace} (hg : g ∈ soninExtendedSpace a) :
    (∫ t in Ioi (0 : ℝ),
        burnolShiftFun ρ (((g : evenSubspace) : SoninL2) : ℝ → ℂ) t * soninMellinKernel v t) =
      (∫ t in Ioi (0 : ℝ),
        (((g : evenSubspace) : SoninL2) : ℝ → ℂ) t * soninMellinKernel v t) / (ρ - v) := by
  set F : ℝ → ℂ := (((g : evenSubspace) : SoninL2) : ℝ → ℂ) with hFdef
  have hFm : StronglyMeasurable F := Lp.stronglyMeasurable _
  have hintv : IntegrableOn (fun s : ℝ => F s * soninMellinKernel v s) (Ioi (0 : ℝ)) volume :=
    integrableOn_extendedSonin_mul_mellinKernel hvlo hvhi ha ⟨g, hg⟩
  set Φ : ℝ → ℝ := fun s : ℝ => ‖F s * soninMellinKernel v s‖ with hΦ
  set C : ℝ := ∫ s in Ioi (0 : ℝ), Φ s with hCdef
  have hΦint : IntegrableOn Φ (Ioi (0 : ℝ)) volume := hintv.norm
  -- product integrability
  have hprodmeas : StronglyMeasurable
      (fun p : ℝ × ℝ => (burnolShiftKernel ρ p.2 * F (p.2 * p.1)) * burnolShiftKernel v p.1) :=
    (stronglyMeasurable_burnolShiftIntegrand ρ hFm).mul
      ((measurable_burnolShiftKernel v).comp measurable_fst).stronglyMeasurable
  have hprod : Integrable
      (fun p : ℝ × ℝ => (burnolShiftKernel ρ p.2 * F (p.2 * p.1)) * burnolShiftKernel v p.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (1 : ℝ)))) := by
    rw [integrable_prod_iff' hprodmeas.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := lt_trans zero_lt_one hu
      have hbase := integrableOn_dilate_mellinKernel hu0 (v := v) (F := F) hintv
      have hconst := hbase.const_mul (burnolShiftKernel ρ u)
      refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mpr hconst
      intro t ht
      have ht0 : 0 < t := ht
      dsimp only
      rw [burnolShiftKernel_eq_mellinKernel ht0 v]
      ring
    · have hswap : StronglyMeasurable
          (fun q : ℝ × ℝ =>
            ‖(burnolShiftKernel ρ q.1 * F (q.1 * q.2)) * burnolShiftKernel v q.2‖) :=
        ((stronglyMeasurable_burnolShiftIntegrand_swap ρ hFm).mul
          ((measurable_burnolShiftKernel v).comp measurable_snd).stronglyMeasurable).norm
      have hmeasint : StronglyMeasurable (fun u : ℝ => ∫ t in Ioi (0 : ℝ),
          ‖(burnolShiftKernel ρ u * F (u * t)) * burnolShiftKernel v t‖) :=
        hswap.integral_prod_right'
      have hboundint : IntegrableOn
          (fun u : ℝ => u ^ (-ρ.re + (v.re - 1)) * C) (Ioi (1 : ℝ)) volume := by
        apply Integrable.mul_const
        exact (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by linarith)
      refine Integrable.mono' hboundint hmeasint.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := lt_trans zero_lt_one hu
      have hnn : 0 ≤ ∫ t in Ioi (0 : ℝ),
          ‖(burnolShiftKernel ρ u * F (u * t)) * burnolShiftKernel v t‖ :=
        setIntegral_nonneg measurableSet_Ioi fun t _ => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hpull : (∫ t in Ioi (0 : ℝ),
            ‖(burnolShiftKernel ρ u * F (u * t)) * burnolShiftKernel v t‖) =
          u ^ (-ρ.re) * (u ^ (v.re) * (u⁻¹ * C)) := by
        have hstep : ∀ t ∈ Ioi (0 : ℝ),
            ‖(burnolShiftKernel ρ u * F (u * t)) * burnolShiftKernel v t‖ =
              u ^ (-ρ.re) * (u ^ (v.re) * Φ (u * t)) := by
          intro t ht
          have ht0 : 0 < t := ht
          rw [norm_mul, norm_mul, norm_burnolShiftKernel hu0,
            burnolShiftKernel_eq_mellinKernel ht0 v,
            dilate_mellinKernel hu0 ht0 v, hΦ]
          dsimp only
          rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
          ring
        rw [setIntegral_congr_fun measurableSet_Ioi hstep, integral_const_mul,
          integral_const_mul, hCdef,
          integral_comp_mul_left_Ioi Φ 0 hu0, mul_zero, smul_eq_mul]
      rw [hpull]
      have hcomb : u ^ (-ρ.re) * (u ^ v.re * u⁻¹) = u ^ (-ρ.re + (v.re - 1)) := by
        rw [show u⁻¹ = u ^ (-1 : ℝ) by rw [Real.rpow_neg_one], ← Real.rpow_add hu0,
          ← Real.rpow_add hu0, show -ρ.re + (v.re + -1) = -ρ.re + (v.re - 1) by ring]
      have heq : u ^ (-ρ.re) * (u ^ v.re * (u⁻¹ * C)) = u ^ (-ρ.re + (v.re - 1)) * C := by
        rw [← hcomb]
        ring
      rw [heq]
  -- swap and evaluate
  have hlhs : (∫ t in Ioi (0 : ℝ), burnolShiftFun ρ F t * soninMellinKernel v t) =
      ∫ t in Ioi (0 : ℝ), ∫ u in Ioi (1 : ℝ),
        (burnolShiftKernel ρ u * F (u * t)) * burnolShiftKernel v t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    dsimp only
    rw [burnolShiftFun, ← integral_mul_const, burnolShiftKernel_eq_mellinKernel ht0 v]
  rw [hlhs, integral_integral_swap hprod]
  have hinner : ∀ u ∈ Ioi (1 : ℝ),
      (∫ t in Ioi (0 : ℝ), (burnolShiftKernel ρ u * F (u * t)) * burnolShiftKernel v t) =
        burnolShiftKernel ρ u * ((u : ℂ) ^ (v - 1)) *
          ∫ x in Ioi (0 : ℝ), F x * soninMellinKernel v x := by
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    have hcongr : (∫ t in Ioi (0 : ℝ),
          (burnolShiftKernel ρ u * F (u * t)) * burnolShiftKernel v t) =
        burnolShiftKernel ρ u * ∫ t in Ioi (0 : ℝ), F (u * t) * soninMellinKernel v t := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      dsimp only
      rw [burnolShiftKernel_eq_mellinKernel ht0 v]
      ring
    rw [hcongr, integral_dilate_mellinKernel hu0, ← mul_assoc]
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_mul_const]
  have hchar : ∀ u ∈ Ioi (1 : ℝ),
      burnolShiftKernel ρ u * ((u : ℂ) ^ (v - 1)) = (u : ℂ) ^ (v - ρ - 1) := by
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    have hune : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu0
    rw [burnolShiftKernel_eq_cpow hu0, ← Complex.cpow_add _ _ hune]
    congr 1
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hchar]
  have hlt : (v - ρ - 1).re < -1 := by
    rw [Complex.sub_re, Complex.sub_re]
    norm_num
    linarith
  rw [integral_Ioi_cpow_of_lt hlt zero_lt_one, Complex.ofReal_one, Complex.one_cpow]
  have hne : ρ - v ≠ 0 := by
    intro h
    have : v = ρ := by linear_combination -h
    rw [this] at hvρ
    linarith
  rw [show v - ρ - 1 + 1 = -(ρ - v) by ring]
  field_simp

end RHTower
