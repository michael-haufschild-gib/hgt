import GaloisForLFunctions.RHTower.SoninDilationContinuity
import GaloisForLFunctions.RHTower.BurnolSoninProjectedEvaluationTransport

/-!
# The divided-shift operators of the extended Sonine space

For a point `ρ` of the open right half of the critical strip the two operators

```text
(A_ρ f)(t) = ∫_1^∞ u^(-ρ) f(u t) du,     (C_ρ f)(t) = ∫_0^1 u^(ρ-1) f(u t) du
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

end RHTower
