import GaloisForLFunctions.HTGeometry.HillEventContinuity

/-!
# The second-order chart calculus of the evolution

Each first partial of the chart field is again a synthesis: the time partial synthesises the velocity
density against the character, a spatial partial synthesises the density against the character times
the frequency factor. Differentiating them once more produces the four second-order objects — the
second time derivative, the two mixed derivatives, which coincide because differentiating in time and
multiplying by the frequency commute, and the mixed spatial derivatives.

All of them are dominated by two powers of the frequency against the initial density, so a single
integrability hypothesis carries the whole calculus, and the first partials are differentiable — the
hypothesis of the divergence-form d'Alembertian.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped RealInnerProductSpace

section DirChar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The multiplier of a spatial derivative: the character times the frequency factor. -/
noncomputable def kgDirChar (v x ξ : E) : ℂ :=
  kgChar x ξ * (2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_kgDirChar_le (v x ξ : E) : ‖kgDirChar v x ξ‖ ≤ 2 * Real.pi * ‖v‖ * kgFreq ξ := by
  rw [kgDirChar, norm_mul, norm_kgChar, one_mul, norm_two_pi_I_inner]
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  calc 2 * Real.pi * |(⟪ξ, v⟫ : ℝ)| ≤ 2 * Real.pi * (‖v‖ * kgFreq ξ) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_kgFreq v ξ) hpi
    _ = 2 * Real.pi * ‖v‖ * kgFreq ξ := by ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_kgDirChar (v x : E) : Continuous (kgDirChar v x) := by
  have hinner : Continuous fun ξ : E => ((⟪ξ, v⟫ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_inner.comp (continuous_id.prodMk continuous_const))
  exact (continuous_kgChar' x).mul (continuous_const.mul hinner)

/-- The synthesis against the derivative multiplier is the synthesis of the derived density. -/
theorem hillSynthesis_kgDirChar (m : ℝ) (c : ℝ → ℝ) (G₀ : E → ℂ) (v x : E) (t : ℝ) :
    hillSynthesis m c G₀ (kgDirChar v x) (volume : Measure E) t
      = kgSynthesis (kgDirDensity v (hillDensity m c G₀ t)) x := by
  rw [hillSynthesis, kgSynthesis]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show kgDirChar v x ξ * hillDensity m c G₀ t ξ
    = kgChar x ξ * kgDirDensity v (hillDensity m c G₀ t) ξ
  rw [kgDirChar, kgDirDensity]
  ring

/-- The velocity synthesis against the derivative multiplier is the synthesis of the derived velocity
density. -/
theorem hillSynthesisDeriv_kgDirChar (m : ℝ) (c : ℝ → ℝ) (G₀ : E → ℂ) (v x : E) (t : ℝ) :
    hillSynthesisDeriv m c G₀ (kgDirChar v x) (volume : Measure E) t
      = kgSynthesis (kgDirDensity v (hillDensityDeriv m c G₀ t)) x := by
  rw [hillSynthesisDeriv, kgSynthesis]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show kgDirChar v x ξ * hillDensityDeriv m c G₀ t ξ
    = kgChar x ξ * kgDirDensity v (hillDensityDeriv m c G₀ t) ξ
  rw [kgDirChar, kgDirDensity]
  ring

end DirChar

section ChartSecond

variable {d : ℕ} {m K C cmin : ℝ} {c dc : ℝ → ℝ} {G : EuclideanSpace ℝ (Fin d) → ℂ}

/-! ## The second-order families -/

/-- The partials of the time partial. -/
noncomputable def hillChartTimeSecond (m : ℝ) (c : ℝ → ℝ) (G : EuclideanSpace ℝ (Fin d) → ℂ)
    (k : Fin (d + 1)) : (Fin (d + 1) → ℝ) → ℝ :=
  Fin.cases (fun y => (hillSynthesisSecond m c G (kgChar (kgSpatial d y)) (volume) (y 0)).re)
    (fun i y => (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
      (hillDensityDeriv m c G (y 0))) (kgSpatial d y)).re) k

/-- The partials of the `i`-th spatial partial. -/
noncomputable def hillChartSpaceSecond (m : ℝ) (c : ℝ → ℝ) (G : EuclideanSpace ℝ (Fin d) → ℂ)
    (i : Fin d) (k : Fin (d + 1)) : (Fin (d + 1) → ℝ) → ℝ :=
  Fin.cases (fun y => (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
      (hillDensityDeriv m c G (y 0))) (kgSpatial d y)).re)
    (fun j y => (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d j)
      (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (hillDensity m c G (y 0))))
        (kgSpatial d y)).re) k

theorem hillChartTimeSecond_zero (m : ℝ) (c : ℝ → ℝ) (G : EuclideanSpace ℝ (Fin d) → ℂ) :
    hillChartTimeSecond m c G 0
      = fun y => (hillSynthesisSecond m c G (kgChar (kgSpatial d y)) (volume) (y 0)).re := rfl

theorem hillChartTimeSecond_succ (m : ℝ) (c : ℝ → ℝ) (G : EuclideanSpace ℝ (Fin d) → ℂ)
    (i : Fin d) :
    hillChartTimeSecond m c G i.succ
      = fun y => (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
          (hillDensityDeriv m c G (y 0))) (kgSpatial d y)).re := by
  rw [hillChartTimeSecond, Fin.cases_succ]

theorem hillChartSpaceSecond_zero (m : ℝ) (c : ℝ → ℝ) (G : EuclideanSpace ℝ (Fin d) → ℂ)
    (i : Fin d) :
    hillChartSpaceSecond m c G i 0
      = fun y => (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
          (hillDensityDeriv m c G (y 0))) (kgSpatial d y)).re := rfl

theorem hillChartSpaceSecond_succ (m : ℝ) (c : ℝ → ℝ) (G : EuclideanSpace ℝ (Fin d) → ℂ)
    (i j : Fin d) :
    hillChartSpaceSecond m c G i j.succ
      = fun y => (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d j)
          (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (hillDensity m c G (y 0))))
            (kgSpatial d y)).re := by
  rw [hillChartSpaceSecond, Fin.cases_succ]

/-! ## The derivatives of the time partial -/

/-- **The second time derivative of the chart field.** -/
theorem hasDerivAt_hillChartTimePartial_zero (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume))
    (y : Fin (d + 1) → ℝ) :
    HasDerivAt (fun r : ℝ => hillChartTimePartial m c G (Function.update y 0 r))
      (hillChartTimeSecond m c G 0 y) (y 0) := by
  have h1 := integrable_kgFreq_mul_of_sq hG h2
  have hwA := integrable_massWeight (c := c) hm (hcpos 0) hG h1
  have hwB := integrable_massWeightSq (m := m) (C := C) hG h2
  have hwA' : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) =>
      (1 : ℝ) * ((m + c 0 * ‖ξ‖) * ‖G ξ‖)) (volume) :=
    hwA.congr (Filter.Eventually.of_forall fun ξ => (one_mul _).symm)
  have hwB' : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) =>
      (1 : ℝ) * ((m ^ 2 + C ^ 2 * ‖ξ‖ ^ 2) * ‖G ξ‖)) (volume) :=
    hwB.congr (Filter.Eventually.of_forall fun ξ => (one_mul _).symm)
  have hfun : (fun r : ℝ => hillChartTimePartial m c G (Function.update y 0 r))
      = fun r : ℝ => (hillSynthesisDeriv m c G (kgChar (kgSpatial d y)) (volume) r).re := by
    funext r
    rw [hillChartTimePartial, kgSpatial_update_zero, Function.update_self]
  rw [hfun, hillChartTimeSecond_zero]
  have hbase := hasDerivAt_hillSynthesisDeriv_weighted_all (C := C) hm hc hcd hcpos hK hC hcmin
    hclow hG ((continuous_kgChar' (kgSpatial d y)).aestronglyMeasurable)
    (W := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    (fun ξ => le_of_eq (norm_kgChar (kgSpatial d y) ξ)) hwA' hwB' (y 0)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt (y 0) hbase

/-- **The spatial derivative of the time partial.** -/
theorem hasDerivAt_hillChartTimePartial_succ (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume))
    (y : Fin (d + 1) → ℝ) (i : Fin d) :
    HasDerivAt (fun r : ℝ => hillChartTimePartial m c G (Function.update y i.succ r))
      (hillChartTimeSecond m c G i.succ y) (y i.succ) := by
  have h1 := integrable_kgFreq_mul_of_sq hG h2
  have hwA := integrable_massWeight (c := c) hm (hcpos 0) hG h1
  have hwC := integrable_kgFreq_mul_massWeight (c := c) hm (hcpos 0) hG h2
  have hmeas : AEStronglyMeasurable (hillDensityDeriv m c G (y 0))
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    (continuous_hillDensityDeriv_all (C := C) hm hc hC hG (y 0)).aestronglyMeasurable
  have hint := integrable_hillDensityDeriv_all (C := C) hm hc hcd hcpos hK hC hG hwA (y 0)
  have hfreq := integrable_kgFreq_mul_hillDensityDeriv_all (C := C) hm hc hcd hcpos hK hC hG hwC
    (y 0)
  have hfun : (fun r : ℝ => hillChartTimePartial m c G (Function.update y i.succ r))
      = fun r : ℝ => (kgSynthesis (hillDensityDeriv m c G (y 0))
        (kgSpatial d y + (r - y i.succ) • ((2 * Real.pi)⁻¹ • kgDir d i))).re := by
    funext r
    rw [hillChartTimePartial, kgSpatial_update_succ,
      Function.update_of_ne (Fin.succ_ne_zero i).symm]
    rfl
  have hbase : HasDerivAt (fun s : ℝ => (kgSynthesis (hillDensityDeriv m c G (y 0))
      (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • kgDir d i))).re)
      (hillChartTimeSecond m c G i.succ y) 0 := by
    have hcomplex := hasDerivAt_kgSynthesis_dir_synthesis hmeas hint hfreq (kgSpatial d y)
      ((2 * Real.pi)⁻¹ • kgDir d i) 0
    have hzero : kgSpatial d y + (0 : ℝ) • ((2 * Real.pi)⁻¹ • kgDir d i) = kgSpatial d y := by
      rw [zero_smul, add_zero]
    rw [hzero] at hcomplex
    rw [hillChartTimeSecond_succ]
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hcomplex
  have hbase' : HasDerivAt (fun s : ℝ => (kgSynthesis (hillDensityDeriv m c G (y 0))
      (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • kgDir d i))).re)
      (hillChartTimeSecond m c G i.succ y) (y i.succ - y i.succ) := by
    rw [sub_self]
    exact hbase
  have hcomp := HasDerivAt.comp_sub_const (f := fun s : ℝ =>
    (kgSynthesis (hillDensityDeriv m c G (y 0))
      (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • kgDir d i))).re) (y i.succ) (y i.succ) hbase'
  rw [hfun]
  exact hcomp

/-! ## The derivatives of a spatial partial -/

/-- **The time derivative of a spatial partial.** -/
theorem hasDerivAt_hillChartSpacePartial_zero (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume))
    (y : Fin (d + 1) → ℝ) (i : Fin d) :
    HasDerivAt (fun r : ℝ => hillChartSpacePartial m c G i (Function.update y 0 r))
      (hillChartSpaceSecond m c G i 0 y) (y 0) := by
  set v : EuclideanSpace ℝ (Fin d) := (2 * Real.pi)⁻¹ • kgDir d i with hv
  have h1 := integrable_kgFreq_mul_of_sq hG h2
  have hwC := integrable_kgFreq_mul_massWeight (c := c) hm (hcpos 0) hG h2
  have hwD : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) =>
      2 * Real.pi * ‖v‖ * kgFreq ξ * ‖G ξ‖) (volume) := by
    refine (h1.const_mul (2 * Real.pi * ‖v‖)).congr ?_
    filter_upwards with ξ
    ring
  have hwE : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) =>
      2 * Real.pi * ‖v‖ * kgFreq ξ * ((m + c 0 * ‖ξ‖) * ‖G ξ‖)) (volume) := by
    refine (hwC.const_mul (2 * Real.pi * ‖v‖)).congr ?_
    filter_upwards with ξ
    ring
  have hfun : (fun r : ℝ => hillChartSpacePartial m c G i (Function.update y 0 r))
      = fun r : ℝ => (hillSynthesis m c G (kgDirChar v (kgSpatial d y)) (volume) r).re := by
    funext r
    rw [hillChartSpacePartial, kgSpatial_update_zero, Function.update_self,
      hillSynthesis_kgDirChar]
  rw [hfun, hillChartSpaceSecond_zero]
  have hbase := hasDerivAt_hillSynthesis_weighted_all (C := C) hm hc hcd hcpos hK hC hG
    ((continuous_kgDirChar v (kgSpatial d y)).aestronglyMeasurable)
    (W := fun ξ => 2 * Real.pi * ‖v‖ * kgFreq ξ)
    (fun ξ => mul_nonneg (by positivity) (le_of_lt (kgFreq_pos ξ)))
    (fun ξ => norm_kgDirChar_le v (kgSpatial d y) ξ) hwD hwE (y 0)
  rw [hillSynthesisDeriv_kgDirChar] at hbase
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt (y 0) hbase

/-- **The mixed spatial derivatives of a spatial partial.** -/
theorem hasDerivAt_hillChartSpacePartial_succ (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume))
    (y : Fin (d + 1) → ℝ) (i j : Fin d) :
    HasDerivAt (fun r : ℝ => hillChartSpacePartial m c G i (Function.update y j.succ r))
      (hillChartSpaceSecond m c G i j.succ y) (y j.succ) := by
  have h1 := integrable_kgFreq_mul_of_sq hG h2
  have hmeas := aestronglyMeasurable_hillDensity_all (C := C) hm hc hC hG (y 0)
    (volume : Measure (EuclideanSpace ℝ (Fin d)))
  have hw1 := integrable_kgFreq_mul_hillDensity_all (C := C) hm hc hcd hcpos hK hC hG h1 (y 0)
  have hw2 := integrable_kgFreq_sq_mul_hillDensity_all (C := C) hm hc hcd hcpos hK hC hG h2 (y 0)
  have hfun : (fun r : ℝ => hillChartSpacePartial m c G i (Function.update y j.succ r))
      = fun r : ℝ => (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
        (hillDensity m c G (y 0)))
        (kgSpatial d y + (r - y j.succ) • ((2 * Real.pi)⁻¹ • kgDir d j))).re := by
    funext r
    rw [hillChartSpacePartial, kgSpatial_update_succ,
      Function.update_of_ne (Fin.succ_ne_zero j).symm]
  have hbase : HasDerivAt (fun s : ℝ => (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
      (hillDensity m c G (y 0)))
      (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • kgDir d j))).re)
      (hillChartSpaceSecond m c G i j.succ y) 0 := by
    have hcomplex := hasDerivAt_kgSynthesis_dir_dir hmeas hw1 hw2 (kgSpatial d y)
      ((2 * Real.pi)⁻¹ • kgDir d i) ((2 * Real.pi)⁻¹ • kgDir d j) 0
    have hzero : kgSpatial d y + (0 : ℝ) • ((2 * Real.pi)⁻¹ • kgDir d j) = kgSpatial d y := by
      rw [zero_smul, add_zero]
    rw [hzero] at hcomplex
    rw [hillChartSpaceSecond_succ]
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hcomplex
  have hbase' : HasDerivAt (fun s : ℝ => (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
      (hillDensity m c G (y 0)))
      (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • kgDir d j))).re)
      (hillChartSpaceSecond m c G i j.succ y) (y j.succ - y j.succ) := by
    rw [sub_self]
    exact hbase
  have hcomp := HasDerivAt.comp_sub_const (f := fun s : ℝ =>
    (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (hillDensity m c G (y 0)))
      (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • kgDir d j))).re) (y j.succ) (y j.succ) hbase'
  rw [hfun]
  exact hcomp


/-! ## Continuity of the second-order families -/

/-- **The second time derivative is continuous in the event.** -/
theorem continuous_hillChartTimeSecond_zero (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume)) :
    Continuous (hillChartTimeSecond m c G 0) := by
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ |dc 0| := abs_nonneg _
    have h1 := hK 0
    have h3 := hcpos 0
    nlinarith
  have hfun : hillChartTimeSecond m c G 0
      = (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
          (kgSynthesis (hillDensitySecond m c G p.1) p.2).re)
        ∘ (fun y : Fin (d + 1) → ℝ => (y 0, kgSpatial d y)) := by
    funext y
    rfl
  rw [hfun]
  refine (Complex.continuous_re.comp ?_).comp (continuous_chartPoint d)
  refine continuous_kgSynthesis_event
    (fun r => (continuous_hillDensitySecond_all (C := C) hm hc hC hG r).aestronglyMeasurable)
    (fun ξ => continuous_hillDensitySecond_time (C := C) hm hc hC ξ) ?_
    (integrable_massWeightSq (m := m) (C := C) hG h2)
  intro T
  refine ⟨max 1 (c 0 / cmin) * Real.exp (K * T), fun r hr ξ => ?_⟩
  have hratio : max 1 (c 0 / c r) ≤ max 1 (c 0 / cmin) :=
    max_le_max le_rfl (div_le_div_of_nonneg_left (le_of_lt (hcpos 0)) hcmin (hclow r))
  have hexp : Real.exp (K * |r|) ≤ Real.exp (K * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr hK0)
  have hstep : max 1 (c 0 / c r) * Real.exp (K * |r|)
      ≤ max 1 (c 0 / cmin) * Real.exp (K * T) :=
    mul_le_mul hratio hexp (le_of_lt (Real.exp_pos _)) (le_trans zero_le_one (le_max_left _ _))
  have hsq : (0 : ℝ) ≤ m ^ 2 + C ^ 2 * ‖ξ‖ ^ 2 := by positivity
  calc ‖hillDensitySecond m c G r ξ‖
      ≤ ((m ^ 2 + C ^ 2 * ‖ξ‖ ^ 2) * (max 1 (c 0 / c r) * Real.exp (K * |r|))) * ‖G ξ‖ :=
        norm_hillDensitySecond_le_abs hm hc hcd hcpos hK hC r ξ
    _ ≤ ((m ^ 2 + C ^ 2 * ‖ξ‖ ^ 2) * (max 1 (c 0 / cmin) * Real.exp (K * T))) * ‖G ξ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hsq) (norm_nonneg _)
    _ = max 1 (c 0 / cmin) * Real.exp (K * T) * ((m ^ 2 + C ^ 2 * ‖ξ‖ ^ 2) * ‖G ξ‖) := by ring

/-- **The mixed derivative is continuous in the event.** -/
theorem continuous_hillChartMixedSecond (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume))
    (i : Fin d) :
    Continuous fun y : Fin (d + 1) → ℝ =>
      (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
        (hillDensityDeriv m c G (y 0))) (kgSpatial d y)).re := by
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ |dc 0| := abs_nonneg _
    have h1 := hK 0
    have h3 := hcpos 0
    nlinarith
  set v : EuclideanSpace ℝ (Fin d) := (2 * Real.pi)⁻¹ • kgDir d i with hv
  have hfun : (fun y : Fin (d + 1) → ℝ =>
      (kgSynthesis (kgDirDensity v (hillDensityDeriv m c G (y 0))) (kgSpatial d y)).re)
      = (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
          (kgSynthesis (kgDirDensity v (hillDensityDeriv m c G p.1)) p.2).re)
        ∘ (fun y : Fin (d + 1) → ℝ => (y 0, kgSpatial d y)) := by
    funext y
    rfl
  rw [hfun]
  refine (Complex.continuous_re.comp ?_).comp (continuous_chartPoint d)
  refine continuous_kgSynthesis_event
    (fun r => aestronglyMeasurable_kgDirDensity
      (continuous_hillDensityDeriv_all (C := C) hm hc hC hG r).aestronglyMeasurable v)
    (fun ξ => continuous_kgDirDensity_time v ξ
      (continuous_hillDensityDeriv_time (C := C) hm hc hC ξ)) ?_
    (integrable_kgFreq_mul_massWeight (c := c) hm (hcpos 0) hG h2)
  intro T
  refine ⟨2 * Real.pi * ‖v‖ * Real.exp (K * T), fun r hr ξ => ?_⟩
  have hexp : Real.exp (K * |r|) ≤ Real.exp (K * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr hK0)
  have hfreq := massiveFreq_zero_le (c := c) hm hcpos ξ
  have hmf : (0 : ℝ) ≤ massiveFreq m c ‖ξ‖ 0 := le_of_lt (massiveFreq_pos hm c ‖ξ‖ 0)
  have hsum : (0 : ℝ) ≤ m + c 0 * ‖ξ‖ := le_trans hmf hfreq
  have hstep : massiveFreq m c ‖ξ‖ 0 * Real.exp (K * |r|)
      ≤ (m + c 0 * ‖ξ‖) * Real.exp (K * T) :=
    mul_le_mul hfreq hexp (le_of_lt (Real.exp_pos _)) hsum
  have hden : ‖hillDensityDeriv m c G r ξ‖ ≤ ((m + c 0 * ‖ξ‖) * Real.exp (K * T)) * ‖G ξ‖ :=
    (norm_hillDensityDeriv_le_abs hm hc hcd hcpos hK hC r ξ).trans
      (mul_le_mul_of_nonneg_right hstep (norm_nonneg _))
  have hpiv : (0 : ℝ) ≤ 2 * Real.pi * ‖v‖ := by positivity
  calc ‖kgDirDensity v (hillDensityDeriv m c G r) ξ‖
      ≤ 2 * Real.pi * ‖v‖ * (kgFreq ξ * ‖hillDensityDeriv m c G r ξ‖) :=
        norm_kgDirDensity_le v _ ξ
    _ ≤ 2 * Real.pi * ‖v‖ * (kgFreq ξ * (((m + c 0 * ‖ξ‖) * Real.exp (K * T)) * ‖G ξ‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hden (le_of_lt (kgFreq_pos ξ))) hpiv
    _ = 2 * Real.pi * ‖v‖ * Real.exp (K * T) * (kgFreq ξ * ((m + c 0 * ‖ξ‖) * ‖G ξ‖)) := by ring

/-- **The mixed spatial derivatives are continuous in the event.** -/
theorem continuous_hillChartSpaceSecond_succ (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume))
    (i j : Fin d) : Continuous (hillChartSpaceSecond m c G i j.succ) := by
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ |dc 0| := abs_nonneg _
    have h1 := hK 0
    have h3 := hcpos 0
    nlinarith
  set v : EuclideanSpace ℝ (Fin d) := (2 * Real.pi)⁻¹ • kgDir d i with hv
  set w : EuclideanSpace ℝ (Fin d) := (2 * Real.pi)⁻¹ • kgDir d j with hw
  have hfun : hillChartSpaceSecond m c G i j.succ
      = (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
          (kgSynthesis (kgDirDensity w (kgDirDensity v (hillDensity m c G p.1))) p.2).re)
        ∘ (fun y : Fin (d + 1) → ℝ => (y 0, kgSpatial d y)) := by
    rw [hillChartSpaceSecond_succ]
    funext y
    rfl
  rw [hfun]
  refine (Complex.continuous_re.comp ?_).comp (continuous_chartPoint d)
  refine continuous_kgSynthesis_event
    (fun r => aestronglyMeasurable_kgDirDensity (aestronglyMeasurable_kgDirDensity
      (aestronglyMeasurable_hillDensity_all (C := C) hm hc hC hG r _) v) w)
    (fun ξ => continuous_kgDirDensity_time w ξ (continuous_kgDirDensity_time v ξ
      (continuous_hillDensity_time (C := C) hm hc hC ξ))) ?_ h2
  intro T
  refine ⟨2 * Real.pi * ‖w‖ * (2 * Real.pi * ‖v‖) *
    (max 1 (c 0 / cmin) * Real.exp (K * T)), fun r hr ξ => ?_⟩
  have hratio : max 1 (c 0 / c r) ≤ max 1 (c 0 / cmin) :=
    max_le_max le_rfl (div_le_div_of_nonneg_left (le_of_lt (hcpos 0)) hcmin (hclow r))
  have hexp : Real.exp (K * |r|) ≤ Real.exp (K * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr hK0)
  have hstep : max 1 (c 0 / c r) * Real.exp (K * |r|)
      ≤ max 1 (c 0 / cmin) * Real.exp (K * T) :=
    mul_le_mul hratio hexp (le_of_lt (Real.exp_pos _)) (le_trans zero_le_one (le_max_left _ _))
  have hden : ‖hillDensity m c G r ξ‖ ≤ (max 1 (c 0 / cmin) * Real.exp (K * T)) * ‖G ξ‖ :=
    (norm_hillDensity_le_abs hm hc hcd hcpos hK hC r ξ).trans
      (mul_le_mul_of_nonneg_right hstep (norm_nonneg _))
  have hpiv : (0 : ℝ) ≤ 2 * Real.pi * ‖v‖ := by positivity
  have hpiw : (0 : ℝ) ≤ 2 * Real.pi * ‖w‖ := by positivity
  have hfreqnn : (0 : ℝ) ≤ kgFreq ξ := le_of_lt (kgFreq_pos ξ)
  have hinner : ‖kgDirDensity v (hillDensity m c G r) ξ‖
      ≤ 2 * Real.pi * ‖v‖ * (kgFreq ξ * ((max 1 (c 0 / cmin) * Real.exp (K * T)) * ‖G ξ‖)) :=
    (norm_kgDirDensity_le v _ ξ).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden hfreqnn) hpiv)
  calc ‖kgDirDensity w (kgDirDensity v (hillDensity m c G r)) ξ‖
      ≤ 2 * Real.pi * ‖w‖ * (kgFreq ξ * ‖kgDirDensity v (hillDensity m c G r) ξ‖) :=
        norm_kgDirDensity_le w _ ξ
    _ ≤ 2 * Real.pi * ‖w‖ * (kgFreq ξ *
          (2 * Real.pi * ‖v‖ * (kgFreq ξ * ((max 1 (c 0 / cmin) * Real.exp (K * T)) * ‖G ξ‖)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hfreqnn) hpiw
    _ = 2 * Real.pi * ‖w‖ * (2 * Real.pi * ‖v‖) * (max 1 (c 0 / cmin) * Real.exp (K * T)) *
          (kgFreq ξ ^ 2 * ‖G ξ‖) := by ring

/-- **Every partial of the time partial is continuous.** -/
theorem continuous_hillChartTimeSecond (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume))
    (k : Fin (d + 1)) : Continuous (hillChartTimeSecond m c G k) := by
  refine Fin.cases ?_ ?_ k
  · exact continuous_hillChartTimeSecond_zero (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h2
  · intro i
    rw [hillChartTimeSecond_succ]
    exact continuous_hillChartMixedSecond (C := C) hm hc hcd hcpos hK hC hG h2 i

/-- **Every partial of a spatial partial is continuous.** -/
theorem continuous_hillChartSpaceSecond (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume))
    (i : Fin d) (k : Fin (d + 1)) : Continuous (hillChartSpaceSecond m c G i k) := by
  refine Fin.cases ?_ ?_ k
  · rw [hillChartSpaceSecond_zero]
    exact continuous_hillChartMixedSecond (C := C) hm hc hcd hcpos hK hC hG h2 i
  · intro j
    exact continuous_hillChartSpaceSecond_succ (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h2 i j

/-! ## The first partials are differentiable -/

/-- **The time partial has continuous partial derivatives everywhere.** -/
theorem isC1OnPi_hillChartTimePartial (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume)) :
    IsC1OnPi (hillChartTimePartial m c G) (hillChartTimeSecond m c G) Set.univ where
  isOpen := isOpen_univ
  hasDeriv := by
    intro y _ k
    refine Fin.cases ?_ ?_ k
    · exact hasDerivAt_hillChartTimePartial_zero (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h2 y
    · intro i
      exact hasDerivAt_hillChartTimePartial_succ (C := C) hm hc hcd hcpos hK hC hG h2 y i
  cont := fun k =>
    continuous_hillChartTimeSecond (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h2 k

/-- **A spatial partial has continuous partial derivatives everywhere.** -/
theorem isC1OnPi_hillChartSpacePartial (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume))
    (i : Fin d) :
    IsC1OnPi (hillChartSpacePartial m c G i) (hillChartSpaceSecond m c G i) Set.univ where
  isOpen := isOpen_univ
  hasDeriv := by
    intro y _ k
    refine Fin.cases ?_ ?_ k
    · exact hasDerivAt_hillChartSpacePartial_zero (C := C) hm hc hcd hcpos hK hC hG h2 y i
    · intro j
      exact hasDerivAt_hillChartSpacePartial_succ (C := C) hm hc hcd hcpos hK hC hG h2 y i j
  cont := fun k =>
    continuous_hillChartSpaceSecond (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h2 i k

/-- **Every first partial of the chart field is differentiable.** -/
theorem differentiableAt_hillChartPartial (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume))
    (j : Fin (d + 1)) (y : Fin (d + 1) → ℝ) :
    DifferentiableAt ℝ (hillChartPartial m c G j) y := by
  refine Fin.cases ?_ ?_ j
  · rw [hillChartPartial_zero]
    exact (hasFDerivAt_of_isC1OnPi (d + 1) (hillChartTimePartial m c G)
      (hillChartTimeSecond m c G) Set.univ
      (isC1OnPi_hillChartTimePartial (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h2) y
      (Set.mem_univ y)).differentiableAt
  · intro i
    rw [hillChartPartial_succ]
    exact (hasFDerivAt_of_isC1OnPi (d + 1) (hillChartSpacePartial m c G i)
      (hillChartSpaceSecond m c G i) Set.univ
      (isC1OnPi_hillChartSpacePartial (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h2 i) y
      (Set.mem_univ y)).differentiableAt

/-- **Hence every coordinate partial of the chart field is differentiable** — the hypothesis of the
divergence-form d'Alembertian. -/
theorem differentiableAt_coordPartial_hillChartField (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ 2 * ‖G ξ‖) (volume))
    (j : Fin (d + 1)) (y : Fin (d + 1) → ℝ) :
    DifferentiableAt ℝ (coordPartial j (hillChartField m c G)) y := by
  have h1 := integrable_kgFreq_mul_of_sq hG h2
  have h0 := integrable_of_kgFreq_mul hG h1
  have hwA := integrable_massWeight (c := c) hm (hcpos 0) hG h1
  have hfun : coordPartial j (hillChartField m c G) = hillChartPartial m c G j := by
    funext z
    exact coordPartial_hillChartField (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h0 hwA h1 j z
  rw [hfun]
  exact differentiableAt_hillChartPartial (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h2 j y

end ChartSecond

end GaloisForLFunctions.HTGeometry
