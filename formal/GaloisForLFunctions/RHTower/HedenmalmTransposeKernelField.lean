import GaloisForLFunctions.RHTower.HedenmalmQuantileSliceMoment
import GaloisForLFunctions.RHTower.HedenmalmThetaTrace

/-!
# The transposed row of the pinned kernel

The pinned kernel `K(t,u) = i q(t) (1_{u ≤ t} - t)` has rows `t ↦ K(t, ·)` which the corpus already
assembles into an `L²` field.  Its adjoint is the kernel operator of the transposed conjugate
kernel: the row of `B*` at `t` is `u ↦ conj (K(u,t)) = -i q(u) (1_{t ≤ u} - u)`, which carries the
quantile speed inside the vector rather than as an outside scalar.

Those rows are square integrable, which is what makes the adjoint a kernel operator.  The slice
bound `|1_{t ≤ u} - u| ≤ u(1-u) / min t (1-t)` of the slice-moment layer converts the transposed row
energy into the finite kernel energy `q² u(1-u)`.

* `transposeKernelFun` — the transposed row.
* `memLp_transposeKernelFun` — it is square integrable for every interior parameter.
* `transposeKernelVec` — the row as an `L²` vector.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmHilbertSchmidt

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- The transposed row of the pinned kernel at the parameter `t`:
`u ↦ conj (K(u,t)) = -i q(u) (1_{t ≤ u} - u)`. -/
def transposeKernelFun (S : PositiveDensitySource) (t u : ℝ) : ℂ :=
  -(Complex.I * ((quantileSpeed S u : ℝ) : ℂ)) * ((pinnedKernelSlice u t : ℝ) : ℂ)

theorem transposeKernelFun_eq_conj (S : PositiveDensitySource) (t u : ℝ) :
    transposeKernelFun S t u = (starRingEnd ℂ) (pinnedKernelFun S u t) := by
  rw [transposeKernelFun, pinnedKernelFun]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem norm_transposeKernelFun (S : PositiveDensitySource) (t u : ℝ) :
    ‖transposeKernelFun S t u‖ = quantileSpeed S u * |pinnedKernelSlice u t| := by
  rw [transposeKernelFun, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (quantileSpeed_pos S u)]

theorem measurable_transposeKernelFun (S : PositiveDensitySource) (t : ℝ) :
    Measurable (transposeKernelFun S t) := by
  have hmq : Measurable (quantileSpeed S) :=
    measurable_const.div (S.continuous_k.measurable.comp S.measurable_quantileFun)
  have hind : Measurable (fun u : ℝ => (if t ≤ u then (1 : ℝ) else 0)) := by
    have h : Measurable (fun u : ℝ => (Set.Ici t).indicator (fun _ => (1 : ℝ)) u) :=
      measurable_const.indicator measurableSet_Ici
    have hfun : (fun u : ℝ => (Set.Ici t).indicator (fun _ => (1 : ℝ)) u)
        = fun u : ℝ => (if t ≤ u then (1 : ℝ) else 0) := by
      funext u; simp [Set.indicator_apply]
    rwa [hfun] at h
  have hslice : Measurable (fun u : ℝ => pinnedKernelSlice u t) := hind.sub measurable_id
  exact ((measurable_const.mul (Complex.measurable_ofReal.comp hmq)).neg).mul
    (Complex.measurable_ofReal.comp hslice)

/-- **The transposed row has finite energy.**  The slice weight bound turns its energy into the
finite kernel energy. -/
theorem memLp_transposeKernelFun (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    MemLp (transposeKernelFun S t) 2 unitIntervalMeasure := by
  have hm : 0 < min t (1 - t) := lt_min ht.1 (by linarith [ht.2])
  have hmsq : (0 : ℝ) < min t (1 - t) ^ 2 := by positivity
  refine (memLp_two_iff_integrable_sq_norm
    (measurable_transposeKernelFun S t).aestronglyMeasurable).mpr ?_
  refine Integrable.mono' (hfin.const_mul (1 / (4 * min t (1 - t) ^ 2))) ?_ ?_
  · exact ((measurable_transposeKernelFun S t).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with u hu
    have hq : 0 < quantileSpeed S u := quantileSpeed_pos S u
    have hw : 0 ≤ u * (1 - u) := by nlinarith [hu.1, hu.2]
    have hslice := abs_pinnedKernelSlice_le_weight ht hu
    have h1 : |pinnedKernelSlice u t| ^ 2 ≤ (u * (1 - u)) ^ 2 / min t (1 - t) ^ 2 := by
      rw [← div_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hslice 2
    have h3 : (u * (1 - u)) ^ 2 ≤ 1 / 4 * (u * (1 - u)) := by
      nlinarith [sq_nonneg (u - 1 / 2), hw]
    have hsq : (quantileSpeed S u * |pinnedKernelSlice u t|) ^ 2
        ≤ 1 / (4 * min t (1 - t) ^ 2) * (quantileSpeed S u ^ 2 * (u * (1 - u))) := by
      have hstep : quantileSpeed S u ^ 2 * ((u * (1 - u)) ^ 2 / min t (1 - t) ^ 2)
          ≤ quantileSpeed S u ^ 2 * (1 / 4 * (u * (1 - u)) / min t (1 - t) ^ 2) := by
        gcongr
      calc (quantileSpeed S u * |pinnedKernelSlice u t|) ^ 2
          = quantileSpeed S u ^ 2 * |pinnedKernelSlice u t| ^ 2 := by ring
        _ ≤ quantileSpeed S u ^ 2 * ((u * (1 - u)) ^ 2 / min t (1 - t) ^ 2) := by
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ quantileSpeed S u ^ 2 * (1 / 4 * (u * (1 - u)) / min t (1 - t) ^ 2) := hstep
        _ = 1 / (4 * min t (1 - t) ^ 2) * (quantileSpeed S u ^ 2 * (u * (1 - u))) := by
            field_simp
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖transposeKernelFun S t u‖ ^ 2),
      norm_transposeKernelFun]
    exact hsq

/-- The transposed row as an `L²` vector. -/
def transposeKernelVec (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : Lp ℂ 2 unitIntervalMeasure :=
  (memLp_transposeKernelFun S hfin ht).toLp _

theorem transposeKernelVec_coeFn (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (transposeKernelVec S hfin ht : ℝ → ℂ) =ᵐ[unitIntervalMeasure] transposeKernelFun S t :=
  MemLp.coeFn_toLp _


/-! ### The transposed rows move continuously -/

/-- **The pointwise increment of the transposed row.**  Two transposed rows differ exactly on the
interval between their parameters, where the difference has modulus the quantile speed. -/
theorem norm_sq_transposeKernelFun_sub (S : PositiveDensitySource) {t' t : ℝ} (hle : t' ≤ t)
    (u : ℝ) :
    ‖transposeKernelFun S t u - transposeKernelFun S t' u‖ ^ 2
      = (Ico t' t).indicator (fun u => quantileSpeed S u ^ 2) u := by
  have hslice : (pinnedKernelSlice u t : ℝ) - pinnedKernelSlice u t'
      = -((Ico t' t).indicator (fun _ => (1 : ℝ)) u) := by
    rw [pinnedKernelSlice, pinnedKernelSlice, Set.indicator_apply]
    by_cases h1 : t ≤ u
    · have h2 : t' ≤ u := hle.trans h1
      have h3 : u ∉ Ico t' t := fun hx => absurd h1 (not_le.mpr hx.2)
      rw [if_pos h1, if_pos h2, if_neg h3]
      ring
    · have h1' := not_le.mp h1
      by_cases h2 : t' ≤ u
      · have h3 : u ∈ Ico t' t := ⟨h2, h1'⟩
        rw [if_neg h1, if_pos h2, if_pos h3]
        ring
      · have h3 : u ∉ Ico t' t := fun hx => h2 hx.1
        rw [if_neg h1, if_neg h2, if_neg h3]
        ring
  have hdiff : transposeKernelFun S t u - transposeKernelFun S t' u
      = -(Complex.I * ((quantileSpeed S u : ℝ) : ℂ))
        * (((pinnedKernelSlice u t : ℝ) : ℂ) - ((pinnedKernelSlice u t' : ℝ) : ℂ)) := by
    rw [transposeKernelFun, transposeKernelFun]
    ring
  rw [hdiff, ← Complex.ofReal_sub, hslice]
  by_cases h : u ∈ Ico t' t
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    simp only [Complex.ofReal_neg, Complex.ofReal_one]
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (quantileSpeed_pos S u)]
    simp
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    simp

/-- **The transposed rows move continuously in `L²`.**  Their squared distance is the quantile
energy of the interval between the two parameters. -/
theorem integral_norm_sq_transposeKernelFun_sub (S : PositiveDensitySource) {t' t : ℝ}
    (hle : t' ≤ t) :
    (∫ u, ‖transposeKernelFun S t u - transposeKernelFun S t' u‖ ^ 2 ∂unitIntervalMeasure)
      = ∫ u in Ico t' t, quantileSpeed S u ^ 2 ∂unitIntervalMeasure := by
  rw [← integral_indicator measurableSet_Ico]
  exact integral_congr_ae
    (Filter.Eventually.of_forall (norm_sq_transposeKernelFun_sub S hle))



/-- The transposed row as a total `L²`-valued function of its parameter, zero outside the open
interval where it has finite energy. -/
def transposeVec (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S) (t : ℝ) :
    Lp ℂ 2 unitIntervalMeasure :=
  if h : t ∈ Ioo (0 : ℝ) 1 then (memLp_transposeKernelFun S hfin h).toLp _ else 0

theorem transposeVec_coeFn (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (transposeVec S hfin t : ℝ → ℂ) =ᵐ[unitIntervalMeasure] transposeKernelFun S t := by
  rw [transposeVec, dif_pos ht]
  exact MemLp.coeFn_toLp _

/-- **The `L²` increment of the transposed rows is the quantile energy of the interval between
their parameters.** -/
theorem norm_sq_transposeVec_sub (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)
    {t' t : ℝ} (ht' : t' ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) (hle : t' ≤ t) :
    ‖transposeVec S hfin t - transposeVec S hfin t'‖ ^ 2
      = ∫ u in Ico t' t, quantileSpeed S u ^ 2 ∂unitIntervalMeasure := by
  have hcoe : ((transposeVec S hfin t - transposeVec S hfin t' : Lp ℂ 2 unitIntervalMeasure) :
        ℝ → ℂ)
      =ᵐ[unitIntervalMeasure]
      fun u => transposeKernelFun S t u - transposeKernelFun S t' u := by
    filter_upwards [Lp.coeFn_sub (transposeVec S hfin t) (transposeVec S hfin t'),
      transposeVec_coeFn S hfin ht, transposeVec_coeFn S hfin ht'] with u h1 h2 h3
    rw [h1]
    simp only [Pi.sub_apply]
    rw [h2, h3]
  have hC := norm_sq_lp_eq_integral (transposeVec S hfin t - transposeVec S hfin t')
  have hcongr : (fun u => ((‖(transposeVec S hfin t - transposeVec S hfin t' :
        Lp ℂ 2 unitIntervalMeasure) u‖ ^ 2 : ℝ) : ℂ))
      =ᵐ[unitIntervalMeasure]
      fun u => ((‖transposeKernelFun S t u - transposeKernelFun S t' u‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [hcoe] with u hu
    rw [hu]
  rw [integral_congr_ae hcongr, integral_complex_ofReal,
    integral_norm_sq_transposeKernelFun_sub S hle] at hC
  exact_mod_cast hC



theorem norm_sq_transposeVec_sub' (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)
    {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1) :
    ‖transposeVec S hfin t - transposeVec S hfin t'‖ ^ 2
      = ∫ u in Ico (min t t') (max t t'), quantileSpeed S u ^ 2 ∂unitIntervalMeasure := by
  rcases le_total t' t with h | h
  · rw [min_eq_right h, max_eq_left h]
    exact norm_sq_transposeVec_sub S hfin ht' ht h
  · rw [min_eq_left h, max_eq_right h, norm_sub_rev]
    exact norm_sq_transposeVec_sub S hfin ht ht' h

/-- **The quantile energy of a subinterval is controlled by its length.**  On a compact
subinterval of the open unit interval the quantile speed is bounded. -/
theorem setIntegral_quantileSpeed_sq_le (S : PositiveDensitySource) {a b : ℝ}
    (hab : Icc a b ⊆ Ioo (0 : ℝ) 1) (hab01 : Icc a b ⊆ Icc (0 : ℝ) 1) {C : ℝ}
    (hbound : ∀ u ∈ Icc a b, quantileSpeed S u ^ 2 ≤ C) {c d : ℝ}
    (hcd : Ico c d ⊆ Icc a b) (hle : c ≤ d) :
    (∫ u in Ico c d, quantileSpeed S u ^ 2 ∂unitIntervalMeasure) ≤ C * (d - c) := by
  have hres : unitIntervalMeasure.restrict (Ico c d) = (volume : Measure ℝ).restrict (Ico c d) := by
    rw [unitIntervalMeasure, Measure.restrict_restrict measurableSet_Ico,
      Set.inter_eq_left.mpr (hcd.trans hab01)]
  have hcontOn : ContinuousOn (fun u => quantileSpeed S u ^ 2) (Icc a b) :=
    ((HedenmalmQuantile.continuousOn_quantileSpeed S).mono hab).pow 2
  have hintOn : IntegrableOn (fun u => quantileSpeed S u ^ 2) (Ico c d) volume :=
    ((hcontOn.integrableOn_compact isCompact_Icc).mono_set hcd)
  have hconst : IntegrableOn (fun _ : ℝ => C) (Ico c d) volume :=
    (continuousOn_const.integrableOn_compact (isCompact_Icc (a := c) (b := d))).mono_set
      Set.Ico_subset_Icc_self
  calc (∫ u in Ico c d, quantileSpeed S u ^ 2 ∂unitIntervalMeasure)
      = ∫ u in Ico c d, quantileSpeed S u ^ 2 ∂(volume : Measure ℝ) := by rw [hres]
    _ ≤ ∫ _u in Ico c d, C ∂(volume : Measure ℝ) := by
        refine setIntegral_mono_on hintOn hconst measurableSet_Ico fun u hu => ?_
        exact hbound u (hcd hu)
    _ = C * (d - c) := by
        rw [setIntegral_const]
        have hvol : (volume : Measure ℝ).real (Ico c d) = d - c := by
          rw [measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
        rw [hvol, smul_eq_mul]
        ring



/-- **The transposed rows form an `L²`-continuous family.**  This is what makes the adjoint an
honest kernel operator: the field of transposed rows is strongly measurable. -/
theorem continuousOn_transposeVec (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S) :
    ContinuousOn (transposeVec S hfin) (Ioo (0 : ℝ) 1) := by
  intro t₀ ht₀
  obtain ⟨h0, h1⟩ := ht₀
  set a : ℝ := t₀ / 2 with ha
  set b : ℝ := (t₀ + 1) / 2 with hb
  have hab : Icc a b ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨lt_of_lt_of_le (by linarith) hx.1, lt_of_le_of_lt hx.2 (by linarith)⟩
  have hab01 : Icc a b ⊆ Icc (0 : ℝ) 1 := fun x hx =>
    ⟨(hab hx).1.le, (hab hx).2.le⟩
  have hat : a < t₀ := by linarith
  have htb : t₀ < b := by linarith
  have hcontOn : ContinuousOn (fun u => quantileSpeed S u ^ 2) (Icc a b) :=
    ((HedenmalmQuantile.continuousOn_quantileSpeed S).mono hab).pow 2
  obtain ⟨C, hCle⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontOn
  have hCnonneg : 0 ≤ C :=
    le_trans (norm_nonneg _) (hCle a ⟨le_rfl, by linarith⟩)
  have hbound : ∀ u ∈ Icc a b, quantileSpeed S u ^ 2 ≤ C := by
    intro u hu
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hCle u hu)
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min (min (t₀ - a) (b - t₀)) (ε ^ 2 / (C + 1)), ?_, ?_⟩
  · have : (0 : ℝ) < ε ^ 2 / (C + 1) := by positivity
    exact lt_min (lt_min (by linarith) (by linarith)) this
  · intro t htmem hdist
    have hlt1 : |t - t₀| < t₀ - a := lt_of_lt_of_le hdist ((min_le_left _ _).trans (min_le_left _ _))
    have hlt2 : |t - t₀| < b - t₀ := lt_of_lt_of_le hdist ((min_le_left _ _).trans (min_le_right _ _))
    have hlt3 : |t - t₀| < ε ^ 2 / (C + 1) := lt_of_lt_of_le hdist (min_le_right _ _)
    have habs := abs_lt.mp (show |t - t₀| < t₀ - a from hlt1)
    have habs' := abs_lt.mp (show |t - t₀| < b - t₀ from hlt2)
    have hsub : Ico (min t t₀) (max t t₀) ⊆ Icc a b := by
      intro x hx
      constructor
      · exact le_trans (by rcases le_total t t₀ with h | h <;> simp [h] <;> linarith)
          hx.1
      · exact le_trans hx.2.le (by rcases le_total t t₀ with h | h <;> simp [h] <;>
          linarith)
    have hle : min t t₀ ≤ max t t₀ := min_le_max
    have hnormsq := norm_sq_transposeVec_sub' S hfin htmem ⟨h0, h1⟩
    have hbnd := setIntegral_quantileSpeed_sq_le S hab hab01 hbound hsub hle
    have hlen : max t t₀ - min t t₀ = |t - t₀| := by
      rcases le_total t t₀ with h | h
      · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]
        ring
      · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
    rw [hlen] at hbnd
    have hkey : ‖transposeVec S hfin t - transposeVec S hfin t₀‖ ^ 2 < ε ^ 2 := by
      rw [hnormsq]
      calc (∫ u in Ico (min t t₀) (max t t₀), quantileSpeed S u ^ 2 ∂unitIntervalMeasure)
          ≤ C * |t - t₀| := hbnd
        _ < ε ^ 2 := by
            rcases eq_or_lt_of_le (abs_nonneg (t - t₀)) with heq | hpos
            · rw [← heq, mul_zero]; positivity
            · have hstep : C * |t - t₀| < C * (ε ^ 2 / (C + 1)) + (ε ^ 2 / (C + 1)) := by
                nlinarith [hlt3, hCnonneg, hpos]
              have : C * (ε ^ 2 / (C + 1)) + (ε ^ 2 / (C + 1)) = ε ^ 2 := by
                field_simp
              linarith [hstep, this.le, this.ge]
    rw [dist_eq_norm]
    nlinarith [hkey, norm_nonneg (transposeVec S hfin t - transposeVec S hfin t₀), hε]



/-! ### The transposed kernel field -/

theorem conj_transposeKernelFun (S : PositiveDensitySource) (t u : ℝ) :
    (starRingEnd ℂ) (transposeKernelFun S t u) = -transposeKernelFun S t u := by
  rw [transposeKernelFun]
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- The transposed kernel field: the continuous functional `f ↦ ∫ conj K(u,t) f(u) du`, whose
Riesz vector is minus the transposed row. -/
def transposeKernelField (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S) (t : ℝ) :
    (Lp ℂ 2 unitIntervalMeasure) →L[ℂ] ℂ :=
  innerSL ℂ (-(transposeVec S hfin t))

/-- **The transposed field really is the integral against the transposed row.** -/
theorem transposeKernelField_apply (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (f : Lp ℂ 2 unitIntervalMeasure) :
    transposeKernelField S hfin t f
      = ∫ u, transposeKernelFun S t u * f u ∂unitIntervalMeasure := by
  show (inner ℂ (-(transposeVec S hfin t)) f : ℂ) = _
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_neg (transposeVec S hfin t), transposeVec_coeFn S hfin ht] with u h1 h2
  show (inner ℂ (((-(transposeVec S hfin t) : Lp ℂ 2 unitIntervalMeasure) : ℝ → ℂ) u) (f u) : ℂ)
    = _
  rw [h1]
  simp only [Pi.neg_apply]
  rw [h2, RCLike.inner_apply', map_neg, conj_transposeKernelFun]
  ring

theorem norm_transposeKernelField (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)
    (t : ℝ) : ‖transposeKernelField S hfin t‖ = ‖transposeVec S hfin t‖ := by
  rw [transposeKernelField, innerSL_apply_norm, norm_neg]

theorem continuousOn_transposeKernelField (S : PositiveDensitySource)
    (hfin : HasFiniteKernelEnergy S) :
    ContinuousOn (transposeKernelField S hfin) (Ioo (0 : ℝ) 1) :=
  (innerSL (𝕜 := ℂ) (E := Lp ℂ 2 unitIntervalMeasure)).continuous.comp_continuousOn
    (continuousOn_transposeVec S hfin).neg

theorem aestronglyMeasurable_transposeKernelField (S : PositiveDensitySource)
    (hfin : HasFiniteKernelEnergy S) :
    AEStronglyMeasurable (transposeKernelField S hfin) unitIntervalMeasure := by
  have hres : unitIntervalMeasure.restrict (Ioo (0 : ℝ) 1) = unitIntervalMeasure := by
    rw [unitIntervalMeasure, Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.mpr Ioo_subset_Icc_self, restrict_Ioo_eq_restrict_Icc]
  have h := (continuousOn_transposeKernelField S hfin).aestronglyMeasurable
    (μ := unitIntervalMeasure) measurableSet_Ioo
  rwa [hres] at h



theorem norm_sq_transposeVec (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ‖transposeVec S hfin t‖ ^ 2
      = ∫ u, quantileSpeed S u ^ 2 * pinnedKernelSlice u t ^ 2 ∂unitIntervalMeasure := by
  have hC := norm_sq_lp_eq_integral (transposeVec S hfin t)
  have hcongr : (fun u => ((‖(transposeVec S hfin t : Lp ℂ 2 unitIntervalMeasure) u‖ ^ 2 : ℝ) : ℂ))
      =ᵐ[unitIntervalMeasure]
      fun u => ((quantileSpeed S u ^ 2 * pinnedKernelSlice u t ^ 2 : ℝ) : ℂ) := by
    filter_upwards [transposeVec_coeFn S hfin ht] with u hu
    show ((‖(transposeVec S hfin t : Lp ℂ 2 unitIntervalMeasure) u‖ ^ 2 : ℝ) : ℂ) = _
    rw [show (transposeVec S hfin t : ℝ → ℂ) u = transposeKernelFun S t u from hu,
      norm_transposeKernelFun, mul_pow, sq_abs]
  rw [integral_congr_ae hcongr, integral_complex_ofReal] at hC
  exact_mod_cast hC

theorem measurable_uncurry_slice_sq (S : PositiveDensitySource) :
    Measurable (fun p : ℝ × ℝ => quantileSpeed S p.1 ^ 2 * pinnedKernelSlice p.1 p.2 ^ 2) := by
  have hmq : Measurable (quantileSpeed S) :=
    measurable_const.div (S.continuous_k.measurable.comp S.measurable_quantileFun)
  have hset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hite : Measurable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then (1 : ℝ) else 0) :=
    Measurable.ite hset measurable_const measurable_const
  have hslice : Measurable (fun p : ℝ × ℝ => pinnedKernelSlice p.1 p.2) :=
    hite.sub measurable_fst
  exact ((hmq.comp measurable_fst).pow_const 2).mul (hslice.pow_const 2)

set_option maxHeartbeats 2000000 in
/-- **The transposed field has finite energy.**  Its total energy is the Hilbert--Schmidt energy of
the source inverse, computed with the roles of the two variables exchanged. -/
theorem memLp_transposeKernelField (S : PositiveDensitySource)
    (hfin : HasFiniteKernelEnergy S) :
    MemLp (transposeKernelField S hfin) 2 unitIntervalMeasure := by
  refine (memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_transposeKernelField S hfin)).mpr ?_
  have hmeasF := (measurable_uncurry_slice_sq S).aestronglyMeasurable
    (μ := unitIntervalMeasure.prod unitIntervalMeasure)
  have hinner : ∀ u ∈ Ioo (0 : ℝ) 1,
      (∫ t, quantileSpeed S u ^ 2 * pinnedKernelSlice u t ^ 2 ∂unitIntervalMeasure)
        = quantileSpeed S u ^ 2 * (u * (1 - u)) := by
    intro u hu
    rw [MeasureTheory.integral_const_mul, unitIntervalMeasure_eq,
      integral_pinnedKernelSlice_sq hu]
  have hprod : Integrable
      (fun p : ℝ × ℝ => quantileSpeed S p.1 ^ 2 * pinnedKernelSlice p.1 p.2 ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) := by
    rw [integrable_prod_iff hmeasF]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with u hu
      refine Integrable.mono' (integrable_const (quantileSpeed S u ^ 2)) ?_ ?_
      · have hite : Measurable (fun t : ℝ => if t ≤ u then (1 : ℝ) else 0) :=
          Measurable.ite measurableSet_Iic measurable_const measurable_const
        have hsl : Measurable (fun t : ℝ => pinnedKernelSlice u t) :=
          hite.sub measurable_const
        exact (measurable_const.mul (hsl.pow_const 2)).aestronglyMeasurable
      · filter_upwards with t
        have h1 : |pinnedKernelSlice u t| ≤ 1 :=
          abs_pinnedKernelSlice_le (Ioo_subset_Icc_self hu) t
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h2 : pinnedKernelSlice u t ^ 2 ≤ 1 := by
          rw [← sq_abs]
          nlinarith [abs_nonneg (pinnedKernelSlice u t), h1]
        nlinarith [sq_nonneg (quantileSpeed S u), h2]
    · refine hfin.congr ?_
      filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with u hu
      rw [← hinner u hu]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show quantileSpeed S u ^ 2 * pinnedKernelSlice u t ^ 2
        = ‖quantileSpeed S u ^ 2 * pinnedKernelSlice u t ^ 2‖
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine (hprod.integral_prod_right).congr ?_
  filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with t ht
  rw [norm_transposeKernelField, norm_sq_transposeVec S hfin ht]

/-- The transposed field as an element of `L²((0,1); H*)`. -/
def transposeKernelL2 (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S) :
    Lp ((Lp ℂ 2 unitIntervalMeasure) →L[ℂ] ℂ) 2 unitIntervalMeasure :=
  (memLp_transposeKernelField S hfin).toLp _



/-! ### The adjoint is the transposed kernel operator -/

theorem kernelOperator_ae_of_field {K : Lp ((Lp ℂ 2 unitIntervalMeasure) →L[ℂ] ℂ) 2
      unitIntervalMeasure} (f : Lp ℂ 2 unitIntervalMeasure) :
    (kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure K f : ℝ → ℂ)
      =ᵐ[unitIntervalMeasure] fun t => (K t) f := by
  have hholder := (evalBilinear (𝕜 := ℂ) (E := Lp ℂ 2 unitIntervalMeasure)).coeFn_holder
    (r := (2 : ENNReal)) K (Lp.const ∞ unitIntervalMeasure f)
  have hconst := Lp.coeFn_const (p := ∞) unitIntervalMeasure f
  filter_upwards [hholder, hconst] with t hholderT hconstT
  rw [kernelOperator, kernelOperatorMap_apply, hholderT, hconstT]
  simp [evalBilinear]

theorem transposeKernelL2_coeFn (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S) :
    (transposeKernelL2 S hfin : ℝ → (Lp ℂ 2 unitIntervalMeasure) →L[ℂ] ℂ)
      =ᵐ[unitIntervalMeasure] transposeKernelField S hfin :=
  MemLp.coeFn_toLp _

theorem pinnedKernelL2_coeFn (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S) :
    (pinnedKernelL2 S hfin : ℝ → (Lp ℂ 2 unitIntervalMeasure) →L[ℂ] ℂ)
      =ᵐ[unitIntervalMeasure] pinnedKernelField S :=
  MemLp.coeFn_toLp _

theorem memLp_swap_pinnedKernelFun (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S) :
    MemLp (fun p : ℝ × ℝ => pinnedKernelFun S p.2 p.1) 2
      (unitIntervalMeasure.prod unitIntervalMeasure) := by
  refine (memLp_two_iff_integrable_sq_norm ?_).mpr
    (integrable_sq_norm_swap_pinnedKernelFun S hfin)
  exact ((measurable_uncurry_pinnedKernelFun S).comp measurable_swap).aestronglyMeasurable

set_option maxHeartbeats 2000000 in
/-- **The adjoint of the source inverse is the transposed kernel operator.**  This is the last
structural input of the trace calibration: it turns `tr(B²) = ⟨B†, B⟩_HS` into a double kernel
integral. -/
theorem adjoint_kernelOperator_eq (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S) :
    ContinuousLinearMap.adjoint
        (kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure
          (pinnedKernelL2 S hfin))
      = kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure
          (transposeKernelL2 S hfin) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  have hswap : Integrable (Function.uncurry
      (fun t u : ℝ => pinnedKernelFun S u t * (starRingEnd ℂ) (f u) * g t))
      (unitIntervalMeasure.prod unitIntervalMeasure) := by
    have hmul := (memLp_swap_pinnedKernelFun S hfin).integrable_mul (memLp_tensor f g)
    refine hmul.congr ?_
    filter_upwards with p
    show (fun p : ℝ × ℝ => pinnedKernelFun S p.2 p.1) p * ((starRingEnd ℂ) (f p.2) * g p.1)
      = Function.uncurry (fun t u : ℝ => pinnedKernelFun S u t * (starRingEnd ℂ) (f u) * g t) p
    simp only [Function.uncurry]
    ring
  have hleft : (inner ℂ (kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure
        (transposeKernelL2 S hfin) f) g : ℂ)
      = ∫ t, ∫ u, pinnedKernelFun S u t * (starRingEnd ℂ) (f u) * g t ∂unitIntervalMeasure
        ∂unitIntervalMeasure := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [kernelOperator_ae_of_field (K := transposeKernelL2 S hfin) f,
      transposeKernelL2_coeFn S hfin,
      ae_unitIntervalMeasure_mem_Ioo] with t h1 h2 ht
    show (inner ℂ ((kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure
        (transposeKernelL2 S hfin) f : Lp ℂ 2 unitIntervalMeasure) t) (g t) : ℂ) = _
    rw [RCLike.inner_apply', h1]
    show (starRingEnd ℂ) ((transposeKernelL2 S hfin) t f) * g t = _
    rw [show (transposeKernelL2 S hfin : ℝ → (Lp ℂ 2 unitIntervalMeasure) →L[ℂ] ℂ) t
        = transposeKernelField S hfin t from h2,
      transposeKernelField_apply S hfin ht f, ← integral_conj, ← MeasureTheory.integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show (starRingEnd ℂ) (transposeKernelFun S t u * f u) * g t
      = pinnedKernelFun S u t * (starRingEnd ℂ) (f u) * g t
    rw [map_mul, transposeKernelFun_eq_conj, Complex.conj_conj]
  have hright : (inner ℂ f (kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure
        (pinnedKernelL2 S hfin) g) : ℂ)
      = ∫ u, ∫ t, pinnedKernelFun S u t * (starRingEnd ℂ) (f u) * g t ∂unitIntervalMeasure
        ∂unitIntervalMeasure := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [kernelOperator_ae_of_field (K := pinnedKernelL2 S hfin) g,
      pinnedKernelL2_coeFn S hfin] with u h1 h2
    show (inner ℂ (f u) ((kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure
        (pinnedKernelL2 S hfin) g : Lp ℂ 2 unitIntervalMeasure) u) : ℂ) = _
    rw [RCLike.inner_apply', h1]
    show (starRingEnd ℂ) (f u) * ((pinnedKernelL2 S hfin) u g) = _
    rw [show (pinnedKernelL2 S hfin : ℝ → (Lp ℂ 2 unitIntervalMeasure) →L[ℂ] ℂ) u
        = pinnedKernelField S u from h2,
      pinnedKernelField_apply S u g, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    ring
  rw [hleft, hright]
  exact integral_integral_swap hswap



/-- **The off-diagonal product of two pinned slices.**  Off the diagonal the product of the two
transposed slices is minus the covariance kernel `min(t,u) - t u`.  On the diagonal the identity
fails, but the diagonal is null in the product measure. -/
theorem neg_mul_pinnedKernelSlice {t u : ℝ} (htu : t ≠ u) :
    -(pinnedKernelSlice t u * pinnedKernelSlice u t) = min t u - t * u := by
  rcases lt_or_gt_of_ne htu with h | h
  · have h1 : ¬ u ≤ t := not_le.mpr h
    have h2 : t ≤ u := h.le
    rw [pinnedKernelSlice, pinnedKernelSlice, if_neg h1, if_pos h2, min_eq_left h2]
    ring
  · have h1 : u ≤ t := h.le
    have h2 : ¬ t ≤ u := not_le.mpr h
    rw [pinnedKernelSlice, pinnedKernelSlice, if_pos h1, if_neg h2, min_eq_right h1]
    ring



/-! ### The covariance decomposition of the slice pairing -/

set_option maxHeartbeats 1000000 in
/-- **The slice pairing is the covariance kernel.**  For `t ≤ u` the pairing of the two pinned
slices over the unit interval is `t(1-u)`. -/
theorem integral_pinnedKernelSlice_mul {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hle : t ≤ u) :
    (∫ s in Ioo (0 : ℝ) 1, pinnedKernelSlice t s * pinnedKernelSlice u s) = t * (1 - u) := by
  have hbdd : ∀ s : ℝ, ‖pinnedKernelSlice t s * pinnedKernelSlice u s‖ ≤ 1 := by
    intro s
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := abs_pinnedKernelSlice_le (Ioo_subset_Icc_self ht) s
    have h2 := abs_pinnedKernelSlice_le (Ioo_subset_Icc_self hu) s
    nlinarith [abs_nonneg (pinnedKernelSlice t s), abs_nonneg (pinnedKernelSlice u s)]
  have hmeas : AEStronglyMeasurable
      (fun s => pinnedKernelSlice t s * pinnedKernelSlice u s) volume := by
    refine Measurable.aestronglyMeasurable (Measurable.mul ?_ ?_) <;>
      exact (measurable_const.ite (measurableSet_le measurable_id measurable_const)
        measurable_const).sub measurable_const
  have hint : ∀ v : Set ℝ, MeasurableSet v → volume v ≠ ⊤ →
      IntegrableOn (fun s => pinnedKernelSlice t s * pinnedKernelSlice u s) v volume := by
    intro v hv hfin
    refine Measure.integrableOn_of_bounded (M := (1 : ℝ)) hfin hmeas ?_
    filter_upwards with s
    exact hbdd s
  have hsplit1 : Ioo (0 : ℝ) 1 = Ioc 0 t ∪ Ioo t 1 := by
    ext s
    simp only [mem_Ioo, mem_union, mem_Ioc]
    constructor
    · rintro ⟨h0, h1⟩
      rcases le_or_gt s t with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨h, h1⟩
    · rintro (⟨h0, h⟩ | ⟨h, h1⟩)
      · exact ⟨h0, lt_of_le_of_lt h ht.2⟩
      · exact ⟨lt_trans ht.1 h, h1⟩
  have hsplit2 : Ioo t (1 : ℝ) = Ioc t u ∪ Ioo u 1 := by
    ext s
    simp only [mem_Ioo, mem_union, mem_Ioc]
    constructor
    · rintro ⟨h0, h1⟩
      rcases le_or_gt s u with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨h, h1⟩
    · rintro (⟨h0, h⟩ | ⟨h, h1⟩)
      · exact ⟨h0, lt_of_le_of_lt h hu.2⟩
      · exact ⟨lt_of_le_of_lt hle h, h1⟩
  have hdisj1 : Disjoint (Ioc (0 : ℝ) t) (Ioo t 1) := by
    rw [Set.disjoint_left]
    rintro s ⟨_, hs⟩ ⟨hs', _⟩
    exact absurd hs (not_le.mpr hs')
  have hdisj2 : Disjoint (Ioc t u) (Ioo u 1) := by
    rw [Set.disjoint_left]
    rintro s ⟨_, hs⟩ ⟨hs', _⟩
    exact absurd hs (not_le.mpr hs')
  have hA := hint (Ioc (0 : ℝ) t) measurableSet_Ioc
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hB := hint (Ioc t u) measurableSet_Ioc
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hC := hint (Ioo u 1) measurableSet_Ioo
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  rw [hsplit1, MeasureTheory.setIntegral_union hdisj1 measurableSet_Ioo hA
    (by rw [hsplit2]; exact hB.union hC), hsplit2,
    MeasureTheory.setIntegral_union hdisj2 measurableSet_Ioo hB hC]
  have hleft : (∫ s in Ioc (0 : ℝ) t, pinnedKernelSlice t s * pinnedKernelSlice u s)
      = t * ((1 - t) * (1 - u)) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (1 - t) * (1 - u)) fun s hs => ?_]
    · rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero, smul_eq_mul,
        ENNReal.toReal_ofReal ht.1.le]
    · rw [pinnedKernelSlice, pinnedKernelSlice, if_pos hs.2, if_pos (hs.2.trans hle)]
  have hmid : (∫ s in Ioc t u, pinnedKernelSlice t s * pinnedKernelSlice u s)
      = (u - t) * (-t * (1 - u)) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => -t * (1 - u)) fun s hs => ?_]
    · rw [setIntegral_const, Measure.real, Real.volume_Ioc, smul_eq_mul,
        ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ u - t)]
    · rw [pinnedKernelSlice, pinnedKernelSlice, if_neg (not_le.mpr hs.1), if_pos hs.2]
      ring
  have hright : (∫ s in Ioo u (1 : ℝ), pinnedKernelSlice t s * pinnedKernelSlice u s)
      = (1 - u) * (t * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => t * u) fun s hs => ?_]
    · rw [setIntegral_const, Measure.real, Real.volume_Ioo, smul_eq_mul,
        ENNReal.toReal_ofReal (by linarith [hu.2] : (0 : ℝ) ≤ 1 - u)]
    · rw [pinnedKernelSlice, pinnedKernelSlice,
        if_neg (not_le.mpr (lt_of_le_of_lt hle hs.1)), if_neg (not_le.mpr hs.1)]
      ring
  rw [hleft, hmid, hright]
  ring

/-- **The covariance decomposition.**  The slice pairing over the unit interval is exactly
`min(t,u) - t u`. -/
theorem integral_pinnedKernelSlice_mul_min {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫ s in Ioo (0 : ℝ) 1, pinnedKernelSlice t s * pinnedKernelSlice u s)
      = min t u - t * u := by
  rcases le_total t u with h | h
  · rw [integral_pinnedKernelSlice_mul ht hu h, min_eq_left h]
    ring
  · rw [show (fun s => pinnedKernelSlice t s * pinnedKernelSlice u s)
        = fun s => pinnedKernelSlice u s * pinnedKernelSlice t s from
      funext fun s => mul_comm _ _, integral_pinnedKernelSlice_mul hu ht h, min_eq_right h]
    ring


end HedenmalmThetaSource

end

end RHTower
