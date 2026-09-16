import GaloisForLFunctions.RHTower.EulerDeletionResidueMartingale
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Exact weighted residue equations for the chronological physical projection

The chronological history projection is a conditional expectation for the
original Báez--Duarte cell probability measure. This file identifies each
of its residue-fibre moments with the literal weighted residue sum. The
weights remain `1 / ((j + 1) * (j + 2))`; no uniform-period replacement or
absolute-value estimate is used.
-/

noncomputable section
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped BigOperators
namespace RHTower.DeletionResidueMartingale

/-- Exact physical residue fibre at chronological stage `L`. -/
def historyFibre (L r : ℕ) : Set ℕ := {j | j % clock L = r}

/-- Every residue class below the chronological clock has strictly positive
physical mass. -/
theorem historyFibre_mass_pos (L r : ℕ) (hr : r < clock L) :
    0 < cellMeasure.real (historyFibre L r) := by
  calc
    0 < cellWeight r := by unfold cellWeight; positivity
    _ = cellMeasure.real {r} := (cellMeasure_singleton r).symm
    _ ≤ cellMeasure.real (historyFibre L r) := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro j hj
      have hjr : j = r := by simpa only [Set.mem_singleton_iff] using hj
      subst j
      simp only [historyFibre, Set.mem_setOf_eq]
      exact Nat.mod_eq_of_lt hr

private theorem historyFibre_measurable (L r : ℕ) :
    MeasurableSet[residueSigma (clock L)] (historyFibre L r) := by
  change MeasurableSet[MeasurableSpace.comap (fun j : ℕ => j % clock L) ⊤] _
  exact MeasurableSpace.measurableSet_comap.mpr
    ⟨{r}, (Set.to_countable _).measurableSet, rfl⟩

private theorem historyFibre_measurable_top (L r : ℕ) : MeasurableSet (historyFibre L r) :=
  (Set.to_countable _).measurableSet

private theorem integrable_historyFibre_residue (n L r : ℕ) :
    Integrable ((historyFibre L r).indicator (residue n)) cellMeasure := by
  apply (MemLp.of_bound (measurable_from_top.aestronglyMeasurable) 1
    (Eventually.of_forall fun j => by
      simp only [Real.norm_eq_abs]
      by_cases hj : j ∈ historyFibre L r
      · rw [Set.indicator_of_mem hj]
        rw [abs_of_nonneg (residue_bounds n j).1]
        exact (residue_bounds n j).2
      · simp [Set.indicator, hj])).integrable one_le_two

/-- Every chronological conditional residue projection retains the exact physical
weighted sum on each of its residue fibres. -/
theorem integral_historyProjection_on_fibre_eq_weighted_residue
    (n L r : ℕ) :
    ∫ j in historyFibre L r,
      ((historySpace L).starProjection (residueVec n)) j ∂cellMeasure =
      ∑' j : ℕ, cellWeight j * ((historyFibre L r).indicator (residue n) j) := by
  have hproj := integral_condExpL2_eq (E' := ℝ) (𝕜 := ℝ)
    (m := residueSigma (clock L)) (m0 := (inferInstance : MeasurableSpace ℕ))
    (μ := cellMeasure)
    (show residueSigma (clock L) ≤ (inferInstance : MeasurableSpace ℕ) from le_top)
    (residueVec n) (historyFibre_measurable L r) (measure_ne_top _ _)
  have hvec : (residueVec n : ℕ → ℝ) =ᵐ[cellMeasure] residue n := by
    exact MemLp.coeFn_toLp _
  have hweight :
      ∫ j in historyFibre L r, residue n j ∂cellMeasure =
        ∑' j : ℕ, cellWeight j * ((historyFibre L r).indicator (residue n) j) := by
    rw [← integral_indicator (historyFibre_measurable_top L r)]
    have h := PMF.integral_eq_tsum cellPMF ((historyFibre L r).indicator (residue n))
      (integrable_historyFibre_residue n L r)
    change (∫ j, (historyFibre L r).indicator (residue n) j ∂cellPMF.toMeasure) = _
    rw [h]
    apply tsum_congr
    intro j
    change (ENNReal.ofReal (cellWeight j)).toReal *
      (historyFibre L r).indicator (residue n) j = _
    rw [ENNReal.toReal_ofReal (by unfold cellWeight; positivity)]
  calc
    _ = ∫ j in historyFibre L r, (residueVec n) j ∂cellMeasure := by
      simpa only [historySpace, condExpL2, Submodule.starProjection_apply] using hproj
    _ = ∫ j in historyFibre L r, residue n j ∂cellMeasure := by
      exact setIntegral_congr_ae (historyFibre_measurable_top L r)
        (hvec.mono fun _ h _ => h)
    _ = _ := hweight

/-- A chronological physical projection is pointwise constant on the actual
residue fibres.  Full support of `cellMeasure` upgrades the conditional
almost-everywhere statement to a pointwise fibre law. -/
theorem historyProjection_factors_through_clock (n L : ℕ) :
    ∃ h : ℕ → ℝ, StronglyMeasurable h ∧
      ∀ j : ℕ, ((historySpace L).starProjection (residueVec n)) j = h (j % clock L) := by
  let g : ℕ → ℝ := ((historySpace L).starProjection (residueVec n) : ℕ → ℝ)
  have hmem : (historySpace L).starProjection (residueVec n) ∈ historySpace L :=
    Submodule.starProjection_apply_mem _ _
  change ((historySpace L).starProjection (residueVec n) : Lp ℝ 2 cellMeasure) ∈
    lpMeas ℝ ℝ (residueSigma (clock L)) 2 cellMeasure at hmem
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hmem
  let g₀ : ℕ → ℝ := hmem.mk g
  have hg₀ : StronglyMeasurable[residueSigma (clock L)] g₀ :=
    hmem.stronglyMeasurable_mk
  obtain ⟨h, hh, hfac⟩ := hg₀.exists_eq_measurable_comp
    (f := fun j : ℕ => j % clock L)
  refine ⟨h, hh, ?_⟩
  have hae : g =ᵐ[cellMeasure] g₀ := hmem.ae_eq_mk
  have hpoint : ∀ j : ℕ, g j = g₀ j := by
    intro j
    apply (ae_iff_of_countable.mp hae) j
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    change ENNReal.ofReal (cellWeight j) ≠ 0
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by unfold cellWeight; positivity))
  intro j
  change g j = _
  rw [hpoint j, hfac]
  rfl

/-- The value of a chronological projection on a residue fibre is its exact
physical fibre moment divided by that fibre's physical mass.  This still
uses the original nonuniform cell law. -/
theorem exists_historyProjection_fibre_means (n L : ℕ) :
    ∃ h : ℕ → ℝ, StronglyMeasurable h ∧
      (∀ j : ℕ, ((historySpace L).starProjection (residueVec n)) j = h (j % clock L)) ∧
      ∀ r : ℕ,
        ∫ j in historyFibre L r,
          ((historySpace L).starProjection (residueVec n)) j ∂cellMeasure =
          cellMeasure.real (historyFibre L r) * h r := by
  obtain ⟨h, hh, hpoint⟩ := historyProjection_factors_through_clock n L
  refine ⟨h, hh, hpoint, ?_⟩
  intro r
  rw [show (∫ j in historyFibre L r,
      ((historySpace L).starProjection (residueVec n)) j ∂cellMeasure) =
      ∫ j in historyFibre L r, h r ∂cellMeasure by
        apply setIntegral_congr_fun (historyFibre_measurable_top L r)
        intro j hj
        rw [hpoint j]
        congr]
  simpa only [smul_eq_mul] using
    (setIntegral_const (μ := cellMeasure) (s := historyFibre L r) (h r))

/-- On every physical residue class below the clock, the chronological
predictor is the literal signed weighted residue moment divided by the
physical fibre mass. -/
theorem exists_historyProjection_eq_weighted_residue_quotient (n L : ℕ) :
    ∃ h : ℕ → ℝ, StronglyMeasurable h ∧
      (∀ j : ℕ, ((historySpace L).starProjection (residueVec n)) j = h (j % clock L)) ∧
      ∀ r : ℕ, r < clock L →
        h r =
          (∑' j : ℕ, cellWeight j * ((historyFibre L r).indicator (residue n) j)) /
            cellMeasure.real (historyFibre L r) := by
  obtain ⟨h, hh, hpoint, hmean⟩ := exists_historyProjection_fibre_means n L
  refine ⟨h, hh, hpoint, ?_⟩
  intro r hr
  have hmass : cellMeasure.real (historyFibre L r) ≠ 0 :=
    ne_of_gt (historyFibre_mass_pos L r hr)
  have hsource := integral_historyProjection_on_fibre_eq_weighted_residue n L r
  have hvalue := hmean r
  rw [hsource] at hvalue
  apply (eq_div_iff hmass).mpr
  rw [mul_comm]
  exact hvalue.symm

/-- Exact physical coarea for a chronological residue projection.  The right
side has finitely many clock fibres, but each numerator is the literal signed
infinite physical residue sum and each denominator is that fibre's actual
cell mass. -/
theorem historyProjection_norm_sq_eq_weighted_residue_coarea (n L : ℕ) :
    ‖(historySpace L).starProjection (residueVec n)‖ ^ 2 =
      ∑ r ∈ range (clock L),
        (∑' j : ℕ, cellWeight j * ((historyFibre L r).indicator (residue n) j)) ^ 2 /
          cellMeasure.real (historyFibre L r) := by
  obtain ⟨h, hh, hpoint, hquot⟩ :=
    exists_historyProjection_eq_weighted_residue_quotient n L
  let g : ℕ → ℝ := ((historySpace L).starProjection (residueVec n) : ℕ → ℝ)
  have hint : Integrable (fun j => g j ^ 2) cellMeasure := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm
        (Lp.aestronglyMeasurable ((historySpace L).starProjection (residueVec n)))).mp
          (Lp.memLp ((historySpace L).starProjection (residueVec n)))
  have hnorm : ‖(historySpace L).starProjection (residueVec n)‖ ^ 2 =
      ∫ j, g j ^ 2 ∂cellMeasure := by
    change ‖(historySpace L).starProjection (residueVec n)‖ ^ 2 =
      ∫ j, ((historySpace L).starProjection (residueVec n)) j ^ 2 ∂cellMeasure
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have hunion : (⋃ r ∈ range (clock L), historyFibre L r) = Set.univ := by
    ext j
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨j % clock L, mem_range.mpr (Nat.mod_lt _ (clock_pos L)), ?_⟩
    simp [historyFibre]
  have hdisjoint : Set.Pairwise (↑(range (clock L)) : Set ℕ)
      (fun a b => Disjoint (historyFibre L a) (historyFibre L b)) := by
    intro a ha b hb hab
    refine Set.disjoint_left.2 ?_
    intro j hja hjb
    apply hab
    rw [historyFibre, Set.mem_setOf_eq] at hja hjb
    exact hja.symm.trans hjb
  calc
    ‖(historySpace L).starProjection (residueVec n)‖ ^ 2 =
        ∫ j, g j ^ 2 ∂cellMeasure := hnorm
    _ = ∫ j in ⋃ r ∈ range (clock L), historyFibre L r, g j ^ 2 ∂cellMeasure := by
      rw [hunion, setIntegral_univ]
    _ = ∑ r ∈ range (clock L), ∫ j in historyFibre L r, g j ^ 2 ∂cellMeasure := by
      exact integral_biUnion_finset (range (clock L))
        (fun r _ => historyFibre_measurable_top L r) hdisjoint
        (fun _ _ => hint.integrableOn)
    _ = ∑ r ∈ range (clock L), cellMeasure.real (historyFibre L r) * h r ^ 2 := by
      apply sum_congr rfl
      intro r hr
      rw [show (∫ j in historyFibre L r, g j ^ 2 ∂cellMeasure) =
          ∫ j in historyFibre L r, h r ^ 2 ∂cellMeasure by
            apply setIntegral_congr_fun (historyFibre_measurable_top L r)
            intro j hj
            change ((historySpace L).starProjection (residueVec n)) j ^ 2 = _
            rw [hpoint j]
            congr]
      simpa only [smul_eq_mul] using
        (setIntegral_const (μ := cellMeasure) (s := historyFibre L r) (h r ^ 2))
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      have hmass : cellMeasure.real (historyFibre L r) ≠ 0 :=
        ne_of_gt (historyFibre_mass_pos L r (mem_range.mp hr))
      rw [hquot r (mem_range.mp hr)]
      field_simp [hmass]

/-- Every vector in a chronological history space is pointwise a function of
its residue clock, since every physical cell has positive mass. -/
theorem historySpace_factors_through_clock (L : ℕ) (v : Lp ℝ 2 cellMeasure)
    (hv : v ∈ historySpace L) :
    ∃ h : ℕ → ℝ, StronglyMeasurable h ∧ ∀ j : ℕ, v j = h (j % clock L) := by
  let g : ℕ → ℝ := (v : ℕ → ℝ)
  change v ∈ lpMeas ℝ ℝ (residueSigma (clock L)) 2 cellMeasure at hv
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hv
  let g₀ : ℕ → ℝ := hv.mk g
  have hg₀ : StronglyMeasurable[residueSigma (clock L)] g₀ :=
    hv.stronglyMeasurable_mk
  obtain ⟨h, hh, hfac⟩ := hg₀.exists_eq_measurable_comp
    (f := fun j : ℕ => j % clock L)
  refine ⟨h, hh, ?_⟩
  have hae : g =ᵐ[cellMeasure] g₀ := hv.ae_eq_mk
  have hpoint : ∀ j : ℕ, g j = g₀ j := by
    intro j
    apply (ae_iff_of_countable.mp hae) j
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    change ENNReal.ofReal (cellWeight j) ≠ 0
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by unfold cellWeight; positivity))
  intro j
  change g j = _
  rw [hpoint j, hfac]
  rfl

/-- Exact physical coarea for every vector determined by a chronological
residue clock. -/
theorem historySpace_norm_sq_eq_fibre_coarea (L : ℕ) (v : Lp ℝ 2 cellMeasure)
    (hv : v ∈ historySpace L) :
    ‖v‖ ^ 2 = ∑ r ∈ range (clock L),
      (∫ j in historyFibre L r, v j ∂cellMeasure) ^ 2 /
        cellMeasure.real (historyFibre L r) := by
  obtain ⟨h, hh, hpoint⟩ := historySpace_factors_through_clock L v hv
  let g : ℕ → ℝ := (v : ℕ → ℝ)
  have hint : Integrable (fun j => g j ^ 2) cellMeasure := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hnorm : ‖v‖ ^ 2 = ∫ j, g j ^ 2 ∂cellMeasure := by
    change ‖v‖ ^ 2 = ∫ j, v j ^ 2 ∂cellMeasure
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have hunion : (⋃ r ∈ range (clock L), historyFibre L r) = Set.univ := by
    ext j
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨j % clock L, mem_range.mpr (Nat.mod_lt _ (clock_pos L)), ?_⟩
    simp [historyFibre]
  have hdisjoint : Set.Pairwise (↑(range (clock L)) : Set ℕ)
      (fun a b => Disjoint (historyFibre L a) (historyFibre L b)) := by
    intro a ha b hb hab
    refine Set.disjoint_left.2 ?_
    intro j hja hjb
    apply hab
    rw [historyFibre, Set.mem_setOf_eq] at hja hjb
    exact hja.symm.trans hjb
  have hmean : ∀ r : ℕ,
      ∫ j in historyFibre L r, v j ∂cellMeasure =
        cellMeasure.real (historyFibre L r) * h r := by
    intro r
    rw [show (∫ j in historyFibre L r, v j ∂cellMeasure) =
        ∫ j in historyFibre L r, h r ∂cellMeasure by
          apply setIntegral_congr_fun (historyFibre_measurable_top L r)
          intro j hj
          calc
            g j = h (j % clock L) := hpoint j
            _ = h r := by congr]
    simpa only [smul_eq_mul] using
      (setIntegral_const (μ := cellMeasure) (s := historyFibre L r) (h r))
  calc
    ‖v‖ ^ 2 = ∫ j, g j ^ 2 ∂cellMeasure := hnorm
    _ = ∫ j in ⋃ r ∈ range (clock L), historyFibre L r, g j ^ 2 ∂cellMeasure := by
      rw [hunion, setIntegral_univ]
    _ = ∑ r ∈ range (clock L), ∫ j in historyFibre L r, g j ^ 2 ∂cellMeasure := by
      exact integral_biUnion_finset (range (clock L))
        (fun r _ => historyFibre_measurable_top L r) hdisjoint
        (fun _ _ => hint.integrableOn)
    _ = ∑ r ∈ range (clock L), cellMeasure.real (historyFibre L r) * h r ^ 2 := by
      apply sum_congr rfl
      intro r hr
      rw [show (∫ j in historyFibre L r, g j ^ 2 ∂cellMeasure) =
          ∫ j in historyFibre L r, h r ^ 2 ∂cellMeasure by
            apply setIntegral_congr_fun (historyFibre_measurable_top L r)
            intro j hj
            change v j ^ 2 = _
            rw [hpoint j]
            congr]
      simpa only [smul_eq_mul] using
        (setIntegral_const (μ := cellMeasure) (s := historyFibre L r) (h r ^ 2))
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      have hmass : cellMeasure.real (historyFibre L r) ≠ 0 :=
        ne_of_gt (historyFibre_mass_pos L r (mem_range.mp hr))
      rw [hmean r]
      field_simp [hmass]

/-- The accumulated Möbius predictable drift belongs to the current
chronological history space. -/
theorem predictableDrift_mem_historySpace (N : ℕ) : predictableDrift N ∈ historySpace N := by
  change (∑ i ∈ range N, ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) •
    (historySpace i).starProjection (residueVec (i + 1))) ∈ historySpace N
  refine Submodule.sum_mem _ ?_
  intro i hi
  refine Submodule.smul_mem (historySpace N) _ ?_
  exact historySpace_mono (Nat.le_of_lt (mem_range.mp hi))
    (Submodule.starProjection_apply_mem _ _)

/-- The complete predictable energy is an exact finite-clock physical
coarea.  The only remaining analytic task is to bound its signed fibre
moments, including their cross-time cancellations. -/
theorem predictableDrift_norm_sq_eq_fibre_coarea (N : ℕ) :
    ‖predictableDrift N‖ ^ 2 = ∑ r ∈ range (clock N),
      (∫ j in historyFibre N r, predictableDrift N j ∂cellMeasure) ^ 2 /
        cellMeasure.real (historyFibre N r) :=
  historySpace_norm_sq_eq_fibre_coarea N (predictableDrift N)
    (predictableDrift_mem_historySpace N)


/-- Literal signed residue moment divided by its physical chronological fibre
mass.  It is used only at representatives below the relevant clock. -/
def weightedResidueQuotient (n L r : ℕ) : ℝ :=
  (∑' j : ℕ, cellWeight j * ((historyFibre L r).indicator (residue n) j)) /
    cellMeasure.real (historyFibre L r)

private theorem ae_eq_cell_point {f g : ℕ → ℝ} (h : f =ᵐ[cellMeasure] g) (j : ℕ) : f j = g j := by
  apply (ae_iff_of_countable.mp h) j
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change ENNReal.ofReal (cellWeight j) ≠ 0
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by unfold cellWeight; positivity))

/-- Pointwise source formula for a chronological projection. -/
theorem historyProjection_apply_eq_weightedResidueQuotient (n L j : ℕ) :
    ((historySpace L).starProjection (residueVec n)) j =
      weightedResidueQuotient n L (j % clock L) := by
  obtain ⟨h, hh, hpoint, hquot⟩ :=
    exists_historyProjection_eq_weighted_residue_quotient n L
  rw [hpoint j, hquot (j % clock L) (Nat.mod_lt _ (clock_pos L))]
  rfl

/-- Scalar chronological projections retain the same pointwise signed quotient. -/
theorem smul_historyProjection_apply_eq_weightedResidueQuotient
    (c : ℝ) (n L j : ℕ) :
    (c • (historySpace L).starProjection (residueVec n)) j =
      c * weightedResidueQuotient n L (j % clock L) := by
  apply ae_eq_cell_point
  filter_upwards [Lp.coeFn_smul c ((historySpace L).starProjection (residueVec n))] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul,
    historyProjection_apply_eq_weightedResidueQuotient]

/-- Pointwise signed residue-quotient expansion of the entire predictable drift. -/
theorem predictableDrift_apply_eq_weightedResidueQuotient_sum (N j : ℕ) :
    predictableDrift N j = ∑ i ∈ range N,
      ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
        weightedResidueQuotient (i + 1) i (j % clock i) := by
  have hae : (predictableDrift N : ℕ → ℝ) =ᵐ[cellMeasure]
      fun x => ∑ i ∈ range N,
        (((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) •
          (historySpace i).starProjection (residueVec (i + 1))) x := by
    simpa only [predictableDrift] using
      (Lp.coeFn_fun_finsetSum (range N) fun i =>
        ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) •
          (historySpace i).starProjection (residueVec (i + 1)))
  calc
    predictableDrift N j = ∑ i ∈ range N,
        (((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) •
          (historySpace i).starProjection (residueVec (i + 1))) j :=
      ae_eq_cell_point hae j
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      exact smul_historyProjection_apply_eq_weightedResidueQuotient _ _ _ _

/-- Refined-clock fibre evaluation of the predictable drift. -/
theorem predictableDrift_apply_on_historyFibre (N r j : ℕ)
    (hj : j ∈ historyFibre N r) :
    predictableDrift N j = ∑ i ∈ range N,
      ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
        weightedResidueQuotient (i + 1) i (r % clock i) := by
  rw [predictableDrift_apply_eq_weightedResidueQuotient_sum]
  apply sum_congr rfl
  intro i hi
  congr 2
  rw [historyFibre, Set.mem_setOf_eq] at hj
  calc
    j % clock i = (j % clock N) % clock i :=
      (Nat.mod_mod_of_dvd j (clock_dvd (Nat.le_of_lt (mem_range.mp hi)))).symm
    _ = r % clock i := by rw [hj]


/-- Exact signed physical covariance formula for the complete predictable
Euler-deletion drift. -/
theorem predictableDrift_norm_sq_eq_signedResidueCovariance (N : ℕ) :
    ‖predictableDrift N‖ ^ 2 = ∑ r ∈ range (clock N),
      cellMeasure.real (historyFibre N r) *
        (∑ i ∈ range N, ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
          weightedResidueQuotient (i + 1) i (r % clock i)) ^ 2 := by
  rw [predictableDrift_norm_sq_eq_fibre_coarea]
  apply sum_congr rfl
  intro r hr
  have hmean :
      ∫ j in historyFibre N r, predictableDrift N j ∂cellMeasure =
        cellMeasure.real (historyFibre N r) *
          (∑ i ∈ range N, ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
            weightedResidueQuotient (i + 1) i (r % clock i)) := by
    rw [show (∫ j in historyFibre N r, predictableDrift N j ∂cellMeasure) =
        ∫ j in historyFibre N r,
          (∑ i ∈ range N, ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
            weightedResidueQuotient (i + 1) i (r % clock i)) ∂cellMeasure by
          apply setIntegral_congr_fun (historyFibre_measurable_top N r)
          intro j hj
          exact predictableDrift_apply_on_historyFibre N r j hj]
    simpa only [smul_eq_mul] using
      (setIntegral_const (μ := cellMeasure) (s := historyFibre N r)
        (∑ i ∈ range N, ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
          weightedResidueQuotient (i + 1) i (r % clock i)))
  rw [hmean]
  have hmass : cellMeasure.real (historyFibre N r) ≠ 0 :=
    ne_of_gt (historyFibre_mass_pos N r (mem_range.mp hr))
  field_simp [hmass]

end RHTower.DeletionResidueMartingale
