import GaloisForLFunctions.HTGeometry.StratifiedParametricAvoidance
import GaloisForLFunctions.HTGeometry.SmoothAffineControlFamily
import GaloisForLFunctions.HTGeometry.PrevalentSets
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Stratified parametric avoidance holds almost surely, not merely densely

The parametric transversality estimate bounds the Hausdorff dimension of the bad parameter set by
one less than the dimension of the parameter space.  Over a Euclidean parameter block that upgrades
Baire genericity to a measure statement: the bad set is Lebesgue null, hence null for every
absolutely continuous parameter law.  This is what turns a residual avoidance phase into a
prevalent one.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-- **The bad parameter set of a stratified parametric family is Lebesgue null.**  Its Hausdorff
dimension is at most one less than the dimension of the parameter block. -/
theorem volume_parameter_preimage_finite_stratification_eq_zero
    {d : ℕ} {H Y : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (F : (Fin d → ℝ) × H → Y) (bad : Set Y) (c : ℕ) (U K : Set H)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Set.univ ×ˢ U))
    (hparameter : ∀ p h, h ∈ U → Function.Surjective (fderiv ℝ (fun v => F (v, h)) p))
    (hstrata : FiniteRegularStratification bad c)
    (hdim : Module.finrank ℝ H < c) :
    volume {p : Fin d → ℝ | ∃ h ∈ K, F (p, h) ∈ bad} = 0 := by
  classical
  set B : Set (Fin d → ℝ) := {p | ∃ h ∈ K, F (p, h) ∈ bad} with hB
  rcases Set.eq_empty_or_nonempty B with hBe | hBne
  · rw [hBe]; simp
  · obtain ⟨p, h, hhK, hhbad⟩ := hBne
    have hcover := hhbad
    rw [hstrata.cover] at hcover
    obtain ⟨i, hi⟩ := mem_iUnion.mp hcover
    have hPpos : 0 < Module.finrank ℝ (Fin d → ℝ) :=
      parameter_finrank_pos_of_hits_regular_stratum
        F U hU hF hparameter (hstrata.regular i) hdim p h (hKU hhK) hi
    have hrank : Module.finrank ℝ (Fin d → ℝ) = d := Module.finrank_fin_fun ℝ
    have hdpos : 0 < d := by rwa [hrank] at hPpos
    have hdimB : dimH B ≤ ((Module.finrank ℝ (Fin d → ℝ) - 1 : ℕ) : ℝ≥0∞) :=
      dimH_parameter_preimage_finite_stratification_le_pred
        F U K hU hKU hF hparameter hstrata hdim
    have hlt : dimH B < ((d : ℝ≥0) : ℝ≥0∞) := by
      refine lt_of_le_of_lt hdimB ?_
      rw [hrank]
      have : ((d - 1 : ℕ) : ℝ≥0∞) < (d : ℝ≥0∞) := by
        exact_mod_cast Nat.sub_lt hdpos (by omega : 0 < 1)
      simpa using this
    have habs : (volume : Measure (Fin d → ℝ)) ≪ μH[((d : ℝ≥0) : ℝ)] := by
      have hpi : (μH[(Fintype.card (Fin d) : ℝ)] : Measure (Fin d → ℝ)) = volume :=
        hausdorffMeasure_pi_real
      have hcard : (Fintype.card (Fin d) : ℝ) = ((d : ℝ≥0) : ℝ) := by
        simp
      rw [hcard] at hpi
      rw [← hpi]
    exact measure_zero_of_dimH_lt habs hlt

/-- **Every absolutely continuous parameter law misses the bad set almost surely.** -/
theorem measure_parameter_preimage_finite_stratification_eq_zero
    {d : ℕ} {H Y : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (F : (Fin d → ℝ) × H → Y) (bad : Set Y) (c : ℕ) (U K : Set H)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Set.univ ×ˢ U))
    (hparameter : ∀ p h, h ∈ U → Function.Surjective (fderiv ℝ (fun v => F (v, h)) p))
    (hstrata : FiniteRegularStratification bad c)
    (hdim : Module.finrank ℝ H < c)
    (μ : Measure (Fin d → ℝ)) (hμ : μ ≪ volume) :
    μ {p : Fin d → ℝ | ∃ h ∈ K, F (p, h) ∈ bad} = 0 :=
  hμ (volume_parameter_preimage_finite_stratification_eq_zero F bad c U K hU hKU hF hparameter
    hstrata hdim)

/-- **Compact-patch avoidance has probability one.**  For every absolutely continuous parameter law
the family avoids the bad set on the whole compact patch almost surely. -/
theorem measure_compactConfigurationAvoidance_eq_one
    {d : ℕ} {H Y : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (F : (Fin d → ℝ) × H → Y) (bad : Set Y) (c : ℕ) (U K : Set H)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Set.univ ×ˢ U))
    (hparameter : ∀ p h, h ∈ U → Function.Surjective (fderiv ℝ (fun v => F (v, h)) p))
    (hstrata : FiniteRegularStratification bad c)
    (hdim : Module.finrank ℝ H < c)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (hμ : μ ≪ volume) :
    μ (compactConfigurationAvoidance F bad K) = 1 := by
  set B : Set (Fin d → ℝ) := {p | ∃ h ∈ K, F (p, h) ∈ bad} with hB
  have hzero : μ B = 0 :=
    measure_parameter_preimage_finite_stratification_eq_zero F bad c U K hU hKU hF hparameter
      hstrata hdim μ hμ
  have havoidEq : compactConfigurationAvoidance F bad K = Bᶜ := by
    ext p
    simp only [compactConfigurationAvoidance, hB, mem_setOf_eq, mem_compl_iff]
    push Not
    rfl
  rw [havoidEq]
  have hone : μ Bᶜ ≤ 1 := by
    have := measure_mono (μ := μ) (Set.subset_univ Bᶜ)
    rwa [measure_univ] at this
  refine le_antisymm hone ?_
  have hsub : (1 : ℝ≥0∞) ≤ μ B + μ Bᶜ := by
    have := measure_union_le (μ := μ) B Bᶜ
    rw [Set.union_compl_self, measure_univ] at this
    exact this
  rw [hzero, zero_add] at hsub
  exact hsub

/-- **Almost-sure compact-patch avoidance for a finite affine probe.**  If the probe operator is
onto at every configuration of the patch and the bad set is a finite regular stratification of
codimension larger than the patch dimension, then every absolutely continuous probe law avoids the
bad set on the whole patch with probability one. -/
theorem measure_compactConfigurationAvoidance_smoothAffineControlFamily_eq_one
    {d : ℕ} {H Y : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (base : H → Y) (direction : H → ((Fin d → ℝ) →L[ℝ] Y))
    (bad : Set Y) (c : ℕ) (U K : Set H)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hbase : ContDiffOn ℝ (⊤ : ℕ∞) base U)
    (hdirection : ContDiffOn ℝ (⊤ : ℕ∞) direction U)
    (hDirection : ∀ h ∈ U, Function.Surjective (direction h))
    (hstrata : FiniteRegularStratification bad c)
    (hdim : Module.finrank ℝ H < c)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (hμ : μ ≪ volume) :
    μ (compactConfigurationAvoidance (smoothAffineControlFamily base direction) bad K) = 1 :=
  measure_compactConfigurationAvoidance_eq_one
    (smoothAffineControlFamily base direction) bad c U K hU hKU
    (contDiffOn_smoothAffineControlFamily hbase hdirection)
    (fun p h hh => by
      rw [fderiv_smoothAffineControlFamily_probe]
      exact hDirection h hh)
    hstrata hdim μ hμ

/-- **The compact-patch avoidance phase is prevalent.**  One finite-block probe, pushed into the
ambient perturbation space by a controllable linear parametrization, makes the avoidance phase full
after *every* deterministic recentring — the probe does not depend on the centre. -/
theorem prevalent_compactConfigurationAvoidance
    {d : ℕ} {X H Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (l : (Fin d → ℝ) →L[ℝ] X)
    (base : H → Y) (direction : H → (X →L[ℝ] Y))
    (bad : Set Y) (c : ℕ) (U K : Set H)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hbase : ContDiffOn ℝ (⊤ : ℕ∞) base U)
    (hdirection : ContDiffOn ℝ (⊤ : ℕ∞) direction U)
    (hDirection : ∀ h ∈ U, Function.Surjective ((direction h).comp l))
    (hstrata : FiniteRegularStratification bad c)
    (hdim : Module.finrank ℝ H < c)
    (P : CompactProbe (Fin d → ℝ)) (hP : P.measure ≪ volume)
    (hA : MeasurableSet
      (compactConfigurationAvoidance (smoothAffineControlFamily base direction) bad K)) :
    Prevalent
      (compactConfigurationAvoidance (smoothAffineControlFamily base direction) bad K) := by
  classical
  set A := compactConfigurationAvoidance (smoothAffineControlFamily base direction) bad K with hAdef
  refine ⟨P.map l l.continuous l.continuous.measurable, fun center _ => ?_⟩
  have hmeas : MeasurableSet {w : X | center + w ∉ A} :=
    (hA.compl).preimage (measurable_const_add center)
  rw [CompactProbe.map_measure, Measure.map_apply l.continuous.measurable hmeas]
  have hbase' : ContDiffOn ℝ (⊤ : ℕ∞) (fun h => base h + direction h center) U :=
    hbase.add (hdirection.clm_apply contDiffOn_const)
  have hcompL : ContDiff ℝ (⊤ : ℕ∞)
      (fun T : X →L[ℝ] Y => T.comp l) := by
    exact ((ContinuousLinearMap.compL ℝ (Fin d → ℝ) X Y).flip l).contDiff
  have hdirection' : ContDiffOn ℝ (⊤ : ℕ∞) (fun h => (direction h).comp l) U :=
    hcompL.comp_contDiffOn hdirection
  have hpre : l ⁻¹' {w : X | center + w ∉ A}
      = {p : Fin d → ℝ | ∃ h ∈ K, smoothAffineControlFamily
          (fun h => base h + direction h center) (fun h => (direction h).comp l) (p, h) ∈ bad} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hAdef, compactConfigurationAvoidance,
      smoothAffineControlFamily, ContinuousLinearMap.coe_comp, Function.comp_apply]
    push Not
    constructor
    · rintro ⟨h, hhK, hhbad⟩
      refine ⟨h, hhK, ?_⟩
      have hval : base h + direction h (center + l p) = base h + direction h center
          + direction h (l p) := by rw [map_add]; abel
      rwa [hval] at hhbad
    · rintro ⟨h, hhK, hhbad⟩
      refine ⟨h, hhK, ?_⟩
      have hval : base h + direction h (center + l p) = base h + direction h center
          + direction h (l p) := by rw [map_add]; abel
      rwa [hval]
  rw [hpre]
  exact measure_parameter_preimage_finite_stratification_eq_zero
    (smoothAffineControlFamily (fun h => base h + direction h center)
      (fun h => (direction h).comp l)) bad c U K hU hKU
    (contDiffOn_smoothAffineControlFamily hbase' hdirection')
    (fun p h hh => by
      rw [fderiv_smoothAffineControlFamily_probe]
      exact hDirection h hh)
    hstrata hdim P.measure hP

/-! ### Finite probe parametrizations -/

/-- The linear parametrization of a finite family of perturbation directions. -/
def blockCLM {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X] {d : ℕ} (v : Fin d → X) :
    (Fin d → ℝ) →L[ℝ] X :=
  ∑ k, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k).smulRight (v k)

@[simp] theorem blockCLM_apply {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X] {d : ℕ}
    (v : Fin d → X) (p : Fin d → ℝ) : blockCLM v p = ∑ k, p k • v k := by
  simp [blockCLM]

/-- A probe family that controls the target through one continuous linear map gives a surjective
composite. -/
theorem surjective_comp_blockCLM {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y] {d : ℕ} (T : X →L[ℝ] Y) (v : Fin d → X)
    (h : ∀ y : Y, ∃ c : Fin d → ℝ, T (∑ k, c k • v k) = y) :
    Function.Surjective (T.comp (blockCLM v)) := by
  intro y
  obtain ⟨c, hc⟩ := h y
  exact ⟨c, by simpa using hc⟩

/-- A probe spanning a submodule on which the control is onto gives a surjective composite. -/
theorem surjective_comp_blockCLM_of_domRestrict {X Y : Type*} [SeminormedAddCommGroup X]
    [NormedSpace ℝ X] [SeminormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y)
    {V : Submodule ℝ X} {d : ℕ} (v : Fin d → X) (hv : Submodule.span ℝ (Set.range v) = V)
    (h : Function.Surjective (T.domRestrict V)) :
    Function.Surjective (T.comp (blockCLM v)) := by
  refine surjective_comp_blockCLM T v fun y => ?_
  obtain ⟨x, hx⟩ := h y
  have hxV : (x : X) ∈ Submodule.span ℝ (Set.range v) := by rw [hv]; exact x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hxV
  exact ⟨c, by rw [hc]; exact hx⟩

/-- A finitely generated submodule carries a finite probe parametrization. -/
theorem exists_blockCLM_of_fg {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    {V : Submodule ℝ X} (hV : V.FG) :
    ∃ (d : ℕ) (v : Fin d → X), Submodule.span ℝ (Set.range v) = V :=
  Submodule.fg_iff_exists_fin_generating_family.1 hV

/-- Enlarging a probe family preserves controllability. -/
theorem surjective_comp_blockCLM_mono {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) {d d' : ℕ}
    (v : Fin d → X) (v' : Fin d' → X)
    (hsub : Set.range v ⊆ Submodule.span ℝ (Set.range v'))
    (h : Function.Surjective (T.comp (blockCLM v))) :
    Function.Surjective (T.comp (blockCLM v')) := by
  refine surjective_comp_blockCLM T v' fun y => ?_
  obtain ⟨c, hc⟩ := h y
  have hx : (∑ k, c k • v k) ∈ Submodule.span ℝ (Set.range v') := by
    have : Submodule.span ℝ (Set.range v) ≤ Submodule.span ℝ (Set.range v') :=
      Submodule.span_le.2 hsub
    exact this ((Submodule.mem_span_range_iff_exists_fun ℝ).2 ⟨c, rfl⟩)
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
  refine ⟨c', ?_⟩
  rw [hc']
  simpa using hc

/-- Concatenate finitely many finite probe families into one. -/
noncomputable def concatBlock {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} {d : Fin n → ℕ}
    (v : ∀ j, Fin (d j) → X) : Fin (Fintype.card (Σ j, Fin (d j))) → X :=
  fun k =>
    let p := (Fintype.equivFin (Σ j, Fin (d j))).symm k
    v p.1 p.2

theorem mem_range_concatBlock {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}
    {d : Fin n → ℕ} (v : ∀ j, Fin (d j) → X) (j : Fin n) (k : Fin (d j)) :
    v j k ∈ Set.range (concatBlock v) :=
  ⟨Fintype.equivFin (Σ j, Fin (d j)) ⟨j, k⟩, by
    have hsym : (Fintype.equivFin (Σ j, Fin (d j))).symm
        ((Fintype.equivFin (Σ j, Fin (d j))) ⟨j, k⟩) = ⟨j, k⟩ := Equiv.symm_apply_apply _ _
    simp only [concatBlock]
    rw [hsym]⟩

/-- **The concatenated probe controls every block.** -/
theorem surjective_comp_concatBlock {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) {n : ℕ} {d : Fin n → ℕ}
    (v : ∀ j, Fin (d j) → X) (j : Fin n)
    (h : Function.Surjective (T.comp (blockCLM (v j)))) :
    Function.Surjective (T.comp (blockCLM (concatBlock v))) := by
  refine surjective_comp_blockCLM_mono T (v j) (concatBlock v) ?_ h
  rintro y ⟨k, rfl⟩
  exact Submodule.subset_span (mem_range_concatBlock v j k)

/-- **The recentred bad set is null for every absolutely continuous probe law.**  This is the
probe-level form of prevalence: no measurable structure on the ambient perturbation space is
needed, because the law lives on the Euclidean block and the recentring is deterministic. -/
theorem measure_recentred_parameter_bad_eq_zero
    {d : ℕ} {X H Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (l : (Fin d → ℝ) →L[ℝ] X)
    (base : H → Y) (direction : H → (X →L[ℝ] Y))
    (bad : Set Y) (c : ℕ) (U K : Set H)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hbase : ContDiffOn ℝ (⊤ : ℕ∞) base U)
    (hdirection : ContDiffOn ℝ (⊤ : ℕ∞) direction U)
    (hDirection : ∀ h ∈ U, Function.Surjective ((direction h).comp l))
    (hstrata : FiniteRegularStratification bad c)
    (hdim : Module.finrank ℝ H < c)
    (P : Measure (Fin d → ℝ)) (hP : P ≪ volume) (center : X) :
    P {p : Fin d → ℝ | ∃ h ∈ K,
      smoothAffineControlFamily base direction (center + l p, h) ∈ bad} = 0 := by
  have hbase' : ContDiffOn ℝ (⊤ : ℕ∞) (fun h => base h + direction h center) U :=
    hbase.add (hdirection.clm_apply contDiffOn_const)
  have hcompL : ContDiff ℝ (⊤ : ℕ∞) (fun T : X →L[ℝ] Y => T.comp l) :=
    ((ContinuousLinearMap.compL ℝ (Fin d → ℝ) X Y).flip l).contDiff
  have hdirection' : ContDiffOn ℝ (⊤ : ℕ∞) (fun h => (direction h).comp l) U :=
    hcompL.comp_contDiffOn hdirection
  have hset : {p : Fin d → ℝ | ∃ h ∈ K,
      smoothAffineControlFamily base direction (center + l p, h) ∈ bad}
      = {p : Fin d → ℝ | ∃ h ∈ K, smoothAffineControlFamily
          (fun h => base h + direction h center) (fun h => (direction h).comp l) (p, h) ∈ bad} := by
    ext p
    simp only [Set.mem_setOf_eq, smoothAffineControlFamily, ContinuousLinearMap.coe_comp,
      Function.comp_apply]
    constructor
    · rintro ⟨h, hhK, hhbad⟩
      refine ⟨h, hhK, ?_⟩
      have hval : base h + direction h (center + l p) = base h + direction h center
          + direction h (l p) := by rw [map_add]; abel
      rwa [hval] at hhbad
    · rintro ⟨h, hhK, hhbad⟩
      refine ⟨h, hhK, ?_⟩
      have hval : base h + direction h (center + l p) = base h + direction h center
          + direction h (l p) := by rw [map_add]; abel
      rwa [hval]
  rw [hset]
  exact measure_parameter_preimage_finite_stratification_eq_zero
    (smoothAffineControlFamily (fun h => base h + direction h center)
      (fun h => (direction h).comp l)) bad c U K hU hKU
    (contDiffOn_smoothAffineControlFamily hbase' hdirection')
    (fun p h hh => by
      rw [fderiv_smoothAffineControlFamily_probe]
      exact hDirection h hh)
    hstrata hdim P hP

end GaloisForLFunctions.HTGeometry
