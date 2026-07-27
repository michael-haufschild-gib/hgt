import GaloisForLFunctions.RHTower.FieldOneFiniteAdeleCompactOpenBasis
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Density of finite-adele Bruhat--Schwartz functions in Haar L²

Regularity of Haar measure approximates every measurable finite-measure set
by compact and open outer/inner approximants.  The compact-open basis of the
rational finite adeles inserts a compact-open set between them, giving
arbitrarily small symmetric difference.

Indicators of compact-open sets are locally constant and compactly
supported, hence are Bruhat--Schwartz functions.  Approximation of
finite-measure indicators, followed by the standard `Lp.induction`, proves
that the algebraic finite-adele Bruhat--Schwartz realization has dense range
in Haar `L²`.

This is an unconditional approximation theorem.  It uses no numerical
computation, trace formula, spectral assertion, Hodge structure, or RH
premise.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal symmDiff

/-- Every measurable finite-Haar-measure subset of the rational finite
adeles can be approximated in symmetric difference by a compact-open set. -/
theorem fieldOneFiniteAdele_exists_compactOpen_symmDiff_lt
    {s : Set FieldOneFiniteAdele}
    (hs : MeasurableSet s)
    (hμs :
      ((fieldOneFiniteAdeleAddHaar :
        Measure FieldOneFiniteAdele) s) ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ C : Set FieldOneFiniteAdele,
      IsCompact C ∧ IsOpen C ∧
        ((fieldOneFiniteAdeleAddHaar :
          Measure FieldOneFiniteAdele) (C ∆ s)) < ε := by
  have hhalf : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  rcases hs.exists_isCompact_diff_lt hμs hhalf with
    ⟨K, hKs, hKc, hμK⟩
  rcases hs.exists_isOpen_diff_lt hμs hhalf with
    ⟨U, hsU, hUo, hμUtop, hμU⟩
  rcases fieldOneFiniteAdele_exists_compactOpen_between
      hKc hUo (hKs.trans hsU) with
    ⟨C, hCc, hCo, hKC, hCU⟩
  refine ⟨C, hCc, hCo, ?_⟩
  rw [measure_symmDiff_eq hCo.nullMeasurableSet
    hs.nullMeasurableSet]
  rw [← ENNReal.add_halves ε]
  exact ENNReal.add_lt_add
    (lt_of_le_of_lt
      (measure_mono (diff_subset_diff_left hCU)) hμU)
    (lt_of_le_of_lt
      (measure_mono (diff_subset_diff_right hKC)) hμK)

/-- The finite-adele Bruhat--Schwartz realization as a complex-linear map. -/
def fieldOneFiniteBruhatToL2Linear :
    FieldOneFiniteBruhatSchwartz →ₗ[ℂ]
      Lp ℂ 2 fieldOneFiniteAdeleAddHaar where
  toFun := fieldOneFiniteBruhatToL2
  map_add' f g := by
    change
      fieldOneFiniteBruhatToL2 (f + g) =
        fieldOneFiniteBruhatToL2 f +
          fieldOneFiniteBruhatToL2 g
    apply Lp.ext
    filter_upwards [
      fieldOneFiniteBruhatToL2_ae (f + g),
      Lp.coeFn_add
        (fieldOneFiniteBruhatToL2 f)
        (fieldOneFiniteBruhatToL2 g),
      fieldOneFiniteBruhatToL2_ae f,
      fieldOneFiniteBruhatToL2_ae g]
      with x hfg hadd hf hg
    rw [hfg, hadd]
    simp only [Pi.add_apply]
    rw [hf, hg]
    simp
  map_smul' c f := by
    change
      fieldOneFiniteBruhatToL2 (c • f) =
        c • fieldOneFiniteBruhatToL2 f
    apply Lp.ext
    filter_upwards [
      fieldOneFiniteBruhatToL2_ae (c • f),
      Lp.coeFn_smul c (fieldOneFiniteBruhatToL2 f),
      fieldOneFiniteBruhatToL2_ae f]
      with x hcf hsmul hf
    rw [hcf, hsmul]
    simp only [Pi.smul_apply]
    rw [hf]
    simp

/-- Locally constant compact-open indicator with arbitrary complex
coefficient. -/
def fieldOneFiniteAdeleCompactOpenIndicatorLocallyConstant
    (C : Set FieldOneFiniteAdele)
    (hCc : IsCompact C) (hCo : IsOpen C) (c : ℂ) :
    LocallyConstant FieldOneFiniteAdele ℂ :=
  (LocallyConstant.const FieldOneFiniteAdele c).indicator
    ⟨hCc.isClosed, hCo⟩

open Classical in
@[simp]
theorem fieldOneFiniteAdeleCompactOpenIndicatorLocallyConstant_apply
    (C : Set FieldOneFiniteAdele)
    (hCc : IsCompact C) (hCo : IsOpen C)
    (c : ℂ) (x : FieldOneFiniteAdele) :
    fieldOneFiniteAdeleCompactOpenIndicatorLocallyConstant
        C hCc hCo c x =
      if x ∈ C then c else 0 := by
  exact LocallyConstant.indicator_apply_eq_if _ _ _

/-- A compact-open indicator has compact support. -/
theorem fieldOneFiniteAdeleCompactOpenIndicator_hasCompactSupport
    (C : Set FieldOneFiniteAdele)
    (hCc : IsCompact C) (hCo : IsOpen C) (c : ℂ) :
    HasCompactSupport
      (fieldOneFiniteAdeleCompactOpenIndicatorLocallyConstant
          C hCc hCo c :
        FieldOneFiniteAdele → ℂ) := by
  classical
  apply HasCompactSupport.of_support_subset_isCompact hCc
  intro x hx
  by_contra hnot
  apply hx
  rw [
    fieldOneFiniteAdeleCompactOpenIndicatorLocallyConstant_apply,
    if_neg hnot]

/-- Compact-open indicators are finite-adele Bruhat--Schwartz functions. -/
def fieldOneFiniteAdeleCompactOpenBruhat
    (C : Set FieldOneFiniteAdele)
    (hCc : IsCompact C) (hCo : IsOpen C) (c : ℂ) :
    FieldOneFiniteBruhatSchwartz :=
  ⟨fieldOneFiniteAdeleCompactOpenIndicatorLocallyConstant C hCc hCo c,
    fieldOneFiniteAdeleCompactOpenIndicator_hasCompactSupport
      C hCc hCo c⟩

/-- The Bruhat--Schwartz compact-open indicator realizes the canonical `Lp`
indicator exactly. -/
theorem fieldOneFiniteAdeleCompactOpenBruhatToL2_eq_indicator
    (C : Set FieldOneFiniteAdele)
    (hCc : IsCompact C) (hCo : IsOpen C) (c : ℂ) :
    fieldOneFiniteBruhatToL2Linear
        (fieldOneFiniteAdeleCompactOpenBruhat C hCc hCo c) =
      indicatorConstLp 2 hCo.measurableSet
        hCc.measure_lt_top.ne c := by
  change
    fieldOneFiniteBruhatToL2
        (fieldOneFiniteAdeleCompactOpenBruhat C hCc hCo c) =
      indicatorConstLp 2 hCo.measurableSet
        hCc.measure_lt_top.ne c
  apply Lp.ext
  filter_upwards [
    fieldOneFiniteBruhatToL2_ae
      (fieldOneFiniteAdeleCompactOpenBruhat C hCc hCo c),
    indicatorConstLp_coeFn
      (p := 2) (μ := fieldOneFiniteAdeleAddHaar)
      (hs := hCo.measurableSet)
      (hμs := hCc.measure_lt_top.ne) (c := c)]
      with x hleft hright
  rw [hleft, hright]
  by_cases hx : x ∈ C <;>
    simp [
      fieldOneFiniteAdeleCompactOpenBruhat,
      fieldOneFiniteAdeleCompactOpenIndicatorLocallyConstant_apply,
      hx]

/-- Every finite-measure indicator lies in the closure of the finite-adele
Bruhat--Schwartz image. -/
theorem fieldOneFiniteAdele_indicatorConstLp_mem_bruhatClosure
    (c : ℂ) {s : Set FieldOneFiniteAdele}
    (hs : MeasurableSet s)
    (hμs :
      ((fieldOneFiniteAdeleAddHaar :
        Measure FieldOneFiniteAdele) s) ≠ ∞) :
    indicatorConstLp 2 hs hμs c ∈
      (LinearMap.range fieldOneFiniteBruhatToL2Linear).topologicalClosure := by
  change
    indicatorConstLp 2 hs hμs c ∈
      ((LinearMap.range
        fieldOneFiniteBruhatToL2Linear).topologicalClosure :
        Set (Lp ℂ 2 fieldOneFiniteAdeleAddHaar))
  rw [Submodule.topologicalClosure_coe]
  apply EMetric.mem_closure_iff.2
  intro ε hε
  by_cases hεtop : ε = ∞
  · refine ⟨0, SetLike.coe_mem 0, ?_⟩
    rw [hεtop]
    exact edist_lt_top _ _
  have hhalf : ε / 2 ≠ 0 :=
    (ENNReal.half_pos hε.ne').ne'
  obtain ⟨η, hηpos, hηbound⟩ :=
    exists_eLpNorm_indicator_le
      (α := FieldOneFiniteAdele)
      (E := ℂ) (p := 2)
      (μ := fieldOneFiniteAdeleAddHaar)
      (by norm_num) c hhalf
  rcases fieldOneFiniteAdele_exists_compactOpen_symmDiff_lt
      hs hμs (ε := (η : ℝ≥0∞))
      (ENNReal.coe_ne_zero.mpr hηpos.ne') with
    ⟨C, hCc, hCo, hμC⟩
  let g := fieldOneFiniteAdeleCompactOpenBruhat C hCc hCo c
  refine
    ⟨fieldOneFiniteBruhatToL2Linear g, ⟨g, rfl⟩, ?_⟩
  rw [fieldOneFiniteAdeleCompactOpenBruhatToL2_eq_indicator]
  rw [edist_indicatorConstLp_eq_enorm]
  calc
    ‖indicatorConstLp 2
        (hs.symmDiff hCo.measurableSet)
        (by
          rw [symmDiff_comm]
          exact (hμC.trans ENNReal.coe_lt_top).ne) c‖ₑ =
        eLpNorm ((s ∆ C).indicator fun _ => c) 2
          fieldOneFiniteAdeleAddHaar := by
      rw [indicatorConstLp, Lp.enorm_toLp]
    _ ≤ ε / 2 := hηbound _ (by
      rw [symmDiff_comm]
      exact hμC.le)
    _ < ε := ENNReal.half_lt_self hε.ne' hεtop

/-- Finite-adele Bruhat--Schwartz functions are dense in Haar `L²`. -/
theorem fieldOneFiniteBruhatToL2Linear_denseRange :
    DenseRange fieldOneFiniteBruhatToL2Linear := by
  let S :
      Submodule ℂ (Lp ℂ 2 fieldOneFiniteAdeleAddHaar) :=
    LinearMap.range fieldOneFiniteBruhatToL2Linear
  have hall :
      ∀ f : Lp ℂ 2 fieldOneFiniteAdeleAddHaar,
        f ∈ S.topologicalClosure := by
    intro f
    apply Lp.induction
      (p := 2) (μ := fieldOneFiniteAdeleAddHaar)
      (motive := fun u => u ∈ S.topologicalClosure)
      (by norm_num)
    · intro c s hs hμs
      simpa only [Lp.simpleFunc.coe_indicatorConst, S] using
        fieldOneFiniteAdele_indicatorConstLp_mem_bruhatClosure
          c hs hμs.ne
    · intro u v hu hv huv hu' hv'
      exact S.topologicalClosure.add_mem hu' hv'
    · exact Submodule.isClosed_topologicalClosure S
  have htop : S.topologicalClosure = ⊤ :=
    eq_top_iff.mpr (fun f _ => hall f)
  rw [denseRange_iff_closure_range]
  simpa only [S, Submodule.topologicalClosure_coe,
    Submodule.top_coe] using
    congrArg
      (fun U :
        Submodule ℂ (Lp ℂ 2 fieldOneFiniteAdeleAddHaar) =>
        (U : Set (Lp ℂ 2 fieldOneFiniteAdeleAddHaar)))
      htop

end

end GaloisForLFunctions.RHTower
