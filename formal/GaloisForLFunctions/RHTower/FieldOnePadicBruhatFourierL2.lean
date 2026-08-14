import GaloisForLFunctions.RHTower.FieldOnePadicBruhatFourierInversion
import GaloisForLFunctions.RHTower.DeningerLocallyConstantApproximation
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Literal p-adic Bruhat density and the L² Fourier unitary

Compactly supported locally constant functions on `ℚ_p` are dense in Haar
`L²`. The exact Bruhat Plancherel and inversion theorems therefore extend
the literal integral transform uniquely to a unitary of the whole `L²`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal symmDiff ComplexConjugate

variable (p : ℕ) [Fact p.Prime]

abbrev FieldOnePadicL2 :=
  Lp ℂ 2 (fieldOnePadicUnitBallNormalizedHaar p)

theorem fieldOnePadicBruhat_memLp
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    MemLp (f.1 : ℚ_[p] → ℂ) 2
      (fieldOnePadicUnitBallNormalizedHaar p) :=
  f.1.continuous.memLp_of_hasCompactSupport f.2

def fieldOnePadicBruhatToL2
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    FieldOnePadicL2 p :=
  (fieldOnePadicBruhat_memLp p f).toLp f.1

theorem fieldOnePadicBruhatToL2_ae
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    (fieldOnePadicBruhatToL2 p f : ℚ_[p] → ℂ) =ᵐ[
      fieldOnePadicUnitBallNormalizedHaar p] f.1 :=
  (fieldOnePadicBruhat_memLp p f).coeFn_toLp

def fieldOnePadicBruhatToL2Linear :
    compactlySupportedLocallyConstant ℚ_[p] →ₗ[ℂ]
      FieldOnePadicL2 p where
  toFun := fieldOnePadicBruhatToL2 p
  map_add' f g := by
    exact MemLp.toLp_add
      (fieldOnePadicBruhat_memLp p f)
      (fieldOnePadicBruhat_memLp p g)
  map_smul' c f := by
    exact MemLp.toLp_const_smul c (fieldOnePadicBruhat_memLp p f)

theorem fieldOnePadicBruhatToL2Linear_injective :
    Function.Injective (fieldOnePadicBruhatToL2Linear p) := by
  intro f g hfg
  apply Subtype.ext
  apply LocallyConstant.ext
  have hcoe :
      ((fieldOnePadicBruhatToL2Linear p f : FieldOnePadicL2 p) :
          ℚ_[p] → ℂ) =
        ((fieldOnePadicBruhatToL2Linear p g : FieldOnePadicL2 p) :
          ℚ_[p] → ℂ) :=
    congrArg (fun h : FieldOnePadicL2 p => (h : ℚ_[p] → ℂ)) hfg
  have hae : (f.1 : ℚ_[p] → ℂ) =ᵐ[
      fieldOnePadicUnitBallNormalizedHaar p] g.1 :=
    let hemb :
        ((fieldOnePadicBruhatToL2Linear p f : FieldOnePadicL2 p) :
            ℚ_[p] → ℂ) =ᵐ[fieldOnePadicUnitBallNormalizedHaar p]
          ((fieldOnePadicBruhatToL2Linear p g : FieldOnePadicL2 p) :
            ℚ_[p] → ℂ) :=
      Filter.Eventually.of_forall fun x => congrFun hcoe x
    (fieldOnePadicBruhatToL2_ae p f).symm.trans
      (hemb.trans (fieldOnePadicBruhatToL2_ae p g))
  exact congrFun ((Continuous.ae_eq_iff_eq
    (fieldOnePadicUnitBallNormalizedHaar p)
    f.1.continuous g.1.continuous).mp hae)

theorem fieldOnePadic_compactOpen_basis :
    IsTopologicalBasis
      {s : Set ℚ_[p] | IsCompact s ∧ IsOpen s} := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro s hs
    exact hs.2
  · intro x U hxU hU
    obtain ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset hU hxU
    obtain ⟨V, hVcl, hxV, hVK⟩ :=
      loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1
        (isOpen_interior.mem_nhds hxK)
    refine ⟨V, ⟨?_, hVcl.2⟩, hxV,
      (hVK.trans interior_subset).trans hKU⟩
    exact hKc.of_isClosed_subset hVcl.1
      (hVK.trans interior_subset)

theorem fieldOnePadic_exists_compactOpen_between
    {K U : Set ℚ_[p]} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ C : Set ℚ_[p],
      IsCompact C ∧ IsOpen C ∧ K ⊆ C ∧ C ⊆ U := by
  choose V hV using fun (x : K) =>
    fieldOnePadic_compactOpen_basis p |>.mem_nhds_iff.1
      (hU.mem_nhds (hKU x.property))
  have hcover : K ⊆ ⋃ x : K, V x := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, (hV ⟨x, hx⟩).2.1⟩
  choose I hI using hK.elim_finite_subcover V
    (fun x => (hV x).1.2) hcover
  refine ⟨⋃ x ∈ I, V x,
    I.isCompact_biUnion (fun x _ => (hV x).1.1),
    isOpen_biUnion (fun x _ => (hV x).1.2), hI, ?_⟩
  exact iUnion₂_subset fun x _ => (hV x).2.2

theorem fieldOnePadic_exists_compactOpen_symmDiff_lt
    {s : Set ℚ_[p]} (hs : MeasurableSet s)
    (hμs : fieldOnePadicUnitBallNormalizedHaar p s ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ C : Set ℚ_[p], IsCompact C ∧ IsOpen C ∧
      fieldOnePadicUnitBallNormalizedHaar p (C ∆ s) < ε := by
  have hhalf : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  rcases hs.exists_isCompact_sdiff_lt hμs hhalf with
    ⟨K, hKs, hKc, hμK⟩
  rcases hs.exists_isOpen_sdiff_lt hμs hhalf with
    ⟨U, hsU, hUo, _hμUtop, hμU⟩
  rcases fieldOnePadic_exists_compactOpen_between p hKc hUo
      (hKs.trans hsU) with ⟨C, hCc, hCo, hKC, hCU⟩
  refine ⟨C, hCc, hCo, ?_⟩
  rw [measure_symmDiff_eq hCo.nullMeasurableSet hs.nullMeasurableSet]
  rw [← ENNReal.add_halves ε]
  exact ENNReal.add_lt_add
    (lt_of_le_of_lt (measure_mono (sdiff_subset_sdiff_left hCU)) hμU)
    (lt_of_le_of_lt (measure_mono (sdiff_subset_sdiff_right hKC)) hμK)

def fieldOnePadicCompactOpenIndicatorLocallyConstant
    (C : Set ℚ_[p]) (hCc : IsCompact C) (hCo : IsOpen C) (c : ℂ) :
    LocallyConstant ℚ_[p] ℂ :=
  (LocallyConstant.const ℚ_[p] c).indicator ⟨hCc.isClosed, hCo⟩

open Classical in
@[simp] theorem fieldOnePadicCompactOpenIndicatorLocallyConstant_apply
    (C : Set ℚ_[p]) (hCc : IsCompact C) (hCo : IsOpen C)
    (c : ℂ) (x : ℚ_[p]) :
    fieldOnePadicCompactOpenIndicatorLocallyConstant p C hCc hCo c x =
      if x ∈ C then c else 0 :=
  LocallyConstant.indicator_apply_eq_if _ _ _

theorem fieldOnePadicCompactOpenIndicator_hasCompactSupport
    (C : Set ℚ_[p]) (hCc : IsCompact C) (hCo : IsOpen C) (c : ℂ) :
    HasCompactSupport
      (fieldOnePadicCompactOpenIndicatorLocallyConstant p C hCc hCo c :
        ℚ_[p] → ℂ) := by
  classical
  apply HasCompactSupport.of_support_subset_isCompact hCc
  intro x hx
  by_contra hnot
  apply hx
  rw [fieldOnePadicCompactOpenIndicatorLocallyConstant_apply p,
    if_neg hnot]

def fieldOnePadicCompactOpenBruhat
    (C : Set ℚ_[p]) (hCc : IsCompact C) (hCo : IsOpen C) (c : ℂ) :
    compactlySupportedLocallyConstant ℚ_[p] :=
  ⟨fieldOnePadicCompactOpenIndicatorLocallyConstant p C hCc hCo c,
    fieldOnePadicCompactOpenIndicator_hasCompactSupport p C hCc hCo c⟩

theorem fieldOnePadicCompactOpenBruhatToL2_eq_indicator
    (C : Set ℚ_[p]) (hCc : IsCompact C) (hCo : IsOpen C) (c : ℂ) :
    fieldOnePadicBruhatToL2Linear p
        (fieldOnePadicCompactOpenBruhat p C hCc hCo c) =
      indicatorConstLp 2 hCo.measurableSet hCc.measure_lt_top.ne c := by
  change fieldOnePadicBruhatToL2 p
      (fieldOnePadicCompactOpenBruhat p C hCc hCo c) = _
  apply Lp.ext
  filter_upwards [
    fieldOnePadicBruhatToL2_ae p
      (fieldOnePadicCompactOpenBruhat p C hCc hCo c),
    indicatorConstLp_coeFn (p := 2)
      (μ := fieldOnePadicUnitBallNormalizedHaar p)
      (hs := hCo.measurableSet) (hμs := hCc.measure_lt_top.ne) (c := c)]
      with x hleft hright
  rw [hleft, hright]
  by_cases hx : x ∈ C <;>
    simp [fieldOnePadicCompactOpenBruhat,
      fieldOnePadicCompactOpenIndicatorLocallyConstant_apply, hx]

theorem fieldOnePadic_indicatorConstLp_mem_bruhatClosure
    (c : ℂ) {s : Set ℚ_[p]} (hs : MeasurableSet s)
    (hμs : fieldOnePadicUnitBallNormalizedHaar p s ≠ ∞) :
    indicatorConstLp 2 hs hμs c ∈
      (LinearMap.range (fieldOnePadicBruhatToL2Linear p)).topologicalClosure := by
  change indicatorConstLp 2 hs hμs c ∈
    ((LinearMap.range
      (fieldOnePadicBruhatToL2Linear p)).topologicalClosure :
      Set (FieldOnePadicL2 p))
  rw [Submodule.topologicalClosure_coe]
  apply EMetric.mem_closure_iff.2
  intro ε hε
  by_cases hεtop : ε = ∞
  · refine ⟨0, SetLike.coe_mem 0, ?_⟩
    rw [hεtop]
    exact edist_lt_top _ _
  have hhalf : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  obtain ⟨η, hηpos, hηbound⟩ :=
    exists_eLpNorm_indicator_le
      (α := ℚ_[p]) (E := ℂ) (p := 2)
      (μ := fieldOnePadicUnitBallNormalizedHaar p)
      (by norm_num) c hhalf
  rcases fieldOnePadic_exists_compactOpen_symmDiff_lt p hs hμs
      (ε := (η : ℝ≥0∞)) (ENNReal.coe_ne_zero.mpr hηpos.ne') with
    ⟨C, hCc, hCo, hμC⟩
  let g := fieldOnePadicCompactOpenBruhat p C hCc hCo c
  refine ⟨fieldOnePadicBruhatToL2Linear p g, ⟨g, rfl⟩, ?_⟩
  rw [fieldOnePadicCompactOpenBruhatToL2_eq_indicator]
  rw [edist_indicatorConstLp_eq_enorm]
  calc
    ‖indicatorConstLp 2 (hs.symmDiff hCo.measurableSet)
        (by
          rw [symmDiff_comm]
          exact (hμC.trans ENNReal.coe_lt_top).ne) c‖ₑ =
        eLpNorm ((s ∆ C).indicator fun _ => c) 2
          (fieldOnePadicUnitBallNormalizedHaar p) := by
      rw [indicatorConstLp, Lp.enorm_toLp]
    _ ≤ ε / 2 := hηbound _ (by rw [symmDiff_comm]; exact hμC.le)
    _ < ε := ENNReal.half_lt_self hε.ne' hεtop

theorem fieldOnePadicBruhatToL2Linear_denseRange :
    DenseRange (fieldOnePadicBruhatToL2Linear p) := by
  let S : Submodule ℂ (FieldOnePadicL2 p) :=
    LinearMap.range (fieldOnePadicBruhatToL2Linear p)
  have hall : ∀ f : FieldOnePadicL2 p, f ∈ S.topologicalClosure := by
    intro f
    apply Lp.induction (p := 2)
      (μ := fieldOnePadicUnitBallNormalizedHaar p)
      (motive := fun u => u ∈ S.topologicalClosure) (by norm_num)
    · intro c s hs hμs
      simpa only [Lp.simpleFunc.coe_indicatorConst, S] using
        fieldOnePadic_indicatorConstLp_mem_bruhatClosure p c hs hμs.ne
    · intro u v hu hv huv hu' hv'
      exact S.topologicalClosure.add_mem hu' hv'
    · exact Submodule.isClosed_topologicalClosure S
  have htop : S.topologicalClosure = ⊤ :=
    eq_top_iff.mpr (fun f _ => hall f)
  rw [denseRange_iff_closure_range]
  simpa only [S, Submodule.topologicalClosure_coe, Submodule.top_coe] using!
    congrArg (fun U : Submodule ℂ (FieldOnePadicL2 p) =>
      (U : Set (FieldOnePadicL2 p))) htop

noncomputable instance fieldOnePadicBruhatNormedAddCommGroup :
    NormedAddCommGroup (compactlySupportedLocallyConstant ℚ_[p]) :=
  NormedAddCommGroup.induced
    (compactlySupportedLocallyConstant ℚ_[p]) (FieldOnePadicL2 p)
    (fieldOnePadicBruhatToL2Linear p)
    (fieldOnePadicBruhatToL2Linear_injective p)

noncomputable instance fieldOnePadicBruhatNormedSpace :
    NormedSpace ℂ (compactlySupportedLocallyConstant ℚ_[p]) :=
  NormedSpace.induced ℂ
    (compactlySupportedLocallyConstant ℚ_[p]) (FieldOnePadicL2 p)
    (fieldOnePadicBruhatToL2Linear p)

theorem fieldOnePadicBruhatFourier_l2Norm
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    ‖fieldOnePadicBruhatToL2Linear p
        (fieldOnePadicBruhatFourierLinearEquiv p f)‖ =
      ‖fieldOnePadicBruhatToL2Linear p f‖ := by
  let u := fieldOnePadicBruhatToL2Linear p
    (fieldOnePadicBruhatFourierLinearEquiv p f)
  let v := fieldOnePadicBruhatToL2Linear p f
  have hu : (u : ℚ_[p] → ℂ) =ᵐ[
      fieldOnePadicUnitBallNormalizedHaar p]
      fieldOnePadicBruhatFourier p f := by
    change ((fieldOnePadicBruhatToL2 p
        (fieldOnePadicBruhatFourierLinearEquiv p f) : FieldOnePadicL2 p) :
          ℚ_[p] → ℂ) =ᵐ[fieldOnePadicUnitBallNormalizedHaar p]
      fieldOnePadicBruhatFourier p f
    filter_upwards [fieldOnePadicBruhatToL2_ae p
      (fieldOnePadicBruhatFourierLinearEquiv p f)] with x hx
    rw [hx]
    rfl
  have hv : (v : ℚ_[p] → ℂ) =ᵐ[
      fieldOnePadicUnitBallNormalizedHaar p] f.1 := by
    exact fieldOnePadicBruhatToL2_ae p f
  have husq : ‖u‖ ^ 2 =
      ∫ x, Complex.normSq (fieldOnePadicBruhatFourier p f x)
        ∂fieldOnePadicUnitBallNormalizedHaar p := by
    calc
      ‖u‖ ^ 2 = RCLike.re (inner ℂ u u) :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) u).symm
      _ = RCLike.re (∫ x, inner ℂ (u x) (u x)
          ∂fieldOnePadicUnitBallNormalizedHaar p) := by
        rw [MeasureTheory.L2.inner_def]
      _ = ∫ x, RCLike.re (inner ℂ (u x) (u x))
          ∂fieldOnePadicUnitBallNormalizedHaar p := by
        symm
        exact integral_re (𝕜 := ℂ)
          (MeasureTheory.L2.integrable_inner u u)
      _ = ∫ x, ‖u x‖ ^ 2
          ∂fieldOnePadicUnitBallNormalizedHaar p := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact inner_self_eq_norm_sq (𝕜 := ℂ) (u x)
      _ = ∫ x, Complex.normSq
          (fieldOnePadicBruhatFourier p f x)
          ∂fieldOnePadicUnitBallNormalizedHaar p := by
        apply integral_congr_ae
        filter_upwards [hu] with x hx
        rw [hx, Complex.normSq_eq_norm_sq]
  have hvsq : ‖v‖ ^ 2 = ∫ x, Complex.normSq (f.1 x)
      ∂fieldOnePadicUnitBallNormalizedHaar p := by
    calc
      ‖v‖ ^ 2 = RCLike.re (inner ℂ v v) :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) v).symm
      _ = RCLike.re (∫ x, inner ℂ (v x) (v x)
          ∂fieldOnePadicUnitBallNormalizedHaar p) := by
        rw [MeasureTheory.L2.inner_def]
      _ = ∫ x, RCLike.re (inner ℂ (v x) (v x))
          ∂fieldOnePadicUnitBallNormalizedHaar p := by
        symm
        exact integral_re (𝕜 := ℂ)
          (MeasureTheory.L2.integrable_inner v v)
      _ = ∫ x, ‖v x‖ ^ 2
          ∂fieldOnePadicUnitBallNormalizedHaar p := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact inner_self_eq_norm_sq (𝕜 := ℂ) (v x)
      _ = ∫ x, Complex.normSq (f.1 x)
          ∂fieldOnePadicUnitBallNormalizedHaar p := by
        apply integral_congr_ae
        filter_upwards [hv] with x hx
        rw [hx, Complex.normSq_eq_norm_sq]
  have hsquare : ‖u‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [husq, hvsq]
    exact fieldOnePadicBruhatFourier_plancherel p f
  nlinarith [norm_nonneg u, norm_nonneg v]

/-- Literal p-adic Fourier transform on the whole Haar `L²`. -/
def fieldOnePadicL2Fourier :
    FieldOnePadicL2 p ≃ₗᵢ[ℂ] FieldOnePadicL2 p :=
  (fieldOnePadicBruhatFourierLinearEquiv p).extendOfIsometry
    (fieldOnePadicBruhatToL2Linear p)
    (fieldOnePadicBruhatToL2Linear p)
    (fieldOnePadicBruhatToL2Linear_denseRange p)
    (fieldOnePadicBruhatToL2Linear_denseRange p)
    (fieldOnePadicBruhatFourier_l2Norm p)

@[simp] theorem fieldOnePadicL2Fourier_bruhat
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicL2Fourier p (fieldOnePadicBruhatToL2Linear p f) =
      fieldOnePadicBruhatToL2Linear p
        (fieldOnePadicBruhatFourierLinearEquiv p f) := by
  exact LinearEquiv.extendOfIsometry_eq
    (fieldOnePadicBruhatFourierLinearEquiv p)
    (fieldOnePadicBruhatToL2Linear p)
    (fieldOnePadicBruhatToL2Linear p)
    (fieldOnePadicBruhatToL2Linear_denseRange p)
    (fieldOnePadicBruhatToL2Linear_denseRange p)
    (fieldOnePadicBruhatFourier_l2Norm p) f

end

end GaloisForLFunctions.RHTower

