import GaloisForLFunctions.RHTower.SelbergMaassTraceStokes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Standard area measure on the truncated modular domain

The domain is the actual closed subset of the plane with horizontal coordinates in
`[-1/2,1/2]`, height at most `Y`, and lying above the unit circle. Indicator Fubini
identifies its standard two-dimensional set integral with both slice orders.
Below height one, each horizontal slice is exactly the union of two side intervals;
their possible common endpoint has zero measure.

The geometric argument is adapted from the corpus's actual first-Stokes Fubini
proof. No specialized Eisenstein or unrelated research modules are imported.
-/

open Set Filter Topology MeasureTheory
namespace GaloisForLFunctions.RHTower.SelbergModularDomainSlices
open SelbergMaassTraceStokes
noncomputable section

def arcFloor : ℝ := arcHeight (1 / 2)
def sideRadius (y : ℝ) : ℝ := Real.sqrt (1 - y ^ 2)
def cell (Y : ℝ) : Set (ℝ × ℝ) := Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Icc (1 / 2 : ℝ) Y

theorem continuous_arcHeight : Continuous arcHeight := by unfold arcHeight; fun_prop

theorem arcHeight_le_one {x : ℝ} (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) : arcHeight x ≤ 1 := by
  have h := arcHeight_sq hx
  have h0 := (arcHeight_pos hx).le
  nlinarith [sq_nonneg x]

theorem arcHeight_half_le {x : ℝ} (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    (1 / 2 : ℝ) ≤ arcHeight x := by
  have h := arcHeight_sq hx
  have h0 := (arcHeight_pos hx).le
  nlinarith [hx.1, hx.2, sq_nonneg (x + 1 / 2), sq_nonneg (1 / 2 - x)]

theorem arcFloor_pos : 0 < arcFloor := arcHeight_pos ⟨by norm_num, le_rfl⟩

theorem arcFloor_gt_half : (1 / 2 : ℝ) < arcFloor := by
  have h := arcHeight_sq (x := (1 / 2 : ℝ)) ⟨by norm_num, le_rfl⟩
  change arcFloor ^ 2 = _ at h
  nlinarith [arcFloor_pos]

def domain (Y : ℝ) : Set (ℝ × ℝ) :=
  cell Y ∩
    {w : ℝ × ℝ | arcHeight w.1 ≤ w.2}

theorem isCompact_domain (Y : ℝ) :
    IsCompact (domain Y) := by
  unfold domain cell
  apply (isCompact_Icc.prod isCompact_Icc).inter_right
  exact isClosed_le
    (continuous_arcHeight.comp continuous_fst) continuous_snd

theorem domain_subset_cell (Y : ℝ) :
    domain Y ⊆ cell Y := by
  intro w hw
  exact hw.1

def verticalSlice
    (f : ℝ × ℝ → ℝ) (Y x : ℝ) : ℝ :=
  ∫ y in Set.Icc (arcHeight x) Y, f (x, y)

private theorem integral_indicator_domain_verticalSlice
    (f : ℝ × ℝ → ℝ) (Y x : ℝ) :
    (∫ y, (domain Y).indicator f (x, y)) =
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
        (verticalSlice f Y) x := by
  by_cases hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
  · rw [Set.indicator_of_mem hx]
    have hfun :
        (fun y : ℝ => (domain Y).indicator f (x, y)) =
          (Set.Icc (arcHeight x) Y).indicator (fun y => f (x, y)) := by
      funext y
      by_cases hy : y ∈ Set.Icc (arcHeight x) Y
      · have hyhalf : (1 / 2 : ℝ) ≤ y :=
          (arcHeight_half_le hx).trans hy.1
        have hmem : (x, y) ∈ domain Y := by
          exact ⟨⟨hx, ⟨hyhalf, hy.2⟩⟩, hy.1⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hy]
      · have hnotmem : (x, y) ∉ domain Y := by
          intro hw
          apply hy
          exact ⟨hw.2, hw.1.2.2⟩
        rw [Set.indicator_of_notMem hnotmem, Set.indicator_of_notMem hy]
    rw [hfun, MeasureTheory.integral_indicator measurableSet_Icc]
    rfl
  · rw [Set.indicator_of_notMem hx]
    have hzero :
        (fun y : ℝ => (domain Y).indicator f (x, y)) = 0 := by
      funext y
      have hnotmem : (x, y) ∉ domain Y := by
        intro hw
        exact hx hw.1.1
      rw [Set.indicator_of_notMem hnotmem]
      rfl
    rw [hzero]
    simp

private theorem setIntegral_domain_eq_indicator_prod
    (f : ℝ × ℝ → ℝ) (Y : ℝ) :
    (∫ w in domain Y, f w) =
      ∫ w, (domain Y).indicator f w
        ∂(volume.prod volume) := by
  calc
    (∫ w in domain Y, f w) =
        ∫ w in domain Y, f w ∂(volume.prod volume) := by
      rw [← MeasureTheory.Measure.volume_eq_prod]
    _ = ∫ w, (domain Y).indicator f w
          ∂(volume.prod volume) := by
      rw [MeasureTheory.integral_indicator
        (isCompact_domain Y).measurableSet]

private theorem integral_indicator_domain_eq_iterated
    {f : ℝ × ℝ → ℝ} {Y : ℝ}
    (hf : IntegrableOn f (domain Y)) :
    (∫ w, (domain Y).indicator f w
        ∂(volume.prod volume)) =
      ∫ x, ∫ y, (domain Y).indicator f (x, y) := by
  have hfprod : IntegrableOn f (domain Y)
      (volume.prod volume) := by
    simpa only [← MeasureTheory.Measure.volume_eq_prod] using hf
  have hind := hfprod.integrable_indicator
    (isCompact_domain Y).measurableSet
  exact MeasureTheory.integral_prod
    ((domain Y).indicator f) hind

set_option maxHeartbeats 800000 in
private theorem iterated_indicator_domain_eq_outerIndicator
    (f : ℝ × ℝ → ℝ) (Y : ℝ) :
    (∫ x, ∫ y, (domain Y).indicator f (x, y)) =
      ∫ x, (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
        (verticalSlice f Y) x := by
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall
    (integral_indicator_domain_verticalSlice f Y)

private theorem integral_outerIndicator_domain_eq_setSlices
    (f : ℝ × ℝ → ℝ) (Y : ℝ) :
    (∫ x, (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
        (verticalSlice f Y) x) =
      ∫ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
        verticalSlice f Y x := by
  rw [MeasureTheory.integral_indicator measurableSet_Icc]

private theorem setIntegral_domain_eq_verticalSetSlices
    {f : ℝ × ℝ → ℝ} {Y : ℝ}
    (hf : IntegrableOn f (domain Y)) :
    (∫ w in domain Y, f w) =
      ∫ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
        verticalSlice f Y x := by
  rw [setIntegral_domain_eq_indicator_prod f Y,
    integral_indicator_domain_eq_iterated hf,
    iterated_indicator_domain_eq_outerIndicator f Y,
    integral_outerIndicator_domain_eq_setSlices f Y]

private theorem verticalSetSlices_eq_intervalSlices
    (f : ℝ × ℝ → ℝ) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
        verticalSlice f Y x) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        ∫ y in arcHeight x..Y, f (x, y) := by
  rw [intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro x hx
  have harcleY : arcHeight x ≤ Y :=
    (arcHeight_le_one hx).trans hY
  change (∫ y in Set.Icc (arcHeight x) Y, f (x, y)) =
    ∫ y in arcHeight x..Y, f (x, y)
  rw [intervalIntegral.integral_of_le harcleY,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- Product-measure Fubini on the genuine curved truncated modular domain, in vertical-fibre
coordinates.  This is not a formal iterated-integral definition: the left side is the standard
two-dimensional set integral. -/
theorem setIntegral_eq_vertical
    {f : ℝ × ℝ → ℝ} {Y : ℝ} (hY : 1 ≤ Y)
    (hf : IntegrableOn f (domain Y)) :
    (∫ w in domain Y, f w) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        ∫ y in arcHeight x..Y, f (x, y) := by
  rw [setIntegral_domain_eq_verticalSetSlices hf,
    verticalSetSlices_eq_intervalSlices f hY]

def horizontalSlice (Y y : ℝ) : Set ℝ :=
  {x : ℝ | (x, y) ∈ domain Y}

def horizontalSliceIntegral
    (f : ℝ × ℝ → ℝ) (Y y : ℝ) : ℝ :=
  ∫ x in horizontalSlice Y y, f (x, y)

private theorem integral_indicator_domain_horizontalSlice
    (f : ℝ × ℝ → ℝ) (Y y : ℝ) :
    (∫ x, (domain Y).indicator f (x, y)) =
      horizontalSliceIntegral f Y y := by
  have hfun :
      (fun x : ℝ => (domain Y).indicator f (x, y)) =
        (horizontalSlice Y y).indicator (fun x => f (x, y)) := by
    funext x
    by_cases hx : (x, y) ∈ domain Y
    · have hxslice : x ∈ horizontalSlice Y y := hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxslice]
    · have hxslice : x ∉ horizontalSlice Y y := hx
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxslice]
  have hmeas : MeasurableSet (horizontalSlice Y y) :=
    (isCompact_domain Y).measurableSet.preimage
      (measurable_id.prodMk measurable_const)
  rw [hfun, MeasureTheory.integral_indicator hmeas]
  rfl

private theorem iterated_indicator_domain_swap
    {f : ℝ × ℝ → ℝ} {Y : ℝ}
    (hf : IntegrableOn f (domain Y)) :
    (∫ x, ∫ y, (domain Y).indicator f (x, y)) =
      ∫ y, ∫ x, (domain Y).indicator f (x, y) := by
  have hfprod : IntegrableOn f (domain Y)
      (volume.prod volume) := by
    simpa only [← MeasureTheory.Measure.volume_eq_prod] using hf
  have hind := hfprod.integrable_indicator
    (isCompact_domain Y).measurableSet
  exact MeasureTheory.integral_integral_swap hind

private theorem horizontal_iterated_indicator_eq_setSlices
    (f : ℝ × ℝ → ℝ) (Y : ℝ) :
    (∫ y, ∫ x, (domain Y).indicator f (x, y)) =
      ∫ y, horizontalSliceIntegral f Y y := by
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall
    (integral_indicator_domain_horizontalSlice f Y)

/-- Product-measure Fubini on the genuine curved truncated modular domain, now in horizontal-slice
coordinates.  Together with the vertical theorem this supplies both orders from one standard
two-dimensional integral. -/
theorem setIntegral_eq_horizontal
    {f : ℝ × ℝ → ℝ} {Y : ℝ}
    (hf : IntegrableOn f (domain Y)) :
    (∫ w in domain Y, f w) =
      ∫ y, horizontalSliceIntegral f Y y := by
  rw [setIntegral_domain_eq_indicator_prod f Y,
    integral_indicator_domain_eq_iterated hf,
    iterated_indicator_domain_swap hf,
    horizontal_iterated_indicator_eq_setSlices f Y]

theorem arcFloor_sq :
    arcFloor ^ 2 = (3 / 4 : ℝ) := by
  have h := arcHeight_sq
    (x := (1 / 2 : ℝ)) (by constructor <;> norm_num)
  change arcHeight (1 / 2 : ℝ) ^ 2 = 3 / 4
  convert h using 1
  norm_num

theorem arcFloor_le_arcHeight
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    arcFloor ≤ arcHeight x := by
  have harcSq := arcHeight_sq hx
  have hxSq : x ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [hx.1, hx.2, sq_nonneg (x + 1 / 2), sq_nonneg (1 / 2 - x)]
  apply (sq_le_sq₀ (le_of_lt arcFloor_pos)
    (Real.sqrt_nonneg _)).1
  calc
    arcFloor ^ 2 = 3 / 4 := arcFloor_sq
    _ ≤ 1 - x ^ 2 := by nlinarith
    _ = arcHeight x ^ 2 := harcSq.symm

theorem sideRadius_sq_of_lowerHeight
    {y : ℝ} (hy : y ∈ Set.Icc arcFloor 1) :
    sideRadius y ^ 2 = 1 - y ^ 2 := by
  unfold sideRadius
  apply Real.sq_sqrt
  have hy0 : 0 ≤ y := (le_of_lt arcFloor_pos).trans hy.1
  nlinarith [hy.2]

theorem sideRadius_le_half
    {y : ℝ} (hy : y ∈ Set.Icc arcFloor 1) :
    sideRadius y ≤ (1 / 2 : ℝ) := by
  have hfloor0 : 0 ≤ arcFloor := le_of_lt arcFloor_pos
  have hy0 : 0 ≤ y := hfloor0.trans hy.1
  have hfloorYsq : arcFloor ^ 2 ≤ y ^ 2 :=
    (sq_le_sq₀ hfloor0 hy0).2 hy.1
  have hrSq := sideRadius_sq_of_lowerHeight hy
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).1
  calc
    sideRadius y ^ 2 = 1 - y ^ 2 := hrSq
    _ ≤ (1 / 2 : ℝ) ^ 2 := by
      rw [arcFloor_sq] at hfloorYsq
      nlinarith

/-- Exact horizontal-slice geometry below height one: the circular exclusion is equivalent to
lying in one of the two side slivers. -/
theorem arcHeight_le_iff_side
    {x y : ℝ} (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hy : y ∈ Set.Icc arcFloor 1) :
    arcHeight x ≤ y ↔
      x ≤ -sideRadius y ∨ sideRadius y ≤ x := by
  have harc0 : 0 ≤ arcHeight x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := (le_of_lt arcFloor_pos).trans hy.1
  have hr0 : 0 ≤ sideRadius y := Real.sqrt_nonneg _
  have harcSq := arcHeight_sq hx
  have hrSq := sideRadius_sq_of_lowerHeight hy
  constructor
  · intro h
    have hsquare : arcHeight x ^ 2 ≤ y ^ 2 :=
      (sq_le_sq₀ harc0 hy0).2 h
    have hrx : sideRadius y ^ 2 ≤ x ^ 2 := by
      calc
        sideRadius y ^ 2 = 1 - y ^ 2 := hrSq
        _ ≤ x ^ 2 := by rw [harcSq] at hsquare; nlinarith
    have habs0 : |sideRadius y| ≤ |x| := (sq_le_sq).1 hrx
    have habs : sideRadius y ≤ |x| := by
      simpa [abs_of_nonneg hr0] using habs0
    by_cases hx0 : 0 ≤ x
    · exact Or.inr (by simpa [abs_of_nonneg hx0] using habs)
    · have hxnonpos : x ≤ 0 := le_of_not_ge hx0
      exact Or.inl (by rw [abs_of_nonpos hxnonpos] at habs; linarith)
  · intro h
    have habs : sideRadius y ≤ |x| := by
      rcases h with hleft | hright
      · have hxnonpos : x ≤ 0 := by linarith [hr0]
        rw [abs_of_nonpos hxnonpos]
        linarith
      · have hx0 : 0 ≤ x := hr0.trans hright
        simpa [abs_of_nonneg hx0] using hright
    have hrx : sideRadius y ^ 2 ≤ x ^ 2 := by
      apply (sq_le_sq).2
      simpa [abs_of_nonneg hr0] using habs
    have hsquare : arcHeight x ^ 2 ≤ y ^ 2 := by
      calc
        arcHeight x ^ 2 = 1 - x ^ 2 := harcSq
        _ ≤ y ^ 2 := by rw [hrSq] at hrx; nlinarith
    exact (sq_le_sq₀ harc0 hy0).1 hsquare

theorem horizontalSlice_eq_full
    {Y y : ℝ} (hy : y ∈ Set.Icc 1 Y) :
    horizontalSlice Y y =
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  ext x
  constructor
  · intro hx
    exact hx.1.1
  · intro hx
    have hyhalf : (1 / 2 : ℝ) ≤ y := by linarith [hy.1]
    have harcle : arcHeight x ≤ y :=
      (arcHeight_le_one hx).trans hy.1
    exact ⟨⟨hx, ⟨hyhalf, hy.2⟩⟩, harcle⟩

theorem horizontalSlice_eq_sideSlivers
    {Y y : ℝ} (hY : 1 ≤ Y)
    (hy : y ∈ Set.Icc arcFloor 1) :
    horizontalSlice Y y =
      Set.Icc (-(1 / 2 : ℝ)) (-sideRadius y) ∪
        Set.Icc (sideRadius y) (1 / 2) := by
  ext x
  constructor
  · intro hx
    have hxstrip : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := hx.1.1
    rcases (arcHeight_le_iff_side hxstrip hy).1 hx.2 with hleft | hright
    · exact Or.inl ⟨hxstrip.1, hleft⟩
    · exact Or.inr ⟨hright, hxstrip.2⟩
  · intro hx
    rcases hx with hxleft | hxright
    · have hxstrip : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
        constructor
        · exact hxleft.1
        · have hr0 : 0 ≤ sideRadius y := Real.sqrt_nonneg _
          linarith [hxleft.2]
      have hyhalf : (1 / 2 : ℝ) ≤ y :=
        (le_of_lt arcFloor_gt_half).trans hy.1
      have hyY : y ≤ Y := hy.2.trans hY
      exact ⟨⟨hxstrip, ⟨hyhalf, hyY⟩⟩,
        (arcHeight_le_iff_side hxstrip hy).2 (Or.inl hxleft.2)⟩
    · have hxstrip : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
        constructor
        · have hr0 : 0 ≤ sideRadius y := Real.sqrt_nonneg _
          linarith [hxright.1]
        · exact hxright.2
      have hyhalf : (1 / 2 : ℝ) ≤ y :=
        (le_of_lt arcFloor_gt_half).trans hy.1
      have hyY : y ≤ Y := hy.2.trans hY
      exact ⟨⟨hxstrip, ⟨hyhalf, hyY⟩⟩,
        (arcHeight_le_iff_side hxstrip hy).2 (Or.inr hxright.1)⟩

theorem horizontalSlice_eq_empty_of_not_mem
    {Y y : ℝ} (hy : y ∉ Set.Icc arcFloor Y) :
    horizontalSlice Y y = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  apply hy
  have hxstrip : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := hx.1.1
  exact ⟨(arcFloor_le_arcHeight hxstrip).trans hx.2, hx.1.2.2⟩

theorem horizontalSliceIntegral_eq_zero_of_not_mem
    (f : ℝ × ℝ → ℝ) {Y y : ℝ}
    (hy : y ∉ Set.Icc arcFloor Y) :
    horizontalSliceIntegral f Y y = 0 := by
  unfold horizontalSliceIntegral
  rw [horizontalSlice_eq_empty_of_not_mem hy]
  simp

theorem integrable_horizontalSliceIntegral
    {f : ℝ × ℝ → ℝ} {Y : ℝ}
    (hf : IntegrableOn f (domain Y)) :
    Integrable (fun y => horizontalSliceIntegral f Y y) := by
  have hfprod : IntegrableOn f (domain Y)
      (volume.prod volume) := by
    simpa only [← MeasureTheory.Measure.volume_eq_prod] using hf
  have hind := hfprod.integrable_indicator
    (isCompact_domain Y).measurableSet
  have hright := hind.integral_prod_right
  exact hright.congr (Filter.Eventually.of_forall fun y =>
    integral_indicator_domain_horizontalSlice f Y y)

theorem integral_horizontalSliceIntegral_eq_interval
    (f : ℝ × ℝ → ℝ) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ y, horizontalSliceIntegral f Y y) =
      ∫ y in arcFloor..Y,
        horizontalSliceIntegral f Y y := by
  have hfloorOne : arcFloor ≤ 1 :=
    arcHeight_le_one (by constructor <;> norm_num)
  have hfloorY : arcFloor ≤ Y := hfloorOne.trans hY
  have hfun :
      (fun y => horizontalSliceIntegral f Y y) =
        (Set.Icc arcFloor Y).indicator
          (fun y => horizontalSliceIntegral f Y y) := by
    funext y
    by_cases hy : y ∈ Set.Icc arcFloor Y
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy,
        horizontalSliceIntegral_eq_zero_of_not_mem f hy]
  calc
    (∫ y, horizontalSliceIntegral f Y y) =
        ∫ y, (Set.Icc arcFloor Y).indicator
          (fun q => horizontalSliceIntegral f Y q) y := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun y => congrFun hfun y
    _ = ∫ y in Set.Icc arcFloor Y,
          horizontalSliceIntegral f Y y := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ y in arcFloor..Y,
          horizontalSliceIntegral f Y y := by
      rw [intervalIntegral.integral_of_le hfloorY,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]


theorem horizontalSliceIntegral_eq_full (F : ℝ × ℝ → ℝ)
    {Y y : ℝ} (hy : y ∈ Icc 1 Y) :
    horizontalSliceIntegral F Y y = ∫ x in (-(1 / 2 : ℝ))..(1 / 2), F (x, y) := by
  unfold horizontalSliceIntegral
  rw [horizontalSlice_eq_full hy, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc]

theorem horizontalSliceIntegral_eq_sides (F : ℝ × ℝ → ℝ)
    {Y y : ℝ} (hY : 1 ≤ Y) (hy : y ∈ Icc arcFloor 1)
    (hc : Continuous (fun x => F (x, y))) :
    horizontalSliceIntegral F Y y =
      (∫ x in (-(1 / 2 : ℝ))..(-sideRadius y), F (x, y)) +
        ∫ x in sideRadius y..(1 / 2), F (x, y) := by
  have hL := hc.integrableOn_Icc (μ := volume) (a := -(1 / 2)) (b := -sideRadius y)
  have hR := hc.integrableOn_Icc (μ := volume) (a := sideRadius y) (b := 1 / 2)
  have hdis : AEDisjoint volume (Icc (-(1 / 2 : ℝ)) (-sideRadius y))
      (Icc (sideRadius y) (1 / 2)) := by
    unfold AEDisjoint
    apply measure_mono_null (t := ({0} : Set ℝ))
    · intro x hx
      have hr0 : 0 ≤ sideRadius y := Real.sqrt_nonneg _
      simp only [mem_singleton_iff]
      linarith [hx.1.2, hx.2.1]
    · exact measure_singleton 0
  have hrhalf := sideRadius_le_half hy
  unfold horizontalSliceIntegral
  rw [horizontalSlice_eq_sideSlivers hY hy,
    setIntegral_union₀ hdis measurableSet_Icc.nullMeasurableSet hL hR,
    intervalIntegral.integral_of_le (by linarith : (-(1 / 2 : ℝ)) ≤ -sideRadius y),
    ← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hrhalf,
    ← integral_Icc_eq_integral_Ioc]

end
end GaloisForLFunctions.RHTower.SelbergModularDomainSlices
