import GaloisForLFunctions.HTGeometry.OrthogonalCodimensionOne
import GaloisForLFunctions.RHTower.BurnolSoninEvenCosineAperture

/-!
# The extended Sonine space as an orthogonal complement

Burnol's second proof of Prop. 4.5 (arXiv:math/0203120) rests on the description

> `L_a` is the perpendicular complement of `(L²(0,a) ∩ 1⊥) + F₊(L²(0,a) ∩ 1⊥)`

— being *constant* on the band is exactly being orthogonal to the mean-zero functions supported in
the band.  This file proves that description for the corpus's `soninExtendedSpace`.

## Main results

* `bandIndicator` — the band indicator as an `L²` vector.
* `mem_orthogonal_meanZeroBand_iff` — orthogonality to the mean-zero band is constancy on the band.
* `soninHeadConstant_iff_band_ae` — for an even vector, a constant head is constancy on the
  symmetric band.
* `mem_soninExtendedSpace_iff_orthogonal_meanZeroBand` — **Burnol's description of `L_a`**.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The indicator of the central band, as a vector of `L²(ℝ)`. -/
def bandIndicator (a : ℝ) : SoninL2 :=
  indicatorConstLp 2 (measurableSet_centralInterval a)
    (by rw [centralInterval]; exact measure_Icc_lt_top.ne) (1 : ℂ)

theorem bandIndicator_coeFn (a : ℝ) :
    (bandIndicator a : ℝ → ℂ) =ᵐ[volume] (centralInterval a).indicator fun _ => (1 : ℂ) :=
  indicatorConstLp_coeFn

theorem bandIndicator_mem_physicalForbidden (a : ℝ) :
    bandIndicator a ∈ physicalForbidden (centralInterval a) (measurableSet_centralInterval a) := by
  have hcut : indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (bandIndicator a) = bandIndicator a := by
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a)
      (bandIndicator a), bandIndicator_coeFn a] with x hx hb
    rw [hx]
    by_cases hmem : x ∈ centralInterval a
    · rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem, hb, Set.indicator_of_notMem hmem]
  exact ⟨bandIndicator a, hcut⟩

/-- The mean-zero band: vectors supported in the band and orthogonal to its indicator. -/
def meanZeroBand (a : ℝ) : Submodule ℂ SoninL2 :=
  physicalForbidden (centralInterval a) (measurableSet_centralInterval a) ⊓
    (ℂ ∙ bandIndicator a)ᗮ

/-- **Orthogonality to the mean-zero band is constancy on the band.** -/
theorem mem_orthogonal_meanZeroBand_iff (a : ℝ) (f : SoninL2) :
    f ∈ (meanZeroBand a)ᗮ ↔
      ∃ c : ℂ, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = c := by
  rw [meanZeroBand, mem_orthogonal_inf_orthogonal_span_singleton_iff
    (A := physicalForbidden (centralInterval a) (measurableSet_centralInterval a))
    (bandIndicator_mem_physicalForbidden a),
    ← indicatorCutoff_eq_physicalForbidden_starProjection]
  constructor
  · rintro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    refine ⟨c, ?_⟩
    filter_upwards [indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a) f,
      bandIndicator_coeFn a, Lp.coeFn_smul c (bandIndicator a),
      (Lp.ext_iff.1 hc.symm : ((indicatorCutoff (centralInterval a)
        (measurableSet_centralInterval a) f : SoninL2) : ℝ → ℂ)
          =ᵐ[volume] ((c • bandIndicator a : SoninL2) : ℝ → ℂ))]
      with x hcut hb hsmul heq
    intro hmemx
    rw [hcut, Set.indicator_of_mem hmemx] at heq
    rw [heq, hsmul, Pi.smul_apply, hb, Set.indicator_of_mem hmemx, smul_eq_mul, mul_one]
  · rintro ⟨c, hc⟩
    refine Submodule.mem_span_singleton.2 ⟨c, ?_⟩
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a) f,
      bandIndicator_coeFn a, Lp.coeFn_smul c (bandIndicator a), hc] with x hcut hb hsmul hx
    rw [hsmul, Pi.smul_apply, hb, hcut]
    by_cases hmem : x ∈ centralInterval a
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, smul_eq_mul, mul_one, hx hmem]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, smul_zero]

/-- For an even vector, a constant aperture head is constancy on the whole symmetric band. -/
theorem soninHeadConstant_iff_band_ae {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ evenSubspace) :
    SoninHeadConstant a (f : ℝ → ℂ) ↔
      ∃ c : ℂ, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = c := by
  have heven : ∀ᵐ t ∂(volume : Measure ℝ), (f : ℝ → ℂ) (-t) = (f : ℝ → ℂ) t := by
    have hrefl : l2Reflection f = f := (mem_evenSubspace_iff f).1 hf
    filter_upwards [l2Reflection_ae f, Lp.ext_iff.1 hrefl] with x hx heq
    rw [← heq, hx]
  constructor
  · rintro ⟨c, hc⟩
    have hc' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo (0 : ℝ) a → (f : ℝ → ℂ) t = c :=
      (ae_restrict_iff' measurableSet_Ioo).1 hc
    have hneg : ∀ᵐ t ∂(volume : Measure ℝ),
        (-t) ∈ Set.Ioo (0 : ℝ) a → (f : ℝ → ℂ) (-t) = c :=
      ((Measure.measurePreserving_neg
        (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae).eventually hc'
    have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (0 : ℝ) := by
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with t ht
      simpa using ht
    have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ a := by
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton a)] with t ht
      simpa using ht
    have h2 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ -a := by
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (-a))] with t ht
      simpa using ht
    refine ⟨c, ?_⟩
    filter_upwards [hc', hneg, heven, h0, h1, h2] with t hpos hnegt hev hne0 hnea hnena
    intro hmem
    rw [centralInterval, Set.mem_Icc] at hmem
    rcases lt_trichotomy t 0 with hlt | heq0 | hgt
    · have hmem' : (-t) ∈ Set.Ioo (0 : ℝ) a := by
        refine ⟨by linarith, ?_⟩
        rcases lt_or_eq_of_le hmem.1 with h | h
        · linarith
        · exact absurd h.symm hnena
      rw [← hev]
      exact hnegt hmem'
    · exact absurd heq0 hne0
    · have hmem' : t ∈ Set.Ioo (0 : ℝ) a := by
        refine ⟨hgt, ?_⟩
        rcases lt_or_eq_of_le hmem.2 with h | h
        · exact h
        · exact absurd h hnea
      exact hpos hmem'
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    filter_upwards [hc] with t ht hmem
    refine ht ?_
    rw [centralInterval, Set.mem_Icc]
    exact ⟨by linarith [hmem.1, ha], le_of_lt hmem.2⟩

/-- **Burnol's description of the extended Sonine space** (second proof of Prop. 4.5):
`L_a` consists of the even vectors that are orthogonal to the mean-zero band, together with their
cosine transforms. -/
theorem mem_soninExtendedSpace_iff_orthogonal_meanZeroBand {a : ℝ} (ha : 0 < a)
    (f : evenSubspace) :
    f ∈ soninExtendedSpace a ↔
      ((f : SoninL2) ∈ (meanZeroBand a)ᗮ ∧
        ((soninCosineUnitary f : evenSubspace) : SoninL2) ∈ (meanZeroBand a)ᗮ) := by
  rw [mem_soninExtendedSpace, soninHeadConstant_iff_band_ae ha f.2,
    soninHeadConstant_iff_band_ae ha (soninCosineUnitary f).2,
    mem_orthogonal_meanZeroBand_iff, mem_orthogonal_meanZeroBand_iff]

end RHTower
