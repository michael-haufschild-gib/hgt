import GaloisForLFunctions.HTGeometry.ConstitutiveObserverFibreChirality

/-!
# Factorization sufficiency for relative entropy

A deterministic observer `q` loses no relative entropy when the likelihood ratio factors through
it.  This is the exact measure-theoretic content of the sufficient-statistic reduction: the
pushforward of a `q`-factored density is the same density read on the observer space, so both
directed Kullback–Leibler costs are literally the same integral.

No finiteness of the source space, no discreteness, and no disintegration are used.
-/

open MeasureTheory InformationTheory

namespace GaloisForLFunctions.HTGeometry

variable {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]

/-- **Pushforward of a factored density.**  Weighting by a density that factors through `q` and
then observing is the same as observing and then weighting by the density itself. -/
theorem map_withDensity_comp (R : Measure Ω) {q : Ω → Y} (hq : Measurable q)
    {g : Y → ENNReal} (hg : Measurable g) :
    (R.withDensity (g ∘ q)).map q = (R.map q).withDensity g := by
  ext B hB
  rw [Measure.map_apply hq hB, withDensity_apply _ (hq hB), withDensity_apply _ hB,
    ← lintegral_indicator (hq hB), ← lintegral_indicator hB,
    lintegral_map (f := fun y => B.indicator g y) (by fun_prop) hq]
  refine lintegral_congr fun x => ?_
  by_cases hx : q x ∈ B <;> simp [Set.indicator_apply, hx]

/-- The relative entropy of a `q`-factored density is carried entirely by the observer. -/
theorem klDiv_map_eq_of_density_comp {P R : Measure Ω} [IsFiniteMeasure P] [IsFiniteMeasure R]
    {q : Ω → Y} (hq : Measurable q) {g : Y → ENNReal} (hg : Measurable g)
    (hPR : P = R.withDensity (g ∘ q)) :
    klDiv P R = klDiv (P.map q) (R.map q) := by
  haveI : IsFiniteMeasure (P.map q) := by
    constructor
    rw [Measure.map_apply hq MeasurableSet.univ]
    exact measure_lt_top P _
  haveI : IsFiniteMeasure (R.map q) := by
    constructor
    rw [Measure.map_apply hq MeasurableSet.univ]
    exact measure_lt_top R _
  have hPac : P ≪ R := hPR ▸ withDensity_absolutelyContinuous R (g ∘ q)
  have hmap : P.map q = (R.map q).withDensity g := by
    rw [hPR, map_withDensity_comp R hq hg]
  have hmapac : P.map q ≪ R.map q := hmap ▸ withDensity_absolutelyContinuous _ g
  have hrn : P.rnDeriv R =ᵐ[R] g ∘ q := by
    rw [hPR]; exact Measure.rnDeriv_withDensity R (hg.comp hq)
  have hrnmap : (P.map q).rnDeriv (R.map q) =ᵐ[R.map q] g := by
    rw [hmap]; exact Measure.rnDeriv_withDensity _ hg
  rw [klDiv_eq_lintegral_klFun_of_ac hPac, klDiv_eq_lintegral_klFun_of_ac hmapac]
  rw [lintegral_congr_ae (hrn.mono fun x hx => by rw [hx]),
    lintegral_congr_ae (hrnmap.mono fun y hy => by rw [hy])]
  exact (lintegral_map (f := fun y => ENNReal.ofReal (klFun (g y).toReal)) (by fun_prop) hq).symm

/-- **Factorization sufficiency.**  If both directed likelihood ratios factor through the observer,
the observer is Kullback–Leibler pair-sufficient: it loses neither directed cost. -/
theorem isKLPairSufficient_of_density_comp {P R : Measure Ω} [IsFiniteMeasure P] [IsFiniteMeasure R]
    {q : Ω → Y} (hq : Measurable q) {g h : Y → ENNReal} (hg : Measurable g) (hh : Measurable h)
    (hPR : P = R.withDensity (g ∘ q)) (hRP : R = P.withDensity (h ∘ q)) :
    IsKLPairSufficient P R q :=
  ⟨(klDiv_map_eq_of_density_comp hq hg hPR).symm,
   (klDiv_map_eq_of_density_comp hq hh hRP).symm⟩

/-- The observer fibre current of a factored likelihood ratio vanishes. -/
theorem observerFibreChirality_eq_zero_of_density_comp
    {P R : Measure Ω} [IsFiniteMeasure P] [IsFiniteMeasure R]
    {q : Ω → Y} (hq : Measurable q) {g h : Y → ENNReal} (hg : Measurable g) (hh : Measurable h)
    (hPR : P = R.withDensity (g ∘ q)) (hRP : R = P.withDensity (h ∘ q)) :
    observerFibreChirality P R q = 0 :=
  observerFibreChirality_eq_zero_of_pairSufficient P R q
    (isKLPairSufficient_of_density_comp hq hg hh hPR hRP)

/-! ## The exponential (Esscher) family -/

/-- The exponentially tilted law of a scalar formation statistic. -/
noncomputable def esscherLaw (μ : Measure Ω) (Q : Ω → ℝ) (c t : ℝ) : Measure Ω :=
  μ.withDensity fun x => ENNReal.ofReal (c * Real.exp (-t * Q x))

/-- **(OFCC.11)**  Two members of an exponential family differ by a density that factors through
the scalar statistic. -/
theorem esscherLaw_eq_withDensity_comp (μ : Measure Ω) {Q : Ω → ℝ} (hQ : Measurable Q)
    {cs ct : ℝ} (hcs : 0 ≤ cs) (hct : 0 < ct) (s t : ℝ) :
    esscherLaw μ Q cs s
      = (esscherLaw μ Q ct t).withDensity
          ((fun y => ENNReal.ofReal (cs / ct * Real.exp ((t - s) * y))) ∘ Q) := by
  rw [esscherLaw, esscherLaw, ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  refine withDensity_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hc : ct * (cs / ct) = cs := by field_simp
  symm
  calc ct * Real.exp (-t * Q x) * (cs / ct * Real.exp ((t - s) * Q x))
      = (ct * (cs / ct)) * (Real.exp (-t * Q x) * Real.exp ((t - s) * Q x)) := by ring
    _ = cs * Real.exp (-s * Q x) := by
        rw [hc, ← Real.exp_add]
        congr 2
        ring

/-- **Scalar sufficiency of the exponential family.**  The tilting statistic is Kullback–Leibler
pair-sufficient for every pair of members. -/
theorem esscher_isKLPairSufficient (μ : Measure Ω) {Q : Ω → ℝ} (hQ : Measurable Q)
    {cs ct : ℝ} (hcs : 0 < cs) (hct : 0 < ct) (s t : ℝ)
    [IsFiniteMeasure (esscherLaw μ Q cs s)] [IsFiniteMeasure (esscherLaw μ Q ct t)] :
    IsKLPairSufficient (esscherLaw μ Q cs s) (esscherLaw μ Q ct t) Q :=
  isKLPairSufficient_of_density_comp hQ
    (g := fun y => ENNReal.ofReal (cs / ct * Real.exp ((t - s) * y)))
    (h := fun y => ENNReal.ofReal (ct / cs * Real.exp ((s - t) * y)))
    (by fun_prop) (by fun_prop)
    (esscherLaw_eq_withDensity_comp μ hQ hcs.le hct s t)
    (esscherLaw_eq_withDensity_comp μ hQ hct.le hcs t s)

end GaloisForLFunctions.HTGeometry
