import GaloisForLFunctions.RHTower.BurnolCoPoissonIndicatorSeed
import GaloisForLFunctions.RHTower.BurnolCoPoissonSourceSpace

/-!
# The indicator-seed co-Poisson vector

The co-Poisson sum of the indicator seed is square integrable and even, so it defines a vector of
the even carrier, and its aperture head is constant.  That settles every field of a co-Poisson
source except the constancy of the aperture head of the cosine transform: the entire inhabitation
question for the co-Poisson layer at aperture `b` is reduced to that single analytic statement.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- **An almost-everywhere even square-integrable function is a vector of the even carrier.** -/
theorem memLp_toLp_mem_evenSubspace {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (heven : ∀ x : ℝ, f (-x) = f x) : (hf.toLp f : SoninL2) ∈ evenSubspace := by
  rw [mem_evenSubspace_iff]
  apply Lp.ext
  have hcoe := hf.coeFn_toLp
  have hneg := hcoe.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (hf.toLp f), hneg, hcoe] with x href hleft hright
  have hleft' : ((hf.toLp f : SoninL2) : ℝ → ℂ) (-x) = f (-x) := by
    simpa [Function.comp_apply] using hleft
  rw [href, hleft', hright, heven]

/-- The co-Poisson vector of the indicator seed inside the even carrier. -/
def coPoissonIndicatorEven {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) : evenSubspace :=
  ⟨(memLp_two_burnolCoPoissonRightSum_coPoissonIndicatorSeed hb hb1).toLp _,
    memLp_toLp_mem_evenSubspace _ (burnolCoPoissonRightSum_even (coPoissonIndicatorSeed b))⟩

theorem coPoissonIndicatorEven_coeFn {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    (((coPoissonIndicatorEven hb hb1 : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      burnolCoPoissonRightSum (coPoissonIndicatorSeed b) :=
  (memLp_two_burnolCoPoissonRightSum_coPoissonIndicatorSeed hb hb1).coeFn_toLp

/-- **The aperture head of the indicator co-Poisson vector is constant.**  This is the first of the
two defining Sonine conditions. -/
theorem soninHeadConstant_coPoissonIndicatorEven {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    SoninHeadConstant b (((coPoissonIndicatorEven hb hb1 : evenSubspace) : SoninL2) : ℝ → ℂ) := by
  obtain ⟨c, hc⟩ := soninHeadConstant_burnolCoPoissonRightSum (support_coPoissonIndicatorSeed b)
  refine ⟨c, ?_⟩
  filter_upwards [ae_restrict_of_ae (coPoissonIndicatorEven_coeFn hb hb1), hc] with t h1 h2
  rw [h1, h2]

/-- **The co-Poisson layer is inhabited as soon as the cosine head condition holds.**  Every other
field of a co-Poisson source is supplied unconditionally by the indicator seed: integrability,
compact multiplicative support, square integrability, evenness, constancy of the aperture head, and
the almost-everywhere identification of the vector with the literal co-Poisson sum. -/
def coPoissonIndicatorSource {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hcos : SoninHeadConstant b
      (((soninCosineUnitary (coPoissonIndicatorEven hb hb1) : evenSubspace) : SoninL2) : ℝ → ℂ)) :
    BurnolCoPoissonSource b where
  seed := coPoissonIndicatorSeed b
  seed_integrable := integrable_coPoissonIndicatorSeed b
  seed_support := support_coPoissonIndicatorSeed b
  vector := ⟨coPoissonIndicatorEven hb hb1,
    mem_soninExtendedSpace.mpr ⟨soninHeadConstant_coPoissonIndicatorEven hb hb1, hcos⟩⟩
  vector_eq_sum := coPoissonIndicatorEven_coeFn hb hb1

/-- **The co-Poisson source layer is not vacuous under the cosine head condition.** -/
theorem nonempty_burnolCoPoissonSource_of_cosineHead {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hcos : SoninHeadConstant b
      (((soninCosineUnitary (coPoissonIndicatorEven hb hb1) : evenSubspace) : SoninL2) : ℝ → ℂ)) :
    Nonempty (BurnolCoPoissonSource b) :=
  ⟨coPoissonIndicatorSource hb hb1 hcos⟩


/-- **Reduction of the cosine head condition to the co-Poisson intertwining.**  Burnol's
intertwining says that the cosine transform of a co-Poisson sum is the co-Poisson sum of the
reciprocal seed.  Granting that identity for the indicator seed, the second Sonine condition follows
from the first one applied to the reciprocal seed, which is again supported in the window. -/
theorem soninHeadConstant_cosine_coPoissonIndicatorEven_of_intertwine
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hint : ((((soninCosineUnitary (coPoissonIndicatorEven hb hb1) : evenSubspace) :
        SoninL2)) : ℝ → ℂ) =ᵐ[volume]
      burnolCoPoissonRightSum (coPoissonReciprocalSeed (coPoissonIndicatorSeed b))) :
    SoninHeadConstant b
      (((soninCosineUnitary (coPoissonIndicatorEven hb hb1) : evenSubspace) : SoninL2) :
        ℝ → ℂ) := by
  obtain ⟨c, hc⟩ := soninHeadConstant_burnolCoPoissonRightSum
    (support_coPoissonReciprocalSeed hb (support_coPoissonIndicatorSeed b))
  refine ⟨c, ?_⟩
  filter_upwards [ae_restrict_of_ae hint, hc] with t h1 h2
  rw [h1, h2]

/-- **The co-Poisson intertwining alone inhabits the source layer.**  Every other input is
unconditional. -/
theorem nonempty_burnolCoPoissonSource_of_intertwine {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hint : ((((soninCosineUnitary (coPoissonIndicatorEven hb hb1) : evenSubspace) :
        SoninL2)) : ℝ → ℂ) =ᵐ[volume]
      burnolCoPoissonRightSum (coPoissonReciprocalSeed (coPoissonIndicatorSeed b))) :
    Nonempty (BurnolCoPoissonSource b) :=
  nonempty_burnolCoPoissonSource_of_cosineHead hb hb1
    (soninHeadConstant_cosine_coPoissonIndicatorEven_of_intertwine hb hb1 hint)

end RHTower

