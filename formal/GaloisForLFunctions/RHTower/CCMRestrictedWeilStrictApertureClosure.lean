import GaloisForLFunctions.RHTower.SuzukiHlogMollifiedFormCore
import GaloisForLFunctions.RHTower.CCMArchimedeanFormDomainEquivalence
import GaloisForLFunctions.RHTower.CCMRestrictedWeilApertureMonotonicity
import GaloisForLFunctions.RHTower.CCMConnesConsaniHilbertOne

/-!
# Strict-aperture closure of the exact restricted Weil form

Canonical inward dilation compresses every logarithmic form vector into a genuinely smaller
aperture and converges in the exact weighted form norm.  Aperture extension preserves the literal
archimedean--polar--prime source quadratic.  Consequently, positivity on all strict subapertures
already implies positivity at the endpoint aperture; together with extension this is an exact
equivalence.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The strict subaperture selected by the `n`th canonical inward dilation. -/
def suzukiHlogStrictInwardAperture
    (a : SuzukiPositiveAperture) (n : ℕ) : SuzukiPositiveAperture :=
  ⟨a.1 / suzukiHlogInwardScale n,
    div_pos a.2 (suzukiHlogInwardScale_pos n)⟩

@[simp] theorem suzukiHlogStrictInwardAperture_val
    (a : SuzukiPositiveAperture) (n : ℕ) :
    (suzukiHlogStrictInwardAperture a n).1 =
      a.1 / suzukiHlogInwardScale n := rfl

theorem suzukiHlogStrictInwardAperture_lt
    (a : SuzukiPositiveAperture) (n : ℕ) :
    (suzukiHlogStrictInwardAperture a n).1 < a.1 := by
  exact div_lt_self a.2 (suzukiHlogInwardScale_one_lt n)

theorem suzukiHlogStrictInwardAperture_le
    (a : SuzukiPositiveAperture) (n : ℕ) :
    (suzukiHlogStrictInwardAperture a n).1 ≤ a.1 :=
  (suzukiHlogStrictInwardAperture_lt a n).le

/-- The same inward-dilated weighted Fourier vector, now typed at its strict support radius. -/
def suzukiHlogFormStrictInwardDilate
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SuzukiHlogFormDomain a) :
    SuzukiHlogFormDomain (suzukiHlogStrictInwardAperture a n) :=
  ⟨suzukiHlogDirectInwardDilate n f.1, by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff
      (centralInterval (a.1 / suzukiHlogInwardScale n))
      (measurableSet_centralInterval (a.1 / suzukiHlogInwardScale n)))
        (suzukiHlogFourierToTime (suzukiHlogDirectInwardDilate n f.1)) = 0
    rw [sub_apply, one_apply_eq_self, sub_eq_zero]
    exact (indicatorCutoff_suzukiHlogFormInwardDilate_small a n f).symm⟩

theorem suzukiHlogFormStrictInwardDilate_val
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SuzukiHlogFormDomain a) :
    (suzukiHlogFormStrictInwardDilate a n f).1 =
      (suzukiHlogFormInwardDilate a n f).1 := rfl

@[simp] theorem ccmLogFormToArchimedean_val
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    (ccmLogFormToArchimedean a f).1 = ccmLogToArchimedean f.1 := rfl

/-- Canonical inward approximation on the exact CCM form domain. -/
def ccmArchimedeanFormInwardDilate
    (a : SuzukiPositiveAperture) (n : ℕ) (u : CCMArchimedeanFormDomain a) :
    CCMArchimedeanFormDomain a :=
  ccmLogFormToArchimedean a
    (suzukiHlogFormInwardDilate a n (ccmArchimedeanFormToLog a u))

theorem ccmArchimedeanFormInwardDilate_tendsto
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    Tendsto (fun n => ccmArchimedeanFormInwardDilate a n u) atTop (nhds u) := by
  change Tendsto
    ((ccmLogFormToArchimedean a) ∘ fun n =>
      suzukiHlogFormInwardDilate a n (ccmArchimedeanFormToLog a u))
    atTop (nhds u)
  have h := ((ccmLogFormToArchimedean a).continuous.tendsto
      (ccmArchimedeanFormToLog a u)).comp
    (suzukiHlogFormInwardDilate_tendsto a (ccmArchimedeanFormToLog a u))
  simpa only [ccmLogFormToArchimedean_archimedeanFormToLog] using h

/-- Every canonical inward approximation is an exact extension of a vector living at the
strictly smaller selected aperture. -/
theorem exists_ccmArchimedeanFormDomain_strictInwardSource
    (a : SuzukiPositiveAperture) (n : ℕ) (u : CCMArchimedeanFormDomain a) :
    ∃ v : CCMArchimedeanFormDomain (suzukiHlogStrictInwardAperture a n),
      (ccmArchimedeanFormInwardDilate a n u).1 = v.1 ∧
      ccmRestrictedWeilSourceQuadratic a
          (ccmArchimedeanFormInwardDilate a n u) =
        ccmRestrictedWeilSourceQuadratic (suzukiHlogStrictInwardAperture a n) v := by
  let q := ccmArchimedeanFormToLog a u
  let v : CCMArchimedeanFormDomain (suzukiHlogStrictInwardAperture a n) :=
    ccmLogFormToArchimedean (suzukiHlogStrictInwardAperture a n)
      (suzukiHlogFormStrictInwardDilate a n q)
  have hval : (ccmArchimedeanFormInwardDilate a n u).1 = v.1 := by
    change ccmLogToArchimedean
        (suzukiHlogFormInwardDilate a n (ccmArchimedeanFormToLog a u)).1 =
      ccmLogToArchimedean (suzukiHlogFormStrictInwardDilate a n q).1
    rw [suzukiHlogFormStrictInwardDilate_val]
  refine ⟨v, hval, ?_⟩
  exact ccmRestrictedWeilSourceQuadratic_eq_of_val_eq
    (suzukiHlogStrictInwardAperture_le a n) hval

/-- Positivity on every strict subaperture is closed in the exact logarithmic form norm, so it
already includes the endpoint aperture. -/
theorem ccmRestrictedWeilSourceQuadratic_nonneg_of_strictSubapertures
    (a : SuzukiPositiveAperture)
    (hpos : ∀ b : SuzukiPositiveAperture, b.1 < a.1 →
      ∀ v : CCMArchimedeanFormDomain b,
        0 ≤ ccmRestrictedWeilSourceQuadratic b v)
    (u : CCMArchimedeanFormDomain a) :
    0 ≤ ccmRestrictedWeilSourceQuadratic a u := by
  have hlim : Tendsto
      (fun n => ccmRestrictedWeilSourceQuadratic a
        (ccmArchimedeanFormInwardDilate a n u))
      atTop (nhds (ccmRestrictedWeilSourceQuadratic a u)) :=
    (continuous_ccmRestrictedWeilSourceQuadratic a).continuousAt.tendsto.comp
      (ccmArchimedeanFormInwardDilate_tendsto a u)
  apply ge_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n => by
    obtain ⟨v, _hval, hsource⟩ :=
      exists_ccmArchimedeanFormDomain_strictInwardSource a n u
    rw [hsource]
    exact hpos (suzukiHlogStrictInwardAperture a n)
      (suzukiHlogStrictInwardAperture_lt a n) v

/-- Exact endpoint-closure law: full form positivity at an aperture is equivalent to positivity
at every strictly smaller positive aperture. -/
theorem ccmRestrictedWeilSourceQuadratic_nonneg_iff_strictSubapertures
    (a : SuzukiPositiveAperture) :
    (∀ u : CCMArchimedeanFormDomain a,
        0 ≤ ccmRestrictedWeilSourceQuadratic a u) ↔
      ∀ b : SuzukiPositiveAperture, b.1 < a.1 →
        ∀ v : CCMArchimedeanFormDomain b,
          0 ≤ ccmRestrictedWeilSourceQuadratic b v := by
  constructor
  · intro hpos b hba v
    obtain ⟨u, hu⟩ :=
      exists_ccmArchimedeanFormDomain_extension hba.le v
    rw [← ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hba.le hu]
    exact hpos u
  · intro hpos
    exact ccmRestrictedWeilSourceQuadratic_nonneg_of_strictSubapertures a hpos

end RHTower
