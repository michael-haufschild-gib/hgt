import GaloisForLFunctions.ScaleSignedIncidenceCriticality.DepthResolutionNeedsAScaleBound

/-!
# The deficit budget of an adaptive policy

A fixed aperture resolves no depth once the scale outruns it, so a mechanism must choose its
aperture and its level as functions of the scale it is addressing. Such a choice is a **policy**,
and a policy defines a reading of the data: at the datum `p` it reads the Weil floor at aperture
`A (scale p)` and level `η (scale p)`. This is the first reading of the programme that adapts to
its datum, and it is the first that certifies a nontrivial bound.

For a policy whose aperture stays in the band `(L/2, L]` the reading is exactly a depth bound
(`adaptiveReading_iff`):

`adaptiveReading A η p  ↔  depth p ≤ depthResolution (scale p) (η (scale p))`.

Hence the two halves of the **budget law**:

* `certifies_of_budget` — if the level policy obeys `η L ≤ β² L³` at every scale, the policy
  certifies `depth ≤ β`. The deficit a mechanism may tolerate at scale `L` is cubic in the scale and
  quadratic in the depth it wants to exclude.
* `not_certifies_of_budget_violation` — and the bound is sharp in the exact threshold unit: if at
  one scale the level reaches the threshold of some depth `β' > β`, the policy certifies nothing
  below `β'`.

`theDeficitBudgetLaw` states both. Read against `DepthResolutionNeedsAScaleBound` the message is
that adaptivity is not a technical convenience but the whole of the matter: the fixed-aperture
readings of the programme all have budget `η L` constant, which violates `η L ≤ β² L³` at small
scales and leaves them with the trivial bound. A mechanism's aperture must follow the scale, and its
error must shrink like the cube of it.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. Policies and the readings they define -/

/-- A policy reads, at each datum, the Weil floor at an aperture and a level chosen from the
datum's own scale. -/
def adaptiveReading (A η : ℝ → ℝ) (p : ScaleDepthDatum) : Prop :=
  WeilFloorAtLevel (sdConfig p) (A (sdScale p)) (η (sdScale p))

/-- A policy is *scale-matched* when its aperture lies just above the Nyquist aperture of the scale
it is applied to, and its level is nonnegative. -/
structure ScaleMatched (A η : ℝ → ℝ) : Prop where
  aperture_lb : ∀ L : ℝ, 0 < L → L / 2 < A L
  aperture_ub : ∀ L : ℝ, 0 < L → A L ≤ L
  level_nonneg : ∀ L : ℝ, 0 < L → 0 ≤ η L

/-- **A scale-matched policy reads exactly a depth bound.** -/
theorem adaptiveReading_iff {A η : ℝ → ℝ} (h : ScaleMatched A η) (p : ScaleDepthDatum) :
    adaptiveReading A η p ↔ sdDepth p ≤ depthResolution (sdScale p) (η (sdScale p)) := by
  have h1 := weilFloorAtLevel_offLineLattice_iff_cosh (L := sdScale p) (δ := sdDepth p)
    p.2.1 p.2.2.1 p.2.2.2 (h.aperture_lb _ p.2.1) (h.aperture_ub _ p.2.1) (η (sdScale p))
  have h2 := weilFloorThreshold_le_iff (L := sdScale p) (δ := sdDepth p) (η := η (sdScale p))
    p.2.1 p.2.2.1 (h.level_nonneg _ p.2.1)
  exact h1.trans h2

/-! ### 2. The budget suffices -/

/-- **The budget law, sufficiency.** A level policy bounded by `β² L³` certifies the depth bound
`β`: every datum the policy admits has depth at most `β`. -/
theorem certifies_of_budget {A η : ℝ → ℝ} (h : ScaleMatched A η) {β : ℝ} (hβ : 0 ≤ β)
    (hbudget : ∀ L : ℝ, 0 < L → η L ≤ β ^ 2 * L ^ 3) {p₀ : ScaleDepthDatum}
    (hp₀ : adaptiveReading A η p₀) :
    Certifies sdDepth (adaptiveReading A η) p₀ β := by
  intro p hp
  have hread : adaptiveReading A η p := (mem_shadow_iff.mp hp) ▸ hp₀
  have hL : 0 < sdScale p := p.2.1
  have hdepth := (adaptiveReading_iff h p).mp hread
  have hsqrt : depthResolution (sdScale p) (η (sdScale p)) ≤
      Real.sqrt (η (sdScale p) / sdScale p ^ 3) :=
    depthResolution_le_sqrt hL (h.level_nonneg _ hL)
  have hquot : η (sdScale p) / sdScale p ^ 3 ≤ β ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < sdScale p ^ 3)]
    exact hbudget _ hL
  have hfin : Real.sqrt (η (sdScale p) / sdScale p ^ 3) ≤ β := by
    have hs := Real.sqrt_le_sqrt hquot
    rwa [Real.sqrt_sq hβ] at hs
  exact hdepth.trans (hsqrt.trans hfin)

/-! ### 3. The budget is sharp -/

/-- **The budget law, sharpness.** If at some scale the level reaches the exact threshold of a depth
`β' > β`, the policy admits a datum of depth `β'` and certifies nothing below it. -/
theorem not_certifies_of_budget_violation {A η : ℝ → ℝ} (h : ScaleMatched A η) {β : ℝ}
    {L β' : ℝ} (hL : 0 < L) (hβ'0 : 0 < β') (hβ' : β' ≤ 1 / 2) (hlt : β < β')
    (hreach : weilFloorThreshold L β' ≤ η L) {p₀ : ScaleDepthDatum}
    (hp₀ : adaptiveReading A η p₀) :
    ¬ Certifies sdDepth (adaptiveReading A η) p₀ β := by
  set p : ScaleDepthDatum := ⟨(L, β'), hL, hβ'0, hβ'⟩ with hp
  have hread : adaptiveReading A η p :=
    (adaptiveReading_iff h p).mpr
      ((weilFloorThreshold_le_iff hL hβ'0 (h.level_nonneg _ hL)).mp hreach)
  have hmem : p ∈ shadow (adaptiveReading A η) p₀ := propext (iff_of_true hread hp₀)
  intro hcert
  exact absurd (hcert p hmem) (not_le.mpr hlt)

/-! ### 4. The law -/

/-- **The deficit budget law.** For a scale-matched policy the reading is exactly a depth bound; a
level budget `β² L³` certifies depth `β`; and reaching the threshold of a larger depth at any one
scale destroys the certificate. The tolerable deficit is cubic in the scale and quadratic in the
depth. -/
theorem theDeficitBudgetLaw {A η : ℝ → ℝ} (h : ScaleMatched A η) {β : ℝ} (hβ : 0 ≤ β)
    {p₀ : ScaleDepthDatum} (hp₀ : adaptiveReading A η p₀) :
    (∀ p : ScaleDepthDatum, adaptiveReading A η p ↔
        sdDepth p ≤ depthResolution (sdScale p) (η (sdScale p))) ∧
      ((∀ L : ℝ, 0 < L → η L ≤ β ^ 2 * L ^ 3) →
        Certifies sdDepth (adaptiveReading A η) p₀ β) ∧
      ∀ L β' : ℝ, 0 < L → 0 < β' → β' ≤ 1 / 2 → β < β' → weilFloorThreshold L β' ≤ η L →
        ¬ Certifies sdDepth (adaptiveReading A η) p₀ β :=
  ⟨adaptiveReading_iff h, fun hb => certifies_of_budget h hβ hb hp₀,
    fun _ _ hL hβ'0 hβ' hlt hreach =>
      not_certifies_of_budget_violation h hL hβ'0 hβ' hlt hreach hp₀⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
