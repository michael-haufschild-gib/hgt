import Mathlib.Analysis.Convex.Slope
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading

/-!
# The rate is a cofinal invariant

Every blindness theorem of the aperture face is a statement about a *bounded* parameter range, and
every sufficiency theorem is a statement about an *unbounded* one.  This module isolates the
mechanism common to both and prices a rate reading exactly: for a deficit convex in the aperture,
the reading "the growth rate is at most `γ`" taken on an unbounded set of apertures is the *same
reading* as the one taken at every aperture.

The content is one monotonicity.  The secant rate from the origin,
`secantRate g a = (g a − g 0)/a`, is nondecreasing in the aperture whenever the deficit is convex
(`secantRate_mono`); so a bound holding on apertures that reach arbitrarily far already holds at
every aperture, because each aperture is dominated by a measured one above it.  Hence the two sets
of certified rates coincide (`rateBoundsOn_eq_rateBounds`), the two readings have equal shadows,
and therefore

* the measured rate is unchanged (`sInf_rateBoundsOn`),
* **every** invariant of growth profiles has the same resolution limit and the same floor under the
  thinned reading as under the full one (`resolutionLimit_rateBoundsOn`,
  `resolutionFloor_rateBoundsOn`),
* and the thinned reading resolves exactly the properties the full one resolves
  (`resolves_rateBoundsOn_iff`).

So no floor of a rate-reading class moves when the apertures are thinned to a cofinal set: a rate,
unlike a sign at a bounded aperture, is a tail invariant, and the resource it consumes is
cofinality alone — not density, not an interval, not every scale.  Convexity is what the gate
profiles of the field have in common, and it is exactly what makes the rate readable sparsely.
-/

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false

/-! ### 1. The data -/

/-- A growth profile: a deficit read along the aperture axis, convex in the aperture. -/
structure GrowthProfile where
  /-- The deficit at a given aperture. -/
  deficit : ℝ → ℝ
  /-- Convexity in the aperture, the property the gate profiles share. -/
  convex : ConvexOn ℝ (Set.Ici (0 : ℝ)) deficit

/-- An unbounded set of apertures: the resource a rate reading consumes. -/
structure CofinalApertures where
  /-- The apertures at which the deficit is measured. -/
  carrier : Set ℝ
  /-- Apertures are positive. -/
  pos : ∀ a ∈ carrier, 0 < a
  /-- The apertures reach arbitrarily far. -/
  cofinal : ∀ M : ℝ, ∃ a ∈ carrier, M ≤ a

/-! ### 2. The secant rate and its monotonicity -/

/-- The secant rate at aperture `a`: the deficit's growth per unit aperture, measured from the
origin. -/
noncomputable def secantRate (g : GrowthProfile) (a : ℝ) : ℝ :=
  (g.deficit a - g.deficit 0) / a

/-- **Secant rates increase with the aperture.**  This is the whole content of convexity here, and
the reason a rate needs only cofinally many apertures. -/
theorem secantRate_mono (g : GrowthProfile) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    secantRate g a ≤ secantRate g b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h := g.convex.secant_mono (a := (0 : ℝ)) (x := a) (y := b) Set.self_mem_Ici
    (Set.mem_Ici.mpr ha.le) (Set.mem_Ici.mpr hb.le) (ne_of_gt ha) (ne_of_gt hb) hab
  simpa [secantRate, sub_zero] using h

/-! ### 3. The two rate readings -/

/-- The rates the profile is certified not to exceed, read only on the apertures of `S`. -/
def rateBoundsOn (S : CofinalApertures) (g : GrowthProfile) : Set ℝ :=
  {γ : ℝ | ∀ a ∈ S.carrier, secantRate g a ≤ γ}

/-- The rates the profile is certified not to exceed at every positive aperture. -/
def rateBounds (g : GrowthProfile) : Set ℝ :=
  {γ : ℝ | ∀ a : ℝ, 0 < a → secantRate g a ≤ γ}

/-- **The rate is a cofinal invariant.**  A rate read on an unbounded set of apertures certifies
exactly the rates a rate read at every aperture certifies: the two readings are equal, so thinning
the apertures costs nothing. -/
theorem rateBoundsOn_eq_rateBounds (S : CofinalApertures) (g : GrowthProfile) :
    rateBoundsOn S g = rateBounds g := by
  ext γ
  constructor
  · intro hγ a ha
    obtain ⟨b, hbS, hab⟩ := S.cofinal a
    exact le_trans (secantRate_mono g ha hab) (hγ b hbS)
  · intro hγ a haS
    exact hγ a (S.pos a haS)

/-- The measured rate is unchanged by thinning. -/
theorem sInf_rateBoundsOn (S : CofinalApertures) (g : GrowthProfile) :
    sInf (rateBoundsOn S g) = sInf (rateBounds g) := by
  rw [rateBoundsOn_eq_rateBounds]

/-! ### 4. The floor theorem for rate readings -/

/-- The thinned and the full rate reading have the same shadows. -/
theorem shadow_rateBoundsOn (S : CofinalApertures) (g : GrowthProfile) :
    shadow (rateBoundsOn S) g = shadow rateBounds g := by
  ext h
  simp only [mem_shadow_iff, rateBoundsOn_eq_rateBounds]

/-- **No floor of a rate-reading class moves under thinning.**  For *every* invariant of growth
profiles, the rate read on an unbounded set of apertures has exactly the resolution limit of the
rate read at every aperture. -/
theorem resolutionLimit_rateBoundsOn (S : CofinalApertures) (I : GrowthProfile → ℝ)
    (g : GrowthProfile) :
    resolutionLimit I (rateBoundsOn S) g = resolutionLimit I rateBounds g := by
  rw [resolutionLimit, resolutionLimit, shadow_rateBoundsOn]

/-- The dual statement for the floor. -/
theorem resolutionFloor_rateBoundsOn (S : CofinalApertures) (I : GrowthProfile → ℝ)
    (g : GrowthProfile) :
    resolutionFloor I (rateBoundsOn S) g = resolutionFloor I rateBounds g := by
  rw [resolutionFloor, resolutionFloor, shadow_rateBoundsOn]

/-- A thinned rate reading resolves exactly the properties the full rate reading resolves. -/
theorem resolves_rateBoundsOn_iff (S : CofinalApertures) (P : GrowthProfile → Prop) :
    Resolves (rateBoundsOn S) P ↔ Resolves rateBounds P := by
  unfold Resolves
  refine ⟨fun h d e he => h d e ?_, fun h d e he => h d e ?_⟩
  · rw [shadow_rateBoundsOn]; exact he
  · rw [← shadow_rateBoundsOn]; exact he

/-- **Thinning the apertures of a rate reading is free**, in the reading, in the measured value,
and in the resolution limit of every invariant at once. -/
theorem theRateIsACofinalInvariant (S : CofinalApertures) (g : GrowthProfile) :
    rateBoundsOn S g = rateBounds g ∧
      sInf (rateBoundsOn S g) = sInf (rateBounds g) ∧
      (∀ I : GrowthProfile → ℝ,
        resolutionLimit I (rateBoundsOn S) g = resolutionLimit I rateBounds g) ∧
      ∀ P : GrowthProfile → Prop, Resolves (rateBoundsOn S) P ↔ Resolves rateBounds P :=
  ⟨rateBoundsOn_eq_rateBounds S g, sInf_rateBoundsOn S g,
    fun I => resolutionLimit_rateBoundsOn S I g, fun P => resolves_rateBoundsOn_iff S P⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
