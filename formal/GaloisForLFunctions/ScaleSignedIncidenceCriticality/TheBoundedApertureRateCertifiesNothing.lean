import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheRateIsACofinalInvariant

/-!
# A bounded aperture range certifies no rate at all

The cofinal half of the rate calculus says that thinning the apertures of a rate reading to a
cofinal set changes nothing.  This module is its exact complement: confining the apertures *below a
finite bound* destroys the reading completely — not weakening it, but leaving it with no bound to
certify.

The witnesses are explicit.  The ramp `a ↦ k·max(0, a − M)` is convex on `[0, ∞)`
(`convexOn_ramp`), vanishes identically up to the aperture `M`, and has secant rate exactly `k` in
the limit, so `profileRate (rampProfile k M) = k` (`profileRate_rampProfile`).  Every ramp
therefore shares its whole reading with the flat profile on apertures `≤ M`
(`rampProfile_mem_shadow`), while its rate is `k`, and `k` is free.

Hence for any aperture set confined below a bound, the rates in the shadow of the flat profile are
unbounded (`not_bddAbove_profileRate_shadow`) and the reading certifies no bound whatever
(`not_certifies_rateBoundsBelow`).  Together with the cofinal theorem this makes the rate's
dichotomy sharp and gap-free: the resource is cofinality, and anything short of it is worth
nothing, with no intermediate stages — in contrast with the aperture *sign* readings, whose bounded
stages at least retain the a priori bound `½`.

The pair also fixes which direction carries information: a rate bound measured on apertures that
stop is compatible with every rate, so a rate claim must name an unbounded aperture set or it is
vacuous.
-/

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false

/-! ### 1. Apertures confined below a bound -/

/-- A set of apertures confined below a finite bound. -/
structure BoundedApertures where
  /-- The apertures at which the deficit is measured. -/
  carrier : Set ℝ
  /-- Apertures are positive. -/
  pos : ∀ a ∈ carrier, 0 < a
  /-- The finite bound. -/
  bound : ℝ
  /-- The bound is positive. -/
  bound_pos : 0 < bound
  /-- No aperture passes the bound. -/
  le_bound : ∀ a ∈ carrier, a ≤ bound

/-- The rates certified on a bounded aperture range. -/
def rateBoundsBelow (S : BoundedApertures) (g : GrowthProfile) : Set ℝ :=
  {γ : ℝ | ∀ a ∈ S.carrier, secantRate g a ≤ γ}

/-- The rate a profile actually has: the least rate it never exceeds. -/
noncomputable def profileRate (g : GrowthProfile) : ℝ := sInf (rateBounds g)

/-! ### 2. The witnesses: a flat profile and the ramps -/

/-- The flat profile: no deficit at any aperture. -/
noncomputable def flatProfile : GrowthProfile :=
  ⟨fun _ => 0, convexOn_const 0 (convex_Ici 0)⟩

/-- The ramp `a ↦ k·max(0, a − M)` is convex on `[0, ∞)`: a nonnegative multiple of the maximum of
two affine functions. -/
theorem convexOn_ramp {k M : ℝ} (hk : 0 ≤ k) :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun a => k * max 0 (a - M)) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hMab : a * M + b * M = M := by rw [← add_mul, hab, one_mul]
  have hmax : max 0 (a * x + b * y - M) ≤ a * max 0 (x - M) + b * max 0 (y - M) := by
    refine max_le ?_ ?_
    · have h1 : 0 ≤ a * max 0 (x - M) := mul_nonneg ha (le_max_left _ _)
      have h2 : 0 ≤ b * max 0 (y - M) := mul_nonneg hb (le_max_left _ _)
      linarith
    · have h1 : a * (x - M) ≤ a * max 0 (x - M) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) ha
      have h2 : b * (y - M) ≤ b * max 0 (y - M) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hb
      have h3 : a * x + b * y - M = a * (x - M) + b * (y - M) := by
        have := hMab; ring_nf; ring_nf at this ⊢; linarith
      linarith
  calc k * max 0 (a * x + b * y - M)
      ≤ k * (a * max 0 (x - M) + b * max 0 (y - M)) := mul_le_mul_of_nonneg_left hmax hk
    _ = a * (k * max 0 (x - M)) + b * (k * max 0 (y - M)) := by ring

/-- The ramp profile of height `k` starting at aperture `M`. -/
noncomputable def rampProfile (k M : ℝ) (hk : 0 ≤ k) : GrowthProfile :=
  ⟨fun a => k * max 0 (a - M), convexOn_ramp hk⟩

theorem rampProfile_deficit (k M : ℝ) (hk : 0 ≤ k) (a : ℝ) :
    (rampProfile k M hk).deficit a = k * max 0 (a - M) := rfl

theorem rampProfile_deficit_zero {k M : ℝ} (hk : 0 ≤ k) (hM : 0 < M) :
    (rampProfile k M hk).deficit 0 = 0 := by
  rw [rampProfile_deficit, max_eq_left (by linarith : (0 : ℝ) - M ≤ 0), mul_zero]

/-- Below the ramp's onset the secant rate vanishes, exactly as for the flat profile. -/
theorem secantRate_rampProfile_of_le {k M a : ℝ} (hk : 0 ≤ k) (hM : 0 < M) (haM : a ≤ M) :
    secantRate (rampProfile k M hk) a = 0 := by
  rw [secantRate, rampProfile_deficit, rampProfile_deficit_zero hk hM,
    max_eq_left (by linarith : a - M ≤ 0), mul_zero, sub_zero, zero_div]

theorem secantRate_flatProfile (a : ℝ) : secantRate flatProfile a = 0 := by
  simp [secantRate, flatProfile]

/-! ### 3. The ramp's rate is its height -/

/-- The rates a ramp never exceeds are exactly those at or above its height. -/
theorem rateBounds_rampProfile {k M : ℝ} (hk : 0 ≤ k) (hM : 0 < M) :
    rateBounds (rampProfile k M hk) = Set.Ici k := by
  ext γ
  simp only [rateBounds, Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · intro hγ
    by_contra hlt
    push_neg at hlt
    -- a large aperture forces `γ` above `k − kM/a`, which exceeds `γ` once `a` is big enough
    set a : ℝ := M + k * M / (k - γ) + 1 with hadef
    have hkγ : 0 < k - γ := by linarith
    have hk0 : 0 < k := lt_of_le_of_lt (le_of_lt (lt_of_lt_of_le hlt (le_refl γ))) hlt |>.trans_le hk
      |> fun _ => lt_of_le_of_ne hk (by intro h; rw [← h] at hlt; linarith)
    have hquot : 0 ≤ k * M / (k - γ) := by positivity
    have haM : M < a := by rw [hadef]; linarith
    have ha0 : 0 < a := lt_trans hM haM
    have hgoal := hγ a ha0
    rw [secantRate, rampProfile_deficit, rampProfile_deficit_zero hk hM, sub_zero,
      max_eq_right (by linarith : (0 : ℝ) ≤ a - M)] at hgoal
    rw [div_le_iff₀ ha0] at hgoal
    have hbig : k * M / (k - γ) < a - M := by rw [hadef]; linarith
    rw [div_lt_iff₀ hkγ] at hbig
    nlinarith [hgoal, hbig]
  · intro hγ a ha
    rw [secantRate, rampProfile_deficit, rampProfile_deficit_zero hk hM, sub_zero,
      div_le_iff₀ ha]
    have hle : max 0 (a - M) ≤ a := max_le ha.le (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hle hk]

/-- **The ramp's rate is its height.** -/
theorem profileRate_rampProfile {k M : ℝ} (hk : 0 ≤ k) (hM : 0 < M) :
    profileRate (rampProfile k M hk) = k := by
  rw [profileRate, rateBounds_rampProfile hk hM, csInf_Ici]

/-! ### 4. A bounded aperture range certifies nothing -/

/-- A reading that vanishes on the measured apertures is the same for any two such profiles. -/
theorem rateBoundsBelow_eq_of_vanishing (S : BoundedApertures) {g : GrowthProfile}
    (hg : ∀ a ∈ S.carrier, secantRate g a = 0) :
    rateBoundsBelow S g = {γ : ℝ | ∀ a ∈ S.carrier, (0 : ℝ) ≤ γ} := by
  ext γ
  simp only [rateBoundsBelow, Set.mem_setOf_eq]
  exact ⟨fun h a ha => by rw [← hg a ha]; exact h a ha,
    fun h a ha => by rw [hg a ha]; exact h a ha⟩

/-- Every ramp whose onset is at or beyond the aperture bound is invisible to the reading. -/
theorem rampProfile_mem_shadow (S : BoundedApertures) {k : ℝ} (hk : 0 ≤ k) :
    rampProfile k S.bound hk ∈ shadow (rateBoundsBelow S) flatProfile := by
  refine mem_shadow_iff.mpr ?_
  rw [rateBoundsBelow_eq_of_vanishing S
      (fun a ha => secantRate_rampProfile_of_le hk S.bound_pos (S.le_bound a ha)),
    rateBoundsBelow_eq_of_vanishing S (fun a _ => secantRate_flatProfile a)]

/-- **A bounded aperture range leaves the rate completely open.**  The rates realised inside the
shadow of the flat profile are unbounded above. -/
theorem not_bddAbove_profileRate_shadow (S : BoundedApertures) :
    ¬ BddAbove (profileRate '' shadow (rateBoundsBelow S) flatProfile) := by
  rintro ⟨B, hB⟩
  set k : ℝ := max B 0 + 1 with hk
  have hk0 : 0 ≤ k := by rw [hk]; have := le_max_right B 0; linarith
  have hmem : profileRate (rampProfile k S.bound hk0) ∈
      profileRate '' shadow (rateBoundsBelow S) flatProfile :=
    ⟨rampProfile k S.bound hk0, rampProfile_mem_shadow S hk0, rfl⟩
  have hle := hB hmem
  rw [profileRate_rampProfile hk0 S.bound_pos] at hle
  have : B < k := by rw [hk]; have := le_max_left B 0; linarith
  linarith

/-- **A bounded aperture range certifies no rate.**  No real number is a bound the reading
establishes. -/
theorem not_certifies_rateBoundsBelow (S : BoundedApertures) (β : ℝ) :
    ¬ Certifies profileRate (rateBoundsBelow S) flatProfile β := by
  intro hcert
  exact not_bddAbove_profileRate_shadow S ⟨β, by rintro x ⟨g, hg, rfl⟩; exact hcert g hg⟩

/-- **The rate dichotomy is sharp.**  A cofinal aperture set reads the rate exactly; an aperture
set confined below a bound certifies nothing at all. -/
theorem theRateDichotomyIsSharp (S : BoundedApertures) :
    (¬ BddAbove (profileRate '' shadow (rateBoundsBelow S) flatProfile)) ∧
      ∀ β : ℝ, ¬ Certifies profileRate (rateBoundsBelow S) flatProfile β :=
  ⟨not_bddAbove_profileRate_shadow S, not_certifies_rateBoundsBelow S⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
