import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheApertureLadderIsStrictYetEveryStageIsTrivial

/-!
# Readings transport along a presentation

A proposed mechanism never works on the model objects of a barrier. It works on its own data — a
mollifier, an operator realisation, a sieve datum, a family of parameters — and *presents* a
configuration: there is a map `π : D' → D` from the mechanism's data to the data of the barrier.
Without a transport law the gates cannot be instantiated at all, because the mechanism's reading is
a reading of `D'`, not of `D`.

A **presentation** is any map `π : D' → D`. Pulling a reading back along it gives
`shadow (r ∘ π) d' = π ⁻¹' shadow r (π d')` (`shadow_comp`), so:

* resolution transports forwards always (`Resolves.comp`) and backwards along a surjection
  (`resolves_of_surjective_of_comp`);
* invisible collapses lift whenever they lift as maps (`Invisible.lift`);
* the limit never increases (`resolutionLimit_comp_le`) and is **exactly preserved** when `π`
  covers the shadow (`resolutionLimit_comp_eq_of_covers`).

Two consequences make the gates usable.

* `resolutionLimit_eq_of_refines_of_mem` — the **coarsening floor**: any reading that identifies
  whatever a bounded-aperture certificate identifies has limit exactly `½`, whatever else it
  reads. One does not have to recompute a witness per mechanism.
* `resolutionLimit_width_enriched_aperturePositivity` — **enrichment stability**: attaching
  arbitrary extra apparatus to the configuration (any type `E` of auxiliary data) leaves the limit
  at `½` as long as the reading is still the certificate of the presented configuration. The floor
  is a property of the partition a reading induces, not of the data class it is written on.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

variable {D D' O : Type*} {I : D → ℝ}

/-! ### 1. Pulling a reading back along a presentation -/

/-- The shadow of a pulled-back reading is the preimage of the shadow. -/
theorem shadow_comp (π : D' → D) (r : D → O) (d' : D') :
    shadow (r ∘ π) d' = π ⁻¹' shadow r (π d') := rfl

/-- Resolution transports forwards along every presentation. -/
theorem Resolves.comp {r : D → O} {P : D → Prop} (hres : Resolves r P) (π : D' → D) :
    Resolves (r ∘ π) (P ∘ π) := fun d' e' he' => hres (π d') (π e') he'

/-- Along a surjection, resolution transports backwards as well: a mechanism that decides the
pulled-back property decides the property. -/
theorem resolves_of_surjective_of_comp {r : D → O} {P : D → Prop} {π : D' → D}
    (hπ : Function.Surjective π) (hres : Resolves (r ∘ π) (P ∘ π)) : Resolves r P := by
  intro d e he
  obtain ⟨d', rfl⟩ := hπ d
  obtain ⟨e', rfl⟩ := hπ e
  exact hres d' e' he

/-- A collapse that lifts through the presentation stays invisible. -/
theorem Invisible.lift {r : D → O} {κ : D → D} (h : Invisible r κ) {π : D' → D} {κ' : D' → D'}
    (hlift : ∀ d' : D', π (κ' d') = κ (π d')) : Invisible (r ∘ π) κ' := fun d' => by
  show r (π (κ' d')) = r (π d')
  rw [hlift d', h (π d')]

/-- The pulled-back limit never exceeds the limit: a presentation can only lose shadow. -/
theorem resolutionLimit_comp_le (π : D' → D) {r : D → O} {d' : D'}
    (hbdd : BddAbove (I '' shadow r (π d'))) :
    resolutionLimit (I ∘ π) (r ∘ π) d' ≤ resolutionLimit I r (π d') :=
  csSup_le (shadow_image_nonempty (I ∘ π) (r ∘ π) d') (by
    rintro x ⟨e', he', rfl⟩
    exact le_csSup hbdd ⟨π e', he', rfl⟩)

/-- **Exact transport.** When the presentation covers the shadow, the limit is preserved: the floor
of a barrier is a floor for every mechanism presenting its data. -/
theorem resolutionLimit_comp_eq_of_covers {π : D' → D} {r : D → O} {d' : D'}
    (hcov : ∀ e ∈ shadow r (π d'), ∃ e' : D', π e' = e)
    (hbdd : BddAbove (I '' shadow r (π d'))) :
    resolutionLimit (I ∘ π) (r ∘ π) d' = resolutionLimit I r (π d') := by
  refine le_antisymm (resolutionLimit_comp_le π hbdd) ?_
  refine csSup_le (shadow_image_nonempty I r (π d')) ?_
  rintro x ⟨e, he, rfl⟩
  obtain ⟨e', rfl⟩ := hcov e he
  exact le_csSup
    (⟨resolutionLimit I r (π d'), by
        rintro y ⟨f', hf', rfl⟩
        exact le_csSup hbdd ⟨π f', hf', rfl⟩⟩ :
      BddAbove ((I ∘ π) '' shadow (r ∘ π) d'))
    ⟨e', he, rfl⟩

/-! ### 2. The coarsening floor -/

/-- **Coarsening floor.** If a reading identifies whatever a bounded-aperture certificate
identifies, its resolution limit for the width is exactly `½` — whatever else it reads. -/
theorem resolutionLimit_eq_of_refines_of_mem {a : ℝ} (ha : 0 < a) {O : Type*}
    {r : TemperedZeroConfig → O} (href : Refines (aperturePositivity a) r)
    {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    resolutionLimit width r Z = 1 / 2 := by
  refine le_antisymm (csSup_le (shadow_image_nonempty width r Z) ?_) ?_
  · rintro x ⟨W, -, rfl⟩
    exact width_le_half W
  · rw [← resolutionLimit_width_aperturePositivity ha hZ]
    exact resolutionLimit_le_of_refines href (bddAbove_width_image _)

/-! ### 3. Enrichment stability -/

/-- A mechanism's datum: a configuration together with arbitrary auxiliary apparatus. -/
def EnrichedConfig (E : Type*) : Type _ := TemperedZeroConfig × E

/-- The presentation: forget the apparatus. -/
def presentedConfig {E : Type*} (x : EnrichedConfig E) : TemperedZeroConfig := x.1

/-- **Enrichment stability.** A mechanism carrying any amount of auxiliary apparatus, but reading
only the aperture-`a` certificate of the configuration it presents, still has resolution limit
exactly `½` for the width. Extra apparatus that the reading does not look at is worth nothing. -/
theorem resolutionLimit_width_enriched_aperturePositivity {E : Type*} [Nonempty E] {a : ℝ}
    (ha : 0 < a) {x : EnrichedConfig E} (hx : aperturePositivity a (presentedConfig x)) :
    resolutionLimit (width ∘ presentedConfig) (aperturePositivity a ∘ presentedConfig) x
      = 1 / 2 := by
  have htrans := resolutionLimit_comp_eq_of_covers (I := width)
    (π := presentedConfig (E := E)) (r := aperturePositivity a) (d' := x)
    (fun e _ => ⟨(e, Classical.arbitrary E), rfl⟩) (bddAbove_width_image _)
  rw [htrans]
  exact resolutionLimit_width_aperturePositivity ha hx

/-- **The presented gate.** A mechanism on any data class whose reading factors through the
aperture-`a` certificate of the configuration it presents cannot decide the critical line. -/
theorem not_resolves_presented_aperturePositivity {E : Type*} {a : ℝ} (ha : 0 < a)
    {O : Type*} (g : Prop → O) {x : EnrichedConfig E}
    (hx : aperturePositivity a (presentedConfig x)) :
    ¬ Resolves (fun y : EnrichedConfig E => g (aperturePositivity a (presentedConfig y)))
      (fun y => width (presentedConfig y) = 0) := by
  obtain ⟨Z, hw, hpos⟩ := exists_width_eq_half_aperturePositivity ha
  intro hres
  have hres' : Resolves (aperturePositivity a ∘ presentedConfig)
      (fun y : EnrichedConfig E => width (presentedConfig y) = 0) :=
    Resolves.of_refines (refines_of_comp _ (fun _ => rfl)) hres
  have hmem : ((Z, x.2) : EnrichedConfig E) ∈
      shadow (aperturePositivity a ∘ presentedConfig) ((presentedConfig x, x.2)) :=
    propext (iff_of_true hpos hx)
  have hx0 : width (presentedConfig x) = 0 → width Z = 0 := fun h =>
    (hres' (presentedConfig x, x.2) (Z, x.2) hmem).mpr h
  -- the on-line lattice shares the certificate, so the property is not constant on the shadow
  have hline : aperturePositivity a (onLineLattice (by norm_num : (0 : ℝ) < 1)) :=
    aperturePositivity_onLineLattice _ a
  have hmem2 : ((onLineLattice (by norm_num : (0 : ℝ) < 1), x.2) : EnrichedConfig E) ∈
      shadow (aperturePositivity a ∘ presentedConfig) ((presentedConfig x, x.2)) :=
    propext (iff_of_true hline hx)
  have h0 : width (presentedConfig x) = 0 :=
    (hres' (presentedConfig x, x.2) _ hmem2).mp
      (width_onLineLattice (by norm_num : (0 : ℝ) < 1))
  rw [hw] at hx0
  norm_num at hx0
  exact hx0 h0

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
