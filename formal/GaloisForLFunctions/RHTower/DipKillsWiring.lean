/-
Tier wiring (doc 54 §5): the `dip_kills` field of `MidCentralInput`
discharged from CONCRETE carrier data, making the true remaining hypotheses
explicit.

Re-audit (this cycle): the digamma / θ_RS content is NOT on the critical
path for `dip_kills`. The tower's relative phases φ_{N−m} − φ_N are θ_RS-free
(the Riemann–Siegel theta term is m-independent, cancels in the difference),
so the walk step angles come from the banked, Gamma-free `log_ratio_bounds`
and the slip 2πd² is elementary in √(t/2π). What `dip_kills` genuinely needs,
per non-resonant birth, is the explicit-polar hypothesis bundle:
misalignment of the closed-form angle, step-angle bounds, envelope bounds,
phase-error budget, and the depth inequality.

`CarrierBirthData` packages that bundle per birth; `dipKills_of_carrierData`
produces the `dip_kills` field. Hence `MidCentralInput` (and so
`midCentral_survivors_le`) follows from `CarrierBirthData` for the
non-resonant births PLUS the creation-rate bound (the (T3) open core) — no
digamma anchor in between.
-/
import GaloisForLFunctions.RHTower.MidCentral
import GaloisForLFunctions.RHTower.PerturbedDip

namespace RHTower

/-- Concrete per-birth carrier data sufficient to kill a non-resonant birth.
The polar identity and nonresonance are now discharged from `0 < θ ≤ π/3` by
`birthKilled_of_perturbed_rotation_explicit_polar`; callers supply only the
closed-form-angle misalignment and matching depth inequality. -/
structure CarrierBirthData (pushes : List ℝ) (birth : CascadeBirth) where
  θ : ℝ
  β : ℝ
  δ : ℝ
  e₀ : ℝ
  amin : ℝ
  amax : ℝ
  amp : ℕ → ℝ
  ε : ℕ → ℝ
  P : ℕ
  θ_pos : 0 < θ
  θ_le : θ ≤ Real.pi / 3
  amin_nonneg : 0 ≤ amin
  amp_bounds : ∀ m : ℕ, amin ≤ amp m ∧ amp m ≤ amax
  depth_pos : 0 < birth.depthSq
  push_form : futurePushes pushes birth
    = (List.range P).map fun m : ℕ => amp m * Real.cos (β + (m : ℝ) * θ + ε m)
  len_ok : 2 * Real.pi + 2 * θ ≤ (P : ℝ) * θ
  misaligned : Real.cos (β - θ / 2 + Real.pi / 2) ≤ 1 - δ
  phase_err : ∀ m : ℕ, |ε m| ≤ e₀
  deep : birth.depthSq
    ≤ amin * ((1 / (2 * Real.sin (θ / 2))) * (δ - (1 - Real.cos (θ / 2))))
      - ((2 * Real.pi + 2 * θ) / θ) * (amin * e₀ + (amax - amin))

/-- The carrier data kills the birth. -/
theorem birthKilled_of_carrierData {pushes : List ℝ} {birth : CascadeBirth}
    (d : CarrierBirthData pushes birth) : BirthKilled pushes birth :=
  birthKilled_of_perturbed_rotation_explicit_polar d.θ_pos
    (le_trans d.θ_le (by linarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi))
    d.amin_nonneg d.amp_bounds d.depth_pos d.push_form d.len_ok
    d.misaligned d.phase_err d.deep

/-- **`dip_kills` from carrier data**: if every non-resonant birth carries the
concrete data bundle, the `dip_kills` field of `MidCentralInput` holds — with
NO digamma anchor and NO abstract dip hypothesis. -/
theorem dipKills_of_carrierData {pushes : List ℝ} {births : List CascadeBirth}
    {κ : ℝ} {slip : CascadeBirth → ℝ}
    (hdata : ∀ b ∈ births, ¬ SlipWindow κ slip b → CarrierBirthData pushes b) :
    ∀ b ∈ births, ¬ SlipWindow κ slip b →
      ∃ l₁, l₁ <+: futurePushes pushes b ∧ b.depthSq + pushSum l₁ ≤ 0 := by
  intro b hb hnres
  have hkilled := birthKilled_of_carrierData (hdata b hb hnres)
  -- BirthKilled is KilledFrom on the future pushes; extract a killing prefix
  -- via the total-push witness. We rebuild the prefix from `KilledFrom`.
  have hgen : ∀ (l : List ℝ) (d : ℝ), KilledFrom d l →
      ∃ l₁, l₁ <+: l ∧ d + pushSum l₁ ≤ 0 := by
    intro l
    induction l with
    | nil =>
      intro d hk
      exact ⟨[], List.nil_prefix, by simpa [pushSum] using hk⟩
    | cons q qs ih =>
      intro d hk
      dsimp [KilledFrom] at hk
      rcases hk with hnow | ⟨_, hlater⟩
      · exact ⟨[q], ⟨qs, rfl⟩, by simpa [pushSum] using hnow⟩
      · obtain ⟨l₁, hpre, hsum⟩ := ih (d + q) hlater
        obtain ⟨tl, htl⟩ := hpre
        refine ⟨q :: l₁, ⟨tl, ?_⟩, ?_⟩
        · simp [htl]
        · simp only [pushSum]
          linarith
  exact hgen (futurePushes pushes b) b.depthSq hkilled

/-- **The concrete (MID-central) input**: carrier data for the non-resonant
births plus the creation-rate bound (the (T3) open core) gives
`MidCentralInput` — hence at most `K` survivors, all in the slip window. This
is the honest reduction: everything but `creation_rate` is discharged from
banked lemmas and elementary/per-instance carrier data. -/
theorem midCentralInput_of_carrierData {pushes : List ℝ}
    {births : List CascadeBirth} {κ : ℝ} {slip : CascadeBirth → ℝ} {K : ℕ}
    (hdepth : ∀ b ∈ births, 0 < b.depthSq)
    (hdata : ∀ b ∈ births, ¬ SlipWindow κ slip b → CarrierBirthData pushes b)
    (hcreation : (resonantBirths (SlipWindow κ slip) births).length ≤ K) :
    MidCentralInput pushes births κ slip K :=
  { depth_pos := hdepth
    dip_kills := dipKills_of_carrierData hdata
    creation_rate := hcreation }

/-- The end-to-end concrete reduction: carrier data + creation bound ⇒ at most
`K` mid-band survivors. -/
theorem midCentral_survivors_le_of_carrierData {pushes : List ℝ}
    {births : List CascadeBirth} {κ : ℝ} {slip : CascadeBirth → ℝ} {K : ℕ}
    (hdepth : ∀ b ∈ births, 0 < b.depthSq)
    (hdata : ∀ b ∈ births, ¬ SlipWindow κ slip b → CarrierBirthData pushes b)
    (hcreation : (resonantBirths (SlipWindow κ slip) births).length ≤ K) :
    (survivingBirths pushes births).length ≤ K :=
  midCentral_survivors_le
    (midCentralInput_of_carrierData hdepth hdata hcreation)

end RHTower
