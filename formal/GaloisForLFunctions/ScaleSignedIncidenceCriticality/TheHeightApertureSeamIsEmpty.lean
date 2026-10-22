import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheApertureLadderIsStrictYetEveryStageIsTrivial

/-!
# The height–aperture seam is empty

A bounded aperture has resolution limit `½` for the width, and so has a bounded height. Joining two
readings intersects their shadows, so the general theory only gives
`resolutionLimit ≤ min = ½` for the pair: joining could in principle be strictly better than either
part. *Exploiting a seam* between two proved barriers means exactly that strict drop. Here the
drop is computed and there is none.

The witness is one object carrying both collapses at once: the doubled on-line lattice of spacing
`2π/L` with a single reflected off-line pair of depth `δ` inserted at ordinate `γ₀`. Placing the
pair above the truncation height makes it invisible to the divisor
(`heightReading_latticeWithPairAt`), and the isolated-pair visibility law makes its aperture-`a`
certificate an explicit inequality (`aperturePositivity_latticeWithPairAt_iff`):

`sinh (2 δ a) / δ ≤ 2 L + 2 a`.

* `depth_le_resolutionLimit_heightJoinAperture` — the **seam floor**: every depth obeying that
  inequality floors the joint limit. The floor is the largest depth the pair-visibility threshold
  admits at the pair `(L, a)`, so the seam has a unit of its own.
* `resolutionLimit_width_heightJoinAperture` — at every spacing `L ≥ 2a + sinh a` the joint limit
  of the bounded-height and bounded-aperture readings is exactly `½`.
* `resolutionLimit_width_heightFamilyJoinApertureFamily` — the same for *families*: an arbitrary
  family of truncation heights bounded by `T` together with an arbitrary family of apertures
  bounded by `A`, at every spacing `L ≥ 2A + sinh A`, still has joint limit `½`.

So the two zero-side walls do not leak into each other: no amount of finite-height divisor data
combined with any amount of bounded-aperture certificate data improves the trivial bound. Since
every spacing `L` large enough works and the pair sits at an arbitrary height, the statement is not
about a special configuration: it is the emptiness of the seam.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. One datum carrying both collapses -/

/-- The doubled on-line lattice of spacing `2π/L` with one reflected off-line pair of depth `δ`
inserted at ordinate `γ₀`. -/
noncomputable def latticeWithPairAt {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (γ₀ : ℝ) : TemperedZeroConfig :=
  ⟨isolatedPairConfig hL hδ hδ' γ₀, temperedConfig_isolatedPairConfig hL hδ hδ' γ₀⟩

/-- The inserted pair sits at depth `δ`, so the width is at least `δ`. -/
theorem depth_le_width_latticeWithPairAt {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (γ₀ : ℝ) : δ ≤ width (latticeWithPairAt hL hδ hδ' γ₀) := by
  have hmem : offLinePoint δ γ₀ ∈ (isolatedPairConfig hL hδ hδ' γ₀).carrier :=
    Or.inl (Or.inr rfl)
  have h := abs_re_sub_half_le_configWidth hmem
  have hre : |(offLinePoint δ γ₀).re - 1 / 2| = δ := by
    simp only [offLinePoint]
    rw [show (1 / 2 + δ : ℝ) - 1 / 2 = δ by ring, abs_of_pos hδ]
  rwa [hre] at h

/-- **The pair above the truncation height is invisible to the divisor.** -/
theorem heightReading_latticeWithPairAt {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {T γ₀ : ℝ} (hγ : T < |γ₀|) :
    heightReading T (latticeWithPairAt hL hδ hδ' γ₀) = heightReading T (onLineLattice hL) := by
  have habove : ¬ |γ₀| ≤ T := not_le.mpr hγ
  funext ρ
  by_cases hρ : ρ ∈ heightWindow T (onLineLattice hL)
  · obtain ⟨hc, hT⟩ := mem_heightWindow.mp hρ
    obtain ⟨k, rfl⟩ := hc
    have hre : (verticalLatticePoint L 0 k).re = 1 / 2 := by simp [verticalLatticePoint]
    have hmemP : verticalLatticePoint L 0 k ∈
        heightWindow T (latticeWithPairAt hL hδ hδ' γ₀) :=
      mem_heightWindow.mpr ⟨Or.inl (Or.inl ⟨k, rfl⟩), hT⟩
    have hmem0 : verticalLatticePoint L 0 k ∈ heightWindow T (onLineLattice hL) :=
      mem_heightWindow.mpr ⟨⟨k, rfl⟩, hT⟩
    have h1 : (latticeWithPairAt hL hδ hδ' γ₀).1.mult (verticalLatticePoint L 0 k) = 2 := by
      show (if (verticalLatticePoint L 0 k).re = 1 / 2 then 2 else 1) = 2
      rw [if_pos hre]
    have h2 : (onLineLattice hL).1.mult (verticalLatticePoint L 0 k) = 2 := rfl
    rw [heightReading_of_mem hmemP, heightReading_of_mem hmem0, h1, h2]
  · have hpair : ρ ∉ heightWindow T (latticeWithPairAt hL hδ hδ' γ₀) := by
      intro hmem
      obtain ⟨hc, hT⟩ := mem_heightWindow.mp hmem
      rcases hc with (hlat | hp) | hp
      · exact hρ (mem_heightWindow.mpr ⟨hlat, hT⟩)
      · rw [Set.mem_singleton_iff] at hp
        subst hp
        exact habove (by simpa [offLinePoint] using hT)
      · rw [Set.mem_singleton_iff] at hp
        subst hp
        exact habove (by simpa [offLinePoint] using hT)
    rw [heightReading_of_notMem hpair, heightReading_of_notMem hρ]

/-- **The aperture certificate of the witness is one explicit inequality.** Below the Nyquist
aperture of the background lattice, the pair of depth `δ` is hidden at aperture `a` exactly when
`sinh (2 δ a) / δ ≤ 2 L + 2 a`. -/
theorem aperturePositivity_latticeWithPairAt_iff {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2) :
    aperturePositivity a (latticeWithPairAt hL hδ hδ' γ₀) ↔
      Real.sinh (2 * δ * a) / δ ≤ 2 * L + 2 * a :=
  isolatedPairConfig_weil_nonneg_iff hL hδ hδ' γ₀ ha haL

/-! ### 2. The seam floor -/

/-- **The seam floor.** Joining the divisor truncated at height `T` with the aperture-`a`
certificate still admits every depth the pair-visibility threshold allows: that depth floors the
joint resolution limit of the width. -/
theorem depth_le_resolutionLimit_heightJoinAperture {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2)
    (hth : Real.sinh (2 * δ * a) / δ ≤ 2 * L + 2 * a) (T : ℝ) :
    δ ≤ resolutionLimit width (joinReading (heightReading T) (aperturePositivity a))
      (onLineLattice hL) := by
  set Z : TemperedZeroConfig := latticeWithPairAt hL hδ hδ' (|T| + 1) with hZ
  have hγ : T < |(|T| + 1 : ℝ)| := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |T| + 1)]
    linarith [le_abs_self T]
  have hheight : heightReading T Z = heightReading T (onLineLattice hL) :=
    heightReading_latticeWithPairAt hL hδ hδ' hγ
  have haper : aperturePositivity a Z = aperturePositivity a (onLineLattice hL) :=
    propext (iff_of_true ((aperturePositivity_latticeWithPairAt_iff hL hδ hδ' _ ha haL).mpr hth)
      (aperturePositivity_onLineLattice hL a))
  have hmem : Z ∈ shadow (joinReading (heightReading T) (aperturePositivity a))
      (onLineLattice hL) :=
    (shadow_joinReading _ _ _).symm.subset ⟨hheight, haper⟩
  exact (depth_le_width_latticeWithPairAt hL hδ hδ' (|T| + 1)).trans
    (le_csSup (bddAbove_width_image _) ⟨Z, hmem, rfl⟩)

/-! ### 3. The seam is empty -/

/-- **The height–aperture seam is empty.** At every spacing `L ≥ 2a + sinh a` the joint reading of
the divisor truncated at height `T` and the aperture-`a` certificate has resolution limit exactly
`½` for the width: combining the two bounded zero-side readings gains nothing over either. -/
theorem resolutionLimit_width_heightJoinAperture {L a : ℝ} (ha : 0 < a)
    (hLa : 2 * a + Real.sinh a ≤ L) (T : ℝ) (hL : 0 < L) :
    resolutionLimit width (joinReading (heightReading T) (aperturePositivity a))
      (onLineLattice hL) = 1 / 2 := by
  have hs : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  refine le_antisymm (csSup_le (shadow_image_nonempty width _ _) ?_) ?_
  · rintro x ⟨W, -, rfl⟩
    exact width_le_half W
  · refine depth_le_resolutionLimit_heightJoinAperture hL (by norm_num) le_rfl ha
      (by linarith) ?_ T
    rw [show 2 * (1 / 2 : ℝ) * a = a by ring]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith

/-! ### 4. Families on both axes -/

/-- **No bounded data on either zero-side axis.** An arbitrary family of truncation heights bounded
by `T`, joined with an arbitrary family of apertures bounded by `A`, has resolution limit exactly
`½` for the width at every spacing `L ≥ 2A + sinh A`. Neither axis leaks into the other, and
cardinality is irrelevant on both. -/
theorem resolutionLimit_width_heightFamilyJoinApertureFamily {ι κ : Type*} (Tf : κ → ℝ)
    (af : ι → ℝ) {T A L : ℝ} (hA : 0 < A) (hTb : ∀ j : κ, Tf j ≤ T) (hAb : ∀ i : ι, af i ≤ A)
    (hLA : 2 * A + Real.sinh A ≤ L) (hL : 0 < L) :
    resolutionLimit width
        (joinReading (familyReading fun j : κ => heightReading (Tf j)) (familyPositivity af))
        (onLineLattice hL) = 1 / 2 := by
  have hs : 0 < Real.sinh A := Real.sinh_pos_iff.mpr hA
  set Z : TemperedZeroConfig :=
    latticeWithPairAt hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl (|T| + 1) with hZ
  have hA' : A ≤ L / 2 := by linarith
  have hthr : Real.sinh (2 * (1 / 2 : ℝ) * A) / (1 / 2 : ℝ) ≤ 2 * L + 2 * A := by
    rw [show 2 * (1 / 2 : ℝ) * A = A by ring, div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hposA : aperturePositivity A Z :=
    (aperturePositivity_latticeWithPairAt_iff hL _ le_rfl _ hA hA').mpr hthr
  -- the pair sits above every height of the family
  have hheight : (familyReading fun j : κ => heightReading (Tf j)) Z =
      (familyReading fun j : κ => heightReading (Tf j)) (onLineLattice hL) := by
    refine funext fun j => heightReading_latticeWithPairAt hL _ le_rfl ?_
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |T| + 1)]
    linarith [hTb j, le_abs_self T]
  have haper : familyPositivity af Z = familyPositivity af (onLineLattice hL) :=
    propext (iff_of_true (fun i => aperturePositivity_mono (hAb i) hposA)
      (fun i => aperturePositivity_onLineLattice hL (af i)))
  have hmem : Z ∈ shadow
      (joinReading (familyReading fun j : κ => heightReading (Tf j)) (familyPositivity af))
      (onLineLattice hL) :=
    (shadow_joinReading _ _ _).symm.subset ⟨hheight, haper⟩
  refine le_antisymm (csSup_le (shadow_image_nonempty width _ _) ?_) ?_
  · rintro x ⟨W, -, rfl⟩
    exact width_le_half W
  · exact (depth_le_width_latticeWithPairAt hL (by norm_num) le_rfl (|T| + 1)).trans
      (le_csSup (bddAbove_width_image _) ⟨Z, hmem, rfl⟩)

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
