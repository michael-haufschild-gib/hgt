import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheRightApertureIndexIncludesExactlyTheNullModes
import GaloisForLFunctions.RHTower.FiniteSmoothWeilGramsAndRestrictedIndex
import GaloisForLFunctions.RHTower.PaperRestrictedWeilGroundThreshold
import GaloisForLFunctions.ArithmeticCriticalityTheory.WindowGaugeLogarithmicGroundEnergyFloor
import GaloisForLFunctions.SquareRootThreshold.TheRoutesMeasureOneAperture

/-!
# The index at an aperture is the sum of the nullities below it

Weil's form restricted to the aperture `a`, shifted by the energy `E`, has a finite negative index
`negativeRank a E` and a finite space of null modes of dimension `weilNullity a E`. The apertures
form a path of quadratic forms on an increasing family of spaces. Its index obeys the law of a
Morse index:

  `negativeRank b E = Σ_{a < b} weilNullity a E`   (`negativeRank_eq_sum_nullity`),

a finite sum over the resonant apertures below `b`. Three properties of the path give it.

* **Left continuity** (`exists_smaller_aperture_negativeRank_eq`). The index is attained on a
  finite family of smooth packets supported strictly inside the aperture; their supports are
  compact, so the family lives in a smaller aperture, where form and mass are the same.
* **The jump to the right** is the nullity (corpus), and the index does not decrease.
* **The start** (`exists_aperture_negativeRank_eq_zero`). The ground energy of a short window is
  at least `−log(2a) − C`, so at every energy the index vanishes at small apertures.

The proof is an induction on the index: below the last aperture of smaller index the law holds,
and that aperture carries the missing null modes.

Consequences: the index at `b` vanishes iff no smaller aperture carries a null mode
(`negativeRank_eq_zero_iff_forall_weilNullity`); the Riemann hypothesis holds iff no aperture
carries a null mode at the energy zero (`riemannHypothesis_iff_forall_weilNullity_zero`).
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil
open ArithmeticContinuationAndCriticalEnergy HTGeometry

/-! ### Left continuity -/

/-- A compact subset of an open symmetric interval lies in a smaller one. -/
theorem exists_lt_subset_Ioo {K : Set ℝ} (hK : IsCompact K) {a : ℝ} (ha : 0 < a)
    (hKa : K ⊆ Ioo (-a) a) : ∃ c, 0 < c ∧ c < a ∧ K ⊆ Ioo (-c) c := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨a / 2, by linarith, by linarith, empty_subset _⟩
  · obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hne continuous_abs.continuousOn
    have hlt : |x₀| < a := abs_lt.mpr (hKa hx₀)
    refine ⟨(|x₀| + a) / 2, by linarith [abs_nonneg x₀], by linarith, fun x hx => ?_⟩
    have hx' : |x| ≤ |x₀| := isMaxOn_iff.mp hmax x hx
    exact abs_lt.mp (by linarith)

/-- The mass pairing of two smooth packets does not depend on the aperture in which they are
placed. -/
theorem inner_physical_congr {a c : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource c) (u' v' : CCMComplexSmoothInteriorSource a)
    (hu : ∀ x, u x = u' x) (hv : ∀ x, v x = v' x) :
    inner ℂ (ccmArchimedeanFormToAperture c u.toCCMFormVector)
        (ccmArchimedeanFormToAperture c v.toCCMFormVector) =
      inner ℂ (ccmArchimedeanFormToAperture a u'.toCCMFormVector)
        (ccmArchimedeanFormToAperture a v'.toCCMFormVector) := by
  change inner ℂ (ccmArchimedeanFormToAperture c u.toCCMFormVector : SoninL2)
      (ccmArchimedeanFormToAperture c v.toCCMFormVector : SoninL2) =
    inner ℂ (ccmArchimedeanFormToAperture a u'.toCCMFormVector : SoninL2)
      (ccmArchimedeanFormToAperture a v'.toCCMFormVector : SoninL2)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [u.toCCMFormVector_physical_coeFn, v.toCCMFormVector_physical_coeFn,
    u'.toCCMFormVector_physical_coeFn, v'.toCCMFormVector_physical_coeFn] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4, hu, hv]

/-- **Left continuity of the index.** The index at an aperture is attained at a smaller
aperture. -/
theorem exists_smaller_aperture_negativeRank_eq (a : SuzukiPositiveAperture) (E : ℝ) :
    ∃ c : SuzukiPositiveAperture, c.1 < a.1 ∧ negativeRank c E = negativeRank a E := by
  obtain ⟨f, hf⟩ := exists_smoothShiftedWeilGram_index_eq a E
  have hK : IsCompact (⋃ i, tsupport (f i : ℝ → ℂ)) :=
    isCompact_iUnion fun i => (f i).hasCompactSupport.isCompact
  have hKa : (⋃ i, tsupport (f i : ℝ → ℂ)) ⊆ Ioo (-a.1) a.1 :=
    iUnion_subset fun i => (f i).tsupport_subset
  obtain ⟨c, hc0, hca, hKc⟩ := exists_lt_subset_Ioo hK a.2 hKa
  -- the same packets, placed in the aperture `c`
  let g : Fin (negativeRank a E) →
      CCMComplexSmoothInteriorSource (⟨c, hc0⟩ : SuzukiPositiveAperture) :=
    fun i => ⟨f i, (f i).smooth, (f i).hasCompactSupport,
      (subset_iUnion (fun i => tsupport (f i : ℝ → ℂ)) i).trans hKc⟩
  have hgram : smoothShiftedWeilGram E g = smoothShiftedWeilGram E f := by
    ext i j
    simp only [smoothShiftedWeilGram]
    rw [inner_physical_congr (g i) (g j) (f i) (f j) (fun _ => rfl) (fun _ => rfl)]
  refine ⟨⟨c, hc0⟩, hca, le_antisymm (negativeRank_mono_of_aperture_le hca.le E) ?_⟩
  calc negativeRank a E = hermNegIndex (smoothShiftedWeilGram E f) := hf.symm
    _ = hermNegIndex (smoothShiftedWeilGram E g) := by rw [hgram]
    _ ≤ negativeRank ⟨c, hc0⟩ E := hermNegIndex_smoothShiftedWeilGram_le E g

/-! ### The start of the path -/

/-- **At every energy the index vanishes at small apertures**: the ground energy of a short
window is at least `−log(2a) − (3/2)a − (γ + log π) − 4a³`. -/
theorem exists_aperture_negativeRank_eq_zero (E : ℝ) :
    ∃ a : SuzukiPositiveAperture, negativeRank a E = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = 2 * RHTower.CHMDPolar.archConstantReal := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = min (1 / 4) (Real.exp (-(E + k + 1)) / 2) := ⟨_, rfl⟩
  have hR0 : 0 < R := by
    rw [hR]
    exact lt_min (by norm_num) (by positivity)
  have hR1 : R ≤ 1 / 4 := by
    rw [hR]
    exact min_le_left _ _
  have hR2 : 2 * R ≤ Real.exp (-(E + k + 1)) := by
    have := min_le_right (1 / 4 : ℝ) (Real.exp (-(E + k + 1)) / 2)
    rw [← hR] at this
    linarith
  have hlog : Real.log (2 * R) ≤ -(E + k + 1) := by
    have h := Real.log_le_log (mul_pos two_pos hR0) hR2
    rwa [Real.log_exp] at h
  have hR3 : R ^ 3 ≤ 1 / 64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR1) (sq_nonneg R),
      mul_nonneg (sub_nonneg.mpr hR1) hR0.le]
  have hfloor : E ≤ ArithmeticCriticalityTheory.windowFloor R := by
    unfold ArithmeticCriticalityTheory.windowFloor
    linarith
  have hlt : 2 * R < Real.log 2 := by linarith [Real.log_two_gt_d9]
  exact ⟨⟨R, hR0⟩, (negativeRank_eq_zero_iff_ground _ E).mpr (hfloor.trans
    (ArithmeticCriticalityTheory.windowFloor_le_ccmRestrictedWeilGroundEnergy_self
      (A := ⟨R, hR0⟩) hlt))⟩

/-! ### The index law -/

/-- The resonant apertures below `b` at the energy `E`: those that carry a null mode. -/
def resonantBelow (b : SuzukiPositiveAperture) (E : ℝ) : Finset SuzukiPositiveAperture :=
  (finite_resonant_apertures_below b E).toFinset

theorem mem_resonantBelow {a b : SuzukiPositiveAperture} {E : ℝ} :
    a ∈ resonantBelow b E ↔ a.1 < b.1 ∧ 0 < weilNullity a E := by
  rw [resonantBelow, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- The index is at most the sum of the nullities below: induction on the index. Below the last
aperture `s` of index less than `n` the law holds; just to the right of `s` the index is `n`, so
`s` carries the missing null modes. -/
theorem negativeRank_le_sum_nullity (E : ℝ) :
    ∀ (n : ℕ) (b : SuzukiPositiveAperture), negativeRank b E = n →
      n ≤ ∑ a ∈ resonantBelow b E, weilNullity a E := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hb
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Nat.zero_le _
    obtain ⟨a₀, ha₀⟩ := exists_aperture_negativeRank_eq_zero E
    -- the apertures of index below `n`
    obtain ⟨T, hT⟩ : ∃ T : Set ℝ,
        T = {t | ∃ a : SuzukiPositiveAperture, a.1 = t ∧ negativeRank a E < n} := ⟨_, rfl⟩
    have hT0 : a₀.1 ∈ T := by
      rw [hT]
      exact ⟨a₀, rfl, by omega⟩
    have hTb : ∀ t ∈ T, t ≤ b.1 := by
      intro t ht
      rw [hT] at ht
      obtain ⟨a, rfl, ha⟩ := ht
      by_contra hlt
      have := negativeRank_mono_of_aperture_le (not_le.mp hlt).le E
      omega
    have hbdd : BddAbove T := ⟨b.1, hTb⟩
    have hs0 : 0 < sSup T := lt_of_lt_of_le a₀.2 (le_csSup hbdd hT0)
    obtain ⟨s, hs⟩ : ∃ s : SuzukiPositiveAperture, s.1 = sSup T := ⟨⟨sSup T, hs0⟩, rfl⟩
    -- left continuity: the index at `s` is below `n`
    have hsn : negativeRank s E < n := by
      obtain ⟨c, hcs, hc⟩ := exists_smaller_aperture_negativeRank_eq s E
      rw [hs] at hcs
      obtain ⟨t, ht, hct⟩ := exists_lt_of_lt_csSup ⟨a₀.1, hT0⟩ hcs
      rw [hT] at ht
      obtain ⟨a, rfl, ha⟩ := ht
      have := negativeRank_mono_of_aperture_le hct.le E
      omega
    have hsb : s.1 < b.1 := by
      refine lt_of_le_of_ne (hs ▸ csSup_le ⟨a₀.1, hT0⟩ hTb) fun h => ?_
      have h2 : negativeRank s E = negativeRank b E :=
        congrArg (fun x => negativeRank x E) (Subtype.ext h)
      omega
    -- just to the right of `s` the index is `n`
    obtain ⟨b', hsb', hjump⟩ := exists_right_interval_negativeRank_eq s E
    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : SuzukiPositiveAperture, c₀.1 = min b'.1 b.1 :=
      ⟨⟨min b'.1 b.1, lt_min b'.2 b.2⟩, rfl⟩
    have hc₀s : s.1 < c₀.1 := hc₀ ▸ lt_min hsb' hsb
    have hc₀j : negativeRank c₀ E = negativeRank s E + weilNullity s E :=
      hjump c₀ hc₀s (hc₀ ▸ min_le_left _ _)
    have hc₀n : negativeRank c₀ E = n := by
      have hle := negativeRank_mono_of_aperture_le (show c₀.1 ≤ b.1 from hc₀ ▸ min_le_right _ _) E
      have hge : n ≤ negativeRank c₀ E := by
        by_contra hlt
        have hmem : c₀.1 ∈ T := by
          rw [hT]
          exact ⟨c₀, rfl, not_le.mp hlt⟩
        exact absurd (le_csSup hbdd hmem) (not_le.mpr (hs ▸ hc₀s))
      omega
    have hih := ih (negativeRank s E) hsn s rfl
    have hsub : resonantBelow s E ⊆ resonantBelow b E := fun a ha => by
      rw [mem_resonantBelow] at ha ⊢
      exact ⟨ha.1.trans hsb, ha.2⟩
    rcases Nat.eq_zero_or_pos (weilNullity s E) with h0 | hpos
    · have h1 : ∑ a ∈ resonantBelow s E, weilNullity a E ≤
          ∑ a ∈ resonantBelow b E, weilNullity a E := Finset.sum_le_sum_of_subset hsub
      omega
    · have hs_not : s ∉ resonantBelow s E := fun h => lt_irrefl _ (mem_resonantBelow.mp h).1
      have hins : insert s (resonantBelow s E) ⊆ resonantBelow b E := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact mem_resonantBelow.mpr ⟨hsb, hpos⟩
        · exact hsub ha
      have h1 : ∑ a ∈ insert s (resonantBelow s E), weilNullity a E ≤
          ∑ a ∈ resonantBelow b E, weilNullity a E := Finset.sum_le_sum_of_subset hins
      rw [Finset.sum_insert hs_not] at h1
      omega

/-- **The index law of the aperture path.** The negative index at the aperture `b` and the
energy `E` is the sum of the nullities of the resonant apertures below `b`. -/
theorem negativeRank_eq_sum_nullity (b : SuzukiPositiveAperture) (E : ℝ) :
    negativeRank b E = ∑ a ∈ resonantBelow b E, weilNullity a E :=
  le_antisymm (negativeRank_le_sum_nullity E _ b rfl)
    (sum_nullity_le_negativeRank _ b E fun _ ha => (mem_resonantBelow.mp ha).1)

/-- The index at `b` vanishes iff no smaller aperture carries a null mode. -/
theorem negativeRank_eq_zero_iff_forall_weilNullity (b : SuzukiPositiveAperture) (E : ℝ) :
    negativeRank b E = 0 ↔ ∀ a : SuzukiPositiveAperture, a.1 < b.1 → weilNullity a E = 0 := by
  constructor
  · intro h a hab
    have := negativeRank_add_nullity_le_of_aperture_lt hab E
    omega
  · intro h
    rw [negativeRank_eq_sum_nullity]
    exact Finset.sum_eq_zero fun a ha => h a (mem_resonantBelow.mp ha).1

/-- **The Riemann hypothesis holds iff the aperture path has no conjugate point**: no aperture
carries a null mode of Weil's form at the energy zero. -/
theorem riemannHypothesis_iff_forall_weilNullity_zero :
    RiemannHypothesis ↔ ∀ a : SuzukiPositiveAperture, weilNullity a 0 = 0 := by
  rw [SquareRootThreshold.riemannHypothesis_iff_forall_ccmRestrictedWeilGroundEnergy_nonneg]
  constructor
  · intro h a
    have hb : negativeRank (⟨a.1 + 1, by linarith [a.2]⟩ : SuzukiPositiveAperture) 0 = 0 :=
      (negativeRank_eq_zero_iff_ground _ 0).mpr (h _)
    exact (negativeRank_eq_zero_iff_forall_weilNullity _ 0).mp hb a
      (show a.1 < a.1 + 1 by linarith)
  · intro h A
    exact (negativeRank_eq_zero_iff_ground A 0).mp
      ((negativeRank_eq_zero_iff_forall_weilNullity A 0).mpr fun a _ => h a)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
