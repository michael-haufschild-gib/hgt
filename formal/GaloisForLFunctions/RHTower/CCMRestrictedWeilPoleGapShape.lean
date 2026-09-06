import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleParityCurvature

/-!
# Opposite gap shapes and the unique actual even minimum

Both actual matrix entries agree with their frozen expressions on a closed
prime-power gap. Beyond the explicit curvature threshold the odd profile is
strictly concave and the even profile strictly convex. The even energy has a
unique actual minimum, stationary when interior, whose sign decides the gap.
-/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RHTower

/-- Both actual matrix entries equal the incoming expressions on a whole closed prime-power gap. -/
theorem ccmWeilPoleMatrix_eq_chamber_on_primePower_gap (a b c : SuzukiPositiveAperture)
    (hc : c.1 ∈ Icc a.1 b.1)
    (hfree : ∀ n : ℕ, 2 ≤ n → a.1 < Real.log n/2 → Real.log n/2 < b.1 → ¬IsPrimePow n) :
    ccmWeilPoleDiagonal c = ccmWeilPoleChamberDiagonal a c.1 ∧
      ccmWeilPoleCross c = ccmWeilPoleChamberCross a c.1 := by
  have hA : ccmWeilPoleDiagonal c = ccmWeilPoleChamberDiagonal a c.1 := by
    rw [ccmWeilPoleDiagonal_eq_chamber_of_floor_eq c c rfl,
      ccmWeilPoleChamberDiagonal_eq_sum_atoms,ccmWeilPoleChamberDiagonal_eq_sum_atoms]
    have hsub : Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊ ⊆ Finset.Icc 2 ⌊Real.exp (2*c.1)⌋₊ :=
      Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith [hc.1])))
    rw [Finset.sum_subset hsub (fun n hn hnot => ?_)]
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hnc := (Finset.mem_Icc.mp hn).2
    have hna : ⌊Real.exp (2*a.1)⌋₊ < n := by
      simp only [Finset.mem_Icc] at hnot
      omega
    have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hl : a.1 < Real.log n/2 := by
      have h := (Real.lt_log_iff_exp_lt hnpos).mpr (Nat.lt_of_floor_lt hna)
      linarith
    have hr : Real.log n/2 ≤ c.1 := by
      have h := (Real.log_le_iff_le_exp hnpos).mpr
        ((show (n:ℝ) ≤ (⌊Real.exp (2*c.1)⌋₊:ℝ) by exact_mod_cast hnc).trans (Nat.floor_le (Real.exp_pos _).le))
      linarith
    rcases (hr.trans hc.2).lt_or_eq with hlt | heq
    · exact (ccmWeilPolePrimeAtoms_zero_of_not_primePow (hfree n hn2 hl hlt) c.1).1
    · have hv : (ccmWeilIntegerEntry n hn2).1 = c.1 := by
        change Real.log n/2 = c.1
        linarith [hc.2]
      rw [← hv]
      exact (ccmWeilPolePrimeAtoms_zero_at_entry n hn2).1
  refine ⟨hA,?_⟩
  have hodd := ccmWeilOddPole_eq_chamber_on_primePower_gap a b c hc hfree
  rw [ccmWeilPoleCompression_parity_energy c (Or.inr rfl),hA] at hodd
  unfold ccmWeilOddPoleChamber at hodd
  linarith

/-- The complete actual even source agrees with its chamber expression throughout the closed gap. -/
theorem ccmWeilEvenPole_eq_chamber_on_primePower_gap (a b c : SuzukiPositiveAperture)
    (hc : c.1 ∈ Icc a.1 b.1)
    (hfree : ∀ n : ℕ, 2 ≤ n → a.1 < Real.log n/2 → Real.log n/2 < b.1 → ¬IsPrimePow n) :
    ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c 1) = ccmWeilEvenPoleChamber a c.1 := by
  obtain ⟨hA,hC⟩ := ccmWeilPoleMatrix_eq_chamber_on_primePower_gap a b c hc hfree
  rw [ccmWeilPoleCompression_parity_energy c (Or.inl rfl),hA,hC]
  unfold ccmWeilEvenPoleChamber
  ring

/-- Beyond the explicit threshold, the actual odd/even gap profiles are strictly
concave/convex, respectively, including both gap endpoints. -/
theorem ccmWeilPole_primePower_gap_strict_shape (a b : SuzukiPositiveAperture)
    (ha : ccmWeilPoleCurvatureThreshold ≤ a.1)
    (hfree : ∀ n : ℕ, 2 ≤ n → a.1 < Real.log n/2 → Real.log n/2 < b.1 → ¬IsPrimePow n) :
    StrictConcaveOn ℝ (Icc a.1 b.1) (ccmWeilOddPoleChamber a) ∧
      StrictConvexOn ℝ (Icc a.1 b.1) (ccmWeilEvenPoleChamber a) := by
  have hsign (s : ℝ) (hs : s ∈ Ioo a.1 b.1) :
      deriv (deriv (ccmWeilOddPoleChamber a)) s < 0 ∧
      0 < deriv (deriv (ccmWeilEvenPoleChamber a)) s := by
    let c : SuzukiPositiveAperture := ⟨s,by linarith [a.2,hs.1]⟩
    obtain ⟨hA,hC⟩ := ccmWeilPoleChambers_eq_on_primePower_gap a b c ⟨hs.1.le,hs.2⟩ hfree
    have hodd : ccmWeilOddPoleChamber a = ccmWeilOddPoleChamber c := by
      funext t
      unfold ccmWeilOddPoleChamber
      rw [hA,hC]
    have heven : ccmWeilEvenPoleChamber a = ccmWeilEvenPoleChamber c := by
      funext t
      unfold ccmWeilEvenPoleChamber
      rw [hA,hC]
    rw [hodd,heven]
    exact ⟨ccmWeilOddPoleChamber_second_neg c c rfl (ha.trans hs.1.le),
      ccmWeilEvenPoleChamber_second_pos c c rfl (ha.trans hs.1.le)⟩
  constructor
  · apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
    · intro s hs
      exact (differentiableAt_ccmWeilOddPoleChamber a (by linarith [a.2,hs.1])).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hsign s hs).1
  · apply strictConvexOn_of_deriv2_pos (convex_Icc _ _)
    · intro s hs
      exact (differentiableAt_ccmWeilEvenPoleChamber a (by linarith [a.2,hs.1])).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hsign s hs).2

/-- Each closed prime-power gap above the threshold has one uniquely determined
actual even-energy minimizer. This supplies the point to check, not its sign. -/
theorem exists_unique_ccmWeilEvenPole_gap_minimum (a b : SuzukiPositiveAperture)
    (ha : ccmWeilPoleCurvatureThreshold ≤ a.1) (hab : a.1 ≤ b.1)
    (hfree : ∀ n : ℕ, 2 ≤ n → a.1 < Real.log n/2 → Real.log n/2 < b.1 → ¬IsPrimePow n) :
    ∃! c : SuzukiPositiveAperture, c.1 ∈ Icc a.1 b.1 ∧
      ∀ d : SuzukiPositiveAperture, d.1 ∈ Icc a.1 b.1 →
        ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c 1) ≤
          ccmRestrictedWeilSourceQuadratic d (ccmPolarParityFormVector d 1) := by
  have hcont : ContinuousOn (ccmWeilEvenPoleChamber a) (Icc a.1 b.1) := by
    intro s hs
    exact (differentiableAt_ccmWeilEvenPoleChamber a (by linarith [a.2,hs.1])).continuousAt.continuousWithinAt
  obtain ⟨s,hs,hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a.1,le_rfl,hab⟩ hcont
  let c : SuzukiPositiveAperture := ⟨s,by linarith [a.2,hs.1]⟩
  refine ⟨c,⟨hs,?_⟩,?_⟩
  · intro d hd
    rw [ccmWeilEvenPole_eq_chamber_on_primePower_gap a b c hs hfree,
      ccmWeilEvenPole_eq_chamber_on_primePower_gap a b d hd hfree]
    exact hmin hd
  · intro d hd
    have hmind : IsMinOn (ccmWeilEvenPoleChamber a) (Icc a.1 b.1) d.1 := by
      intro t ht
      let e : SuzukiPositiveAperture := ⟨t,by linarith [a.2,ht.1]⟩
      have h := hd.2 e ht
      rw [ccmWeilEvenPole_eq_chamber_on_primePower_gap a b d hd.1 hfree,
        ccmWeilEvenPole_eq_chamber_on_primePower_gap a b e ht hfree] at h
      exact h
    apply Subtype.ext
    exact (ccmWeilPole_primePower_gap_strict_shape a b ha hfree).2.eq_of_isMinOn hmind hmin hd.1 hs

/-- Testing an actual even minimum is exactly testing nonnegativity on the whole gap. -/
theorem ccmWeilEvenPole_gap_nonneg_iff_minimum (a b c : SuzukiPositiveAperture)
    (hc : c.1 ∈ Icc a.1 b.1)
    (hmin : ∀ d : SuzukiPositiveAperture, d.1 ∈ Icc a.1 b.1 →
      ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c 1) ≤
        ccmRestrictedWeilSourceQuadratic d (ccmPolarParityFormVector d 1)) :
    (∀ d : SuzukiPositiveAperture, d.1 ∈ Icc a.1 b.1 →
      0 ≤ ccmRestrictedWeilSourceQuadratic d (ccmPolarParityFormVector d 1)) ↔
      0 ≤ ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c 1) := by
  exact ⟨fun h => h c hc,fun h d hd => h.trans (hmin d hd)⟩

/-- An interior actual even-gap minimizer is a stationary point of the exact
incoming chamber expression. Boundary minimizers are excluded by the open-interval condition. -/
theorem ccmWeilEvenPole_gap_minimum_stationary (a b c : SuzukiPositiveAperture)
    (hc : c.1 ∈ Ioo a.1 b.1)
    (hfree : ∀ n : ℕ, 2 ≤ n → a.1 < Real.log n/2 → Real.log n/2 < b.1 → ¬IsPrimePow n)
    (hmin : ∀ d : SuzukiPositiveAperture, d.1 ∈ Icc a.1 b.1 →
      ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c 1) ≤
        ccmRestrictedWeilSourceQuadratic d (ccmPolarParityFormVector d 1)) :
    deriv (ccmWeilEvenPoleChamber a) c.1 = 0 := by
  have hm : IsMinOn (ccmWeilEvenPoleChamber a) (Icc a.1 b.1) c.1 := by
    intro s hs
    let d : SuzukiPositiveAperture := ⟨s,by linarith [a.2,hs.1]⟩
    have h := hmin d hs
    rw [ccmWeilEvenPole_eq_chamber_on_primePower_gap a b c ⟨hc.1.le,hc.2.le⟩ hfree,
      ccmWeilEvenPole_eq_chamber_on_primePower_gap a b d hs hfree] at h
    exact h
  exact (hm.isLocalMin (Icc_mem_nhds hc.1 hc.2)).deriv_eq_zero

end RHTower
