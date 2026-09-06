import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleCutoffAtoms

/-!
# Full odd-source comparison across a prime-power gap

All frozen matrix functions remain identical while only zero-Mangoldt integers
enter. At the right boundary, a newly entering prime power has zero energy.
The shifted differential inequality therefore controls the whole closed gap
through its actual endpoint values, with strict positivity in the interior.
-/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RHTower

private theorem new_entry_bounds (a c : SuzukiPositiveAperture) {n : ℕ}
    (hn : n ∈ Finset.Icc 2 ⌊Real.exp (2*c.1)⌋₊)
    (hnot : n ∉ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊) :
    a.1 < Real.log n/2 ∧ Real.log n/2 ≤ c.1 := by
  have hn2 := (Finset.mem_Icc.mp hn).1
  have hnc := (Finset.mem_Icc.mp hn).2
  have hna : ⌊Real.exp (2*a.1)⌋₊ < n := by
    simp only [Finset.mem_Icc] at hnot
    omega
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hl := (Real.lt_log_iff_exp_lt hnpos).mpr (Nat.lt_of_floor_lt hna)
  have hr := (Real.log_le_iff_le_exp hnpos).mpr
    ((show (n:ℝ) ≤ (⌊Real.exp (2*c.1)⌋₊:ℝ) by exact_mod_cast hnc).trans
      (Nat.floor_le (Real.exp_pos _).le))
  constructor <;> linarith

private theorem cutoff_subset (a c : SuzukiPositiveAperture) (hac : a.1 ≤ c.1) :
    Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊ ⊆ Finset.Icc 2 ⌊Real.exp (2*c.1)⌋₊ :=
  Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith)))

/-- With no prime-power entry before the current radius, both frozen matrix
functions remain identical even when zero-weight integer cutoffs are crossed. -/
theorem ccmWeilPoleChambers_eq_on_primePower_gap (a b c : SuzukiPositiveAperture)
    (hc : c.1 ∈ Ico a.1 b.1)
    (hfree : ∀ n : ℕ, 2 ≤ n → a.1 < Real.log n/2 → Real.log n/2 < b.1 → ¬IsPrimePow n) :
    ccmWeilPoleChamberDiagonal a = ccmWeilPoleChamberDiagonal c ∧
      ccmWeilPoleChamberCross a = ccmWeilPoleChamberCross c := by
  have hz (n : ℕ) (hn : n ∈ Finset.Icc 2 ⌊Real.exp (2*c.1)⌋₊)
      (hnot : n ∉ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊) (s : ℝ) :
      ccmWeilPolePrimeDiagonalAtom n s = 0 ∧ ccmWeilPolePrimeCrossAtom n s = 0 := by
    obtain ⟨hl,hr⟩ := new_entry_bounds a c hn hnot
    exact ccmWeilPolePrimeAtoms_zero_of_not_primePow
      (hfree n (Finset.mem_Icc.mp hn).1 hl (hr.trans_lt hc.2)) s
  constructor
  · funext s
    rw [ccmWeilPoleChamberDiagonal_eq_sum_atoms,ccmWeilPoleChamberDiagonal_eq_sum_atoms]
    rw [Finset.sum_subset (cutoff_subset a c hc.1) (fun n hn hnot => (hz n hn hnot s).1)]
  · funext s
    rw [ccmWeilPoleChamberCross_eq_sum_atoms,ccmWeilPoleChamberCross_eq_sum_atoms]
    rw [Finset.sum_subset (cutoff_subset a c hc.1) (fun n hn hnot => (hz n hn hnot s).2)]

/-- The full moving odd source equals one frozen expression throughout a closed
prime-power gap; a prime power at the right endpoint contributes zero there. -/
theorem ccmWeilOddPole_eq_chamber_on_primePower_gap (a b c : SuzukiPositiveAperture)
    (hc : c.1 ∈ Icc a.1 b.1)
    (hfree : ∀ n : ℕ, 2 ≤ n → a.1 < Real.log n/2 → Real.log n/2 < b.1 → ¬IsPrimePow n) :
    ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c (-1)) =
      ccmWeilOddPoleChamber a c.1 := by
  have hz (n : ℕ) (hn : n ∈ Finset.Icc 2 ⌊Real.exp (2*c.1)⌋₊)
      (hnot : n ∉ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊) :
      ccmWeilPolePrimeDiagonalAtom n c.1 = 0 ∧ ccmWeilPolePrimeCrossAtom n c.1 = 0 := by
    obtain ⟨hl,hr⟩ := new_entry_bounds a c hn hnot
    rcases (hr.trans hc.2).lt_or_eq with hlt | heq
    · exact ccmWeilPolePrimeAtoms_zero_of_not_primePow
        (hfree n (Finset.mem_Icc.mp hn).1 hl hlt) c.1
    · have hnc : Real.log n/2 = c.1 := le_antisymm hr (by linarith [hc.2])
      have hv : (ccmWeilIntegerEntry n (Finset.mem_Icc.mp hn).1).1 = c.1 := hnc
      rw [← hv]
      exact ccmWeilPolePrimeAtoms_zero_at_entry n (Finset.mem_Icc.mp hn).1
  rw [ccmWeilOddPole_eq_chamber_of_floor_eq c c rfl]
  unfold ccmWeilOddPoleChamber
  rw [ccmWeilPoleChamberDiagonal_eq_sum_atoms,ccmWeilPoleChamberDiagonal_eq_sum_atoms,
    ccmWeilPoleChamberCross_eq_sum_atoms,ccmWeilPoleChamberCross_eq_sum_atoms]
  rw [Finset.sum_subset (cutoff_subset a c hc.1) (fun n hn hnot => (hz n hn hnot).1),
    Finset.sum_subset (cutoff_subset a c hc.1) (fun n hn hnot => (hz n hn hnot).2)]

private theorem second_nonneg_of_localMin {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMin f x) (hc : ContinuousAt f x) : 0 ≤ deriv (deriv f) x := by
  by_contra hn
  have hneg : deriv (deriv f) x < 0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hm.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hm,hmax] with y hymin hymax
    exact le_antisymm hymax hymin
  have hzero := heq.deriv.deriv_eq
  simp only [deriv_const'] at hzero
  linarith

private theorem interval_nonneg_of_shifted_second_neg {f : ℝ → ℝ} {l r : ℝ}
    (hc : ContinuousOn f (Icc l r))
    (hd : ∀ x∈Ioo l r, deriv (deriv f) x-f x < 0)
    (hl : 0 ≤ f l) (hr : 0 ≤ f r) : ∀ x∈Icc l r, 0 ≤ f x := by
  intro x hx
  by_contra hn
  have hxneg : f x < 0 := lt_of_not_ge hn
  obtain ⟨m,hm,hmin⟩ := isCompact_Icc.exists_isMinOn ⟨x,hx⟩ hc
  have hmneg : f m < 0 := (hmin hx).trans_lt hxneg
  have hlm : l < m := by
    by_contra h
    have he : m=l := le_antisymm (le_of_not_gt h) hm.1
    rw [he] at hmneg
    linarith
  have hmr : m < r := by
    by_contra h
    have he : m=r := le_antisymm hm.2 (le_of_not_gt h)
    rw [he] at hmneg
    linarith
  have hnhds := Icc_mem_nhds hlm hmr
  have hs := second_nonneg_of_localMin (hmin.isLocalMin hnhds) (hc.continuousAt hnhds)
  have hforce := hd m ⟨hlm,hmr⟩
  linarith

private theorem interval_pos_of_shifted_second_neg {f : ℝ → ℝ} {l r : ℝ}
    (hc : ContinuousOn f (Icc l r))
    (hd : ∀ x∈Ioo l r, deriv (deriv f) x-f x < 0)
    (hl : 0 ≤ f l) (hr : 0 ≤ f r) : ∀ x∈Ioo l r, 0 < f x := by
  intro x hx
  have hn := interval_nonneg_of_shifted_second_neg hc hd hl hr
  by_contra h
  have he : f x=0 := le_antisymm (le_of_not_gt h) (hn x ⟨hx.1.le,hx.2.le⟩)
  have hm : IsMinOn f (Icc l r) x := by
    intro y hy
    rw [he]
    exact hn y hy
  have hnhds := Icc_mem_nhds hx.1 hx.2
  have hs := second_nonneg_of_localMin (hm.isLocalMin hnhds) (hc.continuousAt hnhds)
  have hforce := hd x hx
  rw [he] at hforce
  linarith

private theorem gap_chamber_force (a b : SuzukiPositiveAperture) (ha : 2 ≤ a.1)
    (hfree : ∀ n : ℕ, 2 ≤ n → a.1 < Real.log n/2 → Real.log n/2 < b.1 → ¬IsPrimePow n) :
    ∀ s ∈ Ioo a.1 b.1, deriv (deriv (ccmWeilOddPoleChamber a)) s-
      ccmWeilOddPoleChamber a s < 0 := by
  intro s hs
  let c : SuzukiPositiveAperture := ⟨s,by linarith [a.2,hs.1]⟩
  obtain ⟨hA,hC⟩ := ccmWeilPoleChambers_eq_on_primePower_gap a b c ⟨hs.1.le,hs.2⟩ hfree
  have hE : ccmWeilOddPoleChamber a = ccmWeilOddPoleChamber c := by
    funext t
    unfold ccmWeilOddPoleChamber
    rw [hA,hC]
  rw [hE]
  exact ccmWeilOddPoleChamber_shifted_second_neg c c rfl (by dsimp [c]; linarith [hs.1])

/-- Nonnegative actual endpoint energies force strict interior odd positivity
across a whole interval with no prime-power entry inside, above radius two. -/
theorem ccmWeilOddPole_pos_between_primePower_entries (a b c : SuzukiPositiveAperture)
    (ha : 2 ≤ a.1) (hc : c.1 ∈ Ioo a.1 b.1)
    (hfree : ∀ n : ℕ, 2 ≤ n → a.1 < Real.log n/2 → Real.log n/2 < b.1 → ¬IsPrimePow n)
    (hQa : 0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)))
    (hQb : 0 ≤ ccmRestrictedWeilSourceQuadratic b (ccmPolarParityFormVector b (-1))) :
    0 < ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c (-1)) := by
  have hab : a.1 ≤ b.1 := hc.1.le.trans hc.2.le
  have hcont : ContinuousOn (ccmWeilOddPoleChamber a) (Icc a.1 b.1) := by
    intro s hs
    exact (differentiableAt_ccmWeilOddPoleChamber a (by linarith [a.2,hs.1])).continuousAt.continuousWithinAt
  rw [ccmWeilOddPole_eq_chamber_on_primePower_gap a b a ⟨le_rfl,hab⟩ hfree] at hQa
  rw [ccmWeilOddPole_eq_chamber_on_primePower_gap a b b ⟨hab,le_rfl⟩ hfree] at hQb
  rw [ccmWeilOddPole_eq_chamber_on_primePower_gap a b c ⟨hc.1.le,hc.2.le⟩ hfree]
  exact interval_pos_of_shifted_second_neg hcont (gap_chamber_force a b ha hfree) hQa hQb c.1 hc

/-- Exact endpoint criterion across a prime-power gap, including its two boundaries. -/
theorem ccmWeilOddPole_nonneg_primePower_gap_iff_endpoints (a b : SuzukiPositiveAperture)
    (ha : 2 ≤ a.1) (hab : a.1 ≤ b.1)
    (hfree : ∀ n : ℕ, 2 ≤ n → a.1 < Real.log n/2 → Real.log n/2 < b.1 → ¬IsPrimePow n) :
    (∀ c : SuzukiPositiveAperture, c.1 ∈ Icc a.1 b.1 →
      0 ≤ ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c (-1))) ↔
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) ∧
      0 ≤ ccmRestrictedWeilSourceQuadratic b (ccmPolarParityFormVector b (-1)) := by
  constructor
  · intro h
    exact ⟨h a ⟨le_rfl,hab⟩,h b ⟨hab,le_rfl⟩⟩
  · rintro ⟨hQa,hQb⟩ c hc
    rcases hc.1.eq_or_lt with he | he
    · have hca : c = a := Subtype.ext he.symm
      subst c
      exact hQa
    rcases hc.2.eq_or_lt with he' | he'
    · have hcb : c = b := Subtype.ext he'
      subst c
      exact hQb
    exact (ccmWeilOddPole_pos_between_primePower_entries a b c ha ⟨he,he'⟩ hfree hQa hQb).le

end RHTower
