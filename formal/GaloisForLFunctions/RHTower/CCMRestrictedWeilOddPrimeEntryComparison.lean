import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolePrimeEntry
import GaloisForLFunctions.RHTower.CCMRestrictedWeilOddPrimeChamberComparison

/-!
# Odd Weil positivity up to the next integer boundary

The exact zero-energy handoff extends the frozen-chamber minimum principle to
its next cutoff boundary. Nonnegative actual endpoint energies are equivalent
to nonnegativity throughout that closed interval and force strict positivity
at every interior radius, provided the left radius is at least two.
-/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RHTower

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

private theorem floor_eq_before_next (a b : SuzukiPositiveAperture)
    (hab : a.1 ≤ b.1)
    (hb : Real.exp (2*b.1) < (⌊Real.exp (2*a.1)⌋₊:ℝ)+1) :
    ⌊Real.exp (2*b.1)⌋₊ = ⌊Real.exp (2*a.1)⌋₊ := by
  apply (Nat.floor_eq_iff (Real.exp_pos _).le).mpr
  exact ⟨(Nat.floor_le (Real.exp_pos _).le).trans
    (Real.exp_le_exp.mpr (by linarith)),hb⟩

/-- The complete actual odd energy equals the incoming chamber expression all the
way to the next integer boundary, including that boundary itself. -/
theorem ccmWeilOddPole_eq_chamber_until_next_entry (a b : SuzukiPositiveAperture)
    (hab : a.1 ≤ b.1)
    (hb : Real.exp (2*b.1) ≤ (⌊Real.exp (2*a.1)⌋₊:ℝ)+1) :
    ccmRestrictedWeilSourceQuadratic b (ccmPolarParityFormVector b (-1)) =
      ccmWeilOddPoleChamber a b.1 := by
  rcases hb.lt_or_eq with h | h
  · exact ccmWeilOddPole_eq_chamber_of_floor_eq a b (floor_eq_before_next a b hab h)
  · apply ccmWeilOddPole_eq_chamber_at_next_entry a b
    simpa only [Nat.cast_add,Nat.cast_one] using h

private theorem chamber_continuous (a b : SuzukiPositiveAperture) :
    ContinuousOn (ccmWeilOddPoleChamber a) (Icc a.1 b.1) := by
  intro s hs
  exact (differentiableAt_ccmWeilOddPoleChamber a (by linarith [a.2,hs.1])).continuousAt.continuousWithinAt

private theorem chamber_force_until_next (a b : SuzukiPositiveAperture) (ha : 2 ≤ a.1)
    (hb : Real.exp (2*b.1) ≤ (⌊Real.exp (2*a.1)⌋₊:ℝ)+1) :
    ∀ s ∈ Ioo a.1 b.1,
      deriv (deriv (ccmWeilOddPoleChamber a)) s-ccmWeilOddPoleChamber a s < 0 := by
  intro s hs
  let c : SuzukiPositiveAperture := ⟨s,by linarith [a.2,hs.1]⟩
  apply ccmWeilOddPoleChamber_shifted_second_neg a c
  · apply floor_eq_before_next a c hs.1.le
    exact (Real.exp_lt_exp.mpr (show 2*s < 2*b.1 by linarith [hs.2])).trans_le hb
  · dsimp [c]
    linarith [hs.1]

/-- Above radius two, nonnegative endpoint energies force strict odd positivity
throughout the open interval reaching the next integer entry. -/
theorem ccmWeilOddPole_pos_before_next_entry (a b c : SuzukiPositiveAperture)
    (ha : 2 ≤ a.1) (hb : Real.exp (2*b.1) ≤ (⌊Real.exp (2*a.1)⌋₊:ℝ)+1)
    (hc : c.1 ∈ Ioo a.1 b.1)
    (hQa : 0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)))
    (hQb : 0 ≤ ccmRestrictedWeilSourceQuadratic b (ccmPolarParityFormVector b (-1))) :
    0 < ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c (-1)) := by
  rw [ccmWeilOddPole_eq_chamber_of_floor_eq a a rfl] at hQa
  rw [ccmWeilOddPole_eq_chamber_until_next_entry a b (le_trans hc.1.le hc.2.le) hb] at hQb
  rw [ccmWeilOddPole_eq_chamber_until_next_entry a c hc.1.le
    ((Real.exp_le_exp.mpr (show 2*c.1 ≤ 2*b.1 by linarith [hc.2])).trans hb)]
  exact interval_pos_of_shifted_second_neg (chamber_continuous a b)
    (chamber_force_until_next a b ha hb) hQa hQb c.1 hc

/-- Nonnegativity on a whole closed chamber, including its next cutoff boundary,
is exactly the pair of actual endpoint inequalities. -/
theorem ccmWeilOddPole_nonneg_until_next_entry_iff_endpoints (a b : SuzukiPositiveAperture)
    (ha : 2 ≤ a.1) (hab : a.1 ≤ b.1)
    (hb : Real.exp (2*b.1) ≤ (⌊Real.exp (2*a.1)⌋₊:ℝ)+1) :
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
    exact (ccmWeilOddPole_pos_before_next_entry a b c ha hb ⟨he,he'⟩ hQa hQb).le

end RHTower
