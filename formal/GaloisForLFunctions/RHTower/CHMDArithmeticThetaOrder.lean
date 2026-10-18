import GaloisForLFunctions.RHTower.CHMDArithmeticThetaIsolation

/-!
# Signed arithmetic cusp order and uniqueness from sparse observations

The first differing coefficient determines the eventual strict order of integer
samples of any two admissible signed arithmetic theta sources. Distinct sources cannot
agree on an unbounded set of integer samples. No sign constraint is imposed on
either coefficient sequence.
-/

open Filter Topology
open scoped BigOperators
noncomputable section

namespace RHTower.CHMDArithmeticTheta

/-- Once the earlier coefficients agree, the normalized source difference reads
the next coefficient difference. -/
theorem first_difference_limit (a b : Data) (m : ℕ)
    (hhead : ∀ n < m, a n = b n) :
    Tendsto (fun N : ℕ => (wave b N - wave a N) / atom m N) atTop
      (𝓝 (b m - a m)) := by
  have h := (recover_from_wave b m).sub (recover_from_wave a m)
  convert h using 1
  funext N
  have hh : (∑ n ∈ Finset.range m, b n * atom n N) =
      ∑ n ∈ Finset.range m, a n * atom n N := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hhead n (Finset.mem_range.mp hn)]
  rw [hh]
  ring

/-- Signed cancellations cannot change the eventual order selected by the first
differing arithmetic coefficient. -/
theorem eventually_wave_lt_of_first_difference {a b : Data} {m : ℕ}
    (hhead : ∀ n < m, a n = b n) (hlt : a m < b m) :
    ∀ᶠ N : ℕ in atTop, wave a N < wave b N := by
  have h := (first_difference_limit a b m hhead).eventually
    (eventually_gt_nhds (sub_pos.mpr hlt))
  filter_upwards [h] with N hN
  exact sub_pos.mp ((div_pos_iff_of_pos_right (atom_pos m N)).mp hN)

/-- Any two distinct signed coefficient sequences have an eventual strict source
order. This is a lexicographic order law, not coefficientwise domination. -/
theorem eq_or_eventually_wave_lt_or_gt (a b : Data) :
    a = b ∨ (∀ᶠ N : ℕ in atTop, wave a N < wave b N) ∨
      (∀ᶠ N : ℕ in atTop, wave b N < wave a N) := by
  classical
  by_cases hab : a = b
  · exact Or.inl hab
  have hex : ∃ m : ℕ, a m ≠ b m := by
    by_contra h
    push Not at h
    exact hab (lp.ext (funext h))
  let m := Nat.find hex
  have hne : a m ≠ b m := Nat.find_spec hex
  have hhead : ∀ n < m, a n = b n := by
    intro n hn
    exact not_ne_iff.mp (Nat.find_min hex hn)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inr (Or.inl (eventually_wave_lt_of_first_difference hhead hlt))
  · exact Or.inr (Or.inr
      (eventually_wave_lt_of_first_difference (fun n hn => (hhead n hn).symm) hgt))

/-- Infinitely late equality already determines all signed arithmetic data. -/
theorem eq_of_frequently_wave_eq {a b : Data}
    (hab : ∃ᶠ N : ℕ in atTop, wave a N = wave b N) : a = b := by
  rcases eq_or_eventually_wave_lt_or_gt a b with h | h | h
  · exact h
  · obtain ⟨N, hN, hlt⟩ := (hab.and_eventually h).exists
    exact False.elim (hlt.ne hN)
  · obtain ⟨N, hN, hgt⟩ := (hab.and_eventually h).exists
    exact False.elim (hgt.ne hN.symm)

/-- An arbitrary unbounded set of integer observations is a uniqueness set. -/
theorem eq_of_unbounded_wave_eq {a b : Data}
    (hab : ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ wave a N = wave b N) : a = b :=
  eq_of_frequently_wave_eq (frequently_atTop.mpr hab)

theorem wave_zero (x : ℝ) : wave 0 x = 0 := by
  simp [wave]

/-- A nonzero signed arithmetic source cannot keep changing sign along integer
cusp samples. -/
theorem eventually_wave_pos_or_neg {a : Data} (ha : a ≠ 0) :
    (∀ᶠ N : ℕ in atTop, 0 < wave a N) ∨
      (∀ᶠ N : ℕ in atTop, wave a N < 0) := by
  rcases eq_or_eventually_wave_lt_or_gt a 0 with h | h | h
  · exact False.elim (ha h)
  · exact Or.inr (by simpa only [wave_zero] using h)
  · exact Or.inl (by simpa only [wave_zero] using h)

end RHTower.CHMDArithmeticTheta
