import GaloisForLFunctions.BiScaleUncertainty.FiniteGridTraceStability
import GaloisForLFunctions.BiScaleUncertainty.CoprimeProjectionNeighbors

/-!
# Two-spacing recovery from the longest-run invariant

The arithmetic run length is one for a shared divisor, two for coprime spacings
at least three, and three when one coprime spacing is two. Hence the general
finite-family sine factors recover the previously sharp two-grid constants.
-/

noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

theorem finiteGridActive_pair (d e k : ℕ) :
    finiteGridActive d {e} k ↔ d + 2 ∣ k + 1 ∨ e + 2 ∣ k + 1 := by
  simp [finiteGridActive]

theorem finiteGridRunLength_pair_comm (d e : ℕ) :
    finiteGridRunLength d {e} = finiteGridRunLength e {d} := by
  apply le_antisymm
  · obtain ⟨k, hk⟩ := finiteGridRunLength_attained d {e}
    apply finiteGrid_run_le e {d} (k := k)
    intro i hi
    simpa only [finiteGridActive_pair, or_comm] using hk i hi
  · obtain ⟨k, hk⟩ := finiteGridRunLength_attained e {d}
    apply finiteGrid_run_le d {e} (k := k)
    intro i hi
    simpa only [finiteGridActive_pair, or_comm] using hk i hi

private theorem not_divides_near (d k i j : ℕ) (hij : i < j) (hgap : j-i < d+2) :
    ¬ (d+2 ∣ k+i+1 ∧ d+2 ∣ k+j+1) := by
  rintro ⟨hi, hj⟩
  have hd : d+2 ∣ j-i := (Nat.dvd_add_iff_right hi).mpr
    (by simpa only [show k+i+1+(j-i) = k+j+1 by omega] using hj)
  have := Nat.le_of_dvd (by omega : 0 < j-i) hd
  omega

theorem finiteGridRunLength_pair_of_gcd (d e : ℕ) (hg : 2 ≤ Nat.gcd (d+2) (e+2)) :
    finiteGridRunLength d {e} = 1 := by
  have hupper : finiteGridRunLength d {e} ≤ 1 := by
    apply finiteGridRunLength_le_of_gap
    intro k
    by_cases hk : finiteGridActive d {e} k
    · refine ⟨1, le_rfl, ?_⟩
      intro hk1
      have hdiv (j : ℕ) (hj : finiteGridActive d {e} j) : Nat.gcd (d+2) (e+2) ∣ j+1 := by
        rcases (finiteGridActive_pair d e j).mp hj with hd | he
        · exact (Nat.gcd_dvd_left _ _).trans hd
        · exact (Nat.gcd_dvd_right _ _).trans he
      exact not_adjacent_of_common_divisor hg (hdiv k hk) (hdiv (k+1) hk1) rfl
    · exact ⟨0, by omega, by simpa using hk⟩
  have := finiteGridRunLength_pos d {e}
  omega

theorem finiteGridRunLength_pair_ge_two (d e : ℕ) (h : Nat.Coprime (d+2) (e+2)) :
    2 ≤ finiteGridRunLength d {e} := by
  obtain ⟨i, j, hij⟩ := exists_adjacent_coprimeCenters d e h
  have hb := coprimeCenter_ge_two e j
  apply finiteGrid_run_le d {e} (k := coprimeCenter e j - 1)
  intro l hl
  rw [finiteGridActive_pair]
  have hl01 : l = 0 ∨ l = 1 := by omega
  rcases hl01 with hl0 | hl1
  · right
    simpa only [hl0, Nat.add_zero, Nat.sub_add_cancel (by omega : 1 ≤ coprimeCenter e j)]
      using coprimeCenter_dvd e j
  · left
    have he : coprimeCenter e j - 1 + l + 1 = coprimeCenter d i := by omega
    rw [he]
    exact coprimeCenter_dvd d i

theorem finiteGridRunLength_pair_le_two (d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e) :
    finiteGridRunLength d {e} ≤ 2 := by
  apply finiteGridRunLength_le_of_gap
  intro k
  by_contra h
  push Not at h
  have h0 := (finiteGridActive_pair d e (k+0)).mp (h 0 (by omega))
  have h1 := (finiteGridActive_pair d e (k+1)).mp (h 1 (by omega))
  have h2 := (finiteGridActive_pair d e (k+2)).mp (h 2 (by omega))
  have ha01 := not_divides_near d k 0 1 (by omega) (by omega)
  have ha02 := not_divides_near d k 0 2 (by omega) (by omega)
  have ha12 := not_divides_near d k 1 2 (by omega) (by omega)
  have hb01 := not_divides_near e k 0 1 (by omega) (by omega)
  have hb02 := not_divides_near e k 0 2 (by omega) (by omega)
  have hb12 := not_divides_near e k 1 2 (by omega) (by omega)
  rcases h0 with ha0 | hb0
  · have hb1 := h1.resolve_left (fun ha1 => ha01 ⟨ha0, ha1⟩)
    have ha2 := h2.resolve_right (fun hb2 => hb12 ⟨hb1, hb2⟩)
    exact ha02 ⟨ha0, ha2⟩
  · have ha1 := h1.resolve_right (fun hb1 => hb01 ⟨hb0, hb1⟩)
    have hb2 := h2.resolve_left (fun ha2 => ha12 ⟨ha1, ha2⟩)
    exact hb02 ⟨hb0, hb2⟩

theorem finiteGridRunLength_pair_of_large_coprime (d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e)
    (h : Nat.Coprime (d+2) (e+2)) : finiteGridRunLength d {e} = 2 :=
  le_antisymm (finiteGridRunLength_pair_le_two d e hd he) (finiteGridRunLength_pair_ge_two d e h)

private theorem zero_pair_run_le_three (e : ℕ) (he : 1 ≤ e) :
    finiteGridRunLength 0 {e} ≤ 3 := by
  apply finiteGridRunLength_le_of_gap
  intro k
  by_contra h
  push Not at h
  have h0 := (finiteGridActive_pair 0 e (k+0)).mp (h 0 (by omega))
  have h1 := (finiteGridActive_pair 0 e (k+1)).mp (h 1 (by omega))
  have h2 := (finiteGridActive_pair 0 e (k+2)).mp (h 2 (by omega))
  have h3 := (finiteGridActive_pair 0 e (k+3)).mp (h 3 (by omega))
  have ha01 := not_divides_near 0 k 0 1 (by omega) (by omega)
  have ha12 := not_divides_near 0 k 1 2 (by omega) (by omega)
  have ha23 := not_divides_near 0 k 2 3 (by omega) (by omega)
  have hb01 := not_divides_near e k 0 1 (by omega) (by omega)
  have hb02 := not_divides_near e k 0 2 (by omega) (by omega)
  have hb12 := not_divides_near e k 1 2 (by omega) (by omega)
  have hb13 := not_divides_near e k 1 3 (by omega) (by omega)
  rcases h0 with ha0 | hb0
  · have hb1 := h1.resolve_left (fun ha1 => ha01 ⟨ha0, ha1⟩)
    have ha2 := h2.resolve_right (fun hb2 => hb12 ⟨hb1, hb2⟩)
    have hb3 := h3.resolve_left (fun ha3 => ha23 ⟨ha2, ha3⟩)
    exact hb13 ⟨hb1, hb3⟩
  · have ha1 := h1.resolve_right (fun hb1 => hb01 ⟨hb0, hb1⟩)
    have hb2 := h2.resolve_left (fun ha2 => ha12 ⟨ha1, ha2⟩)
    exact hb02 ⟨hb0, hb2⟩

theorem finiteGridRunLength_zero_pair (e : ℕ) (h : Nat.Coprime 2 (e+2)) :
    finiteGridRunLength 0 {e} = 3 := by
  have he : 1 ≤ e := by
    by_contra hn
    have he0 : e = 0 := by omega
    norm_num [he0] at h
  have hn : ¬2 ∣ coprimeCenter e 0 := by
    intro hn
    have hdiv : 2 ∣ e+2 := by simpa [coprimeCenter] using hn
    have hh := Nat.dvd_gcd (dvd_refl 2) hdiv
    rw [h] at hh
    norm_num at hh
  obtain ⟨i, j, hij, hjk⟩ := exists_two_even_neighbors he hn
  have hi := coprimeCenter_ge_two 0 i
  apply le_antisymm (zero_pair_run_le_three e he)
  apply finiteGrid_run_le 0 {e} (k := coprimeCenter 0 i - 1)
  intro l hl
  rw [finiteGridActive_pair]
  have hl012 : l = 0 ∨ l = 1 ∨ l = 2 := by omega
  rcases hl012 with hl0 | hl1 | hl2
  · left
    have heq : coprimeCenter 0 i - 1 + l + 1 = coprimeCenter 0 i := by omega
    rw [heq]
    exact coprimeCenter_dvd 0 i
  · right
    have heq : coprimeCenter 0 i - 1 + l + 1 = coprimeCenter e 0 := by omega
    rw [heq]
    exact coprimeCenter_dvd e 0
  · left
    have heq : coprimeCenter 0 i - 1 + l + 1 = coprimeCenter 0 j := by omega
    rw [heq]
    exact coprimeCenter_dvd 0 j

/-- Complete unconditional two-spacing classification of the run invariant. -/
theorem finiteGridRunLength_pair (d e : ℕ) :
    finiteGridRunLength d {e} =
      if 2 ≤ Nat.gcd (d+2) (e+2) then 1 else if d = 0 ∨ e = 0 then 3 else 2 := by
  by_cases hg : 2 ≤ Nat.gcd (d+2) (e+2)
  · rw [if_pos hg]
    exact finiteGridRunLength_pair_of_gcd d e hg
  · rw [if_neg hg]
    have hp := Nat.gcd_pos_of_pos_left (e+2) (by omega : 0 < d+2)
    have hc : Nat.Coprime (d+2) (e+2) := by change Nat.gcd _ _ = 1; omega
    by_cases hz : d = 0 ∨ e = 0
    · rw [if_pos hz]
      rcases hz with hd | he
      · subst d
        exact finiteGridRunLength_zero_pair e hc
      · subst e
        rw [finiteGridRunLength_pair_comm]
        exact finiteGridRunLength_zero_pair d hc.symm
    · rw [if_neg hz]
      exact finiteGridRunLength_pair_of_large_coprime d e (by omega) (by omega) hc

theorem finiteGridSineFactor_pair (d e : ℕ) :
    finiteGridSineFactor d {e} =
      if 2 ≤ Nat.gcd (d+2) (e+2) then 0 else
        if d = 0 ∨ e = 0 then Real.sqrt 2 / 2 else 1 / 2 := by
  unfold finiteGridSineFactor
  rw [finiteGridRunLength_pair]
  split_ifs <;> norm_num [Real.cos_pi_div_two, Real.cos_pi_div_three, Real.cos_pi_div_four]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
