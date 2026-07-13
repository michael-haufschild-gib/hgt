import Mathlib

/-!
# Infinite boundary under a positive translation in a bounded strip

An infinite subset of the open vertical strip `0 < re z < 1` has infinitely many points whose
predecessor under any fixed positive real translation leaves the set.  The proof follows each
point leftward only a uniformly bounded number of steps.  If the boundary were finite, the whole
set would be the image of a finite boundary-times-step carrier.
-/

open Complex Set

namespace RHTower

def leftShiftBoundary (S : Set ℂ) (h : ℝ) : Set ℂ :=
  {z : ℂ | z ∈ S ∧ z - (h : ℂ) ∉ S}

theorem infinite_leftShiftBoundary_of_infinite_in_openUnitStrip
    {S : Set ℂ} (hS : S.Infinite)
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z.re < 1)
    {h : ℝ} (hh : 0 < h) :
    (leftShiftBoundary S h).Infinite := by
  have hreach : ∀ N : ℕ, ∀ z : ℂ, z ∈ S →
      z.re < ((N + 1 : ℕ) : ℝ) * h →
      ∃ n : ℕ, n ≤ N ∧ z - (((n : ℝ) * h : ℝ) : ℂ) ∈ leftShiftBoundary S h := by
    intro N
    induction N with
    | zero =>
        intro z hz hzbound
        refine ⟨0, by simp, ?_⟩
        have hzBoundary : z ∈ leftShiftBoundary S h := by
          rw [leftShiftBoundary]
          constructor
          · simpa using hz
          · intro hprev
            have hpos := (hstrip (z - (h : ℂ)) hprev).1
            simp only [sub_re, ofReal_re] at hpos
            norm_num at hzbound
            linarith
        simpa using hzBoundary
    | succ N ih =>
        intro z hz hzbound
        by_cases hprev : z - (h : ℂ) ∈ S
        · have hprevBound : (z - (h : ℂ)).re < ((N + 1 : ℕ) : ℝ) * h := by
            simp only [sub_re, ofReal_re]
            calc
              z.re - h < (N : ℝ) * h + h := by
                push_cast at hzbound
                ring_nf at hzbound
                linarith
              _ = ((N + 1 : ℕ) : ℝ) * h := by
                push_cast
                ring
          obtain ⟨n, hn, hnboundary⟩ := ih (z - (h : ℂ)) hprev hprevBound
          refine ⟨n + 1, Nat.succ_le_succ hn, ?_⟩
          convert hnboundary using 1
          push_cast
          ring
        · refine ⟨0, by simp, ?_⟩
          rw [leftShiftBoundary]
          simpa using ⟨hz, hprev⟩
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / h)
  have hNh : 1 < (N : ℝ) * h := (div_lt_iff₀ hh).mp hN
  by_contra hboundary
  have hBfinite : (leftShiftBoundary S h).Finite := Set.not_infinite.mp hboundary
  letI : Fintype (leftShiftBoundary S h) := hBfinite.fintype
  let carrier : (leftShiftBoundary S h) × Fin N → ℂ := fun p =>
    (p.1 : ℂ) + ((p.2 : ℝ) * h : ℝ)
  have hrange : (Set.range carrier).Finite := Set.finite_range carrier
  have hsubset : S ⊆ Set.range carrier := by
    intro z hz
    have hzlt : z.re < (N : ℝ) * h := lt_trans (hstrip z hz).2 hNh
    have hNpos : 0 < N := by
      by_contra hNzero
      have : N = 0 := Nat.eq_zero_of_not_pos hNzero
      simp [this] at hNh
      linarith
    obtain ⟨n, hn, hnBoundary⟩ := hreach (N - 1) z hz (by
      have hNsub : N - 1 + 1 = N := by omega
      simpa [hNsub] using hzlt)
    have hnN : n < N := by omega
    let bn : leftShiftBoundary S h :=
      ⟨z - (((n : ℝ) * h : ℝ) : ℂ), hnBoundary⟩
    let fn : Fin N := ⟨n, hnN⟩
    refine ⟨(bn, fn), ?_⟩
    dsimp [carrier, bn, fn]
    push_cast
    ring
  apply hS
  exact hrange.subset hsubset

end RHTower
