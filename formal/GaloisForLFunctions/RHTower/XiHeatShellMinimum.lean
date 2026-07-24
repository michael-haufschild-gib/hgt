import GaloisForLFunctions.RHTower.XiResolventLowRungVacuity
import GaloisForLFunctions.RHTower.XiZerosInfinite

/-!
# The squared divisor has a bottom shell

The shell coordinate `Re (xiSpectralPoint q ^ 2) = g^2 - b^2` is positive and its sublevel sets are
finite, and the divisor is nonempty because the completed zeta has infinitely many zeros.  Hence
the shell coordinate attains its minimum: there is a copy no other copy lies below.

That minimum is the object the large-time analysis of the Turán minor is organised around — the
sign of `xiHeatTuranDefect t` for large `t` is decided by the copies of minimal shell coordinate
and by nothing else, since every other pair term is exponentially subordinate.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The multiplicity-exact divisor is nonempty: the completed zeta has zeros. -/
theorem nonempty_xiZeroCopy : Nonempty XiZeroCopy := by
  obtain ⟨ρ, hρ⟩ := xiDivisorSupport_infinite.nonempty
  refine ⟨⟨⟨ρ, hρ⟩, ⟨0, ?_⟩⟩⟩
  have hpos := xi_divisor_pos_on_support ⟨ρ, hρ⟩
  omega

/-- **The shell coordinate attains its minimum on the divisor.**  Finiteness of every shell plus
nonemptiness of the divisor give a copy of least shell coordinate. -/
theorem exists_min_xiSpectralSq_re :
    ∃ q₀ : XiZeroCopy, ∀ q : XiZeroCopy,
      (xiSpectralPoint q₀ ^ 2).re ≤ (xiSpectralPoint q ^ 2).re := by
  classical
  obtain ⟨q₁⟩ := nonempty_xiZeroCopy
  set R : ℝ := (xiSpectralPoint q₁ ^ 2).re with hR
  have hfin := finite_xiHeatShell R
  set S : Finset XiZeroCopy := hfin.toFinset with hS
  have hq₁S : q₁ ∈ S := by
    rw [hS, Set.Finite.mem_toFinset]
    exact le_of_eq hR.symm
  obtain ⟨q₀, hq₀S, hq₀⟩ :=
    S.exists_min_image (fun q => (xiSpectralPoint q ^ 2).re) ⟨q₁, hq₁S⟩
  refine ⟨q₀, fun q => ?_⟩
  by_cases hq : q ∈ S
  · exact hq₀ q hq
  · have hgt : R < (xiSpectralPoint q ^ 2).re := by
      rw [hS, Set.Finite.mem_toFinset] at hq
      exact not_le.mp hq
    have hle : (xiSpectralPoint q₀ ^ 2).re ≤ R := by
      have := hq₀ q₁ hq₁S
      rw [← hR] at this
      exact this
    linarith


/-- **The bottom shell is isolated.**  There is a positive gap below which no copy sits other than
those of minimal shell coordinate: every copy either lies exactly in the bottom shell or is at
least `delta` above it.  Finiteness of shells makes the set of competing values finite, so the gap
is attained. -/
theorem exists_bottom_shell_gap :
    ∃ (A δ : ℝ), 0 < δ ∧ (∃ q₀ : XiZeroCopy, (xiSpectralPoint q₀ ^ 2).re = A) ∧
      (∀ q : XiZeroCopy, A ≤ (xiSpectralPoint q ^ 2).re) ∧
      ∀ q : XiZeroCopy,
        (xiSpectralPoint q ^ 2).re = A ∨ A + δ ≤ (xiSpectralPoint q ^ 2).re := by
  classical
  obtain ⟨q₀, hmin⟩ := exists_min_xiSpectralSq_re
  set A : ℝ := (xiSpectralPoint q₀ ^ 2).re with hA
  have hfin := finite_xiHeatShell (A + 1)
  set S : Finset XiZeroCopy := hfin.toFinset with hS
  have hmemS : ∀ q : XiZeroCopy, q ∈ S ↔ (xiSpectralPoint q ^ 2).re ≤ A + 1 := by
    intro q
    rw [hS, Set.Finite.mem_toFinset]
    exact Iff.rfl
  set T : Finset XiZeroCopy :=
    S.filter (fun q => A < (xiSpectralPoint q ^ 2).re) with hT
  by_cases hTe : T.Nonempty
  · obtain ⟨q₁, hq₁T, hq₁⟩ :=
      T.exists_min_image (fun q => (xiSpectralPoint q ^ 2).re) hTe
    have hq₁gt : A < (xiSpectralPoint q₁ ^ 2).re := by
      have hmem := hq₁T
      rw [hT, Finset.mem_filter] at hmem
      exact hmem.2
    refine ⟨A, min ((xiSpectralPoint q₁ ^ 2).re - A) 1, ?_, ⟨q₀, rfl⟩, hmin, ?_⟩
    · exact lt_min (by linarith) one_pos
    · intro q
      rcases eq_or_lt_of_le (hmin q) with heq | hlt
      · exact Or.inl heq.symm
      · right
        by_cases hqS : q ∈ S
        · have hqT : q ∈ T := by
            rw [hT, Finset.mem_filter]
            exact ⟨hqS, hlt⟩
          have := hq₁ q hqT
          have hle : min ((xiSpectralPoint q₁ ^ 2).re - A) 1 ≤
              (xiSpectralPoint q₁ ^ 2).re - A := min_le_left _ _
          linarith
        · have hgt : A + 1 < (xiSpectralPoint q ^ 2).re := by
            rw [hmemS] at hqS
            exact not_le.mp hqS
          have hle : min ((xiSpectralPoint q₁ ^ 2).re - A) 1 ≤ 1 := min_le_right _ _
          linarith
  · refine ⟨A, 1, one_pos, ⟨q₀, rfl⟩, hmin, ?_⟩
    intro q
    rcases eq_or_lt_of_le (hmin q) with heq | hlt
    · exact Or.inl heq.symm
    · right
      by_cases hqS : q ∈ S
      · exact absurd ⟨q, by rw [hT, Finset.mem_filter]; exact ⟨hqS, hlt⟩⟩ hTe
      · have hgt : A + 1 < (xiSpectralPoint q ^ 2).re := by
          rw [hmemS] at hqS
          exact not_le.mp hqS
        linarith

end

end RHTower
