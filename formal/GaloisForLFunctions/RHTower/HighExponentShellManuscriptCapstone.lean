import GaloisForLFunctions.RHTower.HighExponentShellHypertranscendence
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# Manuscript capstone for the positive hypertranscendental Riemann-divisor frame

This module packages the exact critical-strip consequences of the shell divisor theorem with
the optimal relative differential-independence result.  Every statement is unconditional:
`RiemannHypothesis` occurs only as one side of proved equivalences.
-/

open scoped Differential UpperEndDifferentialInstances UpperEndComplexTowerInstances

namespace RHTower

open Complex Set
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Zero-freeness of one continued shell current in the open right critical half-strip. -/
def shellCriticalStripZeroFree (m : ℕ) : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
    riemannZeta s * shellMultiplier m s ≠ 0

/-- **One-shell RH equivalence.** Every zero-free high-exponent shell is an exact RH detector,
because its multiplier is holomorphic and zero-free throughout the strict right half-plane. -/
theorem riemannHypothesis_iff_shellCriticalStripZeroFree
    {m : ℕ} (hm : 12 ≤ m) :
    RiemannHypothesis ↔ shellCriticalStripZeroFree m := by
  rw [rh_iff_xi_ne_zero_right]
  constructor
  · intro hxi s hs hsu
    apply mul_ne_zero
    · intro hzeta
      have hs0 : 0 < s.re := by linarith
      have hs1 : s ≠ 1 := by
        intro h
        subst s
        norm_num at hsu
      have hzero : xi s = 0 := (xi_eq_zero_iff hs0 hs1).2 hzeta
      exact hxi s hs hzero
    · exact shellMultiplier_ne_zero hm hs
  · intro hshell s hs hzero
    by_cases hge : 1 ≤ s.re
    · by_cases hs1 : s = 1
      · subst s
        rw [xi_one] at hzero
        norm_num at hzero
      · have hs0 : 0 < s.re := by linarith
        have hzeta : riemannZeta s = 0 := (xi_eq_zero_iff hs0 hs1).1 hzero
        exact (riemannZeta_ne_zero_of_one_le_re hge) hzeta
    · have hlt : s.re < 1 := lt_of_not_ge hge
      have hsprod := hshell s hs hlt
      have hs1 : s ≠ 1 := by
        intro h
        subst s
        norm_num at hlt
      have hs0 : 0 < s.re := lt_trans (by norm_num) hs
      have hzeta : riemannZeta s = 0 := (xi_eq_zero_iff hs0 hs1).1 hzero
      exact hsprod (by rw [hzeta, zero_mul])

/-- RH is equivalent to zero-freeness of at least one shell from the zero-free range. -/
theorem riemannHypothesis_iff_exists_shellCriticalStripZeroFree :
    RiemannHypothesis ↔
      ∃ m : ℕ, 12 ≤ m ∧ shellCriticalStripZeroFree m := by
  constructor
  · intro hRH
    exact ⟨12, le_rfl,
      (riemannHypothesis_iff_shellCriticalStripZeroFree le_rfl).1 hRH⟩
  · rintro ⟨m, hm, hshell⟩
    exact (riemannHypothesis_iff_shellCriticalStripZeroFree hm).2 hshell

/-- RH is equivalent to simultaneous zero-freeness of every high-exponent shell. -/
theorem riemannHypothesis_iff_forall_shellCriticalStripZeroFree :
    RiemannHypothesis ↔
      ∀ m : ℕ, 12 ≤ m → shellCriticalStripZeroFree m := by
  constructor
  · intro hRH m hm
    exact (riemannHypothesis_iff_shellCriticalStripZeroFree hm).1 hRH
  · intro hall
    exact (riemannHypothesis_iff_shellCriticalStripZeroFree le_rfl).2
      (hall 12 le_rfl)

/-- Pointwise form of emptiness of the common shell zero set in the open right critical
half-strip. -/
def shellFrameCommonZeroFree : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
    ∃ m : ℕ, 12 ≤ m ∧ riemannZeta s * shellMultiplier m s ≠ 0

/-- RH is equivalent to emptiness of the common zero set of the high shell frame. -/
theorem riemannHypothesis_iff_shellFrameCommonZeroFree :
    RiemannHypothesis ↔ shellFrameCommonZeroFree := by
  constructor
  · intro hRH s hs hlt
    exact ⟨12, le_rfl,
      (riemannHypothesis_iff_shellCriticalStripZeroFree le_rfl).1 hRH s hs hlt⟩
  · intro hcommon
    apply (riemannHypothesis_iff_shellCriticalStripZeroFree le_rfl).2
    intro s hs hlt hzero
    obtain ⟨m, hm, hnonzero⟩ := hcommon s hs hlt
    have hzeta : riemannZeta s = 0 :=
      (mul_eq_zero.mp hzero).resolve_right
        (shellMultiplier_ne_zero le_rfl hs)
    exact hnonzero (by rw [hzeta, zero_mul])

/-- **Publication capstone.** Adjacent reciprocal zeta dilations from level two onward have
maximal relative differential rank over the full zeta differential field; the level-twelve
subfamily is zero-free in the strict right half-plane, exactly replicates the zeta zeros there,
and its common critical-strip zero-freeness is equivalent to RH. -/
theorem positiveHypertranscendentalRiemannDivisorFrame :
    DifferentialIndependent zetaUpperEndDifferentialField
        (fun m : {m : ℕ // 2 ≤ m} =>
          relativeShellMultiplierUpperEndCarrier m.1)
    ∧ (∀ m : ℕ, 12 ≤ m → ∀ s : ℂ, 1 / 2 < s.re →
        shellMultiplier m s ≠ 0)
    ∧ (∀ m : ℕ, 12 ≤ m → ∀ s : ℂ, 1 / 2 < s.re →
        (riemannZeta s * shellMultiplier m s = 0 ↔ riemannZeta s = 0))
    ∧ (RiemannHypothesis ↔ shellFrameCommonZeroFree) := by
  exact ⟨relativeShellMultiplierUpperEndCarrier_differentialIndependent_two,
    fun _ hm _ hs => shellMultiplier_ne_zero hm hs,
    fun _ hm _ hs => riemannZeta_mul_shellMultiplier_eq_zero_iff hm hs,
    riemannHypothesis_iff_shellFrameCommonZeroFree⟩

end

end RHTower
