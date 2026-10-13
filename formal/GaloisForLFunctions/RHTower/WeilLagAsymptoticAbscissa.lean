import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse
import GaloisForLFunctions.RHTower.WeilLagZerosApproachLine

/-!
# The subtracted Weil lag reads the asymptotic abscissa exactly

Let `Φ_S = Φ − Re Σ_{q ∈ S} w_q e^{u(ρ_q − ½)}` be the Weil lag function with the waves of a finite
set `S` of zero copies removed (`subtractedLag`).

**Theorem** (`exists_subtractedLag_le_exp_iff_finite_re_gt`).  For `0 ≤ a < ½`, some finite `S`
gives `Φ_S(u) ≤ M e^{au}` for all `u ≥ 0` iff only finitely many zeros have `Re ρ > ½ + a`.

So the infimal growth exponent of the lag after finite subtraction is the limit superior `Θ∞` of
`Re ρ − ½` along growing heights, in the same way as the Gaussian central gap (rate
`Θ∞ + Θ∞²/8`) and Hadamard positivity (abscissa `½ + Θ∞`).  At `a = 0` this is the corpus's
finite off-line law.  Under the asymptotic abscissa law the subtraction is useless
(`exists_subtractedLag_le_exp_iff_forall_re_le_of_asymptoticAbscissaLaw`): the exponent is then the
full supremum of `Re ρ − ½`.

**Proof.**  If only finitely many zeros lie right of `½ + a`, so do their reflections, and removing
all zeros at distance `> a` from the line leaves `|Φ_S(u)| ≤ e^{au} Σ|w_q|`
(`abs_subtractedLag_le_exp_of_subset`).  Conversely, Landau's argument places every zero whose pole
is not removed in `Re ρ ≤ ½ + a` (`re_le_half_add_of_subtractedLag_le_exp`); the zeros with removed
poles have bounded spectral points, so they are finitely many.
-/

open Complex Set

namespace RHTower.BacklundConverse

open RHTower.LindelofSparse

noncomputable section

/-- **The subtracted lag reads the asymptotic abscissa.** -/
theorem exists_subtractedLag_le_exp_iff_finite_re_gt {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    (∃ S : Finset XiZeroCopy, ∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → subtractedLag S u ≤ M * Real.exp (a * u)) ↔
      {q : XiZeroCopy | 1 / 2 + a < (q.1 : ℂ).re}.Finite := by
  constructor
  · rintro ⟨S, M, hM⟩
    obtain ⟨R, hR⟩ := ((Set.finite_coe_iff.mp (offLinePoles_finite S)).image
      fun p : ℂ => ‖p‖).bddAbove
    refine (xiZeroBall (⌈R⌉₊)).finite_toSet.subset fun q hq => ?_
    simp only [mem_setOf_eq] at hq
    simp only [Finset.mem_coe, mem_xiZeroBall]
    have hpole : lagPole q ∈ offLinePoles S := by
      by_contra hnot
      have := re_le_half_add_of_subtractedLag_le_exp S ha0 ha hM q hnot
      linarith
    rw [norm_xiSpectralPoint_eq_norm_lagPole]
    exact (hR ⟨lagPole q, hpole, rfl⟩).trans (Nat.le_ceil R)
  · intro hF
    have hE := finite_abs_spectral_im_gt_of_finite_re_gt hF
    refine ⟨hE.toFinset, lagWeightTotal, fun u hu => ?_⟩
    have hb := abs_subtractedLag_le_exp_of_subset hE.toFinset (a := a) (fun q hq => ?_) hu
    · have := (abs_le.mp hb).2
      linarith [mul_comm (Real.exp (a * u)) lagWeightTotal]
    · rw [Set.Finite.mem_toFinset]
      show a < |(xiSpectralPoint q).im|
      rw [spectral_im_eq, abs_sub_comm]
      exact hq

/-- **Under the asymptotic abscissa law, finite subtraction does not lower the lag exponent.** -/
theorem exists_subtractedLag_le_exp_iff_forall_re_le_of_asymptoticAbscissaLaw
    (hA : AsymptoticAbscissaLaw) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    (∃ S : Finset XiZeroCopy, ∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → subtractedLag S u ≤ M * Real.exp (a * u)) ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + a := by
  rw [exists_subtractedLag_le_exp_iff_finite_re_gt ha0 ha]
  refine ⟨hA a ha0, fun hall => Set.finite_empty.subset fun q hq => ?_⟩
  simp only [mem_setOf_eq] at hq
  exact absurd (hall q) (not_le.mpr hq)

end

end RHTower.BacklundConverse
