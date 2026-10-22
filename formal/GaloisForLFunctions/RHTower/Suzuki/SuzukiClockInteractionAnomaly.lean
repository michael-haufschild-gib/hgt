import GaloisForLFunctions.HTGeometry.ObserverClockInteractionAnomaly
import GaloisForLFunctions.RHTower.Suzuki.SuzukiHarmonicRieszClockTransmutation

/-!
# Suzuki clock-created interaction anomaly

The literal completed harmonic-to-square-root clock rate is paired with one fixed two-state
marginal reporter.  Its anchored interaction is exactly twice the clock contrast and escapes every
finite bound.  Thus this physical clock change cannot descend through even the smallest nontrivial
marginal quotient.
-/

namespace GaloisForLFunctions.RHTower

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Literal harmonic-to-square-root clock paired with the fixed two-state sign organ. -/
def completedRieszClockOrganObservable :
    FullValueSubtype (ℕ × Fin 2) → ℂ :=
  separatedClockOrganObservable
    (fun k => (completedRieszHarmonicClockRatio k : ℂ)) finTwoOrganSign

/-- Exact literal clock-created interaction amplitude. -/
theorem completedRieszClockOrganObservable_interaction_zero (k : ℕ) :
    productAnchoredInteractionPart ℕ (Fin 2)
        completedRieszClockOrganObservable
        ⟨(k, 0), Set.mem_univ _⟩ =
      (-2 : ℂ) *
        ((completedRieszHarmonicClockRatio k : ℂ) -
          (completedRieszHarmonicClockRatio 1 : ℂ)) := by
  exact finTwo_clock_interaction_anomaly_zero
    ℕ (fun j => (completedRieszHarmonicClockRatio j : ℂ)) k

/-- Closed unconditional witness: one fixed marginal probe creates unbounded interaction anomaly. -/
theorem exists_completedRieszClockInteractionAnomaly_escape (C : ℝ) :
    ∃ k : ℕ,
      C < ‖productAnchoredInteractionPart ℕ (Fin 2)
        completedRieszClockOrganObservable
        ⟨(k, 0), Set.mem_univ _⟩‖ := by
  obtain ⟨n : ℕ, hn⟩ :=
    exists_nat_gt (C + |completedRieszHarmonicClockRatio 1|)
  let k : ℕ := n + 3
  have hk : 3 ≤ k := by omega
  have hlower := completedRieszHarmonicClockRatio_ge_index (k := k) hk
  have hanchor : completedRieszHarmonicClockRatio 1 ≤
      |completedRieszHarmonicClockRatio 1| := le_abs_self _
  have hdiff : C < completedRieszHarmonicClockRatio k -
      completedRieszHarmonicClockRatio 1 := by
    dsimp only [k] at hlower
    push_cast at hlower
    nlinarith
  have habs : C < |completedRieszHarmonicClockRatio k -
      completedRieszHarmonicClockRatio 1| :=
    lt_of_lt_of_le hdiff (le_abs_self _)
  refine ⟨k, ?_⟩
  rw [completedRieszClockOrganObservable_interaction_zero]
  have hnorm :
      ‖(-2 : ℂ) *
        ((completedRieszHarmonicClockRatio k : ℂ) -
          (completedRieszHarmonicClockRatio 1 : ℂ))‖ =
        2 * |completedRieszHarmonicClockRatio k -
          completedRieszHarmonicClockRatio 1| := by
    rw [norm_mul]
    norm_num
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  have hdouble : |completedRieszHarmonicClockRatio k -
      completedRieszHarmonicClockRatio 1| ≤
      2 * |completedRieszHarmonicClockRatio k -
        completedRieszHarmonicClockRatio 1| := by
    nlinarith [abs_nonneg
      (completedRieszHarmonicClockRatio k - completedRieszHarmonicClockRatio 1)]
  exact lt_of_lt_of_le habs hdouble

/-- Zero-argument certificate for the exact literal anomaly and its unconditional escape. -/
theorem suzukiClockInteractionAnomaly_completion_certificate :
    (∀ k : ℕ,
      productAnchoredInteractionPart ℕ (Fin 2)
          completedRieszClockOrganObservable
          ⟨(k, 0), Set.mem_univ _⟩ =
        (-2 : ℂ) *
          ((completedRieszHarmonicClockRatio k : ℂ) -
            (completedRieszHarmonicClockRatio 1 : ℂ))) ∧
    (∀ C : ℝ, ∃ k : ℕ,
      C < ‖productAnchoredInteractionPart ℕ (Fin 2)
        completedRieszClockOrganObservable
        ⟨(k, 0), Set.mem_univ _⟩‖) := by
  exact ⟨completedRieszClockOrganObservable_interaction_zero,
    exists_completedRieszClockInteractionAnomaly_escape⟩

end

end GaloisForLFunctions.RHTower
