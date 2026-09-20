import GaloisForLFunctions.RHTower.SuzukiCausalDepthFrostmanRecurrenceNoGo

/-!
# Finite-head recurrence obstruction for Suzuki causal-depth Frostman walls

The causal-depth transfer has a strictly faithful two-prime diagonal, but any fixed finite head
still consists of finitely many Bohr phases.  This file gives the exact finite-head object and
proves its source-radius-explicit late recurrence estimate.  Consequently no finite positive
Frostman head, of any cardinality, can supply the cofinal lower wall needed by the unresolved
cross-prime Ward transfer.

The obstruction retains every literal Suzuki radius.  It does not replace the source by a compact
model or a generic norm estimate.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- Sum of normalized causal-depth Frostman diagonals on a literal finite prime head. -/
def suzukiCriticalApertureDepthFrostmanFiniteHeadProfile
    (h a t : ℝ) (P : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ P, suzukiCriticalApertureDepthFrostmanProfile h a t p

/-- Translation-invariant deficit from the central cap of a literal finite prime head. -/
def suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation
    (h a : ℝ) (P : Finset Nat.Primes) (t u : ℝ) : ℝ :=
  ∑ p ∈ P, (1 - suzukiCriticalApertureDepthFrostmanProfile h a (t - u) p)

/-- The finite-head deficit is exactly its cardinal central cap minus its profile. -/
theorem suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation_eq_card_sub_profile
    (h a t u : ℝ) (P : Finset Nat.Primes) :
    suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation h a P t u =
      (P.card : ℝ) -
        suzukiCriticalApertureDepthFrostmanFiniteHeadProfile h a (t - u) P := by
  rw [suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation,
    suzukiCriticalApertureDepthFrostmanFiniteHeadProfile,
    Finset.sum_sub_distrib]
  simp

/-- A finite causal-depth Frostman head has nonnegative central deficit. -/
theorem suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation_nonneg
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (P : Finset Nat.Primes) (t u : ℝ) :
    0 ≤ suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation h a P t u := by
  rw [suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation]
  exact Finset.sum_nonneg fun p _ =>
    sub_nonneg.mpr (suzukiCriticalApertureDepthFrostmanProfile_le_one hh ha (t - u) p)

/-- Every fixed finite causal-depth head returns arbitrarily close to its central cap at
arbitrarily late heights.  The error coefficient is the exact sum of its source-selected
Frostman radii. -/
theorem exists_late_suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation_le
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (P : Finset Nat.Primes) {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧
      suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation h a P t 0 ≤
        (∑ p ∈ P,
          (suzukiCriticalApertureDepthFusionRadius h a p)⁻¹ /
            ((suzukiCriticalApertureDepthFusionRadius h a p)⁻¹ - 1)^2) * δ^2 := by
  let B : {p : Nat.Primes // p ∈ P} → ℝ := fun p =>
    -(Real.log (p.1 : ℝ) / 2)
  obtain ⟨t, ht, hphase⟩ := exists_simultaneous_phase_recurrence B hδ T
  refine ⟨t, ht, ?_⟩
  rw [suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  let q : ℝ := (suzukiCriticalApertureDepthFusionRadius h a p)⁻¹
  have hq : 1 < q :=
    one_lt_inv_suzukiCriticalApertureDepthFusionRadius hh ha p
  have hpPhase : ‖HTGeometry.phaseClockValue (Real.log (p : ℝ) / 2) t - 1‖ ≤ δ := by
    rw [← bohrChar_neg_eq_phaseClock]
    simpa only [B] using hphase ⟨p, hp⟩
  have hphaseSq : ‖HTGeometry.phaseClockValue (Real.log (p : ℝ) / 2) t - 1‖ ^ 2 ≤ δ^2 :=
    (sq_le_sq₀ (norm_nonneg _) hδ.le).mpr hpPhase
  have hdef : 1 - suzukiCriticalApertureDepthFrostmanProfile h a t p ≤
      (q / (q - 1)^2) * δ^2 := by
    have hbase := frostman_profile_deficit_le_phaseClock_sq hq
      (r := Real.log (p : ℝ) / 2) (t := t)
    have hmul := mul_le_mul_of_nonneg_left hphaseSq
      (by positivity : 0 ≤ q / (q - 1)^2)
    calc
      1 - suzukiCriticalApertureDepthFrostmanProfile h a t p =
          1 - ccmFrostmanPoissonProfile q ((Real.log (p : ℝ) / 2) * t) := by
            simp only [suzukiCriticalApertureDepthFrostmanProfile, q]
            ring
      _ ≤ (q / (q - 1)^2) *
          ‖HTGeometry.phaseClockValue (Real.log (p : ℝ) / 2) t - 1‖ ^ 2 := hbase
      _ ≤ (q / (q - 1)^2) * δ^2 := hmul
  simpa only [sub_zero, q] using hdef

/-- **Finite-head recurrence no-go.** No fixed finite positive causal-depth Frostman head can be
eventually bounded away from its central cap.  This eliminates every finite-head enlargement of
the earlier two-prime separator as a cofinal Ward-coercive producer. -/
theorem not_exists_eventual_positive_lowerBound_suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (P : Finset Nat.Primes) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ε ≤ suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation h a P t 0 := by
  rintro ⟨ε, hε, T, hlower⟩
  let C : ℝ := ∑ p ∈ P,
    (suzukiCriticalApertureDepthFusionRadius h a p)⁻¹ /
      ((suzukiCriticalApertureDepthFusionRadius h a p)⁻¹ - 1)^2
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact Finset.sum_nonneg fun p _ => by
      have hp := one_lt_inv_suzukiCriticalApertureDepthFusionRadius hh ha p
      positivity
  let δ : ℝ := min 1 (ε / (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min (by norm_num) (div_pos hε hC1)
  obtain ⟨t, ht, hbound⟩ :=
    exists_late_suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation_le
      hh ha P hδ T
  change suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation h a P t 0 ≤ C * δ^2 at hbound
  have hδone : δ ≤ 1 := by
    dsimp only [δ]
    exact min_le_left _ _
  have hδsq : δ ^ 2 ≤ δ := by
    nlinarith [mul_self_nonneg (δ - 1)]
  have hCδsq : C * δ ^ 2 ≤ C * δ :=
    mul_le_mul_of_nonneg_left hδsq hC
  have hδfrac : δ ≤ ε / (C + 1) := by
    dsimp only [δ]
    exact min_le_right _ _
  have hCδ : C * δ ≤ C * (ε / (C + 1)) :=
    mul_le_mul_of_nonneg_left hδfrac hC
  have hCfrac : C * (ε / (C + 1)) < ε := by
    rw [show C * (ε / (C + 1)) = (C * ε) / (C + 1) by ring]
    rw [div_lt_iff₀ hC1]
    nlinarith
  have hlt : suzukiCriticalApertureDepthFrostmanFiniteHeadSeparation h a P t 0 < ε :=
    lt_of_le_of_lt hbound (lt_of_le_of_lt hCδsq (lt_of_le_of_lt hCδ hCfrac))
  exact (not_lt_of_ge (hlower t ht)) hlt

end

end RHTower
