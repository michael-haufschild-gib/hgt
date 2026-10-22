import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthFrostmanTransfer
import GaloisForLFunctions.RHTower.SimultaneousPhaseRecurrence

/-!
# Finite-prime recurrence obstruction for Suzuki causal-depth Frostman separation

The two-prime causal-depth Frostman separator is nonnegative and vanishes only at equal heights.
That pointwise faithfulness cannot yield cofinal coercivity: every fixed finite family of prime-log
phases has arbitrarily late simultaneous recurrences.  This module quantifies the collapse for the
literal two-prime Suzuki profile and rules out an eventual positive lower bound.

Thus the unresolved cross-prime Ward transfer cannot be closed by any fixed finite Frostman packet.
It must retain a genuinely non-finite mechanism (or a non-recurrent coordinate) before attempting a
rectangular Ward lower bound.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

private theorem frostman_profile_deficit_le_phase_sq {q θ : ℝ} (hq : 1 < q) :
    1 - ccmFrostmanPoissonProfile q θ ≤
      (q / (q - 1)^(2 : ℕ)) * ‖1 - Complex.exp ((θ : ℂ) * I)‖ ^ (2 : ℕ) := by
  have hD : 0 < q ^ (2 : ℕ) - 2 * q * Real.cos θ + 1 :=
    ccmFrostman_denominator_pos hq
  have hbase : 0 < (q - 1)^(2 : ℕ) := sq_pos_of_pos (sub_pos.mpr hq)
  have hbasele : (q - 1)^(2 : ℕ) ≤ q ^ (2 : ℕ) - 2 * q * Real.cos θ + 1 := by
    have hc := Real.cos_le_one θ
    nlinarith
  rw [ccmFrostmanPoissonProfile, Complex.sq_norm, normSq_one_sub_exp_I_mul]
  have hid : 1 - (q - 1) ^ (2 : ℕ) / (q ^ (2 : ℕ) - 2 * q * Real.cos θ + 1) =
      q * (2 - 2 * Real.cos θ) / (q ^ (2 : ℕ) - 2 * q * Real.cos θ + 1) := by
    calc
      1 - (q - 1) ^ (2 : ℕ) / (q ^ (2 : ℕ) - 2 * q * Real.cos θ + 1) =
          (q ^ (2 : ℕ) - 2 * q * Real.cos θ + 1) /
              (q ^ (2 : ℕ) - 2 * q * Real.cos θ + 1) -
            (q - 1) ^ (2 : ℕ) / (q ^ (2 : ℕ) - 2 * q * Real.cos θ + 1) := by
              nth_rewrite 1 [← div_self hD.ne']
              rfl
      _ = ((q ^ (2 : ℕ) - 2 * q * Real.cos θ + 1) - (q - 1) ^ (2 : ℕ)) /
            (q ^ (2 : ℕ) - 2 * q * Real.cos θ + 1) := by
              exact (sub_div _ _ _).symm
      _ = q * (2 - 2 * Real.cos θ) / (q ^ (2 : ℕ) - 2 * q * Real.cos θ + 1) := by
              congr 1
              ring
  rw [hid]
  have hnon : 0 ≤ 2 - 2 * Real.cos θ := by
    linarith [Real.cos_le_one θ]
  calc
    q * (2 - 2 * Real.cos θ) / (q ^ (2 : ℕ) - 2 * q * Real.cos θ + 1)
        ≤ q * (2 - 2 * Real.cos θ) / (q - 1)^(2 : ℕ) := by
          exact (div_le_div_iff₀ hD hbase).mpr (by nlinarith)
    _ = (q / (q - 1)^(2 : ℕ)) * (2 - 2 * Real.cos θ) := by ring

/-- The Bohr character at the reflected rate is the prime-phase clock. -/
theorem bohrChar_neg_eq_phaseClock (r t : ℝ) :
    GaloisForLFunctions.bohrChar (-r) t = HTGeometry.phaseClockValue r t := by
  rw [GaloisForLFunctions.bohrChar, HTGeometry.phaseClockValue]
  congr 1
  push_cast
  ring

/-- A Frostman deficit is quadratically controlled by its literal phase displacement. -/
theorem frostman_profile_deficit_le_phaseClock_sq {q r t : ℝ} (hq : 1 < q) :
    1 - ccmFrostmanPoissonProfile q (r * t) ≤
      (q / (q - 1)^(2 : ℕ)) * ‖HTGeometry.phaseClockValue r t - 1‖ ^ (2 : ℕ) := by
  have hprofile := frostman_profile_deficit_le_phase_sq (θ := r * t) hq
  have hnorm : ‖1 - Complex.exp (((r * t : ℝ) : ℂ) * I)‖ =
      ‖HTGeometry.phaseClockValue r t - 1‖ := by
    rw [HTGeometry.phaseClockValue]
    rw [show Complex.exp (((r * t : ℝ) : ℂ) * I) - 1 =
      -(1 - Complex.exp (((r * t : ℝ) : ℂ) * I)) by ring, norm_neg]
  rwa [hnorm] at hprofile

/-- Every fixed pair of literal causal-depth Frostman coordinates returns arbitrarily close to its
zero-height cap at arbitrarily late heights.  The displayed constant is source-selected: it uses
the two actual aperture-dependent radii, rather than an abstract compactness modulus. -/
theorem exists_late_suzukiCriticalApertureDepthFrostmanSeparation_le
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (p q : Nat.Primes) {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧
      suzukiCriticalApertureDepthFrostmanSeparation h a p q t 0 ≤
        ((suzukiCriticalApertureDepthFusionRadius h a p)⁻¹ /
          ((suzukiCriticalApertureDepthFusionRadius h a p)⁻¹ - 1)^(2 : ℕ) +
          (suzukiCriticalApertureDepthFusionRadius h a q)⁻¹ /
          ((suzukiCriticalApertureDepthFusionRadius h a q)⁻¹ - 1)^(2 : ℕ)) * δ^(2 : ℕ) := by
  let B : Fin 2 → ℝ := fun j =>
    if j = 0 then -(Real.log (p : ℝ) / 2) else -(Real.log (q : ℝ) / 2)
  obtain ⟨t, ht, hpq⟩ := exists_simultaneous_phase_recurrence B hδ T
  refine ⟨t, ht, ?_⟩
  have hpPhase : ‖HTGeometry.phaseClockValue (Real.log (p : ℝ) / 2) t - 1‖ ≤ δ := by
    rw [← bohrChar_neg_eq_phaseClock]
    simpa [B] using hpq 0
  have hqPhase : ‖HTGeometry.phaseClockValue (Real.log (q : ℝ) / 2) t - 1‖ ≤ δ := by
    rw [← bohrChar_neg_eq_phaseClock]
    simpa [B] using hpq 1
  let qp : ℝ := (suzukiCriticalApertureDepthFusionRadius h a p)⁻¹
  let qq : ℝ := (suzukiCriticalApertureDepthFusionRadius h a q)⁻¹
  have hqp : 1 < qp := one_lt_inv_suzukiCriticalApertureDepthFusionRadius hh ha p
  have hqq : 1 < qq := one_lt_inv_suzukiCriticalApertureDepthFusionRadius hh ha q
  have hpsq : ‖HTGeometry.phaseClockValue (Real.log (p : ℝ) / 2) t - 1‖ ^ (2 : ℕ) ≤ δ^(2 : ℕ) :=
    (sq_le_sq₀ (norm_nonneg _) hδ.le).mpr hpPhase
  have hqsq : ‖HTGeometry.phaseClockValue (Real.log (q : ℝ) / 2) t - 1‖ ^ (2 : ℕ) ≤ δ^(2 : ℕ) :=
    (sq_le_sq₀ (norm_nonneg _) hδ.le).mpr hqPhase
  have hpdef : 1 - suzukiCriticalApertureDepthFrostmanProfile h a t p ≤
      (qp / (qp - 1)^(2 : ℕ)) * δ^(2 : ℕ) := by
    rw [suzukiCriticalApertureDepthFrostmanProfile]
    have hprofile := frostman_profile_deficit_le_phaseClock_sq hqp
      (r := Real.log (p : ℝ) / 2) (t := t)
    have hmul := mul_le_mul_of_nonneg_left hpsq (by positivity : 0 ≤ qp / (qp - 1)^(2 : ℕ))
    calc
      1 - ccmFrostmanPoissonProfile
          (suzukiCriticalApertureDepthFusionRadius h a p)⁻¹
          (t * Real.log (p : ℝ) / 2) =
          1 - ccmFrostmanPoissonProfile qp
            ((Real.log (p : ℝ) / 2) * t) := by simp only [qp]; ring
      _ ≤ (qp / (qp - 1)^(2 : ℕ)) *
          ‖HTGeometry.phaseClockValue (Real.log (p : ℝ) / 2) t - 1‖ ^ (2 : ℕ) := hprofile
      _ ≤ (qp / (qp - 1)^(2 : ℕ)) * δ^(2 : ℕ) := hmul
  have hqdef : 1 - suzukiCriticalApertureDepthFrostmanProfile h a t q ≤
      (qq / (qq - 1)^(2 : ℕ)) * δ^(2 : ℕ) := by
    rw [suzukiCriticalApertureDepthFrostmanProfile]
    have hprofile := frostman_profile_deficit_le_phaseClock_sq hqq
      (r := Real.log (q : ℝ) / 2) (t := t)
    have hmul := mul_le_mul_of_nonneg_left hqsq (by positivity : 0 ≤ qq / (qq - 1)^(2 : ℕ))
    calc
      1 - ccmFrostmanPoissonProfile
          (suzukiCriticalApertureDepthFusionRadius h a q)⁻¹
          (t * Real.log (q : ℝ) / 2) =
          1 - ccmFrostmanPoissonProfile qq
            ((Real.log (q : ℝ) / 2) * t) := by simp only [qq]; ring
      _ ≤ (qq / (qq - 1)^(2 : ℕ)) *
          ‖HTGeometry.phaseClockValue (Real.log (q : ℝ) / 2) t - 1‖ ^ (2 : ℕ) := hprofile
      _ ≤ (qq / (qq - 1)^(2 : ℕ)) * δ^(2 : ℕ) := hmul
  rw [suzukiCriticalApertureDepthFrostmanSeparation,
    suzukiCriticalApertureDepthFrostmanPairProfile]
  simp only [sub_zero]
  dsimp [qp, qq] at hpdef hqdef ⊢
  linarith

/-- **Finite-prime recurrence no-go.**  Although distinct primes make the literal pair separator
pointwise faithful, no fixed two-prime causal-depth Frostman block is eventually bounded away from
zero.  Hence it cannot itself provide a cofinal coercive or Ward-semibounding mechanism. -/
theorem not_exists_eventual_positive_lowerBound_suzukiCriticalApertureDepthFrostmanSeparation
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (p q : Nat.Primes) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ε ≤ suzukiCriticalApertureDepthFrostmanSeparation h a p q t 0 := by
  rintro ⟨ε, hε, T, hsep⟩
  let C : ℝ :=
    (suzukiCriticalApertureDepthFusionRadius h a p)⁻¹ /
        ((suzukiCriticalApertureDepthFusionRadius h a p)⁻¹ - 1)^(2 : ℕ) +
      (suzukiCriticalApertureDepthFusionRadius h a q)⁻¹ /
        ((suzukiCriticalApertureDepthFusionRadius h a q)⁻¹ - 1)^(2 : ℕ)
  have hCp : 0 ≤ (suzukiCriticalApertureDepthFusionRadius h a p)⁻¹ /
      ((suzukiCriticalApertureDepthFusionRadius h a p)⁻¹ - 1)^(2 : ℕ) := by
    have hp := one_lt_inv_suzukiCriticalApertureDepthFusionRadius hh ha p
    positivity
  have hCq : 0 ≤ (suzukiCriticalApertureDepthFusionRadius h a q)⁻¹ /
      ((suzukiCriticalApertureDepthFusionRadius h a q)⁻¹ - 1)^(2 : ℕ) := by
    have hq := one_lt_inv_suzukiCriticalApertureDepthFusionRadius hh ha q
    positivity
  have hC : 0 ≤ C := by dsimp [C]; linarith
  let δ : ℝ := min 1 (ε / (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (div_pos hε hC1)
  obtain ⟨t, ht, hbound⟩ :=
    exists_late_suzukiCriticalApertureDepthFrostmanSeparation_le hh ha p q hδ T
  have hδnonneg : 0 ≤ δ := hδ.le
  have hδone : δ ≤ 1 := by
    dsimp [δ]
    exact min_le_left _ _
  have hsq : δ ^ (2 : ℕ) ≤ δ := by
    nlinarith [mul_self_nonneg (δ - 1)]
  have hCδsq : C * δ ^ (2 : ℕ) ≤ C * δ :=
    mul_le_mul_of_nonneg_left hsq hC
  have hδfrac : δ ≤ ε / (C + 1) := by
    dsimp [δ]
    exact min_le_right _ _
  have hCδ : C * δ ≤ C * (ε / (C + 1)) :=
    mul_le_mul_of_nonneg_left hδfrac hC
  have hCfrac : C * (ε / (C + 1)) < ε := by
    rw [show C * (ε / (C + 1)) = (C * ε) / (C + 1) by ring]
    rw [div_lt_iff₀ hC1]
    nlinarith
  have hlt : suzukiCriticalApertureDepthFrostmanSeparation h a p q t 0 < ε :=
    lt_of_le_of_lt hbound (lt_of_le_of_lt hCδsq (lt_of_le_of_lt hCδ hCfrac))
  exact (not_lt_of_ge (hsep t ht)) hlt

end

end RHTower
