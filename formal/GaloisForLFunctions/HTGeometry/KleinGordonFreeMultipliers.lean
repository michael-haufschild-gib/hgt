import GaloisForLFunctions.HTGeometry.KleinGordonFloquetNontrivial

/-!
# The free Floquet multipliers lie on the unit circle

The free monodromy has spectral radius one (statement 344), so all of its multipliers lie in the
closed unit disc. None of them lies inside it.

The reason is that the free evolution is reversible with an inverse of the same size: running one
period backwards is the evolution over `-T`, and that is an isometry too. So for `|k| < 1` the
factorisation

`k·1 − M₀ = (−M₀)(1 − k M₀⁻¹)`

exhibits `k·1 − M₀` as a product of two units — the second by the Neumann series, since
`‖kM₀⁻¹‖ = |k| < 1` — and `k` cannot be a multiplier. Every free multiplier therefore has modulus
exactly one: the free clock oscillates and neither grows nor decays, which is the spectral form of the
exact conservation of its energy.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section FreeMultipliers

variable {T : ℝ}

/-- **The free monodromy is a unit**, with inverse the free monodromy over the opposite period. -/
theorem kgMonodromy_zero_isUnit (hb0 : (0 : ℝ) ≤ 0)
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) r‖ ≤ 0)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
        Lp ℂ 2 (volume : Measure E))) r x) :
    IsUnit (kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T) := by
  set M := kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
    Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T with hM
  set N := kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
    Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs (-T) with hN
  have hper := periodic_const (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
    Lp ℂ 2 (volume : Measure E)) T
  have hNM : N * M = 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    have h : kgPeriodMap (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
        Lp ℂ 2 (volume : Measure E))) (-T)
          (kgPeriodMap (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
            Lp ℂ 2 (volume : Measure E))) T v) = v :=
      kgPeriodMap_left_inverse hb0 hWb hWs hper v
    exact h
  have hMN : M * N = 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    have h : kgPeriodMap (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
        Lp ℂ 2 (volume : Measure E))) T
          (kgPeriodMap (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
            Lp ℂ 2 (volume : Measure E))) (-T) v) = v :=
      kgPeriodMap_right_inverse hb0 hWb hWs hper v
    exact h
  exact ⟨⟨M, N, hMN, hNM⟩, rfl⟩

/-- **No free multiplier lies inside the unit disc.** -/
theorem one_le_norm_of_mem_spectrum_kgMonodromy_zero (hb0 : (0 : ℝ) ≤ 0)
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) r‖ ≤ 0)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
        Lp ℂ 2 (volume : Measure E))) r x) {k : ℂ}
    (hk : k ∈ spectrum ℂ (kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T)) : 1 ≤ ‖k‖ := by
  set M := kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
    Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T with hM
  set N := kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
    Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs (-T) with hN
  by_contra hlt
  push Not at hlt
  have hNnorm : ‖N‖ = 1 := by
    have h := norm_kgMonodromy_zero_pow (T := -T) hb0 hWb hWs 1
    rwa [pow_one] at h
  have hsmul : ‖k • N‖ < 1 := by
    rw [norm_smul, hNnorm, mul_one]
    exact hlt
  have hunit1 : IsUnit (1 - k • N) := isUnit_one_sub_of_norm_lt_one hsmul
  have hunitM : IsUnit M := kgMonodromy_zero_isUnit hb0 hWb hWs
  have hMN : M * N = 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    have hper := periodic_const (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E)) T
    have h : kgPeriodMap (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
        Lp ℂ 2 (volume : Measure E))) T
          (kgPeriodMap (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
            Lp ℂ 2 (volume : Measure E))) (-T) v) = v :=
      kgPeriodMap_right_inverse hb0 hWb hWs hper v
    exact h
  have hfac : algebraMap ℂ (KGEnergy E →L[ℂ] KGEnergy E) k - M = -(M * (1 - k • N)) := by
    have hk' : k • N = algebraMap ℂ (KGEnergy E →L[ℂ] KGEnergy E) k * N := Algebra.smul_def k N
    rw [hk', mul_sub, mul_one, ← mul_assoc, ← Algebra.commutes k M, mul_assoc, hMN, mul_one]
    abel
  have hunit : IsUnit (algebraMap ℂ (KGEnergy E →L[ℂ] KGEnergy E) k - M) := by
    rw [hfac]
    exact (hunitM.mul hunit1).neg
  exact absurd hunit (spectrum.mem_iff.mp hk)

/-- **The free Floquet multipliers lie on the unit circle.** The free clock oscillates: it neither
grows nor decays, which is the spectral form of the exact conservation of its energy. -/
theorem norm_eq_one_of_mem_spectrum_kgMonodromy_zero (hb0 : (0 : ℝ) ≤ 0)
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) r‖ ≤ 0)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
        Lp ℂ 2 (volume : Measure E))) r x) {k : ℂ}
    (hk : k ∈ spectrum ℂ (kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T)) : ‖k‖ = 1 := by
  have hge := one_le_norm_of_mem_spectrum_kgMonodromy_zero hb0 hWb hWs hk
  have hC : ∀ n : ℕ, ‖kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T ^ n‖ ≤ 1 := fun n =>
    le_of_eq (norm_kgMonodromy_zero_pow hb0 hWb hWs n)
  have hle := norm_le_one_of_mem_spectrum_of_pow_bound hb0 hWb hWs hC hk
  exact le_antisymm hle hge

end FreeMultipliers

end GaloisForLFunctions.HTGeometry
