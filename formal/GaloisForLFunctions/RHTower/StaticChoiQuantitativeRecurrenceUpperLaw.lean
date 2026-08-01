import GaloisForLFunctions.RHTower.FiniteQuantumSurvivalWorstSpectrumSharpnessLaw
import GaloisForLFunctions.RHTower.FiniteQuantumObserverPostExitRateDistortionLaw
import GaloisForLFunctions.RHTower.StaticChoiTraceDistanceLaw

/-!
# Quantitative recurrence upper law for static Choi clocks

Every finite static Hamiltonian has a normalized spectral Choi trajectory.
The uniform survival-packet recurrence theorem gives a deterministic
rank-`(d-1)` deadline for this actual Choi state.  Rescaling the spectrum
by `M+1` then produces a return strictly after any prescribed discrete
delay `M`, with only the same multiplicative delay factor.

The result is independent of spectral arithmetic, eigenvectors, randomness,
locality, or a complexity hypothesis.  For `d = 2^n` and fixed resolution,
the deadline `(Q+1)^(d-1)` is doubly exponential in qubit number.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Convert a Hamiltonian phase into the unit additive-circle coordinate
used by the normalized Choi vector. -/
def finiteHamiltonianAddCirclePhase
    {d : ℕ} (t : ℝ) (energy : Fin d → ℝ) (i : Fin d) :
    UnitAddCircle :=
  (AddCircle.homeomorphCircle one_ne_zero).symm
    ⟨finiteObserverHamiltonianVertexPhase t energy i,
      by
        simpa [Submonoid.unitSphere] using
          finiteObserverHamiltonianVertexPhase_norm t energy i⟩

/-- The circle character of the additive coordinate is exactly the ordinary
Hamiltonian phase. -/
theorem fourier_finiteHamiltonianAddCirclePhase
    {d : ℕ} (t : ℝ) (energy : Fin d → ℝ) (i : Fin d) :
    fourier 1 (finiteHamiltonianAddCirclePhase t energy i) =
      finiteObserverHamiltonianVertexPhase t energy i := by
  rw [fourier_apply]
  simp only [one_smul]
  change
    ((AddCircle.toCircle
      (finiteHamiltonianAddCirclePhase t energy i) : Circle) : ℂ) =
        finiteObserverHamiltonianVertexPhase t energy i
  have hcircle :=
    (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply
      (⟨finiteObserverHamiltonianVertexPhase t energy i,
        by
          simpa [Submonoid.unitSphere] using
            finiteObserverHamiltonianVertexPhase_norm t energy i⟩ : Circle)
  exact congrArg Subtype.val
    ((AddCircle.homeomorphCircle_apply one_ne_zero _).symm.trans hcircle)

/-- Normalized Choi state of a finite static Hamiltonian, written in its
spectral basis. -/
def staticSpectralChoiVector
    (d : ℕ) (t : ℝ) (energy : Fin d → ℝ) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  fullUniformPhaseChoiVector d
    (finiteHamiltonianAddCirclePhase t energy)

theorem staticSpectralChoiVector_norm
    {d : ℕ} (hd : 0 < d) (t : ℝ) (energy : Fin d → ℝ) :
    ‖staticSpectralChoiVector d t energy‖ = 1 :=
  fullUniformPhaseChoiVector_norm hd _

/-- The overlap with the initial Choi state is exactly the uniform spectral
survival amplitude. -/
theorem inner_staticSpectralChoiVector_zero
    {d : ℕ} (hd : 0 < d) (t : ℝ) (energy : Fin d → ℝ) :
    inner ℂ
        (staticSpectralChoiVector d 0 energy)
        (staticSpectralChoiVector d t energy) =
      finiteSpectralSurvivalAmplitude (uniformSurvivalWeight d)
        (finiteObserverHamiltonianVertexPhase t energy) := by
  rw [EuclideanSpace.inner_toLp_toLp]
  change
    (∑ ij : Fin d × Fin d,
      (if ij.1 = ij.2 then
          ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
            fourier 1
              (finiteHamiltonianAddCirclePhase t energy ij.1)
        else 0) *
      starRingEnd ℂ
        (if ij.1 = ij.2 then
            ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
              fourier 1
                (finiteHamiltonianAddCirclePhase 0 energy ij.1)
          else 0)) =
      finiteSpectralSurvivalAmplitude (uniformSurvivalWeight d)
        (finiteObserverHamiltonianVertexPhase t energy)
  rw [Fintype.sum_prod_type]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hdR)
  have hreal :
      (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ =
        (d : ℝ)⁻¹ := by
    field_simp [hsqrt]
    simpa [pow_two] using (Real.mul_self_sqrt hdR.le).symm
  have hcoef :
      (((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
          starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ))) =
        (((d : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [starRingEnd_apply, Complex.star_def, map_inv₀,
      Complex.conj_ofReal]
    exact_mod_cast hreal
  simp_rw [fourier_finiteHamiltonianAddCirclePhase]
  have hzero :
      ∀ i : Fin d,
        finiteObserverHamiltonianVertexPhase 0 energy i = 1 := by
    intro i
    simp [finiteObserverHamiltonianVertexPhase]
  simp_rw [hzero]
  simp only [map_one, mul_one]
  simp only [ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [finiteSpectralSurvivalAmplitude]
  simp only [uniformSurvivalWeight]
  push_cast
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show
    (((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
        finiteObserverHamiltonianVertexPhase t energy i) *
          starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ)) =
      ((((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
        starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ))) *
          finiteObserverHamiltonianVertexPhase t energy i) by ring,
    hcoef]

/-- Operational Choi trace distance squared is exactly uniform survival
loss. -/
theorem staticSpectralChoiTraceDistance_sq_eq_survivalDeviation
    {d : ℕ} (hd : 0 < d) (t : ℝ) (energy : Fin d → ℝ) :
    pureStateTraceDistance
        (staticSpectralChoiVector d 0 energy)
        (staticSpectralChoiVector d t energy) ^ 2 =
      finiteSpectralSurvivalDeviation (uniformSurvivalWeight d)
        (finiteObserverHamiltonianVertexPhase t energy) := by
  have hprob :
      finiteSpectralSurvivalProbability (uniformSurvivalWeight d)
          (finiteObserverHamiltonianVertexPhase t energy) ≤ 1 :=
    finiteSpectralSurvivalProbability_le_one
      (uniformSurvivalWeight d)
      (finiteObserverHamiltonianVertexPhase t energy)
      (uniformSurvivalWeight_nonneg (d := d))
      (uniformSurvivalWeight_sum hd)
      (finiteObserverHamiltonianVertexPhase_norm t energy)
  have hdeficit :
      0 ≤ 1 -
        ‖inner ℂ
          (staticSpectralChoiVector d 0 energy)
          (staticSpectralChoiVector d t energy)‖ ^ 2 := by
    rw [inner_staticSpectralChoiVector_zero hd]
    rw [← Complex.normSq_eq_norm_sq]
    exact sub_nonneg.mpr hprob
  rw [pureStateTraceDistance, Real.sq_sqrt hdeficit]
  rw [inner_staticSpectralChoiVector_zero hd,
    ← Complex.normSq_eq_norm_sq]
  exact
    (finiteSpectralSurvivalDeviation_eq_one_sub
      (uniformSurvivalWeight d)
      (finiteObserverHamiltonianVertexPhase t energy)
      (uniformSurvivalWeight_nonneg (d := d))
      (uniformSurvivalWeight_sum hd)
      (finiteObserverHamiltonianVertexPhase_norm t energy)).symm

/-- **Static Choi recurrence after an arbitrary delay.** For every finite
static Hamiltonian, tick duration, resolution parameter, and prescribed
discrete delay `M`, there is a recurrence strictly after `M` ticks and no
later than `(M+1)(Q+1)^(d-1)` ticks.  Its operational trace-distance squared
is at most `2(2π/(Q+1))²`.

No spectral nonresonance or randomness premise is used. -/
theorem exists_staticSpectralChoi_recurrence_after
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    (tick : ℝ) (Q M : ℕ) :
    ∃ n : ℕ,
      M < n ∧
      n ≤ (M + 1) * (Q + 1) ^ (d - 1) ∧
      pureStateTraceDistance
          (staticSpectralChoiVector d 0 energy)
          (staticSpectralChoiVector d ((n : ℝ) * tick) energy) ^ 2 ≤
        2 * (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 := by
  let scaledEnergy : Fin d → ℝ :=
    fun i ↦ (M + 1 : ℕ) * tick * energy i
  obtain ⟨q, hq0, hqQ, hreturn⟩ :=
    exists_uniformSurvival_rank_recurrence hd scaledEnergy Q
  let n : ℕ := (M + 1) * q
  have hnM : M < n := by
    calc
      M < M + 1 := Nat.lt_succ_self M
      _ = (M + 1) * 1 := by simp
      _ ≤ (M + 1) * q := Nat.mul_le_mul_left (M + 1) hq0
  have hnQ :
      n ≤ (M + 1) * (Q + 1) ^ (d - 1) :=
    Nat.mul_le_mul_left (M + 1) hqQ
  refine ⟨n, hnM, hnQ, ?_⟩
  rw [staticSpectralChoiTraceDistance_sq_eq_survivalDeviation hd]
  have hphase :
      finiteObserverHamiltonianVertexPhase ((n : ℝ) * tick) energy =
        finiteObserverHamiltonianVertexPhase (q : ℝ) scaledEnergy := by
    funext i
    unfold finiteObserverHamiltonianVertexPhase scaledEnergy n
    congr 1
    push_cast
    ring
  rw [hphase]
  exact hreturn

end RHTower
