import GaloisForLFunctions.HTGeometry.CyclicPhaseContinuum
import GaloisForLFunctions.RHTower.StaticChoiSubunitWeightedCrowdingLaw

/-!
# A continuous cyclic static-Choi plateau and exact return

This module transfers the off-grid cyclic phase theorem to arbitrary finite dictionaries of Choi
targets.  Target-dependent diagonal mass is allowed to vanish or vary; the dimension-linear
variance ceiling is enough.  The resulting single static spectrum avoids every target throughout
the full return-excised continuum and returns exactly at the period endpoint.
-/

open scoped BigOperators ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Static spectrum whose one-period Choi orbit is the selected cyclic-frequency phase curve. -/
def cyclicStaticChoiEnergy {d : ℕ} (p : ℕ) (q : Fin d → Fin p) (i : Fin d) : ℝ :=
  -(2 * Real.pi * (q i).val / p)

/-- Complex coefficient of an arbitrary Choi target against the cyclic diagonal orbit. -/
def directCyclicChoiTargetWeight
    (d : ℕ) (target : EuclideanSpace ℂ (Fin d × Fin d)) (i : Fin d) : ℂ :=
  (directStaticChoiTargetWeight d target i : ℂ) * directStaticChoiTargetTwist target i

lemma norm_directCyclicChoiTargetWeight
    {d : ℕ} (target : EuclideanSpace ℂ (Fin d × Fin d)) (i : Fin d) :
    ‖directCyclicChoiTargetWeight d target i‖ =
      directStaticChoiTargetWeight d target i := by
  rw [directCyclicChoiTargetWeight, norm_mul, norm_directStaticChoiTargetTwist,
    mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (directStaticChoiTargetWeight_nonneg target i)]

lemma sum_norm_directCyclicChoiTargetWeight_le_one_of_norm_le_one
    {d : ℕ} (hd : 0 < d) {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ ≤ 1) :
    ∑ i, ‖directCyclicChoiTargetWeight d target i‖ ≤ 1 := by
  simpa only [norm_directCyclicChoiTargetWeight] using
    sum_directStaticChoiTargetWeight_le_one_of_norm_le_one hd htarget

lemma sum_nnreal_sq_directCyclicChoiTargetWeight_le_inv_of_norm_le_one
    {d : ℕ} (hd : 0 < d) {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ ≤ 1) :
    (↑(∑ i, ‖directCyclicChoiTargetWeight d target i‖₊ ^ 2) : ℝ) ≤
      (d : ℝ)⁻¹ := by
  simpa only [NNReal.coe_sum, NNReal.coe_pow, coe_nnnorm,
    norm_directCyclicChoiTargetWeight] using
      sum_sq_directStaticChoiTargetWeight_le_inv_of_norm_le_one hd htarget

lemma inner_cyclicStaticChoiVector_target_eq_cyclicOverlap
    {d p : ℕ} (q : Fin d → Fin p) (t : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    inner ℂ (staticSpectralChoiVector d t (cyclicStaticChoiEnergy p q)) target =
      ∑ i, directCyclicChoiTargetWeight d target i * cyclicPhaseValue p t (q i) := by
  rw [inner_staticSpectralChoiVector_target_eq_directTwistedAmplitude]
  unfold twistedFiniteSpectralAmplitude directCyclicChoiTargetWeight
  apply Finset.sum_congr rfl
  intro i _hi
  rw [cyclicPhaseValue_eq_exp]
  congr 1
  unfold cyclicStaticChoiEnergy
  congr 1
  push_cast
  ring

lemma finiteObserverHamiltonianVertexPhase_cyclic_period
    {d p : ℕ} (hp : 0 < p) (q : Fin d → Fin p) (i : Fin d) :
    finiteObserverHamiltonianVertexPhase p (cyclicStaticChoiEnergy p q) i = 1 := by
  unfold finiteObserverHamiltonianVertexPhase cyclicStaticChoiEnergy
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have harg : Complex.I * (((p : ℝ) * (-(2 * Real.pi * (q i).val / p)) : ℝ) : ℂ) =
      -((q i).val : ℕ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [harg]
  rw [show -((q i).val : ℕ) * (2 * Real.pi * Complex.I) =
      (q i).val * (-(2 * Real.pi * Complex.I)) by ring]
  rw [Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, one_pow]

/-- The cyclic static Choi orbit returns exactly after one full period. -/
theorem cyclicStaticChoiVector_period_return
    {d p : ℕ} (hp : 0 < p) (q : Fin d → Fin p) :
    staticSpectralChoiVector d p (cyclicStaticChoiEnergy p q) =
      staticSpectralChoiVector d 0 (cyclicStaticChoiEnergy p q) := by
  ext ij
  simp only [staticSpectralChoiVector, fullUniformPhaseChoiVector_apply]
  split_ifs
  · rw [fourier_finiteHamiltonianAddCirclePhase,
      fourier_finiteHamiltonianAddCirclePhase,
      finiteObserverHamiltonianVertexPhase_cyclic_period hp]
    simp [finiteObserverHamiltonianVertexPhase]
  · rfl

variable {Y : Type*} [Fintype Y]

/-- One cyclic static Hamiltonian Choi orbit avoids a complete finite target dictionary throughout
the return-excised continuum, with dimension-linear exponent. -/
theorem exists_cyclicStaticChoi_continuous_returnExcised_avoid
    (d p : ℕ) (hd : 0 < d) (hp8 : 8 ≤ p)
    (target : Y → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ y, ‖target y‖ ≤ 1)
    (hbudget : ((256 * (p - 8) + 1 : ℕ) : ℝ) * Fintype.card Y *
        (4 * Real.exp (-((3 / 4 : ℝ) - 1 / 8) ^ 2 /
          (16 * (d : ℝ)⁻¹))) < 1) :
    ∃ q : Fin d → Fin p, ∀ t ∈ Set.Icc (4 : ℝ) ((p : ℝ) - 4), ∀ y,
      ‖inner ℂ (staticSpectralChoiVector d t (cyclicStaticChoiEnergy p q)) (target y)‖ <
        4 / 5 := by
  have henergy : 0 < (d : ℝ)⁻¹ := by positivity
  obtain ⟨q, hq⟩ := exists_cyclicFrequencies_continuous_returnExcised_avoid
    (I := Fin d) p hp8 (fun y => directCyclicChoiTargetWeight d (target y))
      henergy
      (fun y => sum_nnreal_sq_directCyclicChoiTargetWeight_le_inv_of_norm_le_one
        hd (htarget y))
      (fun y => sum_norm_directCyclicChoiTargetWeight_le_one_of_norm_le_one
        hd (htarget y)) hbudget
  refine ⟨q, ?_⟩
  intro t ht y
  rw [inner_cyclicStaticChoiVector_target_eq_cyclicOverlap]
  exact hq t ht y

/-- Growth--plateau--return form: one static spectrum avoids the whole target dictionary over the
continuous return-excised period and returns exactly at its period endpoint. -/
theorem exists_cyclicStaticChoi_continuous_plateau_and_exact_return
    (d p : ℕ) (hd : 0 < d) (hp8 : 8 ≤ p)
    (target : Y → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ y, ‖target y‖ ≤ 1)
    (hbudget : ((256 * (p - 8) + 1 : ℕ) : ℝ) * Fintype.card Y *
        (4 * Real.exp (-((3 / 4 : ℝ) - 1 / 8) ^ 2 /
          (16 * (d : ℝ)⁻¹))) < 1) :
    ∃ q : Fin d → Fin p,
      (∀ t ∈ Set.Icc (4 : ℝ) ((p : ℝ) - 4), ∀ y,
        ‖inner ℂ (staticSpectralChoiVector d t (cyclicStaticChoiEnergy p q)) (target y)‖ <
          4 / 5) ∧
      staticSpectralChoiVector d p (cyclicStaticChoiEnergy p q) =
        staticSpectralChoiVector d 0 (cyclicStaticChoiEnergy p q) := by
  obtain ⟨q, hq⟩ := exists_cyclicStaticChoi_continuous_returnExcised_avoid
    d p hd hp8 target htarget hbudget
  exact ⟨q, hq, cyclicStaticChoiVector_period_return (by omega) q⟩

/-- Operational form of the plateau: normalized targets remain at pure-state trace distance
strictly greater than `3/5` throughout the return-excised continuum. -/
theorem exists_cyclicStaticChoi_traceDistance_plateau_and_exact_return
    (d p : ℕ) (hd : 0 < d) (hp8 : 8 ≤ p)
    (target : Y → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ y, ‖target y‖ = 1)
    (hbudget : ((256 * (p - 8) + 1 : ℕ) : ℝ) * Fintype.card Y *
        (4 * Real.exp (-((3 / 4 : ℝ) - 1 / 8) ^ 2 /
          (16 * (d : ℝ)⁻¹))) < 1) :
    ∃ q : Fin d → Fin p,
      (∀ t ∈ Set.Icc (4 : ℝ) ((p : ℝ) - 4), ∀ y,
        3 / 5 < pureStateTraceDistance
          (staticSpectralChoiVector d t (cyclicStaticChoiEnergy p q)) (target y)) ∧
      staticSpectralChoiVector d p (cyclicStaticChoiEnergy p q) =
        staticSpectralChoiVector d 0 (cyclicStaticChoiEnergy p q) := by
  obtain ⟨q, havoid, hreturn⟩ :=
    exists_cyclicStaticChoi_continuous_plateau_and_exact_return
      d p hd hp8 target (fun y => (htarget y).le) hbudget
  refine ⟨q, ?_, hreturn⟩
  intro t ht y
  have hoverlap := havoid t ht y
  by_contra hdist
  have hdist' : pureStateTraceDistance
      (staticSpectralChoiVector d t (cyclicStaticChoiEnergy p q)) (target y) ≤ 3 / 5 :=
    le_of_not_gt hdist
  have hge := norm_inner_ge_sqrt_one_sub_sq_of_traceDistance_le
    (staticSpectralChoiVector d t (cyclicStaticChoiEnergy p q)) (target y)
      (staticSpectralChoiVector_norm hd _ _) (htarget y)
      (epsilon := (3 / 5 : ℝ)) (by norm_num) (by norm_num) hdist'
  norm_num at hge
  linarith

/-- **Complete finite-gate circuit union.**  Fixed-length identity-padded words encode every circuit
of length at most `s`; hence the exact circuit entropy loss is `|gate|^(s+1)`.  One cyclic static
spectrum avoids all such circuit targets over the continuous plateau and returns exactly at `p`. -/
theorem exists_cyclicStaticChoi_paddedCircuit_plateau_and_exact_return
    {gate : Type*} [Fintype gate] (d p s : ℕ) (hd : 0 < d) (hp8 : 8 ≤ p)
    (target : PaddedCircuitWord gate s → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ ≤ 1)
    (hbudget : ((256 * (p - 8) + 1 : ℕ) : ℝ) *
        (Fintype.card gate : ℝ) ^ (s + 1) *
        (4 * Real.exp (-((3 / 4 : ℝ) - 1 / 8) ^ 2 /
          (16 * (d : ℝ)⁻¹))) < 1) :
    ∃ q : Fin d → Fin p,
      (∀ t ∈ Set.Icc (4 : ℝ) ((p : ℝ) - 4), ∀ w,
        ‖inner ℂ (staticSpectralChoiVector d t (cyclicStaticChoiEnergy p q)) (target w)‖ <
          4 / 5) ∧
      staticSpectralChoiVector d p (cyclicStaticChoiEnergy p q) =
        staticSpectralChoiVector d 0 (cyclicStaticChoiEnergy p q) := by
  apply exists_cyclicStaticChoi_continuous_plateau_and_exact_return
    d p hd hp8 target htarget
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using hbudget

end RHTower
