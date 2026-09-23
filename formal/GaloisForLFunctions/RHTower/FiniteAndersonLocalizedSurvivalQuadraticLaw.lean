import GaloisForLFunctions.RHTower.FiniteQuantumObserverGraphRateDistortionLaw
import GaloisForLFunctions.RHTower.FiniteAndersonLocalizedSurvivalRecurrenceLaw
import GaloisForLFunctions.RHTower.FiniteQuantumSurvivalHistoryLaw
import GaloisForLFunctions.RHTower.ProjectiveWeightedCoherence

/-!
# Quadratic Anderson-localized survival recurrence

The density matrix of a finite pure spectral packet with Born weights `pᵢ`
has entries `sqrt(pᵢ)sqrt(pⱼ)`.  Its squared Hilbert--Schmidt displacement
is exactly twice the scalar survival-probability loss.  Applying the squared
observer-graph rate--distortion theorem to this matrix therefore replaces
the linear phase-resolution remainder in the earlier localized survival law
by a quadratic one, without changing the localization-volume exponent.

The Anderson statements below are deterministic transfers from explicit
spectral localization and shell-growth hypotheses.  They do not assert
localization for an arbitrary Hamiltonian ensemble.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Unit weight for the single weighted pure-state observer. -/
def finiteWeightedPureObserverWeight (_ : Unit) : ℝ := 1

/-- Density-matrix block of a pure state whose Born weights are `p`. -/
def finiteWeightedPureObserverBlock
    {d : ℕ} (p : Fin d → ℝ)
    (_ : Unit) (i j : Fin d) : ℂ :=
  ((Real.sqrt (p i) * Real.sqrt (p j) : ℝ) : ℂ)

/-- The weighted pure-state observer puts exactly mass `pᵢpⱼ` on the
directed pair `(i,j)`. -/
theorem finiteWeightedPureObserverUnionWeight
    {d : ℕ} (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i)
    (i j : Fin d) :
    finiteObserverUnionWeight finiteWeightedPureObserverWeight
        (finiteWeightedPureObserverBlock p) i j =
      p i * p j := by
  rw [finiteObserverUnionWeight]
  simp only [Finset.univ_unique, Finset.sum_singleton,
    finiteWeightedPureObserverWeight, finiteWeightedPureObserverBlock,
    one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
    mul_pow, Real.sq_sqrt (hp i), Real.sq_sqrt (hp j)]

/-- Observer selected mass agrees exactly with the scalar survival-history
selected coefficient mass. -/
theorem finiteWeightedPureObserver_selectedMass_eq
    {d : ℕ} (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i)
    (G : SimpleGraph (Fin d)) :
    finiteObserverSelectedDirectedWeightMass G
        finiteWeightedPureObserverWeight
        (finiteWeightedPureObserverBlock p) =
      finiteExpectationSelectedDirectedMass G
        (fun _ : Unit => 1)
        (finiteLocalizedSpectralCoefficient p) := by
  classical
  unfold finiteObserverSelectedDirectedWeightMass
    finiteExpectationSelectedDirectedMass
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hij : G.Adj i j
  · rw [if_pos hij, if_pos hij,
      finiteWeightedPureObserverUnionWeight p hp,
      finiteLocalizedSpectral_unionCoefficientMass_eq p hp]
  · rw [if_neg hij, if_neg hij]

/-- Observer omitted mass agrees exactly with the scalar survival-history
omitted coefficient mass. -/
theorem finiteWeightedPureObserver_omittedMass_eq
    {d : ℕ} (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i)
    (G : SimpleGraph (Fin d)) :
    finiteObserverOmittedDirectedWeightMass G
        finiteWeightedPureObserverWeight
        (finiteWeightedPureObserverBlock p) =
      finiteExpectationOmittedDirectedMass G
        (fun _ : Unit => 1)
        (finiteLocalizedSpectralCoefficient p) := by
  classical
  unfold finiteObserverOmittedDirectedWeightMass
    finiteExpectationOmittedDirectedMass
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hij : i ≠ j ∧ ¬ G.Adj i j
  · rw [if_pos hij, if_pos hij,
      finiteWeightedPureObserverUnionWeight p hp,
      finiteLocalizedSpectral_unionCoefficientMass_eq p hp]
  · rw [if_neg hij, if_neg hij]

/-- Weighted pure-state squared Hilbert--Schmidt displacement is the
weighted ordered pairwise phase energy. -/
theorem finiteWeightedPureObserver_distanceSq_eq_pairwiseEnergy
    {d : ℕ} (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i)
    (z : Fin d → ℂ) (hunit : ∀ i, ‖z i‖ = 1) :
    finiteQuantumObserverDistanceSq finiteWeightedPureObserverWeight z
        (finiteWeightedPureObserverBlock p) =
      projectiveWeightedPairwiseEnergy p z := by
  rw [finiteQuantumObserverDistanceSq_eq_phaseEnergy]
  unfold finiteQuantumObserverPhaseEnergy
    projectiveWeightedPairwiseEnergy
  simp_rw [finiteWeightedPureObserverUnionWeight p hp]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [finiteQuantumObserverPhase]
  have hrewrite :
      z i * star (z j) - 1 = (z i - z j) * star (z j) := by
    rw [sub_mul]
    have hj : z j * star (z j) = 1 := by
      change z j * (starRingEnd ℂ) (z j) = 1
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit j]
      norm_num
    rw [hj]
  rw [hrewrite, norm_mul, norm_star, hunit j, mul_one]

/--
**Exact scalar--matrix identity for arbitrary Born weights.**

For every normalized nonnegative finite spectral packet and every unit phase
packet, survival-probability loss is exactly half of the weighted pure-state
squared Hilbert--Schmidt displacement.
-/
theorem finiteSpectralSurvivalDeviation_eq_half_weightedPureObserverDistanceSq
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpSum : ∑ i, p i = 1)
    (z : Fin d → ℂ) (hunit : ∀ i, ‖z i‖ = 1) :
    finiteSpectralSurvivalDeviation p z =
      finiteQuantumObserverDistanceSq finiteWeightedPureObserverWeight z
        (finiteWeightedPureObserverBlock p) / 2 := by
  rw [finiteSpectralSurvivalDeviation_eq_one_sub p z hp hpSum hunit,
    finiteSpectralSurvivalProbability, Complex.normSq_eq_norm_sq,
    finiteWeightedPureObserver_distanceSq_eq_pairwiseEnergy
      p hp z hunit,
    projectiveWeightedPairwiseEnergy_eq_two_mul_fidelityDeficit
      p z hpSum hunit]
  simp only [finiteSpectralSurvivalAmplitude,
    projectiveWeightedPhaseAmplitude]
  ring

/-- Quadratic localized survival budget: linear tail loss plus quadratic
retained-phase resolution. -/
def finiteLocalizedSurvivalQuadraticBudget
    (α : ℝ) (Q : ℕ) : ℝ :=
  4 * α + 2 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ)

/--
**Quadratic finite localized-support survival recurrence.**

For arbitrary normalized nonnegative finite Born weights, a nonempty
retained subset `S`, and any certified tail bound `tail(p,S) ≤ α`, some
positive integer clock satisfies

`n ≤ (Q+1)^(|S|-1)`

and has survival loss at most

`4α + 2(2π/(Q+1))²`.
-/
theorem exists_finiteLocalizedSurvival_quadratic_recurrence
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpSum : ∑ i, p i = 1)
    (S : Finset (Fin d)) (hS : S.Nonempty)
    (α : ℝ) (htail : finiteLocalizedSubsetTail p S ≤ α)
    (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^ (S.card - 1) ∧
      finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) ≤
        finiteLocalizedSurvivalQuadraticBudget α Q := by
  obtain ⟨n, hn0, hnQ, hdistance⟩ :=
    exists_finiteQuantumObserver_graph_rateDistortion
      (finiteLocalizedSpectralSupportGraph S)
      finiteWeightedPureObserverWeight
      (finiteWeightedPureObserverBlock p)
      (by intro a; simp [finiteWeightedPureObserverWeight]) energy Q
  have hrank :
      d -
          Nat.card
            (finiteLocalizedSpectralSupportGraph S).ConnectedComponent =
        S.card - 1 := by
    simpa only [Fintype.card_fin] using
      finiteLocalizedSpectralSupportGraph_rank S hS
  rw [hrank] at hnQ
  refine ⟨n, hn0, hnQ, ?_⟩
  have homitted :
      finiteObserverOmittedDirectedWeightMass
          (finiteLocalizedSpectralSupportGraph S)
          finiteWeightedPureObserverWeight
          (finiteWeightedPureObserverBlock p) ≤
        2 * α := by
    rw [finiteWeightedPureObserver_omittedMass_eq p hp]
    exact finiteLocalizedSpectral_omittedMass_le_two_alpha
      p hp hpSum S α htail
  have hselected :
      finiteObserverSelectedDirectedWeightMass
          (finiteLocalizedSpectralSupportGraph S)
          finiteWeightedPureObserverWeight
          (finiteWeightedPureObserverBlock p) ≤
        1 := by
    rw [finiteWeightedPureObserver_selectedMass_eq p hp]
    exact finiteLocalizedSpectral_selectedMass_le_one p hp hpSum S
  rw [finiteSpectralSurvivalDeviation_eq_half_weightedPureObserverDistanceSq
    p hp hpSum
    (finiteObserverHamiltonianVertexPhase (n : ℝ) energy)
    (finiteObserverHamiltonianVertexPhase_norm (n : ℝ) energy)]
  let δ : ℝ := 2 * Real.pi / (Q + 1 : ℝ)
  calc
    finiteQuantumObserverDistanceSq finiteWeightedPureObserverWeight
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy)
          (finiteWeightedPureObserverBlock p) / 2 ≤
        (4 * finiteObserverOmittedDirectedWeightMass
            (finiteLocalizedSpectralSupportGraph S)
            finiteWeightedPureObserverWeight
            (finiteWeightedPureObserverBlock p) +
          4 * δ ^ (2 : ℕ) *
            finiteObserverSelectedDirectedWeightMass
              (finiteLocalizedSpectralSupportGraph S)
              finiteWeightedPureObserverWeight
              (finiteWeightedPureObserverBlock p)) / 2 := by
      exact div_le_div_of_nonneg_right hdistance (by norm_num)
    _ ≤ (4 * (2 * α) + 4 * δ ^ (2 : ℕ) * 1) / 2 := by
      apply div_le_div_of_nonneg_right
      · exact add_le_add
          (mul_le_mul_of_nonneg_left homitted (by norm_num))
          (mul_le_mul_of_nonneg_left hselected
            (mul_nonneg (by norm_num) (sq_nonneg δ)))
      · norm_num
    _ = finiteLocalizedSurvivalQuadraticBudget α Q := by
      unfold finiteLocalizedSurvivalQuadraticBudget
      dsimp only [δ]
      ring

/-- Intrinsic quadratic recurrence using the exact probability tail. -/
theorem exists_finiteLocalizedSurvival_quadratic_recurrence_exactTail
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpSum : ∑ i, p i = 1)
    (S : Finset (Fin d)) (hS : S.Nonempty)
    (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^ (S.card - 1) ∧
      finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) ≤
        4 * finiteLocalizedSubsetTail p S +
          2 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) := by
  simpa only [finiteLocalizedSurvivalQuadraticBudget] using
    exists_finiteLocalizedSurvival_quadratic_recurrence
      p hp hpSum S hS (finiteLocalizedSubsetTail p S) le_rfl energy Q

/--
**Quadratic localized survival escape--return law.**

At the same quadratic budget, survival either never exits at nonnegative
time or an exit is followed strictly later by a certified return with the
same `|S|-1` exponent.
-/
theorem finiteLocalizedSurvival_quadratic_neverExits_or_postExit_return
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpSum : ∑ i, p i = 1)
    (S : Finset (Fin d)) (hS : S.Nonempty)
    (α : ℝ) (htail : finiteLocalizedSubsetTail p S ≤ α)
    (energy : Fin d → ℝ) (Q : ℕ)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase t energy) ≤
        finiteLocalizedSurvivalQuadraticBudget α Q) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧
      n ≤ (Q + 1) ^ (S.card - 1) ∧
      finiteLocalizedSurvivalQuadraticBudget α Q <
        finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase exitTime energy) ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (((Q + 1) ^ (S.card - 1) : ℕ) : ℝ) *
          (exitTime + guardTime) ∧
      finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase
            ((n : ℝ) * (exitTime + guardTime)) energy) ≤
        finiteLocalizedSurvivalQuadraticBudget α Q := by
  classical
  by_cases hnever :
      ∀ t : ℝ, 0 ≤ t →
        finiteSpectralSurvivalDeviation p
            (finiteObserverHamiltonianVertexPhase t energy) ≤
          finiteLocalizedSurvivalQuadraticBudget α Q
  · exact Or.inl hnever
  · right
    push Not at hnever
    obtain ⟨exitTime, hexitTime, hexit⟩ := hnever
    let tick : ℝ := exitTime + guardTime
    have htick0 : 0 < tick := by
      dsimp only [tick]
      linarith
    obtain ⟨n, hn0, hnQ, hreturn⟩ :=
      exists_finiteLocalizedSurvival_quadratic_recurrence
        p hp hpSum S hS α htail
        (fun i => tick * energy i) Q
    have hnOne : 1 ≤ n :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn0)
    have hpost : exitTime < (n : ℝ) * tick := by
      calc
        exitTime < tick := by
          dsimp only [tick]
          linarith
        _ = (1 : ℝ) * tick := by ring
        _ ≤ (n : ℝ) * tick := by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast hnOne) htick0.le
    have hdeadline :
        (n : ℝ) * tick ≤
          (((Q + 1) ^ (S.card - 1) : ℕ) : ℝ) * tick :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast hnQ) htick0.le
    have hreturnPhysical :
        finiteSpectralSurvivalDeviation p
            (finiteObserverHamiltonianVertexPhase
              ((n : ℝ) * tick) energy) ≤
          finiteLocalizedSurvivalQuadraticBudget α Q := by
      rw [← finiteObserverHamiltonianVertexPhase_scaledEnergy]
      exact hreturn
    exact
      ⟨exitTime, n, hexitTime, hn0, hnQ, hexit,
        by simpa only [tick] using hpost,
        by simpa only [tick] using hdeadline,
        by simpa only [tick] using hreturnPhysical⟩

/--
**Quadratic Anderson localization-volume survival recurrence.**

Explicit exponential localization and shell growth convert the exact tail
into a geometric tail, while retained phase resolution stays quadratic.
-/
theorem exists_finiteAndersonLocalizedSurvival_quadratic_recurrence
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpSum : ∑ i, p i = 1)
    (radius : Fin d → ℕ) (R : ℕ)
    (hBall : (finiteLocalizationBall radius R).Nonempty)
    (C μ A B : ℝ)
    (hC : 0 ≤ C) (hμ : 0 < μ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcontract : B * Real.exp (-2 * μ) < 1)
    (hdecay :
      ∀ i, p i ≤ C * Real.exp (-2 * μ * (radius i : ℝ)))
    (hshell :
      ∀ m,
        ((finiteLocalizationShell radius m).card : ℝ) ≤ A * B ^ m)
    (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        ((finiteLocalizationBall radius R).card - 1) ∧
      finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) ≤
        4 * finiteLocalizationGeometricTailBound C μ A B R +
          2 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) := by
  have htail :
      finiteLocalizedSubsetTail p (finiteLocalizationBall radius R) ≤
        finiteLocalizationGeometricTailBound C μ A B R := by
    rw [finiteLocalizedSubsetTail_localizationBall_eq]
    exact finiteLocalizedSpectralTail_le_shellExponential
      p radius R C μ A B hC hμ hA hB hcontract hdecay hshell
  simpa only [finiteLocalizedSurvivalQuadraticBudget] using
    exists_finiteLocalizedSurvival_quadratic_recurrence
      p hp hpSum (finiteLocalizationBall radius R) hBall
      (finiteLocalizationGeometricTailBound C μ A B R) htail
      energy Q

/--
**Quadratic Anderson-localized survival escape--return law.**

Under the same explicit localization hypotheses, local survival either
never exits the quadratic localization budget or an exit is followed
strictly later by a return with localization-ball exponent.
-/
theorem
    finiteAndersonLocalizedSurvival_quadratic_neverExits_or_postExit_return
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpSum : ∑ i, p i = 1)
    (radius : Fin d → ℕ) (R : ℕ)
    (hBall : (finiteLocalizationBall radius R).Nonempty)
    (C μ A B : ℝ)
    (hC : 0 ≤ C) (hμ : 0 < μ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcontract : B * Real.exp (-2 * μ) < 1)
    (hdecay :
      ∀ i, p i ≤ C * Real.exp (-2 * μ * (radius i : ℝ)))
    (hshell :
      ∀ m,
        ((finiteLocalizationShell radius m).card : ℝ) ≤ A * B ^ m)
    (energy : Fin d → ℝ) (Q : ℕ)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase t energy) ≤
        4 * finiteLocalizationGeometricTailBound C μ A B R +
          2 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ)) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧
      n ≤ (Q + 1) ^
        ((finiteLocalizationBall radius R).card - 1) ∧
      4 * finiteLocalizationGeometricTailBound C μ A B R +
          2 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) <
        finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase exitTime energy) ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (((Q + 1) ^
          ((finiteLocalizationBall radius R).card - 1) : ℕ) : ℝ) *
            (exitTime + guardTime) ∧
      finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase
            ((n : ℝ) * (exitTime + guardTime)) energy) ≤
        4 * finiteLocalizationGeometricTailBound C μ A B R +
          2 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) := by
  have htail :
      finiteLocalizedSubsetTail p (finiteLocalizationBall radius R) ≤
        finiteLocalizationGeometricTailBound C μ A B R := by
    rw [finiteLocalizedSubsetTail_localizationBall_eq]
    exact finiteLocalizedSpectralTail_le_shellExponential
      p radius R C μ A B hC hμ hA hB hcontract hdecay hshell
  simpa only [finiteLocalizedSurvivalQuadraticBudget] using
    finiteLocalizedSurvival_quadratic_neverExits_or_postExit_return
      p hp hpSum (finiteLocalizationBall radius R) hBall
      (finiteLocalizationGeometricTailBound C μ A B R) htail
      energy Q guardTime hguard

/-- Volume-growth form of the quadratic Anderson-localized recurrence law. -/
theorem exists_finiteAndersonLocalizedSurvival_quadratic_volume_recurrence
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpSum : ∑ i, p i = 1)
    (radius : Fin d → ℕ) (R Veff : ℕ)
    (hBall : (finiteLocalizationBall radius R).Nonempty)
    (hvolume : (finiteLocalizationBall radius R).card ≤ Veff)
    (C μ A B : ℝ)
    (hC : 0 ≤ C) (hμ : 0 < μ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcontract : B * Real.exp (-2 * μ) < 1)
    (hdecay :
      ∀ i, p i ≤ C * Real.exp (-2 * μ * (radius i : ℝ)))
    (hshell :
      ∀ m,
        ((finiteLocalizationShell radius m).card : ℝ) ≤ A * B ^ m)
    (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^ (Veff - 1) ∧
      finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) ≤
        4 * finiteLocalizationGeometricTailBound C μ A B R +
          2 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) := by
  obtain ⟨n, hn0, hnBall, hdev⟩ :=
    exists_finiteAndersonLocalizedSurvival_quadratic_recurrence
      p hp hpSum radius R hBall C μ A B hC hμ hA hB
      hcontract hdecay hshell energy Q
  refine ⟨n, hn0, hnBall.trans ?_, hdev⟩
  exact Nat.pow_le_pow_right (by omega)
    (Nat.sub_le_sub_right hvolume 1)

private theorem finiteAndersonQuadratic_two_pow_sub_one_add_one (N : ℕ) :
    (2 ^ N - 1) + 1 = 2 ^ N :=
  Nat.sub_add_cancel (Nat.one_le_pow N 2 (by norm_num))

/--
**Quadratic Anderson resolution-scale law.**

At spatial scale `N`, phase resolution `Q=2^N-1`, and localization-ball
growth `|B_N| ≤ V(N+1)^ν`, one positive clock satisfies

`n ≤ 2^(N(V(N+1)^ν-1))`

with survival deviation at most

`4 geometricTail(C,μ,A,B,N) + 2(2π/2^N)²`.
-/
theorem exists_finiteAndersonLocalizedSurvival_quadratic_resolutionScale_recurrence
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpSum : ∑ i, p i = 1)
    (radius : Fin d → ℕ) (N ν V : ℕ)
    (hBall : (finiteLocalizationBall radius N).Nonempty)
    (hvolume :
      (finiteLocalizationBall radius N).card ≤
        V * (N + 1) ^ ν)
    (C μ A B : ℝ)
    (hC : 0 ≤ C) (hμ : 0 < μ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcontract : B * Real.exp (-2 * μ) < 1)
    (hdecay :
      ∀ i, p i ≤ C * Real.exp (-2 * μ * (radius i : ℝ)))
    (hshell :
      ∀ m,
        ((finiteLocalizationShell radius m).card : ℝ) ≤ A * B ^ m)
    (energy : Fin d → ℝ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ 2 ^ (N * (V * (N + 1) ^ ν - 1)) ∧
      finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) ≤
        4 * finiteLocalizationGeometricTailBound C μ A B N +
          2 * (2 * Real.pi / (2 : ℝ) ^ N) ^ (2 : ℕ) := by
  obtain ⟨n, hn0, hnQ, hdev⟩ :=
    exists_finiteAndersonLocalizedSurvival_quadratic_volume_recurrence
      p hp hpSum radius N (V * (N + 1) ^ ν)
      hBall hvolume C μ A B hC hμ hA hB
      hcontract hdecay hshell energy (2 ^ N - 1)
  rw [finiteAndersonQuadratic_two_pow_sub_one_add_one N] at hnQ
  have hnDeadline :
      n ≤ 2 ^ (N * (V * (N + 1) ^ ν - 1)) := by
    simpa only [pow_mul] using hnQ
  refine ⟨n, hn0, hnDeadline, ?_⟩
  have hbaseReal :
      (((2 ^ N - 1 : ℕ) : ℝ) + 1) =
        ((2 ^ N : ℕ) : ℝ) := by
    exact_mod_cast finiteAndersonQuadratic_two_pow_sub_one_add_one N
  rw [hbaseReal] at hdev
  have hcastPow :
      ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by
    norm_num
  rwa [hcastPow] at hdev

/--
**Quadratic Anderson resolution-scale escape--return law.**

At binary phase resolution `Q=2^N-1`, local survival either never exits
the quadratic resolution-scale budget or an exit is followed strictly later
by a return.  Both the sampled clock and its physical-time realization obey
the volume-growth deadline `2^(N(V(N+1)^ν-1))`.
-/
theorem
    finiteAndersonLocalizedSurvival_quadratic_resolutionScale_neverExits_or_postExit_return
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpSum : ∑ i, p i = 1)
    (radius : Fin d → ℕ) (N ν V : ℕ)
    (hBall : (finiteLocalizationBall radius N).Nonempty)
    (hvolume :
      (finiteLocalizationBall radius N).card ≤
        V * (N + 1) ^ ν)
    (C μ A B : ℝ)
    (hC : 0 ≤ C) (hμ : 0 < μ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcontract : B * Real.exp (-2 * μ) < 1)
    (hdecay :
      ∀ i, p i ≤ C * Real.exp (-2 * μ * (radius i : ℝ)))
    (hshell :
      ∀ m,
        ((finiteLocalizationShell radius m).card : ℝ) ≤ A * B ^ m)
    (energy : Fin d → ℝ)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase t energy) ≤
        4 * finiteLocalizationGeometricTailBound C μ A B N +
          2 * (2 * Real.pi / (2 : ℝ) ^ N) ^ (2 : ℕ)) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧
      n ≤ 2 ^ (N * (V * (N + 1) ^ ν - 1)) ∧
      4 * finiteLocalizationGeometricTailBound C μ A B N +
          2 * (2 * Real.pi / (2 : ℝ) ^ N) ^ (2 : ℕ) <
        finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase exitTime energy) ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        ((2 ^ (N * (V * (N + 1) ^ ν - 1)) : ℕ) : ℝ) *
          (exitTime + guardTime) ∧
      finiteSpectralSurvivalDeviation p
          (finiteObserverHamiltonianVertexPhase
            ((n : ℝ) * (exitTime + guardTime)) energy) ≤
        4 * finiteLocalizationGeometricTailBound C μ A B N +
          2 * (2 * Real.pi / (2 : ℝ) ^ N) ^ (2 : ℕ) := by
  have hbaseReal :
      (((2 ^ N - 1 : ℕ) : ℝ) + 1) =
        ((2 ^ N : ℕ) : ℝ) := by
    exact_mod_cast finiteAndersonQuadratic_two_pow_sub_one_add_one N
  have hcastPow :
      ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by
    norm_num
  rcases
      finiteAndersonLocalizedSurvival_quadratic_neverExits_or_postExit_return
        p hp hpSum radius N hBall C μ A B hC hμ hA hB
        hcontract hdecay hshell energy (2 ^ N - 1)
        guardTime hguard with
    hnever | ⟨exitTime, n, hexitTime, hn0, hnBall, hexit,
      hpost, _hphysicalBall, hreturn⟩
  · left
    intro t ht
    have h := hnever t ht
    rwa [hbaseReal, hcastPow] at h
  · right
    rw [finiteAndersonQuadratic_two_pow_sub_one_add_one N] at hnBall
    have hnVolume :
        n ≤ (2 ^ N) ^ (V * (N + 1) ^ ν - 1) :=
      hnBall.trans
        (Nat.pow_le_pow_right (Nat.pow_pos (by norm_num))
          (Nat.sub_le_sub_right hvolume 1))
    have hnDeadline :
        n ≤ 2 ^ (N * (V * (N + 1) ^ ν - 1)) := by
      simpa only [pow_mul] using hnVolume
    have htick0 : 0 < exitTime + guardTime := by
      linarith
    have hphysical :
        (n : ℝ) * (exitTime + guardTime) ≤
          ((2 ^ (N * (V * (N + 1) ^ ν - 1)) : ℕ) : ℝ) *
            (exitTime + guardTime) :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast hnDeadline) htick0.le
    rw [hbaseReal, hcastPow] at hexit hreturn
    exact
      ⟨exitTime, n, hexitTime, hn0, hnDeadline, hexit,
        hpost, hphysical, hreturn⟩

end RHTower
