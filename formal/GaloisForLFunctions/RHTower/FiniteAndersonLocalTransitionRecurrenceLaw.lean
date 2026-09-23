import GaloisForLFunctions.RHTower.FiniteAndersonLocalizedSurvivalRecurrenceLaw

/-!
# Anderson-local transition recurrence

This module extends localization-volume recurrence from survival probability
to site-to-site transition probability. Complex spectral transition
amplitudes are handled through their cancellation-resistant absolute mass.
The theorem is deterministic: a concrete Anderson model must separately
supply the eigensystem localization and shell-growth estimates.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

def finiteSpectralTransitionCoefficient
    {d : ℕ} (amplitude : Fin d → ℂ)
    (_ : Unit) (i j : Fin d) : ℂ :=
  amplitude i * starRingEnd ℂ (amplitude j)

def finiteEigenvectorTransitionAmplitude
    {X : Type*} {d : ℕ}
    (eigenvector : X → Fin d → ℂ)
    (source detector : X) (k : Fin d) : ℂ :=
  starRingEnd ℂ (eigenvector detector k) *
    eigenvector source k

def finiteSpectralTransitionMass
    {d : ℕ} (amplitude : Fin d → ℂ) : ℝ :=
  ∑ i, ‖amplitude i‖

def finiteSpectralTransitionTail
    {d : ℕ} (amplitude : Fin d → ℂ)
    (S : Finset (Fin d)) : ℝ :=
  ∑ i, if i ∈ S then 0 else ‖amplitude i‖

theorem finiteSpectralTransitionTail_localizationBall_eq
    {d : ℕ} (amplitude : Fin d → ℂ)
    (radius : Fin d → ℕ) (R : ℕ) :
    finiteSpectralTransitionTail amplitude
        (finiteLocalizationBall radius R) =
      finiteLocalizedSpectralTail
        (fun k => ‖amplitude k‖) radius R := by
  classical
  unfold finiteSpectralTransitionTail finiteLocalizationBall
    finiteLocalizedSpectralTail
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : radius i ≤ R
  · simp [h]
  · have hR : R < radius i := by omega
    simp [h, hR]

def finiteSpectralTransitionDeviation
    {d : ℕ} (amplitude : Fin d → ℂ)
    (z : Fin d → ℂ) : ℝ :=
  finiteQuantumExpectationTotalDeviation
    (fun _ : Unit => 1) z
    (finiteSpectralTransitionCoefficient amplitude)

def finiteSpectralTransitionProbability
    {d : ℕ} (amplitude : Fin d → ℂ)
    (z : Fin d → ℂ) : ℝ :=
  Complex.normSq (∑ i, amplitude i * z i)

def finiteSpectralTransitionRecurrenceBudget
    (totalMass tailBound : ℝ) (Q : ℕ) : ℝ :=
  4 * totalMass * tailBound +
    2 * (2 * Real.pi / (Q + 1 : ℝ)) * totalMass ^ (2 : ℕ)

theorem finiteSpectralTransition_history_eq_probability
    {d : ℕ} (amplitude z : Fin d → ℂ) :
    (∑ i, ∑ j,
      finiteSpectralTransitionCoefficient amplitude () i j *
        finiteQuantumObserverPhase z i j) =
      (finiteSpectralTransitionProbability amplitude z : ℂ) := by
  classical
  unfold finiteSpectralTransitionCoefficient
    finiteQuantumObserverPhase
    finiteSpectralTransitionProbability
  rw [Complex.normSq_eq_conj_mul_self, map_sum]
  simp_rw [map_mul]
  calc
    (∑ i, ∑ j,
      amplitude i * starRingEnd ℂ (amplitude j) *
        (z i * starRingEnd ℂ (z j))) =
        (∑ i, amplitude i * z i) *
          (∑ j,
            starRingEnd ℂ (amplitude j) *
              starRingEnd ℂ (z j)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = (∑ i,
          starRingEnd ℂ (amplitude i) *
            starRingEnd ℂ (z i)) *
        (∑ i, amplitude i * z i) := by
          ring

theorem finiteQuantumExpectationDisplacement_transitionCoefficient
    {d : ℕ} (amplitude z : Fin d → ℂ) :
    finiteQuantumExpectationDisplacement z
        (finiteSpectralTransitionCoefficient amplitude) () =
      (finiteSpectralTransitionProbability amplitude z : ℂ) -
        (finiteSpectralTransitionProbability amplitude
          (fun _ => 1) : ℂ) := by
  classical
  unfold finiteQuantumExpectationDisplacement
  simp_rw [mul_sub]
  simp_rw [Finset.sum_sub_distrib]
  apply congrArg₂ (· - ·)
  · exact finiteSpectralTransition_history_eq_probability amplitude z
  · simp only [mul_one]
    simpa [finiteQuantumObserverPhase] using
      (finiteSpectralTransition_history_eq_probability
        amplitude (fun _ => 1))

theorem finiteSpectralTransitionDeviation_eq_abs_probability_sub
    {d : ℕ} (amplitude z : Fin d → ℂ) :
    finiteSpectralTransitionDeviation amplitude z =
      |finiteSpectralTransitionProbability amplitude z -
        finiteSpectralTransitionProbability amplitude (fun _ => 1)| := by
  rw [finiteSpectralTransitionDeviation,
    finiteQuantumExpectationTotalDeviation]
  simp only [Finset.univ_unique, Finset.sum_singleton,
    one_mul]
  rw [finiteQuantumExpectationDisplacement_transitionCoefficient]
  rw [← Complex.ofReal_sub]
  change
    ‖((finiteSpectralTransitionProbability amplitude z -
      finiteSpectralTransitionProbability amplitude (fun _ => 1) :
        ℝ) : ℂ)‖ =
      |finiteSpectralTransitionProbability amplitude z -
        finiteSpectralTransitionProbability amplitude (fun _ => 1)|
  rw [Complex.norm_real, Real.norm_eq_abs]

theorem finiteSpectralTransition_unionCoefficientMass_eq
    {d : ℕ} (amplitude : Fin d → ℂ) (i j : Fin d) :
    finiteExpectationUnionCoefficientMass
        (fun _ : Unit => 1)
        (finiteSpectralTransitionCoefficient amplitude) i j =
      ‖amplitude i‖ * ‖amplitude j‖ := by
  simp [finiteExpectationUnionCoefficientMass,
    finiteSpectralTransitionCoefficient]

theorem finiteEigenvectorTransitionMass_le_one
    {X : Type*} {d : ℕ}
    (eigenvector : X → Fin d → ℂ)
    (source detector : X)
    (hsource :
      ∑ k, ‖eigenvector source k‖ ^ (2 : ℕ) = 1)
    (hdetector :
      ∑ k, ‖eigenvector detector k‖ ^ (2 : ℕ) = 1) :
    finiteSpectralTransitionMass
        (finiteEigenvectorTransitionAmplitude
          eigenvector source detector) ≤ 1 := by
  unfold finiteSpectralTransitionMass
    finiteEigenvectorTransitionAmplitude
  calc
    (∑ k,
      ‖starRingEnd ℂ (eigenvector detector k) *
        eigenvector source k‖) =
        ∑ k,
          ‖eigenvector detector k‖ *
            ‖eigenvector source k‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul]
      simp
    _ ≤
      Real.sqrt (∑ k, ‖eigenvector detector k‖ ^ (2 : ℕ)) *
        Real.sqrt (∑ k, ‖eigenvector source k‖ ^ (2 : ℕ)) := by
      exact Real.sum_mul_le_sqrt_mul_sqrt
        Finset.univ
        (fun k => ‖eigenvector detector k‖)
        (fun k => ‖eigenvector source k‖)
    _ = 1 := by
      rw [hsource, hdetector]
      norm_num

theorem finiteSpectralTransition_selectedMass_le_sq
    {d : ℕ} (amplitude : Fin d → ℂ)
    (S : Finset (Fin d)) :
    finiteExpectationSelectedDirectedMass
        (finiteLocalizedSpectralSupportGraph S)
        (fun _ : Unit => 1)
        (finiteSpectralTransitionCoefficient amplitude) ≤
      finiteSpectralTransitionMass amplitude ^ (2 : ℕ) := by
  classical
  unfold finiteExpectationSelectedDirectedMass
  calc
    (∑ i, ∑ j,
      if (finiteLocalizedSpectralSupportGraph S).Adj i j
      then finiteExpectationUnionCoefficientMass
        (fun _ : Unit => 1)
        (finiteSpectralTransitionCoefficient amplitude) i j
      else 0) ≤
        ∑ i, ∑ j, ‖amplitude i‖ * ‖amplitude j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hadj :
          (finiteLocalizedSpectralSupportGraph S).Adj i j
      · simp [hadj,
          finiteSpectralTransition_unionCoefficientMass_eq]
      · simp [hadj, mul_nonneg (norm_nonneg _) (norm_nonneg _)]
    _ = (∑ i, ‖amplitude i‖) * (∑ j, ‖amplitude j‖) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = finiteSpectralTransitionMass amplitude ^ (2 : ℕ) := by
      unfold finiteSpectralTransitionMass
      ring

theorem finiteSpectralTransition_omittedMass_le_two_mul
    {d : ℕ} (amplitude : Fin d → ℂ)
    (S : Finset (Fin d)) :
    finiteExpectationOmittedDirectedMass
        (finiteLocalizedSpectralSupportGraph S)
        (fun _ : Unit => 1)
        (finiteSpectralTransitionCoefficient amplitude) ≤
      2 * finiteSpectralTransitionMass amplitude *
        finiteSpectralTransitionTail amplitude S := by
  classical
  let p : Fin d → ℝ := fun i => ‖amplitude i‖
  let q : Fin d → ℝ := fun i => if i ∈ S then 0 else p i
  unfold finiteExpectationOmittedDirectedMass
  calc
    (∑ i, ∑ j,
      if i ≠ j ∧
          ¬ (finiteLocalizedSpectralSupportGraph S).Adj i j
      then finiteExpectationUnionCoefficientMass
        (fun _ : Unit => 1)
        (finiteSpectralTransitionCoefficient amplitude) i j
      else 0) ≤
        ∑ i, ∑ j, (q i * p j + p i * q j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases homit :
          i ≠ j ∧
            ¬ (finiteLocalizedSpectralSupportGraph S).Adj i j
      · rw [if_pos homit,
          finiteSpectralTransition_unionCoefficientMass_eq]
        by_cases hiS : i ∈ S
        · have hjS : j ∉ S := by
            intro hjS
            exact homit.2 ⟨homit.1, hiS, hjS⟩
          simp [p, q, hiS, hjS]
        · by_cases hjS : j ∈ S
          · simp [p, q, hiS, hjS]
          · simp [p, q, hiS, hjS,
              mul_nonneg (norm_nonneg _) (norm_nonneg _)]
      · rw [if_neg homit]
        have hqi : 0 ≤ q i := by
          simp only [q]
          split_ifs
          · exact le_rfl
          · exact norm_nonneg _
        have hqj : 0 ≤ q j := by
          simp only [q]
          split_ifs
          · exact le_rfl
          · exact norm_nonneg _
        exact add_nonneg
          (mul_nonneg hqi (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) hqj)
    _ = (∑ i, q i) * (∑ j, p j) +
          (∑ i, p i) * (∑ j, q j) := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · calc
          (∑ i, ∑ j, q i * p j) =
              ∑ i, q i * (∑ j, p j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
          _ = (∑ i, q i) * (∑ j, p j) := by
            rw [Finset.sum_mul]
      · calc
          (∑ i, ∑ j, p i * q j) =
              ∑ i, p i * (∑ j, q j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
          _ = (∑ i, p i) * (∑ j, q j) := by
            rw [Finset.sum_mul]
    _ = 2 * finiteSpectralTransitionMass amplitude *
          finiteSpectralTransitionTail amplitude S := by
      simp only [p, q, finiteSpectralTransitionMass,
        finiteSpectralTransitionTail]
      ring

theorem exists_finiteSpectralTransition_recurrence
    {d : ℕ} (amplitude : Fin d → ℂ)
    (S : Finset (Fin d)) (hS : S.Nonempty)
    (tailBound : ℝ)
    (htail :
      finiteSpectralTransitionTail amplitude S ≤ tailBound)
    (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^ (S.card - 1) ∧
      finiteSpectralTransitionDeviation amplitude
          (finiteObserverHamiltonianVertexPhase
            (n : ℝ) energy) ≤
        finiteSpectralTransitionRecurrenceBudget
          (finiteSpectralTransitionMass amplitude)
          tailBound Q := by
  obtain ⟨n, hn0, hnQ, hdist⟩ :=
    exists_finiteQuantumExpectation_graph_rateDistortion
      (finiteLocalizedSpectralSupportGraph S)
      (fun _ : Unit => 1)
      (finiteSpectralTransitionCoefficient amplitude)
      (by intro a; norm_num) energy Q
  have hrank :
      d -
          Nat.card
            (finiteLocalizedSpectralSupportGraph S).ConnectedComponent =
        S.card - 1 := by
    simpa only [Fintype.card_fin] using
      finiteLocalizedSpectralSupportGraph_rank S hS
  rw [hrank] at hnQ
  refine ⟨n, hn0, hnQ, ?_⟩
  have hmassNonneg :
      0 ≤ finiteSpectralTransitionMass amplitude := by
    unfold finiteSpectralTransitionMass
    exact Finset.sum_nonneg fun i hi => norm_nonneg _
  have homit :
      finiteExpectationOmittedDirectedMass
          (finiteLocalizedSpectralSupportGraph S)
          (fun _ : Unit => 1)
          (finiteSpectralTransitionCoefficient amplitude) ≤
        2 * finiteSpectralTransitionMass amplitude * tailBound := by
    exact
      (finiteSpectralTransition_omittedMass_le_two_mul
        amplitude S).trans
        (mul_le_mul_of_nonneg_left htail
          (mul_nonneg (by norm_num) hmassNonneg))
  have hselected :
      finiteExpectationSelectedDirectedMass
          (finiteLocalizedSpectralSupportGraph S)
          (fun _ : Unit => 1)
          (finiteSpectralTransitionCoefficient amplitude) ≤
        finiteSpectralTransitionMass amplitude ^ (2 : ℕ) :=
    finiteSpectralTransition_selectedMass_le_sq amplitude S
  unfold finiteSpectralTransitionDeviation
  calc
    finiteQuantumExpectationTotalDeviation
        (fun _ : Unit => 1)
        (finiteObserverHamiltonianVertexPhase (n : ℝ) energy)
        (finiteSpectralTransitionCoefficient amplitude) ≤
      2 * finiteExpectationOmittedDirectedMass
          (finiteLocalizedSpectralSupportGraph S)
          (fun _ : Unit => 1)
          (finiteSpectralTransitionCoefficient amplitude) +
        2 * (2 * Real.pi / (Q + 1 : ℝ)) *
          finiteExpectationSelectedDirectedMass
            (finiteLocalizedSpectralSupportGraph S)
            (fun _ : Unit => 1)
            (finiteSpectralTransitionCoefficient amplitude) :=
      hdist
    _ ≤
      2 * (2 * finiteSpectralTransitionMass amplitude * tailBound) +
        2 * (2 * Real.pi / (Q + 1 : ℝ)) *
          finiteSpectralTransitionMass amplitude ^ (2 : ℕ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left homit (by norm_num))
        (mul_le_mul_of_nonneg_left hselected (by positivity))
    _ = finiteSpectralTransitionRecurrenceBudget
          (finiteSpectralTransitionMass amplitude)
          tailBound Q := by
      unfold finiteSpectralTransitionRecurrenceBudget
      ring

/--
Every prescribed exit of a finite spectral transition record is followed
strictly later by a sampled return.  The physical return time is bounded by
the projective finite-head clock multiplied by the prescribed exit-plus-guard
sampling tick.
-/
theorem exists_finiteSpectralTransition_postExit_recurrence
    {d : ℕ} (amplitude : Fin d → ℂ)
    (S : Finset (Fin d)) (hS : S.Nonempty)
    (tailBound : ℝ)
    (htail :
      finiteSpectralTransitionTail amplitude S ≤ tailBound)
    (energy : Fin d → ℝ) (Q : ℕ)
    (exitTime guardTime : ℝ)
    (hexitTime : 0 ≤ exitTime) (hguard : 0 < guardTime)
    (hexit :
      finiteSpectralTransitionRecurrenceBudget
          (finiteSpectralTransitionMass amplitude)
          tailBound Q <
        finiteSpectralTransitionDeviation amplitude
          (finiteObserverHamiltonianVertexPhase
            exitTime energy)) :
    ∃ n : ℕ,
      0 < n ∧
      n ≤ (Q + 1) ^ (S.card - 1) ∧
      finiteSpectralTransitionRecurrenceBudget
          (finiteSpectralTransitionMass amplitude)
          tailBound Q <
        finiteSpectralTransitionDeviation amplitude
          (finiteObserverHamiltonianVertexPhase
            exitTime energy) ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (((Q + 1) ^ (S.card - 1) : ℕ) : ℝ) *
          (exitTime + guardTime) ∧
      finiteSpectralTransitionDeviation amplitude
          (finiteObserverHamiltonianVertexPhase
            ((n : ℝ) * (exitTime + guardTime)) energy) ≤
        finiteSpectralTransitionRecurrenceBudget
          (finiteSpectralTransitionMass amplitude)
          tailBound Q := by
  let tick : ℝ := exitTime + guardTime
  have htick0 : 0 < tick := by
    dsimp only [tick]
    linarith
  obtain ⟨n, hn0, hnQ, hreturn⟩ :=
    exists_finiteSpectralTransition_recurrence
      amplitude S hS tailBound htail
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
      finiteSpectralTransitionDeviation amplitude
          (finiteObserverHamiltonianVertexPhase
            ((n : ℝ) * tick) energy) ≤
        finiteSpectralTransitionRecurrenceBudget
          (finiteSpectralTransitionMass amplitude)
          tailBound Q := by
    rw [← finiteObserverHamiltonianVertexPhase_scaledEnergy]
    exact hreturn
  exact
    ⟨n, hn0, hnQ, hexit,
      by simpa only [tick] using hpost,
      by simpa only [tick] using hdeadline,
      by simpa only [tick] using hreturnPhysical⟩

theorem finiteSpectralTransition_neverExits_or_postExit_return
    {d : ℕ} (amplitude : Fin d → ℂ)
    (S : Finset (Fin d)) (hS : S.Nonempty)
    (tailBound : ℝ)
    (htail :
      finiteSpectralTransitionTail amplitude S ≤ tailBound)
    (energy : Fin d → ℝ) (Q : ℕ)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      finiteSpectralTransitionDeviation amplitude
          (finiteObserverHamiltonianVertexPhase t energy) ≤
        finiteSpectralTransitionRecurrenceBudget
          (finiteSpectralTransitionMass amplitude)
          tailBound Q) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧
      n ≤ (Q + 1) ^ (S.card - 1) ∧
      finiteSpectralTransitionRecurrenceBudget
          (finiteSpectralTransitionMass amplitude)
          tailBound Q <
        finiteSpectralTransitionDeviation amplitude
          (finiteObserverHamiltonianVertexPhase
            exitTime energy) ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (((Q + 1) ^ (S.card - 1) : ℕ) : ℝ) *
          (exitTime + guardTime) ∧
      finiteSpectralTransitionDeviation amplitude
          (finiteObserverHamiltonianVertexPhase
            ((n : ℝ) * (exitTime + guardTime)) energy) ≤
        finiteSpectralTransitionRecurrenceBudget
          (finiteSpectralTransitionMass amplitude)
          tailBound Q := by
  classical
  by_cases hnever :
      ∀ t : ℝ, 0 ≤ t →
        finiteSpectralTransitionDeviation amplitude
            (finiteObserverHamiltonianVertexPhase t energy) ≤
          finiteSpectralTransitionRecurrenceBudget
            (finiteSpectralTransitionMass amplitude)
            tailBound Q
  · exact Or.inl hnever
  · right
    push Not at hnever
    obtain ⟨exitTime, hexitTime, hexit⟩ := hnever
    obtain
      ⟨n, hn0, hnQ, _hexit, hpost, hdeadline, hreturn⟩ :=
      exists_finiteSpectralTransition_postExit_recurrence
        amplitude S hS tailBound htail energy Q
        exitTime guardTime hexitTime hguard hexit
    exact
      ⟨exitTime, n, hexitTime, hn0, hnQ, hexit,
        hpost, hdeadline, hreturn⟩

theorem exists_finiteAndersonLocalTransition_recurrence
    {d : ℕ} (amplitude : Fin d → ℂ)
    (radius : Fin d → ℕ) (R : ℕ)
    (hball : (finiteLocalizationBall radius R).Nonempty)
    (C μ A B : ℝ)
    (hC : 0 ≤ C) (hμ : 0 < μ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcontract : B * Real.exp (-2 * μ) < 1)
    (hdecay :
      ∀ k,
        ‖amplitude k‖ ≤
          C * Real.exp (-2 * μ * (radius k : ℝ)))
    (hshell :
      ∀ m,
        ((finiteLocalizationShell radius m).card : ℝ) ≤
          A * B ^ m)
    (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        ((finiteLocalizationBall radius R).card - 1) ∧
      finiteSpectralTransitionDeviation amplitude
          (finiteObserverHamiltonianVertexPhase
            (n : ℝ) energy) ≤
        finiteSpectralTransitionRecurrenceBudget
          (finiteSpectralTransitionMass amplitude)
          (finiteLocalizationGeometricTailBound
            C μ A B R) Q := by
  apply exists_finiteSpectralTransition_recurrence
    amplitude (finiteLocalizationBall radius R) hball
    (finiteLocalizationGeometricTailBound C μ A B R)
  rw [finiteSpectralTransitionTail_localizationBall_eq]
  exact finiteLocalizedSpectralTail_le_shellExponential
    (fun k => ‖amplitude k‖) radius R C μ A B
    hC hμ hA hB hcontract hdecay hshell

theorem finiteAndersonLocalTransition_neverExits_or_postExit_return
    {d : ℕ} (amplitude : Fin d → ℂ)
    (radius : Fin d → ℕ) (R : ℕ)
    (hball : (finiteLocalizationBall radius R).Nonempty)
    (C μ A B : ℝ)
    (hC : 0 ≤ C) (hμ : 0 < μ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcontract : B * Real.exp (-2 * μ) < 1)
    (hdecay :
      ∀ k,
        ‖amplitude k‖ ≤
          C * Real.exp (-2 * μ * (radius k : ℝ)))
    (hshell :
      ∀ m,
        ((finiteLocalizationShell radius m).card : ℝ) ≤
          A * B ^ m)
    (energy : Fin d → ℝ) (Q : ℕ)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      finiteSpectralTransitionDeviation amplitude
          (finiteObserverHamiltonianVertexPhase t energy) ≤
        finiteSpectralTransitionRecurrenceBudget
          (finiteSpectralTransitionMass amplitude)
          (finiteLocalizationGeometricTailBound
            C μ A B R) Q) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧
      n ≤ (Q + 1) ^
        ((finiteLocalizationBall radius R).card - 1) ∧
      finiteSpectralTransitionRecurrenceBudget
          (finiteSpectralTransitionMass amplitude)
          (finiteLocalizationGeometricTailBound
            C μ A B R) Q <
        finiteSpectralTransitionDeviation amplitude
          (finiteObserverHamiltonianVertexPhase exitTime energy) ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (((Q + 1) ^
          ((finiteLocalizationBall radius R).card - 1) : ℕ) : ℝ) *
            (exitTime + guardTime) ∧
      finiteSpectralTransitionDeviation amplitude
          (finiteObserverHamiltonianVertexPhase
            ((n : ℝ) * (exitTime + guardTime)) energy) ≤
        finiteSpectralTransitionRecurrenceBudget
          (finiteSpectralTransitionMass amplitude)
          (finiteLocalizationGeometricTailBound
            C μ A B R) Q := by
  apply finiteSpectralTransition_neverExits_or_postExit_return
    amplitude (finiteLocalizationBall radius R) hball
    (finiteLocalizationGeometricTailBound C μ A B R)
  · rw [finiteSpectralTransitionTail_localizationBall_eq]
    exact finiteLocalizedSpectralTail_le_shellExponential
      (fun k => ‖amplitude k‖) radius R C μ A B
      hC hμ hA hB hcontract hdecay hshell
  · exact hguard

end RHTower
