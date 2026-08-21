/-
# Common deterministic times of positive-mass circuit hardness

The completed-time circuit bound is quenched: it says that a fixed generic Hamiltonian spends
almost no long-run time inside a circuit ball, but the times themselves depend on the Hamiltonian.
Averaging the quenched statement over the coefficient ensemble removes that dependence.  Fatou's
lemma and Tonelli's theorem turn a lower time-density valid on half the coefficient mass into a
lower bound `(1-η)/2` for the long-run average of the fixed-time hardness probability, and hence
for its upper limit; so a positive fraction of the ensemble is hard at an unbounded sequence of
common deterministic times.

The coefficient set on which the quenched bound holds is not known to be measurable -- it is cut
out by the spectral collision, a function of a chosen eigenbasis.  Only an outer bound on its
complement is available, and that is enough: the complement's measurable hull has mass at most one
half, so its own complement is a measurable subset of the good set carrying at least half the mass.

Main results:
* `exists_measurableSet_subset_of_measure_compl_le` — the measurable-hull selection.
* `hardCircuitEvent` — the jointly measurable coefficient-time hardness event.
* `exists_measurable_goodSet_quenched` — **`(5)`--`(6)`**: a measurable half-mass coefficient set
  on which the hardness event has quenched lower time density `1-η`.
* `half_mul_one_sub_le_liminf_quenchedWindowAverage_pauliEnsemble` — **`(8)`**.
* `half_mul_one_sub_le_liminf_restricted_pauliEnsemble` — **`(8a)`**.
* `le_limsup_quenchedFixedTimeProb_pauliEnsemble` — **`(9)`**.
-/
import GaloisForLFunctions.HTGeometry.JointHardEventMeasurability
import GaloisForLFunctions.HTGeometry.GaussianEnsembleCircuitDensity
import GaloisForLFunctions.HTGeometry.QuenchedFixedTimeTransfer
import GaloisForLFunctions.HTGeometry.ShellSimpleSpectrum

open MeasureTheory Filter Set Matrix
open scoped ENNReal Topology Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-! ## Measurable selection inside a set of large outer mass -/

section Selection

variable {Ω : Type*} [MeasurableSpace Ω] {γ : Measure Ω} [IsProbabilityMeasure γ]

/-- A set whose complement has outer measure at most `c` contains a measurable set of measure at
least `1-c`: take the complement of a measurable hull of the complement. -/
theorem exists_measurableSet_subset_of_measure_compl_le {G : Set Ω} {c : ℝ≥0∞}
    (h : γ Gᶜ ≤ c) :
    ∃ G' : Set Ω, MeasurableSet G' ∧ G' ⊆ G ∧ 1 - c ≤ γ G' := by
  refine ⟨(toMeasurable γ Gᶜ)ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · intro x hx
    by_contra hxG
    exact hx (subset_toMeasurable γ Gᶜ hxG)
  · rw [measure_compl (measurableSet_toMeasurable _ _) (measure_ne_top _ _), measure_toMeasurable,
      measure_univ]
    exact tsub_le_tsub_left h 1

/-- Intersecting with a conull set does not lose mass. -/
theorem le_measure_inter_of_ae_mem {G A : Set Ω} (hA : γ Aᶜ = 0) : γ G ≤ γ (G ∩ A) := by
  have hsub : G ⊆ (G ∩ A) ∪ Aᶜ := by
    intro x hx
    by_cases h : x ∈ A
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  calc γ G ≤ γ ((G ∩ A) ∪ Aᶜ) := measure_mono hsub
    _ ≤ γ (G ∩ A) + γ Aᶜ := measure_union_le _ _
    _ = γ (G ∩ A) := by rw [hA, add_zero]

end Selection

/-! ## The hardness event of the Pauli ensemble -/

variable {n q : ℕ}

/-- The event that the orbit of the seed state under the ensemble Hamiltonian with coefficient
vector `J` stays farther than `eps` from every dictionary target at time `t`. -/
def hardCircuitEvent {C : Type} (w : (Fin n → Option (Fin 3)) → ℝ)
    (psi : FiniteQubitConfiguration (Fin n) → ℂ) (eps : ℝ)
    (Z : C → (FiniteQubitConfiguration (Fin n) → ℂ)) :
    Set ((((Fin n → Option (Fin 3)) → ℝ)) × ℝ) :=
  {p | p.2 ∉ metricEasySet (pauliEnsemble w p.1) psi eps Z}

variable {C : Type} [Fintype C]

/-- **The hardness event is jointly measurable.** -/
theorem measurableSet_hardCircuitEvent (w : (Fin n → Option (Fin 3)) → ℝ)
    (psi : FiniteQubitConfiguration (Fin n) → ℂ) (eps : ℝ)
    (Z : C → (FiniteQubitConfiguration (Fin n) → ℂ)) :
    MeasurableSet (hardCircuitEvent w psi eps Z) :=
  measurableSet_hardPairEvent (pauliEnsemble w) (continuous_pauliEnsemble w) psi Z eps

theorem preimage_compl_hardCircuitEvent (w : (Fin n → Option (Fin 3)) → ℝ)
    (psi : FiniteQubitConfiguration (Fin n) → ℂ) (eps : ℝ)
    (Z : C → (FiniteQubitConfiguration (Fin n) → ℂ))
    (J : (Fin n → Option (Fin 3)) → ℝ) :
    Prod.mk J ⁻¹' (hardCircuitEvent w psi eps Z)ᶜ
      = metricEasySet (pauliEnsemble w J) psi eps Z := by
  ext t
  simp only [Set.mem_preimage, Set.mem_compl_iff, hardCircuitEvent, Set.mem_setOf_eq,
    not_not]

/-- The quenched time fraction of the easy times is a window probability of the capture set. -/
theorem quenchedTimeFraction_compl_le_windowProbability
    [Nonempty C] {w : (Fin n → Option (Fin 3)) → ℝ}
    {psi : FiniteQubitConfiguration (Fin n) → ℂ}
    (hpsi : finiteComplexInner psi psi = 1)
    {eps : ℝ} (heps : 0 ≤ eps)
    {Z : C → (FiniteQubitConfiguration (Fin n) → ℂ)}
    (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    (J : (Fin n → Option (Fin 3)) → ℝ) {T : ℝ} (hT : 0 < T) :
    quenchedTimeFraction (hardCircuitEvent w psi eps Z)ᶜ J T
      ≤ (windowProbabilityMeasure T : Measure ℝ)
          (physicalCaptureSet (pauliEnsemble w J) psi (1 - eps ^ 2) Z) := by
  have hsub : metricEasySet (pauliEnsemble w J) psi eps Z
      ⊆ physicalCaptureSet (pauliEnsemble w J) psi (1 - eps ^ 2) Z :=
    metricEasySet_subset_physicalCaptureSet
      (Matrix.isHermitian_iff_isSelfAdjoint.mp (isHermitian_pauliEnsemble w J)) hpsi heps hZ
  have hwin : ∀ S : Set ℝ, volume (S ∩ Ioc 0 T) / ENNReal.ofReal T
      = (windowProbabilityMeasure T : Measure ℝ) S := by
    intro S
    rw [windowProb_apply, windowLength, if_pos hT,
      Measure.restrict_apply' measurableSet_Ioc, ENNReal.div_eq_inv_mul]
  rw [← hwin]
  rw [quenchedTimeFraction, preimage_compl_hardCircuitEvent]
  exact ENNReal.div_le_div_right
    (measure_mono (Set.inter_subset_inter_left _ hsub)) _

/-! ## The half-mass coefficient set with a quenched density bound -/

/-- **`(5)`--`(6)`.**  There is a measurable set of coefficient vectors of Gaussian mass at least
one half on which the hardness event has quenched lower time density `1 - 2^{-r/2}`: the bounded,
collision-good set carries half the mass, and outside a null set every one of its members obeys the
completed-time circuit bound. -/
theorem exists_measurable_goodSet_quenched [Nonempty C]
    (w : (Fin n → Option (Fin 3)) → ℝ) (hq : 2 ≤ q)
    (hwsupp : SupportInvariantWeight w)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0)
    (hcard0 : 0 < Fintype.card (Fin n → Option (Fin 3)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : 2 * Real.log (8 * Fintype.card (Fin n → Option (Fin 3))) ≤ B ^ 2)
    (Z : C → (FiniteQubitConfiguration (Fin n) → ℂ))
    (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps1 : eps < 1)
    {r : ℕ} (hr : 1 ≤ r)
    (hscale : 16 * (4 * (2 / 3 : ℝ) ^ n) / (1 - eps ^ 2) ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    ∃ G : Set ((Fin n → Option (Fin 3)) → ℝ), MeasurableSet G ∧
      1 / 2 ≤ centredProductGaussian (Fin n → Option (Fin 3)) 1 G ∧
      ∀ J ∈ G, limsup (fun T => quenchedTimeFraction
          (hardCircuitEvent w (zeroProductState (Fin n)) eps Z)ᶜ J T) atTop
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2))) := by
  classical
  have hOmega : finiteComplexInner (zeroProductState (Fin n)) (zeroProductState (Fin n)) = 1 := by
    rw [finiteComplexInner_self_eq_sum_normSq, sum_normSq_zeroProductState]
    norm_num
  have ha : (0 : ℝ) < 1 - eps ^ 2 := by nlinarith
  have hae := ae_limsup_physicalCapture_le_of_gaussianGoodSet (q := q) w hq hw hwne
    (fun _ => false) Z hZ ha hr hscale hM hcard hs (B := B)
  obtain ⟨A, hAmem, hAmeas, hA⟩ := hae.exists_measurable_mem
  have hAnull : centredProductGaussian (Fin n → Option (Fin 3)) 1 Aᶜ = 0 := hAmem
  have hcomplreal := measureReal_gaussianGoodSet_compl_le (q := q) w hq hwsupp hw hwne hcard0 hB0 hB
  have hcompl : centredProductGaussian (Fin n → Option (Fin 3)) 1 ((gaussianGoodSet w B 4)ᶜ)
      ≤ 1 / 2 := by
    rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (by norm_num)]
    simpa [Measure.real] using hcomplreal
  obtain ⟨G₀, hG₀meas, hG₀sub, hG₀mass⟩ := exists_measurableSet_subset_of_measure_compl_le hcompl
  refine ⟨G₀ ∩ A, hG₀meas.inter hAmeas, ?_, ?_⟩
  · calc (1 : ℝ≥0∞) / 2 = 1 - 1 / 2 := (ENNReal.sub_half (by norm_num)).symm
      _ ≤ centredProductGaussian (Fin n → Option (Fin 3)) 1 G₀ := hG₀mass
      _ ≤ centredProductGaussian (Fin n → Option (Fin 3)) 1 (G₀ ∩ A) :=
          le_measure_inter_of_ae_mem hAnull
  · rintro J ⟨hJG₀, hJA⟩
    refine le_trans (limsup_le_limsup ?_) (hA J hJA (hG₀sub hJG₀))
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact quenchedTimeFraction_compl_le_windowProbability hOmega heps0 hZ J hT

end GaloisForLFunctions.HTGeometry

end
