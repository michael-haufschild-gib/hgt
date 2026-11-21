import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliThresholdObstruction
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PairedRows

/-!
# Finite probability of the Pauli claw certificate

The six entries in a two-row claw certificate are independent standard
Gaussians. Disjoint two-row blocks therefore give an exact failure
probability for the certificate and an upper bound on line-graph models
in the sense of Projansky et al. (arXiv:2611.26315) for every support
containing the large coefficients.
-/

open MeasureTheory ProbabilityTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The two-row coordinates used by the claw and its distinguishing terms. -/
def clawBlockLabels : Finset PathPauliBlockLabel :=
  {(0, .inr (2, 2)), (1, .inr (0, 0)), (0, .inl 0), (1, .inl 0),
    (0, .inl 2), (1, .inr (0, 2))}

theorem card_clawBlockLabels : clawBlockLabels.card = 6 := by
  simp [clawBlockLabels, Finset.card_insert_of_notMem]

private def absoluteTail (cutoff : ℝ) : Set ℝ := {x | cutoff < |x|}

/-- The probability of a standard Gaussian coefficient surviving the cutoff. -/
def gaussianAbsoluteTailMass (cutoff : ℝ) : ENNReal := gaussianReal 0 1 (absoluteTail cutoff)

theorem gaussianAbsoluteTailMass_pos (cutoff : ℝ) : 0 < gaussianAbsoluteTailMass cutoff := by
  apply lt_of_lt_of_le (gaussianReal_Icc_pos (show cutoff + 1 < cutoff + 2 by linarith))
  apply measure_mono
  intro x hx
  exact (show cutoff < cutoff + 1 by linarith).trans_le (hx.1.trans (le_abs_self _))

private theorem measurableSet_absoluteTail (cutoff : ℝ) : MeasurableSet (absoluteTail cutoff) :=
  measurableSet_lt measurable_const measurable_id.abs

/-- The six certificate coordinates all survive the prescribed cutoff. -/
def clawBlockEvent (cutoff : ℝ) : Set (PathPauliBlockLabel → ℝ) :=
  (↑clawBlockLabels : Set PathPauliBlockLabel).pi (fun _ => absoluteTail cutoff)

theorem measurableSet_clawBlockEvent (cutoff : ℝ) : MeasurableSet (clawBlockEvent cutoff) :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_absoluteTail cutoff)

/-- Exact mass of a certificate in a single block. -/
theorem gaussian_measure_clawBlockEvent (cutoff : ℝ) :
    (Measure.infinitePi fun _ : PathPauliBlockLabel => gaussianReal 0 1) (clawBlockEvent cutoff) =
      gaussianAbsoluteTailMass cutoff ^ 6 := by
  rw [clawBlockEvent, Measure.infinitePi_pi _ (fun _ _ => measurableSet_absoluteTail cutoff),
    Finset.prod_const, card_clawBlockLabels, gaussianAbsoluteTailMass]

/-- The event that none of the first m disjoint blocks gives the certificate. -/
def noClawBlockEvent (cutoff : ℝ) (m : ℕ) : Set PathPauliDisorder :=
  pathPauliBlock ⁻¹' ((↑(Finset.range m) : Set ℕ).pi (fun _ => (clawBlockEvent cutoff)ᶜ))

/-- Exact failure probability for the six-coordinate test on m blocks. -/
theorem gaussian_measure_noClawBlockEvent (cutoff : ℝ) (m : ℕ) :
    pathPauliDisorderLaw (noClawBlockEvent cutoff m) =
      (1 - gaussianAbsoluteTailMass cutoff ^ 6) ^ m := by
  let μ : Measure (PathPauliBlockLabel → ℝ) := Measure.infinitePi fun _ => gaussianReal 0 1
  letI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  let T := (clawBlockEvent cutoff)ᶜ
  have hT : MeasurableSet T := (measurableSet_clawBlockEvent cutoff).compl
  have hm : MeasurePreserving pathPauliBlock pathPauliDisorderLaw
      (Measure.infinitePi fun _ : ℕ => μ) := measurePreserving_paired_rows _
  have hmeas : MeasurableSet ((↑(Finset.range m) : Set ℕ).pi (fun _ => T)) :=
    MeasurableSet.pi (Set.to_countable _) (fun _ _ => hT)
  change pathPauliDisorderLaw (pathPauliBlock ⁻¹' ((↑(Finset.range m) : Set ℕ).pi (fun _ => T))) = _
  rw [← Measure.map_apply hm.measurable hmeas, hm.map_eq,
    Measure.infinitePi_pi _ (fun _ _ => hT), Finset.prod_const, Finset.card_range]
  have hmass : μ T = 1 - gaussianAbsoluteTailMass cutoff ^ 6 := by
    rw [show T = (clawBlockEvent cutoff)ᶜ from rfl,
      measure_compl (measurableSet_clawBlockEvent cutoff) (measure_ne_top _ _), measure_univ]
    exact congrArg (1 - ·) (gaussian_measure_clawBlockEvent cutoff)
  rw [hmass]

/-- A certificate inside the prefix obstructs every twin line model of
any support that retains all above-cutoff coefficients. -/
theorem path_no_twinLineModel_of_clawBlock {ρ : Type*} [DecidableEq ρ]
    (ω : PathPauliDisorder) (n j : ℕ) (hj : 2 * j + 1 < n + 1) (cutoff : ℝ)
    (hblock : pathPauliBlock ω j ∈ clawBlockEvent cutoff) (S : Set (PathLabel n))
    (hS : ∀ l, cutoff < |pathPauliDisorderShell ω n l| → l ∈ S) :
    IsEmpty (TwinLineModel (pathFrustrationAdj S) ρ) := by
  let e : Fin (n + 1) := ⟨2 * j, by omega⟩
  let f : Fin (n + 1) := ⟨2 * j + 1, hj⟩
  have hef : e.succ = f.castSucc := Fin.ext rfl
  have hl (i : PathPauliBlockLabel) (hi : i ∈ clawBlockLabels) :
      cutoff < |pathPauliBlock ω j i| := hblock _ hi
  exact path_no_twinLineModel_of_adjacent_rows S e f hef
    (hS _ (hl (0, .inr (2, 2)) (by simp [clawBlockLabels])))
    (hS _ (hl (1, .inr (0, 0)) (by simp [clawBlockLabels])))
    (hS _ (hl (0, .inl 0) (by simp [clawBlockLabels])))
    (hS _ (hl (1, .inl 0) (by simp [clawBlockLabels])))
    (hS _ (hl (0, .inl 2) (by simp [clawBlockLabels])))
    (hS _ (hl (1, .inr (0, 2)) (by simp [clawBlockLabels])))

/-- Uniform finite-prefix bound over retained supports. The event of
an admissible line model is contained in the measurable certificate failure event. -/
theorem gaussian_measure_exists_twinLineModel_le {ρ : Type*} [DecidableEq ρ]
    (n : ℕ) (cutoff : ℝ) :
    pathPauliDisorderLaw {ω | ∃ S : Set (PathLabel n),
      (∀ l, cutoff < |pathPauliDisorderShell ω n l| → l ∈ S) ∧
        Nonempty (TwinLineModel (pathFrustrationAdj S) ρ)} ≤
      (1 - gaussianAbsoluteTailMass cutoff ^ 6) ^ ((n + 1) / 2) := by
  rw [← gaussian_measure_noClawBlockEvent]
  apply measure_mono
  rintro ω ⟨S, hS, ⟨M⟩⟩
  change ∀ j ∈ Finset.range ((n + 1) / 2), pathPauliBlock ω j ∉ clawBlockEvent cutoff
  intro j hj hblock
  have h := Finset.mem_range.mp hj
  exact (path_no_twinLineModel_of_clawBlock ω n j (by omega) cutoff hblock S hS).false M

#print axioms gaussian_measure_clawBlockEvent
#print axioms gaussian_measure_noClawBlockEvent
#print axioms gaussian_measure_exists_twinLineModel_le

end

end GaloisForLFunctions.HTGeometry
