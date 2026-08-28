import GaloisForLFunctions.RHTower.FiniteQuantumObserverGraphExtremalityLaw
import GaloisForLFunctions.RHTower.NearestNeighborFullProjectiveSameDrawLaw

/-!
# One static local Hamiltonian for complexity growth and every observer recurrence law

The exact onsite-plus-nearest-neighbour path family has a positive-measure laboratory complexity-
growth event.  Its exceptional set for the simultaneous finite-observer first-return law is null.
Deleting that null set therefore leaves one fixed time-independent bounded-degree Hamiltonian that
obeys both conclusions.

The same coefficient vector defines every occurrence of the Hamiltonian below.  Locality,
self-adjointness, simple spectrum, and the all-observer recurrence exponent are all explicit
conclusions rather than premises.
-/

open Set MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace RHTower

noncomputable section

/-- Failure of the simultaneous universal observer law is null on the full simple-spectrum locus
of the exact nearest-neighbour path family. -/
theorem volume_nearestNeighborPath_not_hasUniversalObserverLaw_eq_zero (k : ℕ) :
    volume {p ∈ simpleEnsembleLocus
        (nearestNeighborPathFinGenerator_isHermitian (k + 2)) |
      ¬ HasUniversalFiniteObserverFirstReturnLaw
        (sortedEnsembleSpectrum
          (nearestNeighborPathFinGenerator_isHermitian (k + 2)) p)} = 0 := by
  letI : NeZero (nearestNeighborPathLocalParameterCount (k + 2)) :=
    ⟨(nearestNeighborPathLocalParameterCount_pos k).ne'⟩
  have hae := ae_hasUniversalFiniteObserverFirstReturnLaw_simpleLocus
    (nearestNeighborPathFinGenerator_isHermitian (k + 2))
    (nearestNeighborPathFinGenerator_spectrumEscapesRealRelations k)
  rw [MeasureTheory.ae_iff] at hae
  simpa only [Classical.not_imp] using hae

/-- **Static local same-Hamiltonian capstone.**  Every admissible laboratory window contains one
fixed time-independent nearest-neighbour path Hamiltonian that lies in the literal local
submodule, is self-adjoint with simple spectrum, obeys the certified complexity-growth event, and
simultaneously has exact first-return exponent `(r - 1) / 2` for every finite observer of visible
phase capacity `r`. -/
theorem exists_nearestNeighborPath_sameDraw_growth_universalObserverLaw
    {k : ℕ} {T epsilon rho : ℝ}
    (hT : 0 ≤ T) (hepsilon : 0 < epsilon)
    (hepsilonMax : epsilon ≤ 1 / 200) (hrho : 0 < rho)
    (hscale : T * (rho * nearestNeighborPathLocalGeneratorMass (k + 2)) ≤ epsilon) :
    ∃ p : Fin (nearestNeighborPathLocalParameterCount (k + 2)) → ℝ,
      p ∈ nearestNeighborPathGaussianGrowthMaximalEvent (k + 2) T epsilon ∧
      p ∈ simpleEnsembleLocus
        (nearestNeighborPathFinGenerator_isHermitian (k + 2)) ∧
      IsSelfAdjoint (nearestNeighborPathLocalHamiltonian (k + 2) p) ∧
      nearestNeighborPathLocalHamiltonian (k + 2) p ∈
        nearestNeighborPathLocalSubmodule (k + 2) ∧
      spectralEnsembleMatrix (nearestNeighborPathFinGenerator (k + 2)) p =
        Matrix.reindex (nearestNeighborPathFinEquiv (k + 2))
          (nearestNeighborPathFinEquiv (k + 2))
          (nearestNeighborPathLocalHamiltonian (k + 2) p) ∧
      HasUniversalFiniteObserverFirstReturnLaw
        (sortedEnsembleSpectrum
          (nearestNeighborPathFinGenerator_isHermitian (k + 2)) p) := by
  let mu := centredProductGaussian
    (Fin (nearestNeighborPathLocalParameterCount (k + 2))) 1
  let bad := {p ∈ simpleEnsembleLocus
      (nearestNeighborPathFinGenerator_isHermitian (k + 2)) |
    ¬ HasUniversalFiniteObserverFirstReturnLaw
      (sortedEnsembleSpectrum
        (nearestNeighborPathFinGenerator_isHermitian (k + 2)) p)}
  have hbadVolume : (volume : Measure
      (Fin (nearestNeighborPathLocalParameterCount (k + 2)) → ℝ)) bad = 0 := by
    simpa only [bad] using
      volume_nearestNeighborPath_not_hasUniversalObserverLaw_eq_zero k
  have hbad : mu bad = 0 := by
    apply (productGaussian_absolutelyContinuous
      (nearestNeighborPathLocalParameterCount (k + 2)) one_ne_zero
      (fun _ => 0))
    exact hbadVolume
  have hgrowth : 0 < mu
      (nearestNeighborPathGaussianGrowthMaximalEvent (k + 2) T epsilon) :=
    measure_nearestNeighborPathGaussianGrowthMaximalEvent_pos
      (by omega) hT hepsilon hepsilonMax hrho hscale
  have hdiff : mu
      (nearestNeighborPathGaussianGrowthMaximalEvent (k + 2) T epsilon \ bad) =
      mu (nearestNeighborPathGaussianGrowthMaximalEvent (k + 2) T epsilon) :=
    measure_sdiff_null hbad
  have hdiffNe : mu
      (nearestNeighborPathGaussianGrowthMaximalEvent (k + 2) T epsilon \ bad) ≠ 0 := by
    rw [hdiff]
    exact ne_of_gt hgrowth
  obtain ⟨p, hpGrowth, hpNotBad⟩ := nonempty_of_measure_ne_zero hdiffNe
  have hpSimple := nearestNeighborPathFin_simple_of_mem_maximalSet hpGrowth.1
  have hpUniversal : HasUniversalFiniteObserverFirstReturnLaw
      (sortedEnsembleSpectrum
        (nearestNeighborPathFinGenerator_isHermitian (k + 2)) p) := by
    by_contra hbadLaw
    exact hpNotBad ⟨hpSimple, hbadLaw⟩
  have hpLocal : nearestNeighborPathLocalHamiltonian (k + 2) p ∈
      nearestNeighborPathLocalSubmodule (k + 2) := by
    change realAffineMatrix 0
      (realMatrixSubmoduleGenerator (nearestNeighborPathLocalSubmodule (k + 2))) p ∈
        nearestNeighborPathLocalSubmodule (k + 2)
    exact realAffineMatrix_mem_submodule
      (nearestNeighborPathLocalSubmodule (k + 2)) p
  exact ⟨p, hpGrowth, hpSimple,
    nearestNeighborPathLocalHamiltonian_isSelfAdjoint (k + 2) p,
    hpLocal, spectralEnsembleMatrix_nearestNeighborPathFinGenerator (k + 2) p,
    hpUniversal⟩

def universalObserverPathLength (k : ℕ) : ℕ := (k + 8192) + 2

def universalObserverResolution : ℝ := 1 / 400

def universalObserverLaboratoryTime (k : ℕ) : ℝ :=
  universalObserverResolution * universalObserverPathLength k

def universalObserverRadius (k : ℕ) : ℝ :=
  universalObserverResolution /
    ((universalObserverLaboratoryTime k + 1) *
      (nearestNeighborPathLocalGeneratorMass (universalObserverPathLength k) + 1))

def universalObserverWitnessTime : ℝ :=
  2048 * Real.pi * universalObserverResolution

/-- **Unconditional static local capstone.**  For every size offset, one literal bounded-degree
nearest-neighbour Hamiltonian is self-adjoint, has simple spectrum, requires at least one two-site
gate at an explicit certified laboratory time, and obeys the exact universal observer exponent
simultaneously for every finite observer.  No physical, spectral, arithmetic, or chart premise
remains. -/
theorem universalNearestNeighborPath_growth_universalObserverLaw (k : ℕ) :
    ∃ p : Fin (nearestNeighborPathLocalParameterCount
        (universalObserverPathLength k)) → ℝ,
      p ∈ nearestNeighborPathGaussianGrowthMaximalEvent
        (universalObserverPathLength k)
        (universalObserverLaboratoryTime k) universalObserverResolution ∧
      p ∈ simpleEnsembleLocus
        (nearestNeighborPathFinGenerator_isHermitian
          (universalObserverPathLength k)) ∧
      IsSelfAdjoint
        (nearestNeighborPathLocalHamiltonian (universalObserverPathLength k) p) ∧
      nearestNeighborPathLocalHamiltonian (universalObserverPathLength k) p ∈
        nearestNeighborPathLocalSubmodule (universalObserverPathLength k) ∧
      spectralEnsembleMatrix
          (nearestNeighborPathFinGenerator (universalObserverPathLength k)) p =
        Matrix.reindex (nearestNeighborPathFinEquiv (universalObserverPathLength k))
          (nearestNeighborPathFinEquiv (universalObserverPathLength k))
          (nearestNeighborPathLocalHamiltonian (universalObserverPathLength k) p) ∧
      (1 : ℕ∞) ≤ operatorTwoGateComplexityTo
        (universalObserverPathLength k) universalObserverResolution
        (unitaryEvolution
          (nearestNeighborPathLocalHamiltonian (universalObserverPathLength k) p)
          universalObserverWitnessTime) ∧
      HasUniversalFiniteObserverFirstReturnLaw
        (sortedEnsembleSpectrum
          (nearestNeighborPathFinGenerator_isHermitian
            (universalObserverPathLength k)) p) := by
  have hepsilon : 0 < universalObserverResolution := by
    norm_num [universalObserverResolution]
  have hepsilonMax : universalObserverResolution ≤ 1 / 200 := by
    norm_num [universalObserverResolution]
  have hlength : 2048 * Real.pi ≤ (universalObserverPathLength k : ℝ) := by
    have hpi := Real.pi_le_four
    rw [universalObserverPathLength]
    push_cast
    nlinarith
  have hT : 0 ≤ universalObserverLaboratoryTime k := by
    rw [universalObserverLaboratoryTime]
    positivity
  have hmass : 0 ≤ nearestNeighborPathLocalGeneratorMass
      (universalObserverPathLength k) := by
    rw [nearestNeighborPathLocalGeneratorMass]
    apply Finset.sum_nonneg
    intro i _
    rw [Matrix.cstar_norm_def]
    exact ContinuousLinearMap.opNorm_nonneg _
  have hradius : 0 < universalObserverRadius k := by
    rw [universalObserverRadius]
    positivity
  have hscale : universalObserverLaboratoryTime k *
      (universalObserverRadius k *
        nearestNeighborPathLocalGeneratorMass (universalObserverPathLength k)) ≤
      universalObserverResolution := by
    let A := universalObserverLaboratoryTime k
    let M := nearestNeighborPathLocalGeneratorMass (universalObserverPathLength k)
    let E := universalObserverResolution
    have hA : 0 ≤ A := hT
    have hM : 0 ≤ M := hmass
    have hApos : 0 < A + 1 := by positivity
    have hMpos : 0 < M + 1 := by positivity
    have hAratio0 : 0 ≤ A / (A + 1) := div_nonneg hA hApos.le
    have hAratio1 : A / (A + 1) ≤ 1 :=
      (div_le_one hApos).2 (by linarith)
    have hMratio0 : 0 ≤ M / (M + 1) := div_nonneg hM hMpos.le
    have hMratio1 : M / (M + 1) ≤ 1 :=
      (div_le_one hMpos).2 (by linarith)
    have hproduct : (A / (A + 1)) * (M / (M + 1)) ≤ 1 :=
      mul_le_one₀ hAratio1 hMratio0 hMratio1
    rw [universalObserverRadius]
    change A * (E / ((A + 1) * (M + 1)) * M) ≤ E
    calc
      A * (E / ((A + 1) * (M + 1)) * M) =
          E * ((A / (A + 1)) * (M / (M + 1))) := by
            field_simp
      _ ≤ E * 1 := mul_le_mul_of_nonneg_left hproduct hepsilon.le
      _ = E := mul_one E
  obtain ⟨p, hpGrowth, hpSimple, hpSelfAdjoint, hpLocal, hpReindex,
      hpUniversal⟩ :=
    exists_nearestNeighborPath_sameDraw_growth_universalObserverLaw
      (k := k + 8192) hT hepsilon hepsilonMax hradius hscale
  have htLab : universalObserverWitnessTime ≤
      universalObserverResolution * universalObserverPathLength k := by
    rw [universalObserverWitnessTime]
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_right hlength hepsilon.le)
  have hcomplexity := hpGrowth.2 universalObserverWitnessTime
    (le_refl universalObserverWitnessTime) htLab
    (by simpa only [universalObserverLaboratoryTime] using htLab)
  have hratio : (1 : ℝ) ≤ universalObserverWitnessTime /
      (256 * Real.pi * universalObserverResolution) := by
    rw [show universalObserverWitnessTime /
        (256 * Real.pi * universalObserverResolution) = 8 by
      rw [universalObserverWitnessTime]
      field_simp [Real.pi_ne_zero, hepsilon.ne']
      norm_num]
    norm_num
  have hfloor : 1 ≤ ⌊universalObserverWitnessTime /
      (256 * Real.pi * universalObserverResolution)⌋₊ := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using hratio
  have hcomplexityOne : (1 : ℕ∞) ≤ operatorTwoGateComplexityTo
      (universalObserverPathLength k) universalObserverResolution
      (unitaryEvolution
        (nearestNeighborPathLocalHamiltonian (universalObserverPathLength k) p)
        universalObserverWitnessTime) := by
    have hcast : (1 : ℕ∞) ≤
        ((⌊universalObserverWitnessTime /
          (256 * Real.pi * universalObserverResolution)⌋₊ : ℕ) : ℕ∞) := by
      exact_mod_cast hfloor
    exact hcast.trans hcomplexity
  exact ⟨p, hpGrowth, hpSimple, hpSelfAdjoint, hpLocal, hpReindex,
    hcomplexityOne, hpUniversal⟩

/-- Conventional path-length form of the unconditional capstone. -/
theorem exists_nearestNeighborPath_growth_universalObserverLaw_of_length
    {L : ℕ} (hL : 8194 ≤ L) :
    ∃ p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ,
      p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L
        (universalObserverResolution * L) universalObserverResolution ∧
      p ∈ simpleEnsembleLocus (nearestNeighborPathFinGenerator_isHermitian L) ∧
      IsSelfAdjoint (nearestNeighborPathLocalHamiltonian L p) ∧
      nearestNeighborPathLocalHamiltonian L p ∈ nearestNeighborPathLocalSubmodule L ∧
      spectralEnsembleMatrix (nearestNeighborPathFinGenerator L) p =
        Matrix.reindex (nearestNeighborPathFinEquiv L) (nearestNeighborPathFinEquiv L)
          (nearestNeighborPathLocalHamiltonian L p) ∧
      (1 : ℕ∞) ≤ operatorTwoGateComplexityTo L universalObserverResolution
        (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p)
          universalObserverWitnessTime) ∧
      HasUniversalFiniteObserverFirstReturnLaw
        (sortedEnsembleSpectrum (nearestNeighborPathFinGenerator_isHermitian L) p) := by
  let k := L - 8194
  have hpath : universalObserverPathLength k = L := by
    rw [universalObserverPathLength]
    dsimp only [k]
    omega
  have hmain := universalNearestNeighborPath_growth_universalObserverLaw k
  rw [hpath] at hmain
  simpa only [universalObserverLaboratoryTime, hpath] using hmain

end

end RHTower
