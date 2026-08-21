import GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianOneDrawGrowthLaw
import GaloisForLFunctions.HTGeometry.RobustStaticLocalCircuitSetAvoidanceLaw
import GaloisForLFunctions.HTGeometry.NestedPathCutWitness
import GaloisForLFunctions.HTGeometry.SiteFactorGraphWitness
import GaloisForLFunctions.HTGeometry.PiMeasureAbsoluteContinuity
import GaloisForLFunctions.HTGeometry.ShellSimpleSpectrum

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal NNReal
open Matrix MeasureTheory ProbabilityTheory Metric Set Topology Filter

open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

def nearestNeighborPathLocalSubmodule (L : ℕ) :=
  siteFactorLocalSubmodule (fun _ : PairQubit L => Bool) (nestedQubitPathGraph L)

theorem matchingOccupationMatrix_isSiteSupported {L : ℕ} (j : Fin L) :
    IsSiteSupported (A := fun _ : PairQubit L => Bool) {(j, false), (j, true)}
      (matchingOccupationMatrix j) := by
  constructor
  · intro x y hxy
    have hne : x ≠ y := by
      intro h
      subst y
      exact hxy.choose_spec.2 rfl
    simp [matchingOccupationMatrix, hne]
  · intro x y x' y' hx hy hout hout'
    by_cases hxy : x = y
    · subst y
      have hxy' : x' = y' := by
        funext w
        by_cases hw : w ∈ ({(j, false), (j, true)} : Finset (PairQubit L))
        · rw [← hx w hw, ← hy w hw]
        · exact hout' w hw
      subst y'
      have hfalse : x (j, false) = x' (j, false) := hx _ (by simp)
      have htrue : x (j, true) = x' (j, true) := hx _ (by simp)
      simp [matchingOccupationMatrix, hfalse, htrue]
    · have hxy' : x' ≠ y' := by
        intro h
        subst y'
        apply hxy
        funext w
        by_cases hw : w ∈ ({(j, false), (j, true)} : Finset (PairQubit L))
        · rw [hx w hw, hy w hw]
        · exact hout w hw
      simp [matchingOccupationMatrix, hxy, hxy']

theorem bridgeOccupationMatrix_isSiteSupported {L : ℕ} (j : Fin L)
    (h : j.val + 1 < L) :
    IsSiteSupported (A := fun _ : PairQubit L => Bool)
      {(j, true), (⟨j.val + 1, h⟩, false)} (bridgeOccupationMatrix j) := by
  constructor
  · intro x y hxy
    have hne : x ≠ y := by
      intro hxy'
      subst y
      exact hxy.choose_spec.2 rfl
    simp [bridgeOccupationMatrix, h, hne]
  · intro x y x' y' hx hy hout hout'
    by_cases hxy : x = y
    · subst y
      have hxy' : x' = y' := by
        funext w
        by_cases hw : w ∈ ({(j, true), (⟨j.val + 1, h⟩, false)} :
            Finset (PairQubit L))
        · rw [← hx w hw, ← hy w hw]
        · exact hout' w hw
      subst y'
      have hleft : x (j, true) = x' (j, true) := hx _ (by simp)
      have hright : x (⟨j.val + 1, h⟩, false) =
          x' (⟨j.val + 1, h⟩, false) := hx _ (by simp)
      simp [bridgeOccupationMatrix, h, hleft, hright]
    · have hxy' : x' ≠ y' := by
        intro hxy'
        subst y'
        apply hxy
        funext w
        by_cases hw : w ∈ ({(j, true), (⟨j.val + 1, h⟩, false)} :
            Finset (PairQubit L))
        · rw [hx w hw, hy w hw]
        · exact hout w hw
      simp [bridgeOccupationMatrix, h, hxy, hxy']

theorem matchingOccupationMatrix_mem_nearestNeighborPathLocalSubmodule
    {L : ℕ} (j : Fin L) :
    matchingOccupationMatrix j ∈ nearestNeighborPathLocalSubmodule L := by
  exact mem_siteFactorLocalSubmodule_of_edge
    (fun _ : PairQubit L => Bool) (nestedQubitPathGraph L)
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr
      (matchingOccupationMatrix_isSelfAdjoint j))
    (nestedQubitPathGraph_adj_pair j)
    (matchingOccupationMatrix_isSiteSupported j)

theorem bridgeOccupationMatrix_mem_nearestNeighborPathLocalSubmodule
    {L : ℕ} (j : Fin L) :
    bridgeOccupationMatrix j ∈ nearestNeighborPathLocalSubmodule L := by
  by_cases h : j.val + 1 < L
  · exact mem_siteFactorLocalSubmodule_of_edge
      (fun _ : PairQubit L => Bool) (nestedQubitPathGraph L)
      (Matrix.isHermitian_iff_isSelfAdjoint.mpr
        (bridgeOccupationMatrix_isSelfAdjoint j))
      (by
        rw [nestedQubitPathGraph, SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj]
        left
        simp [pairQubitPathEquiv, finProdFinEquiv, finTwoEquiv]
        omega)
      (bridgeOccupationMatrix_isSiteSupported j h)
  · have hz : bridgeOccupationMatrix j = 0 := by
      ext x y
      simp [bridgeOccupationMatrix, h]
    rw [hz]
    exact Submodule.zero_mem _

theorem inverseSquareChainHamiltonian_eq_localTerms (L : ℕ) :
    inverseSquareChainHamiltonian L =
      (∑ j : Fin L, (1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) •
        matchingOccupationMatrix j) +
      ∑ j : Fin L, (1 / (L : ℝ) ^ 3) • bridgeOccupationMatrix j := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [inverseSquareChainHamiltonian, inverseSquareChainEnergy,
      inverseSquareMatchingEnergy, inverseCubeBridgeEnergy,
      matchingOccupationMatrix, bridgeOccupationMatrix,
      Matrix.sum_apply]
    rw [Finset.mul_sum]
    congr 1 <;>
      apply Finset.sum_congr rfl <;>
      intro j _ <;>
      split_ifs <;> simp_all
  · simp [inverseSquareChainHamiltonian, matchingOccupationMatrix,
      bridgeOccupationMatrix, Matrix.sum_apply, hxy]

theorem inverseSquareChainHamiltonian_mem_nearestNeighborPathLocalSubmodule (L : ℕ) :
    inverseSquareChainHamiltonian L ∈ nearestNeighborPathLocalSubmodule L := by
  rw [inverseSquareChainHamiltonian_eq_localTerms]
  apply Submodule.add_mem
  · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (matchingOccupationMatrix_mem_nearestNeighborPathLocalSubmodule j)
  · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (bridgeOccupationMatrix_mem_nearestNeighborPathLocalSubmodule j)

def nearestNeighborPathLocalParameterCount (L : ℕ) : ℕ :=
  Module.finrank ℝ (nearestNeighborPathLocalSubmodule L)

def nearestNeighborPathLocalGenerator (L : ℕ) :
    Fin (nearestNeighborPathLocalParameterCount L) →
      Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  realMatrixSubmoduleGenerator (nearestNeighborPathLocalSubmodule L)

def nearestNeighborPathLocalHamiltonian (L : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  realAffineMatrix 0 (nearestNeighborPathLocalGenerator L) p

theorem nearestNeighborPathLocalGenerator_isHermitian (L : ℕ)
    (i : Fin (nearestNeighborPathLocalParameterCount L)) :
    (nearestNeighborPathLocalGenerator L i).IsHermitian :=
  realMatrixSubmoduleGenerator_isHermitian
    (nearestNeighborPathLocalSubmodule L)
    (siteFactorLocalSubmodule_le_selfAdjoint
      (fun _ : PairQubit L => Bool) (nestedQubitPathGraph L)) i

theorem nearestNeighborPathLocalHamiltonian_isSelfAdjoint (L : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    IsSelfAdjoint (nearestNeighborPathLocalHamiltonian L p) := by
  exact Matrix.isHermitian_iff_isSelfAdjoint.mp
    (realAffineMatrix_isHermitian 0 (nearestNeighborPathLocalGenerator L)
      Matrix.isHermitian_zero (nearestNeighborPathLocalGenerator_isHermitian L) p)

theorem nearestNeighborPathLocalHamiltonian_isHermitian (L : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    (nearestNeighborPathLocalHamiltonian L p).IsHermitian :=
  realAffineMatrix_isHermitian 0 (nearestNeighborPathLocalGenerator L)
    Matrix.isHermitian_zero (nearestNeighborPathLocalGenerator_isHermitian L) p

def inverseSquarePathLocalCenter (L : ℕ) :
    Fin (nearestNeighborPathLocalParameterCount L) → ℝ :=
  Classical.choose (exists_realAffineMatrix_eq_of_mem_submodule
    (nearestNeighborPathLocalSubmodule L)
    (inverseSquareChainHamiltonian L)
    (inverseSquareChainHamiltonian_mem_nearestNeighborPathLocalSubmodule L))

@[simp] theorem nearestNeighborPathLocalHamiltonian_center (L : ℕ) :
    nearestNeighborPathLocalHamiltonian L (inverseSquarePathLocalCenter L) =
      inverseSquareChainHamiltonian L :=
  Classical.choose_spec (exists_realAffineMatrix_eq_of_mem_submodule
    (nearestNeighborPathLocalSubmodule L)
    (inverseSquareChainHamiltonian L)
    (inverseSquareChainHamiltonian_mem_nearestNeighborPathLocalSubmodule L))

def nearestNeighborPathLocalGeneratorMass (L : ℕ) : ℝ :=
  ∑ i, ‖nearestNeighborPathLocalGenerator L i‖

theorem norm_nearestNeighborPathLocalHamiltonian_sub_center_le
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) {ρ : ℝ}
    (hp : p ∈ closedBall (inverseSquarePathLocalCenter L) ρ) :
    ‖nearestNeighborPathLocalHamiltonian L p - inverseSquareChainHamiltonian L‖ ≤
      ρ * nearestNeighborPathLocalGeneratorMass L := by
  classical
  have hnorm : ‖p - inverseSquarePathLocalCenter L‖ ≤ ρ := by
    simpa [mem_closedBall, dist_eq_norm] using hp
  have hcoord : ∀ i, |p i - inverseSquarePathLocalCenter L i| ≤ ρ := by
    intro i
    have hi := norm_le_pi_norm (p - inverseSquarePathLocalCenter L) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at hi
    exact hi.trans hnorm
  rw [← nearestNeighborPathLocalHamiltonian_center L]
  unfold nearestNeighborPathLocalHamiltonian
  have hrewrite (q : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
      realAffineMatrix 0 (nearestNeighborPathLocalGenerator L) q =
        ∑ i, q i • nearestNeighborPathLocalGenerator L i := by
    ext a b
    simp [realAffineMatrix, Matrix.sum_apply, Matrix.smul_apply]
  rw [hrewrite p, hrewrite (inverseSquarePathLocalCenter L)]
  calc
    ‖(∑ i, p i • nearestNeighborPathLocalGenerator L i) -
        ∑ i, inverseSquarePathLocalCenter L i • nearestNeighborPathLocalGenerator L i‖
      = ‖∑ i, (p i - inverseSquarePathLocalCenter L i) •
          nearestNeighborPathLocalGenerator L i‖ := by
          rw [← Finset.sum_sub_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [sub_smul]
    _ ≤ ∑ i, ‖(p i - inverseSquarePathLocalCenter L i) •
          nearestNeighborPathLocalGenerator L i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ρ * ‖nearestNeighborPathLocalGenerator L i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hcoord i) (norm_nonneg _)
    _ = ρ * nearestNeighborPathLocalGeneratorMass L := by
      rw [nearestNeighborPathLocalGeneratorMass, Finset.mul_sum]

def nearestNeighborPathLocalMaximalSet (L : ℕ) :
    Set (Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :=
  realHermitianSubmoduleMaximalSet
    (nearestNeighborPathLocalSubmodule L)
    (siteFactorLocalSubmodule_le_selfAdjoint
      (fun _ : PairQubit L => Bool) (nestedQubitPathGraph L))

theorem maximallyProjectiveEnergy_nearestNeighborPathLocalHamiltonian
    {L : ℕ} {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathLocalMaximalSet L) :
    MaximallyProjectiveEnergy
      (nearestNeighborPathLocalHamiltonian_isHermitian L p).eigenvalues := by
  rw [nearestNeighborPathLocalMaximalSet,
    realHermitianSubmoduleMaximalSet, realAffineHermitianMaximalSet,
    polynomialHermitianMatrixMaximalSet] at hp
  change MaximallyProjectiveEnergy _ at hp
  convert hp using 1
  exact (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).2 (by
    rw [eval_realAffineMatrixPolynomial]
    rfl)

theorem nearestNeighborPathLocalMaximalSet_dense_residual_fullMeasure
    {L : ℕ} (hL : 0 < L) :
    Dense (nearestNeighborPathLocalMaximalSet L) ∧
      nearestNeighborPathLocalMaximalSet L ∈
        residual (Fin (nearestNeighborPathLocalParameterCount L) → ℝ) ∧
      volume (nearestNeighborPathLocalMaximalSet L)ᶜ = 0 := by
  letI : Nonempty (PairQubit L) := ⟨(⟨0, hL⟩, false)⟩
  have hconnected : (nestedQubitPathGraph L).Connected :=
    (nestedQubitPathGraph_isTree hL).connected
  obtain ⟨H, hH, hHmem, hmax⟩ :=
    exists_maximallyProjective_mem_siteFactorLocalSubmodule
      (nestedQubitPathGraph L) hconnected
      (fun _ : PairQubit L => Bool) (fun _ => by simp)
  exact realHermitianSubmoduleMaximalSet_dense_residual_fullMeasure
    (nearestNeighborPathLocalSubmodule L)
    (siteFactorLocalSubmodule_le_selfAdjoint
      (fun _ : PairQubit L => Bool) (nestedQubitPathGraph L))
    H hHmem hH hmax

def nearestNeighborPathGaussianGrowthMaximalEvent
    (L : ℕ) (T ε : ℝ) :
    Set (Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :=
  {p | p ∈ nearestNeighborPathLocalMaximalSet L ∧
    ∀ t : ℝ,
      2048 * Real.pi * ε ≤ t →
      t ≤ ε * L →
      t ≤ T →
      ((⌊t / (256 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L ε
          (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t)}

/-- Every draw in the growth--maximal event avoids the complete two-gate cutoff set throughout
the corresponding certified laboratory window.  The target is the union of all support-certified
circuits below the cutoff, not only a neighbourhood of the initial operator. -/
theorem nearestNeighborPathGaussianGrowthMaximalEvent_uniform_circuitSet_avoidance
    {L s : ℕ} {T ε : ℝ}
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L T ε)
    (hε : 0 < ε) :
    ∀ t : ℝ,
      2048 * Real.pi * ε ≤ t →
      256 * Real.pi * ε * (s + 1) ≤ t →
      t ≤ ε * L →
      t ≤ T →
      ¬ InTwoGateCircuitSetAtMost ε
        (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t) s := by
  intro t htMin htCircuit htLab htT hmem
  have hlow := hp.2 t htMin htLab htT
  rcases hmem with ⟨c, hc, hcost⟩
  have hupper := operatorTwoGateComplexityTo_le_of_circuit hc
  have hden : 0 < 256 * Real.pi * ε := by
    positivity
  have hratio : ((s + 1 : ℕ) : ℝ) ≤ t / (256 * Real.pi * ε) := by
    rw [le_div_iff₀ hden]
    simpa [mul_comm, mul_left_comm, mul_assoc] using htCircuit
  have hfloor : s + 1 ≤ ⌊t / (256 * Real.pi * ε)⌋₊ := Nat.le_floor hratio
  have hchain : (((s + 1 : ℕ) : ℕ∞)) ≤ (s : ℕ∞) := by
    exact (by exact_mod_cast hfloor : ((s + 1 : ℕ) : ℕ∞) ≤
      ((⌊t / (256 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞)).trans
        (hlow.trans (hupper.trans (by exact_mod_cast hcost)))
  have hnat : s + 1 ≤ s := by exact_mod_cast hchain
  omega

theorem measure_nearestNeighborPathGaussianGrowthMaximalEvent_pos
    {L : ℕ} (hL : 0 < L) {T ε ρ : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (hρ : 0 < ρ)
    (hscale : T * (ρ * nearestNeighborPathLocalGeneratorMass L) ≤ ε) :
    0 < (centredProductGaussian
      (Fin (nearestNeighborPathLocalParameterCount L)) 1)
      (nearestNeighborPathGaussianGrowthMaximalEvent L T ε) := by
  let μ := centredProductGaussian
    (Fin (nearestNeighborPathLocalParameterCount L)) 1
  let B := ball (inverseSquarePathLocalCenter L) ρ
  have hvolB : 0 < (volume : Measure
      (Fin (nearestNeighborPathLocalParameterCount L) → ℝ)) B :=
    Metric.measure_ball_pos volume _ hρ
  have hvolAC : (volume : Measure
      (Fin (nearestNeighborPathLocalParameterCount L) → ℝ)) ≪ μ := by
    exact volume_absolutelyContinuous_centredProductGaussian _ one_ne_zero
  have hμB : μ B ≠ 0 := by
    intro hzero
    exact hvolB.ne' (hvolAC hzero)
  have hμAC : μ ≪ (volume : Measure
      (Fin (nearestNeighborPathLocalParameterCount L) → ℝ)) := by
    simpa [μ, centredProductGaussian] using
      (productGaussian_absolutelyContinuous
        (nearestNeighborPathLocalParameterCount L) one_ne_zero
        (fun _ => 0))
  have hbadVol :=
    (nearestNeighborPathLocalMaximalSet_dense_residual_fullMeasure hL).2.2
  have hbadμ : μ (nearestNeighborPathLocalMaximalSet L)ᶜ = 0 := hμAC hbadVol
  have hinter : μ (B ∩ nearestNeighborPathLocalMaximalSet L) = μ B := by
    rw [show B ∩ nearestNeighborPathLocalMaximalSet L =
      B \ (nearestNeighborPathLocalMaximalSet L)ᶜ by ext p; simp]
    exact measure_sdiff_null hbadμ
  have hsubset : B ∩ nearestNeighborPathLocalMaximalSet L ⊆
      nearestNeighborPathGaussianGrowthMaximalEvent L T ε := by
    intro p hp
    refine ⟨hp.2, ?_⟩
    intro t htMin htLab htT
    have hpclosed : p ∈ closedBall (inverseSquarePathLocalCenter L) ρ :=
      Metric.ball_subset_closedBall hp.1
    have hnorm := norm_nearestNeighborPathLocalHamiltonian_sub_center_le
      L p hpclosed
    have htube : T * ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤ ε :=
      (mul_le_mul_of_nonneg_left hnorm hT).trans hscale
    exact perturbed_inverseSquareChain_uniform_laboratory_growth
      (nearestNeighborPathLocalHamiltonian_isSelfAdjoint L p)
      hε hεmax htube t htMin htLab htT
  have hle : μ (B ∩ nearestNeighborPathLocalMaximalSet L) ≤
      μ (nearestNeighborPathGaussianGrowthMaximalEvent L T ε) :=
    measure_mono hsubset
  rw [hinter] at hle
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hμB) hle

end

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
