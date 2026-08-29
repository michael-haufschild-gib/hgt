import GaloisForLFunctions.HTGeometry.PauliChainDephasing
import GaloisForLFunctions.HTGeometry.HistogramCentralizerDimension
import GaloisForLFunctions.HTGeometry.AnnealedSpectralDephasing
import GaloisForLFunctions.HTGeometry.AngularPhaseLaw

open Filter Topology MeasureTheory Metric Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Real spectral character carried by two ordered replica tuples. -/
def orderedReplicaActionCharacter {D r : ℕ}
    (α β : Fin r → Fin D) : Fin D → ℝ :=
  fun j => (orderedReplicaMultiplicity α j : ℝ) - orderedReplicaMultiplicity β j

/-- Every ordered-replica action character is balanced. -/
theorem sum_orderedReplicaActionCharacter {D r : ℕ} (α β : Fin r → Fin D) :
    ∑ j, orderedReplicaActionCharacter α β j = 0 := by
  classical
  have hα : ∑ j, orderedReplicaMultiplicity α j = r :=
    (Finset.mem_piAntidiag.mp (orderedReplicaMultiplicity_mem_piAntidiag α)).1
  have hβ : ∑ j, orderedReplicaMultiplicity β j = r :=
    (Finset.mem_piAntidiag.mp (orderedReplicaMultiplicity_mem_piAntidiag β)).1
  change (∑ j, (((orderedReplicaMultiplicity α j : ℕ) : ℝ) -
    (orderedReplicaMultiplicity β j : ℕ))) = 0
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, hα, hβ, sub_self]

/-- The ordered-replica action character vanishes exactly on a histogram collision. -/
theorem orderedReplicaActionCharacter_eq_zero_iff {D r : ℕ} (α β : Fin r → Fin D) :
    orderedReplicaActionCharacter α β = 0 ↔
      orderedReplicaMultiplicity α = orderedReplicaMultiplicity β := by
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    simp only [orderedReplicaActionCharacter, Pi.zero_apply, sub_eq_zero] at hj
    exact_mod_cast hj
  · intro h
    funext j
    rw [orderedReplicaActionCharacter, h]
    simp

/-- Ordered pairs of replica tuples with distinct multiplicity histograms. -/
abbrev OffHistogramReplicaPair (D r : ℕ) :=
  {q : (Fin r → Fin D) × (Fin r → Fin D) //
    orderedReplicaMultiplicity q.1 ≠ orderedReplicaMultiplicity q.2}

/-- Every off-histogram replica phase on the nearest-neighbour Pauli shell dephases against an
arbitrary bounded measurable amplitude. -/
theorem tendsto_integral_exp_orderedReplicaAction_zero_pauliChain (k r : ℕ)
    (q : OffHistogramReplicaPair (2 ^ (k + 3)) r)
    (g : coeffSphere (Fintype.card (ChainLabel (k + 3))) → ℂ)
    (hg : Measurable g) {Cb : ℝ} (hC0 : 0 ≤ Cb) (hC : ∀ x, ‖g x‖ ≤ Cb) :
    Tendsto (fun t : ℝ => ∫ x, g x *
        Complex.exp (-((t * sortedSpectralAction (chainPauliFin_isHermitian (k + 3))
          (orderedReplicaActionCharacter q.1.1 q.1.2) (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
        ∂(volume.toSphere))
      (cocompact ℝ) (nhds 0) := by
  apply tendsto_integral_exp_sortedSpectralAction_zero_pauliChain k
  · exact sum_orderedReplicaActionCharacter q.1.1 q.1.2
  · exact (orderedReplicaActionCharacter_eq_zero_iff q.1.1 q.1.2).not.mpr q.2
  · exact hg
  · exact hC0
  · exact hC

variable {w : Type*} [Fintype w] [DecidableEq w]

/-- **Equation (19), nearest-neighbour Pauli-shell replica form.**  Every finite matrix whose
entries are finite sums of off-histogram replica phases with bounded measurable spectral weights
converges to zero in operator norm. -/
theorem tendsto_pauliChain_offHistogramAnnealedMatrix_l2_opNorm_zero (k r : ℕ)
    (γ : OffHistogramReplicaPair (2 ^ (k + 3)) r → w → w →
      coeffSphere (Fintype.card (ChainLabel (k + 3))) → ℂ)
    (hγ : ∀ q i j, Measurable (γ q i j))
    {Cb : ℝ} (hCb0 : 0 ≤ Cb) (hCb : ∀ q i j x, ‖γ q i j x‖ ≤ Cb)
    (M : ℝ → Matrix w w ℂ)
    (hM : ∀ t i j, M t i j =
      ∑ q, ∫ x, γ q i j x *
        Complex.exp (-((t * sortedSpectralAction (chainPauliFin_isHermitian (k + 3))
          (orderedReplicaActionCharacter q.1.1 q.1.2) (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
        ∂(volume.toSphere)) :
    Tendsto (fun t : ℝ => ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := w)) (M t)‖)
      (cocompact ℝ) (nhds 0) := by
  refine finiteMatrix_entrywise_tendsto_operatorNorm_zero M fun i j => ?_
  have hterm : ∀ q : OffHistogramReplicaPair (2 ^ (k + 3)) r,
      Tendsto (fun t : ℝ => ∫ x, γ q i j x *
        Complex.exp (-((t * sortedSpectralAction (chainPauliFin_isHermitian (k + 3))
          (orderedReplicaActionCharacter q.1.1 q.1.2) (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
        ∂(volume.toSphere)) (cocompact ℝ) (nhds 0) :=
    fun q => tendsto_integral_exp_orderedReplicaAction_zero_pauliChain k r q
      (γ q i j) (hγ q i j) hCb0 (fun x => hCb q i j x)
  have hsum := tendsto_finsetSum (s := Finset.univ) fun q _ => hterm q
  simpa only [Finset.sum_const_zero] using
    hsum.congr (fun t => (hM t i j).symm)

end

end GaloisForLFunctions.HTGeometry
