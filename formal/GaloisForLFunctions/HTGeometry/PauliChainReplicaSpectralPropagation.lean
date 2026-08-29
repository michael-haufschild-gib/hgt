import GaloisForLFunctions.HTGeometry.PauliChainReplicaAnnealedDephasing
import GaloisForLFunctions.HTGeometry.ShellPlateauAssembly
import GaloisForLFunctions.HTGeometry.TorusReplicaMomentBound

open Filter Topology MeasureTheory Metric Matrix ComplexConjugate
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Standard coordinate ket in a finite complex Hilbert space. -/
def finiteCoordinateKet {D : ℕ} (i : Fin D) : Fin D → ℂ :=
  fun j => if j = i then 1 else 0

theorem finiteComplexInner_finiteCoordinateKet_right {D : ℕ}
    (u : Fin D → ℂ) (i : Fin D) :
    finiteComplexInner u (finiteCoordinateKet i) = conj (u i) := by
  classical
  rw [finiteComplexInner]
  simp [finiteCoordinateKet]

theorem norm_orthoEigenBasis_coordinate_le_one {D : ℕ}
    {H : Matrix (Fin D) (Fin D) ℂ} {e : Fin D → Fin D → ℂ} {lam : Fin D → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (j i : Fin D) : ‖e j i‖ ≤ 1 := by
  have hsum : ∑ x, ‖e j x‖ ^ 2 = 1 := by
    have hinner : finiteComplexInner (e j) (e j) = (1 : ℂ) := by
      simpa using heb.orth j j
    rw [finiteComplexInner_self_eq_sum_normSq] at hinner
    exact Complex.ofReal_injective hinner
  have hsq : ‖e j i‖ ^ 2 ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun x _ => sq_nonneg ‖e j x‖) (Finset.mem_univ i)
  nlinarith [norm_nonneg (e j i)]

theorem measurable_lagrangeFactor_family_entry {X α : Type*} [MeasurableSpace X]
    [Fintype α] [DecidableEq α] {Ef : X → α → ℝ} {Hf : X → Matrix α α ℂ}
    (hE : ∀ i, Measurable (fun x => Ef x i))
    (hH : ∀ a b, Measurable (fun x => Hf x a b)) (j k a b : α) :
    Measurable (fun x => lagrangeFactor (Ef x) j (Hf x) k a b) := by
  simp only [lagrangeFactor, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply]
  fun_prop

theorem measurable_listProd_lagrangeFactor_family_entry {X α : Type*} [MeasurableSpace X]
    [Fintype α] [DecidableEq α] {Ef : X → α → ℝ} {Hf : X → Matrix α α ℂ}
    (hE : ∀ i, Measurable (fun x => Ef x i))
    (hH : ∀ a b, Measurable (fun x => Hf x a b))
    (j : α) (l : List α) (a b : α) :
    Measurable (fun x => (l.map (lagrangeFactor (Ef x) j (Hf x))).prod a b) := by
  induction l generalizing a b with
  | nil => simp only [List.map_nil, List.prod_nil]; fun_prop
  | cons k l ih =>
      simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
      exact Finset.measurable_sum _ fun c _ =>
        (measurable_lagrangeFactor_family_entry hE hH j k a c).mul (ih c b)

theorem measurable_lagrangeSpectralProjector_family_entry {X α : Type*} [MeasurableSpace X]
    [Fintype α] [DecidableEq α] {Ef : X → α → ℝ} {Hf : X → Matrix α α ℂ}
    (hE : ∀ i, Measurable (fun x => Ef x i))
    (hH : ∀ a b, Measurable (fun x => Hf x a b)) (j a b : α) :
    Measurable (fun x => lagrangeSpectralProjector (Ef x) j (Hf x) a b) := by
  unfold lagrangeSpectralProjector
  exact measurable_listProd_lagrangeFactor_family_entry hE hH j _ a b

theorem measurable_spectralCrossWeight_family {X α : Type*} [MeasurableSpace X]
    [Fintype α] [DecidableEq α] {Ef : X → α → ℝ} {Hf : X → Matrix α α ℂ}
    (hE : ∀ i, Measurable (fun x => Ef x i))
    (hH : ∀ a b, Measurable (fun x => Hf x a b)) (u v : α → ℂ) (j : α) :
    Measurable (fun x => spectralCrossWeight (Ef x) (Hf x) u v j) := by
  simp only [spectralCrossWeight, finiteComplexInner, Matrix.mulVec]
  exact Finset.measurable_sum _ fun a _ => measurable_const.mul
    (Finset.measurable_sum _ fun b _ =>
      (measurable_lagrangeSpectralProjector_family_entry hE hH j a b).mul measurable_const)

/-- Gauge-invariant matrix entry of the `j`-th sorted rank-one spectral projector, extended by
zero across the null repeated-spectrum locus. -/
noncomputable def pauliChainSpectralProjectorEntry (k : ℕ)
    (x : coeffSphere (Fintype.card (ChainLabel (k + 3))))
    (j u v : Fin (2 ^ (k + 3))) : ℂ := by
  classical
  exact if x ∈ simpleLocus (chainPauliFin_isHermitian (k + 3)) then
      spectralCrossWeight
        (spectralTuple (chainPauliFin_isHermitian (k + 3)) (sphereCoeff x))
        (spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff x))
        (finiteCoordinateKet u) (finiteCoordinateKet v) j
    else 0

theorem measurable_pauliChainSpectralProjectorEntry (k : ℕ)
    (j u v : Fin (2 ^ (k + 3))) :
    Measurable (fun x => pauliChainSpectralProjectorEntry k x j u v) := by
  classical
  simp only [pauliChainSpectralProjectorEntry]
  apply Measurable.ite (isOpen_simpleLocus
    (chainPauliFin_isHermitian (k + 3))).measurableSet
  · exact measurable_spectralCrossWeight_family
      (fun i => ((continuous_apply i).comp
        ((continuous_spectralTuple (chainPauliFin_isHermitian (k + 3))).comp
          continuous_sphereCoeff)).measurable)
      (fun a b => ((continuous_apply b).comp ((continuous_apply a).comp
        ((continuous_spectralEnsembleMatrix (chainPauliFin (k + 3))).comp
          continuous_sphereCoeff))).measurable)
      (finiteCoordinateKet u) (finiteCoordinateKet v) j
  · exact measurable_const

theorem norm_pauliChainSpectralProjectorEntry_le_one (k : ℕ)
    (x : coeffSphere (Fintype.card (ChainLabel (k + 3))))
    (j u v : Fin (2 ^ (k + 3))) :
    ‖pauliChainSpectralProjectorEntry k x j u v‖ ≤ 1 := by
  rw [pauliChainSpectralProjectorEntry]
  split_ifs with hx
  · rw [spectralCrossWeight_eq
      (isOrthoEigenBasis_sortedEigenBasis (chainPauliFin_isHermitian (k + 3)) (sphereCoeff x))
      (injective_spectralTuple (chainPauliFin_isHermitian (k + 3)) hx),
      finiteComplexInner_finiteCoordinateKet_right,
      finiteComplexInner_finiteCoordinateKet_right, norm_mul, Complex.norm_conj]
    have hu := norm_orthoEigenBasis_coordinate_le_one
      (isOrthoEigenBasis_sortedEigenBasis (chainPauliFin_isHermitian (k + 3)) (sphereCoeff x)) j u
    have hu' : ‖conj (sortedEigenBasis (chainPauliFin_isHermitian (k + 3))
        (sphereCoeff x) j u)‖ ≤ 1 := by simpa using hu
    have hv := norm_orthoEigenBasis_coordinate_le_one
      (isOrthoEigenBasis_sortedEigenBasis (chainPauliFin_isHermitian (k + 3)) (sphereCoeff x)) j v
    have hv' : ‖conj (sortedEigenBasis (chainPauliFin_isHermitian (k + 3))
        (sphereCoeff x) j v)‖ ≤ 1 := by simpa using hv
    exact mul_le_one₀ hu'
      (norm_nonneg _) hv'
  · simp

/-- Matrix entry of a tensor-product spectral projector on the ordered `r`-replica space. -/
def pauliChainReplicaSpectralProjectorEntry (k r : ℕ)
    (x : coeffSphere (Fintype.card (ChainLabel (k + 3))))
    (α u v : Fin r → Fin (2 ^ (k + 3))) : ℂ :=
  ∏ a, pauliChainSpectralProjectorEntry k x (α a) (u a) (v a)

theorem measurable_pauliChainReplicaSpectralProjectorEntry (k r : ℕ)
    (α u v : Fin r → Fin (2 ^ (k + 3))) :
    Measurable (fun x => pauliChainReplicaSpectralProjectorEntry k r x α u v) := by
  apply Finset.measurable_prod
  intro a ha
  exact measurable_pauliChainSpectralProjectorEntry k (α a) (u a) (v a)

theorem norm_pauliChainReplicaSpectralProjectorEntry_le_one (k r : ℕ)
    (x : coeffSphere (Fintype.card (ChainLabel (k + 3))))
    (α u v : Fin r → Fin (2 ^ (k + 3))) :
    ‖pauliChainReplicaSpectralProjectorEntry k r x α u v‖ ≤ 1 := by
  rw [pauliChainReplicaSpectralProjectorEntry, norm_prod]
  exact Finset.prod_le_one (fun a _ => norm_nonneg _)
    (fun a _ => norm_pauliChainSpectralProjectorEntry_le_one k x (α a) (u a) (v a))

/-- Matrix coefficient of one Liouville eigenmode in physical coordinates. -/
def pauliChainReplicaLiouvilleAmplitudeAll (k r : ℕ)
    (q : (Fin r → Fin (2 ^ (k + 3))) × (Fin r → Fin (2 ^ (k + 3))))
    (out inp : (Fin r → Fin (2 ^ (k + 3))) × (Fin r → Fin (2 ^ (k + 3))))
    (x : coeffSphere (Fintype.card (ChainLabel (k + 3)))) : ℂ :=
  pauliChainReplicaSpectralProjectorEntry k r x q.1 out.1 inp.1 *
    pauliChainReplicaSpectralProjectorEntry k r x q.2 inp.2 out.2

/-- Off-histogram restriction of the physical Liouville eigenmode coefficient. -/
def pauliChainReplicaLiouvilleAmplitude (k r : ℕ)
    (q : OffHistogramReplicaPair (2 ^ (k + 3)) r) :=
  pauliChainReplicaLiouvilleAmplitudeAll k r q.1

theorem measurable_pauliChainReplicaLiouvilleAmplitude (k r : ℕ)
    (q : OffHistogramReplicaPair (2 ^ (k + 3)) r)
    (out inp : (Fin r → Fin (2 ^ (k + 3))) × (Fin r → Fin (2 ^ (k + 3)))) :
    Measurable (pauliChainReplicaLiouvilleAmplitude k r q out inp) :=
  (measurable_pauliChainReplicaSpectralProjectorEntry k r q.1.1 out.1 inp.1).mul
    (measurable_pauliChainReplicaSpectralProjectorEntry k r q.1.2 inp.2 out.2)

theorem norm_pauliChainReplicaLiouvilleAmplitude_le_one (k r : ℕ)
    (q : OffHistogramReplicaPair (2 ^ (k + 3)) r)
    (out inp : (Fin r → Fin (2 ^ (k + 3))) × (Fin r → Fin (2 ^ (k + 3))))
    (x : coeffSphere (Fintype.card (ChainLabel (k + 3)))) :
    ‖pauliChainReplicaLiouvilleAmplitude k r q out inp x‖ ≤ 1 := by
  rw [pauliChainReplicaLiouvilleAmplitude, pauliChainReplicaLiouvilleAmplitudeAll, norm_mul]
  exact mul_le_one₀
    (norm_pauliChainReplicaSpectralProjectorEntry_le_one k r x q.1.1 out.1 inp.1)
    (norm_nonneg _)
    (norm_pauliChainReplicaSpectralProjectorEntry_le_one k r x q.1.2 inp.2 out.2)

abbrev PauliChainReplicaLiouvilleIndex (k r : ℕ) :=
  (Fin r → Fin (2 ^ (k + 3))) × (Fin r → Fin (2 ^ (k + 3)))

/-- Full annealed replica Liouville propagator, before subtracting the quenched moving
centralizer. -/
def pauliChainReplicaAnnealedPropagator (k r : ℕ) (t : ℝ) :
    Matrix (PauliChainReplicaLiouvilleIndex k r) (PauliChainReplicaLiouvilleIndex k r) ℂ :=
  fun out inp =>
    ∑ q : (Fin r → Fin (2 ^ (k + 3))) × (Fin r → Fin (2 ^ (k + 3))), ∫ x,
      pauliChainReplicaLiouvilleAmplitudeAll k r q out inp x *
        Complex.exp (-((t * sortedSpectralAction (chainPauliFin_isHermitian (k + 3))
          (orderedReplicaActionCharacter q.1 q.2) (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
      ∂(volume.toSphere)

/-- Annealed quenched-centralizer projector: precisely the equal-histogram Liouville modes. -/
def pauliChainReplicaAveragedCentralizerProjector (k r : ℕ) :
    Matrix (PauliChainReplicaLiouvilleIndex k r) (PauliChainReplicaLiouvilleIndex k r) ℂ :=
  fun out inp =>
    ∑ q : (Fin r → Fin (2 ^ (k + 3))) × (Fin r → Fin (2 ^ (k + 3))),
      if orderedReplicaMultiplicity q.1 = orderedReplicaMultiplicity q.2 then
        ∫ x, pauliChainReplicaLiouvilleAmplitudeAll k r q out inp x ∂(volume.toSphere)
      else 0

/-- Annealed centered replica propagator on the fixed nearest-neighbour Pauli shell, in the exact
tensor-spectral-projector expansion.  Equal-histogram terms are the moving centralizer and have
already been subtracted. -/
def pauliChainReplicaCenteredAnnealedPropagator (k r : ℕ) (t : ℝ) :
    Matrix (PauliChainReplicaLiouvilleIndex k r) (PauliChainReplicaLiouvilleIndex k r) ℂ :=
  fun out inp =>
    ∑ q : OffHistogramReplicaPair (2 ^ (k + 3)) r, ∫ x,
      pauliChainReplicaLiouvilleAmplitude k r q out inp x *
        Complex.exp (-((t * sortedSpectralAction (chainPauliFin_isHermitian (k + 3))
          (orderedReplicaActionCharacter q.1.1 q.1.2) (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
      ∂(volume.toSphere)

/-- The off-histogram formula is exactly full annealed propagation minus the averaged moving
centralizer projector. -/
theorem pauliChainReplicaAnnealedPropagator_sub_averagedCentralizerProjector (k r : ℕ) (t : ℝ) :
    pauliChainReplicaAnnealedPropagator k r t -
        pauliChainReplicaAveragedCentralizerProjector k r =
      pauliChainReplicaCenteredAnnealedPropagator k r t := by
  classical
  ext out inp
  simp only [pauliChainReplicaAnnealedPropagator,
    pauliChainReplicaAveragedCentralizerProjector,
    pauliChainReplicaCenteredAnnealedPropagator, Matrix.sub_apply,
    ← Finset.sum_sub_distrib]
  let F := fun q : (Fin r → Fin (2 ^ (k + 3))) × (Fin r → Fin (2 ^ (k + 3))) =>
    ∫ x, pauliChainReplicaLiouvilleAmplitudeAll k r q out inp x *
      Complex.exp (-((t * sortedSpectralAction (chainPauliFin_isHermitian (k + 3))
        (orderedReplicaActionCharacter q.1 q.2) (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
      ∂(volume.toSphere)
  have hterm : ∀ q : (Fin r → Fin (2 ^ (k + 3))) × (Fin r → Fin (2 ^ (k + 3))),
      F q - (if orderedReplicaMultiplicity q.1 = orderedReplicaMultiplicity q.2 then
        ∫ x, pauliChainReplicaLiouvilleAmplitudeAll k r q out inp x ∂(volume.toSphere)
        else 0) =
      if orderedReplicaMultiplicity q.1 ≠ orderedReplicaMultiplicity q.2 then F q else 0 := by
    intro q
    by_cases hq : orderedReplicaMultiplicity q.1 = orderedReplicaMultiplicity q.2
    · rw [if_pos hq, if_neg (not_ne_iff.mpr hq)]
      have hchar : orderedReplicaActionCharacter q.1 q.2 = 0 :=
        (orderedReplicaActionCharacter_eq_zero_iff q.1 q.2).mpr hq
      simp [F, hchar, sortedSpectralAction]
    · rw [if_neg hq, if_pos hq, sub_zero]
  rw [Finset.sum_congr rfl fun q _ => hterm q]
  rw [← Finset.sum_filter (s := Finset.univ)
    (fun q => orderedReplicaMultiplicity q.1 ≠ orderedReplicaMultiplicity q.2) F]
  rw [Finset.sum_subtype (p := fun q : (Fin r → Fin (2 ^ (k + 3))) ×
      (Fin r → Fin (2 ^ (k + 3))) =>
        orderedReplicaMultiplicity q.1 ≠ orderedReplicaMultiplicity q.2)
    (Finset.univ.filter fun q =>
    orderedReplicaMultiplicity q.1 ≠ orderedReplicaMultiplicity q.2)
    (fun q => by simp) F]
  rfl

/-- **Equation (19), concrete fixed-shell form.**  At every replica order, the annealed static
nearest-neighbour Pauli propagator minus its moving-centralizer average converges to zero in
operator norm. -/
theorem pauliChainReplicaCenteredAnnealedPropagator_l2_opNorm_tendsto_zero (k r : ℕ) :
    Tendsto (fun t : ℝ => ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)
      (n := PauliChainReplicaLiouvilleIndex k r))
        (pauliChainReplicaCenteredAnnealedPropagator k r t)‖)
      (cocompact ℝ) (nhds 0) := by
  apply tendsto_pauliChain_offHistogramAnnealedMatrix_l2_opNorm_zero k r
    (pauliChainReplicaLiouvilleAmplitude k r)
  · exact measurable_pauliChainReplicaLiouvilleAmplitude k r
  · exact zero_le_one
  · exact norm_pauliChainReplicaLiouvilleAmplitude_le_one k r
  · intro t i j
    rfl

/-- **Equation (19), literal difference form.**  The full annealed replicated static propagator
converges in operator norm to the average of its quenched centralizer projector. -/
theorem pauliChainReplicaAnnealedPropagator_sub_averagedCentralizer_l2_opNorm_tendsto_zero
    (k r : ℕ) :
    Tendsto (fun t : ℝ => ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)
      (n := PauliChainReplicaLiouvilleIndex k r))
        (pauliChainReplicaAnnealedPropagator k r t -
          pauliChainReplicaAveragedCentralizerProjector k r)‖)
      (cocompact ℝ) (nhds 0) := by
  simpa only [pauliChainReplicaAnnealedPropagator_sub_averagedCentralizerProjector] using
    pauliChainReplicaCenteredAnnealedPropagator_l2_opNorm_tendsto_zero k r

end

end GaloisForLFunctions.HTGeometry
