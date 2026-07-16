import GaloisForLFunctions.HTGeometry.HolographicCommutatorRank
import GaloisForLFunctions.HTGeometry.DirectionalProjectiveCompleteRealization

/-!
# Universal free horizons have maximal commutator rank

The complete free-word realization of an arbitrary projective hypertranscendence horizon does not
merely use some noncommutativity.  Evaluation of its law commutators on one tail root records the
two oriented length-two tail generators.  Their algebraic independence supplies a linear decoder
back to the second exterior power of law space.  The decoder is a left inverse to the commutator
map, so that map is injective.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

universe u v

variable {K : Type u} {ι η : Type v} [Field K] [CharZero K]
  [Fintype ι] [Fintype η]

/-- Package the finite family of complete free-word derivations as a linear law map. -/
def projectiveCompleteLawMap
    (a : η → ProjectiveWordState ι → K) (d : ℕ) :
    (ι → K) →ₗ[K] Derivation K (ProjectiveCompleteField K ι η)
      (ProjectiveCompleteField K ι η) where
  toFun := directionalDerivation (projectiveCompleteDerivation a d)
  map_add' c e := by
    classical
    simp [directionalDerivation, add_smul, Finset.sum_add_distrib]
  map_smul' r c := by
    classical
    simp [directionalDerivation, Finset.smul_sum, smul_smul]

omit [CharZero K] in
@[simp]
theorem projectiveCompleteLawMap_basisFun
    (a : η → ProjectiveWordState ι → K) (d : ℕ) (i : ι) :
    projectiveCompleteLawMap a d (Pi.basisFun K ι i) =
      projectiveCompleteDerivation a d i := by
  classical
  ext z
  simp [projectiveCompleteLawMap, directionalDerivation]

/-- The oriented length-two tail generator selected by an ordered pair of laws. -/
def projectiveCompleteTailPair (j : η) (p : ι × ι) :
    ProjectiveCompleteField K ι η :=
  projectiveCompleteTail (K := K) j 2 ![p.1, p.2]

def projectiveCompleteTailPairEmbedding (j : η) :
    ι × ι ↪ ProjectiveCompleteGenerator ι η where
  toFun p := Sum.inr (j, ⟨2, ![p.1, p.2]⟩)
  inj' := by
    intro p q h
    have hw : (![p.1, p.2] : Fin 2 → ι) = ![q.1, q.2] := by
      simpa using h
    exact Prod.ext (congrFun hw 0) (congrFun hw 1)

omit [CharZero K] [Fintype ι] [Fintype η] in
theorem projectiveCompleteTailPair_algebraicIndependent (j : η) :
    AlgebraicIndependent K
      (projectiveCompleteTailPair (K := K) (ι := ι) (η := η) j) := by
  have h :=
    (projectiveCompleteGenerator_algebraicIndependent (K := K) (ι := ι) (η := η)).comp
      (projectiveCompleteTailPairEmbedding (ι := ι) (η := η) j)
      (projectiveCompleteTailPairEmbedding (ι := ι) (η := η) j).injective
  simpa [projectiveCompleteTailPair, projectiveCompleteTailPairEmbedding,
    projectiveCompleteTail, projectiveCompleteEmbedding] using h

/-- The basis wedge assigned to an oriented tail pair. -/
def projectiveCompleteTailPairWedge (p : ι × ι) :
    ⋀[K]^2 (ι → K) :=
  exteriorPower.ιMulti K 2 ![Pi.basisFun K ι p.1, Pi.basisFun K ι p.2]

/-- Decode the independent length-two tail family on its linear span. -/
def projectiveCompleteTailPairSpanDecoder (j : η) :
    Submodule.span K (Set.range
      (projectiveCompleteTailPair (K := K) (ι := ι) (η := η) j)) →ₗ[K]
      ⋀[K]^2 (ι → K) :=
  (Finsupp.linearCombination K fun p : ι × ι ↦
    (2 : K)⁻¹ • projectiveCompleteTailPairWedge (K := K) p).comp
      (projectiveCompleteTailPair_algebraicIndependent
        (K := K) (ι := ι) (η := η) j).linearIndependent.repr

/-- Extend the tail-pair decoder from its span to the whole free rational field. -/
noncomputable def projectiveCompleteTailPairDecoder (j : η) :
    ProjectiveCompleteField K ι η →ₗ[K] ⋀[K]^2 (ι → K) :=
  Classical.choose (LinearMap.exists_extend
    (projectiveCompleteTailPairSpanDecoder (K := K) j))

omit [CharZero K] [Fintype η] in
theorem projectiveCompleteTailPairDecoder_apply (j : η) (p : ι × ι) :
    projectiveCompleteTailPairDecoder (K := K) j
        (projectiveCompleteTailPair (K := K) (ι := ι) (η := η) j p) =
      (2 : K)⁻¹ • projectiveCompleteTailPairWedge (K := K) p := by
  have hp : projectiveCompleteTailPair (K := K) (ι := ι) (η := η) j p ∈
      Submodule.span K (Set.range
        (projectiveCompleteTailPair (K := K) (ι := ι) (η := η) j)) :=
    Submodule.subset_span (Set.mem_range_self p)
  have hext := LinearMap.congr_fun
    (Classical.choose_spec (LinearMap.exists_extend
      (projectiveCompleteTailPairSpanDecoder (K := K) j)))
    ⟨projectiveCompleteTailPair (K := K) (ι := ι) (η := η) j p, hp⟩
  rw [LinearMap.comp_apply] at hext
  have hrepr :=
    (projectiveCompleteTailPair_algebraicIndependent
      (K := K) (ι := ι) (η := η) j).linearIndependent.repr_eq_single
      p ⟨projectiveCompleteTailPair (K := K) (ι := ι) (η := η) j p, hp⟩ rfl
  calc
    projectiveCompleteTailPairDecoder (K := K) j
        (projectiveCompleteTailPair (K := K) (ι := ι) (η := η) j p) =
        projectiveCompleteTailPairSpanDecoder (K := K) j
          ⟨projectiveCompleteTailPair (K := K) (ι := ι) (η := η) j p, hp⟩ := by
      simpa [projectiveCompleteTailPairDecoder] using hext
    _ = (2 : K)⁻¹ • projectiveCompleteTailPairWedge (K := K) p := by
      unfold projectiveCompleteTailPairSpanDecoder
      rw [LinearMap.comp_apply, hrepr]
      simp

/-- Evaluate a derivation on one fixed tail root. -/
def projectiveCompleteDerivationEvaluation (j : η) :
    Derivation K (ProjectiveCompleteField K ι η) (ProjectiveCompleteField K ι η) →ₗ[K]
      ProjectiveCompleteField K ι η where
  toFun D := D (projectiveCompleteTail (K := K) j 0 Fin.elim0)
  map_add' D E := by simp
  map_smul' c D := by simp

omit [CharZero K] [Fintype ι] in
theorem projectiveCompleteCommutator_evaluation
    (a : η → ProjectiveWordState ι → K) (d : ℕ) (j : η) (i k : ι) :
    projectiveCompleteDerivationEvaluation (K := K) j
        ⁅projectiveCompleteDerivation a d i, projectiveCompleteDerivation a d k⁆ =
      projectiveCompleteTailPair (K := K) j (i, k) -
        projectiveCompleteTailPair (K := K) j (k, i) := by
  simp [projectiveCompleteDerivationEvaluation, Derivation.commutator_apply,
    projectiveCompleteTailPair, projectiveCompleteDerivation_tail]
  have hik : Fin.cons i (Fin.cons k Fin.elim0) = (![i, k] : Fin 2 → ι) := by
    funext r
    fin_cases r <;> rfl
  have hki : Fin.cons k (Fin.cons i Fin.elim0) = (![k, i] : Fin 2 → ι) := by
    funext r
    fin_cases r <;> rfl
  rw [hik, hki]

/-- Evaluation followed by the tail decoder, composed with the free commutator map. -/
def decodedProjectiveCompleteCommutatorMap
    (a : η → ProjectiveWordState ι → K) (d : ℕ) (j : η) :
    (⋀[K]^2 (ι → K)) →ₗ[K] ⋀[K]^2 (ι → K) :=
  (projectiveCompleteTailPairDecoder (K := K) j).comp
    ((projectiveCompleteDerivationEvaluation (K := K) j).comp
      (derivationCommutatorMap (projectiveCompleteLawMap a d)))

/-- The decoded free commutator map is the identity on the second exterior law space. -/
theorem decodedProjectiveCompleteCommutatorMap_eq_id
    (a : η → ProjectiveWordState ι → K) (d : ℕ) (j : η) :
    decodedProjectiveCompleteCommutatorMap a d j = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply (Pi.basisFun K ι).ext_alternating
  intro f hf
  have hne : f 0 ≠ f 1 := by
    intro h
    exact Fin.zero_ne_one (hf h)
  change projectiveCompleteTailPairDecoder (K := K) j
      (projectiveCompleteDerivationEvaluation (K := K) j
        (derivationCommutatorMap (projectiveCompleteLawMap a d)
          (exteriorPower.ιMulti K 2
            ![Pi.basisFun K ι (f 0), Pi.basisFun K ι (f 1)]))) = _
  rw [derivationCommutatorMap_wedge,
    projectiveCompleteLawMap_basisFun, projectiveCompleteLawMap_basisFun,
    projectiveCompleteCommutator_evaluation,
    map_sub, projectiveCompleteTailPairDecoder_apply,
    projectiveCompleteTailPairDecoder_apply]
  change (2 : K)⁻¹ • exteriorPower.ιMulti K 2
      ![Pi.basisFun K ι (f 0), Pi.basisFun K ι (f 1)] -
    (2 : K)⁻¹ • exteriorPower.ιMulti K 2
      ![Pi.basisFun K ι (f 1), Pi.basisFun K ι (f 0)] = _
  have hswap : exteriorPower.ιMulti K 2
      ![Pi.basisFun K ι (f 1), Pi.basisFun K ι (f 0)] =
      -exteriorPower.ιMulti K 2
        ![Pi.basisFun K ι (f 0), Pi.basisFun K ι (f 1)] := by
    simpa [Function.comp_def] using
      (exteriorPower.ιMulti K 2).map_swap
        (![Pi.basisFun K ι (f 0), Pi.basisFun K ι (f 1)]) Fin.zero_ne_one
  rw [hswap, smul_neg, sub_neg_eq_add, ← add_smul]
  have hhalf : (2 : K)⁻¹ + (2 : K)⁻¹ = 1 := by
    field_simp
    ring
  rw [hhalf, one_smul]
  simp
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **Maximal free-horizon commutator theorem.**  For a nonempty terminal packet, the second
exterior commutator symbol of the complete free-word horizon realization is injective. -/
theorem projectiveComplete_commutatorMap_injective
    (a : η → ProjectiveWordState ι → K) (d : ℕ) [Nonempty η] :
    Function.Injective (derivationCommutatorMap (projectiveCompleteLawMap a d)) := by
  let j : η := Classical.choice inferInstance
  intro z z' h
  have hdecoded := congrArg
    (fun D ↦ projectiveCompleteTailPairDecoder (K := K) j
      (projectiveCompleteDerivationEvaluation (K := K) j D)) h
  change decodedProjectiveCompleteCommutatorMap a d j z =
    decodedProjectiveCompleteCommutatorMap a d j z' at hdecoded
  simpa [decodedProjectiveCompleteCommutatorMap_eq_id] using hdecoded

end

end GaloisForLFunctions.HTGeometry
