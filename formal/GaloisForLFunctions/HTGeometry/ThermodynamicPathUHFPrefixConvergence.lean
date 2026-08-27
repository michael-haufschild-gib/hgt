import GaloisForLFunctions.HTGeometry.ThermodynamicPathUHFDynamics
import GaloisForLFunctions.HTGeometry.PathChainLabelIdentification

/-!
# Literal finite-path convergence to one UHF dynamics

Every finite path Hamiltonian obtained by restricting one countable Pauli field is embedded into
the qubit UHF algebra.  The embedding is identified term by term with the corresponding finite
partial sum of the infinite Hamiltonian.  Absolute coefficient summability then gives operator-norm
convergence of the Hamiltonians, compact-time-uniform convergence of their Schrödinger evolutions,
and compact-time-uniform point-norm convergence of their Heisenberg evolutions.

Thus finite-volume and infinite-volume dynamics are not separately selected objects: they are
literal restrictions and the norm limit of the same static nearest-neighbour field.
-/

open scoped BigOperators
open NormedSpace

namespace GaloisForLFunctions.HTGeometry

open PrimeQuasiLocalCharge

noncomputable section

noncomputable local instance primeUHFNormedAlgebraRatForPrefixes :
    NormedAlgebra ℚ (PrimeUHFAlgebra qubitLocalDim) :=
  NormedAlgebra.restrictScalars ℚ ℂ (PrimeUHFAlgebra qubitLocalDim)

/-- Every path word at stage `k` is exactly its countable UHF Pauli observable. -/
theorem qubitUHFPauli_pathWord (k : ℕ) (l : PathLabel (k + 1)) :
    qubitUHFPauli (k + 3) (pathWord l) =
      infinitePathUHFPauli (pathLabelToInfinite k l) := by
  rcases l with ⟨s, q⟩ | ⟨e, ab⟩
  · exact qubitUHFPauli_siteLabel_eq_infinite s q
  · exact qubitUHFPauli_adjacentPair_eq_infinite (k + 1) e ab

/-- Physical `(k+3)`-qubit path Hamiltonian embedded into the qubit UHF algebra. -/
def embeddedInfinitePathPrefixHamiltonian
    (p : InfinitePathLabel → ℝ) (k : ℕ) :
    PrimeUHFAlgebra qubitLocalDim :=
  matrixAFStageToUHF (k + 3)
    (qubitStageMatrix (k + 3)
      (pathHamiltonian (infinitePathPrefixShell k p)))

/-- Exact termwise identification of the physical finite path with one partial sum of the
countable field. -/
theorem embeddedInfinitePathPrefixHamiltonian_eq_sum
    (p : InfinitePathLabel → ℝ) (k : ℕ) :
    embeddedInfinitePathPrefixHamiltonian p k =
      ∑ l : PathLabel (k + 1),
        infinitePathUHFTerm p (pathLabelToInfinite k l) := by
  rw [embeddedInfinitePathPrefixHamiltonian, pathHamiltonian_eq_sum]
  rw [qubitStageMatrix_sum, map_sum]
  simp_rw [qubitStageMatrix_smul, map_smul]
  apply Finset.sum_congr rfl
  intro l _
  rw [infinitePathUHFTerm]
  change ((p (pathLabelToInfinite k l) : ℝ) : ℂ) •
      qubitUHFPauli (k + 3) (pathWord l) = _
  rw [qubitUHFPauli_pathWord]

/-- Three onsite Pauli terms at one site. -/
def infinitePathUHFOnsiteBlock (p : InfinitePathLabel → ℝ) (s : ℕ) :
    PrimeUHFAlgebra qubitLocalDim :=
  ∑ q : Fin 3, infinitePathUHFTerm p (Sum.inl (s, q))

/-- Nine two-site Pauli terms on one nearest-neighbour edge. -/
def infinitePathUHFEdgeBlock (p : InfinitePathLabel → ℝ) (e : ℕ) :
    PrimeUHFAlgebra qubitLocalDim :=
  ∑ ab : Fin 3 × Fin 3, infinitePathUHFTerm p (Sum.inr (e, ab))

theorem summable_infinitePathUHFOnsiteBlock
    {p : InfinitePathLabel → ℝ} (hp : Summable (fun i => |p i|)) :
    Summable (infinitePathUHFOnsiteBlock p) := by
  have hmass : Summable (fun sq : ℕ × Fin 3 => |p (Sum.inl sq)|) :=
    hp.comp_injective Sum.inl_injective
  have hblocks : Summable (fun s => ∑ q : Fin 3, |p (Sum.inl (s, q))|) := by
    simpa only [tsum_fintype] using hmass.prod
  apply hblocks.of_norm_bounded
  intro s
  calc
    ‖infinitePathUHFOnsiteBlock p s‖ ≤
        ∑ q : Fin 3, ‖infinitePathUHFTerm p (Sum.inl (s, q))‖ :=
      norm_sum_le _ _
    _ = ∑ q : Fin 3, |p (Sum.inl (s, q))| := by
      simp only [norm_infinitePathUHFTerm]

theorem summable_infinitePathUHFEdgeBlock
    {p : InfinitePathLabel → ℝ} (hp : Summable (fun i => |p i|)) :
    Summable (infinitePathUHFEdgeBlock p) := by
  have hmass : Summable
      (fun eab : ℕ × (Fin 3 × Fin 3) => |p (Sum.inr eab)|) :=
    hp.comp_injective Sum.inr_injective
  have hblocks : Summable
      (fun e => ∑ ab : Fin 3 × Fin 3, |p (Sum.inr (e, ab))|) := by
    simpa only [tsum_fintype] using hmass.prod
  apply hblocks.of_norm_bounded
  intro e
  calc
    ‖infinitePathUHFEdgeBlock p e‖ ≤
        ∑ ab : Fin 3 × Fin 3,
          ‖infinitePathUHFTerm p (Sum.inr (e, ab))‖ :=
      norm_sum_le _ _
    _ = ∑ ab : Fin 3 × Fin 3, |p (Sum.inr (e, ab))| := by
      simp only [norm_infinitePathUHFTerm]

/-- Onsite/edge decomposition of the bounded infinite-volume Hamiltonian. -/
theorem infinitePathUHFHamiltonian_eq_tsum_blocks
    {p : InfinitePathLabel → ℝ} (hp : Summable (fun i => |p i|)) :
    infinitePathUHFHamiltonian p =
      (∑' s, infinitePathUHFOnsiteBlock p s) +
        ∑' e, infinitePathUHFEdgeBlock p e := by
  have hs := summable_infinitePathUHFTerm hp
  have hon := hs.comp_injective (i := Sum.inl) Sum.inl_injective
  have hedge := hs.comp_injective (i := Sum.inr) Sum.inr_injective
  have honEq :
      (∑' sq : ℕ × Fin 3, infinitePathUHFTerm p (Sum.inl sq)) =
        ∑' s : ℕ, ∑' q : Fin 3,
          infinitePathUHFTerm p (Sum.inl (s, q)) := by
    simpa only [Function.comp_apply] using hon.tsum_prod
  have hedgeEq :
      (∑' eab : ℕ × (Fin 3 × Fin 3), infinitePathUHFTerm p (Sum.inr eab)) =
        ∑' e : ℕ, ∑' ab : Fin 3 × Fin 3,
          infinitePathUHFTerm p (Sum.inr (e, ab)) := by
    simpa only [Function.comp_apply] using hedge.tsum_prod
  rw [infinitePathUHFHamiltonian]
  calc
    ∑' i, infinitePathUHFTerm p i =
        (∑' sq : ℕ × Fin 3, infinitePathUHFTerm p (Sum.inl sq)) +
          ∑' eab : ℕ × (Fin 3 × Fin 3),
            infinitePathUHFTerm p (Sum.inr eab) :=
      (hon.hasSum.sum hedge.hasSum).tsum_eq
    _ = (∑' s, infinitePathUHFOnsiteBlock p s) +
          ∑' e, infinitePathUHFEdgeBlock p e := by
      rw [honEq, hedgeEq]
      simp only [infinitePathUHFOnsiteBlock, infinitePathUHFEdgeBlock,
        tsum_fintype]

theorem pathPrefixTermSum_eq_blockPartialSums
    (p : InfinitePathLabel → ℝ) (k : ℕ) :
    (∑ l : PathLabel (k + 1),
        infinitePathUHFTerm p (pathLabelToInfinite k l)) =
      (∑ s ∈ Finset.range (k + 3), infinitePathUHFOnsiteBlock p s) +
        ∑ e ∈ Finset.range (k + 2), infinitePathUHFEdgeBlock p e := by
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (infinitePathUHFOnsiteBlock p) (k + 3),
    ← Fin.sum_univ_eq_sum_range (infinitePathUHFEdgeBlock p) (k + 2)]
  simp [infinitePathUHFOnsiteBlock, infinitePathUHFEdgeBlock,
    pathLabelToInfinite, Fintype.sum_prod_type]

/-- Literal embedded finite-prefix Hamiltonians converge in operator norm to the infinite
Hamiltonian. -/
theorem tendsto_embeddedInfinitePathPrefixHamiltonian
    {p : InfinitePathLabel → ℝ} (hp : Summable (fun i => |p i|)) :
    Filter.Tendsto (embeddedInfinitePathPrefixHamiltonian p)
      Filter.atTop (nhds (infinitePathUHFHamiltonian p)) := by
  have hon := (summable_infinitePathUHFOnsiteBlock hp).hasSum.tendsto_sum_nat
  have hedge := (summable_infinitePathUHFEdgeBlock hp).hasSum.tendsto_sum_nat
  have hsum := (hon.comp (Filter.tendsto_add_atTop_nat 3)).add
    (hedge.comp (Filter.tendsto_add_atTop_nat 2))
  rw [infinitePathUHFHamiltonian_eq_tsum_blocks hp]
  convert hsum using 1
  funext k
  rw [embeddedInfinitePathPrefixHamiltonian_eq_sum,
    pathPrefixTermSum_eq_blockPartialSums]
  rfl

theorem isSelfAdjoint_embeddedInfinitePathPrefixHamiltonian
    (p : InfinitePathLabel → ℝ) (k : ℕ) :
    IsSelfAdjoint (embeddedInfinitePathPrefixHamiltonian p k) := by
  rw [embeddedInfinitePathPrefixHamiltonian_eq_sum, IsSelfAdjoint, star_sum]
  apply Finset.sum_congr rfl
  intro l _
  exact (isSelfAdjoint_infinitePathUHFTerm p (pathLabelToInfinite k l)).star_eq

/-- Schrödinger evolution of one embedded physical finite prefix. -/
def embeddedInfinitePathPrefixEvolution
    (p : InfinitePathLabel → ℝ) (k : ℕ) (t : ℝ) :
    PrimeUHFAlgebra qubitLocalDim :=
  exp (t • ((-Complex.I) • embeddedInfinitePathPrefixHamiltonian p k))

theorem norm_embeddedInfinitePathPrefixEvolution_sub_le
    {p : InfinitePathLabel → ℝ} (hp : Summable (fun i => |p i|))
    (k : ℕ) (t : ℝ) :
    ‖embeddedInfinitePathPrefixEvolution p k t -
        infinitePathUHFEvolution p t‖ ≤
      |t| * ‖embeddedInfinitePathPrefixHamiltonian p k -
        infinitePathUHFHamiltonian p‖ := by
  exact selfAdjoint_unitaryEvolution_norm_sub_le
    (embeddedInfinitePathPrefixHamiltonian p k)
    (infinitePathUHFHamiltonian p)
    (isSelfAdjoint_embeddedInfinitePathPrefixHamiltonian p k)
    (isSelfAdjoint_infinitePathUHFHamiltonian hp) t

/-- Finite-prefix Schrödinger evolutions converge uniformly on every compact time interval. -/
theorem embeddedInfinitePathPrefixEvolution_uniformOnCompact
    {p : InfinitePathLabel → ℝ} (hp : Summable (fun i => |p i|))
    (T ε : ℝ) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ K, ∀ k, K ≤ k → ∀ t : ℝ, |t| ≤ T →
      ‖embeddedInfinitePathPrefixEvolution p k t -
        infinitePathUHFEvolution p t‖ < ε := by
  have hden : 0 < T + 1 := by linarith
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp
    (tendsto_embeddedInfinitePathPrefixHamiltonian hp)
      (ε / (T + 1)) (div_pos hε hden)
  refine ⟨K, fun k hk t ht => ?_⟩
  have hnorm : ‖embeddedInfinitePathPrefixHamiltonian p k -
      infinitePathUHFHamiltonian p‖ < ε / (T + 1) := by
    simpa only [dist_eq_norm] using hK k hk
  calc
    ‖embeddedInfinitePathPrefixEvolution p k t -
        infinitePathUHFEvolution p t‖ ≤
        |t| * ‖embeddedInfinitePathPrefixHamiltonian p k -
          infinitePathUHFHamiltonian p‖ :=
      norm_embeddedInfinitePathPrefixEvolution_sub_le hp k t
    _ ≤ T * ‖embeddedInfinitePathPrefixHamiltonian p k -
          infinitePathUHFHamiltonian p‖ :=
      mul_le_mul_of_nonneg_right ht (norm_nonneg _)
    _ ≤ (T + 1) * ‖embeddedInfinitePathPrefixHamiltonian p k -
          infinitePathUHFHamiltonian p‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (T + 1) * (ε / (T + 1)) :=
      mul_lt_mul_of_pos_left hnorm hden
    _ = ε := by field_simp

/-- Heisenberg evolution of an observable under one embedded physical finite prefix. -/
def embeddedInfinitePathPrefixHeisenberg
    (p : InfinitePathLabel → ℝ) (k : ℕ) (t : ℝ)
    (A : PrimeUHFAlgebra qubitLocalDim) : PrimeUHFAlgebra qubitLocalDim :=
  star (embeddedInfinitePathPrefixEvolution p k t) * A *
    embeddedInfinitePathPrefixEvolution p k t

theorem embeddedInfinitePathPrefixEvolution_mem_unitary
    (p : InfinitePathLabel → ℝ) (k : ℕ) (t : ℝ) :
    embeddedInfinitePathPrefixEvolution p k t ∈
      unitary (PrimeUHFAlgebra qubitLocalDim) := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  apply skewAdjoint.smul_mem
  rw [skewAdjoint.mem_iff, star_smul,
    (isSelfAdjoint_embeddedInfinitePathPrefixHamiltonian p k).star_eq]
  simp

theorem norm_embeddedInfinitePathPrefixHeisenberg_sub_le
    {p : InfinitePathLabel → ℝ} (hp : Summable (fun i => |p i|))
    (k : ℕ) (t : ℝ) (A : PrimeUHFAlgebra qubitLocalDim) :
    ‖embeddedInfinitePathPrefixHeisenberg p k t A -
        infinitePathUHFHeisenberg p t A‖ ≤
      2 * |t| * ‖embeddedInfinitePathPrefixHamiltonian p k -
        infinitePathUHFHamiltonian p‖ * ‖A‖ := by
  have hU := embeddedInfinitePathPrefixEvolution_mem_unitary p k t
  have hV := infinitePathUHFEvolution_mem_unitary hp t
  have hconj := unitary_conjugation_norm_sub_le
    (star (embeddedInfinitePathPrefixEvolution p k t))
    (star (infinitePathUHFEvolution p t)) A
    (Unitary.star_mem hU) (Unitary.star_mem hV)
  have hevol := norm_embeddedInfinitePathPrefixEvolution_sub_le hp k t
  rw [← star_sub, norm_star] at hconj
  calc
    ‖embeddedInfinitePathPrefixHeisenberg p k t A -
        infinitePathUHFHeisenberg p t A‖ ≤
        2 * ‖embeddedInfinitePathPrefixEvolution p k t -
          infinitePathUHFEvolution p t‖ * ‖A‖ := by
      simpa [embeddedInfinitePathPrefixHeisenberg,
        infinitePathUHFHeisenberg] using hconj
    _ ≤ 2 * (|t| * ‖embeddedInfinitePathPrefixHamiltonian p k -
          infinitePathUHFHamiltonian p‖) * ‖A‖ := by
      gcongr
    _ = 2 * |t| * ‖embeddedInfinitePathPrefixHamiltonian p k -
          infinitePathUHFHamiltonian p‖ * ‖A‖ := by ring

/-- Finite-prefix Heisenberg evolutions converge point-norm uniformly on compact time intervals. -/
theorem embeddedInfinitePathPrefixHeisenberg_uniformOnCompact
    {p : InfinitePathLabel → ℝ} (hp : Summable (fun i => |p i|))
    (A : PrimeUHFAlgebra qubitLocalDim)
    (T ε : ℝ) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ K, ∀ k, K ≤ k → ∀ t : ℝ, |t| ≤ T →
      ‖embeddedInfinitePathPrefixHeisenberg p k t A -
        infinitePathUHFHeisenberg p t A‖ < ε := by
  let δ := ε / (2 * (‖A‖ + 1))
  have hfactor : 0 < 2 * (‖A‖ + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hfactor
  obtain ⟨K, hK⟩ :=
    embeddedInfinitePathPrefixEvolution_uniformOnCompact hp T δ hT hδ
  refine ⟨K, fun k hk t ht => ?_⟩
  have hevol := hK k hk t ht
  have hU := embeddedInfinitePathPrefixEvolution_mem_unitary p k t
  have hV := infinitePathUHFEvolution_mem_unitary hp t
  have hconj := unitary_conjugation_norm_sub_le
    (star (embeddedInfinitePathPrefixEvolution p k t))
    (star (infinitePathUHFEvolution p t)) A
    (Unitary.star_mem hU) (Unitary.star_mem hV)
  rw [← star_sub, norm_star] at hconj
  calc
    ‖embeddedInfinitePathPrefixHeisenberg p k t A -
        infinitePathUHFHeisenberg p t A‖ ≤
        2 * ‖embeddedInfinitePathPrefixEvolution p k t -
          infinitePathUHFEvolution p t‖ * ‖A‖ := by
      simpa [embeddedInfinitePathPrefixHeisenberg,
        infinitePathUHFHeisenberg] using hconj
    _ ≤ 2 * ‖embeddedInfinitePathPrefixEvolution p k t -
          infinitePathUHFEvolution p t‖ * (‖A‖ + 1) := by
      gcongr
      linarith [norm_nonneg A]
    _ = (2 * (‖A‖ + 1)) *
          ‖embeddedInfinitePathPrefixEvolution p k t -
            infinitePathUHFEvolution p t‖ := by ring
    _ < (2 * (‖A‖ + 1)) * δ :=
      mul_lt_mul_of_pos_left hevol hfactor
    _ = ε := by
      dsimp [δ]
      field_simp

end

end GaloisForLFunctions.HTGeometry
