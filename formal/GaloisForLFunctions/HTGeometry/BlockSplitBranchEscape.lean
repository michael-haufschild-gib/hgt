import GaloisForLFunctions.HTGeometry.BlockSplitSpectrum
import GaloisForLFunctions.HTGeometry.ReciprocalSumNonvanishing

/-!
# The block splitting as an analytic family through a diagonal base

The transverse coupling enters the Hamiltonian affinely, so the block splitting is an analytic
matrix family in the coupling, and at coupling zero it is the diagonal Hamiltonian whose entries are
the unsplit block energies.  That is exactly the input of the analytic branch machinery: a simple
diagonal base with an analytic family through it.

Along the real coupling axis the explicit block roots are continuous characteristic roots through
that base, so branch identification makes them the analytic branches, and the block-split escape
applies to the branches themselves.
-/

open scoped BigOperators Matrix.Norms.Elementwise
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- The pure transverse coupling direction. -/
def offCouplingMatrix (Z : Type*) [Fintype Z] [DecidableEq Z] :
    Matrix (Fin 2 × Z) (Fin 2 × Z) ℂ :=
  Matrix.blockDiagonal fun _ : Z => Matrix.of ![![0, 1], ![1, 0]]

theorem blockSplitMatrix_eq_add_smul (m d : Z → ℝ) (u : ℂ) :
    blockSplitMatrix m d u = blockSplitMatrix m d 0 + u • offCouplingMatrix Z := by
  ext p q
  obtain ⟨i, z⟩ := p
  obtain ⟨j, z'⟩ := q
  by_cases hz : z = z'
  · subst hz
    simp only [blockSplitMatrix, offCouplingMatrix, Matrix.blockDiagonal_apply_eq,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [splitBlock]
  · simp only [blockSplitMatrix, offCouplingMatrix, Matrix.blockDiagonal_apply, if_neg hz,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

/-- The block splitting is an analytic family in the transverse coupling. -/
theorem analyticAt_blockSplitMatrix (m d : Z → ℝ) (u₀ : ℂ) :
    AnalyticAt ℂ (fun u : ℂ => blockSplitMatrix m d u) u₀ := by
  have hfun : (fun u : ℂ => blockSplitMatrix m d u)
      = fun u : ℂ => blockSplitMatrix m d 0 + u • offCouplingMatrix Z := by
    funext u
    exact blockSplitMatrix_eq_add_smul m d u
  rw [hfun]
  exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)

/-- The unsplit block energies. -/
def blockEnergy (m d : Z → ℝ) : Fin 2 × Z → ℝ :=
  fun p => m p.2 + (if p.1 = 1 then -1 else 1) * d p.2

omit [Fintype Z] in
/-- At zero coupling the block splitting is the diagonal Hamiltonian of the block energies. -/
theorem blockSplitMatrix_zero (m d : Z → ℝ) :
    blockSplitMatrix m d 0
      = Matrix.diagonal fun p => ((blockEnergy m d p : ℝ) : ℂ) := by
  ext p q
  obtain ⟨i, z⟩ := p
  obtain ⟨j, z'⟩ := q
  by_cases hz : z = z'
  · subst hz
    simp only [blockSplitMatrix, Matrix.blockDiagonal_apply_eq]
    fin_cases i <;> fin_cases j <;>
      simp [splitBlock, blockEnergy, Prod.ext_iff, sub_eq_add_neg]
  · have hpq : ((i, z) : Fin 2 × Z) ≠ (j, z') := fun h => hz (congrArg Prod.snd h)
    simp only [blockSplitMatrix, Matrix.blockDiagonal_apply, if_neg hz,
      Matrix.diagonal_apply_ne _ hpq]

/-- The real block root path. -/
def blockSplitRoot (m d : Z → ℝ) (p : Fin 2 × Z) (u : ℝ) : ℝ :=
  m p.2 + (if p.1 = 1 then -1 else 1) * Real.sqrt (d p.2 ^ (2 : ℕ) + u ^ (2 : ℕ))

omit [Fintype Z] [DecidableEq Z] in
theorem blockSplitRoot_zero_eq (m d : Z → ℝ) (hd : ∀ z, 0 < d z) (p : Fin 2 × Z) :
    blockSplitRoot m d p 0 = blockEnergy m d p := by
  rw [blockSplitRoot, blockEnergy]
  have hsq : Real.sqrt (d p.2 ^ (2 : ℕ) + 0 ^ (2 : ℕ)) = d p.2 := by
    rw [show d p.2 ^ (2 : ℕ) + 0 ^ (2 : ℕ) = d p.2 ^ (2 : ℕ) by ring, Real.sqrt_sq (hd p.2).le]
  rw [hsq]

omit [Fintype Z] [DecidableEq Z] in
theorem continuous_blockSplitRoot_real (m d : Z → ℝ) (p : Fin 2 × Z) :
    Continuous fun u : ℝ => ((blockSplitRoot m d p u : ℝ) : ℂ) := by
  have hsqrt : Continuous fun u : ℝ => Real.sqrt (d p.2 ^ (2 : ℕ) + u ^ (2 : ℕ)) :=
    Real.continuous_sqrt.comp (by fun_prop)
  exact Complex.continuous_ofReal.comp (by unfold blockSplitRoot; fun_prop)

/-- Every real block root path is a characteristic root of the family. -/
theorem matrixCharpolyRelation_blockSplitRoot (m d : Z → ℝ) (p : Fin 2 × Z) (u : ℝ) :
    matrixCharpolyRelation (blockSplitMatrix m d (u : ℂ),
        ((blockSplitRoot m d p u : ℝ) : ℂ)) = 0 := by
  classical
  have h := matrixCharpolyRelation_blockSplitMatrix_root m d u p.2 (decide (p.1 = 1))
  simpa [blockSplitRoot] using h


omit [DecidableEq Z] in
/-- Grouping a character over the two members of each block. -/
theorem sum_blockSplitRoot_eq (m d : Z → ℝ) (k : Fin 2 × Z → ℝ) (u : ℝ) :
    (∑ p : Fin 2 × Z, k p * blockSplitRoot m d p u)
      = blockSplitRelation (∑ z, (k (0, z) + k (1, z)) * m z)
          (fun z => k (0, z) - k (1, z)) d u := by
  classical
  rw [blockSplitRelation, Fintype.sum_prod_type, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Fin.sum_univ_two]
  simp only [blockSplitRoot]
  norm_num
  ring


/-- **Branch-level block escape.**  If the block differences of a character weight the reciprocal
gaps nontrivially, then arbitrarily small transverse couplings make the character's relation among
the analytic eigenvalue branches nonzero. -/
theorem exists_split_branch_relation_ne_zero (m d : Z → ℝ) (hd : ∀ z, 0 < d z)
    (hinj : Function.Injective fun p : Fin 2 × Z => ((blockEnergy m d p : ℝ) : ℂ))
    (branch : Fin 2 × Z → ℂ → ℂ)
    (hbranchA : ∀ p, AnalyticAt ℂ (branch p) 0)
    (hbranch0 : ∀ p, branch p 0 = ((blockEnergy m d p : ℝ) : ℂ))
    (hbranchRoot : ∀ p, ∀ᶠ v in 𝓝 (0 : ℂ),
      matrixCharpolyRelation (blockSplitMatrix m d v, branch p v) = 0)
    (k : Fin 2 × Z → ℝ)
    (hweight : (∑ z, (k (0, z) - k (1, z)) * (1 / |d z|)) ≠ 0)
    {V : Set ℝ} (hV : V ∈ 𝓝 (0 : ℝ)) :
    ∃ u ∈ V, (∑ p : Fin 2 × Z, (k p : ℂ) * branch p (u : ℂ)) ≠ 0 := by
  classical
  have hofReal : Filter.Tendsto (fun u : ℝ => (u : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
    have h := Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))
    rw [ContinuousAt, Complex.ofReal_zero] at h
    exact h
  have hfam : Filter.Tendsto (fun u : ℝ => blockSplitMatrix m d (u : ℂ)) (𝓝 0)
      (𝓝 (Matrix.diagonal fun q => ((blockEnergy m d q : ℝ) : ℂ))) := by
    have hcont : Filter.Tendsto (fun u : ℝ => blockSplitMatrix m d (u : ℂ)) (𝓝 0)
        (𝓝 (blockSplitMatrix m d ((0 : ℝ) : ℂ))) :=
      (((continuous_blockSplitMatrix m d).comp Complex.continuous_ofReal).continuousAt
        (x := (0 : ℝ)))
    rw [Complex.ofReal_zero, blockSplitMatrix_zero] at hcont
    exact hcont
  have hagree : ∀ p : Fin 2 × Z,
      ∀ᶠ u : ℝ in 𝓝 0, ((blockSplitRoot m d p u : ℝ) : ℂ) = branch p (u : ℂ) := by
    intro p
    have hs : Filter.Tendsto (fun u : ℝ => ((blockSplitRoot m d p u : ℝ) : ℂ)) (𝓝 0)
        (𝓝 (((blockEnergy m d p : ℝ) : ℂ))) := by
      have hcont := (continuous_blockSplitRoot_real m d p).continuousAt (x := (0 : ℝ))
      rwa [ContinuousAt, blockSplitRoot_zero_eq m d hd p] at hcont
    have ht : Filter.Tendsto (fun u : ℝ => branch p (u : ℂ)) (𝓝 0)
        (𝓝 (((blockEnergy m d p : ℝ) : ℂ))) := by
      have h1 : Filter.Tendsto (branch p) (𝓝 (0 : ℂ)) (𝓝 (branch p 0)) :=
        (hbranchA p).continuousAt
      have h2 := h1.comp hofReal
      rwa [hbranch0 p] at h2
    exact simpleDiagonalMatrix_root_germs_unique
      (fun q => ((blockEnergy m d q : ℝ) : ℂ)) hinj p hfam hs ht
      (Filter.Eventually.of_forall fun u => matrixCharpolyRelation_blockSplitRoot m d p u)
      (hofReal.eventually (hbranchRoot p))
  have hall : ∀ᶠ u : ℝ in 𝓝 0,
      ∀ p : Fin 2 × Z, ((blockSplitRoot m d p u : ℝ) : ℂ) = branch p (u : ℂ) :=
    Filter.eventually_all.2 hagree
  obtain ⟨u, huV, hune⟩ :=
    exists_ne_zero_blockSplitRelation (∑ z, (k (0, z) + k (1, z)) * m z)
      (fun z => k (0, z) - k (1, z)) d (fun z => ne_of_gt (hd z)) hweight
      (Filter.inter_mem hV hall)
  refine ⟨u, huV.1, ?_⟩
  have hsum : (∑ p : Fin 2 × Z, (k p : ℂ) * branch p (u : ℂ))
      = ((∑ p : Fin 2 × Z, k p * blockSplitRoot m d p u : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [huV.2 p]
  rw [hsum, sum_blockSplitRoot_eq]
  intro hcon
  exact hune (Complex.ofReal_eq_zero.mp hcon)


/-- **Shift selection for the branch escape.**  For pairwise distinct base gaps and a character with
one nonzero block difference, arbitrarily large diagonal shifts make every gap positive and the
reciprocal-gap weight nonzero, which is exactly the hypothesis of the branch-level escape. -/
theorem exists_shift_blockWeight_ne_zero (a : Z → ℝ) (hinj : Function.Injective a)
    (k : Fin 2 × Z → ℝ) {z₀ : Z} (hk : k (0, z₀) - k (1, z₀) ≠ 0) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ (∀ z, 0 < a z + t) ∧
      (∑ z, (k (0, z) - k (1, z)) * (1 / |a z + t|)) ≠ 0 := by
  obtain ⟨t, htT, hpos, hsum⟩ :=
    exists_large_reciprocalSum_ne_zero (β := fun z => k (0, z) - k (1, z)) hinj hk T
  refine ⟨t, htT, hpos, ?_⟩
  have hweight : (∑ z, (k (0, z) - k (1, z)) * (1 / |a z + t|))
      = ∑ z, (k (0, z) - k (1, z)) / (a z + t) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [abs_of_pos (hpos z), mul_one_div]
  rw [hweight]
  exact hsum


/-! ## Shifting the block gaps while splitting -/

/-- The two-parameter block family: a uniform shift of every block gap together with a transverse
coupling. -/
def shiftedBlockSplitMatrix (m d : Z → ℝ) (q : ℝ × ℝ) : Matrix (Fin 2 × Z) (Fin 2 × Z) ℂ :=
  blockSplitMatrix m (fun z => d z + q.1) (q.2 : ℂ)

/-- The corresponding two-parameter block root paths. -/
def shiftedBlockSplitRoot (m d : Z → ℝ) (p : Fin 2 × Z) (q : ℝ × ℝ) : ℝ :=
  blockSplitRoot m (fun z => d z + q.1) p q.2

omit [Fintype Z] in
theorem shiftedBlockSplitMatrix_zero (m d : Z → ℝ) :
    shiftedBlockSplitMatrix m d (0, 0)
      = Matrix.diagonal fun p => ((blockEnergy m d p : ℝ) : ℂ) := by
  have hd : (fun z => d z + (0 : ℝ)) = d := by funext z; ring
  show blockSplitMatrix m (fun z => d z + (0 : ℝ)) ((0 : ℝ) : ℂ) = _
  rw [hd, Complex.ofReal_zero]
  exact blockSplitMatrix_zero m d

omit [Fintype Z] [DecidableEq Z] in
theorem shiftedBlockSplitRoot_zero_eq (m d : Z → ℝ) (hd : ∀ z, 0 < d z) (p : Fin 2 × Z) :
    shiftedBlockSplitRoot m d p (0, 0) = blockEnergy m d p := by
  have hshift : (fun z => d z + (0 : ℝ)) = d := by funext z; ring
  show blockSplitRoot m (fun z => d z + (0 : ℝ)) p 0 = _
  rw [hshift]
  exact blockSplitRoot_zero_eq m d hd p

omit [Fintype Z] in
theorem continuous_shiftedBlockSplitMatrix (m d : Z → ℝ) :
    Continuous (shiftedBlockSplitMatrix m d) := by
  classical
  refine continuous_matrix fun p q => ?_
  obtain ⟨i, z⟩ := p
  obtain ⟨j, z'⟩ := q
  by_cases hz : z = z'
  · subst hz
    simp only [shiftedBlockSplitMatrix, blockSplitMatrix, Matrix.blockDiagonal_apply_eq]
    fin_cases i <;> fin_cases j <;> simp [splitBlock] <;> fun_prop
  · simp only [shiftedBlockSplitMatrix, blockSplitMatrix, Matrix.blockDiagonal_apply, if_neg hz]
    exact continuous_const

omit [Fintype Z] [DecidableEq Z] in
theorem continuous_shiftedBlockSplitRoot (m d : Z → ℝ) (p : Fin 2 × Z) :
    Continuous fun q : ℝ × ℝ => ((shiftedBlockSplitRoot m d p q : ℝ) : ℂ) := by
  have hsqrt : Continuous fun q : ℝ × ℝ => Real.sqrt ((d p.2 + q.1) ^ (2 : ℕ) + q.2 ^ (2 : ℕ)) :=
    Real.continuous_sqrt.comp (by fun_prop)
  exact Complex.continuous_ofReal.comp
    (by unfold shiftedBlockSplitRoot blockSplitRoot; fun_prop)

/-- Every shifted block root path is a characteristic root of the shifted family. -/
theorem matrixCharpolyRelation_shiftedBlockSplitRoot (m d : Z → ℝ) (p : Fin 2 × Z) (q : ℝ × ℝ) :
    matrixCharpolyRelation (shiftedBlockSplitMatrix m d q,
        ((shiftedBlockSplitRoot m d p q : ℝ) : ℂ)) = 0 :=
  matrixCharpolyRelation_blockSplitRoot m (fun z => d z + q.1) p q.2

omit [DecidableEq Z] in
theorem sum_shiftedBlockSplitRoot_eq (m d : Z → ℝ) (k : Fin 2 × Z → ℝ) (q : ℝ × ℝ) :
    (∑ p : Fin 2 × Z, k p * shiftedBlockSplitRoot m d p q)
      = blockSplitRelation (∑ z, (k (0, z) + k (1, z)) * m z)
          (fun z => k (0, z) - k (1, z)) (fun z => d z + q.1) q.2 :=
  sum_blockSplitRoot_eq m (fun z => d z + q.1) k q.2

/-- **Branch-level block escape from every constant.** For pairwise
distinct positive block gaps, a character with one nonzero block
difference cannot remain equal to any prescribed constant near the
unsplit point. No genericity of the base is needed: a small gap shift
makes the reciprocal-gap curvature nonzero, and a transverse coupling
then changes the spectral action. -/
theorem exists_shifted_split_branch_relation_ne_const (m d : Z → ℝ) (hd : ∀ z, 0 < d z)
    (hdinj : Function.Injective d)
    (hinj : Function.Injective fun p : Fin 2 × Z => ((blockEnergy m d p : ℝ) : ℂ))
    (branch : Fin 2 × Z → ℝ × ℝ → ℂ)
    (hbranchC : ∀ p, ContinuousAt (branch p) (0, 0))
    (hbranch0 : ∀ p, branch p (0, 0) = ((blockEnergy m d p : ℝ) : ℂ))
    (hbranchRoot : ∀ p, ∀ᶠ q in 𝓝 ((0, 0) : ℝ × ℝ),
      matrixCharpolyRelation (shiftedBlockSplitMatrix m d q, branch p q) = 0)
    (k : Fin 2 × Z → ℝ) {z₀ : Z} (hk : k (0, z₀) - k (1, z₀) ≠ 0)
    (target : ℝ)
    {W : Set (ℝ × ℝ)} (hW : W ∈ 𝓝 ((0, 0) : ℝ × ℝ)) :
    ∃ q ∈ W, (∑ p : Fin 2 × Z, (k p : ℂ) * branch p q) ≠ (target : ℂ) := by
  classical
  have hfam : Filter.Tendsto (shiftedBlockSplitMatrix m d) (𝓝 ((0, 0) : ℝ × ℝ))
      (𝓝 (Matrix.diagonal fun p => ((blockEnergy m d p : ℝ) : ℂ))) := by
    have hcont := (continuous_shiftedBlockSplitMatrix m d).continuousAt (x := ((0, 0) : ℝ × ℝ))
    rwa [ContinuousAt, shiftedBlockSplitMatrix_zero] at hcont
  have hagree : ∀ p : Fin 2 × Z, ∀ᶠ q in 𝓝 ((0, 0) : ℝ × ℝ),
      ((shiftedBlockSplitRoot m d p q : ℝ) : ℂ) = branch p q := by
    intro p
    have hs : Filter.Tendsto (fun q : ℝ × ℝ => ((shiftedBlockSplitRoot m d p q : ℝ) : ℂ))
        (𝓝 ((0, 0) : ℝ × ℝ)) (𝓝 (((blockEnergy m d p : ℝ) : ℂ))) := by
      have hcont := (continuous_shiftedBlockSplitRoot m d p).continuousAt (x := ((0, 0) : ℝ × ℝ))
      rwa [ContinuousAt, shiftedBlockSplitRoot_zero_eq m d hd p] at hcont
    have ht : Filter.Tendsto (branch p) (𝓝 ((0, 0) : ℝ × ℝ))
        (𝓝 (((blockEnergy m d p : ℝ) : ℂ))) := by
      have hcont := hbranchC p
      rwa [ContinuousAt, hbranch0 p] at hcont
    exact simpleDiagonalMatrix_root_germs_unique
      (fun q => ((blockEnergy m d q : ℝ) : ℂ)) hinj p hfam hs ht
      (Filter.Eventually.of_forall fun q => matrixCharpolyRelation_shiftedBlockSplitRoot m d p q)
      (hbranchRoot p)
  have hall : ∀ᶠ q in 𝓝 ((0, 0) : ℝ × ℝ),
      ∀ p : Fin 2 × Z, ((shiftedBlockSplitRoot m d p q : ℝ) : ℂ) = branch p q :=
    Filter.eventually_all.2 hagree
  obtain ⟨W₁, hW₁, W₂, hW₂, hsub⟩ := mem_nhds_prod_iff.mp (Filter.inter_mem hW hall)
  obtain ⟨t, htW, hposT, hsumT⟩ :=
    exists_small_reciprocalSum_ne_zero (a := d) (β := fun z => k (0, z) - k (1, z)) hdinj hk hd hW₁
  have hweight : (∑ z, (k (0, z) - k (1, z)) * (1 / |d z + t|)) ≠ 0 := by
    have hrewrite : (∑ z, (k (0, z) - k (1, z)) * (1 / |d z + t|))
        = ∑ z, (k (0, z) - k (1, z)) / (d z + t) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [abs_of_pos (hposT z), mul_one_div]
    rw [hrewrite]
    exact hsumT
  obtain ⟨u, huW, hune⟩ :=
    exists_ne_const_blockSplitRelation
      (∑ z, (k (0, z) + k (1, z)) * m z) target
      (fun z => k (0, z) - k (1, z)) (fun z => d z + t)
      (fun z => ne_of_gt (hposT z)) hweight hW₂
  have hqin := hsub (Set.mk_mem_prod htW huW)
  refine ⟨(t, u), hqin.1, ?_⟩
  have hsum : (∑ p : Fin 2 × Z, (k p : ℂ) * branch p (t, u))
      = ((∑ p : Fin 2 × Z, k p * shiftedBlockSplitRoot m d p (t, u) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hqin.2 p]
  rw [hsum, sum_shiftedBlockSplitRoot_eq]
  intro hcon
  exact hune (Complex.ofReal_injective hcon)

/-- The zero-target form retained for relation-genericity arguments. -/
theorem exists_shifted_split_branch_relation_ne_zero (m d : Z → ℝ) (hd : ∀ z, 0 < d z)
    (hdinj : Function.Injective d)
    (hinj : Function.Injective fun p : Fin 2 × Z => ((blockEnergy m d p : ℝ) : ℂ))
    (branch : Fin 2 × Z → ℝ × ℝ → ℂ)
    (hbranchC : ∀ p, ContinuousAt (branch p) (0, 0))
    (hbranch0 : ∀ p, branch p (0, 0) = ((blockEnergy m d p : ℝ) : ℂ))
    (hbranchRoot : ∀ p, ∀ᶠ q in 𝓝 ((0, 0) : ℝ × ℝ),
      matrixCharpolyRelation (shiftedBlockSplitMatrix m d q, branch p q) = 0)
    (k : Fin 2 × Z → ℝ) {z₀ : Z} (hk : k (0, z₀) - k (1, z₀) ≠ 0)
    {W : Set (ℝ × ℝ)} (hW : W ∈ 𝓝 ((0, 0) : ℝ × ℝ)) :
    ∃ q ∈ W, (∑ p : Fin 2 × Z, (k p : ℂ) * branch p q) ≠ 0 := by
  simpa using
    exists_shifted_split_branch_relation_ne_const
      m d hd hdinj hinj branch hbranchC hbranch0 hbranchRoot
      k hk 0 hW


omit [Fintype Z] in
/-- Subtracting a scalar from a block splitting shifts every block mean. -/
theorem blockSplitMatrix_sub_smul_one (m d : Z → ℝ) (u : ℂ) (c : ℝ) :
    blockSplitMatrix m d u - ((c : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Z) (Fin 2 × Z) ℂ)
      = blockSplitMatrix (fun z => m z - c) d u := by
  classical
  ext p q
  obtain ⟨i, z⟩ := p
  obtain ⟨j, y⟩ := q
  by_cases hz : z = y
  · subst hz
    simp only [blockSplitMatrix, Matrix.blockDiagonal_apply_eq, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Prod.mk.injEq, and_true]
    fin_cases i <;> fin_cases j <;> simp [splitBlock] <;> ring
  · have hpq : ((i, z) : Fin 2 × Z) ≠ (j, y) := fun h => hz (congrArg Prod.snd h)
    simp only [blockSplitMatrix, Matrix.blockDiagonal_apply, if_neg hz, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, if_neg hpq]
    ring

omit [Fintype Z] in
theorem shiftedBlockSplitMatrix_sub_smul_one (m d : Z → ℝ) (q : ℝ × ℝ) (c : ℝ) :
    shiftedBlockSplitMatrix m d q - ((c : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Z) (Fin 2 × Z) ℂ)
      = shiftedBlockSplitMatrix (fun z => m z - c) d q :=
  blockSplitMatrix_sub_smul_one m (fun z => d z + q.1) (q.2 : ℂ) c

omit [Fintype Z] [DecidableEq Z] in
theorem blockEnergy_sub_const (m d : Z → ℝ) (c : ℝ) (p : Fin 2 × Z) :
    blockEnergy (fun z => m z - c) d p = blockEnergy m d p - c := by
  rw [blockEnergy, blockEnergy]
  ring

end

end GaloisForLFunctions.HTGeometry
