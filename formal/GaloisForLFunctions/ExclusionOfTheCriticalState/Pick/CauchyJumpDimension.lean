import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.CauchyLogJumpSpectrum
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.PolynomialJumpRealization
import GaloisForLFunctions.HTGeometry.ChainRankStabilization

/-!
# Minimal jump dimension of finite Cauchy probes

At n+1 distinct rates the Cauchy generator needs exactly n real diagonal
jumps. Degree-n momentum polynomials suffice. On the whole real line no
finite collection of functions suffices, while the contrast powers give
a countable realization. The weak-step Gaussian limit drops to a single
jump regardless of the number of distinct probes.
-/

noncomputable section
open Matrix Finset Filter
open scoped Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.LogCauchy
open HilbertMetric.CauchyDephasing JumpGrid
variable {n : ℕ}

def logTable (v : Nodes n) : Table n := fun i j => cost (v i) (v j)

private theorem symm_cost (s t : ℝ) : cost s t=cost t s := by rw [cost,cost,coherence_symm]

private theorem log_hollow (v : Nodes n) : hollow (logTable v) := by
  exact ⟨fun i => by simp [logTable,cost,coherence_self],fun i j => symm_cost _ _⟩

/-- Centering at any one grid point produces a positive definite Gram
matrix on all remaining labels. -/
theorem log_anchored_posDef (v : Nodes n) : (anchored (logTable v)).PosDef := by
  let z : Fin n ↪ {t : ℝ // |t|<1 ∧ t≠0} :=
    ⟨fun i => ⟨contrast (v i.succ) (v 0),contrast_inside _ _,
      fun he => Fin.succ_ne_zero i (v.injective ((contrast_eq_zero_iff _ _).mp he))⟩,
     fun i j he => Fin.succ_injective _ (v.injective (contrast_injective _ (congrArg Subtype.val he)))⟩
  have eq : anchored (logTable v)=(4:ℝ) • (Matrix.of fun i j => diskKernel (z i).val (z j).val) := by
    ext i j
    change 4*(cost (v 0) (v i.succ)+cost (v 0) (v j.succ)-cost (v i.succ) (v j.succ))=
      4*diskKernel (contrast (v i.succ) (v 0)) (contrast (v j.succ) (v 0))
    rw [symm_cost (v 0) (v i.succ),symm_cost (v 0) (v j.succ),anchored_log]
  rw [eq]
  exact (disk_gram_posDef z).smul (by norm_num : (0:ℝ)<4)

theorem log_anchored_rank (v : Nodes n) : (anchored (logTable v)).rank=n := by
  rw [Matrix.rank_of_isUnit _ (log_anchored_posDef v).isUnit,Fintype.card_fin]

/-- Actual continuum functions may be arbitrary in the lower bound.
Evaluating them on the finite grid already forces n jump directions. -/
theorem finite_grid_minimum (v : Nodes n) :
    (∃ F : Fin n → Channel n, table v F=logTable v) ∧
      ∀ (k : ℕ) (f : Fin k → Fin (n+1) → ℝ),
        (∀ i j, jointCost f i j=logTable v i j) → n≤k := by
  have upper := (table_realizable_iff (logTable v) v).mp ⟨log_hollow _,(log_anchored_posDef v).posSemidef⟩
  refine ⟨?_,fun k f hf => ?_⟩
  · rwa [log_anchored_rank] at upper
  · let F := fun k => interpolateValues v (f k)
    have he : table v F=logTable v := by
      ext i j
      simpa only [table,rate,F,eval_values,jointCost] using hf i j
    have h := rank_needed v F
    rwa [he,log_anchored_rank] at h

/-- No finite real feature map of any regularity realizes the logarithmic
Cauchy distance on all momenta. -/
theorem no_finite_jump_bank (k : ℕ) (f : Fin k → ℝ → ℝ) :
    ∃ s t, (∑ a, gapCost (f a s) (f a t))≠cost s t := by
  by_contra! h
  let v : Nodes (k+1) := ⟨fun i => (i.val:ℝ), fun i j he => Fin.ext (by
    change (i.val:ℝ)=(j.val:ℝ) at he
    exact_mod_cast he)⟩
  have impossible := (finite_grid_minimum v).2 k (fun a i => f a (v i)) fun i j => h (v i) (v j)
  omega

private def scaledNodes (N : ℕ) (v : Nodes n) : Nodes n :=
  ⟨fun i => v i/Real.sqrt ((N:ℝ)+1),fun _ _ h => v.injective
    ((div_left_inj' (by positivity : Real.sqrt ((N:ℝ)+1)≠0)).mp h)⟩

private theorem scaled_apply (N : ℕ) (v : Nodes n) (i : Fin (n+1)) :
    scaledNodes N v i=v i/Real.sqrt ((N:ℝ)+1) := rfl

def weakTable (N : ℕ) (v : Nodes n) : Table n := ((N:ℝ)+1) • logTable (scaledNodes N v)

def gaussianTable (v : Nodes n) : Table n := fun i j => gapCost (v i) (v j)

private theorem weak_positive (N : ℕ) (v : Nodes n) : (anchored (weakTable N v)).PosDef := by
  have he : anchored (weakTable N v)=((N:ℝ)+1) • anchored (logTable (scaledNodes N v)) := by
    ext i j
    simp only [anchored,weakTable,Matrix.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact (log_anchored_posDef _).smul (by positivity : 0<(N:ℝ)+1)

private theorem gaussianGram (v : Nodes n) :
    let z := fun i : Fin n => v i.succ-v 0
    anchored (gaussianTable v)=Matrix.vecMulVec z z := by
  intro z
  ext i j
  change 4*(gapCost (v 0) (v i.succ)+gapCost (v 0) (v j.succ)-gapCost (v i.succ) (v j.succ))=z i*z j
  unfold gapCost z
  ring

/-- One Gaussian jump is necessary and sufficient as soon as the grid
contains two points. A singleton records no differences. -/
theorem gaussian_dimension (v : Nodes n) : (anchored (gaussianTable v)).rank=min n 1 := by
  cases n with
  | zero =>
    exact Nat.le_zero.mp (anchored (gaussianTable v)).rank_le_width
  | succ n =>
    let z (i : Fin (n+1)) := v i.succ-v 0
    have h₀ : z 0≠0 := sub_ne_zero.mpr fun e => Fin.succ_ne_zero _ (v.injective e)
    have nz : Matrix.vecMulVec z z≠0 := by
      intro e
      exact (mul_ne_zero h₀ h₀) (congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => M 0 0) e)
    have pos := mt (HTGeometry.DiffOp.rank_eq_zero_iff _).mp nz
    have le := Matrix.rank_vecMulVec_le z z
    rw [gaussianGram,min_eq_right (Nat.succ_le_succ (Nat.zero_le n))]
    change (Matrix.vecMulVec z z).rank=1
    omega

/-- Every rescaled finite-step table has full jump dimension. In its
entrywise limit precisely the linear momentum jump remains. -/
theorem weak_limit_rank_drop (v : Nodes n) :
    Tendsto (fun N => weakTable N v) atTop (𝓝 (gaussianTable v)) ∧
    (∀ N, (anchored (weakTable N v)).rank=n) ∧ (anchored (gaussianTable v)).rank=min n 1 := by
  refine ⟨?_,fun N => by rw [Matrix.rank_of_isUnit _ (weak_positive N v).isUnit,Fintype.card_fin],gaussian_dimension v⟩
  · apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have h := (Real.continuousAt_log ((Real.exp_pos _).ne')).tendsto.comp (weakCoherence_tendsto (v i) (v j))
    have hh := h.neg
    simpa only [Function.comp_def,weakTable,logTable,scaled_apply,gaussianTable,Matrix.smul_apply,smul_eq_mul,
      cost,weakCoherence,Real.log_pow,Nat.cast_add,Nat.cast_one,Real.log_exp,neg_neg,mul_neg] using hh

#print axioms log_anchored_posDef
#print axioms finite_grid_minimum
#print axioms no_finite_jump_bank
#print axioms gaussian_dimension
#print axioms weak_limit_rank_drop
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.LogCauchy
