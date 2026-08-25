import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum
import GaloisForLFunctions.HTGeometry.BlockSumSpectralGenericity
import GaloisForLFunctions.HTGeometry.InertiaScalingSwap

open Complex Filter Topology Matrix
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reindexed direct sum on the canonical `Fin (n+m)` coordinate space. -/
def finiteBlockSum {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (D : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin (n + m)) (Fin (n + m)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (blockSum A D)

/-- Hermitian block matrix on the canonical `Fin (n+m)` coordinate space.  Its off-diagonal
blocks are forced to be adjoints, exactly as for a Gram operator under an orthogonal splitting. -/
def finiteHermitianBlock {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin m) ℂ)
    (D : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin (n + m)) (Fin (n + m)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A C C.conjTranspose D)

theorem finiteHermitianBlock_zero_one {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    finiteHermitianBlock A (0 : Matrix (Fin n) (Fin m) ℂ)
        (1 : Matrix (Fin m) (Fin m) ℂ) =
      finiteBlockSum A (1 : Matrix (Fin m) (Fin m) ℂ) := by
  simp [finiteHermitianBlock, finiteBlockSum, blockSum, Matrix.fromBlocks]

theorem finiteHermitianBlock_isHermitian {n m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    {C : Matrix (Fin n) (Fin m) ℂ}
    {D : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.IsHermitian) (hD : D.IsHermitian) :
    (finiteHermitianBlock A C D).IsHermitian := by
  exact (isHermitian_fromBlocks hA hD C).reindex finSumFinEquiv

/-- Convergence of the three Gram blocks gives convergence of the complete orthogonally split
Gram matrix. -/
theorem tendsto_finiteHermitianBlock {n m : ℕ}
    {X : Type*} {l : Filter X}
    {A : X → Matrix (Fin n) (Fin n) ℂ}
    {C : X → Matrix (Fin n) (Fin m) ℂ}
    {D : X → Matrix (Fin m) (Fin m) ℂ}
    {A₀ : Matrix (Fin n) (Fin n) ℂ}
    {C₀ : Matrix (Fin n) (Fin m) ℂ}
    {D₀ : Matrix (Fin m) (Fin m) ℂ}
    (hA : Tendsto A l (nhds A₀)) (hC : Tendsto C l (nhds C₀))
    (hD : Tendsto D l (nhds D₀)) :
    Tendsto (fun x ↦ finiteHermitianBlock (A x) (C x) (D x)) l
      (nhds (finiteHermitianBlock A₀ C₀ D₀)) := by
  have hcont : Continuous (fun p :
      (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin m) ℂ) ×
        Matrix (Fin m) (Fin m) ℂ ↦
      finiteHermitianBlock p.1.1 p.1.2 p.2) := by
    unfold finiteHermitianBlock
    fun_prop
  have hp : Tendsto (fun x ↦ ((A x, C x), D x)) l
      (nhds ((A₀, C₀), D₀)) := by
    simpa only [nhds_prod_eq] using ((hA.prodMk hC).prodMk hD)
  exact hcont.continuousAt.tendsto.comp hp

/-- Exact assembly behind `(13)`--`(14)`: convergence of the persistent Gram block, vanishing
cross block, and convergence of the crossing Gram block to identity give the direct-sum limit. -/
theorem tendsto_finiteHermitianBlock_peeling {n m : ℕ}
    {X : Type*} {l : Filter X}
    {A : X → Matrix (Fin n) (Fin n) ℂ}
    {C : X → Matrix (Fin n) (Fin m) ℂ}
    {D : X → Matrix (Fin m) (Fin m) ℂ}
    {A₀ : Matrix (Fin n) (Fin n) ℂ}
    (hA : Tendsto A l (nhds A₀))
    (hC : Tendsto C l (nhds (0 : Matrix (Fin n) (Fin m) ℂ)))
    (hD : Tendsto D l (nhds (1 : Matrix (Fin m) (Fin m) ℂ))) :
    Tendsto (fun x ↦ finiteHermitianBlock (A x) (C x) (D x)) l
      (nhds (finiteBlockSum A₀ (1 : Matrix (Fin m) (Fin m) ℂ))) := by
  rw [← finiteHermitianBlock_zero_one]
  exact tendsto_finiteHermitianBlock hA hC hD

theorem finiteBlockSum_isHermitian {n m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} {D : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.IsHermitian) (hD : D.IsHermitian) :
    (finiteBlockSum A D).IsHermitian :=
  (isHermitian_blockSum hA hD).reindex finSumFinEquiv

theorem charpoly_finiteBlockSum {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (D : Matrix (Fin m) (Fin m) ℂ) :
    (finiteBlockSum A D).charpoly = A.charpoly * D.charpoly := by
  rw [finiteBlockSum, Matrix.charpoly_reindex]
  exact Matrix.charpoly_fromBlocks_zero₁₂ A 0 D

theorem polynomial_roots_X_sub_C_pow (a : ℂ) : ∀ m : ℕ,
    ((Polynomial.X - Polynomial.C a) ^ m).roots = Multiset.replicate m a
  | 0 => by simp
  | m + 1 => by
      rw [pow_succ, Polynomial.roots_mul]
      · rw [polynomial_roots_X_sub_C_pow a m, Polynomial.roots_X_sub_C]
        rw [Multiset.replicate_succ, Multiset.add_comm]
        rfl
      · exact mul_ne_zero
          (pow_ne_zero _ (sub_ne_zero.mpr (Polynomial.X_ne_C a)))
          (sub_ne_zero.mpr (Polynomial.X_ne_C a))

/-- Exact finite spectral peeling target: the limit characteristic-root multiset is the persistent
spectrum union `m` copies of the unit channel. -/
theorem roots_charpoly_finiteBlockSum_one {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (finiteBlockSum A (1 : Matrix (Fin m) (Fin m) ℂ)).charpoly.roots =
      A.charpoly.roots + Multiset.replicate m 1 := by
  rw [charpoly_finiteBlockSum, Matrix.charpoly_one, Polynomial.roots_mul]
  · simp only [Fintype.card_fin]
    rw [show (1 : Polynomial ℂ) = Polynomial.C 1 by simp]
    rw [polynomial_roots_X_sub_C_pow]
  · exact mul_ne_zero (Matrix.charpoly_monic A).ne_zero
      (pow_ne_zero _ (sub_ne_zero.mpr (Polynomial.X_ne_C (1 : ℂ))))

theorem trace_blockSum {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (D : Matrix (Fin m) (Fin m) ℂ) :
    (blockSum A D).trace = A.trace + D.trace := by
  rw [Matrix.trace]
  rw [Fintype.sum_sum_type]
  simp [blockSum, Matrix.fromBlocks, Matrix.trace]

/-- Exact unit-channel trace increment. -/
theorem trace_finiteBlockSum_one {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (finiteBlockSum A (1 : Matrix (Fin m) (Fin m) ℂ)).trace = A.trace + m := by
  rw [finiteBlockSum, trace_reindex_eq, trace_blockSum, Matrix.trace_one]
  norm_num

/-- Finite Gram spectral peeling `(13)`: continuous Hermitian family whose crossing limit is the
persistent Gram block plus an identity block has sorted spectrum converging to that direct sum. -/
theorem tendsto_sortedSpectrum_finiteGram_peeling
    {n m : ℕ} {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (G : X → Matrix (Fin (n + m)) (Fin (n + m)) ℂ)
    (hG : Continuous G) (hHerm : ∀ x, (G x).IsHermitian) (x₀ : X) :
    Tendsto (fun x => sortedTuple (hHerm x).eigenvalues) (𝓝 x₀)
      (𝓝 (sortedTuple (hHerm x₀).eigenvalues)) :=
  (continuous_sortedTuple_eigenvalues hG hHerm).tendsto x₀

/-- One-sided form used at a crossing parameter. -/
theorem tendstoWithin_sortedSpectrum_finiteGram_peeling
    {n m : ℕ} {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (G : X → Matrix (Fin (n + m)) (Fin (n + m)) ℂ)
    (hG : Continuous G) (hHerm : ∀ x, (G x).IsHermitian)
    (x₀ : X) (s : Set X) :
    Tendsto (fun x => sortedTuple (hHerm x).eigenvalues) (𝓝[s] x₀)
      (𝓝 (sortedTuple (hHerm x₀).eigenvalues)) :=
  (tendsto_sortedSpectrum_finiteGram_peeling G hG hHerm x₀).mono_left inf_le_left

/-- Finite Hilbert--Schmidt trace peeling `(14)`: convergence of the pre-crossing Gram to the
persistent Gram plus `m` identity channels forces an exact trace jump of `m`. -/
theorem tendsto_trace_finiteGram_peeling
    {n m : ℕ} {ι : Type*} {l : Filter ι}
    (G : ι → Matrix (Fin (n + m)) (Fin (n + m)) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hG : Tendsto G l (𝓝 (finiteBlockSum A (1 : Matrix (Fin m) (Fin m) ℂ)))) :
    Tendsto (fun i => (G i).trace - A.trace) l (𝓝 m) := by
  have htrace : Tendsto (fun i => (G i).trace) l
      (𝓝 (finiteBlockSum A (1 : Matrix (Fin m) (Fin m) ℂ)).trace) := by
    exact (continuous_finsetSum _ fun j _ =>
      (continuous_apply j).comp (continuous_apply j)).continuousAt.tendsto.comp hG
  have hconst : Tendsto (fun _ : ι => A.trace) l (𝓝 A.trace) := tendsto_const_nhds
  have hsub := htrace.sub hconst
  rw [trace_finiteBlockSum_one] at hsub
  convert hsub using 1 <;> norm_num

end

end GaloisForLFunctions.HTGeometry
