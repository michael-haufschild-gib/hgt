import GaloisForLFunctions.HTGeometry.HilbertSchmidtProductLimits
import GaloisForLFunctions.HTGeometry.FiniteRankDeterminantCompletion
import GaloisForLFunctions.HTGeometry.FredholmDeterminantTracePowers

/-!
# The Hilbert--Schmidt determinant multiplication law

Finite coordinate compressions establish the exact trace correction. Passing
to their Hilbert--Schmidt limits gives the law for the global entire determinant.
-/

noncomputable section
open Filter Topology HilbertSchmidt

namespace GaloisForLFunctions.HTGeometry

theorem finiteDet2_one_product {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) :
    finiteDet2 (A + B + A * B) 1 =
      finiteDet2 A 1 * finiteDet2 B 1 * Complex.exp (-(A * B).trace) := by
  have hm : (1 : Matrix m m ℂ) + (A + B + A * B) = (1 + A) * (1 + B) := by
    noncomm_ring
  simp only [finiteDet2, one_smul, one_mul, Matrix.trace_add]
  rw [hm, Matrix.det_mul]
  calc (1 + A).det * (1 + B).det * Complex.exp (-(A.trace + B.trace + (A * B).trace)) =
      (1 + A).det * (1 + B).det *
        Complex.exp (-A.trace + -B.trace + -(A * B).trace) := by
          congr 2
          ring
    _ = _ := by rw [Complex.exp_add, Complex.exp_add]; ring

theorem finiteDet2_neg_neg_one {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) : finiteDet2 (-A) (-1) = finiteDet2 A 1 := by
  simp [finiteDet2]

section Blocks
variable {ι : Type*} [DecidableEq ι]

private theorem block_ofBlock {s : Finset ι} (A : Matrix ↥s ↥s ℂ) :
    blockMatrix (ofBlock A) s = A := by
  ext i j
  simp [blockMatrix, ofBlock]

private theorem ofBlock_add {s : Finset ι} (A B : Matrix ↥s ↥s ℂ) :
    ofBlock (A + B) = ofBlock A + ofBlock B := by
  funext p
  by_cases h : p.1 ∈ s ∧ p.2 ∈ s <;> simp [ofBlock, h]

private theorem ofBlock_support {s : Finset ι} (A : Matrix ↥s ↥s ℂ)
    (p : ι × ι) (hp : p ∉ s ×ˢ s) : ofBlock A p = 0 := by
  have hp' : ¬ (p.1 ∈ s ∧ p.2 ∈ s) := by simpa using hp
  simp [ofBlock, hp']

theorem entireDet2_trunc_product {A B : ι × ι → ℂ}
    (hA : IsHS A) (hB : IsHS B) (s : Finset ι) :
    entireDet2 (truncKernel A s + truncKernel B s +
      hsComp (truncKernel A s) (truncKernel B s)) (-1) =
      entireDet2 (truncKernel A s) (-1) * entireDet2 (truncKernel B s) (-1) *
        Complex.exp (-hsTraceDiag (hsComp (truncKernel A s) (truncKernel B s))) := by
  let C := truncKernel A s + truncKernel B s + hsComp (truncKernel A s) (truncKernel B s)
  have hC : IsHS C := isHS_add (isHS_add (isHS_truncKernel hA s) (isHS_truncKernel hB s))
    (isHS_hsComp (isHS_truncKernel hA s) (isHS_truncKernel hB s))
  have hp : hsComp (truncKernel A s) (truncKernel B s) =
      ofBlock (blockMatrix A s * blockMatrix B s) := by
    rw [truncKernel_eq_ofBlock, truncKernel_eq_ofBlock, hsComp_ofBlock]
  have he : C = ofBlock (blockMatrix A s + blockMatrix B s +
      blockMatrix A s * blockMatrix B s) := by
    dsimp only [C]
    rw [hp, truncKernel_eq_ofBlock, truncKernel_eq_ofBlock, ofBlock_add, ofBlock_add]
  have hsC : ∀ p : ι × ι, p ∉ s ×ˢ s → C p = 0 := by
    intro p hp'
    rw [he]
    exact ofBlock_support _ p hp'
  have hsA : ∀ p : ι × ι, p ∉ s ×ˢ s → truncKernel A s p = 0 := by
    intro p hp'
    rw [truncKernel_eq_ofBlock]
    exact ofBlock_support _ p hp'
  have hsB : ∀ p : ι × ι, p ∉ s ×ˢ s → truncKernel B s p = 0 := by
    intro p hp'
    rw [truncKernel_eq_ofBlock]
    exact ofBlock_support _ p hp'
  have hsp : ∀ p : ι × ι, p ∉ s ×ˢ s →
      hsComp (truncKernel A s) (truncKernel B s) p = 0 := by
    intro p hp'
    rw [hp]
    exact ofBlock_support _ p hp'
  have htr : hsTraceDiag (hsComp (truncKernel A s) (truncKernel B s)) =
      (blockMatrix A s * blockMatrix B s).trace := by
    rw [← trace_blockMatrix_eq_hsTraceDiag hsp, hp, block_ofBlock]
  change entireDet2 C (-1) = _
  rw [entireDet2_eq_finiteDet2_of_support hC hsC,
    entireDet2_eq_finiteDet2_of_support (isHS_truncKernel hA s) hsA,
    entireDet2_eq_finiteDet2_of_support (isHS_truncKernel hB s) hsB]
  simp only [finiteDet2_neg_neg_one]
  rw [htr, he, block_ofBlock, truncKernel_eq_ofBlock, block_ofBlock,
    truncKernel_eq_ofBlock, block_ofBlock]
  exact finiteDet2_one_product _ _

/-- The global Carleman determinant, with its exact multiplicative trace correction. -/
theorem entireDet2_product {A B : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) :
    entireDet2 (A + B + hsComp A B) (-1) =
      entireDet2 A (-1) * entireDet2 B (-1) *
        Complex.exp (-(∑' i, hsComp A B (i, i))) := by
  have hA' := fun s : Finset ι => isHS_truncKernel hA s
  have hB' := fun s : Finset ι => isHS_truncKernel hB s
  have hswap (K : ι × ι → ℂ) (s : Finset ι) :
      hsNorm (truncKernel K s - K) = hsNorm (K - truncKernel K s) := by
    rw [show truncKernel K s - K = -(K - truncKernel K s) by abel, hsNorm_neg]
  have ha : Tendsto (fun s : Finset ι => hsNorm (truncKernel A s - A)) atTop (𝓝 0) := by
    simpa only [hswap] using tendsto_hsNorm_sub_truncKernel hA
  have hb : Tendsto (fun s : Finset ι => hsNorm (truncKernel B s - B)) atTop (𝓝 0) := by
    simpa only [hswap] using tendsto_hsNorm_sub_truncKernel hB
  have hab := tendsto_hsNorm_add_sub hA' hB' hA hB ha hb
  have hp := tendsto_hsNorm_hsComp_sub hA' hB' hA hB ha hb
    (fun s => hsNorm_truncKernel_le hB s)
  have hc := tendsto_hsNorm_add_sub (fun s => isHS_add (hA' s) (hB' s))
    (fun s => isHS_hsComp (hA' s) (hB' s)) (isHS_add hA hB) (isHS_hsComp hA hB) hab hp
  have hleft := tendsto_entireDet2_of_hsNorm_sub_filter
    (fun s => isHS_add (isHS_add (hA' s) (hB' s)) (isHS_hsComp (hA' s) (hB' s)))
    (isHS_add (isHS_add hA hB) (isHS_hsComp hA hB)) hc (-1)
  have htr := tendsto_hsTrace_hsComp_of_hsNorm_sub hA' hB' hA hB ha hb
  have hright := ((tendsto_entireDet2_of_hsNorm_sub_filter hA' hA ha (-1)).mul
    (tendsto_entireDet2_of_hsNorm_sub_filter hB' hB hb (-1))).mul
      ((Complex.continuous_exp.tendsto _).comp htr.neg)
  apply tendsto_nhds_unique hleft
  exact hright.congr fun s => by
    simpa only [hsTraceDiag, Function.comp_def] using (entireDet2_trunc_product hA hB s).symm

end Blocks

open _root_.RHTower

/-- Coordinate-free form for any Hilbert basis, without a countability premise. -/
theorem det2Op_multiplication
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)
    {A B : H →L[ℂ] H}
    (hA : ContinuousLinearMap.IsHilbertSchmidt A) (hB : ContinuousLinearMap.IsHilbertSchmidt B) :
    det2Op b (A + B + A ∘L B) = det2Op b A * det2Op b B *
      Complex.exp (-ContinuousLinearMap.opTrace (A ∘L B)) := by
  have h := entireDet2_product (isHS_coordMatrix b hA) (isHS_coordMatrix b hB)
  rw [hsComp_coordMatrix, tsum_diag_coordMatrix_comp b hA hB] at h
  have he : coordMatrix b (A + B + A ∘L B) =
      coordMatrix b A + coordMatrix b B + coordMatrix b (A ∘L B) := by
    funext p
    simp [coordMatrix_apply]
  rw [← he] at h
  exact h

end GaloisForLFunctions.HTGeometry
