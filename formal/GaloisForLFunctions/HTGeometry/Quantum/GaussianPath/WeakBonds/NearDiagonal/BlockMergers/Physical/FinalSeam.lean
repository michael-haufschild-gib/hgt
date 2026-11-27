import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.SumSpectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Subregister.ProductBasis
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.MultiplexedPhases.CompiledBasis

/-! # All-time gate budget from a separated pair of balanced blocks -/
open Matrix Set Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
open FirstAscent.ThermodynamicEdges DiagonalSynthesis.MultiplexedPhases DiagonalSynthesis.CommutatorBounds
noncomputable section

/-- All separated reference levels occur among the diagonal entries of
any exact diagonalization. Equal cardinality rules out unused entries. -/
private theorem diagonal_spacing {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (e : I≃J) (V : unitaryGroup J ℂ) (d : J→ℝ) (a : I→ℝ)
    (hlevels : ∀ i, (a i:ℂ)∈spectrum ℂ ((V : Matrix J J ℂ)*diagonal (fun j => (d j:ℂ))*star (V : Matrix J J ℂ)))
    {g : ℝ} (hg : 0 < g) (hsep : ∀ i j, i≠j → g ≤ |a i-a j|) :
    ∀ i j, i≠j → g ≤ |d i-d j| := by
  let hV := Unitary.mem_iff.mp V.property
  let u : (Matrix J J ℂ)ˣ := ⟨V.val,star V.val,hV.2,hV.1⟩
  have hs (i : I) : ∃ j, d j=a i := by
    have hi := hlevels i
    change (a i:ℂ)∈spectrum ℂ ((u:Matrix J J ℂ)*diagonal (fun j => (d j:ℂ))*(↑u⁻¹:Matrix J J ℂ)) at hi
    rw [spectrum.units_conjugate,spectrum_diagonal] at hi
    obtain ⟨j,hj⟩ := hi
    exact ⟨j,Complex.ofReal_injective hj⟩
  exact transfer_spacing e (by rintro _ ⟨i,rfl⟩; exact hs i) hg hsep

/-- With product-level spacing g, a physical joining bond of norm
O(εg) gives a uniform-in-time O(2ᴷ) gate cap on balanced children. -/
theorem final_seam_cap (l r : ℕ) (hl : l ≤ r) (hr : r ≤ l+1) (x : PathLabel (l+r+2)→ℝ)
    {ε g : ℝ} (hg : 0 < g)
    (hgap : ∀ a b : Fin (2^(l+2))×Fin (2^(r+2)), a≠b → g ≤
      |(energies l (extractBlocks l r x).1.1 a.1+energies r (extractBlocks l r x).1.2 a.2)-
       (energies l (extractBlocks l r x).1.1 b.1+energies r (extractBlocks l r x).1.2 b.2)|)
    {δ : ℝ} (hc : 4*sqrt packConstant/g*(9*δ) ≤ ε)
    (hseam : ∀ i, |(extractBlocks l r x).2 i| ≤ δ) :
    let K := l+r+4
    let H := pathHamiltonian (WithLp.toLp 2 x : PathShell (l+r+2))
    ∀ t, HasProjectiveCircuitApproximation K ε (213*2^K) (unitaryEvolution H t) := by
  classical
  intro K H t
  let m := l+r+2
  let S := intervalWires K 0 (l+2)
  let T := intervalWires K (l+2) (r+2)
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro i h₁ h₂
    have hL := (mem_filter.mp h₁).2.2
    have hR := (mem_filter.mp h₂).2.1
    omega
  let e := numberWires (B:=0) (m:=l) (n:=m) (by dsimp only [m]; omega)
  let f := numberWires (B:=l+2) (m:=r) (n:=m) (by dsimp only [m]; omega)
  let A : PathShell l := WithLp.toLp 2 (extractBlocks l r x).1.1
  let B : PathShell r := WithLp.toLp 2 (extractBlocks l r x).1.2
  obtain ⟨V,d,hV,he⟩ := Subregister.disjoint_sum_basis e f hST (by omega) (by omega)
    (isSelfAdjoint_pathHamiltonian A).isHermitian (isSelfAdjoint_pathHamiltonian B).isHermitian
  change blockSum l r x=(V : Register K)*diagonal (fun i => (d i:ℂ))*star (V : Register K) at he
  let p := fun i : Fin (2^(l+2))×Fin (2^(r+2)) =>
    energies l (extractBlocks l r x).1.1 i.1+energies r (extractBlocks l r x).1.2 i.2
  let b : (Fin (2^(l+2))×Fin (2^(r+2)))≃(Fin K→Bool) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_fun,Fintype.card_bool]
    rw [←pow_add]; congr 1; dsimp only [K]; omega)
  have hs := diagonal_spacing b V d p (fun i => he ▸ sum_mem_spectrum l r x i.1 i.2) hg hgap
  have hHH : IsSelfAdjoint H := isSelfAdjoint_pathHamiltonian _
  obtain ⟨z,hz,C,hC,hfit⟩ := compiled_basis_orbit (by dsimp only [K]; omega : 2 ≤ K) ⟨H,hHH⟩ V hV d hg hs t
  rw [←he,norm_sub_rev H (blockSum l r x)] at hfit
  have herr := (mul_le_mul_of_nonneg_left (seam_error l r x hseam)
    (div_nonneg (mul_nonneg (by norm_num) (sqrt_nonneg _)) hg.le)).trans hc
  have hb₁ : (2^(l+2))^2 ≤ 2^K := by rw [←pow_mul]; exact Nat.pow_le_pow_right (by decide) (by dsimp only [K]; omega)
  have hb₂ : (2^(r+2))^2 ≤ 2^K*2 := by rw [←pow_succ,←pow_mul]; exact Nat.pow_le_pow_right (by decide) (by dsimp only [K]; omega)
  refine ⟨z,hz,C,hC.trans ?_,hfit.trans herr⟩
  omega

#print axioms final_seam_cap
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
