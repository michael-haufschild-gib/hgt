import GaloisForLFunctions.HTGeometry.QuasiAbelianSeedCompactBound
import GaloisForLFunctions.HTGeometry.QuasiAbelianComplementWeightTransfer
import GaloisForLFunctions.HTGeometry.QuasiAbelianPoincareSeries
import GaloisForLFunctions.HTGeometry.QuasiAbelianCosetPoincareSeries

/-!
# Local normal convergence of the damped coset Poincaré series

At a fixed scale the seed bound is available on every compact set, with a constant depending on the
set; combined with the Gaussian growth of the inverse automorphic factor along the complement, that
gives a polynomial-Gaussian lattice majorant on every compact, which is exactly the hypothesis of
the corpus's local-normal-convergence bridge.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

set_option maxHeartbeats 1000000 in
/-- **The damped coset Poincaré series converges locally normally.** -/
theorem summableLocallyUniformlyOn_poincareTerm_dampedFlatSeed {d c : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (hcomp : ∀ z, comp z ∈ Γ)
    (G : ComplementGaussianGrowth ψ comp hcomp)
    {I : Type*} [Fintype I] [DecidableEq I] (w : I → Fin d → ℂ)
    (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w) (target : I)
    {m : ℕ} (hm : 0 < m) (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    (P : MvPolynomial (Fin d) ℂ) {B : ℝ} (hB : 1 ≤ B)
    {eps : ℝ} (heps : 0 < eps) (hgap : ∀ i, G.tau i + eps ≤ σ i / 4) :
    SummableLocallyUniformlyOn
      (fun z : Fin c → ℤ =>
        poincareTerm ψ (dampedFlatSeed w hdistinct target hm σ P B)
          (complementEmbedding comp hcomp z)) Set.univ := by
  classical
  refine summableLocallyUniformlyOn_of_polynomialGaussianLattice_bound _ Set.univ isOpen_univ
    (fun _ => ∑ i, P.degreeOf i) (fun _ => eps * G.kappa)
    (fun _ => mul_pos heps G.kappa_pos) ?_
  intro K hKs hK
  obtain ⟨Gcst, hGcst0, hGcst⟩ := G.factor_bound K hK
  obtain ⟨Cs, hCs0, hCs⟩ :=
    exists_norm_dampedFlatSeed_realTranslate_le w hdistinct target hm σ hσ P hK hB
  have hlin0 : (0 : ℝ) ≤ (1 + G.lin) ^ (∑ i, P.degreeOf i) :=
    pow_nonneg (by linarith [G.lin_nonneg]) _
  refine ⟨Gcst * (Cs * (1 + G.lin) ^ (∑ i, P.degreeOf i)),
    mul_nonneg hGcst0 (mul_nonneg hCs0 hlin0), fun z x hx => ?_⟩
  have htrans : x + comp z = x + fun i => ((G.vec z i : ℝ) : ℂ) := by
    funext i
    rw [Pi.add_apply, Pi.add_apply, G.vec_eq z i]
  have hseed : ‖(dampedFlatSeed w hdistinct target hm σ P B).1 (x + comp z)‖
      ≤ Cs * ((∏ i, (1 + |G.vec z i|) ^ (P.degreeOf i))
        * Real.exp (-∑ i, σ i / 4 * (G.vec z i) ^ 2)) := by
    rw [htrans]
    exact hCs (G.vec z) x hx
  have hfac := hGcst z x hx
  have hprodnn : (0 : ℝ) ≤ ∏ i, (1 + |G.vec z i|) ^ (P.degreeOf i) :=
    Finset.prod_nonneg fun i _ => by positivity
  have hgauss : Real.exp (∑ i, G.tau i * (G.vec z i) ^ 2)
      * Real.exp (-∑ i, σ i / 4 * (G.vec z i) ^ 2)
      ≤ Real.exp (-(eps * ∑ i, (G.vec z i) ^ 2)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hterm : ∀ i : Fin d,
        G.tau i * (G.vec z i) ^ 2 - σ i / 4 * (G.vec z i) ^ 2 ≤ -(eps * (G.vec z i) ^ 2) := by
      intro i
      nlinarith [hgap i, sq_nonneg (G.vec z i)]
    calc (∑ i, G.tau i * (G.vec z i) ^ 2) + (-∑ i, σ i / 4 * (G.vec z i) ^ 2)
        = ∑ i, (G.tau i * (G.vec z i) ^ 2 - σ i / 4 * (G.vec z i) ^ 2) := by
          rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      _ ≤ ∑ i, -(eps * (G.vec z i) ^ 2) := Finset.sum_le_sum fun i _ => hterm i
      _ = -(eps * ∑ i, (G.vec z i) ^ 2) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  have htransfer := prod_mul_exp_le_polynomialGaussianLatticeWeight G.vec (fun i => P.degreeOf i)
    G.lin_nonneg heps.le G.discrete G.bounded z
  rw [poincareTerm, norm_mul]
  calc ‖((ψ.factor (complementEmbedding comp hcomp z)).1 x)⁻¹‖
        * ‖(dampedFlatSeed w hdistinct target hm σ P B).1
            (x + (complementEmbedding comp hcomp z).1)‖
      ≤ (Gcst * Real.exp (∑ i, G.tau i * (G.vec z i) ^ 2))
        * (Cs * ((∏ i, (1 + |G.vec z i|) ^ (P.degreeOf i))
          * Real.exp (-∑ i, σ i / 4 * (G.vec z i) ^ 2))) :=
        mul_le_mul hfac hseed (norm_nonneg _)
          (mul_nonneg hGcst0 (Real.exp_pos _).le)
    _ = (Gcst * Cs) * ((∏ i, (1 + |G.vec z i|) ^ (P.degreeOf i))
        * (Real.exp (∑ i, G.tau i * (G.vec z i) ^ 2)
          * Real.exp (-∑ i, σ i / 4 * (G.vec z i) ^ 2))) := by ring
    _ ≤ (Gcst * Cs) * ((∏ i, (1 + |G.vec z i|) ^ (P.degreeOf i))
        * Real.exp (-(eps * ∑ i, (G.vec z i) ^ 2))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgauss hprodnn)
          (mul_nonneg hGcst0 hCs0)
    _ ≤ (Gcst * Cs) * ((1 + G.lin) ^ (∑ i, P.degreeOf i)
        * polynomialGaussianLatticeWeight (Fin c) (fun _ => ∑ i, P.degreeOf i)
            (fun _ => eps * G.kappa) z) :=
        mul_le_mul_of_nonneg_left htransfer (mul_nonneg hGcst0 hCs0)
    _ = Gcst * (Cs * (1 + G.lin) ^ (∑ i, P.degreeOf i))
        * polynomialGaussianLatticeWeight (Fin c) (fun _ => ∑ i, P.degreeOf i)
            (fun _ => eps * G.kappa) z := by ring

end

end GaloisForLFunctions.HTGeometry
