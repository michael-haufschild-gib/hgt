import GaloisForLFunctions.HTGeometry.QuasiAbelianComplementWeightTransfer
import GaloisForLFunctions.HTGeometry.QuasiAbelianPoincareSeries

/-!
# Growth data for a complement, and the Poincaré majorant it produces

`AutomorphicFactor` records only that the factor is normalized, cocyclic and nowhere zero — no size
information — so the Poincaré term `(ψ.factor γ x)⁻¹ · seed(x+γ)` cannot be bounded from that
structure alone.  Abe's setting supplies the missing datum through the Appell–Humbert form: along a
complement the inverse factor grows at most Gaussianly, and the complement is a real, uniformly
discrete, boundedly linear image of its index lattice.

Packaging exactly those facts turns the damped-seed bound into the majorant the damping family
needs.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The damped interpolation seed at scale `B`. -/
def dampedFlatSeed {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I] (w : I → Fin d → ℂ)
    (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w) (target : I)
    {m : ℕ} (hm : 0 < m) (σ : Fin d → ℝ) (P : MvPolynomial (Fin d) ℂ) (B : ℝ) :
    MultivariateEntire d :=
  multivariateEntireMul (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump
    (multivariateEntireMul (gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping
      (mvPolynomialMultivariateEntire P))

/-- **Growth data for a complement of a quasi-Abelian lattice.**  The complement is realized by real
vectors, is uniformly discrete and boundedly linear in its index, and the inverse automorphic factor
grows at most Gaussianly along it. -/
structure ComplementGaussianGrowth {d c : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (comp : (Fin c → ℤ) →+ (Fin d → ℂ))
    (hcomp : ∀ z, comp z ∈ Γ) where
  /-- the real vector the complement realizes -/
  vec : (Fin c → ℤ) → Fin d → ℝ
  vec_eq : ∀ (z : Fin c → ℤ) (i : Fin d), comp z i = ((vec z i : ℝ) : ℂ)
  /-- Gaussian growth rates of the inverse factor -/
  tau : Fin d → ℝ
  tau_nonneg : ∀ i, 0 ≤ tau i
  factor_bound : ∀ K : Set (Fin d → ℂ), IsCompact K → ∃ cst : ℝ, 0 ≤ cst ∧
    ∀ (z : Fin c → ℤ) (x : Fin d → ℂ), x ∈ K →
      ‖((ψ.factor ⟨comp z, hcomp z⟩).1 x)⁻¹‖ ≤ cst * Real.exp (∑ i, tau i * (vec z i) ^ 2)
  /-- uniform discreteness -/
  kappa : ℝ
  kappa_pos : 0 < kappa
  discrete : ∀ z : Fin c → ℤ, kappa * ∑ j, (((z j : ℤ) : ℝ)) ^ 2 ≤ ∑ i, (vec z i) ^ 2
  /-- boundedness of the index-to-ambient map -/
  lin : ℝ
  lin_nonneg : 0 ≤ lin
  bounded : ∀ (z : Fin c → ℤ) (i : Fin d), |vec z i| ≤ lin * ∑ j, |((z j : ℤ) : ℝ)|

/-- A nonzero index vector carries at least one unit of squared mass. -/
theorem one_le_sum_sq_of_ne_zero {c : ℕ} {z : Fin c → ℤ} (hz : z ≠ 0) :
    (1 : ℝ) ≤ ∑ j, (((z j : ℤ) : ℝ)) ^ 2 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hz (funext hall)
  have hone : (1 : ℝ) ≤ (((z j : ℤ) : ℝ)) ^ 2 := by
    have h1 : (1 : ℤ) ≤ |z j| := Int.one_le_abs (by omega)
    have h2 : (1 : ℝ) ≤ |((z j : ℤ) : ℝ)| := by exact_mod_cast h1
    nlinarith [abs_nonneg (((z j : ℤ) : ℝ)), sq_abs (((z j : ℤ) : ℝ))]
  refine le_trans hone (Finset.single_le_sum (f := fun i => (((z i : ℤ) : ℝ)) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ j))

/-- **The Poincaré majorant of the damped seed.**  Along a complement with Gaussian growth data, the
term of the damped seed is bounded by an exponentially small multiple of a polynomial-Gaussian
lattice weight. -/
theorem norm_poincareTerm_dampedFlatSeed_le {d c : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (hcomp : ∀ z, comp z ∈ Γ)
    {K : Set (Fin d → ℂ)} (hK : IsCompact K)
    (G : ComplementGaussianGrowth ψ comp hcomp)
    {I : Type*} [Fintype I] [DecidableEq I] (w : I → Fin d → ℂ)
    (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w) (target : I)
    {m : ℕ} (hm : 0 < m) (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    {ρ σ₀ eps : ℝ} (hσ₀le : ∀ i, σ₀ ≤ σ i) (heps : 0 ≤ eps)
    (hgap : ∀ i, G.tau i + eps ≤ σ i / 4)
    (hpos : 0 ≤ σ₀ * G.kappa / 4 - (∑ i, σ i) * (2 * ρ ^ 2))
    (P : MvPolynomial (Fin d) ℂ)
    (hKb : ∀ x ∈ K, ∀ i, |(x i).re - (w target i).re| ≤ ρ ∧ |(x i).im - (w target i).im| ≤ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 1 ≤ B → ∀ z : Fin c → ℤ, z ≠ 0 → ∀ x ∈ K,
      ‖poincareTerm ψ (dampedFlatSeed w hdistinct target hm σ P B) ⟨comp z, hcomp z⟩ x‖
        ≤ C * Real.exp (-((σ₀ * G.kappa / 4 - (∑ i, σ i) * (2 * ρ ^ 2)) * B))
          * polynomialGaussianLatticeWeight (Fin c) (fun _ => ∑ i, P.degreeOf i)
              (fun _ => eps * G.kappa) z := by
  classical
  set rate : ℝ := σ₀ * G.kappa / 4 - (∑ i, σ i) * (2 * ρ ^ 2) with hrate
  set D : ℕ := ∑ i, P.degreeOf i with hD
  obtain ⟨Gcst, hGcst0, hGcst⟩ := G.factor_bound K hK
  obtain ⟨Cs, hCs0, hCs⟩ := exists_norm_scaledFlatSeed_realTranslate_damped w hdistinct target hm
    σ hσ (ρ := ρ) (σ₀ := σ₀ * G.kappa) hpos P hK hKb
  have hlin1 : (0 : ℝ) ≤ 1 + G.lin := by linarith [G.lin_nonneg]
  have hlin0 : (0 : ℝ) ≤ (1 + G.lin) ^ D := pow_nonneg hlin1 D
  refine ⟨Gcst * (Cs * (1 + G.lin) ^ D),
    mul_nonneg hGcst0 (mul_nonneg hCs0 hlin0), fun B hB z hz x hx => ?_⟩
  have htrans : x + comp z = x + fun i => ((G.vec z i : ℝ) : ℂ) := by
    funext i
    rw [Pi.add_apply, Pi.add_apply, G.vec_eq z i]
  have hσ₀0 : 0 ≤ σ₀ := by
    rw [hrate] at hpos
    have hsum : (0 : ℝ) ≤ (∑ i, σ i) * (2 * ρ ^ 2) := by
      refine mul_nonneg (Finset.sum_nonneg fun i _ => (hσ i).le) (by positivity)
    have h1 : 0 ≤ σ₀ * G.kappa := by nlinarith [hpos, hsum]
    by_contra hneg
    push Not at hneg
    nlinarith [G.kappa_pos, h1, mul_neg_of_neg_of_pos hneg G.kappa_pos]
  have hmass : σ₀ * G.kappa ≤ ∑ i, σ i * (G.vec z i) ^ 2 := by
    have hd := G.discrete z
    have hone := one_le_sum_sq_of_ne_zero hz
    have hlow : σ₀ * ∑ i, (G.vec z i) ^ 2 ≤ ∑ i, σ i * (G.vec z i) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hσ₀le i) (sq_nonneg _)
    have h1 := mul_le_mul_of_nonneg_left hd hσ₀0
    have h2 := mul_le_mul_of_nonneg_left hone (mul_nonneg hσ₀0 G.kappa_pos.le)
    nlinarith [h1, h2, hlow]
  have hseed' : ‖(dampedFlatSeed w hdistinct target hm σ P B).1 (x + comp z)‖
      ≤ Cs * Real.exp (-(rate * B))
        * ((∏ i, (1 + |G.vec z i|) ^ (P.degreeOf i))
          * Real.exp (-∑ i, σ i / 4 * (G.vec z i) ^ 2)) := by
    rw [htrans]
    exact hCs B hB (G.vec z) hmass x hx
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
    G.lin_nonneg heps G.discrete G.bounded z
  rw [poincareTerm, norm_mul]
  calc ‖((ψ.factor ⟨comp z, hcomp z⟩).1 x)⁻¹‖
        * ‖(dampedFlatSeed w hdistinct target hm σ P B).1 (x + comp z)‖
      ≤ (Gcst * Real.exp (∑ i, G.tau i * (G.vec z i) ^ 2))
        * (Cs * Real.exp (-(rate * B))
          * ((∏ i, (1 + |G.vec z i|) ^ (P.degreeOf i))
            * Real.exp (-∑ i, σ i / 4 * (G.vec z i) ^ 2))) :=
        mul_le_mul hfac hseed' (norm_nonneg _)
          (mul_nonneg hGcst0 (Real.exp_pos _).le)
    _ = (Gcst * Cs) * Real.exp (-(rate * B))
        * ((∏ i, (1 + |G.vec z i|) ^ (P.degreeOf i))
          * (Real.exp (∑ i, G.tau i * (G.vec z i) ^ 2)
            * Real.exp (-∑ i, σ i / 4 * (G.vec z i) ^ 2))) := by ring
    _ ≤ (Gcst * Cs) * Real.exp (-(rate * B))
        * ((∏ i, (1 + |G.vec z i|) ^ (P.degreeOf i))
          * Real.exp (-(eps * ∑ i, (G.vec z i) ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgauss hprodnn) ?_
        exact mul_nonneg (mul_nonneg hGcst0 hCs0) (Real.exp_pos _).le
    _ ≤ (Gcst * Cs) * Real.exp (-(rate * B))
        * ((1 + G.lin) ^ D
          * polynomialGaussianLatticeWeight (Fin c) (fun _ => D) (fun _ => eps * G.kappa) z) := by
        refine mul_le_mul_of_nonneg_left htransfer ?_
        exact mul_nonneg (mul_nonneg hGcst0 hCs0) (Real.exp_pos _).le
    _ = Gcst * (Cs * (1 + G.lin) ^ D) * Real.exp (-(rate * B))
        * polynomialGaussianLatticeWeight (Fin c) (fun _ => D) (fun _ => eps * G.kappa) z := by
        ring

end

end GaloisForLFunctions.HTGeometry
