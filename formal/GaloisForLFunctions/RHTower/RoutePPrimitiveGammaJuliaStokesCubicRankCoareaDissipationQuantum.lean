import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCubicCoverWeightedTerminalDissipation

/-!
# Cubic Xi rank--coarea dissipation quantum

Every completed-Xi cubic unit landing must pay separately for its fused physical-rank channel at
every marked point.  Canonical pendant Stokes cuts and finite Cauchy--Schwarz force the local floor

`rank² / (cover degree * branch count) ≤ block coarea`.

Summing over all marked points and using the exact moving-landing balance gives a strictly positive
rank-only lower bound for terminal dissipation.  Pendant bookkeeping remains private: the public
API consists only of completed-Xi application theorems.

No landing existence or arithmetic source-to-charge map is asserted.
-/

open GaloisForLFunctions
open GaloisForLFunctions.IrregularStokes
open GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

namespace RHTower

noncomputable section

private theorem coefficientGenerated_physicalRank_sq_le_coverDegree_mul_branchCount_mul_blockEnergy
    {n m K N : ℕ} (d : PuiseuxOrbitCoareaDatum n m K N) (x : Fin n → ℝ) :
    d.toOrbitCoareaDatum.physicalRank x ^ (2 : ℕ) ≤
      (N : ℝ) * (m : ℝ) * d.toOrbitCoareaDatum.blockEnergy x := by
  classical
  let pendant : Fin m → Fin d.edgeCount :=
    fun i => d.branches.toNatContactDendrogram.pendantEdge i
  have hpendant_injective : Function.Injective pendant := by
    intro i j hij
    have hside := congrArg
      (fun edge => d.branches.toNatContactDendrogram.cutSide edge i) hij
    by_contra hne
    simp [pendant, NatContactDendrogram.cutSide_pendant, hne] at hside
  let edgeTerm : Fin d.edgeCount → ℝ := fun edge =>
    d.toOrbitCoareaDatum.cuts.length edge *
      (∑ a, d.toOrbitCoareaDatum.liftCharge x a *
        d.toOrbitCoareaDatum.cuts.side edge a) ^ (2 : ℕ)
  have hpendant_term : ∀ i, edgeTerm (pendant i) =
      (1 / (N : ℝ)) * d.toOrbitCoareaDatum.liftCharge x i ^ (2 : ℕ) := by
    intro i
    have hcoordinate :=
      d.toOrbitCoareaDatum.cuts.toPositivePendantCutFamily.pendant_coordinate_sum
        (d.toOrbitCoareaDatum.liftCharge x) i
    have hcoordinate' :
        (∑ a, d.toOrbitCoareaDatum.liftCharge x a *
          d.toOrbitCoareaDatum.cuts.side (pendant i) a) =
            d.toOrbitCoareaDatum.liftCharge x i := by
      simpa [pendant, PuiseuxOrbitCoareaDatum.toOrbitCoareaDatum,
        FinitePuiseuxFamily.canonicalCuts, NatContactDendrogram.canonicalCuts] using hcoordinate
    simp only [edgeTerm]
    rw [hcoordinate']
    rfl
  have hpendant_floor :
      (1 / (N : ℝ)) * ∑ i, d.toOrbitCoareaDatum.liftCharge x i ^ (2 : ℕ) ≤
        d.toOrbitCoareaDatum.blockEnergy x := by
    calc
      (1 / (N : ℝ)) * ∑ i, d.toOrbitCoareaDatum.liftCharge x i ^ (2 : ℕ) =
          ∑ i, edgeTerm (pendant i) := by
        simp [hpendant_term, Finset.mul_sum]
      _ = ∑ edge ∈ Finset.univ.image pendant, edgeTerm edge := by
        symm
        exact Finset.sum_image hpendant_injective.injOn
      _ ≤ ∑ edge, edgeTerm edge := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (by
            intro edge _ _
            exact mul_nonneg (d.toOrbitCoareaDatum.cuts.length_pos edge).le (sq_nonneg _))
      _ = d.toOrbitCoareaDatum.blockEnergy x := by
        rfl
  have hcoverDegree_pos : 0 < (N : ℝ) :=
    Nat.cast_pos.mpr d.branches.coverDegree_pos
  have hbranchSquare :
      (∑ i, d.toOrbitCoareaDatum.liftCharge x i ^ (2 : ℕ)) ≤
        (N : ℝ) * d.toOrbitCoareaDatum.blockEnergy x := by
    calc
      (∑ i, d.toOrbitCoareaDatum.liftCharge x i ^ (2 : ℕ)) =
          (N : ℝ) * ((1 / (N : ℝ)) *
            ∑ i, d.toOrbitCoareaDatum.liftCharge x i ^ (2 : ℕ)) := by
        field_simp
      _ ≤ (N : ℝ) * d.toOrbitCoareaDatum.blockEnergy x :=
        mul_le_mul_of_nonneg_left hpendant_floor hcoverDegree_pos.le
  have hcauchy :
      d.toOrbitCoareaDatum.physicalRank x ^ (2 : ℕ) ≤
        (m : ℝ) * ∑ i, d.toOrbitCoareaDatum.liftCharge x i ^ (2 : ℕ) := by
    simpa [OrbitCoareaDatum.physicalRank] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i : Fin m => d.toOrbitCoareaDatum.liftCharge x i))
  calc
    d.toOrbitCoareaDatum.physicalRank x ^ (2 : ℕ) ≤
        (m : ℝ) * ∑ i, d.toOrbitCoareaDatum.liftCharge x i ^ (2 : ℕ) := hcauchy
    _ ≤ (m : ℝ) * ((N : ℝ) * d.toOrbitCoareaDatum.blockEnergy x) :=
      mul_le_mul_of_nonneg_left hbranchSquare (Nat.cast_nonneg m)
    _ = (N : ℝ) * (m : ℝ) * d.toOrbitCoareaDatum.blockEnergy x := by
      ring

private theorem coefficientGenerated_branchCount_pos_of_physicalRank_ne_zero
    {n m K N : ℕ} (d : PuiseuxOrbitCoareaDatum n m K N) (x : Fin n → ℝ)
    (hrank : d.toOrbitCoareaDatum.physicalRank x ≠ 0) :
    0 < m := by
  have hm : m ≠ 0 := by
    intro hm
    subst m
    apply hrank
    simp [OrbitCoareaDatum.physicalRank]
  exact Nat.pos_of_ne_zero hm

private theorem coefficientGenerated_physicalRank_sq_div_coverDegree_branchCount_le_blockEnergy
    {n m K N : ℕ} (d : PuiseuxOrbitCoareaDatum n m K N) (x : Fin n → ℝ)
    (hrank : d.toOrbitCoareaDatum.physicalRank x ≠ 0) :
    d.toOrbitCoareaDatum.physicalRank x ^ (2 : ℕ) / ((N : ℝ) * (m : ℝ)) ≤
      d.toOrbitCoareaDatum.blockEnergy x := by
  have hbranchCount_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr
    (coefficientGenerated_branchCount_pos_of_physicalRank_ne_zero d x hrank)
  have hcoverDegree_pos : 0 < (N : ℝ) :=
    Nat.cast_pos.mpr d.branches.coverDegree_pos
  apply (div_le_iff₀ (mul_pos hcoverDegree_pos hbranchCount_pos)).2
  calc
    d.toOrbitCoareaDatum.physicalRank x ^ (2 : ℕ) ≤
        (N : ℝ) * (m : ℝ) * d.toOrbitCoareaDatum.blockEnergy x :=
      coefficientGenerated_physicalRank_sq_le_coverDegree_mul_branchCount_mul_blockEnergy d x
    _ = d.toOrbitCoareaDatum.blockEnergy x * ((N : ℝ) * (m : ℝ)) := by
      ring

/-- Every completed-Xi cubic unit landing pays a strictly positive cumulative rank--coarea
quantum.  Each marked point contributes the reciprocal of its cover degree times branch count. -/
theorem routePPrimitiveGammaJuliaStokesCubicUnitLanding_cumulativeRankCoareaQuantum_pos_le_blockEnergy
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 1)) :
    0 < (∑ a, 1 / ((N a : ℝ) * (m a : ℝ))) * commonRankLinear d x.1 ^ (2 : ℕ) ∧
      (∑ a, 1 / ((N a : ℝ) * (m a : ℝ))) * commonRankLinear d x.1 ^ (2 : ℕ) ≤
        ∑ a, (d a).toOrbitCoareaDatum.blockEnergy (x.1.1 a) := by
  have hrank_ne : commonRankLinear d x.1 ≠ 0 :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_commonRank_ne_zero
      (fun _ _ => zero_le_one) x
  have hlocalRank : ∀ a,
      (d a).toOrbitCoareaDatum.physicalRank (x.1.1 a) = commonRankLinear d x.1 := by
    intro a
    simpa only [localRankLinear_apply] using compatible_localRank d x.1 a
  have hlocalRank_ne : ∀ a,
      (d a).toOrbitCoareaDatum.physicalRank (x.1.1 a) ≠ 0 := by
    intro a hzero
    apply hrank_ne
    rw [← hlocalRank a]
    exact hzero
  have hbranchCount_pos : ∀ a, 0 < m a := by
    intro a
    exact coefficientGenerated_branchCount_pos_of_physicalRank_ne_zero
      (d a) (x.1.1 a) (hlocalRank_ne a)
  constructor
  · apply mul_pos
    · apply Finset.sum_pos'
      · intro a _
        exact (one_div_pos.mpr (mul_pos
          (Nat.cast_pos.mpr (d a).branches.coverDegree_pos)
          (Nat.cast_pos.mpr (hbranchCount_pos a)))).le
      · refine ⟨(0 : Fin (p + 1)), Finset.mem_univ _, ?_⟩
        exact one_div_pos.mpr (mul_pos
          (Nat.cast_pos.mpr (d 0).branches.coverDegree_pos)
          (Nat.cast_pos.mpr (hbranchCount_pos 0)))
    · exact sq_pos_of_ne_zero hrank_ne
  · rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    have hlocal :=
      coefficientGenerated_physicalRank_sq_div_coverDegree_branchCount_le_blockEnergy
        (d a) (x.1.1 a) (hlocalRank_ne a)
    rw [hlocalRank a] at hlocal
    simpa [div_eq_mul_inv, mul_comm] using hlocal

/-- Rank-magnitude-preserving completed-Xi cubic transport dissipates at least the strictly
positive common-rank square times the cumulative inverse cover--branch complexity. -/
theorem routePPrimitiveGammaJuliaStokesCubicRankMagnitudePreservingMovingLanding_rankCoarea_dissipationQuantum
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x₀ : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 0))
    (x₁ : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 1))
    (hrank : commonRankLinear d x₀.1 ^ (2 : ℕ) = commonRankLinear d x₁.1 ^ (2 : ℕ)) :
    0 < (∑ a, 1 / ((N a : ℝ) * (m a : ℝ))) * commonRankLinear d x₁.1 ^ (2 : ℕ) ∧
      (∑ a, 1 / ((N a : ℝ) * (m a : ℝ))) * commonRankLinear d x₁.1 ^ (2 : ℕ) ≤
        (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₀.1.1 a)) -
          ∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₁.1.1 a) := by
  obtain ⟨hquantum_pos, hquantum_le⟩ :=
    routePPrimitiveGammaJuliaStokesCubicUnitLanding_cumulativeRankCoareaQuantum_pos_le_blockEnergy
      x₁
  obtain ⟨hexact, _, _⟩ :=
    routePPrimitiveGammaJuliaStokesCubicRankMagnitudePreservingMovingLanding_terminalEnergy_dissipation
      x₀ x₁ hrank
  constructor
  · exact hquantum_pos
  · linarith

end

end RHTower
