import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCubicMovingChargeReesDissipation

/-!
# Cubic Xi cover-weighted terminal dissipation

Coefficient-generated pendant Stokes cuts force a quantitative energy floor at unit Rees scale.
For every cubic Xi landing, activated block coarea dominates terminal microstalk energy weighted by
the inverse local Puiseux cover degrees.  Combining this with the arbitrary moving-charge balance
gives a quantitative rank--terminal exchange law and an explicit contraction for every
rank-magnitude-preserving moving landing pair.

No landing-pair existence or source-to-charge map is asserted.
-/

open GaloisForLFunctions
open GaloisForLFunctions.IrregularStokes
open GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

namespace RHTower

noncomputable section

private theorem coefficientGenerated_terminalEnergy_div_coverDegree_le_blockEnergy
    {n m K N : ℕ} (d : PuiseuxOrbitCoareaDatum n m K N) (x : Fin n → ℝ) :
    (1 / (N : ℝ)) * d.toOrbitCoareaDatum.terminalEnergy x ≤
      d.toOrbitCoareaDatum.blockEnergy x := by
  classical
  let s : Fin n → Fin m := fun i => Classical.choose (d.orbit_surjective i)
  have hs : ∀ i, d.orbit (s i) = i := fun i => Classical.choose_spec (d.orbit_surjective i)
  have hs_injective : Function.Injective s := by
    intro i j hij
    simpa [hs] using congrArg d.orbit hij
  let pendant : Fin m → Fin d.edgeCount :=
    fun i => d.branches.toNatContactDendrogram.pendantEdge i
  have hpendant_injective : Function.Injective pendant := by
    intro i j hij
    have hside := congrArg
      (fun edge => d.branches.toNatContactDendrogram.cutSide edge i) hij
    by_contra hne
    simp [pendant, NatContactDendrogram.cutSide_pendant, hne] at hside
  let selected : Fin n → Fin d.edgeCount := fun i => pendant (s i)
  have hselected_injective : Function.Injective selected :=
    hpendant_injective.comp hs_injective
  let edgeTerm : Fin d.edgeCount → ℝ := fun edge =>
    d.toOrbitCoareaDatum.cuts.length edge *
      (∑ a, d.toOrbitCoareaDatum.liftCharge x a *
        d.toOrbitCoareaDatum.cuts.side edge a) ^ (2 : ℕ)
  have hselected_term : ∀ i, edgeTerm (selected i) = (1 / (N : ℝ)) * x i ^ (2 : ℕ) := by
    intro i
    have hcoordinate :=
      d.toOrbitCoareaDatum.cuts.toPositivePendantCutFamily.pendant_coordinate_sum
        (d.toOrbitCoareaDatum.liftCharge x) (s i)
    have hcoordinate' :
        (∑ a, d.toOrbitCoareaDatum.liftCharge x a *
          d.toOrbitCoareaDatum.cuts.side (selected i) a) = x i := by
      simpa [selected, pendant, PuiseuxOrbitCoareaDatum.toOrbitCoareaDatum,
        FinitePuiseuxFamily.canonicalCuts, NatContactDendrogram.canonicalCuts,
        OrbitCoareaDatum.liftCharge, hs] using hcoordinate
    simp only [edgeTerm]
    rw [hcoordinate']
    rfl
  calc
    (1 / (N : ℝ)) * d.toOrbitCoareaDatum.terminalEnergy x =
        ∑ i, edgeTerm (selected i) := by
      simp [OrbitCoareaDatum.terminalEnergy, hselected_term, Finset.mul_sum]
    _ = ∑ edge ∈ Finset.univ.image selected, edgeTerm edge := by
      symm
      exact Finset.sum_image hselected_injective.injOn
    _ ≤ ∑ edge, edgeTerm edge := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (by
          intro edge _ _
          exact mul_nonneg (d.toOrbitCoareaDatum.cuts.length_pos edge).le (sq_nonneg _))
    _ = d.toOrbitCoareaDatum.blockEnergy x := by
      rfl

/-- Every unit-Rees cubic Xi landing activates at least its inverse-cover-weighted terminal
microstalk energy in canonical Stokes block coarea.  This floor is strictly positive. -/
theorem routePPrimitiveGammaJuliaStokesCubicUnitLanding_coverWeightedTerminalEnergy_pos_le_blockEnergy
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 1)) :
    0 < ∑ a, (1 / (N a : ℝ)) *
        (d a).toOrbitCoareaDatum.terminalEnergy (x.1.1 a) ∧
      (∑ a, (1 / (N a : ℝ)) *
          (d a).toOrbitCoareaDatum.terminalEnergy (x.1.1 a)) ≤
        ∑ a, (d a).toOrbitCoareaDatum.blockEnergy (x.1.1 a) := by
  have hxne :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_charge_ne_zero x
  have hlocal : ∃ a, x.1.1 a ≠ 0 := by
    by_contra h
    push Not at h
    apply hxne
    apply Subtype.ext
    funext a i
    exact congrFun (h a) i
  obtain ⟨a, ha⟩ := hlocal
  constructor
  · apply Finset.sum_pos'
    · intro b _
      exact mul_nonneg
        (one_div_pos.mpr (Nat.cast_pos.mpr (d b).branches.coverDegree_pos)).le
        (by
          simp only [OrbitCoareaDatum.terminalEnergy]
          exact Finset.sum_nonneg fun i _ => sq_nonneg _)
    · refine ⟨a, Finset.mem_univ _, mul_pos ?_ ?_⟩
      · exact one_div_pos.mpr (Nat.cast_pos.mpr (d a).branches.coverDegree_pos)
      · exact (d a).toOrbitCoareaDatum.terminalEnergy_pos ha
  · apply Finset.sum_le_sum
    intro a _
    exact coefficientGenerated_terminalEnergy_div_coverDegree_le_blockEnergy
      (d a) (x.1.1 a)

/-- Arbitrary contracted/unit cubic Xi landings obey a quantitative exchange law: unit terminal
energy plus its cover-weighted floor and the contracted rank debt cannot exceed contracted terminal
energy plus the unit rank debt. -/
theorem routePPrimitiveGammaJuliaStokesCubicMovingLanding_coverWeighted_rankTerminal_exchange
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x₀ : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 0))
    (x₁ : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 1)) :
    (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₁.1.1 a)) +
          (∑ a, (1 / (N a : ℝ)) *
            (d a).toOrbitCoareaDatum.terminalEnergy (x₁.1.1 a)) +
          (-globalRankCoefficient genus d) * commonRankLinear d x₀.1 ^ (2 : ℕ) ≤
        (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₀.1.1 a)) +
          (-globalRankCoefficient genus d) * commonRankLinear d x₁.1 ^ (2 : ℕ) ∧
      0 < ∑ a, (1 / (N a : ℝ)) *
        (d a).toOrbitCoareaDatum.terminalEnergy (x₁.1.1 a) := by
  obtain ⟨hbalance, _, _, _⟩ :=
    routePPrimitiveGammaJuliaStokesCubicMovingLanding_rankTerminalBlock_balance x₀ x₁
  obtain ⟨hweighted_pos, hweighted_le⟩ :=
    routePPrimitiveGammaJuliaStokesCubicUnitLanding_coverWeightedTerminalEnergy_pos_le_blockEnergy
      x₁
  constructor
  · linarith
  · exact hweighted_pos

/-- Rank-magnitude-preserving moving cubic Xi transport contracts terminal energy by at least the
strictly positive inverse-cover-weighted terminal energy visible at unit Rees scale. -/
theorem routePPrimitiveGammaJuliaStokesCubicRankMagnitudePreservingMovingLanding_coverWeightedTerminalEnergy_contraction
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x₀ : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 0))
    (x₁ : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 1))
    (hrank : commonRankLinear d x₀.1 ^ (2 : ℕ) = commonRankLinear d x₁.1 ^ (2 : ℕ)) :
    (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₁.1.1 a)) +
          (∑ a, (1 / (N a : ℝ)) *
            (d a).toOrbitCoareaDatum.terminalEnergy (x₁.1.1 a)) ≤
        ∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₀.1.1 a) ∧
      0 < ∑ a, (1 / (N a : ℝ)) *
        (d a).toOrbitCoareaDatum.terminalEnergy (x₁.1.1 a) := by
  obtain ⟨hexchange, hweighted_pos⟩ :=
    routePPrimitiveGammaJuliaStokesCubicMovingLanding_coverWeighted_rankTerminal_exchange x₀ x₁
  constructor
  · rw [hrank] at hexchange
    linarith
  · exact hweighted_pos

end

end RHTower
