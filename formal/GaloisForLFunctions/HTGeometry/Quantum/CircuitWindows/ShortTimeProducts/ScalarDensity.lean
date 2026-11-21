import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.CircuitReturns

/-! # Small-error occupation of the empty circuit and budgets missing a qubit -/
open Filter Topology MeasureTheory Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ShortTimeProducts
noncomputable section
open SharpOccupation

/-- Converting operator error to the fraction of a turn costs between
the two linear chord bounds. -/
theorem physical_arc_bounds {ε : ℝ} (hε : 0<ε) (hsmall : ε<sqrt 2) :
    ε/π ≤ physicalArc ε ∧ physicalArc ε ≤ ε/2 := by
  obtain ⟨hx,he⟩ := physicalArc_spec hε hsmall
  let x := physicalArc ε
  have hx0 : 0 < x := hx.1
  have hxp : 0 ≤ π*x/2 := by positivity
  have hθ : π*x/2 ≤ π/2 := by
    have h := mul_le_mul_of_nonneg_left (show x ≤ 1 by linarith only [hx.2]) Real.pi_pos.le
    linarith only [h]
  change 2*sin (π*x/2)=ε at he
  constructor
  · rw [div_le_iff₀ Real.pi_pos]
    linarith only [Real.sin_le hxp,he]
  · have h := Real.mul_le_sin hxp hθ
    rw [show 2/π*(π*x/2)=x by field_simp] at h
    linarith only [h,he]

theorem scalar_fraction {N : ℕ} (H : selfAdjoint (Register N)) (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    {ε : ℝ} (hε : 0<ε) (hsmall : ε<sqrt 2) (a : ℝ) :
    Tendsto (visitFraction H 0 ε a) atTop (𝓝 (((2^N:ℕ):ℝ)*(physicalArc ε)^(2^N-1:ℕ))) := by
  obtain ⟨hx,he⟩ := physicalArc_spec hε hsmall
  have h := maximallyProjective_zeroGateOccupation_from_start H hi ⟨_,hx.1.le,hx.2.le⟩ a
  have hset : visitSet H 0 ε = zeroGateReturnSet H (physicalArc ε) := by
    ext t
    change HasProjectiveCircuitApproximation N ε 0 (unitaryEvolution H.val t) ↔
      orbitCircuitDistance H 0 t ≤ zeroGateArcTolerance (physicalArc ε)
    rw [he]
    exact hasProjectiveCircuitApproximation_iff_infDist _ _ _
  simpa only [visitFraction,hset,zeroGateArcDensity] using h

/-- For a fixed prefix, the affordable fraction of every budget below
half the qubit count is bounded above and below by fixed multiples of
ε^(D−1), uniformly in the budget as ε decreases. -/
theorem gaussian_low_gate_occupation_order :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∃ A > 0, ∀ ε : ℝ, 0<ε → ε<sqrt 2 → A*ε<sqrt 2 → ∀ a : ℝ, ∀ s : ℕ, 2*s<N →
        ∀ᶠ T : ℝ in atTop, (D:ℝ)/2*(ε/π)^(D-1) < visitFraction H s ε a T ∧
          visitFraction H s ε a T < 2*(D:ℝ)*(A*ε/2)^(D-1) := by
  filter_upwards [UntouchedSites.gaussian_few_gate_scalar_return,gaussian_path_all_prefixes_maximally_projective] with ω hw hspec k
  intro N D H
  obtain ⟨A,hA,h⟩ := hw (k+1)
  refine ⟨A,hA,?_⟩
  intro ε hε hsmall hs' a s hs
  have hlow := scalar_fraction H (hspec k) hε hsmall a
  have hhigh := scalar_fraction H (hspec k) (mul_pos hA hε) hs' a
  have hd : (0:ℝ)<D := by dsimp [D]; positivity
  have hl := (physical_arc_bounds hε hsmall).1
  have hu := (physical_arc_bounds (mul_pos hA hε) hs').2
  have h1 : (↑D:ℝ)/2*(ε/π)^(D-1) < (D:ℝ)*(physicalArc ε)^(D-1) := by
    have hp : 0 < (ε/π)^(D-1) := by positivity
    have hp' := pow_le_pow_left₀ (by positivity) hl (D-1)
    nlinarith only [mul_le_mul_of_nonneg_left hp' hd.le,mul_pos hd hp]
  have h2 : (D:ℝ)*(physicalArc (A*ε))^(D-1) < 2*(D:ℝ)*(A*ε/2)^(D-1) := by
    have hp : 0 < (A*ε/2)^(D-1) := by positivity
    have hp' := pow_le_pow_left₀ (physicalArc_spec (mul_pos hA hε) hs').1.1.le hu (D-1)
    nlinarith only [mul_le_mul_of_nonneg_left hp' hd.le,mul_pos hd hp]
  filter_upwards [hlow.eventually_const_lt h1,hhigh.eventually_lt_const h2,eventually_ge_atTop a] with T hL hU ht
  refine ⟨hL.trans_le (visitFraction_mono H (Nat.zero_le s) ε a ht),lt_of_le_of_lt ?_ hU⟩
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr ht)
  apply measureReal_mono _ (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  exact inter_subset_inter_left _ (fun t ht' => h t ε s hs ht')

#print axioms gaussian_low_gate_occupation_order
end
end GaloisForLFunctions.HTGeometry.ShortTimeProducts
