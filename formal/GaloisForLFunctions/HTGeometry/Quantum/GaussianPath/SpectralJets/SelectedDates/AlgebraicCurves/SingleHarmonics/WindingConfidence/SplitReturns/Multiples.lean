import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.WidthFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.AxisBox
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.WeakCutMass

/-! # Scalar returns at multiples of a prescribed full-width winding -/

open Set MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns
open PrescribedTimes PrescribedTimes.ResonantDraws WeakBonds WeakBonds.NormalizedRadius WeakBonds.SingleCut
noncomputable section

/-- Physical time of a full turn of the prescribed multiplicity. -/
def fullTurn (n m : ℕ) (x : PrefixIndex n→ℝ) : ℝ :=
  (m:ℝ)*(2*π)/circuitHamiltonianSpectralWidth (prefixGenerator n x)

/-- At a common phase return of the two blocks, the uncut evolution
adds at most elapsed time times the norm of the omitted interaction. -/
theorem perturbed_cut_return {n : ℕ} (u : PathShell n) (a : Fin (n+1)) (t : ℝ) (Q : ℕ) :
    ∃ q : ℕ, 1≤q ∧ q≤(Q+1)^(2^(leftBlock a).card+2^(rightBlock a).card) ∧
      ‖unitaryEvolution (pathHamiltonian u) (t*q)-1‖ ≤
        4*π/(Q+1:ℝ) + |t*(q:ℝ)| * ‖edgePart u a‖ := by
  obtain ⟨q,hq,hM,hfit⟩ := cut_integer_return u a t Q
  have hd := norm_unitaryEvolution_sub_le _ _ (isSelfAdjoint_pathHamiltonian u)
    (isSelfAdjoint_pathHamiltonianCut u a) (t*q)
  rw [pathHamiltonian_sub_cut] at hd
  refine ⟨q,hq,hM,?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution (pathHamiltonian u) (t*q))
    (unitaryEvolution (pathHamiltonianCut u a) (t*q)) 1).trans ((add_le_add hd hfit).trans_eq (add_comm ..))

private theorem weak_edge_norm {n : ℕ} (u : PathShell n) (a : Fin (n+1)) {δ : ℝ}
    (hw : ∀ i∈bondSites a, |u (pathCoeffEquiv n i)|≤δ) : ‖edgePart u a‖≤9*δ := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin 3 × Fin 3, δ := Finset.sum_le_sum fun ab _ => by
      rw [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one]
      simpa only [bondIndex,Equiv.apply_symm_apply] using hw (bondIndex a ab)
        (Finset.mem_image.mpr ⟨ab,Finset.mem_univ _,rfl⟩)
    _ = _ := by simp [nsmul_eq_mul]

/-- For every chosen starting winding, a single weak bond supplies an
empty return at a positive integer multiple. The admissible multiplier
depends only on the two block dimensions and the phase resolution.
The return is measured on the uncut Hamiltonian's own clock. -/
theorem gaussian_multiple_full_turn (n m Q : ℕ) (a : Fin (n+1)) {δ : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤1) :
    let M : ℕ := (Q+1)^(2^(leftBlock a).card+2^(rightBlock a).card)
    let T := π*((m:ℝ)+1)*(M:ℝ)
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    bulkMass*(2*gaussianDensityFloor*δ)^9 ≤ μ.real {x |
      2≤circuitHamiltonianSpectralWidth (prefixGenerator n x) ∧
      ∃ q : ℕ, 1≤q ∧ q≤M ∧
        pathGateDistance n 0 x (fullTurn n ((m+1)*q) x)≤4*π/(Q+1:ℝ)+9*T*δ} := by
  intro M T μ
  letI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  let j : PrefixIndex n := (pathCoeffEquiv n).symm (Sum.inl (0,0))
  let S := bondSites a
  have hj : j∉S := by
    intro h
    obtain ⟨ab,_,he⟩ := Finset.mem_image.mp h
    cases (pathCoeffEquiv n).symm.injective he
  have hmass : bulkMass*(2*gaussianDensityFloor*δ)^9≤μ.real (axisBox S j δ) := by
    simpa only [S,bondSites_card] using axisBox_mass S hj hδ hδ'
  apply hmass.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  obtain ⟨hxj,hweak⟩ := axisBox_bounds S hj hx
  let H := prefixGenerator n x
  let g := circuitHamiltonianSpectralWidth H
  have hnorm : 1≤coefficientNorm x := hxj.1.trans
    ((le_abs_self (x j)).trans (abs_coord_le_norm (WithLp.toLp 2 x) j))
  have hg : 2≤g := (show 2≤2*coefficientNorm x by linarith only [hnorm]).trans
    (twice_coefficientNorm_le_width n x)
  have hgpos : 0<g := zero_lt_two.trans_le hg
  let u : PathShell n := WithLp.toLp 2 (fun l => x ((pathCoeffEquiv n).symm l))
  have hu (i : PrefixIndex n) : u (pathCoeffEquiv n i)=x i := by
    simp only [u,Equiv.symm_apply_apply]
  have hH : numberedGenerator n x=pathHamiltonian u := by simpa only [hu] using numberedGenerator_shell u
  let t := fullTurn n (m+1) x
  obtain ⟨q,hq,hqM,hfit⟩ := perturbed_cut_return u a t Q
  have htime : t≤π*((m:ℝ)+1) := by
    change ((m+1:ℕ):ℝ)*(2*π)/g≤_
    rw [Nat.cast_succ,div_le_iff₀ hgpos]
    have hh := mul_le_mul_of_nonneg_left hg (show 0≤π*((m:ℝ)+1) by positivity)
    linarith only [hh]
  have ht : 0≤t := div_nonneg (mul_nonneg (Nat.cast_nonneg _) two_pi_pos.le) hgpos.le
  have hbound : |t*(q:ℝ)|≤T := by
    rw [abs_of_nonneg (mul_nonneg ht (Nat.cast_nonneg q))]
    exact mul_le_mul htime (by exact_mod_cast hqM) (Nat.cast_nonneg _) (by positivity)
  have hpert := mul_le_mul hbound (weak_edge_norm u a (fun i hi => by rw [hu]; exact hweak i hi))
    (norm_nonneg _) (show 0≤T by dsimp only [T]; positivity)
  have hv : fullTurn n ((m+1)*q) x=t*q := by
    dsimp only [t,fullTurn]; rw [Nat.cast_mul]; ring
  refine ⟨hg,q,hq,hqM,?_⟩
  rw [hv,pathGateDistance,hH]
  apply (hasProjectiveCircuitApproximation_iff_infDist ..).mp
  refine ⟨1,norm_one,TwoQubitCircuit.one _,le_rfl,?_⟩
  rw [TwoQubitCircuit.one_eval,one_smul]
  calc
    ‖unitaryEvolution (pathHamiltonian u) (t*q)-1‖
        ≤ 4*π/(Q+1:ℝ) + |t*(q:ℝ)| * ‖edgePart u a‖ := hfit
    _ ≤ 4*π/(Q+1:ℝ) + T*(9*δ) := add_le_add le_rfl hpert
    _ = 4*π/(Q+1:ℝ)+9*T*δ := by ring

#print axioms gaussian_multiple_full_turn
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns
