import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.CapMass
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FinePrecision.DimensionBudget
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.LinearCap.GaussianSector

/-! # Constant-factor occupation of the same-error maximum at fine precision -/
open Set Filter MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
open SharpOccupation PrescribedTimes
noncomputable section

/-- On a Gaussian sector of mass at least aD⁻¹⁸exp[-CK(1+⌈log₂K⌉)],
the maximum at phase width D⁻² lies between D/256 and 213D. The
fraction below one 54528th of that same maximum is less than D⁻⁽ᴰ/²⁾. -/
theorem fine_precision_plateau :
    ∃ a> (0:ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      let n := k+1
      let K := n+2
      let D : ℕ := 2^K
      let y := 1/(D:ℝ)
      let ε := zeroGateArcTolerance (y^2)
      ∃ E : Set PathPauliDisorder, MeasurableSet E ∧
        a*y^18*exp (-C*(K:ℝ)*((Nat.clog 2 K:ℝ)+1)) ≤ pathPauliDisorderLaw.real E ∧
        ∀ᵐ ω ∂pathPauliDisorderLaw, ω∈E →
          let u := pathPauliDisorderShell ω n
          let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
          ∃ m : ℕ, D/256 < m ∧ m ≤ 213*D ∧ IsRecurrentOrbitCircuitMaximumAt H ε m ∧
            ∀ o : ℝ, ∀ᶠ T : ℝ in atTop, ∀ j : ℕ, 54528*j ≤ m →
              visitFraction H j ε o T < 1/(D:ℝ)^(D/2) := by
  obtain ⟨a,ha,C,hC,hsector⟩ := hierarchical_cap_mass
  refine ⟨a,ha.1,C,hC,?_⟩
  intro k hk n K D y ε
  have hK : 3 ≤ K := by dsimp only [K,n]; omega
  have hD : 8 ≤ D := Nat.pow_le_pow_right (by decide : 0<2) hK
  have hd : (8:ℝ) ≤ D := by exact_mod_cast hD
  have hD₀ : (0:ℝ)<D := by linarith only [hd]
  have hy : 0<y := one_div_pos.mpr hD₀
  have hy' : y ≤ 1/8 := one_div_le_one_div_of_le (by norm_num) hd
  have hx : y^2 ≤ 1/3 := (pow_le_pow_left₀ hy.le hy' 2).trans (by norm_num)
  have heL : y^2 ≤ ε := by
    have he := three_mul_le_arcTolerance (sq_nonneg y) hx
    linarith only [he,sq_nonneg y]
  have heU : ε ≤ 1 := by
    have he := Real.sin_le (show 0 ≤ π*y^2/2 by positivity)
    have hπ := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (sq_nonneg y)
    have hsq := pow_le_pow_left₀ hy.le hy' 2
    change 2*sin (π*y^2/2) ≤ 1
    linarith only [he,hπ,hsq]
  have he₀ : 0<ε := (sq_pos_of_pos hy).trans_le heL
  let Y := fun (ω : PathPauliDisorder) l => pathPauliDisorderShell ω n l
  let F := capEvent n ε
  have hF := measurable_capEvent n ε
  have hY := AccuracyScales.TenthPlateau.measurePreserving_pathDisorder_labels n
  have hp := hsector n (by dsimp only [n]; omega) ε ⟨he₀,heU⟩
  have hpow : y^18 ≤ ε^9 := (pow_mul y 2 9).le.trans (pow_le_pow_left₀ (sq_nonneg y) heL 9)
  refine ⟨Y ⁻¹' F,hF.preimage hY.measurable,((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow ha.1.le) (exp_pos _).le).trans hp).trans_eq
    (hY.measureReal_preimage hF.nullMeasurableSet).symm,?_⟩
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro hE u H
  obtain ⟨m,hm⟩ := twoLocal_exists_recurrent_maximum_at (by omega : 2 ≤ K) H
    (hasPauliWeightAtMost_pathHamiltonian u _) ε he₀
  have hmax : m ≤ 213*D := (JointSpeeds.orbitBudget_iff_maximum_le u ε hm).mp hE
  have hthin (o : ℝ) := inverse_square_dimension_budget hK H (hω k) o
  refine ⟨m,?_,hmax,hm,?_⟩
  · by_contra! hsmall
    obtain ⟨T,hT,hh⟩ := ((eventually_gt_atTop (0:ℝ)).and (hthin 0)).exists
    have hlow := hh m hsmall
    have hall : Icc 0 T ⊆ visitSet H m ε := fun t _ => hm.1 t
    have hfrac : visitFraction H m ε 0 T=1 := by
      rw [visitFraction,inter_eq_right.mpr hall,Real.volume_real_Icc_of_le hT.le,sub_zero,div_self hT.ne']
    change visitFraction H m ε 0 T < 1/(D:ℝ)^(D/2) at hlow
    rw [hfrac] at hlow
    exact hlow.not_ge (one_div_le_one_div_of_le zero_lt_one
      (one_le_pow₀ (by linarith only [hd] : (1:ℝ) ≤ D)) |>.trans_eq (by norm_num))
  · intro o
    filter_upwards [hthin o] with T hT j hj
    exact hT j (by omega)

#print axioms fine_precision_plateau
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
