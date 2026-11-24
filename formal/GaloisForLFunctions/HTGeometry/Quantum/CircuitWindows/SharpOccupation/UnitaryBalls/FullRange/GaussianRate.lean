import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.CircuitCover
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.GaussianRate
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.GaussianOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateOccupationScaling

/-! # Affordable-time exponent on the entire operator-error interval -/
open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
noncomputable section

private theorem envelope {s : ℕ → ℕ} (hs : subcriticalBudget s) (m : ℕ)
    {η y b : ℝ} (hη : 0<η) (hy : y∈Ioo (0:ℝ) 1) (hyb : y<b) :
    ∀ᶠ n : ℕ in atTop, (m:ℝ)*(((s n:ℝ)+1)*(((n+1:ℝ)^2)*(1+4*(s n:ℝ)/η)^32)^(s n))*y^(2^n) < b^(2^n:ℕ) := by
  filter_upwards [enlarged_arc_eventually_lt hs (36+128/η) y b hy.1 hyb,
    budget_le_dimension_eventually hs,eventually_ge_atTop m] with n hrate hbudget hn
  let D := (2:ℕ)^n
  have hD : 0<D := Nat.two_pow_pos _
  have hm : (m:ℝ)≤(2:ℝ)^n := by exact_mod_cast hn.trans (Nat.lt_two_pow_self (n:=n)).le
  have hp : y^D≤y^(D-1) := by
    calc y^D = y^(D-1)*y := by rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤D)]
         _ ≤ y^(D-1)*1 := mul_le_mul_of_nonneg_left hy.2.le (pow_nonneg hy.1.le _)
         _ = _ := mul_one _
  rw [mul_comm (m:ℝ),mul_assoc]
  exact (mul_le_mul (net_envelope_le_exp n (s n) η hη hbudget)
    (mul_le_mul hm hp (pow_nonneg hy.1.le _) (by positivity))
    (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hy.1.le _)) (Real.exp_pos _).le).trans_lt hrate

/-- A subcritical number of gates leaves the scalar return exponent unchanged
for every angular width below a full turn, including widths above a semicircle. -/
theorem gaussian_occupation_rate :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ, subcriticalBudget s →
      ∀ x ∈ Ioo (0:ℝ) 1, ∀ l b : ℝ, 0≤l → l<x → x<b → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D : ℕ := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        ∀ᶠ T : ℝ in atTop, ∀ j ≤ s N, l^D < visitFraction H j (zeroGateArcTolerance x) 0 T ∧
          visitFraction H j (zeroGateArcTolerance x) 0 T < b^D := by
  filter_upwards [PhaseBoundary.gaussian_uniform_affordable_fraction,gaussian_path_zeroGateFullOccupation_from_start] with ω hlim hzero
  intro s hs x hx l b hl hlx hxb
  obtain ⟨y,hxy,hy'⟩ := exists_between (lt_min hxb hx.2)
  have hy : y∈Ioo (0:ℝ) 1 := ⟨hx.1.trans hxy,hy'.trans_le (min_le_right ..)⟩
  let η := (zeroGateArcTolerance y-zeroGateArcTolerance x)/2
  have hη : 0<η := half_pos (sub_pos.mpr (strictMonoOn_zeroGateArcTolerance_full
    ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩ hxy))
  obtain ⟨m,hm⟩ := exists_nat_gt (2*Real.pi/η)
  have hm' : 0 < m := Nat.cast_pos.mp ((div_pos Real.two_pi_pos hη).trans hm)
  have hgrid : 2*Real.pi/m ≤ η := (div_le_iff₀ (Nat.cast_pos.mpr hm')).mpr (by
    simpa only [mul_comm η] using ((div_lt_iff₀ hη).mp hm).le)
  have hprice : zeroGateArcTolerance x+η+2*Real.pi/m ≤ zeroGateArcTolerance y := by
    dsimp only [η] at hgrid ⊢
    linarith only [hgrid]
  filter_upwards [(tendsto_add_atTop_nat 3).eventually (envelope hs m hη hy (hy'.trans_le (min_le_left ..)))] with k he
  intro N D H
  let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  have hupper := (circuit_volume_bound e V (s N) m hm' hη ⟨hy.1.le,hy.2⟩ hprice).trans_lt he
  have hhi := (hlim k (s N) (zeroGateArcTolerance x) (fun _ => 0)).eventually_lt_const hupper
  let r : Icc (0:ℝ) 1 := ⟨x,hx.1.le,hx.2.le⟩
  have hD : 0<D := Nat.two_pow_pos _
  have hlower : l^D < zeroGateFullArcMass N r := by
    apply (pow_lt_pow_left₀ hlx hl hD.ne').trans_le
    apply le_trans _ (zeroGateFullArcMass_bounds N r).1
    change x^D≤x^(D-1)
    calc x^D = x^(D-1)*x := by rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤D)]
         _ ≤ x^(D-1)*1 := mul_le_mul_of_nonneg_left hx.2.le (pow_nonneg hx.1.le _)
         _ = _ := mul_one _
  have hset : visitSet H 0 (zeroGateArcTolerance x) = zeroGateReturnSet H r :=
    Set.ext fun _ => hasProjectiveCircuitApproximation_iff_infDist _ _ _
  have hlo := (hzero k r 0).eventually_const_lt hlower
  filter_upwards [hlo,hhi,eventually_ge_atTop (0:ℝ)] with T hL hU hT j hj
  have hL' : l^D < visitFraction H 0 (zeroGateArcTolerance x) 0 T := by
    simpa only [visitFraction,hset] using hL
  have hU' : visitFraction H (s N) (zeroGateArcTolerance x) 0 T < b^D := by simpa only [zero_add] using hU
  exact ⟨hL'.trans_le (visitFraction_mono H (Nat.zero_le j) _ _ _ hT),
    (visitFraction_mono H hj _ _ _ hT).trans_lt hU'⟩

#print axioms gaussian_occupation_rate
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
