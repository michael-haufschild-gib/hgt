import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.TimeAverages.Resolution

/-! # Energy resolution supplied by a Gaussian field at a physical date -/

open Finset Real
open scoped NNReal
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
open Dephasing.PairedFields Dephasing.PairedFields.SpectralEdge
open private action from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.Moments.GaussianActions
noncomputable section
private abbrev Config (n : ℕ) := Fin n → Bool

/-- A local-field variance always resolves at least the component along
the actual Gaussian base. The bound uses the true multiset energy gap
and remains valid at zero field and for any choice of energy ranks. -/
theorem physical_energy_variance (n : ℕ) (h : Coeff n) (R : Finset (Config (n+2)))
    (b : ℝ) (p k : R → ℕ) :
    let E (j : R) := (generator h).2.isHermitian.eigenvalues j.val
    let v (l : PathLabel n) (j : R) := FirstGate.ResponseWeights.localMean (WithLp.toLp 2 h) l j.val
    let u := replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E k
    (b*u)^2 ≤ (∑ l, h l^2)*(pairVariance v b p k:ℝ) := by
  intro E v u
  have hE : E=fieldEnergy v h := funext fun j => FirstGate.energy_from_local_expectations (WithLp.toLp 2 h) j.val
  have he : b*u=∑ l, (b*slopeDifference v p k l)*h l := by
    dsimp only [u]
    rw [hE]
    exact action v b p k h
  rw [he,mul_comm (∑ l, h l^2)]
  exact sum_mul_sq_le_sq_mul_sq univ (fun l => b*slopeDifference v p k l) h

/-- Even with no averaging over dates, field noise damps every physical
pair at its energy gap. The exponent uses the length of the base field. -/
theorem fixed_date_energy_attenuation (n : ℕ) (h : Coeff n) (R : Finset (Config (n+2)))
    (a b m : ℝ) (p k : R → ℕ) :
    let E (j : R) := (generator h).2.isHermitian.eigenvalues j.val
    let v (l : PathLabel n) (j : R) := FirstGate.ResponseWeights.localMean (WithLp.toLp 2 h) l j.val
    let u := replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E k
    ‖timeActionKernel m (a*u) (pairVariance v b p k) 0‖ ≤
      exp (-(m*b*u)^2/(2*∑ l, h l^2)) := by
  intro E v u
  let G := ∑ l, h l^2
  let c : ℝ := pairVariance v b p k
  have hc : 0≤c := (pairVariance v b p k).coe_nonneg
  have hG : 0≤G := sum_nonneg fun _ _ => sq_nonneg _
  have hvar : (b*u)^2 ≤ G*c := physical_energy_variance n h R b p k
  rw [norm_time_action]
  simp only [NNReal.coe_zero,mul_zero,zero_mul,add_zero,add_comm 1 (0:ℝ),zero_add,
    sqrt_one,inv_one,one_mul,mul_one]
  apply exp_le_exp.mpr
  change -(c*m^2)/2 ≤ -(m*b*u)^2/(2*G)
  rcases hG.eq_or_lt with hz|hp
  · rw [←hz,mul_zero,div_zero]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hc (sq_nonneg m))) (by norm_num)
  · apply (le_div_iff₀ (mul_pos (by norm_num) hp)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hvar (sq_nonneg m)]

/-- For positive base norm, a resolved radial energy gap suffices at a
Gaussian date. The discarded transverse variance is nonnegative whenever
the squared center is at least twice the resolution times the date variance. -/
theorem physical_radial_resolution (n : ℕ) (h : Coeff n) (R : Finset (Config (n+2)))
    (a b m H : ℝ) (V : ℝ≥0) (p k : R → ℕ) :
    let E (j : R) := (generator h).2.isHermitian.eigenvalues j.val
    let v (l : PathLabel n) (j : R) := FirstGate.ResponseWeights.localMean (WithLp.toLp 2 h) l j.val
    let u := replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E k
    let G := ∑ l, h l^2
    let M := m^2-2*H*V
    0<G → 0≤M → 2*H*G ≤ (V*a^2*G+M*b^2)*u^2 →
      ‖timeActionKernel m (a*u) (pairVariance v b p k) V‖ ≤ exp (-H) := by
  intro E v u G M hG hM hcut
  have hv : (b*u)^2 ≤ G*(pairVariance v b p k:ℝ) := physical_energy_variance n h R b p k
  apply resolved_action_le
  apply le_of_mul_le_mul_right (a:=G) _ hG
  change 2*H*G ≤ (M*(pairVariance v b p k:ℝ)+V*(a*u)^2)*G
  nlinarith only [hcut,mul_le_mul_of_nonneg_left hv hM]

#print axioms physical_energy_variance
#print axioms fixed_date_energy_attenuation
#print axioms physical_radial_resolution
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
