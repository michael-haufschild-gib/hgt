import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.RelativeCircuit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.Variance

/-! # Removing an arbitrary change of clock and global phase from local fields -/

open Finset
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
open SpectralEdge FirstGate.ResponseWeights
noncomputable section

/-- Covariance of the physical energies with an arbitrary local-field
response equals the Euclidean inner product of the two coefficient vectors. -/
theorem slope_traces {n : ℕ} (h g : Coeff n) :
    let E := (generator h).2.isHermitian.eigenvalues
    (∑ j, localSlope h g j)=0 ∧
    (∑ j, E j*localSlope h g j)=(2:ℝ)^(n+2)*∑ l, h l*g l := by
  intro E
  unfold localSlope
  constructor
  · rw [sum_comm]
    simp_rw [←mul_sum, localMean_sum,mul_zero,sum_const_zero]
  · simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro l _
    calc
      _ = g l*∑ j, E j*localMean (WithLp.toLp 2 h) l j := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by ring
      _ = _ := by
        rw [show (∑ j, E j*localMean (WithLp.toLp 2 h) l j)=(2:ℝ)^(n+2)*h l from
          localMean_energy_sum (WithLp.toLp 2 h) l]
        ring

/-- Subtracting the radial part of the physical local field makes its
response orthogonal to the energy vector. Retiming and a common phase
then contribute exactly two squares, including at the zero Hamiltonian. -/
theorem optimal_retiming {n : ℕ} (h g : Coeff n) (t φ : ℝ) :
    let E := (generator h).2.isHermitian.eigenvalues
    let H := ∑ l, h l^2
    let q := (∑ l, h l*g l)/H
    let v (l : PathLabel n) := g l-q*h l
    (∑ j, (localSlope h g j+t*E j+φ)^2) =
      (∑ j, (localSlope h v j)^2)+(2:ℝ)^(n+2)*(H*(t+q)^2+φ^2) := by
  intro E H q v
  let u := WithLp.toLp 2 h
  have hH : 0≤H := sum_nonneg fun _ _ => sq_nonneg _
  have hHv : (∑ l, h l*v l)=0 := by
    have hsplit : (∑ l, h l*v l)=(∑ l, h l*g l)-q*H := by
      dsimp only [H]
      rw [mul_sum,←sum_sub_distrib]
      exact sum_congr rfl fun l _ => by dsimp only [v]; ring
    rw [hsplit]
    rcases eq_or_lt_of_le hH with hz|hp
    · have hh (l : PathLabel n) : h l=0 := by
        have hle : h l^2 ≤ H := single_le_sum (fun j _ => sq_nonneg (h j)) (mem_univ l)
        nlinarith only [hle,hz]
      simp only [hh,zero_mul,sum_const_zero,←hz,mul_zero,sub_self]
    · rw [show q*H=(∑ l, h l*g l) from div_mul_cancel₀ _ hp.ne',sub_self]
  have he (j) : E j=localSlope h h j := FirstGate.energy_from_local_expectations u j
  have hs (j) : localSlope h g j=localSlope h v j+q*E j := by
    rw [he]
    dsimp only [localSlope]
    rw [mul_sum,←sum_add_distrib]
    exact sum_congr rfl fun l _ => by dsimp only [v]; ring
  have hcov := (slope_traces h v).2
  change (∑ j, E j*localSlope h v j)=_ at hcov
  rw [hHv,mul_zero] at hcov
  obtain ⟨hE,hE₂⟩ := FluxOccupation.path_spectral_moments u
  change (∑ j, E j)=0 at hE
  have hsq : (∑ j, E j^2)=(2:ℝ)^(n+2)*H := by exact_mod_cast hE₂
  have hx (j) : (localSlope h g j+t*E j+φ)^2 =
      (localSlope h v j)^2+(t+q)^2*(E j)^2+φ^2+
      (2*(t+q))*(E j*localSlope h v j)+(2*φ)*localSlope h v j+(2*(t+q)*φ)*E j := by rw [hs]; ring
  simp_rw [hx,sum_add_distrib,←mul_sum,hcov,hE,hsq,(slope_traces h v).1]
  simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,nsmul_eq_mul,
    Nat.cast_pow,Nat.cast_ofNat,mul_zero,add_zero]
  ring

#print axioms optimal_retiming
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
