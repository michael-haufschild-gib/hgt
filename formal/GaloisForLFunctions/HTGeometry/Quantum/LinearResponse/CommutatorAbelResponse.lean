import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.DampedGapResponse
import GaloisForLFunctions.HTGeometry.ResolventSubordination
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import GaloisForLFunctions.HTGeometry.ChainPauliFinFamily
import GaloisForLFunctions.HTGeometry.SpectralEnsembleEigenvalueBound

/-!
# Time averages and damped commutator response

The damped Bohr filter is the Abel average of the Hamiltonian's
conjugation orbit, modulated at the selected frequency. For a local
Pauli forcing, Hilbert--Schmidt contraction bounds the response by
the squared norm of the forcing's coupling coefficients.
-/

open Matrix MeasureTheory Set
open scoped Matrix ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}

/-- Each energy-coordinate entry of the conjugation orbit rotates at
its exact Bohr frequency. -/
theorem energyCoordinates_unitaryEvolution_conj_apply (hH : H.IsHermitian)
    (t : ℝ) (X : Matrix ι ι ℂ) (i j : ι) :
    hamiltonianEnergyCoordinates hH (unitaryEvolution H t * X * star (unitaryEvolution H t)) i j =
      Complex.exp (-(Complex.I * ((t : ℂ) * (hamiltonianGap hH i j : ℂ)))) *
        hamiltonianEnergyCoordinates hH X i j := by
  let f (k : ι) := Complex.exp (-(Complex.I * ((t : ℂ) * (hH.eigenvalues k : ℂ))))
  have hU : hamiltonianEnergyCoordinates hH (unitaryEvolution H t) = Matrix.diagonal f := by
    have h := unitaryEvolution_spectral hH t
    change unitaryEvolution H t = (hamiltonianEnergyCoordinates hH).symm (Matrix.diagonal f) at h
    rw [h, StarAlgEquiv.apply_symm_apply]
  have hstar : star (f j) = Complex.exp (Complex.I * ((t : ℂ) * (hH.eigenvalues j : ℂ))) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp
  rw [map_mul, map_mul, map_star, hU, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  change f i * hamiltonianEnergyCoordinates hH X i j * star (f j) = _
  rw [hstar, mul_right_comm, ← Complex.exp_add]
  congr 1
  congr 1
  dsimp only [f, hamiltonianGap]
  rw [Complex.ofReal_sub]
  ring

/-- The damped Green readout is the exponentially weighted orbit
average, demodulated at the selected real frequency. -/
theorem energyCoordinates_dampedGapResponse_eq_abel
    (hH : H.IsHermitian) (μ : ℝ) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) (i j : ι) :
    hamiltonianEnergyCoordinates hH (hamiltonianDampedGapResponse hH μ ε X) i j =
      ((ε : ℝ) : ℂ) * ∫ t in Ioi (0 : ℝ),
        Complex.exp (-((((ε : ℝ) : ℂ) - Complex.I * (μ : ℂ)) * (t : ℂ))) *
          hamiltonianEnergyCoordinates hH (unitaryEvolution H t * X * star (unitaryEvolution H t))
            i j := by
  let g := hamiltonianGap hH i j
  let w := hamiltonianEnergyCoordinates hH X i j
  let q := ((ε : ℝ) : ℂ) + Complex.I * ((g - μ : ℝ) : ℂ)
  have hq : 0 < q.re := by
    simpa [q, Complex.mul_re] using (show 0 < (ε : ℝ) from ε.2)
  have hfun (t : ℝ) :
      Complex.exp (-((((ε : ℝ) : ℂ) - Complex.I * (μ : ℂ)) * (t : ℂ))) *
          hamiltonianEnergyCoordinates hH (unitaryEvolution H t * X * star (unitaryEvolution H t))
            i j = Complex.exp (-(q * (t : ℂ))) * w := by
    rw [energyCoordinates_unitaryEvolution_conj_apply, ← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    dsimp only [q, g]
    rw [Complex.ofReal_sub]
    ring
  simp only [hfun]
  rw [integral_mul_const, integral_Ioi_cexp_neg hq, energyCoordinates_dampedGapResponse_apply]
  let p : ℂ := (μ : ℂ) - ⟨μ, (ε : ℝ)⟩
  let d : ℂ := (g : ℂ) - ⟨μ, (ε : ℝ)⟩
  change p * (d⁻¹ * w) = ((ε : ℝ) : ℂ) * ((1 / q) * w)
  have hrot : Complex.I * d = q := by
    apply Complex.ext <;> simp [d, q, Complex.mul_re, Complex.mul_im]
  have hrotP : Complex.I * p = ((ε : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [p, Complex.mul_re, Complex.mul_im]
  have hqn : q ≠ 0 := by
    intro h
    simp [h] at hq
  have hdn : d ≠ 0 := fun h => hqn (by rw [← hrot, h, mul_zero])
  have hratio : p / d = ((ε : ℝ) : ℂ) / q := by
    apply (div_eq_div_iff hdn hqn).mpr
    rw [← hrot, ← hrotP]
    ring
  calc
    _ = (p / d) * w := by rw [div_eq_mul_inv, mul_assoc]
    _ = _ := by rw [hratio, div_eq_mul_inv, one_div, mul_assoc]

/-- Squared Hilbert--Schmidt size of a real local Pauli perturbation on
the open chain, in coupling coordinates. -/
theorem hsSqRe_chainPauliSpectralEnsemble (n : ℕ)
    (η : Fin (Fintype.card (ChainLabel n)) → ℝ) :
    hsSqRe (spectralEnsembleMatrix (chainPauliFin n) η) =
      (2 : ℝ) ^ n * ∑ a, η a ^ 2 := by
  have h : (spectralEnsembleMatrix (chainPauliFin n) η)ᴴ =
      spectralEnsembleMatrix (chainPauliFin n) η :=
    isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) η
  rw [hsSqRe, h, ← pow_two, trace_sq_spectralEnsembleMatrix]
  simp_rw [Complex.re_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · rw [trace_chainPauliFin_mul, if_pos rfl, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  · intro b _ hb
    simp [trace_chainPauliFin_mul, Ne.symm hb]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

/-- Uniform contraction for the physical nearest-neighbour Pauli
Hamiltonian at any real coupling vector and any local Pauli forcing. -/
theorem hsSqRe_pauliChainDampedGapResponse_le (n : ℕ)
    (θ η : Fin (Fintype.card (ChainLabel n)) → ℝ) (μ : ℝ) (ε : Ioi (0 : ℝ)) :
    hsSqRe (hamiltonianDampedGapResponse
        (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ) μ ε
        (spectralEnsembleMatrix (chainPauliFin n) η)) ≤
      (2 : ℝ) ^ n * ∑ a, η a ^ 2 := by
  rw [← hsSqRe_chainPauliSpectralEnsemble n η]
  exact hsSqRe_hamiltonianDampedGapResponse_le
    (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ) μ ε _

#print axioms energyCoordinates_dampedGapResponse_eq_abel
#print axioms hsSqRe_pauliChainDampedGapResponse_le

end

end GaloisForLFunctions.HTGeometry
