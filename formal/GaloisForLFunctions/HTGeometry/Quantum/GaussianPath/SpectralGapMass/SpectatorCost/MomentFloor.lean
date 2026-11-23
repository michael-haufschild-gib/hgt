import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.PhaseTail
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.Variance
import GaloisForLFunctions.RHTower.Sieve.DirichletLipschitz

/-! # Inverse-time spectral cost from the second energy moment -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
open SpectralApproximation
noncomputable section

theorem phase_displacement (t E : ℝ) :
    ‖1-Complex.exp (-(Complex.I*((t:ℂ)*E)))‖ ≤ |t*E| := by
  have he : -(Complex.I*((t:ℂ)*E))=((-(t*E):ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [he,norm_sub_rev]
  simpa only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,sub_zero,abs_neg] using
    _root_.RHTower.Sieve.norm_exp_phase_sub_le (-(t*E)) 0

/-- The squared coefficient mass controls how many eigenlines can be
far from identity. Each far spectral feature of a cheap conjugated
circuit costs at least one entire spectator block in this count. -/
theorem variance_gate_floor {n : ℕ} (u : PathShell n) (t : ℝ)
    (W : unitaryGroup (Fin (n+2) → Bool) ℂ) {s : ℕ}
    (hfar : (1/4:ℝ) < ‖1-unitaryEvolution (pathHamiltonian u) t‖)
    (hfit : HasProjectiveCircuitApproximation (n+2) (1/10) s
      (W.val*unitaryEvolution (pathHamiltonian u) t*star W.val)) :
    1 ≤ 400*(4:ℝ)^s*t^2*‖u‖^2 := by
  classical
  let N := n+2
  let h := (isSelfAdjoint_pathHamiltonian u).isHermitian
  let V := h.eigenvectorUnitary
  let E := h.eigenvalues
  let z (j) := Complex.exp (-(Complex.I*((t:ℂ)*E j)))
  let S := univ.filter fun j => (1/20:ℝ) < ‖1-z j‖
  have he : unitaryEvolution (pathHamiltonian u) t = V.val*diagonal z*star V.val :=
    unitaryEvolution_spectral h t
  rw [he] at hfar hfit
  have hc : 2^(N-2*s) ≤ S.card := circuit_phase_tail_count V W z (by norm_num : (0:ℝ) ≤ 1/20)
    (by simpa only [show 2*(1/10:ℝ)+1/20=1/4 by norm_num] using hfar) hfit
  have hd : 2^N ≤ 4^s*S.card := by
    calc 2^N ≤ 2^(2*s+(N-2*s)) := Nat.pow_le_pow_right (by decide) (by omega)
         _ = 4^s*2^(N-2*s) := by rw [pow_add,pow_mul]; rfl
         _ ≤ _ := Nat.mul_le_mul_left _ hc
  have hsum : (S.card:ℝ)/400 ≤ t^2 * ∑ j, (E j)^2 := by
    calc (S.card:ℝ)/400 = ∑ _j ∈ S, (1/20:ℝ)^2 := by simp [nsmul_eq_mul]; ring
         _ ≤ ∑ j ∈ S, (t*E j)^2 := by
           apply sum_le_sum
           intro j hj
           have hh := ((mem_filter.mp hj).2.le.trans (phase_displacement t (E j)))
           exact (sq_le_sq₀ (by norm_num) (abs_nonneg _)).mpr hh |>.trans_eq (sq_abs _)
         _ ≤ ∑ j, (t*E j)^2 := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
         _ = _ := by simp only [mul_pow,Finset.mul_sum]
  have hmass : ∑ j, (E j)^2 = (2:ℝ)^N * ‖u‖^2 := by
    simpa only [E,h,N,EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,Nat.cast_pow,Nat.cast_ofNat] using
      (FluxOccupation.path_spectral_moments u).2
  rw [hmass] at hsum
  have hdc : (2:ℝ)^N ≤ 4^s*(S.card:ℝ) := by exact_mod_cast hd
  have hprod := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (4:ℝ)^s by positivity)
  apply (le_of_mul_le_mul_left (a:=(2:ℝ)^N) ?_ (by positivity))
  nlinarith only [hdc,hprod]

#print axioms variance_gate_floor
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
