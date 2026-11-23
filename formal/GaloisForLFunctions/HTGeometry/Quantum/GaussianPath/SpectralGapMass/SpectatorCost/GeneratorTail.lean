import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.MomentFloor

/-! # Transferring an approximation-rank bound from the generator to the orbit -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
noncomputable section

/-- Dividing the spectral displacement by energy gives an operator of
norm at most |t|, including at zero energy. -/
theorem generator_factor {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {H : Matrix I I ℂ} (h : H.IsHermitian) (t : ℝ) :
    ∃ K : Matrix I I ℂ, ‖K‖ ≤ |t| ∧ 1 - unitaryEvolution H t = K*H := by
  let V := h.eigenvectorUnitary
  let Φ := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) V
  let E (j : I) : ℂ := h.eigenvalues j
  let z (j : I) := Complex.exp (-(Complex.I*((t:ℂ)*E j)))
  let g (j : I) := (1-z j)/E j
  have he (j : I) : g j * E j = 1-z j := by
    by_cases hj : E j = 0
    · simp [g,z,hj]
    · exact div_mul_cancel₀ _ hj
  refine ⟨Φ (diagonal g),?_,?_⟩
  · change ‖V.val*diagonal g*star V.val‖ ≤ |t|
    rw [l2_opNorm_unitary_conj_eq V.property,Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg t)).mpr
    intro j
    by_cases hj : h.eigenvalues j = 0
    · simpa only [g,E,hj,Complex.ofReal_zero,div_zero,norm_zero] using abs_nonneg t
    · change ‖(1-z j)/(h.eigenvalues j:ℂ)‖ ≤ |t|
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,div_le_iff₀ (abs_pos.mpr hj)]
      exact (phase_displacement t _).trans_eq (abs_mul ..)
  have hH : H = Φ (diagonal E) := isHermitian_eq_conj_diagonal h
  have hU : unitaryEvolution H t = Φ (diagonal z) := unitaryEvolution_spectral h t
  rw [hU]
  calc 1 - Φ (diagonal z) = Φ (1-diagonal z) := by rw [map_sub,map_one]
       _ = Φ (diagonal g * diagonal E) := by
         apply congrArg Φ
         rw [Matrix.diagonal_mul_diagonal,←Matrix.diagonal_one,Matrix.diagonal_sub]
         exact congrArg Matrix.diagonal (funext fun j => (he j).symm)
       _ = _ := by rw [map_mul,←hH]

/-- A low-rank matrix can approximate a sum of noncommuting layers by
retaining the large eigenvalues of each layer. Its rank then bounds the
spectator dimension of every circuit fitting the full evolution. -/
theorem generator_rank_gate_floor {N : ℕ}
    {H : Matrix (Fin N → Bool) (Fin N → Bool) ℂ} (h : H.IsHermitian) (t : ℝ)
    (G : Matrix (Fin N → Bool) (Fin N → Bool) ℂ) (W : unitaryGroup (Fin N → Bool) ℂ)
    {s : ℕ} {ε : ℝ} (hfar : 2*ε+|t| *‖H-G‖ < ‖1-unitaryEvolution H t‖)
    (hfit : HasProjectiveCircuitApproximation N ε s (W.val*unitaryEvolution H t*star W.val)) :
    2^(N-2*s) ≤ G.rank := by
  obtain ⟨K,hK,he⟩ := generator_factor h t
  have herr : ‖(1-unitaryEvolution H t)-K*G‖ ≤ |t| *‖H-G‖ := by
    rw [he,←mul_sub]
    exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  exact (SpectralApproximation.conjugate_scalar_tail _ (K*G) W herr hfar hfit).trans
    (Matrix.rank_mul_le_right ..)

#print axioms generator_rank_gate_floor
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
