import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
import GaloisForLFunctions.HTGeometry.ThermodynamicProjectiveRecurrenceDesertLaw
import GaloisForLFunctions.HTGeometry.FidelityReturnExponent

/-! # Comparing full-support fidelity and the projective operator return tube -/
open Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns
noncomputable section

private def chord (x : ℝ) : ℝ := ‖Complex.exp (-(Complex.I * (x : ℂ))) - 1‖

private theorem chord_nonneg (x : ℝ) : 0 ≤ chord x := norm_nonneg _

private theorem chord_eq (x : ℝ) : chord x = ‖Complex.exp ((x : ℂ)*Complex.I)-1‖ := by
  rw [chord,norm_exp_neg_I_mul_sub_one,mul_comm Complex.I]

private theorem chord_le {x r : ℝ} (h : latticeClose (x/(2*π)) r) : chord x ≤ 2*π*r := by
  obtain ⟨m,hm⟩ := h
  have hb := norm_expI_sub_expI_le x 0 m
  simp only [sub_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero] at hb
  rw [chord_eq]
  apply hb.trans
  rw [show x-2*π*m=2*π*(x/(2*π)-m) by field_simp,abs_mul,abs_of_pos (by positivity : 0<2*π)]
  exact mul_le_mul_of_nonneg_left hm.le (by positivity)

private theorem turns_close {x ε : ℝ} (hε : 0 < ε) (h : chord x ≤ 2*ε) :
    latticeClose (x/(2*π)) ε := by
  let m := round (x/(2*π))
  have hh : |(x-0)/(2*π)-(m:ℝ)| ≤ 1/2 := by simpa only [sub_zero] using abs_sub_round (x/(2*π))
  have hs := four_mul_abs_sub_int_le_norm x 0 m hh
  simp only [sub_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,←chord_eq] at hs
  exact ⟨m,by linarith only [hε,h,hs]⟩

abbrev Register (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem anchor_norm {n : ℕ} (H : selfAdjoint (Register n)) (a : Fin n → Bool) (t : ℝ) :
    ‖unitaryEvolution H.val t-anchorPhase H.2.isHermitian.eigenvalues a t • (1 : Register n)‖ =
      ‖fun j => chord (t*(H.2.isHermitian.eigenvalues j-H.2.isHermitian.eigenvalues a))‖ := by
  rw [l2_opNorm_unitaryEvolution_sub_anchorPhase H.2.isHermitian a t]
  simp only [Pi.norm_def]
  congr 1
  apply Finset.sup_congr rfl
  intro i _
  apply NNReal.coe_injective
  change ‖Complex.exp (-(Complex.I * ((t:ℂ) * ((H.2.isHermitian.eigenvalues i:ℂ) -
    (H.2.isHermitian.eigenvalues a:ℂ))))) - 1‖ = |chord _|
  rw [abs_of_nonneg (chord_nonneg _)]
  simp only [chord,Complex.ofReal_mul,Complex.ofReal_sub]

/-- At an empty-circuit visit, every energy gap to any chosen anchor
has phase within ε turns of an integer. -/
theorem anchored_gaps_of_empty {n : ℕ} (H : selfAdjoint (Register n)) (a : Fin n → Bool)
    {t ε : ℝ} (hε : 0 < ε) (hr : HasProjectiveCircuitApproximation n ε 0 (unitaryEvolution H.val t)) :
    ∀ j, latticeClose (t*(H.2.isHermitian.eigenvalues j-H.2.isHermitian.eigenvalues a)/(2*π)) ε := by
  obtain ⟨z,_,C,hC,herr⟩ := hr
  rw [zeroGateCircuit_eval C hC] at herr
  have h := (norm_unitaryEvolution_sub_anchorPhase_le_two_mul_of_scalar H.2.isHermitian a t z).trans
    (mul_le_mul_of_nonneg_left herr zero_le_two)
  rw [anchor_norm] at h
  exact fun j => turns_close hε ((le_abs_self _).trans ((norm_le_pi_norm _ j).trans h))

/-- The uniform physical return at error ε forces a quadratic deficit
for every probability distribution on the energy levels. -/
theorem deficit_of_empty_return {n D : ℕ} (H : selfAdjoint (Register n)) (e : (Fin n → Bool) ≃ Fin D)
    (a : Fin D) (p : Fin D → ℝ) (h1 : ∑ j, p j = 1) (hp : ∀ j, 0 ≤ p j)
    {t ε : ℝ} (hε : 0 < ε) (hr : HasProjectiveCircuitApproximation n ε 0 (unitaryEvolution H.val t)) :
    spectralReturnDeficit (H.2.isHermitian.eigenvalues ∘ e.symm) p t ≤ 8*π^2*ε^2 := by
  apply spectralReturnDeficit_le_of_latticeClose _ p h1 hp a hε.le
  exact fun j => anchored_gaps_of_empty H (e.symm a) hε hr (e.symm j)

/-- With all spectral weights at least c, a deficit below δ produces a
literal empty-circuit return at operator error π√δ/c. -/
theorem empty_return_of_deficit {n D : ℕ} (H : selfAdjoint (Register n)) (e : (Fin n → Bool) ≃ Fin D)
    (a : Fin D) (p : Fin D → ℝ) (h1 : ∑ j, p j = 1) {c : ℝ} (hc : 0 < c) (hp : ∀ j, c ≤ p j)
    {t δ : ℝ} (hr : spectralReturnDeficit (H.2.isHermitian.eigenvalues ∘ e.symm) p t < δ) :
    HasProjectiveCircuitApproximation n (π*Real.sqrt δ/c) 0 (unitaryEvolution H.val t) := by
  let E := H.2.isHermitian.eigenvalues
  refine ⟨anchorPhase E (e.symm a) t,by simp [anchorPhase,Complex.norm_exp],TwoQubitCircuit.one _,le_rfl,?_⟩
  rw [TwoQubitCircuit.one_eval]
  change ‖unitaryEvolution H.val t-anchorPhase E (e.symm a) t • (1 : Register n)‖ ≤ _
  rw [anchor_norm]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ π*Real.sqrt δ/c)).mpr
  intro i
  have h := latticeClose_of_spectralReturnDeficit_lt _ p h1 (fun j => hc.le.trans (hp j)) a hc hp hr (e i)
  simp only [Function.comp_apply,e.symm_apply_apply] at h
  rw [Real.norm_eq_abs,abs_of_nonneg (chord_nonneg _)]
  exact (chord_le h).trans_eq (by field_simp)

#print axioms deficit_of_empty_return
#print axioms empty_return_of_deficit
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns
