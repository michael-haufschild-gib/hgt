import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalResidueState
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTraceIdeal
import GaloisForLFunctions.RHTower.PrimeCoShiftModel

/-!
# Multiplication of shell labels in the Gibbs state

Inserting and removing the same occupation block scales the thermal reading
of every bounded observable by the heat multiplier of that block. Distinct
blocks give zero trace against any periodic shell measurement.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter Topology ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
open _root_.RHTower.PrimeCoShift

/-- Insert a at the output and remove b at the input of a bounded observable. -/
def shiftObservable (a b : ℕ+) (A : Gas →L[ℂ] Gas) : Gas →L[ℂ] Gas :=
  (primeShift a).toContinuousLinearMap ∘L (A ∘L primeCoShift b)

/-- The arithmetic shift moves exactly the energy log b across the propagator. -/
theorem coShift_comp_gibbs (b : ℕ+) (s : {z : ℂ // 1 < z.re}) :
    primeCoShift b ∘L gibbsOperator s = heat s.val b • (gibbsOperator s ∘L primeCoShift b) := by
  ext x n
  change gibbsOperator s x (b*n) = heat s.val b * gibbsOperator s (primeCoShift b x) n
  rw [gibbsOperator_apply, gibbsOperator_apply, primeCoShift_apply, heat_mul, mul_assoc]

private theorem coShift_shift (a : ℕ+) :
    primeCoShift a ∘L (primeShift a).toContinuousLinearMap = ContinuousLinearMap.id ℂ Gas := by
  ext x n
  exact _root_.RHTower.lpScalarInjection_coordinate _ (mulLeft_injective a) x n

theorem gibbs_mem_traceIdeal (s : {z : ℂ // 1 < z.re}) : gibbsOperator s ∈ hsTraceIdeal Gas :=
  comp_mem_hsTraceIdeal (HilbertSchmidt.isHilbertSchmidt_diagOp _ _)
    (HilbertSchmidt.isHilbertSchmidt_diagOp _ _)

/-- Cyclicity moves both shifts to one side of the observable, at the energy cost of b. -/
theorem shiftObservable_trace (a b : ℕ+) (A : Gas →L[ℂ] Gas) (s : {z : ℂ // 1 < z.re}) :
    opTrace (shiftObservable a b A ∘L gibbsOperator s) =
      heat s.val b * opTrace ((primeCoShift b ∘L (primeShift a).toContinuousLinearMap) ∘L
        (A ∘L gibbsOperator s)) := by
  let V := (primeShift a).toContinuousLinearMap
  have ht := hsTraceIdeal_comp_left (gibbs_mem_traceIdeal s) (V ∘L A)
  change opTrace (V ∘L (A ∘L (primeCoShift b ∘L gibbsOperator s))) = _
  rw [coShift_comp_gibbs, comp_smul, comp_smul, opTrace_smul']
  congr 1
  exact (opTrace_comp_comm_of_mem ht (primeCoShift b)).symm

/-- Adding the same multiplicative block on both sides scales every bounded observable. -/
theorem diagonal_shift_trace (a : ℕ+) (A : Gas →L[ℂ] Gas) (s : {z : ℂ // 1 < z.re}) :
    opTrace (shiftObservable a a A ∘L gibbsOperator s) =
      heat s.val a * opTrace (A ∘L gibbsOperator s) := by
  rw [shiftObservable_trace, coShift_shift, id_comp]

/-- Bounded complex measurement of the residue of a shell. -/
def residueObservable (m : ℕ+) (F : ZMod (m : ℕ) → ℂ) : Gas →L[ℂ] Gas :=
  lpDiagonalCLM (fun n : ℕ+ => F (n : ℕ)) (C := ∑ j, ‖F j‖)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun _ =>
    Finset.single_le_sum (fun j _ => norm_nonneg (F j)) (Finset.mem_univ _)

theorem residueObservable_comp_gibbs (m : ℕ+) (F : ZMod (m : ℕ) → ℂ)
    (s : {z : ℂ // 1 < z.re}) :
    residueObservable m F ∘L gibbsOperator s = periodicGibbsOperator m F s := by
  ext x n
  change F (n : ℕ) * gibbsOperator s x n = _
  rw [gibbsOperator_apply, periodicGibbsOperator_apply, mul_assoc]

private theorem periodic_basis (m : ℕ+) (F : ZMod (m : ℕ) → ℂ)
    (s : {z : ℂ // 1 < z.re}) (i : ℕ+) :
    periodicGibbsOperator m F s (lp.single 2 i (1 : ℂ)) =
      (F (i : ℕ) * heat s.val i) • lp.single 2 i (1 : ℂ) := by
  apply lp.ext
  funext j
  rw [periodicGibbsOperator_apply]
  change _ = (F (i : ℕ) * heat s.val i) * (lp.single 2 i (1 : ℂ) : Gas) j
  by_cases hj : j = i
  · subst j
    rfl
  · simp only [lp.single_apply, Pi.single_eq_of_ne hj, mul_zero]

private theorem trace_coordinates {T : Gas →L[ℂ] Gas} (hT : T ∈ hsTraceIdeal Gas) :
    opTrace T = ∑' n : ℕ+, T (lp.single 2 n (1 : ℂ)) n := by
  rw [opTrace_eq_tsum_basis_of_mem hT (HilbertSchmidt.lpBasis ℕ+)]
  exact tsum_congr fun n => by rw [HilbertSchmidt.lpBasis_apply, lp.inner_single_left]; simp

/-- Unmatched creation and annihilation blocks have no diagonal contribution in the shell basis. -/
theorem periodic_shift_trace (m : ℕ+) (F : ZMod (m : ℕ) → ℂ) (a b : ℕ+)
    (s : {z : ℂ // 1 < z.re}) :
    opTrace (shiftObservable a b (residueObservable m F) ∘L gibbsOperator s) =
      if a = b then heat s.val a * ZMod.LFunction F s.val else 0 := by
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl, diagonal_shift_trace, residueObservable_comp_gibbs, periodicGibbs_trace]
  rw [if_neg hab, shiftObservable_trace, residueObservable_comp_gibbs]
  have hT := hsTraceIdeal_comp_left (gibbs_mem_traceIdeal s) (residueObservable m F)
  rw [residueObservable_comp_gibbs] at hT
  rw [trace_coordinates (hsTraceIdeal_comp_left hT _)]
  have hzero (i : ℕ+) :
      ((primeCoShift b ∘L (primeShift a).toContinuousLinearMap) ∘L periodicGibbsOperator m F s)
        (lp.single 2 i (1 : ℂ)) i = 0 := by
    have hne : b*i ≠ a*i := fun he => hab (mul_right_cancel he.symm)
    simp only [comp_apply, periodic_basis, map_smul]
    change (F (i : ℕ) * heat s.val i) *
      ((_root_.RHTower.lpScalarInjection _ (mulLeft_injective a)) (lp.single 2 i (1 : ℂ))) (b*i) = 0
    rw [_root_.RHTower.lpScalarInjection_single, lp.single_apply, Pi.single_eq_of_ne hne, mul_zero]
  simp only [hzero, tsum_zero, mul_zero]

/-- The normalized reading of an arbitrary bounded observable. -/
def gibbsMean (A : Gas →L[ℂ] Gas) (β : TraceTemperature) : ℂ :=
  let s : {z : ℂ // 1 < z.re} := ⟨(β.val : ℂ),β.property⟩
  opTrace (A ∘L gibbsOperator s) / opTrace (gibbsOperator s)

theorem shifted_periodic_mean (m : ℕ+) (F : ZMod (m : ℕ) → ℂ) (a b : ℕ+)
    (β : TraceTemperature) :
    gibbsMean (shiftObservable a b (residueObservable m F)) β =
      if a = b then heat β.val a * periodicGibbsMean m F β else 0 := by
  unfold gibbsMean periodicGibbsMean
  simp only [periodic_shift_trace, periodicGibbs_trace]
  split <;> simp only [mul_div_assoc, zero_div]

private theorem heat_at_pole (n : ℕ+) : Tendsto (fun β : TraceTemperature => heat β.val n)
    atPartitionPole (𝓝 (((n : ℕ) : ℂ)⁻¹)) := by
  have hc : Continuous (fun s : ℂ => heat s n) :=
    Complex.continuous_exp.comp (continuous_neg.mul continuous_const)
  have h := (hc.tendsto 1).comp (tendsto_temperature_punctured.mono_right nhdsWithin_le_nhds)
  rwa [heat_eq_cpow, Complex.cpow_neg_one] at h

/-- The boundary state separates distinct shifts and gives mass 1/a to an equal pair. -/
theorem shifted_periodic_boundary (m : ℕ+) (F : ZMod (m : ℕ) → ℂ) (a b : ℕ+) :
    Tendsto (gibbsMean (shiftObservable a b (residueObservable m F))) atPartitionPole
      (𝓝 (if a = b then ((a : ℕ) : ℂ)⁻¹ * ((∑ j, F j) / (m : ℕ)) else 0)) := by
  by_cases hab : a = b
  · rw [if_pos hab]
    exact ((heat_at_pole a).mul (periodicGibbsMean_limit m F)).congr'
      (Eventually.of_forall fun β => by rw [shifted_periodic_mean, if_pos hab])
  · rw [if_neg hab]
    exact tendsto_const_nhds.congr' (Eventually.of_forall fun β => by
      rw [shifted_periodic_mean, if_neg hab])

/-- The projection onto the shells divisible by a has limiting probability 1/a. -/
theorem range_projection_boundary (a : ℕ+) :
    Tendsto (gibbsMean ((primeShift a).toContinuousLinearMap ∘L primeCoShift a))
      atPartitionPole (𝓝 (((a : ℕ) : ℂ)⁻¹)) := by
  have hid : residueObservable 1 (fun _ => (1 : ℂ)) = ContinuousLinearMap.id ℂ Gas := by
    ext f n
    exact one_mul (f n)
  have h := shifted_periodic_boundary 1 (fun _ => (1 : ℂ)) a a
  simpa [shiftObservable, hid] using h

/-- A single creation range tests the Born normalization, independently of the choice
of any cyclic-order readout. The vacuum range has probability one at every temperature. -/
theorem range_projection_born_iff (a : ℕ+) (s : ℂ) :
    Tendsto (fun β => (gibbsMean ((primeShift a).toContinuousLinearMap ∘L primeCoShift a) β).re)
      atPartitionPole (𝓝 (‖heat s a‖^2)) ↔ a = 1 ∨ s.re = 1/2 := by
  let P := (primeShift a).toContinuousLinearMap ∘L primeCoShift a
  let w : ℝ := ((a : ℕ) : ℝ)⁻¹
  have hp : Tendsto (fun β => (gibbsMean P β).re) atPartitionPole (𝓝 w) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp (range_projection_boundary a)
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv] at h
    exact h
  have ho : Tendsto (orderProbability 1 a) atPartitionPole (𝓝 w) := by
    simpa [w] using orderProbability_limit 1 a
  have hsame (x : ℝ) : Tendsto (fun β => (gibbsMean P β).re) atPartitionPole (𝓝 x) ↔
      Tendsto (orderProbability 1 a) atPartitionPole (𝓝 x) :=
    ⟨fun h => (tendsto_nhds_unique h hp) ▸ ho, fun h => (tendsto_nhds_unique h ho) ▸ hp⟩
  rw [show (primeShift a).toContinuousLinearMap ∘L primeCoShift a = P from rfl, hsame]
  simpa [channel] using orderProbability_born_iff s 1 a

#print axioms coShift_comp_gibbs
#print axioms gibbs_mem_traceIdeal
#print axioms shiftObservable_trace
#print axioms diagonal_shift_trace
#print axioms periodic_shift_trace
#print axioms shifted_periodic_boundary
#print axioms range_projection_born_iff
#print axioms range_projection_boundary

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
