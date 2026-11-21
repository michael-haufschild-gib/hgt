import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DilationGibbsState
import GaloisForLFunctions.HTGeometry.ArithmeticPrimeShiftSource
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Reconstruction of a normal state from finite-residue experiments

Progressively refining a residue selector extracts a single occupation-basis
entry of a trace-class operator. Creation and annihilation allow the row and
column to be chosen independently.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter Topology ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
open _root_.RHTower.PrimeCoShift

abbrev TraceClassOperator := {D : Gas →L[ℂ] Gas // D.IsTraceClass}

private theorem mem_trace_ideal (D : TraceClassOperator) : D.val ∈ hsTraceIdeal Gas := by
  obtain ⟨S,U,hS,hU,h⟩ := D.property
  rw [h]
  exact comp_mem_hsTraceIdeal hS hU

/-- Matrix entry in the positive-integer occupation basis, with row index first. -/
def occupationEntry (D : Gas →L[ℂ] Gas) (i j : ℕ+) : ℂ := D (lp.single 2 j (1 : ℂ)) i

private theorem entry_summable {D : Gas →L[ℂ] Gas} (hD : D ∈ hsTraceIdeal Gas) :
    Summable (fun n => ‖occupationEntry D n n‖) := by
  have h := summable_diag_basis_of_mem hD (HilbertSchmidt.lpBasis ℕ+)
  apply Summable.norm
  apply h.congr
  intro n
  rw [HilbertSchmidt.lpBasis_apply, lp.inner_single_left]
  simp [occupationEntry]

private def singleResidue (m k : ℕ+) (j : ZMod (m : ℕ)) : ℂ :=
  if j = ((k : ℕ) : ZMod (m : ℕ)) then 1 else 0

/-- Projection onto a single finite residue of the shell label. -/
def residueSelector (m k : ℕ+) := residueObservable m (singleResidue m k)

theorem residueSelector_boundary (m k : ℕ+) :
    Tendsto (gibbsMean (residueSelector m k)) atPartitionPole (𝓝 (((m : ℕ) : ℂ)⁻¹)) := by
  have h := periodicGibbsMean_limit m (singleResidue m k)
  have hsum : ∑ j, singleResidue m k j = 1 := by classical simp [singleResidue]
  rw [hsum, one_div] at h
  apply h.congr'
  filter_upwards with β
  change _ = opTrace ((residueObservable m (singleResidue m k)) ∘L _) / _
  rw [residueObservable_comp_gibbs]
  rfl

private theorem selector_trace_series {D : Gas →L[ℂ] Gas} (hD : D ∈ hsTraceIdeal Gas) (m k : ℕ+) :
    opTrace (residueSelector m k ∘L D) = ∑' n : ℕ+,
      if ((n : ℕ) : ZMod (m : ℕ)) = (k : ℕ) then occupationEntry D n n else 0 := by
  rw [traceIdeal_shell_diagonal (hsTraceIdeal_comp_left hD _)]
  apply tsum_congr
  intro n
  change singleResidue m k (n : ℕ) * occupationEntry D n n = _
  simp only [singleResidue, ite_mul, one_mul, zero_mul]

/-- A growing residue modulus recovers one occupation-basis diagonal entry. -/
private theorem selector_limit {D : Gas →L[ℂ] Gas} (hD : D ∈ hsTraceIdeal Gas) (k : ℕ+) :
    Tendsto (fun N : ℕ => opTrace (residueSelector (Nat.succPNat N) k ∘L D))
      atTop (𝓝 (occupationEntry D k k)) := by
  let f (N : ℕ) (n : ℕ+) : ℂ :=
    if ((n : ℕ) : ZMod (N+1)) = (k : ℕ) then occupationEntry D n n else 0
  let g (n : ℕ+) : ℂ := if n = k then occupationEntry D n n else 0
  have hp (n : ℕ+) : Tendsto (fun N => f N n) atTop (𝓝 (g n)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (max (n : ℕ) (k : ℕ))] with N hN
    have hn : (n : ℕ) < N+1 := Nat.lt_succ_of_le ((le_max_left _ _).trans hN)
    have hk : (k : ℕ) < N+1 := Nat.lt_succ_of_le ((le_max_right _ _).trans hN)
    have he : (((n : ℕ) : ZMod (N+1)) = (k : ℕ)) ↔ n = k := by
      refine ⟨fun h => PNat.coe_injective ?_, fun h => h ▸ rfl⟩
      exact (ZMod.val_natCast_of_lt hn).symm.trans
        ((congrArg ZMod.val h).trans (ZMod.val_natCast_of_lt hk))
    simp only [f, g, he]
  have hsum := tendsto_tsum_of_dominated_convergence (entry_summable hD) hp
    (Eventually.of_forall (fun N n => show ‖f N n‖ ≤ ‖occupationEntry D n n‖ by
      unfold f
      split
      · exact le_rfl
      · rw [norm_zero]; exact norm_nonneg _))
  have hsingle : ∑' n, g n = occupationEntry D k k := by
    rw [tsum_eq_single k (fun n hn => if_neg hn)]
    exact if_pos rfl
  rw [hsingle] at hsum
  exact hsum.congr' (Eventually.of_forall fun N => (selector_trace_series hD (Nat.succPNat N) k).symm)

theorem normal_selector_recovery (D : TraceClassOperator) (k : ℕ+) :
    Tendsto (fun N : ℕ => opTrace (residueSelector (Nat.succPNat N) k ∘L D.val))
      atTop (𝓝 (occupationEntry D.val k k)) := selector_limit (mem_trace_ideal D) k

/-- Creation and annihilation move the recovered entry into independently chosen row and column. -/
theorem normal_shifted_residue_recovery (D : TraceClassOperator) (a b k : ℕ+) :
    Tendsto (fun N : ℕ => opTrace (shiftObservable a b (residueSelector (Nat.succPNat N) k) ∘L D.val))
      atTop (𝓝 (occupationEntry D.val (b*k) (a*k))) := by
  let V := (primeShift a).toContinuousLinearMap
  let B := (primeCoShift b ∘L D.val) ∘L V
  have hB : B ∈ hsTraceIdeal Gas := hsTraceIdeal_comp_right (hsTraceIdeal_comp_left (mem_trace_ideal D) _) _
  have he : occupationEntry B k k = occupationEntry D.val (b*k) (a*k) := by
    change D.val ((_root_.RHTower.lpScalarInjection _ (mulLeft_injective a)) (lp.single 2 k (1 : ℂ))) (b*k) = _
    rw [_root_.RHTower.lpScalarInjection_single]
    rfl
  rw [← he]
  apply (selector_limit hB k).congr'
  filter_upwards with N
  let P := residueSelector (Nat.succPNat N) k
  exact (opTrace_comp_comm_of_mem (hsTraceIdeal_comp_left (mem_trace_ideal D) (P ∘L primeCoShift b)) V).symm

/-- Only selectors through the vacuum residue are needed to distinguish all trace-class operators. -/
theorem normal_shifted_readouts_injective :
    Function.Injective (fun D : TraceClassOperator => fun (a b : ℕ+) (N : ℕ) =>
      opTrace (shiftObservable a b (residueSelector (Nat.succPNat N) 1) ∘L D.val)) := by
  intro D E h
  apply Subtype.ext
  apply PrimeShiftSource.ext_basisVec
  intro a
  apply lp.ext
  funext b
  have hD := (normal_shifted_residue_recovery D a b 1).congr'
    (Eventually.of_forall fun N => congrFun (congrFun (congrFun h a) b) N)
  have hentry := tendsto_nhds_unique hD (normal_shifted_residue_recovery E a b 1)
  simpa only [mul_one, occupationEntry, PrimeShiftSource.basisVec] using hentry

private theorem reciprocal_modulus_limit :
    Tendsto (fun N : ℕ => (((Nat.succPNat N : ℕ+) : ℕ) : ℂ)⁻¹) atTop (𝓝 0) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)))
  change Tendsto (fun N : ℕ => ((((N + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) at h
  change Tendsto (fun N : ℕ => ((↑(N+1) : ℂ)⁻¹)) atTop (𝓝 0)
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using h

/-- Even the unshifted finite residue experiments have no trace-class boundary representative. -/
theorem no_traceClass_residue_boundary :
    ¬ ∃ D : TraceClassOperator, ∀ m k : ℕ+, Tendsto (gibbsMean (residueSelector m k))
      atPartitionPole (𝓝 (opTrace (residueSelector m k ∘L D.val))) := by
  rintro ⟨D,hD⟩
  have hm (m k : ℕ+) : opTrace (residueSelector m k ∘L D.val) = ((m : ℕ) : ℂ)⁻¹ :=
    tendsto_nhds_unique (hD m k) (residueSelector_boundary m k)
  have hz (k : ℕ+) : occupationEntry D.val k k = 0 :=
    tendsto_nhds_unique (normal_selector_recovery D k) (reciprocal_modulus_limit.congr'
      (Eventually.of_forall fun N => (hm (Nat.succPNat N) k).symm))
  have ht : opTrace D.val = 0 := by
    rw [traceIdeal_shell_diagonal (mem_trace_ideal D)]
    change (∑' n, occupationEntry D.val n n) = 0
    simp only [hz, tsum_zero]
  have hid : residueSelector 1 1 = ContinuousLinearMap.id ℂ Gas := by
    ext f n
    change (if ((n : ℕ) : ZMod 1) = 1 then (1 : ℂ) else 0) * f n = f n
    rw [if_pos (Subsingleton.elim _ _), one_mul]
  have hunit := hm 1 1
  rw [hid, id_comp, ht] at hunit
  norm_num at hunit

#print axioms residueSelector_boundary
#print axioms normal_selector_recovery
#print axioms normal_shifted_residue_recovery
#print axioms normal_shifted_readouts_injective
#print axioms no_traceClass_residue_boundary

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
