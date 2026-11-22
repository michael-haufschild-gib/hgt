import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.CircuitProfile
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.BoundaryWidth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.ExitBracket
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.FiniteWindows

/-! # Exact field strength for loss of scalar affordability at a deep first return -/
open Filter Set Matrix MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing
noncomputable section
open PrecisionReturns

/-- Infimum of positive field strengths where the empty circuit fails
at physical error 1/10, with the date held fixed. -/
def scalarFieldExit {n : ℕ} (H Z : selfAdjoint (Register n)) (t : ℝ) : ℝ :=
  sInf {h : ℝ | 0 ≤ h ∧ 1/10 < circuitDistance 0 (unitaryEvolution (H.val+h • Z.val) t)}

private theorem field_exit_bound {n : ℕ} (H Z : selfAdjoint (Register n)) {t W η : ℝ}
    (ht : 0 < t) (hW : 0 < W) (hη : 0 ≤ η) (hsmall : η ≤ 1/4)
    (hf : ∀ u∈Icc (0:ℝ) (π/W),
      |circuitDistance 0 (unitaryEvolution (H.val+(u/t) • Z.val) t)-2*sin (u*W/4)| ≤ η) :
    |t*scalarFieldExit H Z t-4*arcsin (1/20)/W| ≤ 4*η/W := by
  let f (h : ℝ) := circuitDistance 0 (unitaryEvolution (H.val+h • Z.val) t)
  have h := scalar_exit_bracket f (mul_pos ht hW) hη hsmall (fun x hx => by
    have hxt : x*t ≤ π/W := (le_div_iff₀ hW).mpr (by
      rw [mul_assoc]
      exact (le_div_iff₀ (mul_pos ht hW)).mp hx.2)
    have hp := hf (x*t) ⟨mul_nonneg hx.1 ht.le,hxt⟩
    simpa only [mul_div_cancel_right₀ _ ht.ne',mul_assoc,f] using hp)
  change |scalarFieldExit H Z t-4*arcsin (1/20)/(t*W)| ≤ 4*η/(t*W) at h
  have he (a : ℝ) : t*(a/(t*W))=a/W := by field_simp
  calc _ = |t*(scalarFieldExit H Z t-4*arcsin (1/20)/(t*W))| := by rw [mul_sub,he]
       _ = _ := abs_mul t _
       _ ≤ t*(4*η/(t*W)) := by rw [abs_of_pos ht]; exact mul_le_mul_of_nonneg_left h ht.le
       _ = _ := he _

/-- For every onsite and bond Pauli on every sufficiently long prefix,
the actual first positive field exit at date v is asymptotic to
4 arcsin(1/20)/(v W). Here v is the first low-budget return from the
first near-Hilbert crossing and W is the width of the dephased Pauli. -/
theorem gaussian_first_return_coupling_exit :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let p := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian p,isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > 0, orbitCircuitDistance H P σ=9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ∀ l : PathLabel (k+1), let Z := couplingField l
        let W := circuitHamiltonianSpectralWidth (pinchedField H Z)
        0 < W ∧ ∀ s : ℕ, 2*s<N →
          Tendsto (fun ε => let v := firstVisit H σ s ε; v*scalarFieldExit H Z v)
            (𝓝[>] (0:ℝ)) (𝓝 (4*arcsin (1/20)/W)) := by
  filter_upwards [gaussian_first_visit_dephased_profile,gaussian_coupling_width_pos,
    UntouchedSites.gaussian_compact_gate_floor,gaussian_first_crossing_precision_wait] with ω hprof hwidth hfloor hcross
  filter_upwards [hcross] with k hk
  intro N p H P
  obtain ⟨σ,hσ,hd,hpre,_⟩ := hk
  refine ⟨σ,hσ,hd,hpre,?_⟩
  intro l Z W
  have hW := hwidth (k+1) l
  change 0 < W at hW
  refine ⟨hW,fun s hs => ?_⟩
  let v := firstVisit H σ s
  have hv : Tendsto v (𝓝[>] (0:ℝ)) atTop := by
    refine tendsto_atTop.mpr fun M => ?_
    obtain ⟨b,hb,hb'⟩ := hfloor k σ (max σ M) hσ (le_max_left ..)
    filter_upwards [Ioo_mem_nhdsGT hb] with ε hε
    have hv' := (firstVisit_isLeast H σ s hε.1).1
    apply le_of_not_gt
    intro hh
    apply hb' (v ε) ⟨hv'.1,hh.le.trans (le_max_right ..)⟩ s hs
    obtain ⟨z,hz,C,hC,he⟩ := hv'.2
    exact ⟨z,hz,C,hC,he.trans hε.2.le⟩
  obtain ⟨A,C,hA,hC,hprof'⟩ := hprof k Z
  let L := π/W
  let η (ε : ℝ) := A*ε+C*(L+L^2)/v ε
  have hη : Tendsto η (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have h₁ := hid.const_mul A
    have h₂ := (tendsto_const_nhds (x:=C*(L+L^2))).mul (tendsto_inv_atTop_zero.comp hv)
    simpa only [η,div_eq_mul_inv,Function.comp_def,id_eq,mul_zero,add_zero] using h₁.add h₂
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  filter_upwards [hη.eventually_lt_const (by norm_num : (0:ℝ)<1/4),
    hη.eventually_lt_const (div_pos (mul_pos hδ hW) (by norm_num : (0:ℝ)<4)),self_mem_nhdsWithin] with ε hsmall hδ' hε
  have hε' : 0 < ε := hε
  have ht := hσ.trans_le (firstVisit_isLeast H σ s hε').1.1
  have hL : 0 ≤ L := (div_pos pi_pos hW).le
  have hη₀ : 0 ≤ η ε := add_nonneg (mul_nonneg hA.le hε'.le) (div_nonneg (mul_nonneg hC.le (add_nonneg hL (sq_nonneg _))) ht.le)
  have hb := field_exit_bound H Z ht hW hη₀ hsmall.le (fun u hu => by
    have h := hprof' σ hσ s hs ε hε' u 0
    have huW : |u| * W ≤ π := by rw [abs_of_nonneg hu.1]; exact (le_div_iff₀ hW).mp hu.2
    have he := orbitCircuitDistance_zeroGate_eq_spectralArc (pinchedField H Z) ⟨u,huW⟩
    change circuitDistance 0 (unitaryEvolution (pinchedField H Z).val u)=2*sin (|u| * (W/4)) at he
    change |circuitDistance 0 (unitaryEvolution (H.val+(u/v ε) • Z.val) (v ε))-
      circuitDistance 0 (unitaryEvolution (pinchedField H Z).val u)| ≤ _ at h
    rw [he,abs_of_nonneg hu.1,←mul_div_assoc] at h
    apply h.trans
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ ht.le
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact add_le_add hu.2 (pow_le_pow_left₀ hu.1 hu.2 2))
  rw [Real.dist_eq]
  exact hb.trans_lt ((div_lt_iff₀ hW).mpr (by linarith only [(lt_div_iff₀ (by norm_num : (0:ℝ)<4)).mp hδ']))

#print axioms gaussian_first_return_coupling_exit
end
end GaloisForLFunctions.HTGeometry.Dephasing
