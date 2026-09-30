import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelForcedCriticalWallResidue
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalPrefixEnergyAbelBounds

/-!
# Quantized critical prefix-energy loading of the natural Wold source

An unconditional critical-wall residue has multiplicity `m >= 1`.  Every positive loading
coefficient below `m^2/|s0|^2` is exceeded at arbitrarily large natural cutoffs.  This is an
actual-source lower law, obtained without RH or an analytic-continuation premise.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower
open WoldNaturalAbelHilbert WoldNaturalAbelPrefixEnergy

/-- Natural-cutoff square energy of the genuine Wold residual. -/
noncomputable def woldNatResidualSquarePrefixEnergy (N : ℕ) : ℝ :=
  prefixEnergy (fun n => xiHeatCassiniWoldNatResidualLogDiscrepancy (n+1)) N

/-- A quantized wall residue forces positive logarithmic prefix-energy loading infinitely often. -/
theorem exists_woldNatResidualCriticalPrefixLoading :
    ∃ (s0 : ℂ) (m : ℕ), s0.re = -(1/2:ℝ) ∧ 0 < s0.im ∧ 1 ≤ m ∧
      ∀ c : ℝ, 0 < c → c < (m:ℝ)^2/‖s0‖^2 →
        ∀ N : ℕ, ∃ K : ℕ, N < K ∧
          c*Real.log (K:ℝ) < woldNatResidualSquarePrefixEnergy K := by
  obtain ⟨s0, m, hs0, him, hm, hpole⟩ := exists_woldNatAbelContinuation_forced_criticalWall_residue
  refine ⟨s0, m, hs0, him, hm, ?_⟩
  intro c hc hcWall N
  by_contra hNo
  push Not at hNo
  let r : ℕ → ℝ := fun n => xiHeatCassiniWoldNatResidualLogDiscrepancy (n+1)
  have hTail : ∀ K : ℕ, N < K → prefixEnergy r K ≤ c*Real.log (K:ℝ) := hNo
  let Chead : ℝ := prefixEnergy r (N+1)
  have hChead : 0 ≤ Chead := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hBound : ∀ K : ℕ, 0 < K → prefixEnergy r K ≤ c*Real.log (K:ℝ)+Chead := by
    intro K hK
    by_cases hNK : N < K
    · have h := hTail K hNK
      linarith
    · have hPrefix : prefixEnergy r K ≤ Chead :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (show K ≤ N+1 by omega))
          (fun n _ _ => sq_nonneg _)
      have hlog : 0 ≤ c*Real.log (K:ℝ) := mul_nonneg hc.le (Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ K by omega)))
      linarith
  let Hol : ℂ := (xiHeatCassiniWoldLogHolonomyConstant : ℂ)
  let F : ℂ → ℂ := fun s => current r s+Hol
  have hF : AnalyticOnNhd ℂ F (xiHeatCassiniWoldResidualODESector 1) := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_xiHeatCassiniWoldResidualODESector 1)
    intro s hs
    exact ((prefix_current_differentiableAt hc.le hChead hBound
      (by simpa only [neg_div] using hs.1)).add_const Hol).differentiableWithinAt
  have hsafe : Set.EqOn F (fun s => abelDirichlet woldNatDifferenceCoeff s)
      {s | s ∈ xiHeatCassiniWoldResidualODESector 1 ∧ 0 < s.re} := by
    intro s hs
    have hD := summable_naturalCpowKernel_sub_succ hs.2
    have hA := prefix_atom_summable hc.le hChead hBound (show -1/2 < s.re by linarith [hs.2])
    have hCD := hD.mul_left Hol
    have heq : (fun n : ℕ => coeffPartial woldNatDifferenceCoeff (n+1)*
        (((((n:ℝ)+1:ℝ):ℂ)^(-s))-((((n:ℝ)+2:ℝ):ℂ)^(-s)))) =
        fun n => atom r s n+Hol*naturalCpowIncrement s n := by
      funext n
      rw [coeffPartial_woldNatDifferenceCoeff]
      dsimp [r, Hol, atom, naturalCpowIncrement, naturalCpowKernel]
      push_cast
      simp only [show ((n:ℂ)+1)+1=(n:ℂ)+2 by ring]
      ring
    change current r s+Hol = ∑' n : ℕ, _
    rw [heq, hA.tsum_add hCD, tsum_mul_left, tsum_naturalCpowKernel_sub_succ hs.2]
    simp [current]
  have hHol : Tendsto (fun x : ℝ => (x:ℂ)*Hol) (𝓝[>]0) (𝓝 0) := by
    simpa using ((Complex.continuous_ofReal.tendsto 0).mul_const Hol).mono_left nhdsWithin_le_nhds
  have hCurrent : Tendsto (fun x : ℝ => (x:ℂ)*current r (s0+(x:ℂ)))
      (𝓝[>]0) (𝓝 (-(m:ℂ))) := by
    simpa only [F, mul_add, add_sub_cancel_right, sub_zero] using (hpole F hF hsafe).sub hHol
  have hLeft : Tendsto (fun x : ℝ => ‖(x:ℂ)*current r (s0+(x:ℂ))‖^2)
      (𝓝[>]0) (𝓝 ((m:ℝ)^2)) := by
    simpa only [norm_neg, Complex.norm_natCast] using hCurrent.norm.pow 2
  have hRight : Tendsto (fun x : ℝ => ‖s0+(x:ℂ)‖^2*
      (c+(c+Chead)*x)*(1+x)) (𝓝[>]0) (𝓝 (c*‖s0‖^2)) := by
    have hcont : Continuous (fun x : ℝ => ‖s0+(x:ℂ)‖^2*
      (c+(c+Chead)*x)*(1+x)) := by fun_prop
    simpa [mul_comm] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hCharge : (m:ℝ)^2 ≤ c*‖s0‖^2 :=
    le_of_tendsto_of_tendsto hLeft hRight (eventually_mem_nhdsWithin.mono (fun x hx => by
      change 0 < x at hx
      exact scaled_current_sq_le hc.le hChead hBound (by simpa only [neg_div] using hs0) hx))
  have hsNe : s0 ≠ 0 := by intro h; rw [h] at hs0; norm_num at hs0
  have hDen : 0 < ‖s0‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hsNe)
  have hSmall : c*‖s0‖^2 < (m:ℝ)^2 := (lt_div_iff₀ hDen).mp hcWall
  exact (not_lt_of_ge hCharge) hSmall

end RHTower
