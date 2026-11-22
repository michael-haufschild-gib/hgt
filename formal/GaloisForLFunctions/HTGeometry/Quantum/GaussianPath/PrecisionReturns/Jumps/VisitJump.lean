import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.GaussianLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.FiniteWindows
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # Jumps in the first return date as the physical error decreases -/
open Filter Set Matrix MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Jumps
noncomputable section

private theorem first_mono {n s : ℕ} (H : selfAdjoint (Register n)) (a : ℝ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδε : δ ≤ ε) : firstVisit H a s ε ≤ firstVisit H a s δ := by
  obtain ⟨ht,z,hz,C,hC,herr⟩ := (firstVisit_isLeast H a s hδ).1
  exact (firstVisit_isLeast H a s (hδ.trans_le hδε)).2 ⟨ht,z,hz,C,hC,herr.trans hδε⟩

/-- Multiplying precision by a fixed positive factor leaves its
logarithmic return exponent unchanged. -/
theorem scaled_exponent {f : ℝ→ℝ} {d c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun ε => log (f ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 d)) :
    Tendsto (fun ε => log (f (c*ε))/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 d) := by
  have ht : Tendsto (fun ε : ℝ => c*ε) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : Continuous (fun x : ℝ => c*x) := continuous_const.mul continuous_id
      simpa only [mul_zero] using (hcont.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos hc hε
  have hrat := (tendsto_const_div_log_one_div (-log c)).add (tendsto_const_nhds (x:=(1:ℝ)))
  have hmain := (h.comp ht).mul hrat
  rw [zero_add,mul_one] at hmain
  apply hmain.congr'
  filter_upwards [Ioo_mem_nhdsGT (by positivity : 0 < min 1 (1/c))] with ε hε
  have h1 := hε.2.trans_le (min_le_left ..)
  have h2 := hε.2.trans_le (min_le_right ..)
  have hce : c*ε < 1 := by simpa only [mul_comm] using (lt_div_iff₀ hc).mp h2
  have hlog : 0 < log (1/ε) := log_pos ((one_lt_div hε.1).mpr h1)
  have hlog' : 0 < log (1/(c*ε)) := log_pos ((one_lt_div (mul_pos hc hε.1)).mpr hce)
  have hid : log (1/(c*ε))= -log c+log (1/ε) := by
    rw [log_div one_ne_zero (mul_pos hc hε.1).ne',log_div one_ne_zero hε.1.ne',log_mul hc.ne' hε.1.ne',log_one]
    ring
  change (log (f (c*ε))/log (1/(c*ε)))*(-log c/log (1/ε)+1)=_
  rw [show -log c/log (1/ε)+1=log (1/(c*ε))/log (1/ε) by rw [hid]; field_simp]
  field_simp [hlog'.ne']

/-- For each precision ε one can identify an attained threshold ρ≤ε.
Through ρ the first date stays within one unit of its ε-value. Every
further reduction skips a gap of at least B(ε), whose logarithmic
precision exponent is the full projective return exponent. -/
theorem gaussian_first_return_precision_jumps :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∃ B : ℝ→ℝ, Tendsto B (𝓝[>] (0:ℝ)) atTop ∧
        Tendsto (fun ε => log (B ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 ((2^N-2:ℕ):ℝ)) ∧
        ∀ a > (0:ℝ), ∀ s : ℕ, 2*s < N → ∀ ε > (0:ℝ),
          let v := firstVisit H a s ε
          ∃ ρ∈Ioc (0:ℝ) ε,
            (∀ δ∈Icc ρ ε, firstVisit H a s δ∈Icc v (v+1)) ∧
            ∀ δ∈Ioo (0:ℝ) ρ, v+1+B ε ≤ firstVisit H a s δ := by
  filter_upwards [UntouchedSites.gaussian_compact_gate_floor,UntouchedSites.gaussian_few_gate_scalar_return,
    gaussian_first_return_precision_exponent] with ω hfloor hcomp hexp
  intro k N H
  obtain ⟨A,hA,hscalar⟩ := hcomp (k+1)
  let B (ε : ℝ) := firstVisit H 1 0 ((2*A)*ε)-1
  have hN : 0 < N := by dsimp [N]; omega
  have he := (hexp k 1 zero_lt_one 0 (by simpa only [mul_zero] using hN)).2.2
  have hC := mul_pos two_pos hA
  have hdiv : Tendsto B (𝓝[>] (0:ℝ)) atTop := by
    refine tendsto_atTop.mpr fun M => ?_
    let L := max M 0+1
    have hL : 1 ≤ L := by dsimp only [L]; linarith only [le_max_right M 0]
    obtain ⟨b,hb,havoid⟩ := hfloor k 1 L zero_lt_one hL
    filter_upwards [Ioo_mem_nhdsGT (div_pos hb hC)] with ε hε
    have hh := (firstVisit_isLeast H 1 0 (mul_pos hC hε.1)).1
    have hout : L < firstVisit H 1 0 ((2*A)*ε) := by
      apply lt_of_not_ge
      intro h
      apply havoid _ ⟨hh.1,h⟩ 0 (by simpa only [mul_zero] using hN)
      obtain ⟨z,hz,C,hcount,herr⟩ := hh.2
      exact ⟨z,hz,C,hcount,herr.trans (by simpa only [mul_comm] using ((lt_div_iff₀ hC).mp hε.2).le)⟩
    dsimp only [B,L] at *
    linarith only [hout,le_max_left M 0]
  refine ⟨B,hdiv,scaled_exponent hC he,?_⟩
  intro a ha s hs ε hε v
  have hv := (firstVisit_isLeast H a s hε).1
  have hpos := ha.trans_le hv.1
  have hab : v ≤ v+1 := le_add_of_nonneg_right zero_le_one
  obtain ⟨t,ht,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) (orbitCircuitDistance_lipschitz H s).continuous.continuousOn
  let ρ := orbitCircuitDistance H s t
  obtain ⟨b,hb,hsep⟩ := hfloor k v (v+1) hpos hab
  have hr : 0 < ρ := hb.trans (lt_of_not_ge fun h => hsep t ht s hs ((hasProjectiveCircuitApproximation_iff_infDist _ s b).mpr h))
  have hvfit := (hasProjectiveCircuitApproximation_iff_infDist _ s ε).mp hv.2
  have hρε : ρ ≤ ε := (hmin ⟨le_rfl,hab⟩).trans hvfit
  refine ⟨ρ,⟨hr,hρε⟩,?_,?_⟩
  · intro δ hδ
    refine ⟨first_mono H a (hr.trans_le hδ.1) hδ.2,?_⟩
    apply le_trans ((firstVisit_isLeast H a s (hr.trans_le hδ.1)).2 (show t∈visitSet H a s δ from ?_)) ht.2
    exact ⟨hv.1.trans ht.1,(hasProjectiveCircuitApproximation_iff_infDist _ s δ).mpr hδ.1⟩
  · intro δ hδ
    let u := firstVisit H a s δ
    have hu := (firstVisit_isLeast H a s hδ.1).1
    have hvu : v ≤ u := first_mono H a hδ.1 (hδ.2.le.trans hρε)
    have hlate : v+1 < u := lt_of_not_ge fun hh => hδ.2.not_ge
      ((hmin ⟨hvu,hh⟩).trans ((hasProjectiveCircuitApproximation_iff_infDist _ s δ).mp hu.2))
    obtain ⟨z,hz,C,hC,herr⟩ := affordable_add_time H (hscalar u δ s hs hu.2) ((hscalar v ε s hs hv.2).neg_time H)
    have herr' : ‖unitaryEvolution H.val (u-v)-z • C.eval.val‖ ≤ (2*A)*ε := by
      rw [sub_eq_add_neg u v]
      exact herr.trans (by linarith only [mul_le_mul_of_nonneg_left (hδ.2.le.trans hρε) hA.le])
    have hmem : u-v∈visitSet H 1 0 ((2*A)*ε) := ⟨by linarith only [hlate],z,hz,C,hC,herr'⟩
    have hl := (firstVisit_isLeast H 1 0 (mul_pos (mul_pos two_pos hA) hε)).2 hmem
    change v+1+(firstVisit H 1 0 ((2*A)*ε)-1) ≤ u
    linarith only [hl]

#print axioms gaussian_first_return_precision_jumps
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Jumps
