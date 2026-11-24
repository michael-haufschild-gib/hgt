import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ShortCircuitReplay.ExitBracket

/-! # First departure date after vanishing-error short-circuit returns -/

open Filter MeasureTheory Set Real
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ShortCircuitReplay
open ThermodynamicEdges
noncomputable section

/-- Deep short-circuit visits reset the first departure clock. The visits
can be chosen on the draw, including as first returns observed after a
specified crossing. -/
theorem gaussian_deep_gate_departure :
    ∃ w : ℝ, 0 < w ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      let N := fun n : ℕ => ((n+2 : ℕ):ℝ)
      let H := fun n => shellOperator (pathPauliDisorderShell ω n)
      Tendsto (fun n => physicalWidth ω n/N n) atTop (𝓝 w) ∧
      ∀ (k s : ℕ → ℕ), (∀ᶠ n in atTop, k n ≤ s n) →
        Tendsto (fun n => (s n:ℝ)/N n) atTop (𝓝 0) →
        ∀ v : ℕ → ℝ, Tendsto (fun n => orbitCircuitDistance (H n) (k n) (v n)) atTop (𝓝 0) →
          ∀ e ∈ Ioo (0:ℝ) 2, Tendsto (fun n => N n*firstDeparture (H n) (s n) (v n) e)
            atTop (𝓝 (4*arcsin (e/2)/w)) := by
  obtain ⟨w,hw,hh⟩ := gaussian_visit_departure
  refine ⟨w,hw,?_⟩
  filter_upwards [hh] with ω hω
  intro N H
  refine ⟨hω.1,?_⟩
  intro k s hk hs v hv e he
  let F := fun x : ℝ => 4*arcsin (x/2)/w
  have hF : Continuous F := by dsimp only [F]; fun_prop
  have hl : Tendsto (fun δ : ℝ => F (e-δ)-δ) (𝓝[>] 0) (𝓝 (F e)) := by
    have h : Continuous (fun δ : ℝ => F (e-δ)-δ) := (hF.comp (continuous_const.sub continuous_id)).sub continuous_id
    simpa only [sub_zero] using (h.continuousAt (x:=0)).continuousWithinAt (s:=Ioi (0:ℝ)) |>.tendsto
  have hu : Tendsto (fun δ : ℝ => F (e+δ)+δ) (𝓝[>] 0) (𝓝 (F e)) := by
    have h : Continuous (fun δ : ℝ => F (e+δ)+δ) := (hF.comp (continuous_const.add continuous_id)).add continuous_id
    simpa only [add_zero] using (h.continuousAt (x:=0)).continuousWithinAt (s:=Ioi (0:ℝ)) |>.tendsto
  have hsmall : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ ∈ Ioo 0 (min e (2-e)) :=
    Ioo_mem_nhdsGT (lt_min he.1 (sub_pos.mpr he.2))
  have bracket {δ : ℝ} (hδ : δ ∈ Ioo (0:ℝ) (min e (2-e))) :
      ∀ᶠ n in atTop, N n*firstDeparture (H n) (s n) (v n) e ∈
        Icc (F (e-δ)-δ) (F (e+δ)+δ) := by
    have hh := hω.2 k s hk hs δ e δ hδ.1.le (hδ.2.trans_le (min_le_left ..))
      (by linarith only [hδ.2.trans_le (min_le_right e (2-e))]) hδ.1
    filter_upwards [hh,hv.eventually_lt_const hδ.1] with n hn hfit
    exact hn (v n) hfit.le
  apply tendsto_order.mpr
  constructor
  · intro l h
    obtain ⟨δ,hδ,hgap⟩ := (hsmall.and (hl.eventually_const_lt h)).exists
    filter_upwards [bracket hδ] with n hn
    exact hgap.trans_le hn.1
  · intro u h
    obtain ⟨δ,hδ,hgap⟩ := (hsmall.and (hu.eventually_lt_const h)).exists
    filter_upwards [bracket hδ] with n hn
    exact hn.2.trans_lt hgap

#print axioms gaussian_deep_gate_departure
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ShortCircuitReplay
