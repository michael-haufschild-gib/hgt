import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.SiteAverages
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.SeamReflection
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianClock

/-! # Deterministic bandwidth per spin of one frozen Gaussian chain -/

open Filter MeasureTheory Finset
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
noncomputable section

private theorem common_limit {a d x : ℕ→ℝ} (hd : Tendsto d atTop (𝓝 0))
    (hx : ∀ m : ℕ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, dist (x n) (a m) ≤ d m+δ) :
    ∃ w : ℝ, (∀ m, dist w (a m) ≤ d m) ∧
      ∀ y : ℕ→ℝ, (∀ m : ℕ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, dist (y n) (a m) ≤ d m+δ) →
        Tendsto y atTop (𝓝 w) := by
  have hc : CauchySeq x := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨m,hm⟩ := (hd.eventually_lt_const (show (0:ℝ)<ε/4 by positivity)).exists
    obtain ⟨k,hk⟩ := eventually_atTop.mp (hx m (ε/8) (by positivity))
    refine ⟨k,fun i hi j hj => ?_⟩
    have ht := dist_triangle (x i) (a m) (x j)
    rw [dist_comm (a m) (x j)] at ht
    linarith only [ht,hk i hi,hk j hj,hm,hε]
  obtain ⟨w,hw⟩ := cauchySeq_tendsto_of_complete hc
  have hb (m : ℕ) : dist w (a m) ≤ d m := by
    exact le_of_forall_pos_le_add fun δ hδ =>
      le_of_tendsto (hw.dist tendsto_const_nhds) (hx m δ hδ)
  refine ⟨w,hb,?_⟩
  intro y hy
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨m,hm⟩ := (hd.eventually_lt_const (show (0:ℝ)<ε/4 by positivity)).exists
  filter_upwards [hy m (ε/4) (by positivity)] with n hn
  have ht := dist_triangle (y n) (a m) w
  rw [dist_comm (a m) w] at ht
  linarith only [ht,hn,hb m,hm,hε]

private theorem mean_le_density {w : ℝ} (hw : ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto
    (fun n : ℕ => physicalWidth ω n/((n+2 : ℕ) : ℝ)) atTop (𝓝 w)) (m : ℕ) :
    meanWidth m/((m+2 : ℕ) : ℝ) ≤ w := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have hf := (reflect_preserving (m+2)).quasiMeasurePreserving.ae hw
  obtain ⟨ω,h₁,h₂,h₃⟩ := (hw.and (hf.and gaussian_full_width_average)).exists
  have h := le_of_tendsto_of_tendsto ((h₃ m).const_mul 2) (h₁.add h₂) (Eventually.of_forall (fun n => by
    have hn : 0 ≤ ((n+2 : ℕ) : ℝ) := by positivity
    have hh := div_le_div_of_nonneg_right (reflected_full_widths ω m n) hn
    rwa [mul_div_assoc,add_div] at hh))
  linarith only [h]

/-- There is a positive nonrandom energy diameter per spin. Every finite
block mean per spin bounds it from below with a one-seam error. -/
theorem gaussian_energy_density :
    ∃ w : ℝ, 0 < w ∧ (∀ m : ℕ, 0 ≤ w-meanWidth m/((m+2 : ℕ) : ℝ) ∧
      w-meanWidth m/((m+2 : ℕ) : ℝ) ≤ 18*meanAbsoluteField/((m+2 : ℕ) : ℝ)) ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto
        (fun n : ℕ => physicalWidth ω n/((n+2 : ℕ) : ℝ)) atTop (𝓝 w) := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let a (m : ℕ) := meanWidth m/((m+2 : ℕ) : ℝ)
  let d (m : ℕ) := 18*meanAbsoluteField/((m+2 : ℕ) : ℝ)
  let x (ω : PathPauliDisorder) (n : ℕ) := physicalWidth ω n/((n+2 : ℕ) : ℝ)
  have hd : Tendsto d atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (18*meanAbsoluteField)).comp (tendsto_add_atTop_nat 2)
  have ht : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ m : ℕ, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop, dist (x ω n) (a m) ≤ d m+δ := by
    simpa only [Real.dist_eq] using gaussian_block_trap
  obtain ⟨ω,hω⟩ := ht.exists
  obtain ⟨w,hb,hlim⟩ := common_limit hd hω
  have hw : ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto (x ω) atTop (𝓝 w) := by
    filter_upwards [ht] with ω h
    exact hlim _ h
  obtain ⟨c,_,hc,_,hclock⟩ := gaussian_initial_clock
  obtain ⟨ξ,hξ,hW⟩ := (hclock.and hw).exists
  have hp : c ≤ w := by
    apply ge_of_tendsto hW
    filter_upwards [hξ] with n hn
    apply (le_div_iff₀ (by positivity : 0 < ((n+2 : ℕ) : ℝ))).mpr
    exact hn.1
  refine ⟨w,hc.trans_le hp,fun m => ⟨sub_nonneg.mpr (mean_le_density hw m),?_⟩,hw⟩
  exact (le_abs_self _).trans (by simpa only [Real.dist_eq] using hb m)

#print axioms gaussian_energy_density
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
