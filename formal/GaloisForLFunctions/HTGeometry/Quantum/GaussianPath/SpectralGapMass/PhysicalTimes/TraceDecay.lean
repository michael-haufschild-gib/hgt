import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.UniformOverlap
import GaloisForLFunctions.HTGeometry.TwoLocalProjectiveTrotterCompilerLaw

/-! # Vanishing spectral form factor throughout bounded positive times -/
open MeasureTheory Set Filter Matrix GaloisForLFunctions.RHTower
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
open SpanningDensity.FixedHorizon
noncomputable section

/-- Normalized trace of the physical Gaussian evolution. -/
def amplitude (ω : PathPauliDisorder) (n : ℕ) (t : ℝ) : ℂ :=
  (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t).trace / (2:ℂ)^(n+2)

/-- The empty circuit leaves a cut across at least half the bonds.
A large normalized trace therefore witnesses the corresponding cut event. -/
theorem trace_lt_of_no_cut_event {ω : PathPauliDisorder} {n : ℕ} {t ε : ℝ}
    (hno : ω ∉ cutOverlapEvent n t (1/2) ε) : ‖amplitude ω n t‖ < ε := by
  let C := TwoQubitCircuit.one (n+2)
  obtain ⟨c,hc⟩ := SpanningDensity.many_crossed C
  change n+1 ≤ 0+2*(SpanningDensity.crossed c).card at hc
  rw [zero_add] at hc
  have hcut : (1/2:ℝ)*(n+1:ℕ) ≤ ((SpanningDensity.crossed c).card:ℝ) := by
    have h : ((n+1:ℕ):ℝ) ≤ 2*((SpanningDensity.crossed c).card:ℝ) := by exact_mod_cast hc
    linarith only [h]
  apply lt_of_not_ge
  intro h
  apply hno ⟨C,c,hcut,?_⟩
  rw [norm_inner_symm,inner_choiVector Fintype.card_pos,show C.eval.val=1 from
    congrArg Subtype.val (TwoQubitCircuit.one_eval _),Matrix.conjTranspose_one,Matrix.one_mul]
  simpa [amplitude] using h

/-- A circuit implementing the identity has no gates, so a cut crossing
at least half the bonds tests the spectral survival amplitude itself. -/
theorem gaussian_uniform_trace_decay {a T ε : ℝ} (ha : 0<a) (hε : 0<ε) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ t∈Icc a T, ‖amplitude ω n t‖ < ε := by
  filter_upwards [gaussian_uniform_cut_overlap (T:=T) ha (by norm_num : (0:ℝ)<1/2) hε] with ω hω
  filter_upwards [hω] with n hn
  intro t ht
  exact trace_lt_of_no_cut_event (hn t ht)

/-- On a single full-measure event all bounded, positive dates separated
from zero have vanishing normalized trace, even when chosen from the draw. -/
theorem gaussian_trace_along_dates :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a T : ℝ, 0<a → ∀ t : ℕ→ℝ,
      (∀ᶠ n in atTop, t n∈Icc a T) → Tendsto (fun n => amplitude ω n (t n)) atTop (𝓝 0) := by
  have hall (k : ℕ) := gaussian_uniform_trace_decay
    (T:=(k:ℝ)+1) (by positivity : 0 < 1/((k:ℝ)+1)) (by positivity : 0 < 1/((k:ℝ)+1))
  filter_upwards [ae_all_iff.mpr hall] with ω hω
  intro a T ha t ht
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_gt (max T (max (1/a) (1/ε)))
  have h : max T (max (1/a) (1/ε)) < (k:ℝ)+1 := hk.trans (lt_add_one _)
  have hka := ((le_max_left (1/a) (1/ε)).trans (le_max_right ..)).trans_lt h
  have hkε := ((le_max_right (1/a) (1/ε)).trans (le_max_right ..)).trans_lt h
  have hpos : 0 < (k:ℝ)+1 := by positivity
  have h₁ : 1/((k:ℝ)+1)<a := (div_lt_iff₀ hpos).mpr (by
    simpa only [mul_comm a] using (div_lt_iff₀ ha).mp hka)
  have h₂ : 1/((k:ℝ)+1)<ε := (div_lt_iff₀ hpos).mpr (by
    simpa only [mul_comm ε] using (div_lt_iff₀ hε).mp hkε)
  filter_upwards [ht,hω k] with n htn hn
  rw [dist_zero_right]
  exact (hn _ ⟨h₁.le.trans htn.1,htn.2.trans ((le_max_left ..).trans h.le)⟩).trans h₂

#print axioms gaussian_uniform_trace_decay
#print axioms gaussian_trace_along_dates
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
