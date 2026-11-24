import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ExitInfimum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.Density
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Thermodynamic date of the first empty-circuit exit -/

open Real Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
noncomputable section

/-- First loss of an empty-circuit fit, measured from the identity. -/
def emptyExit (ω : PathPauliDisorder) (n : ℕ) (ε : ℝ) := sInf {t : ℝ | 0 ≤ t ∧
  ¬HasProjectiveCircuitApproximation (n+2) ε 0 (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t)}

/-- The first failure is exactly the end of an initial closed fit interval. -/
theorem first_failure {P : ℝ → Prop} {a b : ℝ} (ha : 0 ≤ a) (hb : a < b)
    (h : ∀ t ∈ Icc (0 : ℝ) b, P t ↔ t ≤ a) : sInf {t : ℝ | 0 ≤ t ∧ ¬P t} = a := by
  have hh := first_exit_bracket P ha hb (a:=a)
    (fun t ht => (h t ⟨ht.1,ht.2.trans hb.le⟩).mpr ht.2) (fun t ht => (h t ht).mp)
  exact le_antisymm hh.2 hh.1

/-- The first real exit at every tolerance below the semicircle chord has
a deterministic inverse-size limit. Its clock is the same width per spin
that determines the whole initial distance profile. -/
theorem gaussian_first_empty_exit :
    ∃ w : ℝ, 0 < w ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      Tendsto (fun n : ℕ => physicalWidth ω n/((n+2 : ℕ) : ℝ)) atTop (𝓝 w) ∧
      ∀ ε ∈ Ioo (0 : ℝ) (sqrt 2), Tendsto (fun n : ℕ => (n+2 : ℕ)*emptyExit ω n ε)
        atTop (𝓝 (4*arcsin (ε/2)/w)) := by
  obtain ⟨w,hw,_,hd⟩ := gaussian_energy_density
  obtain ⟨a,_,ha,_,hc⟩ := gaussian_initial_clock
  refine ⟨w,hw,?_⟩
  filter_upwards [hd,hc] with ω hω hc
  refine ⟨hω,?_⟩
  intro ε hε
  let θ := 4*arcsin (ε/2)
  have hθ : 0 < θ := mul_pos (by norm_num) (arcsin_pos.mpr (half_pos hε.1))
  have hπ : θ < π := by
    have hh := (SharpOccupation.physicalArc_spec hε.1 hε.2).1.2
    have he := (div_lt_iff₀ pi_pos).mp hh
    dsimp [θ]; linarith only [he]
  have heps : ε ∈ Icc (0 : ℝ) 2 := ⟨hε.1.le,hε.2.le.trans (by nlinarith only [sq_sqrt (by norm_num : (0:ℝ) ≤ 2)])⟩
  have hl := (tendsto_const_nhds (x:=θ)).div hω hw.ne'
  apply hl.congr'
  filter_upwards [hc] with n hn
  let W := physicalWidth ω n
  let N : ℝ := (n+2 : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hW : 0 < W := (mul_pos ha hN).trans_le hn.1
  have he : emptyExit ω n ε=θ/W := first_failure (div_nonneg hθ.le hW.le)
    ((div_lt_div_iff_of_pos_right hW).mpr hπ) (fun t ht => hn.2.2 t ht ε heps)
  change θ/(W/N)=N*emptyExit ω n ε
  rw [he]
  field_simp [hW.ne',hN.ne']

/-- The first semicircle has a deterministic chord profile, also along
rescaled dates chosen after the disorder is observed. -/
theorem gaussian_initial_distance_profile :
    ∃ w : ℝ, 0 < w ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ u : ℕ→ℝ, ∀ x : ℝ,
      Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, 0 ≤ u n) → x*w < π →
      Tendsto (fun n : ℕ => orbitCircuitDistance (shellOperator (pathPauliDisorderShell ω n)) 0
        (u n/((n+2 : ℕ) : ℝ))) atTop (𝓝 (2*sin (x*w/4))) := by
  obtain ⟨w,hw,_,hd⟩ := gaussian_energy_density
  refine ⟨w,hw,?_⟩
  filter_upwards [hd] with ω hω
  intro u x hu hn hx
  have h := hu.mul hω
  have hc := ((continuous_sin.tendsto _).comp (h.div_const 4)).const_mul 2
  apply hc.congr'
  filter_upwards [hn,h.eventually_lt_const hx] with n hn hsmall
  let N : ℝ := (n+2 : ℕ)
  let W := physicalWidth ω n
  have hN : 0 < N := by dsimp [N]; positivity
  have he : u n/N*W=u n*(W/N) := by ring
  have hs : u n/N*W ≤ π := he.le.trans hsmall.le
  rw [empty_distance _ (div_nonneg hn hN.le) hs]
  change 2*sin (u n*(W/N)/4)=2*sin (u n/N*W/4)
  rw [he]

#print axioms gaussian_first_empty_exit
#print axioms gaussian_initial_distance_profile
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
