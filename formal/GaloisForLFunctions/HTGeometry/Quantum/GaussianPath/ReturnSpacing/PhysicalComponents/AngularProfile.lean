import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.PairChord
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.WidthRatio

/-! # A continuous family of phase tests from the longitudinal field mass -/
open Matrix Real Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Variance and sign-discretization errors tend to zero uniformly on
every fixed inverse-volume window. -/
private theorem small_remainder (B : ℝ) (hB : 0<B) : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
    let N := n+2
    ∀ t : ℝ, 0≤t → t≤B/N → (sqrt 21+2)*t*‖pathPauliDisorderShell ω n‖ < 1/70 := by
  obtain ⟨_,b,_,hb,hs⟩ := gaussian_path_eventual_coefficient_mass
  let C := sqrt 21+2
  have hC : 0<C := by dsimp [C]; positivity
  have hl : Tendsto (fun n : ℕ => sqrt ((n+2:ℕ):ℝ)) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  filter_upwards [hs] with ω hω
  filter_upwards [hω,hl.eventually_gt_atTop (70*(C*B*sqrt b))] with n hn hlarge
  intro N t ht hshort
  have hN : 0<(N:ℝ) := by dsimp only [N]; positivity
  have hr := sqrt_pos.mpr hN
  have hsq := sq_sqrt hN.le
  have hshell : ‖pathPauliDisorderShell ω n‖ ≤ sqrt b*sqrt N := by
    simpa only [sqrt_sq (norm_nonneg _),sqrt_mul hb.le] using sqrt_le_sqrt hn.2
  calc
    _ ≤ C*(B/N)*(sqrt b*sqrt N) := mul_le_mul (mul_le_mul_of_nonneg_left hshort hC.le) hshell
        (norm_nonneg _) (mul_nonneg hC.le (div_nonneg hB.le hN.le))
    _ = (C*B*sqrt b)/sqrt N := by
      apply (eq_div_iff hr.ne').mpr
      calc _ = C*B*sqrt b*((sqrt N)^2/N) := by ring
           _ = _ := by rw [hsq,div_self hN.ne',mul_one]
    _ < 1/70 := by
      apply (div_lt_iff₀ hr).mpr
      change 70*(C*B*sqrt b) < sqrt (N:ℝ) at hlarge
      linarith only [hlarge]

/-- Any angle up to one twenty-fifth of twice the elapsed spectral width
can be tested by two product configurations. The error bound is uniform
over all angles and all times in an inverse-volume window. -/
theorem gaussian_chord_from_width (B : ℝ) (hB : 0 < B) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let u := pathPauliDisorderShell ω n
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
      ∀ t : ℝ, 0<t → t≤B/N → ∀ θ : ℝ, 0≤θ → θ≤π →
        25*θ ≤ 2*(t*circuitHamiltonianSpectralWidth H) →
          sin (θ/2)-1/70 < orbitCircuitDistance H 0 t := by
  filter_upwards [gaussian_width_field_ratio,small_remainder B hB] with ω hw hr
  filter_upwards [hw,hr] with n hw hr
  intro N u H t ht hshort θ hθ hπ hangle
  have hmass := mul_le_mul_of_nonneg_left hw ht.le
  have hfit : θ ≤ 2*t * ∑ i : Fin N, |u (.inl (i,2))| := by linarith only [hangle,hmass]
  have hh := paired_angle_floor u ht hθ hπ hfit
  change sin (θ/2) ≤ orbitCircuitDistance H 0 t + (sqrt 21+2)*t*‖u‖ at hh
  linarith only [hh,hr t ht.le hshort]

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
