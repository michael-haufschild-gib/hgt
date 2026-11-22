import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.NoLateLags
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AngularError.Products
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.AfterScalar.UniformAngles
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # Sharp leading duration of sparse physical visits at arbitrary origins -/
open Real Set Filter MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
open FirstAscent AfterScalar AngularError
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Two physical visits in one fixed short window span at most the
maximal empty residence plus the cost correction for their combined
budgets. The earlier visit can be a positive-budget first return. -/
theorem gaussian_pair_duration :
    ∃ b C : ℝ, ∃ M : ℕ, 0<b ∧ 0<C ∧ 0<M ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let N := n+2
        let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
        let W := circuitHamiltonianSpectralWidth H
        ∀ i j : ℕ, M*(i+j)≤N → ∀ v w : ℝ, v≤w → w-v≤b →
          HasProjectiveCircuitApproximation N (1/10) i (unitaryEvolution H.val v) →
          HasProjectiveCircuitApproximation N (1/10) j (unitaryEvolution H.val w) →
          let s : ℝ := i+j
          w-v ≤ 8*arcsin (1/20)/W + C*(s*sqrt (log (N/s))/(N:ℝ)^2) := by
  obtain ⟨b,m,hb,hm,hs⟩ := gaussian_semicircle_only
  obtain ⟨_,C,a,_,k,_,hC,ha,_,_,hw⟩ := gaussian_uniform_angles
  refine ⟨b,C,max m k,hb,hC,hm.trans_le (le_max_left ..),?_⟩
  let θ := arcsin (1/20)
  have hθ : 0<θ := arcsin_pos.mpr (by norm_num)
  have hθ' : θ≤π/40 := by
    have h := GaloisForLFunctions.arcsin_le_pi_half_mul (1/20) (by norm_num) (by norm_num)
    dsimp only [θ]; linarith only [h]
  have hsine : sin θ=1/20 := sin_arcsin (by norm_num) (by norm_num)
  have herr : 2*sin θ=1/10 := by rw [hsine]; norm_num
  have herr' : 2*sin (2*θ)≤1/5 := by
    rw [sin_two_mul,hsine]
    linarith only [cos_le_one θ]
  filter_upwards [hs,hw] with ω hs hw
  filter_upwards [hs,hw] with n hs hw
  intro N H W i j hsize v w hvw hb' hv hh s
  have hN : 0<(N:ℝ) := by dsimp only [N]; positivity
  have hW : 0<W := (mul_pos ha hN).trans_le hw.1
  have hsp : 0 ≤ s := by dsimp only [s]; positivity
  have hterm : 0 ≤ C*(s*sqrt (log (N/s))/(N:ℝ)^2) := by positivity
  rcases hvw.eq_or_lt with rfl|hpos
  · rw [sub_self]
    exact add_nonneg (div_nonneg (mul_nonneg (by norm_num) hθ.le) hW.le) hterm
  have hlag := affordable_add_angle (i := i) (j := j) (x := -v) (y := w) H hθ.le
    (by linarith only [hθ',pi_pos]) (by simpa only [herr] using HasProjectiveCircuitApproximation.neg_time H hv)
    (by simpa only [herr] using hh)
  rw [show -v+w=w-v by ring] at hlag
  obtain ⟨z,hz,D,hD,herrD⟩ := hlag
  have hm' := (Nat.mul_le_mul_right (i+j) (le_max_left ..)).trans hsize
  have hk' := (Nat.mul_le_mul_right (i+j) (le_max_right ..)).trans hsize
  have ht := sub_pos.mpr hpos
  have hangle := hs (i+j) hm' (w-v) ht hb' ⟨z,hz,D,hD,herrD.trans herr'⟩
  rcases eq_zero_or_pos (i+j) with hj|hj
  · have he : orbitCircuitDistance H 0 (w-v) ≤ 2*sin (2*θ) :=
      (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp ⟨z,hz,D,hD.trans_eq hj,herrD⟩
    rw [empty_distance H ht.le hangle.le] at he
    have hhalf : (w-v)*W/4 ≤ 2*θ := by
      by_contra! h'
      have hs' := sin_lt_sin_of_lt_of_le_pi_div_two (show -(π/2) ≤ 2*θ by linarith only [hθ,pi_pos])
        (show (w-v)*W/4 ≤ π/2 by linarith only [hangle,pi_pos]) h'
      linarith only [hs',he]
    exact ((le_div_iff₀ hW).mpr (by linarith only [hhalf])).trans (le_add_of_nonneg_right hterm)
  · have h := (hw.2.2 (i+j) hj hk' (2*θ) ⟨by linarith only [hθ],le_rfl⟩).2 (w-v)
      ⟨ht.le,(le_div_iff₀ hW).mpr hangle.le⟩ ⟨z,hz,D,hD,herrD⟩
    rwa [Nat.cast_add i j,show 4*(2*θ)=8*θ by ring] at h

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
