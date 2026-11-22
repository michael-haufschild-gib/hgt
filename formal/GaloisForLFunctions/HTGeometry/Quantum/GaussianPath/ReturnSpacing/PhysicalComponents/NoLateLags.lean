import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.SparseAdvantage
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.SemicircleFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.PhysicalWindow

/-! # All sparse physical return lags in a fixed window lie in the initial semicircle -/
open MeasureTheory Filter Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- At error 1/5 even a small positive density of gates cannot afford
any lag beyond the initial spectral semicircle up to a fixed horizon. -/
theorem gaussian_semicircle_only :
    ∃ b : ℝ, ∃ M : ℕ, 0<b ∧ 0<M ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      ∀ s : ℕ, M*s≤N → ∀ t : ℝ, 0<t → t≤b →
        HasProjectiveCircuitApproximation N (1/5) s (unitaryEvolution H.val t) →
          t*circuitHamiltonianSpectralWidth H<π := by
  obtain ⟨A,b,hA,hb,he⟩ := SpanningDensity.LocalEcho.gaussian_physical_window (1/2) (by norm_num)
  have hA' : 0<2*A := mul_pos two_pos hA
  obtain ⟨m,hm,hf⟩ := gaussian_sparse_advantage (2*A) (1/1000) hA' (by norm_num)
  refine ⟨b,max m 4,hb,hm.trans_le (le_max_left ..),?_⟩
  filter_upwards [he,hf,gaussian_scalar_semicircle_margin (2*A) hA'] with ω he hf hg
  filter_upwards [he,hf,hg] with n he hf hg
  intro N H s hs t ht hb' hfit
  have hN : 0<(N:ℝ) := by dsimp only [N]; positivity
  have hcost := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp hfit
  by_contra! hwide
  by_cases hshort : t≤2*A/N
  · have h := hf s ((Nat.mul_le_mul_right s (le_max_left ..)).trans hs) t (by rwa [abs_of_pos ht])
    have hbad := hg t ht hshort hwide
    change orbitCircuitDistance H s t ≤ 1/5 at hcost
    linarith only [h,hbad,hcost]
  · have htime' : 2*A ≤ t*N := (div_le_iff₀ hN).mp (le_of_not_ge hshort)
    have htail : A≤|t|*(n+1:ℕ) := by
      rw [abs_of_pos ht]
      dsimp only [N] at htime'
      push_cast at htime' ⊢
      nlinarith only [htime',mul_nonneg ht.le (Nat.cast_nonneg (α:=ℝ) n)]
    obtain ⟨z,hz,C,hC,herr⟩ := hfit
    have h := he t htail (by rwa [abs_of_pos ht]) s ⟨z,hz,C,hC,herr.trans (by norm_num)⟩
    have hs4 : 4*s≤n+2 := (Nat.mul_le_mul_right s (le_max_right ..)).trans hs
    have hs' : 4*(s:ℝ) ≤ (n:ℝ)+2 := by exact_mod_cast hs4
    push_cast at h
    linarith only [h,hs',Nat.cast_nonneg (α:=ℝ) n]

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
