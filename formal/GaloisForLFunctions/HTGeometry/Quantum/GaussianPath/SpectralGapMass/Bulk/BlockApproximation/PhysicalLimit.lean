import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.CriticalWindow

/-! # Gaussian characteristic profile of the physical spectrum -/
open Filter MeasureTheory Real Finset
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section

/-- On a single frozen sample, the trace at any adaptively selected date
with Nt² tending to x has limit exp(−6x). -/
theorem gaussian_spectral_profile :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (t : ℕ → ℝ) (x : ℝ),
      Tendsto (fun n => (n+2:ℕ)*(t n)^2) atTop (𝓝 x) →
      Tendsto (fun n => shellTrace (pathPauliDisorderShell ω n) (t n)) atTop (𝓝 (exp (-6*x):ℂ)) := by
  filter_upwards [gaussian_sample_characteristic,gaussian_variance_per_site] with ω hw hv
  intro t x ht
  let u (n : ℕ) := pathPauliDisorderShell ω n
  have hvar : Tendsto (fun n => shellVariance (u n)/((n+2:ℕ):ℝ)) atTop (𝓝 12) := hv
  have harg : Tendsto (fun n => -((t n)^2*shellVariance (u n)/2)) atTop (𝓝 (-6*x)) := by
    convert ((ht.mul hvar).div_const 2).neg using 1
    · funext n
      field_simp [show ((n+2:ℕ):ℝ)≠0 by positivity]
    · congr 1
      ring
  have hgauss := Complex.continuous_ofReal.continuousAt.tendsto.comp (continuous_exp.continuousAt.tendsto.comp harg)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hR : x < |x|+1 := (le_abs_self x).trans_lt (lt_add_one _)
  filter_upwards [hw (|x|+1) (by positivity) (ε/2) (half_pos hε),ht.eventually_lt_const hR,
    Metric.tendsto_nhds.mp hgauss (ε/2) (half_pos hε)] with n hn hN hg
  have h₁ := hn (t n) hN.le
  rw [dist_eq_norm] at hg ⊢
  change ‖(exp (-((t n)^2*shellVariance (u n)/2)):ℂ)-(exp (-6*x):ℂ)‖ < ε/2 at hg
  change ‖shellTrace (u n) (t n)-(exp (-6*x):ℂ)‖ < ε
  exact (norm_sub_le_norm_sub_add_norm_sub _ (exp (-((t n)^2*shellVariance (u n)/2)):ℂ) _).trans_lt
    ((add_lt_add h₁ hg).trans_eq (add_halves ε))

/-- The characteristic function of the empirical energy divided by √N
converges pointwise to that of the centered Gaussian of variance twelve. -/
theorem gaussian_scaled_characteristic :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℝ,
      Tendsto (fun n : ℕ => shellTrace (pathPauliDisorderShell ω n) (s/sqrt (n+2:ℕ)))
        atTop (𝓝 (exp (-6*s^2):ℂ)) := by
  filter_upwards [gaussian_spectral_profile] with ω hw s
  apply hw
  convert (tendsto_const_nhds (x:=s^2) (f:=atTop (α:=ℕ))) using 1
  funext n
  rw [div_pow,sq_sqrt (Nat.cast_nonneg _),←mul_div_assoc,mul_div_cancel_left₀ _ (by positivity)]

#print axioms gaussian_spectral_profile
#print axioms gaussian_scaled_characteristic
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
