import GaloisForLFunctions.HTGeometry.BohrFejerConvergence
import GaloisForLFunctions.HTGeometry.BohrConvolution

/-!
# The Fejér mean is a trigonometric polynomial supported on the spectrum

Convolving against the Fejér kernel returns the weighted partial sum of the Bohr–Fourier series: its
coefficients are the Bohr coefficients of `f` scaled by the Fejér weights.  Grouping equal
frequencies and discarding the frequencies where the Bohr coefficient vanishes therefore expresses
the Fejér mean as a trigonometric polynomial whose frequencies all lie in the spectrum of `f`.

Combined with the quantitative convergence bound this gives, for a function whose hull frequencies
lie in a single progression `βℤ`, uniform approximation by trigonometric polynomials with
frequencies in the spectrum — the strengthening of the Peter–Weyl approximation theorem the
frequency-module estimates require.
-/

open Filter Topology

open scoped BoundedContinuousFunction Real

namespace GaloisForLFunctions

open _root_.HTGeometry

noncomputable section

/-- **The Fejér mean of `f` is a trigonometric polynomial with Bohr–Fourier coefficients.** -/
theorem bohrMean_fejerKernel_translate (β : ℝ) (N : ℕ) {f : ℝ → ℂ} (hfc : Continuous f)
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) (t : ℝ) :
    bohrMean (fun u => fejerKernel β N u * f (t + u))
      = ∑ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
          (((N : ℂ) + 1)⁻¹ * bohrCoefficient f (((p.2 : ℝ) - (p.1 : ℝ)) * β))
            * expChar (((p.2 : ℝ) - (p.1 : ℝ)) * β) t := by
  classical
  set s : Finset (ℕ × ℕ) := Finset.range (N + 1) ×ˢ Finset.range (N + 1) with hs
  set c : ℕ × ℕ → ℂ := fun _ => ((N : ℂ) + 1)⁻¹ with hc
  set mu : ℕ × ℕ → ℝ := fun p => ((p.2 : ℝ) - (p.1 : ℝ)) * β with hmu
  have hker : ∀ u, fejerKernel β N u = ∑ i ∈ s, c i * bohrChar (mu i) u := by
    intro u
    rw [fejerKernel_eq_sum β N u]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hfreq : -(((p.1 : ℝ) - (p.2 : ℝ)) * β) = mu p := by
      rw [hmu]
      ring
    rw [expChar_eq_bohrChar, hfreq]
  have hfun : (fun u => fejerKernel β N u * f (t + u))
      = fun u => f (u + t) * ∑ i ∈ s, c i * bohrChar (mu i) u := by
    funext u
    rw [hker u, add_comm t u]
    ring
  rw [hfun, bohrMean_translate_mul_trigKernel s c mu hfc hfa t]

/-- **Regrouping onto the spectrum.**  A trigonometric sum whose coefficients carry a factor of the
Bohr coefficient of `f` is a trigonometric polynomial with distinct frequencies, all of them in the
spectrum of `f`. -/
theorem exists_spectrum_trigPoly_of_coeff_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (mu : ι → ℝ)
    (f : ℝ → ℂ) :
    ∃ (S : Finset ℝ) (a : ℝ → ℂ), (↑S ⊆ bohrSpectrum f) ∧
      ∀ t, ∑ i ∈ s, (c i * bohrCoefficient f (mu i)) * expChar (mu i) t
          = ∑ lam ∈ S, a lam * expChar lam t := by
  classical
  set A : ι → ℂ := fun i => c i * bohrCoefficient f (mu i) with hA
  set a : ℝ → ℂ := fun lam => ∑ i ∈ s.filter fun i => mu i = lam, A i with ha
  refine ⟨(s.image mu).filter fun lam => bohrCoefficient f lam ≠ 0, a, ?_, ?_⟩
  · intro lam hlam
    have hlam' := Finset.mem_filter.mp hlam
    exact hlam'.2
  · intro t
    have hmaps : ∀ i ∈ s, mu i ∈ s.image mu := fun i hi => Finset.mem_image_of_mem mu hi
    have hfib : ∑ lam ∈ s.image mu, ∑ i ∈ s.filter fun i => mu i = lam, A i * expChar (mu i) t
        = ∑ i ∈ s, A i * expChar (mu i) t :=
      Finset.sum_fiberwise_of_maps_to hmaps _
    have hinner : ∀ lam ∈ s.image mu,
        (∑ i ∈ s.filter fun i => mu i = lam, A i * expChar (mu i) t)
          = a lam * expChar lam t := by
      intro lam _
      rw [ha, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hmui : mu i = lam := (Finset.mem_filter.mp hi).2
      rw [hmui]
    have hgrouped : ∑ i ∈ s, A i * expChar (mu i) t
        = ∑ lam ∈ s.image mu, a lam * expChar lam t := by
      rw [← hfib]
      exact Finset.sum_congr rfl hinner
    have hdrop : ∑ lam ∈ (s.image mu).filter fun lam => bohrCoefficient f lam ≠ 0,
        a lam * expChar lam t = ∑ lam ∈ s.image mu, a lam * expChar lam t := by
      refine Finset.sum_subset (Finset.filter_subset _ _) fun lam hlam hnot => ?_
      have hzero : bohrCoefficient f lam = 0 := by
        by_contra hne
        exact hnot (Finset.mem_filter.mpr ⟨hlam, hne⟩)
      have halam : a lam = 0 := by
        simp only [ha]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hmui : mu i = lam := (Finset.mem_filter.mp hi).2
        show c i * bohrCoefficient f (mu i) = 0
        rw [hmui, hzero, mul_zero]
      rw [halam, zero_mul]
    rw [hgrouped, ← hdrop]

variable {f : ℝ →ᵇ ℂ}

/-- **Uniform approximation with frequencies in the spectrum, on a single progression.**  If every
hull frequency of `f` is an integer multiple of `β`, then `f` is a uniform limit of trigonometric
polynomials whose frequencies all lie in the Bohr spectrum of `f`. -/
theorem exists_trigPoly_spectrum_approx_lattice {β : ℝ} (hβ : β ≠ 0)
    (hf : UniformContinuous fun x => f x) (htb : HasTotallyBoundedOrbit fun x => f x)
    (hfreq : ∀ μ : ℝ, IsBohrHullFrequency f μ → ∃ k : ℤ, μ = k * β)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (S : Finset ℝ) (a : ℝ → ℂ), (↑S ⊆ bohrSpectrum fun x => f x) ∧
      ∀ t, ‖f t - ∑ lam ∈ S, a lam * expChar lam t‖ ≤ δ := by
  classical
  have hβpos : 0 < |β| := abs_pos.mpr hβ
  -- the modulus of continuity at level `δ/3`
  have hδ3 : 0 < δ / 3 := by linarith
  obtain ⟨d, hd, hdmod⟩ := Metric.uniformContinuous_iff.mp hf (δ / 3) hδ3
  set ρ : ℝ := d / 2 with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]; linarith
  have hmod : ∀ x y : ℝ, |x - y| ≤ ρ → ‖f x - f y‖ ≤ δ / 3 := by
    intro x y hxy
    have hdist : dist x y < d := by
      rw [Real.dist_eq]
      have : ρ < d := by rw [hρdef]; linarith
      linarith
    have := hdmod hdist
    rw [dist_eq_norm] at this
    exact this.le
  -- the concentration scale
  set c : ℝ := 2 * (|β| * ρ / Real.pi) ^ 2 with hcdef
  have hpi : 0 < Real.pi := Real.pi_pos
  have hc : 0 < c := by
    rw [hcdef]
    have : 0 < |β| * ρ / Real.pi := by positivity
    positivity
  have hcρ : Real.pi * Real.sqrt (c / 2) ≤ |β| * ρ := by
    have hhalf : c / 2 = (|β| * ρ / Real.pi) ^ 2 := by
      rw [hcdef]; ring
    have hnn : 0 ≤ |β| * ρ / Real.pi := by positivity
    rw [hhalf, Real.sqrt_sq hnn]
    have heq : Real.pi * (|β| * ρ / Real.pi) = |β| * ρ := by
      field_simp
    exact le_of_eq heq
  -- the Fejér order
  obtain ⟨N, hN⟩ := exists_nat_gt (12 * ‖f‖ / (δ * c))
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have htail : 2 * ‖f‖ * (2 / (((N : ℝ) + 1) * c)) ≤ δ / 3 := by
    have hden : 0 < ((N : ℝ) + 1) * c := mul_pos hNpos hc
    have hdc : 0 < δ * c := mul_pos hδ hc
    rw [div_lt_iff₀ hdc] at hN
    have hstep : 12 * ‖f‖ ≤ δ * (((N : ℝ) + 1) * c) := by nlinarith [hN, hdc]
    have hrw : 2 * ‖f‖ * (2 / (((N : ℝ) + 1) * c)) = 4 * ‖f‖ / (((N : ℝ) + 1) * c) := by
      field_simp
      ring
    rw [hrw, div_le_iff₀ hden]
    linarith [hstep]
  -- the quantitative Fejér bound
  have hbound := norm_bohrMean_fejer_sub_le hβ hf htb hfreq (show (0:ℝ) < δ / 6 by linarith) hρ
    hmod hc hcρ N
  -- the Fejér mean is a spectral polynomial
  have hfc : Continuous fun x => f x := f.continuous
  have hfa : HTGeometry.IsBohrAlmostPeriodic fun x => f x :=
    isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit htb
  obtain ⟨S, a, hSspec, hSeq⟩ := exists_spectrum_trigPoly_of_coeff_sum
    (Finset.range (N + 1) ×ˢ Finset.range (N + 1))
    (fun _ : ℕ × ℕ => ((N : ℂ) + 1)⁻¹)
    (fun p : ℕ × ℕ => ((p.2 : ℝ) - (p.1 : ℝ)) * β) (fun x => f x)
  refine ⟨S, a, hSspec, fun t => ?_⟩
  have hpoly : bohrMean (fun u => fejerKernel β N u * f (t + u))
      = ∑ lam ∈ S, a lam * expChar lam t := by
    rw [bohrMean_fejerKernel_translate β N hfc hfa t]
    exact hSeq t
  have ht := hbound t
  rw [hpoly] at ht
  rw [norm_sub_rev]
  calc ‖(∑ lam ∈ S, a lam * expChar lam t) - f t‖
      ≤ 2 * (δ / 6) + δ / 3 + 2 * ‖f‖ * (2 / (((N : ℝ) + 1) * c)) := ht
    _ ≤ δ := by linarith [htail]

end

end GaloisForLFunctions
