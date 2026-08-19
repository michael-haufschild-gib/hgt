import GaloisForLFunctions.HTGeometry.GammaVerticalDecay

/-!
# Vertical decay of a scaled and shifted Gamma factor

`Γ(λ(σ+it)+μ)` runs along the vertical line of abscissa `λσ + Re μ` at height `λt + Im μ`, so its
decay is the unscaled decay reparameterised.  A finite product of such factors with positive scales
therefore tends to zero without vanishing — the single analytic input of the archimedean monomial
valuation law.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- A scaled and shifted vertical argument is a vertical argument. -/
theorem gammaScale_arg_eq {lam σ t : ℝ} {μ : ℂ} :
    (lam : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) + μ
      = ((lam * σ + μ.re : ℝ) : ℂ) + ((lam * t + μ.im : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- **A scaled shifted Gamma factor tends to zero along a vertical line, without vanishing.** -/
theorem gammaScale_vertical_tendsto_nhdsWithin_zero {lam σ : ℝ} (hlam : 0 < lam) {μ : ℂ}
    (hσ : 0 < lam * σ + μ.re) :
    Tendsto (fun t : ℝ => Complex.Gamma ((lam : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) + μ))
      atTop (nhdsWithin 0 {(0 : ℂ)}ᶜ) := by
  have hinner : Tendsto (fun t : ℝ => lam * t + μ.im) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ _ (Filter.Tendsto.const_mul_atTop hlam tendsto_id)
  have hcomp := (Gamma_vertical_tendsto_nhdsWithin_zero hσ).comp hinner
  refine hcomp.congr fun t => ?_
  rw [Function.comp_apply, gammaScale_arg_eq]

/-- **The archimedean product tends to zero along a vertical line, without vanishing.** -/
theorem archimedeanProduct_vertical_tendsto_nhdsWithin_zero {d : ℕ} (hd : 0 < d)
    (lam : Fin d → ℝ) (μ : Fin d → ℂ) (hlam : ∀ j, 0 < lam j) {σ : ℝ}
    (hσ : ∀ j, 0 < lam j * σ + (μ j).re) (α : ℝ) :
    Tendsto (fun t : ℝ => Complex.exp ((α : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))
        * ∏ j : Fin d, Complex.Gamma ((lam j : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) + μ j))
      atTop (nhdsWithin 0 {(0 : ℂ)}ᶜ) := by
  have hj0 : (⟨0, hd⟩ : Fin d) ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ _
  have hprod : Tendsto
      (fun t : ℝ => ∏ j : Fin d,
        Complex.Gamma ((lam j : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) + μ j))
      atTop (nhds 0) := by
    have h := tendsto_finsetProd (Finset.univ : Finset (Fin d))
      (f := fun j (t : ℝ) => Complex.Gamma ((lam j : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) + μ j))
      (a := fun _ => (0 : ℂ))
      (fun j _ => (gammaScale_vertical_tendsto_nhdsWithin_zero (hlam j) (hσ j)).mono_right
        nhdsWithin_le_nhds)
    have hzero : ∏ _j : Fin d, (0 : ℂ) = 0 := Finset.prod_eq_zero hj0 rfl
    rwa [hzero] at h
  have hnorm : Tendsto (fun t : ℝ => ‖Complex.exp ((α : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))
      * ∏ j : Fin d,
        Complex.Gamma ((lam j : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) + μ j)‖) atTop (nhds 0) := by
    have hexp : ∀ t : ℝ, ‖Complex.exp ((α : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))‖
        = Real.exp (α * σ) := by
      intro t
      rw [Complex.norm_exp]
      congr 1
      simp
    have hpn : Tendsto (fun t : ℝ => ‖∏ j : Fin d,
        Complex.Gamma ((lam j : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) + μ j)‖) atTop (nhds 0) := by
      simpa using hprod.norm
    have hmul := hpn.const_mul (Real.exp (α * σ))
    rw [mul_zero] at hmul
    refine hmul.congr fun t => ?_
    rw [norm_mul, hexp t]
  have hlim : Tendsto (fun t : ℝ => Complex.exp ((α : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))
      * ∏ j : Fin d,
        Complex.Gamma ((lam j : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) + μ j)) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlim ?_
  filter_upwards with t
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  refine mul_ne_zero (Complex.exp_ne_zero _) (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
  refine Complex.Gamma_ne_zero fun m => ?_
  intro hcon
  have hre : ((lam j : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) + μ j).re = lam j * σ + (μ j).re := by
    simp
  rw [hcon] at hre
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have h1 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h2 := hσ j
  linarith

end

end GaloisForLFunctions.HTGeometry
