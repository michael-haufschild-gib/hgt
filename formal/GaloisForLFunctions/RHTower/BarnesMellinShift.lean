import GaloisForLFunctions.RHTower.BarnesMellinPowResidues

/-!
# One-pole shifts of the Mellin contour

Every ingredient of a rectangle shift is available for `F_m(w) = (-w)^m x^{-w}ζ(-sw)(-π/sin πw)`:
holomorphy off the poles, Bochner integrability of each vertical line, vanishing of the horizontal
sides, and the residue at the crossed pole.  Assembling them gives the shift identity

```text
(1/2πi)∫_{(σ')} F_m - (1/2πi)∫_{(σ)} F_m = A ,
```

with `A` the residue of the unique singularity between the two abscissae.
-/

open Complex Filter Set MeasureTheory

namespace RHTower

noncomputable section

/-- Away from the pullback of the zeta pole and from the integers the integrand is regular. -/
theorem barnes_regular_of_ne {s : ℝ} {w : ℂ}
    (hζ : -(s : ℂ) * w ≠ 1) (hint : ∀ k : ℤ, w ≠ (k : ℂ)) :
    -(s : ℂ) * w ≠ 1 ∧ Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := by
  refine ⟨hζ, ?_⟩
  intro hcon
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hcon
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  exact hint k (mul_left_cancel₀ hpi (by rw [hk]; ring))

/-- **One-pole shift of the Mellin contour.** -/
theorem verticalIntegral'_barnes_shift {s x : ℝ} (hs : 0 < s) (hx : 0 < x) (m : ℕ)
    {σ σ' : ℝ} {p A : ℂ} (hσ : σ < p.re) (hσ' : p.re < σ')
    (hreg : ∀ w : ℂ, w.re ∈ Set.Icc σ σ' → w ≠ p →
      -(s : ℂ) * w ≠ 1 ∧ Complex.sin ((Real.pi : ℂ) * w) ≠ 0)
    (hpole : (fun w : ℂ => barnesIntegrandPow s x m w - A / (w - p))
      =O[nhdsWithin p {p}ᶜ] (fun _ : ℂ => (1 : ℂ)))
    (hσsin : Real.sin (Real.pi * σ) ≠ 0) (hσz : -(s : ℝ) * σ ≠ 1)
    (hσ'sin : Real.sin (Real.pi * σ') ≠ 0) (hσ'z : -(s : ℝ) * σ' ≠ 1) :
    VerticalIntegral' (barnesIntegrandPow s x m) σ'
      - VerticalIntegral' (barnesIntegrandPow s x m) σ = A := by
  refine GaloisForLFunctions.HTGeometry.verticalIntegral'_sub_of_simple_pole hσ hσ' ?_ hpole
    (tendsto_horizontal_barnesIntegrandPow_atBot hs hx m)
    (tendsto_horizontal_barnesIntegrandPow_atTop hs hx m)
    (integrable_barnesIntegrandPow_vertical hs hx m hσz hσsin)
    (integrable_barnesIntegrandPow_vertical hs hx m hσ'z hσ'sin)
  refine holomorphicOn_barnesIntegrandPow hx m ?_
  intro w hw hne
  refine hreg w ?_ hne
  rw [Complex.mem_reProdIm] at hw
  exact hw.1

end

end RHTower
