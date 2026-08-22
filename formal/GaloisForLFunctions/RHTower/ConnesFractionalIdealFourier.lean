import GaloisForLFunctions.RHTower.ConnesSelfDualIndicator

/-!
# §VII (21)–(22) at a finite place, and App II (28): the transform of a fractional ideal

§VII (21)(22) and Appendix II (28) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Connes' infrared cut-off `ρ_Λ` is the indicator of the module ball.  At a non-archimedean place
that ball is a *fractional ideal* `c R`, and its Fourier transform is again the indicator of a
fractional ideal, scaled by the module of `c`:

  `F(1_{cR})(x) = |c| · 1_R(c x) = |c| · 1_{c^{-1}R}(x)`.

This is `connes_selfDual_indicator` transported by the dilation `y = c z`; it is also exactly the
computation `1̂_{R^*} = 1_R − |π| 1_{π^{-1}R}` of Appendix II (28), which follows by subtracting
the two fractional ideals `R` and `πR`.

Everything is unconditional given the data: a translation-invariant measure, a subgroup of mass
one closed under multiplication, an additive character with Connes' two normalisations, and the
dilation law that *defines* the module of `c`.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {K : Type*} [CommRing K] [MeasurableSpace K] [MeasurableAdd K]
  {μ : Measure K} [μ.IsAddLeftInvariant]

/-- **§VII (21)–(22) at a finite place.**  The transform of the indicator of the fractional ideal
`c R` is `|c|` times the indicator of the dual fractional ideal. -/
theorem connes_fractionalIdeal_fourier {R : AddSubgroup K}
    (hR : MeasurableSet (R : Set K)) (hmass : μ.real (R : Set K) = 1)
    {α : K → ℂ} (hαadd : ∀ a b : K, α (a + b) = α a * α b)
    (hαtriv : ∀ y ∈ R, α y = 1)
    (hRmul : ∀ x ∈ R, ∀ y ∈ R, x * y ∈ R)
    (hnontriv : ∀ x : K, x ∉ R → ∃ y ∈ R, α (x * y) ≠ 1)
    (c : Kˣ) {m : ℂ}
    (hscale : ∀ g : K → ℂ, (∫ y : K, g y ∂μ) = m * ∫ z : K, g (((c : Kˣ) : K) * z) ∂μ)
    (x : K) :
    (∫ y : K, Set.indicator ((fun z : K => ((c : Kˣ) : K) * z) '' (R : Set K))
        (fun y : K => α (x * y)) y ∂μ)
      = m * Set.indicator (R : Set K) (fun _ : K => (1 : ℂ)) (((c : Kˣ) : K) * x) := by
  have hmemiff : ∀ z : K,
      (((c : Kˣ) : K) * z) ∈ (fun z : K => ((c : Kˣ) : K) * z) '' (R : Set K) ↔ z ∈ (R : Set K) := by
    intro z
    constructor
    · rintro ⟨w, hw, hcw⟩
      have hcw' : ((c : Kˣ) : K) * w = ((c : Kˣ) : K) * z := hcw
      have hinv : ((c⁻¹ : Kˣ) : K) * ((c : Kˣ) : K) = 1 := c.inv_mul
      have hwz : w = z := by
        calc w = 1 * w := (one_mul w).symm
          _ = (((c⁻¹ : Kˣ) : K) * ((c : Kˣ) : K)) * w := by rw [hinv]
          _ = ((c⁻¹ : Kˣ) : K) * (((c : Kˣ) : K) * w) := by ring
          _ = ((c⁻¹ : Kˣ) : K) * (((c : Kˣ) : K) * z) := by rw [hcw']
          _ = (((c⁻¹ : Kˣ) : K) * ((c : Kˣ) : K)) * z := by ring
          _ = z := by rw [hinv, one_mul]
      rwa [hwz] at hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hpt : ∀ z : K,
      Set.indicator ((fun z : K => ((c : Kˣ) : K) * z) '' (R : Set K))
          (fun y : K => α (x * y)) (((c : Kˣ) : K) * z)
        = Set.indicator (R : Set K) (fun z : K => α ((((c : Kˣ) : K) * x) * z)) z := by
    intro z
    by_cases hz : z ∈ (R : Set K)
    · rw [Set.indicator_of_mem ((hmemiff z).mpr hz), Set.indicator_of_mem hz]
      congr 1
      ring
    · rw [Set.indicator_of_notMem (fun hc => hz ((hmemiff z).mp hc)),
        Set.indicator_of_notMem hz]
  rw [hscale (fun y : K => Set.indicator ((fun z : K => ((c : Kˣ) : K) * z) '' (R : Set K))
    (fun y : K => α (x * y)) y)]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_indicator hR]
  rw [connes_selfDual_indicator hR hmass hαadd hαtriv hRmul hnontriv (((c : Kˣ) : K) * x)]

/-- **Appendix II (28).**  `1̂_{R^*} = 1_R − |π| 1_{π^{-1}R}`: the transform of the indicator of
the units is the difference of the transforms of the two fractional ideals `R` and `πR`. -/
theorem connes_unitIndicator_fourier {R : AddSubgroup K}
    (hR : MeasurableSet (R : Set K)) (hmass : μ.real (R : Set K) = 1)
    {α : K → ℂ} (hαadd : ∀ a b : K, α (a + b) = α a * α b)
    (hαtriv : ∀ y ∈ R, α y = 1)
    (hRmul : ∀ x ∈ R, ∀ y ∈ R, x * y ∈ R)
    (hnontriv : ∀ x : K, x ∉ R → ∃ y ∈ R, α (x * y) ≠ 1)
    (π : Kˣ) {m : ℂ}
    (hscale : ∀ g : K → ℂ, (∫ y : K, g y ∂μ) = m * ∫ z : K, g (((π : Kˣ) : K) * z) ∂μ)
    (x : K)
    (hint : Integrable (fun y : K => Set.indicator (R : Set K) (fun y : K => α (x * y)) y) μ)
    (hintP : Integrable (fun y : K =>
      Set.indicator ((fun z : K => ((π : Kˣ) : K) * z) '' (R : Set K))
        (fun y : K => α (x * y)) y) μ) :
    (∫ y : K, (Set.indicator (R : Set K) (fun y : K => α (x * y)) y
        - Set.indicator ((fun z : K => ((π : Kˣ) : K) * z) '' (R : Set K))
            (fun y : K => α (x * y)) y) ∂μ)
      = Set.indicator (R : Set K) (fun _ : K => (1 : ℂ)) x
        - m * Set.indicator (R : Set K) (fun _ : K => (1 : ℂ)) (((π : Kˣ) : K) * x) := by
  rw [MeasureTheory.integral_sub hint hintP, MeasureTheory.integral_indicator hR,
    connes_selfDual_indicator hR hmass hαadd hαtriv hRmul hnontriv x,
    connes_fractionalIdeal_fourier hR hmass hαadd hαtriv hRmul hnontriv π hscale x]

end

end GaloisForLFunctions.RHTower
