import GaloisForLFunctions.RHTower.LevinsonEntirePhaseAdvance
import GaloisForLFunctions.RHTower.EntireArgumentVariationRectangle
import GaloisForLFunctions.RHTower.PhaseAdvanceIncrementCount

/-!
# The Levinson window: from a rectangle zero count to odd critical fibres

Combining

* the polar form of Hardy's `Z` produced by the detector `G = ζ + λζ'`,
* the identification of its phase advance with `θ(T₂)-θ(T₁)` plus the argument variation of the
  entire detector `G♯ = (s-1)^(2 : ℕ) G` along the critical segment, and
* the rectangle argument principle, which turns that argument variation into the variation along
  the other three edges minus `2π` times the number of zeros of `G♯` in `[½,d]×[T₁,T₂]`,

gives the unconditional window inequality

```text
θ(T₂) - θ(T₁) + (three edge integrals) - 2π·#{zeros of G♯ in the box}  ≤  ψ(T₂) - ψ(T₁),
```

and hence, through the sign-chain interface, a lower bound for the number of critical ordinates of
odd multiplicity and for the singleton-fibre count.  The archimedean increment is the main term;
everything else is what an analytic argument has to control.
-/

open Complex Set MeasureTheory

noncomputable section

namespace RHTower

/-- **The Levinson window inequality.** -/
theorem exists_levinson_window_advance {lam : ℝ} (hlam0 : lam < 0)
    {d T₁ T₂ : ℝ} (hd : (1 / 2 : ℝ) < d) (h20 : 20 ≤ T₁) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc (1 / 2 : ℝ) d, levinsonGEntire (lam : ℂ) ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc (1 / 2 : ℝ) d, levinsonGEntire (lam : ℂ) ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, levinsonGEntire (lam : ℂ) ((d : ℂ) + t * I) ≠ 0)
    (hleft : ∀ τ ∈ Icc T₁ T₂, levinsonG (lam : ℂ) (linePt τ) ≠ 0) :
    ∃ (Z : Finset ℂ) (ρ ψ : ℝ → ℝ),
      (∀ z : ℂ, z ∈ Z ↔
        z ∈ (uIcc (1 / 2 : ℝ) d ×ℂ uIcc T₁ T₂) ∧ levinsonGEntire (lam : ℂ) z = 0) ∧
      ContinuousOn ψ (Icc T₁ T₂) ∧ (∀ τ ∈ Icc T₁ T₂, 0 < ρ τ) ∧
      (∀ τ ∈ Icc T₁ T₂, hardyZ τ = ρ τ * Real.cos (ψ τ)) ∧
      (gammaHardyTheta T₂ - gammaHardyTheta T₁)
          + (∫ t in T₁..T₂, (logDeriv (levinsonGEntire (lam : ℂ)) ((d : ℂ) + t * I)).re)
          + (∫ x in (1 / 2 : ℝ)..d,
              (logDeriv (levinsonGEntire (lam : ℂ)) ((x : ℂ) + T₁ * I)).im)
          - (∫ x in (1 / 2 : ℝ)..d,
              (logDeriv (levinsonGEntire (lam : ℂ)) ((x : ℂ) + T₂ * I)).im)
          - 2 * Real.pi *
            (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire (lam : ℂ)) w).toNat : ℝ))
        ≤ ψ T₂ - ψ T₁ := by
  have hlamC : ((lam : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_lt hlam0
  have hne : ∃ z : ℂ, levinsonGEntire (lam : ℂ) z ≠ 0 :=
    exists_levinsonGEntire_ne_zero hlamC
  have huIcc : uIcc T₁ T₂ = Icc T₁ T₂ := uIcc_of_le hT.le
  have hleftE : ∀ t ∈ uIcc T₁ T₂,
      levinsonGEntire (lam : ℂ) (((1 / 2 : ℝ) : ℂ) + t * I) ≠ 0 := by
    intro t ht
    rw [huIcc] at ht
    exact levinsonGEntire_line_ne_zero (hleft t ht)
  obtain ⟨Z, hZ, hid⟩ := exists_entire_argument_variation_rectangle
    (analyticOnNhd_levinsonGEntire (lam : ℂ)) hne hd hT hbot htop hright hleftE
  obtain ⟨ρ, ψ, hψc, hρ, hpolar, hadv⟩ :=
    exists_polar_hardyZ_advance_entire_le hlam0.le h20 hT.le hleft
  refine ⟨Z, ρ, ψ, hZ, hψc, hρ, hpolar, ?_⟩
  have hline : (fun τ : ℝ => (logDeriv (levinsonGEntire (lam : ℂ)) (linePt τ)).re)
      = fun t : ℝ => (logDeriv (levinsonGEntire (lam : ℂ))
          (((1 / 2 : ℝ) : ℂ) + t * I)).re := rfl
  rw [hline] at hadv
  linarith [hadv, hid.ge, hid.le]

/-- The window inequality in counting form: an increment of `(n+1)π` yields `n` odd fibres. -/
theorem le_xiOddFiberCount_of_levinson_window {lam : ℝ} (hlam0 : lam < 0)
    {d T₁ T₂ : ℝ} (hd : (1 / 2 : ℝ) < d) (h20 : 20 ≤ T₁) (hT : T₁ < T₂) {n : ℕ}
    (hbot : ∀ x ∈ uIcc (1 / 2 : ℝ) d, levinsonGEntire (lam : ℂ) ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc (1 / 2 : ℝ) d, levinsonGEntire (lam : ℂ) ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, levinsonGEntire (lam : ℂ) ((d : ℂ) + t * I) ≠ 0)
    (hleft : ∀ τ ∈ Icc T₁ T₂, levinsonG (lam : ℂ) (linePt τ) ≠ 0)
    (hbound : ∀ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔
        z ∈ (uIcc (1 / 2 : ℝ) d ×ℂ uIcc T₁ T₂) ∧ levinsonGEntire (lam : ℂ) z = 0) →
      ((n : ℝ) + 1) * Real.pi ≤
        (gammaHardyTheta T₂ - gammaHardyTheta T₁)
          + (∫ t in T₁..T₂, (logDeriv (levinsonGEntire (lam : ℂ)) ((d : ℂ) + t * I)).re)
          + (∫ x in (1 / 2 : ℝ)..d,
              (logDeriv (levinsonGEntire (lam : ℂ)) ((x : ℂ) + T₁ * I)).im)
          - (∫ x in (1 / 2 : ℝ)..d,
              (logDeriv (levinsonGEntire (lam : ℂ)) ((x : ℂ) + T₂ * I)).im)
          - 2 * Real.pi *
            (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire (lam : ℂ)) w).toNat : ℝ))) :
    n ≤ xiOddFiberCount T₂ := by
  obtain ⟨Z, ρ, ψ, hZ, hψc, hρ, hpolar, hadv⟩ :=
    exists_levinson_window_advance hlam0 hd h20 hT hbot htop hright hleft
  refine le_xiOddFiberCount_of_increment (by linarith) hT.le hψc hρ hpolar ?_
  exact le_trans (hbound Z hZ) hadv

end RHTower

end
