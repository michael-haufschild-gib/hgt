import GaloisForLFunctions.RHTower.CombinedShadowBlindness
import GaloisForLFunctions.RHTower.FiniteDivisorPrefixNonselection

/-!
# Finite divisor/head/tail shadow universality

An arbitrary finite critical-line divisor prefix, finite exact Euler head, and asymptotic
logarithmic-derivative tail remain simultaneously blind to adjoining a generic free reflection
orbit. The extension preserves every prescribed multiplicity and a fresh fixed orbit, while
acquiring simple off-line charge.
-/

open Complex

namespace RHTower

noncomputable section

/-- Add a free reflection orbit to the fixed extension of a finite divisor prefix. -/
def finiteDivisorHeadTailFreeOrbitExtension
    (P : Finset ℕ) (S : Finset ℝ) (m : ℝ → ℕ) (η : ℝ) (ρ : ℂ) : ℂ → ℂ :=
  fun z => orbitQuartic ρ z * fixedOrbitExtension P S m η z

/-- The fixed-orbit extension of every finite divisor prefix is eventually nonvanishing. -/
theorem eventuallyNonvanishing_fixedOrbitExtension
    (P : Finset ℕ) (hP : ∀ p ∈ P, 1 < p)
    (S : Finset ℝ) (m : ℝ → ℕ) (η : ℝ) :
    EventuallyNonvanishing (fixedOrbitExtension P S m η) := by
  obtain ⟨X, hX⟩ := eventuallyNonvanishing_feBundle P hP
  refine ⟨max X 1, fun z hz => ?_⟩
  have hzX : X ≤ z.re := le_trans (le_max_left X 1) hz
  have hzre : z.re ≠ 1 / 2 := by
    have : 1 ≤ z.re := le_trans (le_max_right X 1) hz
    linarith
  exact mul_ne_zero (hX z hzX)
    (mul_ne_zero (lineDivisorPrefix_ne_zero_at_offline S m hzre)
      (linePair_ne_zero_at_offline η hzre))

/-- **Finite divisor/head/tail shadow universality law.** A generic free orbit can be adjoined to
any finite divisor prefix with finite Euler head while preserving the complete prescribed prefix,
the fresh fixed orbit, eventual nonvanishing, and the original logarithmic-derivative tail. The new
free orbit has simple order and nontrivial level-one charge. -/
theorem finiteDivisorHeadTail_freeOrbitShadowUniversality
    (P : Finset ℕ) (hP : ∀ p ∈ P, 1 < p)
    (S : Finset ℝ) (m : ℝ → ℕ) (hS : ∀ τ ∈ S, 0 < τ)
    {η : ℝ} (hη : 0 < η) (hηS : η ∉ S)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hρre : ρ.re ≠ 1 / 2) (hρim : ρ.im ≠ 0) :
    ShadowClass P (fixedOrbitExtension P S m η)
        (finiteDivisorHeadTailFreeOrbitExtension P S m η ρ) ∧
      (∀ τ ∈ S,
        analyticOrderAt (finiteDivisorHeadTailFreeOrbitExtension P S m η ρ)
          (criticalLinePoint τ) = m τ) ∧
      analyticOrderAt (finiteDivisorHeadTailFreeOrbitExtension P S m η ρ)
        (criticalLinePoint η) = 1 ∧
      analyticOrderAt (finiteDivisorHeadTailFreeOrbitExtension P S m η ρ) ρ = 1 ∧
      carrierCharge (finiteDivisorHeadTailFreeOrbitExtension P S m η ρ) 1 ρ ≠ 1 := by
  let f₀ := fixedOrbitExtension P S m η
  let g := finiteDivisorHeadTailFreeOrbitExtension P S m η ρ
  have hnonselect :=
    finiteDivisorPrefix_orbitNonselection P hP S m hS hη hηS hρ0 hρ1 hρre hρim
  have hf₀class : FiniteEulerClass P f₀ := by
    simpa only [f₀] using hnonselect.1
  have hf₀fes : FESchwarz f₀ := by
    dsimp only [f₀, fixedOrbitExtension]
    exact (feBundle_fESchwarz P).mul
      ((lineDivisorPrefix_fESchwarz S m).mul (fESchwarz_linePair η))
  have hf₀diff : Differentiable ℂ f₀ := hf₀fes.1
  have hf₀nv : EventuallyNonvanishing f₀ := by
    simpa only [f₀] using eventuallyNonvanishing_fixedOrbitExtension P hP S m η
  have hgshadow : ShadowClass P f₀ g := by
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨G, hG, hGspec⟩ := hf₀class
      refine ⟨fun z => orbitQuartic ρ z * G z,
        (fESchwarz_orbitQuartic ρ).mul hG, fun z => ?_⟩
      dsimp only [g, finiteDivisorHeadTailFreeOrbitExtension]
      change orbitQuartic ρ z * f₀ z = feBundle P z * (orbitQuartic ρ z * G z)
      rw [hGspec z]
      ring
    · simpa only [g, finiteDivisorHeadTailFreeOrbitExtension] using
        eventuallyNonvanishing_orbitQuartic_mul (ρ₀ := ρ) hf₀nv
    · simpa only [g, finiteDivisorHeadTailFreeOrbitExtension] using
        dlogTail_orbitQuartic_mul hf₀diff hf₀nv (dlogTail_self f₀)
  have hf₀rho : f₀ ρ ≠ 0 := by
    dsimp only [f₀, fixedOrbitExtension]
    exact mul_ne_zero (feBundle_ne_zero_on_strip P hP hρ0 hρ1)
      (mul_ne_zero (lineDivisorPrefix_ne_zero_at_offline S m hρre)
        (linePair_ne_zero_at_offline η hρre))
  have hgold : ∀ τ ∈ S,
      analyticOrderAt g (criticalLinePoint τ) = m τ := by
    intro τ hτ
    dsimp only [g, finiteDivisorHeadTailFreeOrbitExtension]
    change analyticOrderAt (orbitQuartic ρ * f₀)
      (criticalLinePoint τ) = m τ
    rw [analyticOrderAt_mul
      ((fESchwarz_orbitQuartic ρ).1.analyticAt (criticalLinePoint τ))
      (hf₀diff.analyticAt (criticalLinePoint τ)),
      analyticOrderAt_eq_zero.mpr
        (Or.inr (orbitQuartic_ne_zero_at_criticalLinePoint hρre τ)),
      zero_add]
    simpa only [f₀] using (hnonselect.2.2.1 τ hτ).1
  have hgeta : analyticOrderAt g (criticalLinePoint η) = 1 := by
    dsimp only [g, finiteDivisorHeadTailFreeOrbitExtension]
    change analyticOrderAt (orbitQuartic ρ * f₀)
      (criticalLinePoint η) = 1
    rw [analyticOrderAt_mul
      ((fESchwarz_orbitQuartic ρ).1.analyticAt (criticalLinePoint η))
      (hf₀diff.analyticAt (criticalLinePoint η)),
      analyticOrderAt_eq_zero.mpr
        (Or.inr (orbitQuartic_ne_zero_at_criticalLinePoint hρre η)),
      zero_add]
    simpa only [f₀] using hnonselect.2.2.2.1
  have hgrho : analyticOrderAt g ρ = 1 := by
    dsimp only [g, finiteDivisorHeadTailFreeOrbitExtension]
    change analyticOrderAt (fun z => orbitQuartic ρ z * f₀ z) ρ = 1
    rw [analyticOrderAt_orbitQuartic_mul hρre hρim (hf₀diff.analyticAt ρ),
      analyticOrderAt_eq_zero.mpr (Or.inr hf₀rho), add_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [f₀, g] using hgshadow
  · simpa only [g] using hgold
  · simpa only [g] using hgeta
  · simpa only [g] using hgrho
  · rw [carrierCharge_one_eq_neg_one_pow, hgrho, ENat.toNat_one]
    norm_num

end

end RHTower
