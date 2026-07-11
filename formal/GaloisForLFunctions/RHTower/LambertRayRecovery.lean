import GaloisForLFunctions.RHTower.PrimeLambertMobiusInversion

/-!
# Recovery from a vanishing Lambert transform on a ray

This file packages the analytic use of the exact Lambert--Möbius inversion.
Once sectorial prime-log uniqueness makes the Lambert transform vanish on a
positive ray, geometric Fourier--Borel decay recovers the original transform
there without a conditional rearrangement.
-/

noncomputable section

namespace RHTower

open Complex

/-- Derivative Lambert transform `Σ_(m≥1) m F(mz)`. -/
def positiveLambertDerivative (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' m : ℕ+, (m : ℂ) * F ((m : ℂ) * z)

/-- Restricting `F` to a multiplicative ray converts its weighted arithmetic
Lambert transform into `positiveLambertDerivative`. -/
theorem weightedLambertTransform_ray_eq
    (F : ℂ → ℂ) (x : ℂ) (n : ℕ+) :
    weightedLambertTransform (fun k : ℕ+ ↦ F ((k : ℂ) * x)) n =
      positiveLambertDerivative F ((n : ℂ) * x) := by
  unfold weightedLambertTransform positiveLambertDerivative
  apply tsum_congr
  intro m
  congr 2
  push_cast
  ring

/-- Geometric decay plus vanishing of the Lambert transform on a
multiplicative ray recovers the first Fourier--Borel value exactly. -/
theorem fourierBorel_eq_zero_of_lambert_ray_zero
    (F : ℂ → ℂ) (x : ℂ) (C r : ℝ)
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ n : ℕ+, ‖F ((n : ℂ) * x)‖ ≤ C * r ^ (n : ℕ))
    (hzero : ∀ n : ℕ+, positiveLambertDerivative F ((n : ℂ) * x) = 0) :
    F x = 0 := by
  let a : ℕ+ → ℂ := fun n ↦ F ((n : ℂ) * x)
  have hsum : Summable (weightedLambertMobiusPair a) :=
    weightedLambertMobiusPair_summable_of_geometric a C r hC hr0 hr1 hdecay
  have htransform : ∀ n : ℕ+, weightedLambertTransform a n = 0 := by
    intro n
    rw [weightedLambertTransform_ray_eq]
    exact hzero n
  have ha := weightedLambertMobius_first_eq_zero a hsum htransform
  simpa [a] using ha

/-- An entire function which vanishes on a positive real tail vanishes
identically.  The proof feeds the explicit accumulating sequence
`X + 1 + 1/(n+1)` into the analytic identity theorem. -/
theorem entire_eq_zero_of_zero_on_real_tail
    (F : ℂ → ℂ) (X : ℝ)
    (hF : AnalyticOnNhd ℂ F Set.univ)
    (hzero : ∀ x : ℝ, X ≤ x → F x = 0) :
    ∀ z : ℂ, F z = 0 := by
  let z₀ : ℂ := ((X + 1 : ℝ) : ℂ)
  let u : ℕ → ℂ := fun n => ((X + 1 + ((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)
  have hu_tend : Filter.Tendsto u Filter.atTop (nhds z₀) := by
    have hinv : Filter.Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹))
        Filter.atTop (nhds 0) :=
      tendsto_natCast_atTop_atTop.inv_tendsto_atTop.comp (Filter.tendsto_add_atTop_nat 1)
    have hadd : Filter.Tendsto
        (fun n : ℕ => X + 1 + (((n + 1 : ℕ) : ℝ)⁻¹))
        Filter.atTop (nhds (X + 1 + 0)) :=
      tendsto_const_nhds.add hinv
    have hcast := (Complex.continuous_ofReal.tendsto (X + 1 + 0)).comp hadd
    simpa [u, z₀, Function.comp_def] using hcast
  have hu_ne : ∀ n : ℕ, u n ≠ z₀ := by
    intro n h
    have hre : X + 1 + (((n + 1 : ℕ) : ℝ)⁻¹) = X + 1 := by
      apply Complex.ofReal_injective
      simpa [u, z₀] using h
    have hinv : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by positivity
    linarith
  have hu_zero : ∀ n : ℕ, F (u n) = 0 := by
    intro n
    rw [show u n = ((X + 1 + (((n + 1 : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) by rfl]
    apply hzero
    have hinv : 0 ≤ (((n + 1 : ℕ) : ℝ)⁻¹) := by positivity
    linarith
  have hu_within : Filter.Tendsto u Filter.atTop (nhdsWithin z₀ ({z₀} : Set ℂ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hu_tend, Filter.Eventually.of_forall (fun n => by simpa using hu_ne n)⟩
  have hfreq : ∃ᶠ z in nhdsWithin z₀ ({z₀} : Set ℂ)ᶜ, F z = 0 :=
    hu_within.frequently (Filter.Eventually.of_forall hu_zero).frequently
  exact fun z =>
    hF.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (Set.mem_univ z₀) hfreq (Set.mem_univ z)

end RHTower
