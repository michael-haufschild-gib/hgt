import GaloisForLFunctions.RHTower.ConstrainedProlateEvaluationIdentity

/-!
# Centre value of a compensated zero-integral tail

A tail `∑ t_m e_m` is corrected to zero integral by subtracting a multiple of the ground mode,
`r = ∑ t_m e_m − (L/ℓ₀) e₀` with `L = ∑ t_m ℓ_m`.  Its centre value is then not the naive
`∑ t_m e_m(0)` but

`r(0) = ∑ t_m e_m(0) (1 − χ_m/χ₀)`,

because each integral coordinate is its own eigenvalue times its own centre value.  The correction
factor rewrites as

`1 − χ_m/χ₀ = (d_m − d₀)/(χ₀(χ₀ + χ_m))`,   `d_j = 1 − χ_j²`,

so the compensation contributes a factor of the *leakage difference* rather than a reciprocal
leakage.  That is the point of the construction: no `1/d_m` appears.

Both statements are exact algebra over `ℂ`; the arithmetic input is only the evaluation identity
`ℓ_j = χ_j e_j(0)`, which is proved separately for genuine time-band eigenmodes.
-/

open Finset

namespace RHTower

/-- The compensation factor in terms of the leakages `d = 1 - χ²`. -/
theorem one_sub_div_eq_leakage_difference {χ₀ χ : ℂ} (h₀ : χ₀ ≠ 0) (hsum : χ₀ + χ ≠ 0) :
    1 - χ / χ₀ = ((1 - χ ^ 2) - (1 - χ₀ ^ 2)) / (χ₀ * (χ₀ + χ)) := by
  field_simp
  ring

/-- **Compensated centre value.**  Writing each integral coordinate as `ℓ = χ · e(0)`, the
zero-integral correction turns the centre value into a sum weighted by `1 - χ_m/χ₀`. -/
theorem compensated_centre_value {ι : Type*} (s : Finset ι)
    (t χ e : ι → ℂ) {χ₀ e₀ : ℂ} (hχ₀ : χ₀ ≠ 0) (he₀ : e₀ ≠ 0) :
    (∑ m ∈ s, t m * e m)
        - ((∑ m ∈ s, t m * (χ m * e m)) / (χ₀ * e₀)) * e₀
      = ∑ m ∈ s, t m * e m * (1 - χ m / χ₀) := by
  have hsplit : ∑ m ∈ s, t m * e m * (1 - χ m / χ₀)
      = (∑ m ∈ s, t m * e m) - (∑ m ∈ s, t m * (χ m * e m)) / χ₀ := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    field_simp
  rw [hsplit]
  congr 1
  field_simp

/-- The compensation is exactly what makes the corrected tail have zero integral. -/
theorem compensated_integral_eq_zero {ι : Type*} (s : Finset ι)
    (t ℓ : ι → ℂ) {ℓ₀ : ℂ} (hℓ₀ : ℓ₀ ≠ 0) :
    (∑ m ∈ s, t m * ℓ m) - ((∑ m ∈ s, t m * ℓ m) / ℓ₀) * ℓ₀ = 0 := by
  field_simp
  ring

/-- **Specialization to genuine time-band eigenmodes.**  The hypotheses are only that the ground
eigenvalue and ground centre value are nonzero; the identity `ℓ = χ · e(0)` is supplied by
`timeBandEigenSourceIntegral_eq_mul_pointwiseSource_zero`. -/
theorem compensated_centre_value_timeBand {ι : Type*} (s : Finset ι) (t : ι → ℂ)
    {a : ℝ} (ha : 0 < a)
    (f : ι → evenSubspace) (χ : ι → ℂ) (hχ : ∀ i, χ i ≠ 0)
    (heig : ∀ i, evenTimeBandFourier a (f i) = χ i • f i)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (he₀ : timeBandEigenPointwiseSource a f₀ χ₀ hχ₀ heig₀ 0 ≠ 0) :
    (∑ m ∈ s, t m * timeBandEigenPointwiseSource a (f m) (χ m) (hχ m) (heig m) 0)
        - ((∑ m ∈ s, t m * timeBandEigenSourceIntegral a (f m) (χ m) (hχ m) (heig m))
            / timeBandEigenSourceIntegral a f₀ χ₀ hχ₀ heig₀)
          * timeBandEigenPointwiseSource a f₀ χ₀ hχ₀ heig₀ 0
      = ∑ m ∈ s, t m * timeBandEigenPointwiseSource a (f m) (χ m) (hχ m) (heig m) 0
          * (1 - χ m / χ₀) := by
  have hL : ∀ i : ι, timeBandEigenSourceIntegral a (f i) (χ i) (hχ i) (heig i)
      = χ i * timeBandEigenPointwiseSource a (f i) (χ i) (hχ i) (heig i) 0 := fun i =>
    timeBandEigenSourceIntegral_eq_mul_pointwiseSource_zero a ha (f i) (χ i) (hχ i) (heig i)
  have hL₀ : timeBandEigenSourceIntegral a f₀ χ₀ hχ₀ heig₀
      = χ₀ * timeBandEigenPointwiseSource a f₀ χ₀ hχ₀ heig₀ 0 :=
    timeBandEigenSourceIntegral_eq_mul_pointwiseSource_zero a ha f₀ χ₀ hχ₀ heig₀
  have hsum : ∑ m ∈ s, t m * timeBandEigenSourceIntegral a (f m) (χ m) (hχ m) (heig m)
      = ∑ m ∈ s, t m * (χ m *
          timeBandEigenPointwiseSource a (f m) (χ m) (hχ m) (heig m) 0) := by
    apply Finset.sum_congr rfl
    intro m _
    rw [hL m]
  rw [hsum, hL₀]
  exact compensated_centre_value s t χ
    (fun m => timeBandEigenPointwiseSource a (f m) (χ m) (hχ m) (heig m) 0) hχ₀ he₀

end RHTower
