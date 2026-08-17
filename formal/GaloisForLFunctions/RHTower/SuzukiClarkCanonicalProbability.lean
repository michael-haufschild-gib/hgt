import GaloisForLFunctions.RHTower.SuzukiClarkScrewRigidity

/-!
# The canonical squared-ordinate probability of the Xi divisor

Under the reality of every centered squared coordinate, the reciprocal masses
`ω_q⁻¹` are summable with total `M₀(0)`, so the normalized family

`p_q = ω_q⁻¹ / M₀(0)`

is a probability distribution supported on the squared ordinates.  Its Stieltjes transform against
the kernel `u/(u+s)` collapses because the weight cancels the kernel numerator:

`∑_q p_q ω_q/(ω_q + s) = (1/M₀(0)) ∑_q 1/(ω_q + s) = M₀(s)/M₀(0)`,

which is exactly the value the interval law prescribes.  Both identities are unconditional
consequences of summability of the reciprocals.
-/

open Filter

noncomputable section

namespace RHTower

variable {ι : Type*}

/-- The reciprocal-mass normalizer `M₀(s)`. -/
def squaredOrdinateResolventSum (ω : ι → ℝ) (s : ℝ) : ℝ := ∑' q, (ω q + s)⁻¹

/-- The canonical probability weight of one squared ordinate. -/
def xiCanonicalWeight (ω : ι → ℝ) (q : ι) : ℝ :=
  (ω q)⁻¹ / squaredOrdinateResolventSum ω 0

theorem squaredOrdinateResolventSum_zero (ω : ι → ℝ) :
    squaredOrdinateResolventSum ω 0 = ∑' q, (ω q)⁻¹ := by
  rw [squaredOrdinateResolventSum]
  simp

/-- Shifting by a nonnegative amount keeps the reciprocal family summable. -/
theorem summable_shifted_inv {ω : ι → ℝ} (hω : ∀ q, 0 < ω q)
    (hsum : Summable fun q => (ω q)⁻¹) {s : ℝ} (hs : 0 ≤ s) :
    Summable fun q => (ω q + s)⁻¹ := by
  refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hsum
  · have h1 : 0 < ω q := hω q
    have : (0 : ℝ) < ω q + s := by linarith
    positivity
  · have h1 : 0 < ω q := hω q
    exact inv_anti₀ h1 (by linarith)

/-! ## `(117)`: the weights form a probability distribution -/

theorem xiCanonicalWeight_nonneg {ω : ι → ℝ} (hω : ∀ q, 0 < ω q)
    (_hpos : 0 < squaredOrdinateResolventSum ω 0) (q : ι) : 0 ≤ xiCanonicalWeight ω q := by
  rw [xiCanonicalWeight]
  have h1 : 0 < ω q := hω q
  positivity

/-- **`(117)`: the canonical weights sum to one.** -/
theorem hasSum_xiCanonicalWeight {ω : ι → ℝ}
    (hsum : Summable fun q => (ω q)⁻¹) (hpos : 0 < squaredOrdinateResolventSum ω 0) :
    HasSum (xiCanonicalWeight ω) 1 := by
  have hval : (∑' q, (ω q)⁻¹) = squaredOrdinateResolventSum ω 0 :=
    (squaredOrdinateResolventSum_zero ω).symm
  have h := (hsum.hasSum).div_const (squaredOrdinateResolventSum ω 0)
  rw [hval, div_self hpos.ne'] at h
  exact h

/-! ## `(118)`: the Stieltjes transform of the canonical probability -/

/-- **`(118)`: the canonical probability reproduces the resolvent ratio.** -/
theorem tsum_xiCanonicalWeight_stieltjes {ω : ι → ℝ} (hω : ∀ q, 0 < ω q)
    (hsum : Summable fun q => (ω q)⁻¹) (hpos : 0 < squaredOrdinateResolventSum ω 0)
    {s : ℝ} (hs : 0 ≤ s) :
    ∑' q, xiCanonicalWeight ω q * (ω q / (ω q + s))
      = squaredOrdinateResolventSum ω s / squaredOrdinateResolventSum ω 0 := by
  have hshift := summable_shifted_inv hω hsum hs
  have hterm : ∀ q, xiCanonicalWeight ω q * (ω q / (ω q + s))
      = (ω q + s)⁻¹ / squaredOrdinateResolventSum ω 0 := by
    intro q
    have h1 : 0 < ω q := hω q
    have h2 : (0 : ℝ) < ω q + s := by linarith
    rw [xiCanonicalWeight]
    field_simp
  rw [tsum_congr hterm, tsum_div_const]
  rfl

/-! ## The reciprocal-sum form -/

/-- The resolvent sum is decreasing in the shift. -/
theorem squaredOrdinateResolventSum_le {ω : ι → ℝ} (hω : ∀ q, 0 < ω q)
    (hsum : Summable fun q => (ω q)⁻¹) {s : ℝ} (hs : 0 ≤ s) :
    squaredOrdinateResolventSum ω s ≤ squaredOrdinateResolventSum ω 0 := by
  rw [squaredOrdinateResolventSum, squaredOrdinateResolventSum]
  refine Summable.tsum_mono (summable_shifted_inv hω hsum hs)
    (summable_shifted_inv hω hsum (le_refl 0)) fun q => ?_
  have h1 : 0 < ω q := hω q
  exact inv_anti₀ (by linarith) (by linarith)

end RHTower
