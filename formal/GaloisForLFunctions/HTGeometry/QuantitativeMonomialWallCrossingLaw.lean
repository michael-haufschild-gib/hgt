import GaloisForLFunctions.HTGeometry.ConstraintRelativity.SincHorizonExponent
import GaloisForLFunctions.HTGeometry.FiniteWindowReplicaCollisionResolution

/-!
# Quantitative finite-coupling wall crossing for exact monomial detunings

The qualitative three-regime wall-crossing law has an effective version whenever the detuning is
the exact monomial `a * g ^ b`.  Below the birth horizon the sinc defect is quadratically small;
above it the response decays by an explicit inverse-power bound; at the birth horizon the profile
is exactly independent of `g`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Global quadratic upper bound for the sinc defect. -/
theorem abs_real_sinc_sub_one_le_sq_div_six (x : ℝ) :
    |Real.sinc x - 1| ≤ x ^ (2 : ℕ) / 6 := by
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.sinc_le_one x))]
  by_cases hx : x = 0
  · simp [hx]
  · have habs : 0 < |x| := abs_pos.mpr hx
    have heven : Real.sinc |x| = Real.sinc x := by
      by_cases hxnonneg : 0 ≤ x
      · simp [abs_of_nonneg hxnonneg]
      · have hxneg : x < 0 := lt_of_not_ge hxnonneg
        rw [abs_of_neg hxneg]
        exact Real.sinc_neg x
    calc
      1 - Real.sinc x = 1 - Real.sinc |x| := by rw [heven]
      _ ≤ |x| ^ (2 : ℕ) / 6 := by
        simpa [Real.sinc_of_ne_zero habs.ne'] using
          HTGeometry.ConstraintRelativity.one_sub_sinc_le habs
      _ = x ^ (2 : ℕ) / 6 := by rw [sq_abs]

/-- Exact symmetric-window reporter for a monomial detuning at inverse-power horizon `r`. -/
def monomialSincReporter
    (τ a g : ℝ) (b r : ℕ) : ℝ :=
  Real.sinc ((τ / g ^ r) * (g ^ b * a))

/-- Before birth, the finite-coupling error is explicitly quadratic in `g^(b-r)`. -/
theorem abs_monomialSincReporter_sub_one_le_precritical
    {τ a g : ℝ} (hτ : 0 < τ) (ha : 0 < a) (hg : 0 < g)
    {b r : ℕ} (hrb : r < b) :
    |monomialSincReporter τ a g b r - 1| ≤
      (τ * a) ^ (2 : ℕ) * g ^ (2 * (b - r)) / 6 := by
  have harg :
      (τ / g ^ r) * (g ^ b * a) =
        τ * a * g ^ (b - r) := by
    rw [pow_sub₀ g hg.ne' (Nat.le_of_lt hrb)]
    field_simp
  rw [monomialSincReporter, harg]
  calc
    |Real.sinc (τ * a * g ^ (b - r)) - 1|
        ≤ (τ * a * g ^ (b - r)) ^ (2 : ℕ) / 6 :=
          abs_real_sinc_sub_one_le_sq_div_six _
    _ = (τ * a) ^ (2 : ℕ) * g ^ (2 * (b - r)) / 6 := by ring

/-- At birth, the reporter is exactly the universal sinc profile at every nonzero coupling. -/
theorem monomialSincReporter_critical
    {τ a g : ℝ} (hg : g ≠ 0) (b : ℕ) :
    monomialSincReporter τ a g b b = Real.sinc (τ * a) := by
  unfold monomialSincReporter
  congr 1
  field_simp [pow_ne_zero _ hg]

/-- After birth, the finite-coupling response has an explicit power-law envelope. -/
theorem abs_monomialSincReporter_le_postcritical
    {τ a g : ℝ} (hτ : 0 < τ) (ha : 0 < a) (hg : 0 < g)
    {b r : ℕ} (hbr : b < r) :
    |monomialSincReporter τ a g b r| ≤
      g ^ (r - b) / (τ * a) := by
  have hgrb : g ^ (r - b) ≠ 0 := pow_ne_zero _ hg.ne'
  have harg :
      (τ / g ^ r) * (g ^ b * a) =
        (τ * a) / g ^ (r - b) := by
    rw [pow_sub₀ g hg.ne' (Nat.le_of_lt hbr)]
    field_simp
  rw [monomialSincReporter, harg]
  have hx : (τ * a) / g ^ (r - b) ≠ 0 :=
    div_ne_zero (mul_ne_zero hτ.ne' ha.ne') hgrb
  calc
    |Real.sinc ((τ * a) / g ^ (r - b))|
        ≤ |(τ * a) / g ^ (r - b)|⁻¹ :=
          abs_real_sinc_le_inv_abs hx
    _ = g ^ (r - b) / (τ * a) := by
      rw [abs_div, abs_of_pos (mul_pos hτ ha),
        abs_of_pos (pow_pos hg _)]
      field_simp

/-- **Quantitative monomial wall-crossing law.**  All three regimes, with finite-`g` bounds, in
one statement. -/
theorem quantitativeMonomialSincWallCrossing
    {τ a g : ℝ} (hτ : 0 < τ) (ha : 0 < a) (hg : 0 < g)
    (b : ℕ) :
    (∀ r < b,
      |monomialSincReporter τ a g b r - 1| ≤
        (τ * a) ^ (2 : ℕ) * g ^ (2 * (b - r)) / 6) ∧
    monomialSincReporter τ a g b b = Real.sinc (τ * a) ∧
    (∀ r, b < r →
      |monomialSincReporter τ a g b r| ≤
        g ^ (r - b) / (τ * a)) := by
  exact ⟨
    fun r hr =>
      abs_monomialSincReporter_sub_one_le_precritical hτ ha hg hr,
    monomialSincReporter_critical hg.ne' b,
    fun r hr =>
      abs_monomialSincReporter_le_postcritical hτ ha hg hr⟩

end

end GaloisForLFunctions.HTGeometry
