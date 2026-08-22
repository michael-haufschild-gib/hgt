import GaloisForLFunctions.HTGeometry.AbeDerivativeDampingNoGo

/-!
# Normalized polynomial damping tails

The finite graded-determinant construction has a largest damping degree `D`.
After multiplication by `B⁻ᴰ`, a complement term of degree `e ≤ D` is
`B⁻(D-e) exp (-a B)`.  Crucially, for `B ≥ 1` this has norm at most one,
independently of how small the positive phase `a` is.  Thus an existing
summable coefficient majorant survives the normalization, and Tannery applies
without a uniform spectral gap.

This is the analytic step needed by the distinct-speed/Vandermonde route.  It
does not posit a new Poincare-series interface: later work must derive the
summable coefficients and positive phases from Abe's actual period-matrix
formula.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A degree-`e` exponentially damped coefficient after normalization by degree `D`. -/
def normalizedDampingScalar (D e : ℕ) (a B : ℝ) : ℝ :=
  (B ^ (D - e))⁻¹ * Real.exp (-(a * B))

/-- A complex coefficient with the normalized damping scalar. -/
def normalizedDampingTerm {ι : Type*} (D : ℕ) (c : ι → ℂ)
    (e : ι → ℕ) (a : ι → ℝ) (B : ℝ) (i : ι) : ℂ :=
  normalizedDampingScalar D (e i) (a i) B • c i

/-- For positive parameters, the normalized scalar is nonnegative. -/
theorem normalizedDampingScalar_nonneg_of_one_le (D e : ℕ) (a : ℝ)
    {B : ℝ} (hB : 1 ≤ B) :
    0 ≤ normalizedDampingScalar D e a B := by
  exact mul_nonneg
    (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hB) _))
    (Real.exp_nonneg _)

/-- Eventual nonnegativity along the positive damping ray. -/
theorem normalizedDampingScalar_nonneg (D e : ℕ) (a : ℝ) :
    ∀ᶠ B : ℝ in atTop, 0 ≤ normalizedDampingScalar D e a B := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
  exact normalizedDampingScalar_nonneg_of_one_le D e a hB

/-- The polynomial normalization costs no more than the bare exponential on `B ≥ 1`. -/
theorem normalizedDampingScalar_le_exp (D e : ℕ) {a B : ℝ} (hB : 1 ≤ B) :
    normalizedDampingScalar D e a B ≤ Real.exp (-(a * B)) := by
  unfold normalizedDampingScalar
  have hpow : 1 ≤ B ^ (D - e) := one_le_pow₀ hB
  have hinv : (B ^ (D - e))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpow
  calc
    (B ^ (D - e))⁻¹ * Real.exp (-(a * B))
        ≤ 1 * Real.exp (-(a * B)) :=
      mul_le_mul_of_nonneg_right hinv (Real.exp_nonneg _)
    _ = Real.exp (-(a * B)) := one_mul _

/-- Every normalized scalar is bounded by one when its phase is strictly positive. -/
theorem normalizedDampingScalar_le_one (D e : ℕ) {a B : ℝ}
    (ha : 0 < a) (hB : 1 ≤ B) :
    normalizedDampingScalar D e a B ≤ 1 :=
  (normalizedDampingScalar_le_exp D e hB).trans
    (Real.exp_le_one_iff.mpr (by nlinarith))

/-- A normalized monomial-exponential coefficient decays for each fixed positive phase. -/
theorem tendsto_normalizedDampingScalar_zero (D e : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (normalizedDampingScalar D e a) atTop (nhds 0) := by
  have hscale : Tendsto (fun B : ℝ ↦ a * B) atTop atTop :=
    Filter.Tendsto.const_mul_atTop ha tendsto_id
  have hexp : Tendsto (fun B : ℝ ↦ Real.exp (-(a * B))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  refine squeeze_zero' (normalizedDampingScalar_nonneg D e a) ?_ hexp
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
  exact normalizedDampingScalar_le_exp D e hB

/-- A fixed complex coefficient times a normalized damping scalar decays. -/
theorem tendsto_normalizedDampingTerm_zero {ι : Type*} (D : ℕ) (c : ι → ℂ)
    (e : ι → ℕ) (a : ι → ℝ) (i : ι) (ha : 0 < a i) :
    Tendsto (fun B : ℝ ↦ normalizedDampingTerm D c e a B i) atTop (nhds 0) := by
  simpa [normalizedDampingTerm] using
    (tendsto_normalizedDampingScalar_zero D (e i) ha).smul_const (c i)

/-- The original coefficient norm is an eventual dominator for its normalized damped term. -/
theorem norm_normalizedDampingTerm_le {ι : Type*} (D : ℕ) (c : ι → ℂ)
    (e : ι → ℕ) (a : ι → ℝ) (i : ι) {B : ℝ}
    (ha : 0 < a i) (hB : 1 ≤ B) :
    ‖normalizedDampingTerm D c e a B i‖ ≤ ‖c i‖ := by
  rw [normalizedDampingTerm, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg]
  · exact (mul_le_mul_of_nonneg_right
      (normalizedDampingScalar_le_one D (e i) ha hB) (norm_nonneg _)).trans (by simp)
  · exact normalizedDampingScalar_nonneg_of_one_le D (e i) (a i) hB

/-- **Normalized Tannery theorem.** A summable family of coefficients remains summably
controlled after degree normalization, even when its strictly positive damping phases have no
uniform lower bound. -/
theorem tendsto_tsum_normalizedDampingTerm_zero {ι : Type*} (D : ℕ) (c : ι → ℂ)
    (e : ι → ℕ) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hsum : Summable (fun i ↦ ‖c i‖)) :
    Tendsto (fun B : ℝ ↦ tsum (fun i ↦ normalizedDampingTerm D c e a B i))
      atTop (nhds 0) := by
  apply tendsto_tsum_zero_of_pointwise_damping_of_summable_majorant hsum
  · intro i
    exact tendsto_normalizedDampingTerm_zero D c e a i (ha i)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB i
    exact norm_normalizedDampingTerm_le D c e a i (ha i) hB

/-- The normalized scalar is literally multiplication by `B⁻ᴰ` of its degree-`e`
polynomial-exponential term. -/
theorem normalizedDampingScalar_eq_parameter_normalization (D e : ℕ)
    {a B : ℝ} (he : e ≤ D) (hB : B ≠ 0) :
    normalizedDampingScalar D e a B =
      (B⁻¹) ^ D * (B ^ e * Real.exp (-(a * B))) := by
  unfold normalizedDampingScalar
  rw [← inv_pow]
  have hsplit : (B⁻¹) ^ D = (B⁻¹) ^ (D - e) * (B⁻¹) ^ e := by
    rw [← pow_add, Nat.sub_add_cancel he]
  rw [hsplit]
  have hcancel : (B⁻¹) ^ e * B ^ e = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hB, one_pow]
  calc
    (B⁻¹) ^ (D - e) * Real.exp (-(a * B)) =
        (B⁻¹) ^ (D - e) * (1 * Real.exp (-(a * B))) := by ring
    _ = (B⁻¹) ^ (D - e) *
        (((B⁻¹) ^ e * B ^ e) * Real.exp (-(a * B))) := by rw [hcancel]
    _ = (B⁻¹) ^ (D - e) * (B⁻¹) ^ e *
        (B ^ e * Real.exp (-(a * B))) := by ring

/-- Complex-coefficient form of the exact `B⁻ᴰ` normalization identity. -/
theorem normalizedDampingTerm_eq_parameter_normalization {ι : Type*}
    (D : ℕ) (c : ι → ℂ) (e : ι → ℕ) (a : ι → ℝ) (i : ι)
    {B : ℝ} (he : e i ≤ D) (hB : B ≠ 0) :
    normalizedDampingTerm D c e a B i =
      (B⁻¹) ^ D • ((B ^ e i * Real.exp (-(a i * B))) • c i) := by
  rw [normalizedDampingTerm,
    normalizedDampingScalar_eq_parameter_normalization D (e i) he hB,
    smul_smul]

end

end GaloisForLFunctions.HTGeometry
