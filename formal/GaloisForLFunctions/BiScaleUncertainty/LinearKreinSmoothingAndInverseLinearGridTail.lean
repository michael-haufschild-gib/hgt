import GaloisForLFunctions.BiScaleUncertainty.InfiniteGridUniformTail

/-!
# Linear Krein smoothing and the inverse-linear integer-logarithmic interpolation law

Krein's increment inequality `(h(x) - h(y))² ≤ 2h(0)(h(0) - h(x - y))` controls a correlation
increment only by the *square root* of an origin increment. Averaging over a lag progression
removes the square root. For `S h(x) = m⁻² ∑_{i,j<m} h(x + (i - j)λ)`,

`|h(x) - S h(x)| ≤ h(0) - S h(0)`,

because `h - S h` is again a positive-definite profile: the two-point combinations
`f(· + x) ± f` have nonnegative origin increments, and summing these over the progression
gives the two signs. Moving `x` by one lag step `λ` telescopes the double sum, so `S h` moves
by at most `2h(0)/m` per step.

Take `λ` equal to the gap between `T` and the next integer-logarithmic node `log ⌈e^T⌉`
(at most `e^{-T}`) and `m = ⌈T⌉`. The origin defect `h(0) - S h(0)` is an average of origin
increments at scale `≤ (T + 1)e^{-T}`, which the singular Lévy energy pays at logarithmic
cost `≍ T`. The result is the inverse-linear interpolation law

`T |h(T) - h(log ⌈e^T⌉)| ≤ 32 √e 𝒥(f) + 2 h(0)`   for all `T > 0`,

for every compact `C²` source, against the inverse-square-root rate of Krein's inequality.
The same argument at any displacement `d` gives the linear logarithmic modulus of
continuity `log(1/d) |h(x) - h(x + d)| ≤ 32√e 𝒥(f) + 2h(0)`.
On the integer-logarithmic blind cone it is a `1/|T|` tail law, uniform in the source's
support, and it gives uniformly square-integrable tails `∫_{T}^∞ h² ≤ (32√e 𝒥 + 2h(0))²/T`.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

variable {f : ℝ → ℝ}

/-! ### 1. Two-point combinations -/

/-- Correlation of the two-point combination `f(· + x) + c f`. -/
theorem autocorr_shift_add_smul (hfc : HasCompactSupport f) (hf : Continuous f)
    (x c z : ℝ) :
    autocorr (fun u => f (u + x) + c * f u) z =
      (1 + c ^ 2) * autocorr f z + c * (autocorr f (z - x) + autocorr f (z + x)) := by
  have hsx : HasCompactSupport (fun u => f (u + x)) :=
    hfc.comp_homeomorph (Homeomorph.addRight x)
  have hcx : Continuous (fun u => f (u + x)) := hf.comp (continuous_add_const x)
  have hc1 : Continuous (fun u => f (u + (z + x))) := hf.comp (continuous_add_const _)
  have hc2 : Continuous (fun u => f (u + z)) := hf.comp (continuous_add_const _)
  have i1 : Integrable (fun u => f (u + x) * f (u + (z + x))) :=
    (hcx.mul hc1).integrable_of_hasCompactSupport hsx.mul_right
  have i2 : Integrable (fun u => c * (f (u + x) * f (u + z))) :=
    ((hcx.mul hc2).integrable_of_hasCompactSupport hsx.mul_right).const_mul c
  have i3 : Integrable (fun u => c * (f u * f (u + (z + x)))) :=
    ((hf.mul hc1).integrable_of_hasCompactSupport hfc.mul_right).const_mul c
  have i4 : Integrable (fun u => c ^ 2 * (f u * f (u + z))) :=
    ((hf.mul hc2).integrable_of_hasCompactSupport hfc.mul_right).const_mul _
  have e1 : (∫ u, f (u + x) * f (u + (z + x))) = autocorr f z := by
    unfold autocorr
    rw [← integral_add_right_eq_self (μ := volume) (fun u => f u * f (u + z)) x]
    congr 1; funext u; ring_nf
  have e2 : (∫ u, f (u + x) * f (u + z)) = autocorr f (z - x) := by
    unfold autocorr
    rw [← integral_add_right_eq_self (μ := volume) (fun u => f u * f (u + (z - x))) x]
    congr 1; funext u; ring_nf
  unfold autocorr
  have hexp : (fun u => (f (u + x) + c * f u) * (f (u + z + x) + c * f (u + z))) =
      fun u => ((f (u + x) * f (u + (z + x)) + c * (f (u + x) * f (u + z))) +
        c * (f u * f (u + (z + x)))) + c ^ 2 * (f u * f (u + z)) := by
    funext u; ring_nf
  simp only [hexp]
  have i12 : Integrable (fun u => f (u + x) * f (u + (z + x)) + c * (f (u + x) * f (u + z))) :=
    i1.add i2
  have i123 : Integrable (fun u => f (u + x) * f (u + (z + x)) + c * (f (u + x) * f (u + z)) +
      c * (f u * f (u + (z + x)))) := i12.add i3
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul]
  have e1' := e1
  have e2' := e2
  unfold autocorr at e1' e2'
  rw [e1', e2']
  ring

/-- The two-point origin-increment inequality. For every `c`, `x`, `z`,
`0 ≤ (1 + c²)(h(0) - h(z)) + c(2h(x) - h(z - x) - h(z + x))`. -/
theorem autocorr_two_point_increment_nonneg (hfc : HasCompactSupport f) (hf : Continuous f)
    (x c z : ℝ) :
    0 ≤ (1 + c ^ 2) * (autocorr f 0 - autocorr f z) +
      c * (2 * autocorr f x - autocorr f (z - x) - autocorr f (z + x)) := by
  set G : ℝ → ℝ := fun u => f (u + x) + c * f u with hG
  have hGc : Continuous G := (hf.comp (continuous_add_const x)).add (continuous_const.mul hf)
  have hGs : HasCompactSupport G :=
    (hfc.comp_homeomorph (Homeomorph.addRight x)).add (hfc.mul_left)
  have h := autocorr_sub_nonneg hGs hGc z
  rw [hG, autocorr_shift_add_smul hfc hf, autocorr_shift_add_smul hfc hf] at h
  have hn : autocorr f (0 - x) = autocorr f x := by rw [zero_sub, autocorr_neg]
  rw [hn, zero_add] at h
  linarith

/-! ### 2. Progression smoothing -/

/-- The correlation averaged over all lag differences of the progression `0, λ, …, (m-1)λ`. -/
def progressionSmoothedCorrelation (f : ℝ → ℝ) (lag : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ((m : ℝ) ^ 2)⁻¹ * ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
    autocorr f (x + ((i : ℝ) - j) * lag)

/-- The progression double sum is even in the base point. -/
theorem progression_sum_neg (lag : ℝ) (m : ℕ) (x : ℝ) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, autocorr f (-x + ((i : ℝ) - j) * lag)) =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, autocorr f (x + ((i : ℝ) - j) * lag) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← autocorr_neg]
  ring_nf

/-- **Linear Krein smoothing.** The progression-smoothed correlation is uniformly within the
origin defect `h(0) - S h(0)` of the correlation itself; no square root appears. -/
theorem abs_autocorr_sub_progressionSmoothed_le (hfc : HasCompactSupport f)
    (hf : Continuous f) (lag : ℝ) {m : ℕ} (hm : 0 < m) (x : ℝ) :
    |autocorr f x - progressionSmoothedCorrelation f lag m x| ≤
      autocorr f 0 - progressionSmoothedCorrelation f lag m 0 := by
  set P : ℝ → ℝ := fun y => ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
    autocorr f (y + ((i : ℝ) - j) * lag) with hP
  have hsum : ∀ c : ℝ, 0 ≤ (1 + c ^ 2) * ((m : ℝ) ^ 2 * autocorr f 0 - P 0) +
      c * (2 * (m : ℝ) ^ 2 * autocorr f x - P (-x) - P x) := by
    intro c
    have hnn := Finset.sum_nonneg fun (i : ℕ) (_ : i ∈ Finset.range m) =>
      Finset.sum_nonneg fun (j : ℕ) (_ : j ∈ Finset.range m) =>
        autocorr_two_point_increment_nonneg hfc hf x c (((i : ℝ) - j) * lag)
    have hrw : (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        ((1 + c ^ 2) * (autocorr f 0 - autocorr f (((i : ℝ) - j) * lag)) +
          c * (2 * autocorr f x - autocorr f (((i : ℝ) - j) * lag - x) -
            autocorr f (((i : ℝ) - j) * lag + x)))) =
        (1 + c ^ 2) * ((m : ℝ) ^ 2 * autocorr f 0 - P 0) +
          c * (2 * (m : ℝ) ^ 2 * autocorr f x - P (-x) - P x) := by
      simp only [hP, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have a1 : ∀ i j : ℕ, autocorr f (((i : ℝ) - j) * lag) =
          autocorr f (0 + ((i : ℝ) - j) * lag) := fun i j => by rw [zero_add]
      have a2 : ∀ i j : ℕ, autocorr f (((i : ℝ) - j) * lag - x) =
          autocorr f (-x + ((i : ℝ) - j) * lag) := fun i j => by ring_nf
      have a3 : ∀ i j : ℕ, autocorr f (((i : ℝ) - j) * lag + x) =
          autocorr f (x + ((i : ℝ) - j) * lag) := fun i j => by ring_nf
      simp only [a1, a2, a3]
      ring
    rw [hrw] at hnn
    exact hnn
  have hneg : P (-x) = P x := progression_sum_neg lag m x
  have hplus := hsum 1
  have hminus := hsum (-1)
  rw [hneg] at hplus hminus
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hS : ∀ y, progressionSmoothedCorrelation f lag m y = P y / (m : ℝ) ^ 2 := by
    intro y
    simp only [progressionSmoothedCorrelation, hP]
    rw [div_eq_inv_mul]
  rw [hS, hS, abs_le]
  constructor
  · rw [← sub_nonneg]
    have : autocorr f x - P x / (m : ℝ) ^ 2 - -(autocorr f 0 - P 0 / (m : ℝ) ^ 2) =
        ((m : ℝ) ^ 2 * autocorr f 0 - P 0 + ((m : ℝ) ^ 2 * autocorr f x - P x)) /
          (m : ℝ) ^ 2 := by
      field_simp
      ring
    rw [this]
    apply div_nonneg _ hm2.le
    nlinarith
  · rw [← sub_nonneg]
    have : autocorr f 0 - P 0 / (m : ℝ) ^ 2 - (autocorr f x - P x / (m : ℝ) ^ 2) =
        ((m : ℝ) ^ 2 * autocorr f 0 - P 0 - ((m : ℝ) ^ 2 * autocorr f x - P x)) /
          (m : ℝ) ^ 2 := by
      field_simp
    rw [this]
    apply div_nonneg _ hm2.le
    nlinarith

/-- **One lag step.** The smoothed correlation moves by at most `2h(0)/m` when its base
point moves by one lag; the double sum telescopes to `m` boundary terms. -/
theorem abs_progressionSmoothed_add_lag_sub_le (hfc : HasCompactSupport f)
    (hf : Continuous f) (lag : ℝ) {m : ℕ} (hm : 0 < m) (x : ℝ) :
    |progressionSmoothedCorrelation f lag m (x + lag) -
        progressionSmoothedCorrelation f lag m x| ≤ 2 * autocorr f 0 / m := by
  have htel : (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        autocorr f (x + lag + ((i : ℝ) - j) * lag)) -
      (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, autocorr f (x + ((i : ℝ) - j) * lag)) =
      ∑ j ∈ Finset.range m, (autocorr f (x + ((m : ℝ) - j) * lag) -
        autocorr f (x + ((0 : ℝ) - j) * lag)) := by
    rw [Finset.sum_comm (f := fun i j : ℕ => autocorr f (x + lag + ((i : ℝ) - j) * lag)),
      Finset.sum_comm (f := fun i j : ℕ => autocorr f (x + ((i : ℝ) - j) * lag)),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    have hstep : ∀ i : ℕ, autocorr f (x + lag + ((i : ℝ) - j) * lag) =
        autocorr f (x + (((i + 1 : ℕ) : ℝ) - j) * lag) := fun i => by
      push_cast; ring_nf
    simp only [hstep]
    rw [Finset.sum_range_sub (fun i : ℕ => autocorr f (x + ((i : ℝ) - j) * lag)) m]
    simp only [Nat.cast_zero]
  have hbound : |∑ j ∈ Finset.range m, (autocorr f (x + ((m : ℝ) - j) * lag) -
        autocorr f (x + ((0 : ℝ) - j) * lag))| ≤ m * (2 * autocorr f 0) := by
    calc
      _ ≤ ∑ j ∈ Finset.range m, |autocorr f (x + ((m : ℝ) - j) * lag) -
          autocorr f (x + ((0 : ℝ) - j) * lag)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range m, 2 * autocorr f 0 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 := abs_autocorr_le_zero hfc hf (x + ((m : ℝ) - j) * lag)
        have h2 := abs_autocorr_le_zero hfc hf (x + ((0 : ℝ) - j) * lag)
        calc
          _ ≤ |autocorr f (x + ((m : ℝ) - j) * lag)| +
              |autocorr f (x + ((0 : ℝ) - j) * lag)| := abs_sub _ _
          _ ≤ _ := by linarith
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  unfold progressionSmoothedCorrelation
  rw [← mul_sub, htel, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hmpos 2))]
  calc
    _ ≤ ((m : ℝ) ^ 2)⁻¹ * (m * (2 * autocorr f 0)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (by positivity))
    _ = _ := by field_simp

/-- The origin defect of the smoothing is an average of origin increments at the
progression lags, hence bounded by any common bound for them. -/
theorem autocorr_zero_sub_progressionSmoothed_le (lag : ℝ) {m : ℕ} (hm : 0 < m) {B : ℝ}
    (hB : ∀ i < m, ∀ j < m, autocorr f 0 - autocorr f (((i : ℝ) - j) * lag) ≤ B) :
    autocorr f 0 - progressionSmoothedCorrelation f lag m 0 ≤ B := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      (autocorr f 0 - autocorr f (0 + ((i : ℝ) - j) * lag))) ≤
        ∑ _i ∈ Finset.range m, ∑ _j ∈ Finset.range m, B :=
    Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => by
      rw [zero_add]
      exact hB i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  unfold progressionSmoothedCorrelation
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  set Q : ℝ := ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
    autocorr f (0 + ((i : ℝ) - j) * lag) with hQ
  rw [← sub_nonneg]
  have : B - (autocorr f 0 - ((m : ℝ) ^ 2)⁻¹ * Q) =
      ((m : ℝ) * ((m : ℝ) * B) - ((m : ℝ) * ((m : ℝ) * autocorr f 0) - Q)) / (m : ℝ) ^ 2 := by
    field_simp
  rw [this]
  exact div_nonneg (by linarith) hm2.le

/-! ### 3. Lévy energy at short progression lags -/

/-- At every lag of a progression of total length `mλ < 1`, the origin increment is paid
by the Lévy energy at logarithmic cost `-log(mλ)`. -/
theorem autocorr_progression_increment_le (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {lag : ℝ} (hlag : 0 < lag) {m : ℕ} (hml : (m : ℝ) * lag < 1) {i j : ℕ} (hi : i < m)
    (hj : j < m) :
    autocorr f 0 - autocorr f (((i : ℝ) - j) * lag) ≤
      4 * Real.exp (1 / 2) * biScaleLevyEnergy f / (-Real.log ((m : ℝ) * lag)) := by
  have hmpos : (0 : ℝ) < m := by
    have : 0 < m := lt_of_le_of_lt (Nat.zero_le i) hi
    exact_mod_cast this
  have hml0 : 0 < (m : ℝ) * lag := mul_pos hmpos hlag
  have hL : 0 < -Real.log ((m : ℝ) * lag) := neg_pos.mpr (Real.log_neg hml0 hml)
  have hJ : 0 ≤ biScaleLevyEnergy f := biScaleLevyEnergy_nonneg hfc hf.continuous
  have hR : 0 ≤ 4 * Real.exp (1 / 2) * biScaleLevyEnergy f / (-Real.log ((m : ℝ) * lag)) :=
    div_nonneg (mul_nonneg (by positivity) hJ) hL.le
  rcases eq_or_ne i j with rfl | hij
  · simp only [sub_self, zero_mul, sub_self]
    exact hR
  set y : ℝ := ((i : ℝ) - j) * lag with hy
  have heven : autocorr f y = autocorr f |y| := by
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, autocorr_neg]
  have hdiff : 1 ≤ |(i : ℝ) - j| := by
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_pos (by linarith)]
      linarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]
      linarith
  have hdlt : |(i : ℝ) - j| < m := by
    rw [abs_lt]
    have hi' : (i : ℝ) < m := by exact_mod_cast hi
    have hj' : (j : ℝ) < m := by exact_mod_cast hj
    constructor <;> linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hyabs : |y| = |(i : ℝ) - j| * lag := by rw [hy, abs_mul, abs_of_pos hlag]
  have hy0 : 0 < |y| := by rw [hyabs]; exact mul_pos (by linarith) hlag
  have hyle : |y| ≤ (m : ℝ) * lag := by
    rw [hyabs]; exact mul_le_mul_of_nonneg_right hdlt.le hlag.le
  have hy1 : |y| ≤ 1 := hyle.trans hml.le
  have hinc := autocorr_increment_mul_log_le hf hfc hy0 hy1
  have hlog : -Real.log ((m : ℝ) * lag) ≤ -Real.log |y| :=
    neg_le_neg (Real.log_le_log hy0 hyle)
  have hΔ : 0 ≤ autocorr f 0 - autocorr f |y| := autocorr_sub_nonneg hfc hf.continuous _
  rw [heven, le_div_iff₀ hL]
  have he : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hmono : Real.exp (-(1 / 2 : ℝ)) * (autocorr f 0 - autocorr f |y|) *
      (-Real.log ((m : ℝ) * lag)) ≤ 4 * biScaleLevyEnergy f :=
    le_trans (mul_le_mul_of_nonneg_left hlog (mul_nonneg (Real.exp_pos _).le hΔ)) hinc
  calc
    (autocorr f 0 - autocorr f |y|) * -Real.log ((m : ℝ) * lag) =
        Real.exp (1 / 2) * (Real.exp (-(1 / 2 : ℝ)) * (autocorr f 0 - autocorr f |y|) *
          (-Real.log ((m : ℝ) * lag))) := by
      rw [← mul_assoc, ← mul_assoc, mul_comm (Real.exp (1 / 2)), he, one_mul]
    _ ≤ Real.exp (1 / 2) * (4 * biScaleLevyEnergy f) :=
      mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
    _ = _ := by ring

/-! ### 4. The linear logarithmic modulus and the inverse-linear interpolation law -/

/-- `L - log(L + 1) ≥ L/4` for `L ≥ 1`. -/
private theorem quarter_le_sub_log_add_one {L : ℝ} (hL : 1 ≤ L) :
    L / 4 ≤ L - Real.log (L + 1) := by
  have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 * L / 4 by linarith)
  have hle : L + 1 ≤ Real.exp (3 * L / 4) := by nlinarith
  have hl := Real.log_le_log (by linarith) hle
  rw [Real.log_exp] at hl
  linarith

/-- The modulus for a positive displacement `x ↦ x + d`. -/
private theorem neg_log_mul_abs_autocorr_add_sub_le (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (x : ℝ) {d : ℝ} (hd0 : 0 < d) (hd1 : d < 1) :
    (-Real.log d) * |autocorr f x - autocorr f (x + d)| ≤
      32 * Real.exp (1 / 2) * biScaleLevyEnergy f + 2 * autocorr f 0 := by
  have hc := hf.continuous
  have hJ : 0 ≤ biScaleLevyEnergy f := biScaleLevyEnergy_nonneg hfc hc
  have h0 : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have hE : 0 ≤ 32 * Real.exp (1 / 2) * biScaleLevyEnergy f := by positivity
  set L : ℝ := -Real.log d with hLdef
  have hL0 : 0 < L := neg_pos.mpr (Real.log_neg hd0 hd1)
  have hdL : d = Real.exp (-L) := by rw [hLdef, neg_neg, Real.exp_log hd0]
  have htriv : |autocorr f x - autocorr f (x + d)| ≤ 2 * autocorr f 0 := by
    calc
      _ ≤ |autocorr f x| + |autocorr f (x + d)| := abs_sub _ _
      _ ≤ _ := by linarith [abs_autocorr_le_zero hfc hc x, abs_autocorr_le_zero hfc hc (x + d)]
  rcases le_or_gt L 1 with hL1 | hL1
  · calc
      _ ≤ 1 * (2 * autocorr f 0) := mul_le_mul hL1 htriv (abs_nonneg _) zero_le_one
      _ ≤ _ := by linarith
  set m : ℕ := ⌈L⌉₊ with hmdef
  have hmL : L ≤ (m : ℝ) := Nat.le_ceil L
  have hmL1 : (m : ℝ) < L + 1 := Nat.ceil_lt_add_one hL0.le
  have hmpos : 0 < m := by
    have : (0 : ℝ) < m := lt_of_lt_of_le hL0 hmL
    exact_mod_cast this
  have hexpL : L + 1 < Real.exp L := Real.add_one_lt_exp hL0.ne'
  have hml : (m : ℝ) * d ≤ (L + 1) * Real.exp (-L) := by
    rw [hdL]; exact mul_le_mul_of_nonneg_right hmL1.le (Real.exp_pos _).le
  have hml1 : (m : ℝ) * d < 1 := by
    refine lt_of_le_of_lt hml ?_
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos L)]
    exact hexpL
  have hlogml : L / 4 ≤ -Real.log ((m : ℝ) * d) := by
    have hml0 : 0 < (m : ℝ) * d := mul_pos (by exact_mod_cast hmpos) hd0
    have h1 := Real.log_le_log hml0 hml
    rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp] at h1
    linarith [quarter_le_sub_log_add_one hL1.le]
  have hL4 : 0 < L / 4 := by linarith
  set B : ℝ := 4 * Real.exp (1 / 2) * biScaleLevyEnergy f / (-Real.log ((m : ℝ) * d))
    with hBdef
  have hBle : B ≤ 16 * Real.exp (1 / 2) * biScaleLevyEnergy f / L := by
    rw [hBdef, div_le_div_iff₀ (lt_of_lt_of_le hL4 hlogml) hL0]
    have hnum : 0 ≤ 4 * Real.exp (1 / 2) * biScaleLevyEnergy f := by positivity
    nlinarith
  have hD : autocorr f 0 - progressionSmoothedCorrelation f d m 0 ≤ B :=
    autocorr_zero_sub_progressionSmoothed_le d hmpos fun i hi j hj =>
      autocorr_progression_increment_le hf hfc hd0 hml1 hi hj
  have hS1 := abs_autocorr_sub_progressionSmoothed_le hfc hc d hmpos x
  have hS2 := abs_autocorr_sub_progressionSmoothed_le hfc hc d hmpos (x + d)
  have hstep := abs_progressionSmoothed_add_lag_sub_le hfc hc d hmpos x
  have hstepL : 2 * autocorr f 0 / m ≤ 2 * autocorr f 0 / L :=
    div_le_div_of_nonneg_left (by linarith) hL0 hmL
  have htotal : |autocorr f x - autocorr f (x + d)| ≤
      2 * (16 * Real.exp (1 / 2) * biScaleLevyEnergy f / L) + 2 * autocorr f 0 / L := by
    have hsplit : autocorr f x - autocorr f (x + d) =
        (autocorr f x - progressionSmoothedCorrelation f d m x) -
          (progressionSmoothedCorrelation f d m (x + d) -
            progressionSmoothedCorrelation f d m x) -
            (autocorr f (x + d) - progressionSmoothedCorrelation f d m (x + d)) := by ring
    rw [hsplit]
    calc
      _ ≤ |autocorr f x - progressionSmoothedCorrelation f d m x| +
          |progressionSmoothedCorrelation f d m (x + d) -
            progressionSmoothedCorrelation f d m x| +
          |autocorr f (x + d) - progressionSmoothedCorrelation f d m (x + d)| := by
        refine (abs_sub _ _).trans ?_
        exact add_le_add (abs_sub _ _) le_rfl
      _ ≤ _ := by linarith
  calc
    _ ≤ L * (2 * (16 * Real.exp (1 / 2) * biScaleLevyEnergy f / L) + 2 * autocorr f 0 / L) :=
      mul_le_mul_of_nonneg_left htotal hL0.le
    _ = _ := by field_simp; ring

/-- **Linear logarithmic modulus of continuity.** Every compact `C²` source has
`log(1/|x - y|) · |h(x) - h(y)| ≤ 32√e 𝒥(f) + 2h(0)` whenever `0 < |x - y| < 1`.
Krein's inequality gives only the square root of this rate. -/
theorem neg_log_mul_abs_autocorr_sub_le (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {x y : ℝ} (hd0 : 0 < |x - y|) (hd1 : |x - y| < 1) :
    (-Real.log |x - y|) * |autocorr f x - autocorr f y| ≤
      32 * Real.exp (1 / 2) * biScaleLevyEnergy f + 2 * autocorr f 0 := by
  rcases lt_or_gt_of_ne (sub_ne_zero.mp (abs_pos.mp hd0)) with h | h
  · have hd : |x - y| = y - x := by rw [abs_sub_comm, abs_of_pos (sub_pos.mpr h)]
    rw [hd] at hd0 hd1 ⊢
    have := neg_log_mul_abs_autocorr_add_sub_le hf hfc x hd0 hd1
    rwa [add_sub_cancel] at this
  · have hd : |x - y| = x - y := abs_of_pos (sub_pos.mpr h)
    rw [hd] at hd0 hd1 ⊢
    have := neg_log_mul_abs_autocorr_add_sub_le hf hfc y hd0 hd1
    rwa [add_sub_cancel, abs_sub_comm] at this

/-- **Inverse-linear integer-logarithmic interpolation law.** For every compact `C²` source
and every `T > 0`, the correlation at `T` is within `(32√e 𝒥(f) + 2h(0))/T` of its value at
the next integer-logarithmic node `log ⌈e^T⌉`. -/
theorem mul_abs_autocorr_sub_logarithmicCeilNode_le (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {T : ℝ} (hT : 0 < T) :
    T * |autocorr f T - autocorr f (Real.log (logarithmicCeilNode T : ℝ))| ≤
      32 * Real.exp (1 / 2) * biScaleLevyEnergy f + 2 * autocorr f 0 := by
  have hc := hf.continuous
  have hJ : 0 ≤ biScaleLevyEnergy f := biScaleLevyEnergy_nonneg hfc hc
  have h0 : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  obtain ⟨hlag0, hlag1⟩ := logarithmicCeilLag_bounds T
  have hνT : Real.log (logarithmicCeilNode T : ℝ) = T + logarithmicCeilLag T := by
    rw [logarithmicCeilLag]; ring
  rw [hνT]
  rcases eq_or_lt_of_le hlag0 with hl | hlagpos
  · rw [← hl, add_zero, sub_self, abs_zero, mul_zero]
    positivity
  have hlt1 : logarithmicCeilLag T < 1 :=
    lt_of_le_of_lt hlag1 (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hT))
  have hlog : T ≤ -Real.log (logarithmicCeilLag T) := by
    have := Real.log_le_log hlagpos hlag1
    rw [Real.log_exp] at this
    linarith
  calc
    _ ≤ (-Real.log (logarithmicCeilLag T)) *
        |autocorr f T - autocorr f (T + logarithmicCeilLag T)| :=
      mul_le_mul_of_nonneg_right hlog (abs_nonneg _)
    _ ≤ _ := neg_log_mul_abs_autocorr_add_sub_le hf hfc T hlagpos hlt1

/-! ### 5. The integer-logarithmic blind cone -/

/-- **Inverse-linear blind tail law.** If the correlation vanishes at every `log n`, `n ≥ 2`,
then `|T| |h(T)| ≤ 32√e 𝒥(f) + 2h(0)` at every location, uniformly in the support. -/
theorem abs_mul_abs_autocorr_le_of_integerLog_blind (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f)
    (hzeros : ∀ n : ℕ, 2 ≤ n → autocorr f (Real.log (n : ℝ)) = 0) (T : ℝ) :
    |T| * |autocorr f T| ≤ 32 * Real.exp (1 / 2) * biScaleLevyEnergy f + 2 * autocorr f 0 := by
  have hJ : 0 ≤ biScaleLevyEnergy f := biScaleLevyEnergy_nonneg hfc hf.continuous
  have h0 : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have key : ∀ S : ℝ, 0 < S →
      S * |autocorr f S| ≤ 32 * Real.exp (1 / 2) * biScaleLevyEnergy f + 2 * autocorr f 0 := by
    intro S hS
    have h := mul_abs_autocorr_sub_logarithmicCeilNode_le hf hfc hS
    rwa [hzeros _ (logarithmicCeilNode_ge_two hS), sub_zero] at h
  rcases lt_trichotomy T 0 with hT | rfl | hT
  · have := key (-T) (neg_pos.mpr hT)
    rwa [autocorr_neg, ← abs_of_neg hT] at this
  · simp only [abs_zero, zero_mul]
    positivity
  · rw [abs_of_pos hT]
    exact key T hT

/-- **Uniform square-integrable blind tails.** On the integer-logarithmic blind cone,
`∫_{T}^∞ h² ≤ (32√e 𝒥(f) + 2h(0))² / T` for every `T > 0`. -/
theorem integral_Ioi_autocorr_sq_le_of_integerLog_blind (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f)
    (hzeros : ∀ n : ℕ, 2 ≤ n → autocorr f (Real.log (n : ℝ)) = 0) {T : ℝ} (hT : 0 < T) :
    ∫ x in Ioi T, autocorr f x ^ 2 ≤
      (32 * Real.exp (1 / 2) * biScaleLevyEnergy f + 2 * autocorr f 0) ^ 2 / T := by
  set C : ℝ := 32 * Real.exp (1 / 2) * biScaleLevyEnergy f + 2 * autocorr f 0 with hC
  have hcont : Continuous (fun x => autocorr f x ^ 2) := (continuous_autocorr hf hfc).pow 2
  have hcs : HasCompactSupport (fun x => autocorr f x ^ 2) :=
    (hasCompactSupport_autocorr hfc).comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  have hint : IntegrableOn (fun x => autocorr f x ^ 2) (Ioi T) :=
    (hcont.integrable_of_hasCompactSupport hcs).integrableOn
  have hrint : IntegrableOn (fun x : ℝ => C ^ 2 * x ^ (-2 : ℝ)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul _
  have hpt : ∀ x ∈ Ioi T, autocorr f x ^ 2 ≤ C ^ 2 * x ^ (-2 : ℝ) := by
    intro x hx
    have hx0 : 0 < x := lt_trans hT hx
    have hb := abs_mul_abs_autocorr_le_of_integerLog_blind hf hfc hzeros x
    rw [abs_of_pos hx0] at hb
    have hrp : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
      rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hrp, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have habs : (x * |autocorr f x|) ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hx0.le (abs_nonneg _)) hb 2
    calc
      autocorr f x ^ 2 * x ^ 2 = (x * |autocorr f x|) ^ 2 := by rw [mul_pow, sq_abs]; ring
      _ ≤ _ := habs
  calc
    _ ≤ ∫ x in Ioi T, C ^ 2 * x ^ (-2 : ℝ) :=
      setIntegral_mono_on hint hrint measurableSet_Ioi hpt
    _ = C ^ 2 * (-T ^ ((-2 : ℝ) + 1) / ((-2 : ℝ) + 1)) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
    _ = C ^ 2 / T := by
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      field_simp

end

end GaloisForLFunctions.BiScaleUncertainty
