import GaloisForLFunctions.RHTower.WeilArchimedeanExactForm

/-!
# Pillar I: Krein Increment & Chord Cascade Geometry on the Positive-Definite Cone

This module inaugurates **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`) by establishing the derivative-free non-local metric
geometry of positive-definite correlation kernels `h(x) = autocorr f x = ∫ u, f u * f (u + x)`.

Whereas an arbitrary smooth function `h` that vanishes on a discrete grid `Λ` can recover to `h(0)`
immediately outside thin neighborhoods of `Λ` if its derivative norm `‖h'‖` is large, an
autocorrelation `h ∈ 𝒫(ℝ)` is governed by the Hilbert-space translation chord distance
`d_f(x, y) = ‖T_x f - T_y f‖₂ = √(2 (h(0) - h(x - y)))`.

## Main Results

1. **Pointwise Bounds & Sum/Difference Energies (`autocorr_sub_nonneg`, `autocorr_add_nonneg`,
   `abs_autocorr_le_zero`):**
   `0 ≤ h(0) - h(x)`, `0 ≤ h(0) + h(x)`, and `|h(x)| ≤ h(0)` for all `x ∈ ℝ`.
2. **Peter–Paul Chord Inequality & Subadditive Chord Triangle Law
   (`autocorr_chord_peter_paul`, `autocorr_sqrt_sub_add_le`):**
   For all `x, y ∈ ℝ` and `t > 0`,
   `h(0) - h(x + y) ≤ (1 + t) (h(0) - h(x)) + (1 + 1 / t) (h(0) - h(y))`,
   and taking the optimal `t` yields the exact subadditive triangle inequality
   `√(h(0) - h(x + y)) ≤ √(h(0) - h(x)) + √(h(0) - h(y))`.
3. **Krein Doubling, Quadratic Multiple & Dyadic Cascade Laws
   (`autocorr_sub_two_mul_le`, `autocorr_sub_nat_mul_le`, `autocorr_sub_pow_two_mul_le`):**
   For every `m : ℕ` and `k : ℕ`,
   `h(0) - h(2x) ≤ 4 (h(0) - h(x))`,
   `h(0) - h(m * x) ≤ m^2 * (h(0) - h(x))`, and
   `h(0) - h(2^k * x) ≤ 4^k * (h(0) - h(x))`.
4. **Derivative-Free Harmonic & Dyadic Sub-Grid Lower Bounds at Zero Nodes
   (`autocorr_harmonic_subgrid_ge_of_nonpos`, `autocorr_dyadic_subgrid_ge_of_zero`):**
   Whenever `h(x₀) ≤ 0` (in particular at any logarithmic grid node `x₀ = log n` where
   `h(log n) = 0`), every harmonic subdivision `x₀ / m` (`m ≥ 1`) and dyadic subdivision
   `x₀ / 2^k` satisfies the universal derivative-free lower bound
   `h(0) / m^2 ≤ h(0) - h(x₀ / m)` and `h(0) / 4^k ≤ h(0) - h(x₀ / 2^k)`.
5. **Krein's Positive-Definite Increment Inequality (`autocorr_krein_increment_sq_le`):**
   For all `x, y ∈ ℝ`,
   `(h(x) - h(y))^2 ≤ 2 * h(0) * (h(0) - h(x - y))`.
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace GaloisForLFunctions.BiScaleUncertainty

open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section

variable {f : ℝ → ℝ}

/-! ### 1. Fundamental Sum/Difference Shift Identities and Pointwise Envelope -/

/-- The `L²` norm square of `f` equals `autocorr f 0`. -/
theorem integral_sq_eq_autocorr_zero (f : ℝ → ℝ) :
    (∫ u, f u ^ 2) = autocorr f 0 := by
  unfold autocorr
  congr 1
  funext u
  rw [add_zero, sq]

/-- Shifted difference `L²` identity: `∫ (f(u + x) - f(u + y))² du = 2 (h(0) - h(x - y))`. -/
theorem integral_shift_sub_shift_sq (hfc : HasCompactSupport f) (hf : Continuous f) (x y : ℝ) :
    (∫ u, (f (u + x) - f (u + y)) ^ 2) = 2 * (autocorr f 0 - autocorr f (x - y)) := by
  have htrans := integral_add_right_eq_self (μ := volume)
    (fun u => (f u - f (u + (y - x))) ^ 2) x
  have hcongr : (fun u => (f (u + x) - f (u + y)) ^ 2) =
      fun u => (f (u + x) - f (u + x + (y - x))) ^ 2 := by
    funext u
    rw [show u + x + (y - x) = u + y by ring]
  rw [hcongr, htrans, integral_sub_shift_sq hfc hf (y - x),
    show y - x = -(x - y) by ring, autocorr_neg]

/-- Sum-shift `L²` identity: `∫ (f(u) + f(u + x))² du = 2 (h(0) + h(x))`. -/
theorem integral_add_shift_sq (hfc : HasCompactSupport f) (hf : Continuous f) (x : ℝ) :
    (∫ u, (f u + f (u + x)) ^ 2) = 2 * (autocorr f 0 + autocorr f x) := by
  have hi1 : Integrable (fun u => f u ^ 2) := integrable_sq hf hfc
  have hc2 : Continuous (fun u => f (u + x)) := hf.comp (continuous_add_const x)
  have hcs2 : HasCompactSupport (fun u => f (u + x)) := hasCompactSupport_comp_add hfc x
  have hi2 : Integrable (fun u => f (u + x) ^ 2) := integrable_sq hc2 hcs2
  have hi3 : Integrable (fun u => f u * f (u + x)) := integrable_mul_shift hf hfc x
  have hrew : (fun u => (f u + f (u + x)) ^ 2) =
      fun u => (f u ^ 2 + f (u + x) ^ 2) + 2 * (f u * f (u + x)) := by
    funext u; ring
  have e1a : (∫ u, ((f u ^ 2 + f (u + x) ^ 2) + 2 * (f u * f (u + x)))) =
      (∫ u, (f u ^ 2 + f (u + x) ^ 2)) + ∫ u, 2 * (f u * f (u + x)) :=
    integral_add (hi1.add hi2) (hi3.const_mul 2)
  have e2 : (∫ u, (f u ^ 2 + f (u + x) ^ 2)) = (∫ u, f u ^ 2) + ∫ u, f (u + x) ^ 2 :=
    integral_add hi1 hi2
  have e3 : (∫ u, f (u + x) ^ 2) = ∫ u, f u ^ 2 :=
    integral_add_right_eq_self (fun u => f u ^ 2) x
  rw [hrew, e1a, e2, e3, integral_const_mul, integral_sq_eq_autocorr_zero]
  unfold autocorr
  ring

/-- `0 ≤ h(0)`. -/
theorem autocorr_zero_nonneg (f : ℝ → ℝ) : 0 ≤ autocorr f 0 := by
  rw [← integral_sq_eq_autocorr_zero]
  exact integral_nonneg fun u => sq_nonneg (f u)

/-- `0 ≤ h(0) - h(x)` for every shift `x ∈ ℝ`. -/
theorem autocorr_sub_nonneg (hfc : HasCompactSupport f) (hf : Continuous f) (x : ℝ) :
    0 ≤ autocorr f 0 - autocorr f x := by
  have h0 : 0 ≤ ∫ u, (f u - f (u + x)) ^ 2 := integral_nonneg fun u => sq_nonneg _
  rw [integral_sub_shift_sq hfc hf x] at h0
  linarith

/-- `0 ≤ h(0) + h(x)` for every shift `x ∈ ℝ`. -/
theorem autocorr_add_nonneg (hfc : HasCompactSupport f) (hf : Continuous f) (x : ℝ) :
    0 ≤ autocorr f 0 + autocorr f x := by
  have h0 : 0 ≤ ∫ u, (f u + f (u + x)) ^ 2 := integral_nonneg fun u => sq_nonneg _
  rw [integral_add_shift_sq hfc hf x] at h0
  linarith

/-- Cauchy–Schwarz pointwise envelope: `|h(x)| ≤ h(0)` for all `x ∈ ℝ`. -/
theorem abs_autocorr_le_zero (hfc : HasCompactSupport f) (hf : Continuous f) (x : ℝ) :
    |autocorr f x| ≤ autocorr f 0 := by
  rw [abs_le]
  exact ⟨by linarith [autocorr_add_nonneg hfc hf x], by linarith [autocorr_sub_nonneg hfc hf x]⟩

/-- If `h(0) = 0`, then `h(x) = 0` identically for all `x ∈ ℝ`. -/
theorem autocorr_eq_zero_of_zero_eq_zero (hfc : HasCompactSupport f) (hf : Continuous f)
    (h0 : autocorr f 0 = 0) (x : ℝ) : autocorr f x = 0 := by
  have habs := abs_autocorr_le_zero hfc hf x
  rw [h0] at habs
  exact abs_nonpos_iff.mp habs

/-! ### 2. Peter–Paul Chord Inequality & Subadditive Chord Triangle Law -/

/-- Pointwise Peter–Paul inequality for real numbers:
`(a + b)² ≤ (1 + t) a² + (1 + 1 / t) b²` for all `t > 0`. -/
theorem sq_add_le_one_add_mul_sq {a b t : ℝ} (ht : 0 < t) :
    (a + b) ^ 2 ≤ (1 + t) * a ^ 2 + (1 + 1 / t) * b ^ 2 := by
  have hsq : 0 ≤ (t * a - b) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have hident : (1 + t) * a ^ 2 + (1 + 1 / t) * b ^ 2 - (a + b) ^ 2 = (t * a - b) ^ 2 / t := by
    field_simp
    ring
  linarith

/-- **Peter–Paul Chord Inequality:**
For any `x, y ∈ ℝ` and `t > 0`,
`h(0) - h(x + y) ≤ (1 + t) (h(0) - h(x)) + (1 + 1 / t) (h(0) - h(y))`. -/
theorem autocorr_chord_peter_paul (hfc : HasCompactSupport f) (hf : Continuous f)
    (x y : ℝ) {t : ℝ} (ht : 0 < t) :
    autocorr f 0 - autocorr f (x + y) ≤
      (1 + t) * (autocorr f 0 - autocorr f x) +
        (1 + 1 / t) * (autocorr f 0 - autocorr f y) := by
  set A : ℝ → ℝ := fun u => f u - f (u + x)
  set B : ℝ → ℝ := fun u => f (u + x) - f (u + (x + y))
  have hAc : Continuous A := hf.sub (hf.comp (continuous_add_const x))
  have hAcs : HasCompactSupport A := hfc.sub (hasCompactSupport_comp_add hfc x)
  have hBc : Continuous B :=
    (hf.comp (continuous_add_const x)).sub (hf.comp (continuous_add_const (x + y)))
  have hBcs : HasCompactSupport B :=
    (hasCompactSupport_comp_add hfc x).sub (hasCompactSupport_comp_add hfc (x + y))
  have hiA : Integrable (fun u => A u ^ 2) := integrable_sq hAc hAcs
  have hiB : Integrable (fun u => B u ^ 2) := integrable_sq hBc hBcs
  have hiAB : Integrable (fun u => (A u + B u) ^ 2) :=
    integrable_sq (hAc.add hBc) (hAcs.add hBcs)
  have hmono : (∫ u, (A u + B u) ^ 2) ≤
      ∫ u, ((1 + t) * A u ^ 2 + (1 + 1 / t) * B u ^ 2) := by
    refine integral_mono hiAB ((hiA.const_mul (1 + t)).add (hiB.const_mul (1 + 1 / t))) ?_
    intro u
    exact sq_add_le_one_add_mul_sq ht
  rw [integral_add (hiA.const_mul (1 + t)) (hiB.const_mul (1 + 1 / t)),
    integral_const_mul, integral_const_mul] at hmono
  have hsum : (fun u => (A u + B u) ^ 2) = fun u => (f u - f (u + (x + y))) ^ 2 := by
    funext u; simp only [A, B]; ring
  have hAint : (∫ u, A u ^ 2) = 2 * (autocorr f 0 - autocorr f x) :=
    integral_sub_shift_sq hfc hf x
  have hBint : (∫ u, B u ^ 2) = 2 * (autocorr f 0 - autocorr f y) := by
    have := integral_shift_sub_shift_sq hfc hf x (x + y)
    simpa [B, show x - (x + y) = -y by ring, autocorr_neg] using this
  rw [hsum, integral_sub_shift_sq hfc hf (x + y), hAint, hBint] at hmono
  linarith

/-- **Subadditive Chord Triangle Inequality:**
`√(h(0) - h(x + y)) ≤ √(h(0) - h(x)) + √(h(0) - h(y))` for all `x, y ∈ ℝ`. -/
theorem autocorr_sqrt_sub_add_le (hfc : HasCompactSupport f) (hf : Continuous f) (x y : ℝ) :
    Real.sqrt (autocorr f 0 - autocorr f (x + y)) ≤
      Real.sqrt (autocorr f 0 - autocorr f x) + Real.sqrt (autocorr f 0 - autocorr f y) := by
  set a := Real.sqrt (autocorr f 0 - autocorr f x)
  set b := Real.sqrt (autocorr f 0 - autocorr f y)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = autocorr f 0 - autocorr f x :=
    Real.sq_sqrt (autocorr_sub_nonneg hfc hf x)
  have hb2 : b ^ 2 = autocorr f 0 - autocorr f y :=
    Real.sq_sqrt (autocorr_sub_nonneg hfc hf y)
  rw [← Real.sqrt_sq (add_nonneg ha0 hb0)]
  apply Real.sqrt_le_sqrt
  rcases eq_or_lt_of_le ha0 with ha_eq | ha_pos
  · have hx0 : autocorr f 0 - autocorr f x = 0 := by nlinarith [ha2, ha_eq]
    rcases eq_or_lt_of_le hb0 with hb_eq | hb_pos
    · have hy0 : autocorr f 0 - autocorr f y = 0 := by nlinarith [hb2, hb_eq]
      have hpp := autocorr_chord_peter_paul hfc hf x y zero_lt_one
      rw [hx0, hy0] at hpp
      linarith [sq_nonneg (a + b)]
    · apply le_of_forall_pos_le_add
      intro ε hε
      have ht : 0 < 2 * b ^ 2 / ε := div_pos (by positivity) hε
      have hpp := autocorr_chord_peter_paul hfc hf x y ht
      rw [hx0, ← hb2] at hpp
      have hsimp : (1 + 1 / (2 * b ^ 2 / ε)) * b ^ 2 = b ^ 2 + ε / 2 := by
        field_simp
      rw [hsimp] at hpp
      have hab : (a + b) ^ 2 = b ^ 2 := by rw [← ha_eq, zero_add]
      linarith
  · rcases eq_or_lt_of_le hb0 with hb_eq | hb_pos
    · have hy0 : autocorr f 0 - autocorr f y = 0 := by nlinarith [hb2, hb_eq]
      apply le_of_forall_pos_le_add
      intro ε hε
      have ht : 0 < ε / (2 * a ^ 2) := div_pos hε (by positivity)
      have hpp := autocorr_chord_peter_paul hfc hf x y ht
      rw [hy0, ← ha2] at hpp
      have hsimp : (1 + ε / (2 * a ^ 2)) * a ^ 2 = a ^ 2 + ε / 2 := by
        field_simp
      rw [hsimp] at hpp
      have hab : (a + b) ^ 2 = a ^ 2 := by rw [← hb_eq, add_zero]
      linarith
    · have ht : 0 < b / a := div_pos hb_pos ha_pos
      have hpp := autocorr_chord_peter_paul hfc hf x y ht
      rw [← ha2, ← hb2] at hpp
      have hsimp : (1 + b / a) * a ^ 2 + (1 + 1 / (b / a)) * b ^ 2 = (a + b) ^ 2 := by
        field_simp
        ring
      linarith

/-! ### 3. Doubling, Quadratic Multiple, and Dyadic Cascade Laws -/

/-- **Symmetric Chord Sum Bound:**
`h(0) - h(x + y) ≤ 2 (h(0) - h(x)) + 2 (h(0) - h(y))`. -/
theorem autocorr_sub_add_le (hfc : HasCompactSupport f) (hf : Continuous f) (x y : ℝ) :
    autocorr f 0 - autocorr f (x + y) ≤
      2 * (autocorr f 0 - autocorr f x) + 2 * (autocorr f 0 - autocorr f y) := by
  have h := autocorr_chord_peter_paul hfc hf x y zero_lt_one
  linarith

/-- **Krein Doubling Inequality:**
`h(0) - h(2x) ≤ 4 (h(0) - h(x))` for all `x ∈ ℝ`. -/
theorem autocorr_sub_two_mul_le (hfc : HasCompactSupport f) (hf : Continuous f) (x : ℝ) :
    autocorr f 0 - autocorr f (2 * x) ≤ 4 * (autocorr f 0 - autocorr f x) := by
  have h := autocorr_sub_add_le hfc hf x x
  rw [show x + x = 2 * x by ring] at h
  linarith

/-- **Exact Sublinear Multiple Law for the Chord Distance:**
`√(h(0) - h(m * x)) ≤ m * √(h(0) - h(x))` for every `m : ℕ` and `x ∈ ℝ`. -/
theorem autocorr_sqrt_sub_nat_mul_le (hfc : HasCompactSupport f) (hf : Continuous f)
    (m : ℕ) (x : ℝ) :
    Real.sqrt (autocorr f 0 - autocorr f ((m : ℝ) * x)) ≤
      (m : ℝ) * Real.sqrt (autocorr f 0 - autocorr f x) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hsplit : ((m + 1 : ℕ) : ℝ) * x = (m : ℝ) * x + x := by push_cast; ring
    rw [hsplit]
    calc Real.sqrt (autocorr f 0 - autocorr f ((m : ℝ) * x + x))
        ≤ Real.sqrt (autocorr f 0 - autocorr f ((m : ℝ) * x)) +
            Real.sqrt (autocorr f 0 - autocorr f x) :=
          autocorr_sqrt_sub_add_le hfc hf ((m : ℝ) * x) x
      _ ≤ (m : ℝ) * Real.sqrt (autocorr f 0 - autocorr f x) +
            Real.sqrt (autocorr f 0 - autocorr f x) := by linarith
      _ = ((m + 1 : ℕ) : ℝ) * Real.sqrt (autocorr f 0 - autocorr f x) := by push_cast; ring

/-- **Exact Quadratic Multiple Cascade:**
`h(0) - h(m * x) ≤ m^2 * (h(0) - h(x))` for every `m : ℕ` and `x ∈ ℝ`. -/
theorem autocorr_sub_nat_mul_le (hfc : HasCompactSupport f) (hf : Continuous f)
    (m : ℕ) (x : ℝ) :
    autocorr f 0 - autocorr f ((m : ℝ) * x) ≤
      (m : ℝ) ^ 2 * (autocorr f 0 - autocorr f x) := by
  have hsqrt := autocorr_sqrt_sub_nat_mul_le hfc hf m x
  have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) hsqrt
  rw [← sq, ← sq, Real.sq_sqrt (autocorr_sub_nonneg hfc hf _),
    mul_pow, Real.sq_sqrt (autocorr_sub_nonneg hfc hf x)] at hsq
  exact hsq

/-- **Dyadic Cascade Inequality:**
`h(0) - h(2^k * x) ≤ 4^k * (h(0) - h(x))` for every `k : ℕ` and `x ∈ ℝ`. -/
theorem autocorr_sub_pow_two_mul_le (hfc : HasCompactSupport f) (hf : Continuous f)
    (k : ℕ) (x : ℝ) :
    autocorr f 0 - autocorr f ((2 : ℝ) ^ k * x) ≤
      (4 : ℝ) ^ k * (autocorr f 0 - autocorr f x) := by
  have h := autocorr_sub_nat_mul_le hfc hf (2 ^ k) x
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; rfl
  have hpow : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hcast, hpow] at h
  exact h

/-! ### 4. Derivative-Free Sub-Grid Lower Bounds at Zero / Nonpositive Nodes -/

/-- **Harmonic Sub-Grid Lower Bound:**
For any `x₀ ∈ ℝ` and any integer `m ≥ 1`,
`(h(0) - h(x₀)) / m^2 ≤ h(0) - h(x₀ / m)`. -/
theorem autocorr_harmonic_subgrid_ge (hfc : HasCompactSupport f) (hf : Continuous f)
    (x₀ : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (autocorr f 0 - autocorr f x₀) / (m : ℝ) ^ 2 ≤ autocorr f 0 - autocorr f (x₀ / (m : ℝ)) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr ( Nat.pos_of_ne_zero (by omega) )
  have hm2_pos : (0 : ℝ) < (m : ℝ) ^ 2 := pow_pos hm_pos 2
  rw [div_le_iff₀ hm2_pos, mul_comm]
  have h := autocorr_sub_nat_mul_le hfc hf m (x₀ / (m : ℝ))
  rwa [mul_div_cancel₀ x₀ hm_pos.ne'] at h

/-- **Derivative-Free Harmonic Sub-Grid Lower Bound from a Nonpositive Node:**
Whenever `h(x₀) ≤ 0` (e.g., at any logarithmic grid node `x₀ = log n` where `h(log n) = 0`),
every harmonic subdivision `x₀ / m` (`m ≥ 1`) satisfies `h(0) / m^2 ≤ h(0) - h(x₀ / m)`. -/
theorem autocorr_harmonic_subgrid_ge_of_nonpos (hfc : HasCompactSupport f) (hf : Continuous f)
    {x₀ : ℝ} (hx₀ : autocorr f x₀ ≤ 0) {m : ℕ} (hm : 1 ≤ m) :
    autocorr f 0 / (m : ℝ) ^ 2 ≤ autocorr f 0 - autocorr f (x₀ / (m : ℝ)) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm2_pos : (0 : ℝ) < (m : ℝ) ^ 2 := pow_pos hm_pos 2
  have h1 : autocorr f 0 / (m : ℝ) ^ 2 ≤ (autocorr f 0 - autocorr f x₀) / (m : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) hm2_pos.le
  exact h1.trans (autocorr_harmonic_subgrid_ge hfc hf x₀ hm)

/-- **Derivative-Free Dyadic Sub-Grid Lower Bound at a Zero Node:**
Whenever `h(x₀) = 0`, every dyadic subdivision `x₀ / 2^k` (`k : ℕ`) satisfies
`h(0) / 4^k ≤ h(0) - h(x₀ / 2^k)`. -/
theorem autocorr_dyadic_subgrid_ge_of_zero (hfc : HasCompactSupport f) (hf : Continuous f)
    {x₀ : ℝ} (hx₀ : autocorr f x₀ = 0) (k : ℕ) :
    autocorr f 0 / (4 : ℝ) ^ k ≤ autocorr f 0 - autocorr f (x₀ / (2 : ℝ) ^ k) := by
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos zero_lt_two k
  have h4_pos : (0 : ℝ) < (4 : ℝ) ^ k := pow_pos (by norm_num) k
  rw [div_le_iff₀ h4_pos, mul_comm]
  have h := autocorr_sub_pow_two_mul_le hfc hf k (x₀ / (2 : ℝ) ^ k)
  rw [mul_div_cancel₀ x₀ h2_pos.ne', hx₀, sub_zero] at h
  exact h

/-! ### 5. Krein's Positive-Definite Increment Inequality -/

/-- Quadratic discriminant inequality for the correlation increment:
For all `x, y, t ∈ ℝ`,
`0 ≤ 2 (h(0) - h(x - y)) - 2 t (h(x) - h(y)) + t^2 h(0)`. -/
theorem autocorr_increment_quadratic_nonneg (hfc : HasCompactSupport f) (hf : Continuous f)
    (x y t : ℝ) :
    0 ≤ 2 * (autocorr f 0 - autocorr f (x - y)) -
      2 * t * (autocorr f x - autocorr f y) + t ^ 2 * autocorr f 0 := by
  set D : ℝ → ℝ := fun u => f (u + x) - f (u + y)
  have hDc : Continuous D :=
    (hf.comp (continuous_add_const x)).sub (hf.comp (continuous_add_const y))
  have hDcs : HasCompactSupport D :=
    (hasCompactSupport_comp_add hfc x).sub (hasCompactSupport_comp_add hfc y)
  have hiD2 : Integrable (fun u => D u ^ 2) := integrable_sq hDc hDcs
  have hif2 : Integrable (fun u => f u ^ 2) := integrable_sq hf hfc
  have hifx : Integrable (fun u => f u * f (u + x)) := integrable_mul_shift hf hfc x
  have hify : Integrable (fun u => f u * f (u + y)) := integrable_mul_shift hf hfc y
  have hiDf : Integrable (fun u => f u * D u) := by
    have hrew : (fun u => f u * D u) = fun u => f u * f (u + x) - f u * f (u + y) := by
      funext u; simp only [D]; ring
    rw [hrew]
    exact hifx.sub hify
  have h0 : 0 ≤ ∫ u, (D u - t * f u) ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hexpand : (fun u => (D u - t * f u) ^ 2) =
      fun u => (D u ^ 2 - 2 * t * (f u * D u)) + t ^ 2 * f u ^ 2 := by
    funext u; ring
  have e1 : (∫ u, ((D u ^ 2 - 2 * t * (f u * D u)) + t ^ 2 * f u ^ 2)) =
      (∫ u, (D u ^ 2 - 2 * t * (f u * D u))) + ∫ u, t ^ 2 * f u ^ 2 :=
    integral_add (hiD2.sub (hiDf.const_mul (2 * t))) (hif2.const_mul (t ^ 2))
  have e2 : (∫ u, (D u ^ 2 - 2 * t * (f u * D u))) =
      (∫ u, D u ^ 2) - ∫ u, 2 * t * (f u * D u) :=
    integral_sub hiD2 (hiDf.const_mul (2 * t))
  rw [hexpand, e1, e2, integral_const_mul, integral_const_mul] at h0
  have hDint : (∫ u, D u ^ 2) = 2 * (autocorr f 0 - autocorr f (x - y)) :=
    integral_shift_sub_shift_sq hfc hf x y
  have hDfint : (∫ u, f u * D u) = autocorr f x - autocorr f y := by
    have hrew : (fun u => f u * D u) = fun u => f u * f (u + x) - f u * f (u + y) := by
      funext u; simp only [D]; ring
    rw [hrew, integral_sub hifx hify]
    rfl
  rw [hDint, hDfint, integral_sq_eq_autocorr_zero] at h0
  exact h0

/-- **Krein's Positive-Definite Increment Inequality:**
For any `x, y ∈ ℝ`,
`(h(x) - h(y))^2 ≤ 2 * h(0) * (h(0) - h(x - y))`. -/
theorem autocorr_krein_increment_sq_le (hfc : HasCompactSupport f) (hf : Continuous f)
    (x y : ℝ) :
    (autocorr f x - autocorr f y) ^ 2 ≤
      2 * autocorr f 0 * (autocorr f 0 - autocorr f (x - y)) := by
  rcases eq_or_lt_of_le (autocorr_zero_nonneg f) with h0_eq | h0_pos
  · have hx := autocorr_eq_zero_of_zero_eq_zero hfc hf h0_eq.symm x
    have hy := autocorr_eq_zero_of_zero_eq_zero hfc hf h0_eq.symm y
    rw [hx, hy, ← h0_eq]
    ring_nf
    exact le_rfl
  · have hq := autocorr_increment_quadratic_nonneg hfc hf x y
      ((autocorr f x - autocorr f y) / autocorr f 0)
    have hmul := mul_nonneg h0_pos.le hq
    have hident : autocorr f 0 * (2 * (autocorr f 0 - autocorr f (x - y)) -
        2 * ((autocorr f x - autocorr f y) / autocorr f 0) * (autocorr f x - autocorr f y) +
        ((autocorr f x - autocorr f y) / autocorr f 0) ^ 2 * autocorr f 0) =
        2 * autocorr f 0 * (autocorr f 0 - autocorr f (x - y)) -
          (autocorr f x - autocorr f y) ^ 2 := by
      have hne : autocorr f 0 ≠ 0 := h0_pos.ne'
      field_simp
      ring
    linarith

/-- **Krein Zero-Collar Lower Bound:**
At any zero node `x₀ ∈ ℝ` where `h(x₀) = 0`, for all `x ∈ ℝ`,
`h(x)^2 ≤ 2 * h(0) * (h(0) - h(x - x₀))`. -/
theorem autocorr_sq_le_two_mul_sub_of_zero (hfc : HasCompactSupport f) (hf : Continuous f)
    {x₀ : ℝ} (hx₀ : autocorr f x₀ = 0) (x : ℝ) :
    autocorr f x ^ 2 ≤ 2 * autocorr f 0 * (autocorr f 0 - autocorr f (x - x₀)) := by
  have h := autocorr_krein_increment_sq_le hfc hf x x₀
  rwa [hx₀, sub_zero] at h

end

end GaloisForLFunctions.BiScaleUncertainty
