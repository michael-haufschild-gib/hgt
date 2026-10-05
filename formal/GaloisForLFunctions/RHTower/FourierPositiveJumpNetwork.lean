import GaloisForLFunctions.RHTower.ThetaQuantileFourierQuotient
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier-positive jump networks

Let `h` be continuous on `[0,1]`, symmetric about `1/2`, positive on `(0,1)`, zero at the endpoints,
with negative nonzero cosine coefficients `ĥ(n) = ∫₀¹ h cos 2πnt` and finite actions
`Φ_m = ∫₀¹ (1 − cos 2πmt)/h`.  With conductances `a_n = −ĥ(n) > 0`:

* `Σ a_n = ĥ(0)/2` and `h(t) = 2Σ a_n (1 − cos 2πnt)`, absolutely and uniformly on `[0,1]`;
* the jump Laplacian `(L_a f)_m = Σ a_n (2f_m − f_{m−n} − f_{m+n})` has symbol `h`;
* unit capacity `2Σ a_n Φ_n = 1` and the point-source Green law `L_a Φ = −δ₀`;
* the dipole voltage `v^(n)_m = Φ_m − Φ_{m−n}` solves `L_a v^(n) = δ_n − δ₀`, with drop `2Φ_n`;
* the grounded kernel `Φ_m + Φ_n − Φ_{m−n}` is positive: its quadratic form is
  `∫₀¹ |Σ c_m (1 − e^{2πimt})|²/h`.

Summability of the conductances comes from positivity of the Fejér kernels; the expansion of `h`
from the Fourier series of a continuous function with summable coefficients.
-/

namespace RHTower

open MeasureTheory Filter Topology Set

noncomputable section

local instance factZeroLtOneJumpNetwork : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The cosine coefficient `ĥ(n) = ∫₀¹ h(t) cos 2πnt dt`. -/
def profileCoeff (h : ℝ → ℝ) (n : ℤ) : ℝ := ∫ t in (0 : ℝ)..1, h t * Real.cos (2 * Real.pi * n * t)

/-- The jump conductance `a_n = −ĥ(n)`. -/
def jumpConductance (h : ℝ → ℝ) (n : ℕ) : ℝ := -profileCoeff h n

/-- The action `Φ_m = ∫₀¹ (1 − cos 2πmt)/h(t) dt`. -/
def profileAction (h : ℝ → ℝ) (m : ℤ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - Real.cos (2 * Real.pi * m * t)) / h t

/-- The hypotheses of the potential-kernel theorem. -/
structure IsJumpProfile (h : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn h (Icc 0 1)
  symm : ∀ t, h (1 - t) = h t
  pos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < h t
  zero : h 0 = 0
  coeff_neg : ∀ n : ℕ, 1 ≤ n → profileCoeff h n < 0
  action : ∀ m : ℤ, IntervalIntegrable (fun t => (1 - Real.cos (2 * Real.pi * m * t)) / h t) volume 0 1

theorem intervalIntegrable_complex_ofReal {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => (f x : ℂ)) volume a b :=
  ⟨hf.1.ofReal, hf.2.ofReal⟩

theorem profileCoeff_neg (h : ℝ → ℝ) (n : ℤ) : profileCoeff h (-n) = profileCoeff h n := by
  simp only [profileCoeff, Int.cast_neg, mul_neg, neg_mul, Real.cos_neg]

theorem profileAction_neg (h : ℝ → ℝ) (m : ℤ) : profileAction h (-m) = profileAction h m := by
  simp only [profileAction, Int.cast_neg, mul_neg, neg_mul, Real.cos_neg]

theorem profileAction_zero (h : ℝ → ℝ) : profileAction h 0 = 0 := by
  simp [profileAction]

/-! ## Fejér positivity -/

/-- The Fejér identity `N + 2Σ_{m<N} (N − m − 1) cos((m+1)θ) = |Σ_{k<N} e^{ikθ}|²`. -/
theorem fejer_identity (θ : ℝ) (N : ℕ) :
    (N : ℝ) + 2 * ∑ m ∈ Finset.range N, ((N : ℝ) - (m + 1)) * Real.cos ((m + 1) * θ) =
      (∑ k ∈ Finset.range N, Real.cos (k * θ)) ^ 2 + (∑ k ∈ Finset.range N, Real.sin (k * θ)) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hcross : (∑ k ∈ Finset.range N, Real.cos (k * θ)) * Real.cos (N * θ) +
        (∑ k ∈ Finset.range N, Real.sin (k * θ)) * Real.sin (N * θ) =
        ∑ m ∈ Finset.range N, Real.cos ((m + 1) * θ) := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib,
        ← Finset.sum_range_reflect (fun m : ℕ => Real.cos (((m : ℝ) + 1) * θ)) N]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.1 hk
      rw [show Real.cos (k * θ) * Real.cos (N * θ) + Real.sin (k * θ) * Real.sin (N * θ) =
        Real.cos (N * θ - k * θ) by rw [Real.cos_sub]; ring]
      congr 1
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    have hsplit : ∑ m ∈ Finset.range N, (((N : ℝ) + 1) - (m + 1)) * Real.cos ((m + 1) * θ) =
        ∑ m ∈ Finset.range N, ((N : ℝ) - (m + 1)) * Real.cos ((m + 1) * θ) +
          ∑ m ∈ Finset.range N, Real.cos ((m + 1) * θ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    push_cast
    rw [Finset.sum_range_succ (fun m : ℕ => (((N : ℝ) + 1) - (m + 1)) * Real.cos ((m + 1) * θ)), hsplit,
      Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 := Real.sin_sq_add_cos_sq ((N : ℝ) * θ)
    linear_combination ih - 2 * hcross - h1

theorem fejerSum_nonneg (θ : ℝ) (N : ℕ) :
    0 ≤ (N : ℝ) + 2 * ∑ m ∈ Finset.range N, ((N : ℝ) - (m + 1)) * Real.cos ((m + 1) * θ) := by
  rw [fejer_identity]
  positivity

/-- A function odd about `1/2` has zero integral over `[0,1]`. -/
theorem integral_unit_eq_zero_of_odd {g : ℝ → ℝ} (hg : ∀ t, g (1 - t) = -g t) :
    ∫ t in (0 : ℝ)..1, g t = 0 := by
  have h1 := intervalIntegral.integral_comp_sub_left g (1 : ℝ) (a := 0) (b := 1)
  simp only [sub_self, sub_zero, hg, intervalIntegral.integral_neg] at h1
  linarith

theorem integral_cos_two_pi_int_mul (m : ℤ) :
    ∫ t in (0 : ℝ)..1, Real.cos (2 * Real.pi * m * t) = if m = 0 then 1 else 0 := by
  split_ifs with hm
  · simp [hm]
  have hc : (2 * Real.pi * m : ℝ) ≠ 0 := by
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    positivity
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos, mul_zero, mul_one,
    Real.sin_zero, sub_zero, show 2 * Real.pi * (m : ℝ) = ((2 * m : ℤ) : ℝ) * Real.pi by push_cast; ring,
    Real.sin_int_mul_pi, smul_zero]

/-- The cosine bracket of the Laplacian: `2(1−cos mθ) − (1−cos(m−j)θ) − (1−cos(m+j)θ) = −2 cos mθ (1 − cos jθ)`. -/
theorem cos_bracket (m j : ℤ) (t : ℝ) :
    2 * (1 - Real.cos (2 * Real.pi * m * t)) - (1 - Real.cos (2 * Real.pi * ((m - j : ℤ) : ℝ) * t)) -
      (1 - Real.cos (2 * Real.pi * ((m + j : ℤ) : ℝ) * t)) =
      -2 * Real.cos (2 * Real.pi * m * t) * (1 - Real.cos (2 * Real.pi * j * t)) := by
  rw [show 2 * Real.pi * ((m - j : ℤ) : ℝ) * t = 2 * Real.pi * m * t - 2 * Real.pi * j * t by push_cast; ring,
    show 2 * Real.pi * ((m + j : ℤ) : ℝ) * t = 2 * Real.pi * m * t + 2 * Real.pi * j * t by push_cast; ring,
    Real.cos_sub, Real.cos_add]
  ring

/-- The pointwise grounded product `conj(1 − e_m)(1 − e_n)` in real coordinates. -/
theorem conj_one_sub_fourierMode_mul (m n : ℤ) (t : ℝ) :
    (starRingEnd ℂ) (1 - fourierMode m t) * (1 - fourierMode n t) =
      (((1 - Real.cos (2 * Real.pi * m * t)) + (1 - Real.cos (2 * Real.pi * n * t)) -
        (1 - Real.cos (2 * Real.pi * ((m - n : ℤ) : ℝ) * t)) : ℝ) : ℂ) +
      Complex.I * ((Real.sin (2 * Real.pi * m * t) * (1 - Real.cos (2 * Real.pi * n * t)) -
        (1 - Real.cos (2 * Real.pi * m * t)) * Real.sin (2 * Real.pi * n * t) : ℝ) : ℂ) := by
  rw [fourierMode_eq_cos_add_sin, fourierMode_eq_cos_add_sin,
    show 2 * Real.pi * ((m - n : ℤ) : ℝ) * t = 2 * Real.pi * m * t - 2 * Real.pi * n * t by push_cast; ring,
    Real.cos_sub]
  generalize Real.cos (2 * Real.pi * m * t) = cm
  generalize Real.cos (2 * Real.pi * n * t) = cn
  generalize Real.sin (2 * Real.pi * m * t) = sm
  generalize Real.sin (2 * Real.pi * n * t) = sn
  simp only [map_sub, map_one, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  linear_combination (-((sm : ℂ) * sn)) * Complex.I_sq

theorem abs_sin_mul_one_sub_cos_le (a b : ℝ) :
    |Real.sin a * (1 - Real.cos b)| ≤ (1 - Real.cos a) + (1 - Real.cos b) := by
  have h1 := Real.sin_sq_add_cos_sq a
  have h2 := Real.cos_le_one a
  have h3 := Real.neg_one_le_cos a
  have h4 := Real.cos_le_one b
  have h5 := Real.neg_one_le_cos b
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (Real.sin a + (1 - Real.cos b)), sq_nonneg (Real.sin a - (1 - Real.cos b))]

/-- The jump Laplacian `(L_a f)_m = Σ_{n ≥ 1} a_n (2f_m − f_{m−n} − f_{m+n})`. -/
def jumpLaplacian (a : ℕ → ℝ) (f : ℤ → ℂ) (m : ℤ) : ℂ :=
  ∑' n : ℕ, (a (n + 1) : ℂ) * (2 * f m - f (m - (n + 1 : ℕ)) - f (m + (n + 1 : ℕ)))

/-- **`L_a` is defined on bounded sequences.** -/
theorem summable_jumpLaplacian_term {a : ℕ → ℝ} (ha : Summable fun n => a (n + 1))
    (ha0 : ∀ n, 0 ≤ a (n + 1)) {f : ℤ → ℂ} {C : ℝ} (hf : ∀ m, ‖f m‖ ≤ C) (m : ℤ) :
    Summable fun n : ℕ => (a (n + 1) : ℂ) * (2 * f m - f (m - (n + 1 : ℕ)) - f (m + (n + 1 : ℕ))) := by
  refine Summable.of_norm_bounded (ha.mul_right (4 * C)) fun n => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  refine mul_le_mul_of_nonneg_left ?_ (ha0 n)
  calc ‖2 * f m - f (m - (n + 1 : ℕ)) - f (m + (n + 1 : ℕ))‖
      ≤ ‖2 * f m‖ + ‖f (m - (n + 1 : ℕ))‖ + ‖f (m + (n + 1 : ℕ))‖ := by
        linarith [norm_sub_le (2 * f m - f (m - (n + 1 : ℕ))) (f (m + (n + 1 : ℕ))),
          norm_sub_le (2 * f m) (f (m - (n + 1 : ℕ)))]
    _ ≤ 2 * C + C + C := by
        rw [norm_mul, Complex.norm_ofNat]
        gcongr <;> exact hf _
    _ = 4 * C := by ring

/-- The dipole voltage `v^(n)_m = Φ_m − Φ_{m−n}`. -/
def potentialVoltage (h : ℝ → ℝ) (n m : ℤ) : ℝ := profileAction h m - profileAction h (m - n)

/-- **The voltage drop**: `v^(n)_n − v^(n)_0 = 2Φ_n` (effective resistance `2Φ_n`). -/
theorem potentialVoltage_drop (h : ℝ → ℝ) (n : ℤ) :
    potentialVoltage h n n - potentialVoltage h n 0 = 2 * profileAction h n := by
  simp only [potentialVoltage, sub_self, zero_sub, profileAction_neg, profileAction_zero]
  ring

/-- The grounded covariance kernel `K(m,n) = Φ_m + Φ_n − Φ_{m−n}`. -/
def groundedKernel (h : ℝ → ℝ) (m n : ℤ) : ℝ := profileAction h m + profileAction h n - profileAction h (m - n)

/-- The decaying-gauge voltage is the grounded kernel minus the column constant `Φ_n`. -/
theorem potentialVoltage_eq_groundedKernel_sub (h : ℝ → ℝ) (n m : ℤ) :
    potentialVoltage h n m = groundedKernel h m n - profileAction h n := by
  simp only [potentialVoltage, groundedKernel]
  ring

/-- The partial conductance quotient `Σ_{n<N} 2a_{n+1}(1 − cos 2π(n+1)t)/h(t)`. -/
def capacityPartial (h : ℝ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, 2 * jumpConductance h (n + 1) *
    ((1 - Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℤ) * t)) / h t)

namespace IsJumpProfile

variable {h : ℝ → ℝ} (hh : IsJumpProfile h)
include hh

theorem one : h 1 = 0 := by
  have := hh.symm 0
  rw [sub_zero] at this
  rw [this, hh.zero]

theorem nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ h t := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0, hh.zero]
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · rw [h1, hh.one]
  exact (hh.pos t ⟨h0, h1⟩).le

theorem intervalIntegrable_mul {g : ℝ → ℝ} (hg : Continuous g) :
    IntervalIntegrable (fun t => h t * g t) volume 0 1 :=
  (hh.continuousOn.mul hg.continuousOn).intervalIntegrable_of_Icc zero_le_one

theorem profileCoeff_zero_nonneg : 0 ≤ profileCoeff h 0 := by
  refine intervalIntegral.integral_nonneg zero_le_one fun t ht => ?_
  simp only [Int.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one]
  exact hh.nonneg ht

theorem jumpConductance_pos {n : ℕ} (hn : 1 ≤ n) : 0 < jumpConductance h n :=
  neg_pos.2 (hh.coeff_neg n hn)

theorem jumpConductance_succ_nonneg (n : ℕ) : 0 ≤ jumpConductance h (n + 1) :=
  (hh.jumpConductance_pos (by omega)).le

/-- `∫₀¹ h · Fejér ≥ 0`, in coefficients. -/
theorem fejer_coeff_nonneg (N : ℕ) :
    0 ≤ (N : ℝ) * profileCoeff h 0 +
      2 * ∑ m ∈ Finset.range N, ((N : ℝ) - (m + 1)) * profileCoeff h ((m + 1 : ℕ) : ℤ) := by
  have hint : 0 ≤ ∫ t in (0 : ℝ)..1, h t * ((N : ℝ) + 2 * ∑ m ∈ Finset.range N,
      ((N : ℝ) - (m + 1)) * Real.cos ((m + 1) * (2 * Real.pi * t))) :=
    intervalIntegral.integral_nonneg zero_le_one fun t ht => mul_nonneg (hh.nonneg ht) (fejerSum_nonneg _ N)
  have hfun : (fun t => h t * ((N : ℝ) + 2 * ∑ m ∈ Finset.range N,
      ((N : ℝ) - (m + 1)) * Real.cos ((m + 1) * (2 * Real.pi * t)))) =
      fun t => (N : ℝ) * (h t * Real.cos (2 * Real.pi * ((0 : ℤ) : ℝ) * t)) +
        ∑ m ∈ Finset.range N, 2 * ((N : ℝ) - (m + 1)) *
          (h t * Real.cos (2 * Real.pi * (((m + 1 : ℕ) : ℤ) : ℝ) * t)) := by
    funext t
    simp only [mul_add, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun m _ => ?_)
    · simp only [Int.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one]; ring
    · push_cast
      ring_nf
  have hi : ∀ m ∈ Finset.range N, IntervalIntegrable (fun t => 2 * ((N : ℝ) - (m + 1)) *
      (h t * Real.cos (2 * Real.pi * (((m + 1 : ℕ) : ℤ) : ℝ) * t))) volume 0 1 := fun m _ =>
    (hh.intervalIntegrable_mul (g := fun t => Real.cos (2 * Real.pi * (((m + 1 : ℕ) : ℤ) : ℝ) * t))
      (by fun_prop)).const_mul _
  have hsumi : IntervalIntegrable (fun t => ∑ m ∈ Finset.range N, 2 * ((N : ℝ) - (m + 1)) *
      (h t * Real.cos (2 * Real.pi * (((m + 1 : ℕ) : ℤ) : ℝ) * t))) volume 0 1 := by
    have := IntervalIntegrable.sum (Finset.range N) hi
    rwa [Finset.sum_fn] at this
  rw [hfun, intervalIntegral.integral_add ((hh.intervalIntegrable_mul (g := fun t =>
      Real.cos (2 * Real.pi * ((0 : ℤ) : ℝ) * t)) (by fun_prop)).const_mul _) hsumi,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hi] at hint
  simp_rw [intervalIntegral.integral_const_mul] at hint
  have e : (N : ℝ) * profileCoeff h 0 +
      2 * ∑ m ∈ Finset.range N, ((N : ℝ) - (m + 1)) * profileCoeff h ((m + 1 : ℕ) : ℤ) =
      (N : ℝ) * (∫ t in (0 : ℝ)..1, h t * Real.cos (2 * Real.pi * ((0 : ℤ) : ℝ) * t)) +
        ∑ m ∈ Finset.range N, 2 * ((N : ℝ) - (m + 1)) *
          ∫ t in (0 : ℝ)..1, h t * Real.cos (2 * Real.pi * (((m + 1 : ℕ) : ℤ) : ℝ) * t) := by
    rw [Finset.mul_sum]
    simp only [profileCoeff]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [e]
  exact hint

/-- **Bounded conductance sums**: `Σ_{n ≤ K} a_n ≤ ĥ(0)`. -/
theorem sum_range_jumpConductance_le (K : ℕ) :
    ∑ m ∈ Finset.range K, jumpConductance h (m + 1) ≤ profileCoeff h 0 := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simpa using hh.profileCoeff_zero_nonneg
  have h2 := hh.fejer_coeff_nonneg (2 * K)
  have hsub : ∑ m ∈ Finset.range K, (K : ℝ) * jumpConductance h (m + 1) ≤
      ∑ m ∈ Finset.range (2 * K), (((2 * K : ℕ) : ℝ) - (m + 1)) * jumpConductance h (m + 1) := by
    calc ∑ m ∈ Finset.range K, (K : ℝ) * jumpConductance h (m + 1)
        ≤ ∑ m ∈ Finset.range K, (((2 * K : ℕ) : ℝ) - (m + 1)) * jumpConductance h (m + 1) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm' := Finset.mem_range.1 hm
          refine mul_le_mul_of_nonneg_right ?_ (hh.jumpConductance_succ_nonneg m)
          have : (m : ℝ) + 1 ≤ K := by exact_mod_cast hm'
          push_cast; linarith
      _ ≤ ∑ m ∈ Finset.range (2 * K), (((2 * K : ℕ) : ℝ) - (m + 1)) * jumpConductance h (m + 1) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun m hm _ => ?_
          have hm' := Finset.mem_range.1 hm
          refine mul_nonneg ?_ (hh.jumpConductance_succ_nonneg m)
          have : (m : ℝ) + 1 ≤ 2 * K := by exact_mod_cast hm'
          push_cast; linarith
  have hsum : ∑ m ∈ Finset.range (2 * K), (((2 * K : ℕ) : ℝ) - (m + 1)) * profileCoeff h ((m + 1 : ℕ) : ℤ) =
      -∑ m ∈ Finset.range (2 * K), (((2 * K : ℕ) : ℝ) - (m + 1)) * jumpConductance h (m + 1) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by simp only [jumpConductance]; push_cast; ring
  rw [hsum] at h2
  rw [← Finset.mul_sum] at hsub
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  push_cast at h2 hsub
  have hK2 : (K : ℝ) * ∑ m ∈ Finset.range K, jumpConductance h (m + 1) ≤ K * profileCoeff h 0 := by linarith
  exact le_of_mul_le_mul_left hK2 hKpos

theorem summable_jumpConductance : Summable fun n : ℕ => jumpConductance h (n + 1) :=
  summable_of_sum_range_le hh.jumpConductance_succ_nonneg hh.sum_range_jumpConductance_le

/-! ## The Fourier expansion -/

theorem integral_mul_sin_eq_zero (n : ℤ) :
    ∫ t in (0 : ℝ)..1, h t * Real.sin (2 * Real.pi * n * t) = 0 := by
  have h1 := intervalIntegral.integral_comp_sub_left
    (fun t => h t * Real.sin (2 * Real.pi * n * t)) (1 : ℝ) (a := 0) (b := 1)
  simp only [sub_self, sub_zero] at h1
  have h2 : ∀ x : ℝ, h (1 - x) * Real.sin (2 * Real.pi * n * (1 - x)) =
      -(h x * Real.sin (2 * Real.pi * n * x)) := by
    intro x
    rw [hh.symm, show 2 * Real.pi * n * (1 - x) = (n : ℝ) * (2 * Real.pi) - 2 * Real.pi * n * x by ring,
      Real.sin_int_mul_two_pi_sub]
    ring
  simp_rw [h2, intervalIntegral.integral_neg] at h1
  linarith

/-- The profile as a continuous function on the circle `ℝ/ℤ`. -/
def profileCircle : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨AddCircle.liftIco 1 0 (fun t => (h t : ℂ)),
    AddCircle.liftIco_continuous (by simp [hh.zero, hh.one])
      (Complex.continuous_ofReal.comp_continuousOn (by simpa using hh.continuousOn))⟩

theorem profileCircle_coe {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : hh.profileCircle t = (h t : ℂ) := by
  change AddCircle.liftIco 1 0 (fun t => (h t : ℂ)) t = _
  rw [AddCircle.liftIco_coe_apply (by simpa using ht)]

omit hh in
theorem fourier_coe_eq (n : ℤ) (x : ℝ) :
    fourier (T := 1) n (x : AddCircle (1 : ℝ)) =
      (Real.cos (2 * Real.pi * n * x) : ℂ) + (Real.sin (2 * Real.pi * n * x) : ℂ) * Complex.I := by
  rw [fourier_coe_apply, Complex.ofReal_one, div_one, show (2 * Real.pi * Complex.I * n * x : ℂ) =
    ((2 * Real.pi * n * x : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
  push_cast; ring

omit hh in
theorem fourier_coe_eq_fourierMode (n : ℤ) (x : ℝ) :
    fourier (T := 1) n (x : AddCircle (1 : ℝ)) = fourierMode n x := by
  rw [fourier_coe_apply, Complex.ofReal_one, div_one, fourierMode]

theorem fourierCoeff_profileCircle (n : ℤ) : fourierCoeff hh.profileCircle n = (profileCoeff h n : ℂ) := by
  change fourierCoeff (AddCircle.liftIco 1 0 (fun t => (h t : ℂ))) n = _
  rw [fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral]
  simp only [zero_add, sub_zero, div_one, one_smul]
  have hpt : ∀ x : ℝ, fourier (T := 0 + 1 - 0) (-n) (x : AddCircle (0 + 1 - 0 : ℝ)) • (h x : ℂ) =
      ((h x * Real.cos (2 * Real.pi * n * x) : ℝ) : ℂ) -
        Complex.I * ((h x * Real.sin (2 * Real.pi * n * x) : ℝ) : ℂ) := by
    intro x
    rw [fourier_coe_apply, smul_eq_mul]
    have hT : ((0 + 1 - 0 : ℝ) : ℂ) = 1 := by push_cast; ring
    rw [hT, div_one, show (2 * (Real.pi : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * x) =
      ((-(2 * Real.pi * n * x) : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hcongr : ∫ x in (0 : ℝ)..1, fourier (T := 0 + 1 - 0) (-n) (x : AddCircle (0 + 1 - 0 : ℝ)) • (h x : ℂ) =
      ∫ x in (0 : ℝ)..1, (((h x * Real.cos (2 * Real.pi * n * x) : ℝ) : ℂ) -
        Complex.I * ((h x * Real.sin (2 * Real.pi * n * x) : ℝ) : ℂ)) :=
    intervalIntegral.integral_congr fun x _ => hpt x
  refine hcongr.trans ?_
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, hh.integral_mul_sin_eq_zero, Complex.ofReal_zero, mul_zero, sub_zero]
  · rfl
  · exact intervalIntegrable_complex_ofReal (hh.intervalIntegrable_mul
      (g := fun x => Real.cos (2 * Real.pi * n * x)) (by fun_prop))
  · exact (intervalIntegrable_complex_ofReal (hh.intervalIntegrable_mul
      (g := fun x => Real.sin (2 * Real.pi * n * x)) (by fun_prop))).const_mul _

theorem summable_fourierCoeff_profileCircle : Summable (fourierCoeff hh.profileCircle) := by
  have hn : Summable fun n : ℕ => |profileCoeff h n| := by
    rw [← summable_nat_add_iff 1]
    refine hh.summable_jumpConductance.congr fun n => ?_
    rw [jumpConductance, abs_of_neg (hh.coeff_neg (n + 1) (by omega))]
  refine Summable.of_norm ?_
  simp_rw [hh.fourierCoeff_profileCircle, Complex.norm_real, Real.norm_eq_abs]
  refine summable_int_iff_summable_nat_and_neg.2 ⟨by simpa using hn, ?_⟩
  simpa [profileCoeff_neg] using hn

/-- The pointwise Fourier series of the profile on `[0,1)`. -/
theorem hasSum_fourier_profile {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    HasSum (fun n : ℤ => (profileCoeff h n : ℂ) * fourierMode n t) (h t : ℂ) := by
  have h1 := has_pointwise_sum_fourier_series_of_summable hh.summable_fourierCoeff_profileCircle
    (t : AddCircle (1 : ℝ))
  rw [hh.profileCircle_coe ht] at h1
  refine h1.congr_fun fun n => ?_
  rw [hh.fourierCoeff_profileCircle, smul_eq_mul, fourier_coe_eq_fourierMode]

/-- The cosine series `Σ_{n ≥ 1} 2 ĥ(n) cos 2πnt = h(t) − ĥ(0)` on `[0,1)`. -/
theorem hasSum_cos_profile {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 2 * profileCoeff h ((n + 1 : ℕ) : ℤ) * Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℤ) * t))
      (h t - profileCoeff h 0) := by
  have h1 := Complex.hasSum_re (hh.hasSum_fourier_profile ht).nat_add_neg
  have h2 : HasSum (fun n : ℕ => 2 * profileCoeff h n * Real.cos (2 * Real.pi * (n : ℤ) * t))
      (h t + profileCoeff h 0) := by
    have e2 : ((h t : ℂ) + (profileCoeff h 0 : ℂ) * fourierMode 0 t).re = h t + profileCoeff h 0 := by
      simp [fourierMode_zero]
    rw [← e2]
    refine h1.congr_fun fun n => ?_
    rw [fourierMode_eq_cos_add_sin, fourierMode_eq_cos_add_sin, profileCoeff_neg]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Int.cast_neg, mul_neg, neg_mul, Real.cos_neg, Real.sin_neg]
    ring
  have h3 := (hasSum_nat_add_iff' 1).2 h2
  have e3 : h t + profileCoeff h 0 - ∑ i ∈ Finset.range 1,
      2 * profileCoeff h (i : ℤ) * Real.cos (2 * Real.pi * ((i : ℤ) : ℝ) * t) = h t - profileCoeff h 0 := by
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, Int.cast_zero, mul_zero, zero_mul,
      Real.cos_zero, mul_one]
    ring
  rw [e3] at h3
  exact h3

/-- **Capacity of the conductances**: `Σ_{n ≥ 1} a_n = ĥ(0)/2`. -/
theorem hasSum_jumpConductance : HasSum (fun n : ℕ => jumpConductance h (n + 1)) (profileCoeff h 0 / 2) := by
  have h1 := (hh.hasSum_cos_profile (t := 0) ⟨le_rfl, one_pos⟩).mul_left (-1 / 2)
  rw [hh.zero, show -1 / 2 * (0 - profileCoeff h 0) = profileCoeff h 0 / 2 by ring] at h1
  refine h1.congr_fun fun n => ?_
  simp only [jumpConductance, mul_zero, Real.cos_zero, mul_one]
  ring

/-- **(1) The conductance expansion** `h(t) = 2Σ_{n ≥ 1} a_n (1 − cos 2πnt)` on `[0,1]`. -/
theorem hasSum_profile {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 2 * jumpConductance h (n + 1) * (1 - Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℤ) * t)))
      (h t) := by
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst h1
    rw [hh.one]
    refine hasSum_zero.congr_fun fun n => ?_
    rw [show 2 * Real.pi * (((n + 1 : ℕ) : ℤ) : ℝ) * 1 = (((n + 1 : ℕ) : ℤ) : ℝ) * (2 * Real.pi) by ring,
      Real.cos_int_mul_two_pi, sub_self, mul_zero]
  have hc := hh.hasSum_cos_profile ⟨ht.1, h1⟩
  have ha := hh.hasSum_jumpConductance.mul_left 2
  have hs := ha.add hc
  rw [show 2 * (profileCoeff h 0 / 2) + (h t - profileCoeff h 0) = h t by ring] at hs
  refine hs.congr_fun fun n => ?_
  simp only [jumpConductance]
  ring

theorem jumpConductance_term_le (n : ℕ) (t : ℝ) :
    ‖2 * jumpConductance h (n + 1) * (1 - Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℤ) * t))‖ ≤
      4 * jumpConductance h (n + 1) := by
  have ha := hh.jumpConductance_succ_nonneg n
  have hc1 := Real.neg_one_le_cos (2 * Real.pi * ((n + 1 : ℕ) : ℤ) * t)
  have hc2 := Real.cos_le_one (2 * Real.pi * ((n + 1 : ℕ) : ℤ) * t)
  rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
  nlinarith

/-- The conductance expansion converges uniformly on `[0,1]`. -/
theorem tendstoUniformlyOn_profile :
    TendstoUniformlyOn (fun N t => ∑ n ∈ Finset.range N,
        2 * jumpConductance h (n + 1) * (1 - Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℤ) * t))) h atTop (Icc 0 1) := by
  refine (tendstoUniformlyOn_tsum_nat (hh.summable_jumpConductance.mul_left 4)
    fun n t _ => hh.jumpConductance_term_le n t).congr_right fun t ht => (hh.hasSum_profile ht).tsum_eq

/-! ## Unit capacity -/

theorem integrableOn_action (m : ℤ) :
    IntegrableOn (fun t => (1 - Real.cos (2 * Real.pi * m * t)) / h t) (Ioo 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 (hh.action m)

omit hh in
theorem profileAction_eq (m : ℤ) :
    profileAction h m = ∫ t in Ioo (0 : ℝ) 1, (1 - Real.cos (2 * Real.pi * m * t)) / h t := by
  rw [profileAction, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

theorem action_integrand_nonneg (m : ℤ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ (1 - Real.cos (2 * Real.pi * m * t)) / h t :=
  div_nonneg (sub_nonneg.2 (Real.cos_le_one _)) (hh.nonneg ht)

theorem profileAction_nonneg (m : ℤ) : 0 ≤ profileAction h m :=
  intervalIntegral.integral_nonneg zero_le_one fun _ ht => hh.action_integrand_nonneg m ht

theorem capacityPartial_term_nonneg (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ 2 * jumpConductance h (n + 1) * ((1 - Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℤ) * t)) / h t) :=
  mul_nonneg (mul_nonneg zero_le_two (hh.jumpConductance_succ_nonneg n)) (hh.action_integrand_nonneg _ ht)

/-- `Σ_{n ≥ 1} 2a_n(1 − cos 2πnt)/h(t) = 1` on `(0,1)`. -/
theorem hasSum_capacity_quotient {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 2 * jumpConductance h (n + 1) *
      ((1 - Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℤ) * t)) / h t)) 1 := by
  have h1 := (hh.hasSum_profile (Ioo_subset_Icc_self ht)).div_const (h t)
  rw [div_self (hh.pos t ht).ne'] at h1
  exact h1.congr_fun fun n => by ring

theorem capacityPartial_le_one (N : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : capacityPartial h N t ≤ 1 :=
  sum_le_hasSum _ (fun n _ => hh.capacityPartial_term_nonneg n (Ioo_subset_Icc_self ht))
    (hh.hasSum_capacity_quotient ht)

theorem capacityPartial_nonneg (N : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ capacityPartial h N t :=
  Finset.sum_nonneg fun n _ => hh.capacityPartial_term_nonneg n ht

theorem integrableOn_capacityPartial (N : ℕ) : IntegrableOn (capacityPartial h N) (Ioo 0 1) :=
  integrable_finsetSum _ fun _ _ => (hh.integrableOn_action _).const_mul _

theorem integral_capacityPartial (N : ℕ) :
    ∫ t in Ioo (0 : ℝ) 1, capacityPartial h N t =
      ∑ n ∈ Finset.range N, 2 * jumpConductance h (n + 1) * profileAction h ((n + 1 : ℕ) : ℤ) := by
  unfold capacityPartial
  rw [integral_finsetSum _ fun _ _ => (hh.integrableOn_action _).const_mul _]
  exact Finset.sum_congr rfl fun n _ => by rw [integral_const_mul, profileAction_eq]

/-- **(3) Unit capacity**: `2 Σ_{n ≥ 1} a_n Φ_n = 1`. -/
theorem hasSum_unitCapacity :
    HasSum (fun n : ℕ => 2 * jumpConductance h (n + 1) * profileAction h ((n + 1 : ℕ) : ℤ)) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg fun n =>
    mul_nonneg (mul_nonneg zero_le_two (hh.jumpConductance_succ_nonneg n)) (hh.profileAction_nonneg _)]
  have hlim := integral_tendsto_of_tendsto_of_monotone (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (f := fun N t => capacityPartial h N t) (F := fun _ => (1 : ℝ)) (fun N => hh.integrableOn_capacityPartial N)
    (integrable_const _)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht => monotone_nat_of_le_succ fun N => by
      simp only [capacityPartial, Finset.sum_range_succ]
      linarith [hh.capacityPartial_term_nonneg N (Ioo_subset_Icc_self ht)]))
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht =>
      (hh.hasSum_capacity_quotient ht).tendsto_sum_nat))
  rw [setIntegral_const, Real.volume_real_Ioo_of_le zero_le_one, sub_zero, one_smul] at hlim
  exact hlim.congr fun N => hh.integral_capacityPartial N

theorem summable_conductance_action :
    Summable fun n : ℕ => jumpConductance h (n + 1) * profileAction h ((n + 1 : ℕ) : ℤ) :=
  (hh.hasSum_unitCapacity.summable.mul_left (1 / 2)).congr fun n => by ring

/-! ## The point-source Green law -/

theorem intervalIntegrable_bracket (m j : ℤ) :
    IntervalIntegrable (fun t => -2 * Real.cos (2 * Real.pi * m * t) *
      (1 - Real.cos (2 * Real.pi * j * t)) / h t) volume 0 1 := by
  have h1 := ((hh.action m).const_mul 2).sub (hh.action (m - j)) |>.sub (hh.action (m + j))
  refine h1.congr fun t _ => ?_
  rw [← cos_bracket m j t]
  ring

/-- The Laplacian bracket of the actions as one integral. -/
theorem action_bracket (m j : ℤ) :
    2 * profileAction h m - profileAction h (m - j) - profileAction h (m + j) =
      ∫ t in (0 : ℝ)..1, -2 * Real.cos (2 * Real.pi * m * t) * (1 - Real.cos (2 * Real.pi * j * t)) / h t := by
  rw [profileAction, profileAction, profileAction, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub ((hh.action m).const_mul 2) (hh.action (m - j)),
    ← intervalIntegral.integral_sub (((hh.action m).const_mul 2).sub (hh.action (m - j))) (hh.action (m + j))]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [← cos_bracket m j t]
  ring

theorem abs_action_bracket_le (m j : ℤ) :
    |2 * profileAction h m - profileAction h (m - j) - profileAction h (m + j)| ≤ 2 * profileAction h j := by
  rw [hh.action_bracket, profileAction, ← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans
    (intervalIntegral.integral_mono_on zero_le_one (hh.intervalIntegrable_bracket m j).abs
      ((hh.action j).const_mul 2) fun t ht => ?_)
  have hc := Real.abs_cos_le_one (2 * Real.pi * m * t)
  have hj := hh.action_integrand_nonneg j ht
  rw [show -2 * Real.cos (2 * Real.pi * m * t) * (1 - Real.cos (2 * Real.pi * j * t)) / h t =
    -2 * Real.cos (2 * Real.pi * m * t) * ((1 - Real.cos (2 * Real.pi * j * t)) / h t) by ring,
    abs_mul, abs_mul, abs_of_nonneg hj, abs_neg, abs_two]
  nlinarith [abs_nonneg (Real.cos (2 * Real.pi * m * t))]

theorem summable_green (m : ℤ) :
    Summable fun n : ℕ => jumpConductance h (n + 1) *
      (2 * profileAction h m - profileAction h (m - (n + 1 : ℕ)) - profileAction h (m + (n + 1 : ℕ))) := by
  refine Summable.of_norm_bounded (hh.summable_conductance_action.mul_left 2) fun n => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hh.jumpConductance_succ_nonneg n)]
  have := hh.abs_action_bracket_le m ((n + 1 : ℕ) : ℤ)
  nlinarith [hh.jumpConductance_succ_nonneg n]

/-- **(4) The point-source Green law** `(L_aΦ)_m = −1_{m=0}`, absolutely convergent. -/
theorem hasSum_green (m : ℤ) :
    HasSum (fun n : ℕ => jumpConductance h (n + 1) *
      (2 * profileAction h m - profileAction h (m - (n + 1 : ℕ)) - profileAction h (m + (n + 1 : ℕ))))
      (-(if m = 0 then 1 else 0)) := by
  rw [(hh.summable_green m).hasSum_iff_tendsto_nat]
  have hlim := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (F := fun N t => -Real.cos (2 * Real.pi * m * t) * capacityPartial h N t)
    (f := fun t => -Real.cos (2 * Real.pi * m * t)) (fun _ => (1 : ℝ))
    (fun N => ((by fun_prop : Continuous fun t : ℝ => -Real.cos (2 * Real.pi * m * t)).aestronglyMeasurable).mul
      (hh.integrableOn_capacityPartial N).aestronglyMeasurable) (integrable_const _)
    (fun N => (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht => by
      rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hh.capacityPartial_nonneg N (Ioo_subset_Icc_self ht))]
      exact mul_le_one₀ (Real.abs_cos_le_one _) (hh.capacityPartial_nonneg N (Ioo_subset_Icc_self ht))
        (hh.capacityPartial_le_one N ht)))
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht => by
      have := ((hh.hasSum_capacity_quotient ht).tendsto_sum_nat).const_mul (-Real.cos (2 * Real.pi * m * t))
      rw [mul_one] at this
      exact this))
  have hval : ∫ t in Ioo (0 : ℝ) 1, -Real.cos (2 * Real.pi * m * t) = -(if m = 0 then 1 else 0) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_neg, integral_cos_two_pi_int_mul]
  rw [hval] at hlim
  refine hlim.congr fun N => ?_
  have hb : ∀ j : ℤ, IntegrableOn (fun t => -2 * Real.cos (2 * Real.pi * m * t) *
      (1 - Real.cos (2 * Real.pi * j * t)) / h t) (Ioo 0 1) := fun j =>
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 (hh.intervalIntegrable_bracket m j)
  have e : ∀ t, -Real.cos (2 * Real.pi * m * t) * capacityPartial h N t =
      ∑ n ∈ Finset.range N, jumpConductance h (n + 1) * (-2 * Real.cos (2 * Real.pi * m * t) *
        (1 - Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℤ) * t)) / h t) := fun t => by
    unfold capacityPartial
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [integral_congr_ae (Eventually.of_forall e), integral_finsetSum _ fun n _ => (hb _).const_mul _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, hh.action_bracket, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

/-- **The symbol of `L_a` is `h`**: `L_a e^{2πi·t} = h(t) e^{2πi·t}` for `t ∈ [0,1]`. -/
theorem jumpLaplacian_fourierMode {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (m : ℤ) :
    jumpLaplacian (jumpConductance h) (fun k => fourierMode k t) m = h t * fourierMode m t := by
  have h1 := (Complex.hasSum_ofReal.2 (hh.hasSum_profile ht)).mul_right (fourierMode m t)
  refine (h1.congr_fun fun n => ?_).tsum_eq
  beta_reduce
  have hsub : fourierMode (m - ((n + 1 : ℕ) : ℤ)) t = fourierMode m t * fourierMode (-((n + 1 : ℕ) : ℤ)) t := by
    rw [sub_eq_add_neg, fourierMode_add]
  rw [hsub, fourierMode_add, fourierMode_eq_cos_add_sin (-((n + 1 : ℕ) : ℤ)),
    fourierMode_eq_cos_add_sin ((n + 1 : ℕ) : ℤ)]
  push_cast
  simp only [mul_neg, neg_mul, Complex.cos_neg, Complex.sin_neg]
  ring

omit hh in
theorem jumpLaplacian_ofReal {a : ℕ → ℝ} {f : ℤ → ℝ} {m : ℤ} {x : ℝ}
    (hs : HasSum (fun n : ℕ => a (n + 1) * (2 * f m - f (m - (n + 1 : ℕ)) - f (m + (n + 1 : ℕ)))) x) :
    jumpLaplacian a (fun k => (f k : ℂ)) m = x := by
  refine ((Complex.hasSum_ofReal.2 hs).congr_fun fun n => ?_).tsum_eq
  push_cast
  ring

/-- **(4) in operator form**: `L_a Φ = −δ₀`. -/
theorem jumpLaplacian_profileAction (m : ℤ) :
    jumpLaplacian (jumpConductance h) (fun k => (profileAction h k : ℂ)) m = -(if m = 0 then 1 else 0) := by
  rw [jumpLaplacian_ofReal (hh.hasSum_green m)]
  split_ifs <;> simp

/-- **(5) The dipole response**: `L_a v^(n) = δ_n − δ₀`. -/
theorem jumpLaplacian_potentialVoltage (n m : ℤ) :
    jumpLaplacian (jumpConductance h) (fun k => (potentialVoltage h n k : ℂ)) m =
      (if m = n then 1 else 0) - (if m = 0 then 1 else 0) := by
  have h1 := (hh.hasSum_green m).sub (hh.hasSum_green (m - n))
  rw [jumpLaplacian_ofReal (x := -(if m = 0 then 1 else 0) - -(if m - n = 0 then 1 else 0)) ?_]
  · simp only [sub_eq_zero]
    split_ifs <;> simp
  · refine h1.congr_fun fun j => ?_
    simp only [potentialVoltage]
    rw [show m - ((j + 1 : ℕ) : ℤ) - n = m - n - ((j + 1 : ℕ) : ℤ) by ring,
      show m + ((j + 1 : ℕ) : ℤ) - n = m - n + ((j + 1 : ℕ) : ℤ) by ring]
    ring

/-! ## The grounded kernel is positive -/

theorem aemeasurable_restrict_Ioc : AEMeasurable h (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (hh.continuousOn.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc

theorem intervalIntegrable_sin_part (m n : ℤ) :
    IntervalIntegrable (fun t => (Real.sin (2 * Real.pi * m * t) * (1 - Real.cos (2 * Real.pi * n * t)) -
      (1 - Real.cos (2 * Real.pi * m * t)) * Real.sin (2 * Real.pi * n * t)) / h t) volume 0 1 := by
  refine IntervalIntegrable.mono_fun' (((hh.action m).add (hh.action n)).const_mul 2) ?_ ?_
  · rw [uIoc_of_le zero_le_one]
    exact ((Continuous.aemeasurable (by fun_prop)).div hh.aemeasurable_restrict_Ioc).aestronglyMeasurable
  · rw [uIoc_of_le zero_le_one]
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
    have hh0 := hh.nonneg (Ioc_subset_Icc_self ht)
    have h1 := abs_sin_mul_one_sub_cos_le (2 * Real.pi * m * t) (2 * Real.pi * n * t)
    have h2 := abs_sin_mul_one_sub_cos_le (2 * Real.pi * n * t) (2 * Real.pi * m * t)
    dsimp only
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hh0, ← add_div, mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hh0
    have h3 := abs_sub (Real.sin (2 * Real.pi * m * t) * (1 - Real.cos (2 * Real.pi * n * t)))
      ((1 - Real.cos (2 * Real.pi * m * t)) * Real.sin (2 * Real.pi * n * t))
    rw [mul_comm (1 - Real.cos (2 * Real.pi * m * t)) (Real.sin _)] at h3 ⊢
    linarith

theorem intervalIntegrable_grounded (m n : ℤ) :
    IntervalIntegrable (fun t => (starRingEnd ℂ) (1 - fourierMode m t) * (1 - fourierMode n t) / (h t : ℂ))
      volume 0 1 := by
  have h1 := (intervalIntegrable_complex_ofReal (((hh.action m).add (hh.action n)).sub (hh.action (m - n)))).add
    ((intervalIntegrable_complex_ofReal (hh.intervalIntegrable_sin_part m n)).const_mul Complex.I)
  refine h1.congr fun t _ => ?_
  rw [conj_one_sub_fourierMode_mul]
  push_cast
  ring

/-- **The grounded pair integral**: `∫₀¹ conj(1 − e_m)(1 − e_n)/h = Φ_m + Φ_n − Φ_{m−n}`. -/
theorem integral_grounded (m n : ℤ) :
    ∫ t in (0 : ℝ)..1, (starRingEnd ℂ) (1 - fourierMode m t) * (1 - fourierMode n t) / (h t : ℂ) =
      (groundedKernel h m n : ℂ) := by
  have hodd : ∫ t in (0 : ℝ)..1, (Real.sin (2 * Real.pi * m * t) * (1 - Real.cos (2 * Real.pi * n * t)) -
      (1 - Real.cos (2 * Real.pi * m * t)) * Real.sin (2 * Real.pi * n * t)) / h t = 0 := by
    refine integral_unit_eq_zero_of_odd fun t => ?_
    have hs : ∀ k : ℤ, Real.sin (2 * Real.pi * k * (1 - t)) = -Real.sin (2 * Real.pi * k * t) := fun k => by
      rw [show 2 * Real.pi * k * (1 - t) = (k : ℝ) * (2 * Real.pi) - 2 * Real.pi * k * t by ring,
        Real.sin_int_mul_two_pi_sub]
    have hc : ∀ k : ℤ, Real.cos (2 * Real.pi * k * (1 - t)) = Real.cos (2 * Real.pi * k * t) := fun k => by
      rw [show 2 * Real.pi * k * (1 - t) = (k : ℝ) * (2 * Real.pi) - 2 * Real.pi * k * t by ring,
        Real.cos_int_mul_two_pi_sub]
    rw [hs, hs, hc, hc, hh.symm]
    ring
  have hpt : ∀ t, (starRingEnd ℂ) (1 - fourierMode m t) * (1 - fourierMode n t) / (h t : ℂ) =
      ((((1 - Real.cos (2 * Real.pi * m * t)) / h t + (1 - Real.cos (2 * Real.pi * n * t)) / h t) -
        (1 - Real.cos (2 * Real.pi * ((m - n : ℤ) : ℝ) * t)) / h t : ℝ) : ℂ) +
      Complex.I * (((Real.sin (2 * Real.pi * m * t) * (1 - Real.cos (2 * Real.pi * n * t)) -
        (1 - Real.cos (2 * Real.pi * m * t)) * Real.sin (2 * Real.pi * n * t)) / h t : ℝ) : ℂ) := fun t => by
    rw [conj_one_sub_fourierMode_mul]
    push_cast
    ring
  rw [intervalIntegral.integral_congr fun t _ => hpt t,
    intervalIntegral.integral_add (intervalIntegrable_complex_ofReal
      (((hh.action m).add (hh.action n)).sub (hh.action (m - n))))
      ((intervalIntegrable_complex_ofReal (hh.intervalIntegrable_sin_part m n)).const_mul Complex.I),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, hodd,
    intervalIntegral.integral_sub ((hh.action m).add (hh.action n)) (hh.action (m - n)),
    intervalIntegral.integral_add (hh.action m) (hh.action n)]
  simp only [groundedKernel, profileAction, Complex.ofReal_zero, mul_zero, add_zero]

/-- **Positivity of the grounded kernel**: for finitely supported charges `c`,
`Σ c̄_m c_n K(m,n) = ∫₀¹ |Σ c_m (1 − e^{2πimt})|²/h(t) dt`. -/
theorem sum_groundedKernel_eq (S : Finset ℤ) (c : ℤ → ℂ) :
    ∑ m ∈ S, ∑ n ∈ S, (starRingEnd ℂ) (c m) * c n * (groundedKernel h m n : ℂ) =
      ((∫ t in (0 : ℝ)..1, ‖∑ m ∈ S, c m * (1 - fourierMode m t)‖ ^ 2 / h t : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_ofReal]
  have hpt : ∀ t, ((‖∑ m ∈ S, c m * (1 - fourierMode m t)‖ ^ 2 / h t : ℝ) : ℂ) =
      ∑ m ∈ S, ∑ n ∈ S, (starRingEnd ℂ) (c m) * c n *
        ((starRingEnd ℂ) (1 - fourierMode m t) * (1 - fourierMode n t) / (h t : ℂ)) := fun t => by
    push_cast
    rw [← Complex.conj_mul', map_sum, Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul]
    ring
  have hin : ∀ m ∈ S, IntervalIntegrable (fun t => ∑ n ∈ S, (starRingEnd ℂ) (c m) * c n *
      ((starRingEnd ℂ) (1 - fourierMode m t) * (1 - fourierMode n t) / (h t : ℂ))) volume 0 1 := fun m _ => by
    have := IntervalIntegrable.sum S fun n _ =>
      (hh.intervalIntegrable_grounded m n).const_mul ((starRingEnd ℂ) (c m) * c n)
    rwa [Finset.sum_fn] at this
  rw [intervalIntegral.integral_congr fun t _ => hpt t, intervalIntegral.integral_finsetSum hin]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_finsetSum fun n _ => (hh.intervalIntegrable_grounded m n).const_mul _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_const_mul, hh.integral_grounded]

theorem groundedKernel_form_nonneg (S : Finset ℤ) (c : ℤ → ℂ) :
    0 ≤ (∑ m ∈ S, ∑ n ∈ S, (starRingEnd ℂ) (c m) * c n * (groundedKernel h m n : ℂ)).re ∧
      (∑ m ∈ S, ∑ n ∈ S, (starRingEnd ℂ) (c m) * c n * (groundedKernel h m n : ℂ)).im = 0 := by
  rw [hh.sum_groundedKernel_eq, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨intervalIntegral.integral_nonneg zero_le_one fun t ht => div_nonneg (sq_nonneg _) (hh.nonneg ht), rfl⟩

end IsJumpProfile

end

end RHTower
