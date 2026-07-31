import Mathlib

/-!
# Polynomial growth of the seminorms of a modulated weight

Modulating a fixed smooth compactly supported weight `φ₀` by `cos (x t)` moves the peak of its
transform to `±x` without leaving the support of `φ₀`.  The cost is a growth of the derivative
seminorms, and that growth is only polynomial: Leibniz expands the `m`-th derivative of
`cos (x t) φ₀(t)` into `m + 1` terms whose modulation factors are bounded by `|x|^i`, and the
binomial coefficients reassemble into `(1 + |x|)^m`.

This is the estimate behind temperedness of a spectral multiplicity measure: the counting bound
turns a bound on the trace of the smoothing by `φₓ` into a bound on the number of spectral points
in a window around `x`, and a seminorm-continuous trace therefore gives a polynomially bounded
count.
-/

namespace GaloisForLFunctions.HTGeometry

open Real

/-- The modulated weight `φₓ(t) = cos (x t) φ₀(t)`. -/
noncomputable def modulatedWeight (phi : ℝ → ℝ) (x : ℝ) (t : ℝ) : ℝ :=
  Real.cos (x * t) * phi t

theorem contDiff_cos_mul (x : ℝ) : ContDiff ℝ ⊤ fun t : ℝ => Real.cos (x * t) :=
  Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)

theorem contDiff_sin_mul (x : ℝ) : ContDiff ℝ ⊤ fun t : ℝ => Real.sin (x * t) :=
  Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

theorem deriv_cos_mul (x : ℝ) :
    deriv (fun t : ℝ => Real.cos (x * t)) = fun t => -x * Real.sin (x * t) := by
  funext t
  have hid : HasDerivAt (fun y : ℝ => x * y) x t := by
    simpa using (hasDerivAt_id t).const_mul x
  have h : HasDerivAt (fun s : ℝ => Real.cos (x * s)) (-Real.sin (x * t) * x) t :=
    (Real.hasDerivAt_cos (x * t)).comp t hid
  rw [h.deriv]
  ring

theorem deriv_sin_mul (x : ℝ) :
    deriv (fun t : ℝ => Real.sin (x * t)) = fun t => x * Real.cos (x * t) := by
  funext t
  have hid : HasDerivAt (fun y : ℝ => x * y) x t := by
    simpa using (hasDerivAt_id t).const_mul x
  have h : HasDerivAt (fun s : ℝ => Real.sin (x * s)) (Real.cos (x * t) * x) t :=
    (Real.hasDerivAt_sin (x * t)).comp t hid
  rw [h.deriv]
  ring

theorem iteratedDeriv_cos_mul_succ (x : ℝ) (m : ℕ) (t : ℝ) :
    iteratedDeriv (m + 1) (fun s : ℝ => Real.cos (x * s)) t
      = -x * iteratedDeriv m (fun s : ℝ => Real.sin (x * s)) t := by
  rw [iteratedDeriv_succ', deriv_cos_mul]
  exact iteratedDeriv_const_mul (-x) ((contDiff_sin_mul x).of_le le_top).contDiffAt

theorem iteratedDeriv_sin_mul_succ (x : ℝ) (m : ℕ) (t : ℝ) :
    iteratedDeriv (m + 1) (fun s : ℝ => Real.sin (x * s)) t
      = x * iteratedDeriv m (fun s : ℝ => Real.cos (x * s)) t := by
  rw [iteratedDeriv_succ', deriv_sin_mul]
  exact iteratedDeriv_const_mul x ((contDiff_cos_mul x).of_le le_top).contDiffAt

/-- **The derivatives of a modulation are bounded by the powers of its frequency.**  Each
differentiation exchanges cosine for sine and produces one factor `x`. -/
theorem abs_iteratedDeriv_cos_sin_mul_le (x : ℝ) (m : ℕ) :
    (∀ t, |iteratedDeriv m (fun s : ℝ => Real.cos (x * s)) t| ≤ |x| ^ m)
      ∧ ∀ t, |iteratedDeriv m (fun s : ℝ => Real.sin (x * s)) t| ≤ |x| ^ m := by
  induction m with
  | zero =>
      constructor <;> intro t <;> simp [Real.abs_cos_le_one, Real.abs_sin_le_one]
  | succ n ih =>
      refine ⟨fun t => ?_, fun t => ?_⟩
      · rw [iteratedDeriv_cos_mul_succ, abs_mul, abs_neg, pow_succ']
        exact mul_le_mul_of_nonneg_left (ih.2 t) (abs_nonneg x)
      · rw [iteratedDeriv_sin_mul_succ, abs_mul, pow_succ']
        exact mul_le_mul_of_nonneg_left (ih.1 t) (abs_nonneg x)

/-- **The modulation seminorm bound.**  If every derivative of `φ₀` up to order `m` is bounded by
`B`, then the `m`-th derivative of the modulated weight `cos (x t) φ₀(t)` is bounded by
`(1 + |x|)^m B`.  Leibniz plus the binomial theorem. -/
theorem abs_iteratedDeriv_modulatedWeight_le {phi : ℝ → ℝ} (hphi : ContDiff ℝ ⊤ phi)
    {B : ℝ} (m : ℕ) (hbd : ∀ j ≤ m, ∀ t, |iteratedDeriv j phi t| ≤ B) (x t : ℝ) :
    |iteratedDeriv m (modulatedWeight phi x) t| ≤ (1 + |x|) ^ m * B := by
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hbd 0 (Nat.zero_le m) t)
  have hfun : modulatedWeight phi x = (fun s : ℝ => Real.cos (x * s)) * phi := rfl
  rw [hfun, iteratedDeriv_mul ((contDiff_cos_mul x).of_le le_top).contDiffAt
    (hphi.of_le le_top).contDiffAt]
  have hterm : ∀ i ∈ Finset.range (m + 1),
      |(m.choose i : ℝ) * iteratedDeriv i (fun s : ℝ => Real.cos (x * s)) t
        * iteratedDeriv (m - i) phi t| ≤ (m.choose i : ℝ) * |x| ^ i * B := by
    intro i hi
    have hle : (m - i) ≤ m := Nat.sub_le m i
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m.choose i : ℝ))]
    refine mul_le_mul (mul_le_mul_of_nonneg_left ((abs_iteratedDeriv_cos_sin_mul_le x i).1 t)
      (by positivity)) (hbd (m - i) hle t) (abs_nonneg _) (by positivity)
  calc |∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)
          * iteratedDeriv i (fun s : ℝ => Real.cos (x * s)) t * iteratedDeriv (m - i) phi t|
      ≤ ∑ i ∈ Finset.range (m + 1), |(m.choose i : ℝ)
          * iteratedDeriv i (fun s : ℝ => Real.cos (x * s)) t * iteratedDeriv (m - i) phi t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * |x| ^ i * B :=
        Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * |x| ^ i) * B := by
        rw [Finset.sum_mul]
    _ = (1 + |x|) ^ m * B := by
        congr 1
        rw [add_pow]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [one_pow, one_mul]
        ring

end GaloisForLFunctions.HTGeometry
