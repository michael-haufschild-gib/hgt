import Mathlib
import GaloisForLFunctions.HTGeometry.DerivationIterateLeibniz

/-!
# The Taylor morphism of a differential ring

For a differential ring containing the rationals, the exponential generating series of the jet
sequence of an element,

```text
τ a = Σ_n (δ^n a / n!) T^n,
```

is an injective ring homomorphism into the formal power series ring which turns the derivation into
formal differentiation.  It is the algebraic form of "expand a function in its Taylor series at the
origin": the jets of an element *are* a formal arc, and a polynomial relation among elements holds
exactly when the corresponding relation among their arcs holds.

The two structural consequences used later are that the arc of a polynomial expression is that
polynomial evaluated on the arcs, and that the elements killed by `δ^n` are exactly those whose arc
is a polynomial of degree below `n`.
-/

open scoped Differential
open PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] [Differential R]

/-! ### Iterated derivatives -/

/-- The `n`-th derivative of an element of a differential ring. -/
def diffIterate (n : ℕ) (a : R) : R := (fun x : R => x′)^[n] a

@[simp] theorem diffIterate_zero (a : R) : diffIterate 0 a = a := rfl

theorem diffIterate_succ (n : ℕ) (a : R) : diffIterate (n + 1) a = diffIterate n a′ :=
  Function.iterate_succ_apply _ n a

theorem diffIterate_succ' (n : ℕ) (a : R) : diffIterate (n + 1) a = (diffIterate n a)′ :=
  Function.iterate_succ_apply' _ n a

@[simp] theorem diffIterate_zero_elt (n : ℕ) : diffIterate n (0 : R) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [diffIterate_succ', ih, map_zero]

theorem diffIterate_add (n : ℕ) (a b : R) :
    diffIterate n (a + b) = diffIterate n a + diffIterate n b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [diffIterate_succ', ih, map_add, diffIterate_succ', diffIterate_succ']

theorem diffIterate_neg (n : ℕ) (a : R) : diffIterate n (-a) = -diffIterate n a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [diffIterate_succ', ih, map_neg, diffIterate_succ']

theorem diffIterate_sub (n : ℕ) (a b : R) :
    diffIterate n (a - b) = diffIterate n a - diffIterate n b := by
  rw [sub_eq_add_neg, diffIterate_add, diffIterate_neg, sub_eq_add_neg]

/-- The iterated Leibniz rule, in jet notation. -/
theorem diffIterate_mul (n : ℕ) (a b : R) :
    diffIterate n (a * b) =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) • (diffIterate k a * diffIterate (n - k) b) :=
  derivation_iterate_mul (Differential.deriv) a b n

theorem diffIterate_of_deriv_eq_zero {a : R} (ha : a′ = 0) {n : ℕ} (hn : 0 < n) :
    diffIterate n a = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [diffIterate_succ, ha, diffIterate_zero_elt]

/-- Once a jet vanishes every later jet vanishes. -/
theorem diffIterate_eq_zero_of_le {a : R} {n : ℕ} (h : diffIterate n a = 0) {m : ℕ} (hm : n ≤ m) :
    diffIterate m a = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [show n + (k + 1) = (n + k) + 1 by ring, diffIterate_succ',
        ih (Nat.le_add_right n k), map_zero]

/-! ### The Taylor morphism -/

variable [Algebra ℚ R]

/-- The image of `1/n!` in a differential ℚ-algebra. -/
def invFactorial (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) : R :=
  algebraMap ℚ R ((n.factorial : ℚ)⁻¹)

omit [Differential R] in
@[simp] theorem invFactorial_zero : invFactorial R 0 = 1 := by
  simp [invFactorial]

omit [Differential R] in
/-- The binomial identity in the form used by the Taylor product rule. -/
theorem invFactorial_mul_invFactorial {n k : ℕ} (h : k ≤ n) :
    invFactorial R k * invFactorial R (n - k) = (Nat.choose n k : R) * invFactorial R n := by
  have hq : ((k.factorial : ℚ))⁻¹ * (((n - k).factorial : ℚ))⁻¹
      = (Nat.choose n k : ℚ) * ((n.factorial : ℚ))⁻¹ := by
    have hkey : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ)
        = (n.factorial : ℚ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) (Nat.choose_mul_factorial_mul_factorial h)
    have h1 : ((k.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (((n - k).factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h3 : ((n.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    linarith [hkey]
  unfold invFactorial
  rw [← map_mul, hq, map_mul, map_natCast]

/-- The exponential generating series of the jet sequence of an element. -/
def taylor (a : R) : PowerSeries R := PowerSeries.mk fun n => invFactorial R n * diffIterate n a

@[simp] theorem coeff_taylor (n : ℕ) (a : R) :
    PowerSeries.coeff n (taylor a) = invFactorial R n * diffIterate n a :=
  PowerSeries.coeff_mk _ _

@[simp] theorem coeff_zero_taylor (a : R) : PowerSeries.coeff 0 (taylor a) = a := by
  simp

theorem taylor_add (a b : R) : taylor (a + b) = taylor a + taylor b := by
  ext n
  simp [diffIterate_add, mul_add]

theorem taylor_zero : taylor (0 : R) = 0 := by
  ext n; simp

theorem taylor_one : taylor (1 : R) = 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      have h1 : (1 : R)′ = 0 := Derivation.map_one_eq_zero _
      rw [coeff_taylor, diffIterate_of_deriv_eq_zero h1 (Nat.succ_pos n), mul_zero,
        PowerSeries.coeff_one]
      simp

theorem taylor_mul (a b : R) : taylor (a * b) = taylor a * taylor b := by
  ext n
  rw [coeff_taylor, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (taylor a) * PowerSeries.coeff j (taylor b)) n,
    diffIterate_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [coeff_taylor, coeff_taylor, nsmul_eq_mul]
  have hcomb := invFactorial_mul_invFactorial (R := R) hk'
  linear_combination (-(diffIterate k a * diffIterate (n - k) b)) * hcomb

/-- The Taylor morphism as a ring homomorphism. -/
def taylorHom (R : Type*) [CommRing R] [Differential R] [Algebra ℚ R] : R →+* PowerSeries R where
  toFun := taylor
  map_one' := taylor_one
  map_mul' := taylor_mul
  map_zero' := taylor_zero
  map_add' := taylor_add

@[simp] theorem taylorHom_apply (a : R) : taylorHom R a = taylor a := rfl

theorem taylor_injective : Function.Injective (taylor : R → PowerSeries R) := by
  intro a b hab
  have := congrArg (PowerSeries.coeff 0) hab
  simpa using this

/-- The Taylor morphism turns the derivation into formal differentiation. -/
theorem derivative_taylor (a : R) : (d⁄dX R) (taylor a) = taylor a′ := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_taylor, coeff_taylor, diffIterate_succ]
  have hfac : ((n + 1).factorial : ℚ) = (n + 1 : ℚ) * (n.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hn1 : ((n : R) + 1) = algebraMap ℚ R ((n : ℚ) + 1) := by
    rw [map_add, map_one, map_natCast]
  have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hfne : ((n.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have : invFactorial R (n + 1) * ((n : R) + 1) = invFactorial R n := by
    unfold invFactorial
    rw [hn1, ← map_mul]
    congr 1
    rw [hfac]
    field_simp
  calc invFactorial R (n + 1) * diffIterate n a′ * ((n : R) + 1)
      = (invFactorial R (n + 1) * ((n : R) + 1)) * diffIterate n a′ := by ring
    _ = invFactorial R n * diffIterate n a′ := by rw [this]

/-- Iterating the previous identity. -/
theorem iterate_derivative_taylor (n : ℕ) (a : R) :
    (⇑(d⁄dX R))^[n] (taylor a) = taylor (diffIterate n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, derivative_taylor, ih, diffIterate_succ]

/-- The arc of a constant is constant. -/
theorem taylor_of_deriv_eq_zero {a : R} (ha : a′ = 0) : taylor a = PowerSeries.C a := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      rw [coeff_taylor, diffIterate_of_deriv_eq_zero ha (Nat.succ_pos n), mul_zero,
        PowerSeries.coeff_C]
      simp

/-- An element is killed by `δ^n` exactly when its arc has no coefficient in degree `≥ n`. -/
theorem diffIterate_eq_zero_iff_coeff_eq_zero (n : ℕ) (a : R) :
    diffIterate n a = 0 ↔ ∀ m, n ≤ m → PowerSeries.coeff m (taylor a) = 0 := by
  constructor
  · intro h m hm
    rw [coeff_taylor, diffIterate_eq_zero_of_le h hm, mul_zero]
  · intro h
    have hn := h n le_rfl
    rw [coeff_taylor] at hn
    have hfne : ((n.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hone : algebraMap ℚ R ((n.factorial : ℚ)) * invFactorial R n = 1 := by
      unfold invFactorial
      rw [← map_mul, mul_inv_cancel₀ hfne, map_one]
    calc diffIterate n a
        = (algebraMap ℚ R ((n.factorial : ℚ)) * invFactorial R n) * diffIterate n a := by
          rw [hone, one_mul]
      _ = algebraMap ℚ R ((n.factorial : ℚ)) * (invFactorial R n * diffIterate n a) := by ring
      _ = 0 := by rw [hn, mul_zero]

end

end GaloisForLFunctions.HTGeometry
