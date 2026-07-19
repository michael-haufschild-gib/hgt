import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The Liouville–Green amplitude invariant

An oscillatory solution of `u'' = −S²u` has no limit, but its *amplitude* does: the envelope of
the oscillation is governed by `S` alone.  The mechanism is an exact algebraic cancellation.
Form the energy

```text
E = S·u² + u'²/S.
```

Differentiating, the two cross terms `2S·u·u'` and `−2S·u·u'` produced by the equation cancel
identically, leaving

```text
E' = S'·(u² − u'²/S²),
```

with no oscillatory contribution at all: the derivative of the energy is proportional to `S'`,
so a slowly varying `S` makes `E` slowly varying, no matter how fast `u` oscillates.  Since the
bracket is bounded in absolute value by `E/S`, this gives the differential inequality

```text
|E'| ≤ (|S'|/S)·E,
```

whose integrated form is the Liouville–Green amplitude law: `E` is trapped between two constants
depending only on the total variation of `log S`, and therefore

```text
u² ≤ E/S,
```

the envelope `1/S` of WKB theory.  Writing `S = √Q` for the equation `u'' + Qu = 0` recovers the
classical `Q^{-1/2}` amplitude; the formulation here in terms of `S` avoids square roots and keeps
every step algebraic.
-/

namespace GaloisForLFunctions

/-- The Liouville–Green energy of a solution of `u'' = −S²u`, with `v` its derivative. -/
noncomputable def lgEnergy (S u v : ℝ → ℝ) (x : ℝ) : ℝ := S x * u x ^ 2 + v x ^ 2 / S x

theorem lgEnergy_nonneg {S u v : ℝ → ℝ} {x : ℝ} (hS : 0 < S x) : 0 ≤ lgEnergy S u v x := by
  rw [lgEnergy]
  have h1 : 0 ≤ S x * u x ^ 2 := mul_nonneg hS.le (sq_nonneg _)
  have h2 : 0 ≤ v x ^ 2 / S x := div_nonneg (sq_nonneg _) hS.le
  linarith

/-- **The oscillatory cross terms cancel exactly.**  The derivative of the Liouville–Green energy
is proportional to `S'`: it contains no term of size `S`, which is why a slowly varying `S`
controls the amplitude of an arbitrarily fast oscillation. -/
theorem hasDerivAt_lgEnergy {S u v : ℝ → ℝ} {S' : ℝ} {x : ℝ}
    (hS : HasDerivAt S S' x) (hSne : S x ≠ 0)
    (hu : HasDerivAt u (v x) x)
    (hv : HasDerivAt v (-(S x ^ 2) * u x) x) :
    HasDerivAt (lgEnergy S u v) (S' * (u x ^ 2 - v x ^ 2 / S x ^ 2)) x := by
  have hu2 : HasDerivAt (fun y => u y ^ 2) (2 * u x ^ 1 * v x) x := hu.pow 2
  have hv2 : HasDerivAt (fun y => v y ^ 2) (2 * v x ^ 1 * (-(S x ^ 2) * u x)) x := hv.pow 2
  have h1 : HasDerivAt (fun y => S y * u y ^ 2)
      (S' * u x ^ 2 + S x * (2 * u x ^ 1 * v x)) x := hS.mul hu2
  have h2 : HasDerivAt (fun y => v y ^ 2 / S y)
      ((2 * v x ^ 1 * (-(S x ^ 2) * u x) * S x - v x ^ 2 * S') / S x ^ 2) x :=
    hv2.div hS hSne
  have key : S' * (u x ^ 2 - v x ^ 2 / S x ^ 2)
      = S' * u x ^ 2 + S x * (2 * u x ^ 1 * v x)
        + (2 * v x ^ 1 * (-(S x ^ 2) * u x) * S x - v x ^ 2 * S') / S x ^ 2 := by
    field_simp
    ring
  rw [show lgEnergy S u v = fun y => S y * u y ^ 2 + v y ^ 2 / S y from rfl, key]
  exact HasDerivAt.add h1 h2

/-- The energy dominates each of its two nonnegative parts. -/
theorem mul_sq_le_lgEnergy {S u v : ℝ → ℝ} {x : ℝ} (hS : 0 < S x) :
    S x * u x ^ 2 ≤ lgEnergy S u v x := by
  rw [lgEnergy]
  have : 0 ≤ v x ^ 2 / S x := div_nonneg (sq_nonneg _) hS.le
  linarith

/-- **The amplitude bound.**  The solution is bounded by the Liouville–Green envelope `1/S`. -/
theorem sq_le_lgEnergy_div {S u v : ℝ → ℝ} {x : ℝ} (hS : 0 < S x) :
    u x ^ 2 ≤ lgEnergy S u v x / S x := by
  rw [le_div_iff₀ hS, mul_comm]
  exact mul_sq_le_lgEnergy hS

/-- **The Liouville–Green differential inequality.**  The relative rate of change of the energy is
at most the relative rate of change of `S`, independently of the oscillation. -/
theorem abs_deriv_lgEnergy_le {S u v : ℝ → ℝ} {S' : ℝ} {x : ℝ} (hS : 0 < S x) :
    |S' * (u x ^ 2 - v x ^ 2 / S x ^ 2)| ≤ |S'| / S x * lgEnergy S u v x := by
  have hbracket : |u x ^ 2 - v x ^ 2 / S x ^ 2| ≤ lgEnergy S u v x / S x := by
    have h1 : 0 ≤ u x ^ 2 := sq_nonneg _
    have h2 : 0 ≤ v x ^ 2 / S x ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hE : lgEnergy S u v x / S x = u x ^ 2 + v x ^ 2 / S x ^ 2 := by
      rw [lgEnergy]
      field_simp
    rw [hE, abs_le]
    constructor <;> linarith
  calc |S' * (u x ^ 2 - v x ^ 2 / S x ^ 2)|
      = |S'| * |u x ^ 2 - v x ^ 2 / S x ^ 2| := abs_mul _ _
    _ ≤ |S'| * (lgEnergy S u v x / S x) := by
        exact mul_le_mul_of_nonneg_left hbracket (abs_nonneg _)
    _ = |S'| / S x * lgEnergy S u v x := by ring

/-- **Exact conservation for a constant coefficient.**  When `S` is constant the energy is
conserved: this is the classical energy invariant of the harmonic oscillator, and it is the
degenerate case of the amplitude law. -/
theorem hasDerivAt_lgEnergy_const {c : ℝ} {u v : ℝ → ℝ} {x : ℝ} (hc : c ≠ 0)
    (hu : HasDerivAt u (v x) x)
    (hv : HasDerivAt v (-(c ^ 2) * u x) x) :
    HasDerivAt (lgEnergy (fun _ => c) u v) 0 x := by
  have h := hasDerivAt_lgEnergy (S := fun _ => c) (S' := 0) (hasDerivAt_const x c) hc hu hv
  simpa using h

/-! ## Exact monotone invariants

Dividing and multiplying the energy by `S` removes even the `u²`-`u'²` competition, leaving two
quantities whose derivatives have a *fixed sign* determined by `S'` alone:

```text
(E/S)' = −2S'·u'²/S³,        (E·S)' = 2S'S·u².
```

So for a monotone coefficient no integration is needed at all: when `S` increases, `u² + u'²/S²`
is nonincreasing and `S²u² + u'²` is nondecreasing.  These are exact adiabatic bounds, and the
first of them bounds `u²` by its initial value directly.
-/

/-- The Liouville–Green amplitude invariant `u² + u'²/S²`, the energy divided by `S`. -/
noncomputable def lgAmplitude (S u v : ℝ → ℝ) (x : ℝ) : ℝ := u x ^ 2 + v x ^ 2 / S x ^ 2

/-- The Liouville–Green momentum invariant `S²u² + u'²`, the energy multiplied by `S`. -/
noncomputable def lgMomentum (S u v : ℝ → ℝ) (x : ℝ) : ℝ := S x ^ 2 * u x ^ 2 + v x ^ 2

/-- **The amplitude invariant has a sign-definite derivative.**  Every oscillatory term cancels;
what remains is proportional to `−S'`. -/
theorem hasDerivAt_lgAmplitude {S u v : ℝ → ℝ} {S' : ℝ} {x : ℝ}
    (hS : HasDerivAt S S' x) (hSne : S x ≠ 0)
    (hu : HasDerivAt u (v x) x)
    (hv : HasDerivAt v (-(S x ^ 2) * u x) x) :
    HasDerivAt (lgAmplitude S u v) (-(2 * S' * v x ^ 2 / S x ^ 3)) x := by
  have hu2 : HasDerivAt (fun y => u y ^ 2) (2 * u x ^ 1 * v x) x := hu.pow 2
  have hv2 : HasDerivAt (fun y => v y ^ 2) (2 * v x ^ 1 * (-(S x ^ 2) * u x)) x := hv.pow 2
  have hS2 : HasDerivAt (fun y => S y ^ 2) (2 * S x ^ 1 * S') x := hS.pow 2
  have hS2ne : S x ^ 2 ≠ 0 := pow_ne_zero 2 hSne
  have h2 : HasDerivAt (fun y => v y ^ 2 / S y ^ 2)
      ((2 * v x ^ 1 * (-(S x ^ 2) * u x) * S x ^ 2 - v x ^ 2 * (2 * S x ^ 1 * S'))
        / (S x ^ 2) ^ 2) x := hv2.div hS2 hS2ne
  have key : -(2 * S' * v x ^ 2 / S x ^ 3)
      = 2 * u x ^ 1 * v x
        + (2 * v x ^ 1 * (-(S x ^ 2) * u x) * S x ^ 2 - v x ^ 2 * (2 * S x ^ 1 * S'))
          / (S x ^ 2) ^ 2 := by
    field_simp
    ring
  rw [show lgAmplitude S u v = fun y => u y ^ 2 + v y ^ 2 / S y ^ 2 from rfl, key]
  exact HasDerivAt.add hu2 h2

/-- **The momentum invariant has the opposite sign-definite derivative.** -/
theorem hasDerivAt_lgMomentum {S u v : ℝ → ℝ} {S' : ℝ} {x : ℝ}
    (hS : HasDerivAt S S' x)
    (hu : HasDerivAt u (v x) x)
    (hv : HasDerivAt v (-(S x ^ 2) * u x) x) :
    HasDerivAt (lgMomentum S u v) (2 * S' * S x * u x ^ 2) x := by
  have hu2 : HasDerivAt (fun y => u y ^ 2) (2 * u x ^ 1 * v x) x := hu.pow 2
  have hv2 : HasDerivAt (fun y => v y ^ 2) (2 * v x ^ 1 * (-(S x ^ 2) * u x)) x := hv.pow 2
  have hS2 : HasDerivAt (fun y => S y ^ 2) (2 * S x ^ 1 * S') x := hS.pow 2
  have h1 : HasDerivAt (fun y => S y ^ 2 * u y ^ 2)
      (2 * S x ^ 1 * S' * u x ^ 2 + S x ^ 2 * (2 * u x ^ 1 * v x)) x := hS2.mul hu2
  have key : 2 * S' * S x * u x ^ 2
      = 2 * S x ^ 1 * S' * u x ^ 2 + S x ^ 2 * (2 * u x ^ 1 * v x)
        + 2 * v x ^ 1 * (-(S x ^ 2) * u x) := by ring
  rw [show lgMomentum S u v = fun y => S y ^ 2 * u y ^ 2 + v y ^ 2 from rfl, key]
  exact HasDerivAt.add h1 hv2

/-- The amplitude invariant dominates the square of the solution. -/
theorem sq_le_lgAmplitude {S u v : ℝ → ℝ} {x : ℝ} : u x ^ 2 ≤ lgAmplitude S u v x := by
  rw [lgAmplitude]
  have : 0 ≤ v x ^ 2 / S x ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

theorem lgAmplitude_nonneg {S u v : ℝ → ℝ} {x : ℝ} : 0 ≤ lgAmplitude S u v x :=
  le_trans (sq_nonneg _) sq_le_lgAmplitude

/-- The two invariants are reciprocal in `S`: their product is the square of the energy scale. -/
theorem lgAmplitude_mul_sq_eq_lgMomentum {S u v : ℝ → ℝ} {x : ℝ} (hSne : S x ≠ 0) :
    lgAmplitude S u v x * S x ^ 2 = lgMomentum S u v x := by
  rw [lgAmplitude, lgMomentum]
  field_simp

end GaloisForLFunctions
