import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The block-unitary Ward decomposition

Let a normalized curve `x ↦ v x` in a Hilbert space be split by a curve of unitaries into a causal
and an anti-causal block,

```text
‖a x‖² + ‖c x‖² = 1 ,
```

with the anti-causal block vanishing at the base point, `c 0 = 0`.  Differentiating the unitarity
relation twice at `0` gives the exact Ward decomposition

```text
‖c'(0)‖² = -⟪a''(0), a(0)⟫ - ‖a'(0)‖² .
```

Both terms on the right are computed from the causal block alone, and the second is nonnegative, so
the anti-causal derivative energy is bounded by the causal curvature `-⟪a''(0), a(0)⟫`.  This is the
abstract identity behind boundary-unitary Ward estimates: the anti-causal response of a source curve
is a second-order causal quantity.

The statement is proved for a real inner product space.  A complex Hilbert space is one, via
`InnerProductSpace.complexToReal`, and its real inner product is the real part of the complex one
(`real_inner_eq_re_inner`), so this is exactly the `Re⟪·,·⟫` form of the identity.
-/

namespace HTGeometry

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem hasDerivAt_norm_sq {u u' : ℝ → F} (hu : ∀ x, HasDerivAt u (u' x) x) (x : ℝ) :
    HasDerivAt (fun y => ‖u y‖ ^ (2 : ℕ)) (2 * inner ℝ (u' x) (u x)) x := by
  have h := (hu x).inner ℝ (hu x)
  have heq : (fun t => (inner ℝ (u t) (u t) : ℝ)) = fun t => ‖u t‖ ^ (2 : ℕ) := by
    funext t
    exact real_inner_self_eq_norm_sq (u t)
  rw [heq] at h
  have hcomm : (inner ℝ (u x) (u' x) : ℝ) + inner ℝ (u' x) (u x)
      = 2 * inner ℝ (u' x) (u x) := by
    rw [real_inner_comm (u x) (u' x)]
    ring
  rwa [hcomm] at h

/-- **Block-unitary Ward decomposition.**  For a normalized curve split into two blocks whose
anti-causal part vanishes at the base point, the squared derivative of the anti-causal block is the
causal curvature minus the causal derivative energy. -/
theorem norm_sq_antiCausal_deriv_eq {a c a' c' : ℝ → F} {a'' c'' : F}
    (hunit : ∀ x : ℝ, ‖a x‖ ^ (2 : ℕ) + ‖c x‖ ^ (2 : ℕ) = 1)
    (hc0 : c 0 = 0)
    (ha : ∀ x, HasDerivAt a (a' x) x) (ha' : HasDerivAt a' a'' 0)
    (hc : ∀ x, HasDerivAt c (c' x) x) (hc' : HasDerivAt c' c'' 0) :
    ‖c' 0‖ ^ (2 : ℕ) = -(inner ℝ a'' (a 0) : ℝ) - ‖a' 0‖ ^ (2 : ℕ) := by
  -- the first derivative of the unitarity relation vanishes identically
  have hsum : ∀ x : ℝ, HasDerivAt (fun y => ‖a y‖ ^ (2 : ℕ) + ‖c y‖ ^ (2 : ℕ))
      (2 * inner ℝ (a' x) (a x) + 2 * inner ℝ (c' x) (c x)) x :=
    fun x => HasDerivAt.fun_add (hasDerivAt_norm_sq ha x) (hasDerivAt_norm_sq hc x)
  have hzero : ∀ x : ℝ,
      2 * (inner ℝ (a' x) (a x) : ℝ) + 2 * (inner ℝ (c' x) (c x) : ℝ) = 0 := by
    intro x
    have h := hsum x
    rw [funext hunit] at h
    exact h.unique (hasDerivAt_const x (1 : ℝ))
  -- the second derivative of the unitarity relation vanishes at the base point
  have hinnerA : HasDerivAt (fun t => (inner ℝ (a' t) (a t) : ℝ))
      ((inner ℝ (a' 0) (a' 0) : ℝ) + inner ℝ a'' (a 0)) 0 := ha'.inner ℝ (ha 0)
  have hinnerC : HasDerivAt (fun t => (inner ℝ (c' t) (c t) : ℝ))
      ((inner ℝ (c' 0) (c' 0) : ℝ) + inner ℝ c'' (c 0)) 0 := hc'.inner ℝ (hc 0)
  have hsecond : HasDerivAt (fun t => 2 * (inner ℝ (a' t) (a t) : ℝ)
      + 2 * (inner ℝ (c' t) (c t) : ℝ))
      (2 * ((inner ℝ (a' 0) (a' 0) : ℝ) + inner ℝ a'' (a 0))
        + 2 * ((inner ℝ (c' 0) (c' 0) : ℝ) + inner ℝ c'' (c 0))) 0 :=
    HasDerivAt.fun_add (HasDerivAt.const_mul 2 hinnerA) (HasDerivAt.const_mul 2 hinnerC)
  rw [funext hzero] at hsecond
  have hval := hsecond.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  -- the anti-causal block vanishes at the base point
  rw [hc0, inner_zero_right] at hval
  have hA : (inner ℝ (a' 0) (a' 0) : ℝ) = ‖a' 0‖ ^ (2 : ℕ) := real_inner_self_eq_norm_sq (a' 0)
  have hC : (inner ℝ (c' 0) (c' 0) : ℝ) = ‖c' 0‖ ^ (2 : ℕ) := real_inner_self_eq_norm_sq (c' 0)
  rw [hA, hC] at hval
  linarith

end Real

end HTGeometry
