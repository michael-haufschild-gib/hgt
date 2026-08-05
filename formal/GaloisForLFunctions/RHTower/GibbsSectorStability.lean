import Mathlib
import GaloisForLFunctions.RHTower.GibbsClusterRepulsion

/-!
# Sector stability of the squarefree Gibbs gas

Although Lee–Yang reality fails at three primes (the parity vortex), the vortex never
crosses the imaginary axis: at **every** coupling `x > 0` the pair and triple gases have
no zero in the closed right half-plane.  The mechanism is Routh–Hurwitz plus energy
submultiplicativity: `a₂a₁ ≥ e^{−(pq+p)x} > e^{−(pqr+1)x} = a₃a₀` because
`p(q+1) ≤ pqr`.

Consequences: every zero `ζ` satisfies `‖1+ζ‖ < ‖1−ζ‖` — in the Hadamard/cross-ratio
representation of the parity observable, **every zero individually contributes
cancellation**, so parity cancellation is monotonically graded by the zero set, and the
remaining question is purely the condensation rate of zeros at the parity point.

* `quadratic_no_rhp_root`, `cubic_no_rhp_root` — self-contained Routh–Hurwitz criteria
  in the closed right half-plane;
* `gibbsDiag_pair_expand`, `gibbsDiag_triple_expand` — the coefficient bridges;
* `triple_gas_hurwitz` — the energy inequality at every coupling;
* `pair_gas_sector_stable`, `triple_gas_sector_stable` — no zero with `Re z ≥ 0`;
* `norm_one_add_lt_of_re_neg`, `triple_gas_root_grading` — the per-zero cancellation
  grading.
-/

namespace RHTower.GibbsGas

open Real

/-- **Routh–Hurwitz, degree two.**  A real quadratic with positive coefficients has no
zero in the closed right half-plane. -/
theorem quadratic_no_rhp_root (a2 a1 a0 : ℝ) (ha2 : 0 < a2) (ha1 : 0 < a1)
    (ha0 : 0 < a0) (z : ℂ) (hz : 0 ≤ z.re) :
    (a2:ℂ)*z^2 + (a1:ℂ)*z + (a0:ℂ) ≠ 0 := by
  intro hroot
  set s : ℝ := z.re with hs
  set t : ℝ := z.im with ht
  have hz' : z = (s:ℂ) + (t:ℂ) * Complex.I := by
    rw [hs, ht]
    exact (Complex.re_add_im z).symm
  rw [hz'] at hroot
  have hre : a2*(s^2 - t^2) + a1*s + a0 = 0 := by
    have h := congrArg Complex.re hroot
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, pow_two] at h
    linear_combination h
  have him : t * (2*a2*s + a1) = 0 := by
    have h := congrArg Complex.im hroot
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_im, pow_two] at h
    linear_combination h
  have hfac : 0 < 2*a2*s + a1 := by nlinarith [mul_nonneg ha2.le hz, ha1]
  have ht0 : t = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h (ne_of_gt hfac)
  rw [ht0] at hre
  nlinarith [hre, mul_nonneg (mul_nonneg ha2.le hz) hz]

/-- **Routh–Hurwitz, degree three.**  A real cubic with positive extreme coefficients,
nonnegative middle coefficients and `a₃a₀ < a₂a₁` has no zero in the closed right
half-plane: writing a root as `s + it` with `s ≥ 0`, the imaginary part forces
`a₃t² = 3a₃s² + 2a₂s + a₁`, and the real part then yields
`a₂a₁ − a₃a₀ = −(8a₃²s³ + 8a₃a₂s² + 2a₃a₁s + 2a₂²s) ≤ 0`. -/
theorem cubic_no_rhp_root (a3 a2 a1 a0 : ℝ) (ha3 : 0 < a3) (ha2 : 0 ≤ a2)
    (ha1 : 0 ≤ a1) (ha0 : 0 < a0) (hH : a3 * a0 < a2 * a1)
    (z : ℂ) (hz : 0 ≤ z.re) :
    (a3:ℂ)*z^3 + (a2:ℂ)*z^2 + (a1:ℂ)*z + (a0:ℂ) ≠ 0 := by
  intro hroot
  set s : ℝ := z.re with hs
  set t : ℝ := z.im with ht
  have hz' : z = (s:ℂ) + (t:ℂ) * Complex.I := by
    rw [hs, ht]
    exact (Complex.re_add_im z).symm
  rw [hz'] at hroot
  have hre : a3*(s^3 - 3*s*t^2) + a2*(s^2 - t^2) + a1*s + a0 = 0 := by
    have h := congrArg Complex.re hroot
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, pow_succ, pow_zero, one_mul] at h
    linear_combination h
  have him : t * (3*a3*s^2 - a3*t^2 + 2*a2*s + a1) = 0 := by
    have h := congrArg Complex.im hroot
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_im, pow_succ, pow_zero, one_mul] at h
    linear_combination h
  rcases eq_or_ne t 0 with ht0 | ht0
  · rw [ht0] at hre
    nlinarith [hre, mul_nonneg (mul_nonneg ha3.le hz) (mul_nonneg hz hz),
      mul_nonneg (mul_nonneg ha2 hz) hz, mul_nonneg ha1 hz]
  · have hquad : a3*t^2 = 3*a3*s^2 + 2*a2*s + a1 := by
      rcases mul_eq_zero.mp him with h | h
      · exact absurd h ht0
      · linarith [h]
    have hkey : a2*a1 - a3*a0
        = -(8*a3^2*s^3 + 8*a3*a2*s^2 + 2*a3*a1*s + 2*a2^2*s) := by
      linear_combination (-a3) * hre + (-(3*a3*s + a2)) * hquad
    nlinarith [hkey, mul_nonneg (mul_nonneg (mul_nonneg ha3.le ha3.le) hz)
      (mul_nonneg hz hz), mul_nonneg (mul_nonneg (mul_nonneg ha3.le ha2) hz) hz,
      mul_nonneg (mul_nonneg ha3.le ha1) hz, mul_nonneg (mul_nonneg ha2 ha2) hz]

/-- The pair gas in the coefficient basis. -/
theorem gibbsDiag_pair_expand (p q : ℕ) (hpq : p ≠ q) (x z : ℝ) :
    gibbsDiag {p, q} x z
      = Real.exp (-x)
        + (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x))) * z
        + Real.exp (-((q:ℝ)*((p:ℝ)*x))) * z^2 := by
  have hpq' : p ∉ ({q} : Finset ℕ) := by simp [hpq]
  rw [gibbsDiag_insert p {q} hpq', gibbsDiag_singleton, gibbsDiag_singleton]
  ring

/-- The triple gas in the coefficient basis. -/
theorem gibbsDiag_triple_expand (p q r : ℕ) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (x z : ℝ) :
    gibbsDiag {p, q, r} x z
      = Real.exp (-x)
        + (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) + Real.exp (-((r:ℝ)*x))) * z
        + (Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
            + Real.exp (-((r:ℝ)*((q:ℝ)*x)))) * z^2
        + Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) * z^3 := by
  have hqr' : q ∉ ({r} : Finset ℕ) := by simp [hqr]
  have hp' : p ∉ ({q, r} : Finset ℕ) := by simp [hpq, hpr]
  rw [gibbsDiag_insert p {q, r} hp', gibbsDiag_insert q {r} hqr',
    gibbsDiag_insert q {r} hqr', gibbsDiag_singleton, gibbsDiag_singleton,
    gibbsDiag_singleton, gibbsDiag_singleton]
  ring

/-- **The Hurwitz energy inequality of the triple gas, at every coupling**:
`a₃a₀ < a₂a₁` because `p(q+1) ≤ pqr` (energy submultiplicativity). -/
theorem triple_gas_hurwitz (p q r : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (x : ℝ) (hx : 0 < x) :
    Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) * Real.exp (-x)
      < (Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
          + Real.exp (-((r:ℝ)*((q:ℝ)*x))))
        * (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) + Real.exp (-((r:ℝ)*x))) := by
  have hp' : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hq' : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hr' : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hlhs : Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) * Real.exp (-x)
      = Real.exp (-(((r:ℝ)*(q:ℝ)*(p:ℝ) + 1) * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hone : Real.exp (-((q:ℝ)*((p:ℝ)*x))) * Real.exp (-((p:ℝ)*x))
      = Real.exp (-(((q:ℝ)*(p:ℝ) + (p:ℝ)) * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp_lt : Real.exp (-(((r:ℝ)*(q:ℝ)*(p:ℝ) + 1) * x))
      < Real.exp (-(((q:ℝ)*(p:ℝ) + (p:ℝ)) * x)) := by
    apply Real.exp_lt_exp.mpr
    have hqr1 : (0:ℝ) ≤ ((q:ℝ) - 2) * ((r:ℝ) - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have hA : (0:ℝ) ≤ (q:ℝ)*(r:ℝ) - (q:ℝ) - 1 := by nlinarith [hqr1, hr']
    have harith : (q:ℝ)*(p:ℝ) + (p:ℝ) < (r:ℝ)*(q:ℝ)*(p:ℝ) + 1 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (p:ℝ)) hA]
    nlinarith [harith, hx]
  have hpos1 : 0 < Real.exp (-((r:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((q:ℝ)*x))) := by
    positivity
  have hpos2 : 0 < Real.exp (-((q:ℝ)*x)) + Real.exp (-((r:ℝ)*x)) := by positivity
  have hpos3 : 0 < Real.exp (-((q:ℝ)*((p:ℝ)*x))) := Real.exp_pos _
  have hpos4 : 0 < Real.exp (-((p:ℝ)*x)) := Real.exp_pos _
  nlinarith [hlhs, hone, hexp_lt, hpos1, hpos2, hpos3, hpos4,
    mul_pos hpos1 hpos4, mul_pos hpos3 hpos2, mul_pos hpos1 hpos2]

/-- **Sector stability of the pair gas**: no zero in the closed right half-plane, at any
coupling. -/
theorem pair_gas_sector_stable (p q : ℕ) (x : ℝ) (z : ℂ) (hz : 0 ≤ z.re) :
    (Real.exp (-((q:ℝ)*((p:ℝ)*x))) : ℂ) * z^2
      + ((Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) : ℝ) : ℂ) * z
      + (Real.exp (-x) : ℂ) ≠ 0 :=
  quadratic_no_rhp_root _ _ _ (Real.exp_pos _)
    (by positivity) (Real.exp_pos _) z hz

/-- **Sector stability of the triple gas at every coupling**: although Lee–Yang reality
fails (the parity vortex), the vortex never crosses the imaginary axis. -/
theorem triple_gas_sector_stable (p q r : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (x : ℝ) (hx : 0 < x) (z : ℂ) (hz : 0 ≤ z.re) :
    (Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) : ℂ) * z^3
      + ((Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
          + Real.exp (-((r:ℝ)*((q:ℝ)*x))) : ℝ) : ℂ) * z^2
      + ((Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x))
          + Real.exp (-((r:ℝ)*x)) : ℝ) : ℂ) * z
      + (Real.exp (-x) : ℂ) ≠ 0 :=
  cubic_no_rhp_root _ _ _ _ (Real.exp_pos _) (by positivity) (by positivity)
    (Real.exp_pos _) (triple_gas_hurwitz p q r hp hq hr x hx) z hz

/-- Zeros in the open left half-plane contribute strict cancellation at the parity
point: `‖1+ζ‖ < ‖1−ζ‖`. -/
theorem norm_one_add_lt_of_re_neg (ζ : ℂ) (hζ : ζ.re < 0) :
    ‖1 + ζ‖ < ‖1 - ζ‖ := by
  have h1 : Complex.normSq (1 + ζ) < Complex.normSq (1 - ζ) := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    nlinarith [hζ]
  have h2 : ‖1 + ζ‖^2 < ‖1 - ζ‖^2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    exact h1
  have h3 : (0:ℝ) ≤ ‖1 - ζ‖ := norm_nonneg _
  nlinarith [h2, h3, norm_nonneg (1 + ζ)]

/-- **The parity grading of the triple gas**: every zero, at every coupling, individually
contributes cancellation at the parity point. -/
theorem triple_gas_root_grading (p q r : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (x : ℝ) (hx : 0 < x) (ζ : ℂ)
    (hroot : (Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) : ℂ) * ζ^3
      + ((Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
          + Real.exp (-((r:ℝ)*((q:ℝ)*x))) : ℝ) : ℂ) * ζ^2
      + ((Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x))
          + Real.exp (-((r:ℝ)*x)) : ℝ) : ℂ) * ζ
      + (Real.exp (-x) : ℂ) = 0) :
    ‖1 + ζ‖ < ‖1 - ζ‖ := by
  have hre : ζ.re < 0 := by
    by_contra hcon
    rw [not_lt] at hcon
    exact triple_gas_sector_stable p q r hp hq hr x hx ζ hcon hroot
  exact norm_one_add_lt_of_re_neg ζ hre

end RHTower.GibbsGas
