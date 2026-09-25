import GaloisForLFunctions.RHTower.HermiteMonomialWitness

/-!
# The shape of the problem: a signature, not a bound

Stepping back from the estimate. The hypothesis says an involution on a discrete set has **no free
orbits** — every point is fixed. That is not a size statement at all. Over a base field it is the
statement that an étale algebra is **totally real**: a finite real algebra is `ℝ^r × ℂ^s`, its
complex points pair up under conjugation, and "no free orbits" is `s = 0`.

Totally-real statements are decided by a **trace form**. The trace form of `ℝ^r × ℂ^s` has signature
`(r + s, s)`: each real factor gives a positive direction, each complex pair gives one positive and
**one negative** direction. So

  `s = 0  ⟺  the trace form is positive semidefinite`,   and   `s = the negative index`.

That is exactly the localised Hermite form of this lane, and it recasts the target. The problem is
not to bound a quantity below a threshold; it is to **compute a signature**. This module supplies the
orbit decomposition that makes the identification precise.

* A zero and its functional-equation partner contribute `w²` and its conjugate to the form, hence
  twice a real part: each orbit is a single real direction of the trace form.
* A free orbit is an **indefinite** direction: the monomial test vector anchored at the zero's own
  ordinate makes that orbit's contribution strictly negative, for every degree. Fixed orbits
  contribute squares of real numbers and are never negative.

So the free-orbit count is a lower bound for the negative index of the trace form, and the hypothesis
is its positive semidefiniteness.

The reframing also names the classically accessible shadow. For a real algebra the **sign of the
discriminant** is `(−1)^s`, so the discriminant detects the *parity* of the free-orbit count — which
is the parity law this field already holds, and which is exactly as much as a determinant can see.
The full signature, not the parity, is the problem; and signatures are computed by sign patterns of
principal minors of the very Hankel matrices whose entries are the localised power sums, each an
explicit derivative of the logarithmic derivative of the completed function.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Each orbit is one real direction of the trace form.** A zero and its partner contribute a
square and its conjugate, hence twice a real part. -/
theorem orbitTraceContribution (s : Finset ℕ) (c : ℕ → ℝ) (t : ℝ) (q : XiZeroCopy) :
    hermiteTestValue s c t q ^ (2 : ℕ)
      + hermiteTestValue s c t (xiZeroCopyLineConjEquiv q) ^ (2 : ℕ)
      = ((2 * (hermiteTestValue s c t q ^ (2 : ℕ)).re : ℝ) : ℂ) := by
  rw [hermiteTestValue_lineConj, ← map_pow, Complex.add_conj]

/-- With the monomial test vector the test value is a single power of the resolvent. -/
theorem hermiteTestValue_monomialTestVector (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    hermiteTestValue ({2 * n} : Finset ℕ) (monomialTestVector n) t q
      = spectralResolvent t q ^ (2 * n + 1) := by
  rw [hermiteTestValue, Finset.sum_singleton]
  simp [monomialTestVector]

/-- **A fixed orbit is never a negative direction.** On the critical line the resolvent is real, so
the contribution is the square of a real number. -/
theorem orbitTraceContribution_nonneg_of_real {w : ℂ} (h : w.im = 0) :
    0 ≤ (w ^ (2 : ℕ)).re := by
  rw [sq, Complex.mul_re, h]
  nlinarith [sq_nonneg w.re]

/-- **A free orbit is an indefinite direction.** At the ordinate of an off-line zero the monomial
test vector of any degree makes that orbit's contribution to the trace form strictly negative. -/
theorem orbitTraceContribution_neg_of_offLine {ρ : XiDivisorSupport} (h : (ρ : ℂ).re ≠ 1 / 2)
    (q : XiZeroCopy) (hq : q.1 = ρ) (n : ℕ) :
    (hermiteTestValue ({2 * n} : Finset ℕ) (monomialTestVector n) ((ρ : ℂ).im) q
      ^ (2 : ℕ)).re < 0 := by
  have hd : (ρ : ℂ).re - 1 / 2 ≠ 0 := sub_ne_zero.mpr h
  have hres : spectralResolvent ((ρ : ℂ).im) q
      = -(Complex.I / ((((ρ : ℂ).re - 1 / 2 : ℝ)) : ℂ)) :=
    spectralResolvent_at_own_ordinate ρ q hq
  have hpow : (spectralResolvent ((ρ : ℂ).im) q ^ (2 * n + 1)) ^ (2 : ℕ)
      = -((((ρ : ℂ).re - 1 / 2 : ℝ) : ℂ) ^ (4 * n + 2))⁻¹ := by
    rw [← pow_mul]
    rw [show (2 * n + 1) * 2 = 4 * n + 2 by ring]
    exact pow_of_imaginary (Or.inr hres) n
  rw [hermiteTestValue_monomialTestVector, hpow]
  have hreal : (-((((ρ : ℂ).re - 1 / 2 : ℝ) : ℂ) ^ (4 * n + 2))⁻¹).re
      = -(((ρ : ℂ).re - 1 / 2) ^ (4 * n + 2))⁻¹ := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_neg, Complex.ofReal_re]
  rw [hreal, neg_neg_iff_pos, inv_pos]
  have hne : ((ρ : ℂ).re - 1 / 2) ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ hd
  have hsq : (0 : ℝ) < (((ρ : ℂ).re - 1 / 2) ^ (2 * n + 1)) ^ (2 : ℕ) :=
    pow_two_pos_of_ne_zero hne
  rwa [← pow_mul, show (2 * n + 1) * 2 = 4 * n + 2 by ring] at hsq

end

end RHTower
