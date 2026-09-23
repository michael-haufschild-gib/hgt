import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCompletedSource
import GaloisForLFunctions.RHTower.XiResolventArithmeticTarget

/-!
# The resolvent moments are shift derivatives of the Euler-ray response

Differentiating the resolvent trace in the shift lowers a power:

`d/dX Σ_q (α_q² + X)^{-(n+1)} = -(n+1)·Σ_q (α_q² + X)^{-(n+2)}`.

Iterating, every moment is a derivative of the zeroth one,

`(d/dX)^n Σ_q (α_q² + X)^{-1} = (-1)^n·n!·Σ_q (α_q² + X)^{-(n+1)}`,

and the zeroth one is the Euler-ray response of the completed zeta.  Combined with the finite
reduction of the rational hard-edge test to resolvent moments, this expresses the whole completed
divisor form of the test as a finite combination of shift derivatives of one arithmetic function.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **The shift derivative lowers a resolvent power.** -/
theorem hasDerivAt_xiResolventMoment {X : ℝ} (hX : 0 < X) (n : ℕ) :
    HasDerivAt (fun v : ℝ => xiResolventMoment n v)
      (-((n : ℂ) + 1) * xiResolventMoment (n + 1) X) X := by
  have h := hasDerivAt_xiShiftedReciprocalMoment hX n
  rw [xiShiftedReciprocalMoment_eq_xiResolventMoment hX.le (n + 1)] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hX] with v hv
  exact (xiShiftedReciprocalMoment_eq_xiResolventMoment (le_of_lt hv) n).symm

/-- Every moment is a shift derivative of the zeroth one. -/
theorem iteratedDeriv_xiResolventMoment_zero :
    ∀ (n : ℕ) {X : ℝ}, 0 < X →
      iteratedDeriv n (fun v : ℝ => xiResolventMoment 0 v) X
        = (-1 : ℂ) ^ n * ((Nat.factorial n : ℕ) : ℂ) * xiResolventMoment n X := by
  intro n
  induction n with
  | zero =>
    intro X _
    simp
  | succ n ih =>
    intro X hX
    have heq : (fun v : ℝ => iteratedDeriv n (fun w : ℝ => xiResolventMoment 0 w) v)
        =ᶠ[nhds X] fun v : ℝ => (-1 : ℂ) ^ n * ((Nat.factorial n : ℕ) : ℂ) * xiResolventMoment n v := by
      filter_upwards [Ioi_mem_nhds hX] with v hv
      exact ih hv
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hderiv : HasDerivAt (fun v : ℝ => (-1 : ℂ) ^ n * ((Nat.factorial n : ℕ) : ℂ) * xiResolventMoment n v)
        ((-1 : ℂ) ^ n * ((Nat.factorial n : ℕ) : ℂ) * (-((n : ℂ) + 1) * xiResolventMoment (n + 1) X)) X :=
      (hasDerivAt_xiResolventMoment hX n).const_mul _
    rw [hderiv.deriv]
    have hfac : ((Nat.factorial (n + 1) : ℕ) : ℂ) = ((n : ℂ) + 1) * ((Nat.factorial n : ℕ) : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hfac]
    ring

/-- **(CSHC.6) as shift derivatives.**  The completed divisor form of the rational hard-edge test is
a finite combination of shift derivatives of the Euler-ray response. -/
theorem tsum_routeUHardEdgeRationalTestSq_eq_iteratedDeriv {a : ℝ} (ha : 0 < a)
    (p : Polynomial ℝ) :
    (∑' q : XiZeroCopy, routeUHardEdgeRationalTestSq a p (xiSpectralPoint q))
      = ((a ^ (2 : ℕ) : ℝ) : ℂ)
        * ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
            (((routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ)
              * ((-1 : ℂ) ^ (k - 1) / ((Nat.factorial (k - 1) : ℕ) : ℂ)
                  * iteratedDeriv (k - 1) (fun v : ℝ => xiResolventMoment 0 v) (a ^ (2 : ℕ))) := by
  have hX : (0 : ℝ) < a ^ (2 : ℕ) := by positivity
  rw [tsum_routeUHardEdgeRationalTestSq_eq_moments a p]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [iteratedDeriv_xiResolventMoment_zero (k - 1) hX]
  have hfac : ((Nat.factorial (k - 1) : ℕ) : ℂ) ≠ 0 := by
    have : Nat.factorial (k - 1) ≠ 0 := Nat.factorial_ne_zero _
    exact_mod_cast this
  have hsign : ((-1 : ℂ) ^ (k - 1)) * ((-1 : ℂ) ^ (k - 1)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hkey : (-1 : ℂ) ^ (k - 1) / ((Nat.factorial (k - 1) : ℕ) : ℂ)
      * ((-1 : ℂ) ^ (k - 1) * ((Nat.factorial (k - 1) : ℕ) : ℂ)
          * xiResolventMoment (k - 1) (a ^ (2 : ℕ)))
      = ((-1 : ℂ) ^ (k - 1) * (-1 : ℂ) ^ (k - 1))
        * (((Nat.factorial (k - 1) : ℕ) : ℂ) / ((Nat.factorial (k - 1) : ℕ) : ℂ))
        * xiResolventMoment (k - 1) (a ^ (2 : ℕ)) := by
    field_simp
  rw [hkey, hsign, div_self hfac, one_mul, one_mul]

end RHTower

end
