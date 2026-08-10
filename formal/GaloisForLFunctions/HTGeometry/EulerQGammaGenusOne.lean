import GaloisForLFunctions.HTGeometry.EulerQGammaGNS
import GaloisForLFunctions.HTGeometry.EulerQGammaFiniteProcess

/-!
# The genus-one renormalisation of the local response

Subtracting the first-activation counterterm `ℓ_{q}(s) = q(s−1) + q^{1+s}` from the logarithm of
Jackson's local response produces a factor whose unit translation is governed entirely by the
genus-one Euler unit `E₁(z) = (1−z)e^z`:

`R_q(s+1)·E₁(q) = R_q(s)·E₁(q^{1+s})·e^{−q·q^{1+s}}`.

This is the exact per-prime form of the divisor-erasure identity: the translation ratio is a
product of genus-one units and a prime-zeta exponential, and carries no divisor at all.  The
algebraic core is the corpus's unconditional `eulerQGamma_genusOne_local_exchange`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-! ## The first-activation counterterm -/

/-- **Equation (EQG.20).**  The local first-activation counterterm `ℓ_q(s) = q(s−1) + q^{1+s}`. -/
def eqgActivation (q : RealEulerNome) (s : ℂ) : ℂ :=
  (q.val : ℂ) * (s - 1) + (q.val : ℂ) ^ (1 + s)

/-- **Equation (EQG.21), local factor.**  The genus-one renormalised local response. -/
def eqgRenormLocal (q : RealEulerNome) (s : ℂ) : ℂ :=
  qGammaOn q (1 + s) * Complex.exp (-(eqgActivation q s))

theorem qcpow_succ (q : RealEulerNome) (s : ℂ) :
    (q.val : ℂ) ^ (1 + (s + 1)) = (q.val : ℂ) ^ (1 + s) * (q.val : ℂ) := by
  have hstep : (1 : ℂ) + (s + 1) = (1 + s) + 1 := by ring
  rw [hstep, Complex.cpow_add _ _ q.complex_ne_zero, Complex.cpow_one]

/-- The counterterm increment `ℓ_q(s) − ℓ_q(s+1) = −q + (1−q)q^{1+s}`. -/
theorem eqgActivation_diff (q : RealEulerNome) (s : ℂ) :
    eqgActivation q s - eqgActivation q (s + 1)
      = -(q.val : ℂ) + (1 - (q.val : ℂ)) * (q.val : ℂ) ^ (1 + s) := by
  rw [eqgActivation, eqgActivation, qcpow_succ]
  ring

/-! ## The local genus-one exchange -/

theorem ofReal_one_sub (q : RealEulerNome) : ((1 - q.val : ℝ) : ℂ) = 1 - (q.val : ℂ) := by
  push_cast
  ring

/-- **Equation (EQG.24), local form.**  The unit translation of the renormalised local response is
a genus-one unit times a prime-zeta exponential — no divisor survives. -/
theorem eqgRenormLocal_exchange (q : RealEulerNome) {s : ℂ} (hs : 1 + s ∈ qHalfPlane) :
    eqgRenormLocal q (s + 1) * eulerProcessGenusOneFactor ((q.val : ℂ))
      = eqgRenormLocal q s * eulerProcessGenusOneFactor ((q.val : ℂ) ^ (1 + s))
        * Complex.exp (-(q.val : ℂ) * (q.val : ℂ) ^ (1 + s)) := by
  set Q : ℂ := (q.val : ℂ) with hQ
  set x : ℂ := Q ^ (1 + s) with hx
  have hb : ((1 - q.val : ℝ) : ℂ) ≠ 0 := q.one_sub_complex_ne_zero
  have hbval : ((1 - q.val : ℝ) : ℂ) = 1 - Q := ofReal_one_sub q
  -- Jackson's functional equation, cross-multiplied
  have hjack : (1 - Q) * qGammaOn q (1 + s + 1) = (1 - x) * qGammaOn q (1 + s) := by
    have h := qGammaOn_shift q hs
    rw [hbval] at h
    rw [h, ← hx]
    field_simp [hbval ▸ hb]
  -- the counterterm increment
  have hincr : Complex.exp (-(eqgActivation q (s + 1)))
      = Complex.exp (-(eqgActivation q s)) * Complex.exp (-Q + (1 - Q) * x) := by
    rw [← Complex.exp_add]
    congr 1
    have hd := eqgActivation_diff q s
    rw [← hQ, ← hx] at hd
    linear_combination hd
  -- the algebraic exchange
  have hexch := eulerQGamma_genusOne_local_exchange Q x
  -- assemble
  have hstep : (1 - Q) * (eqgRenormLocal q (s + 1) * eulerProcessGenusOneFactor Q)
      = (1 - Q) * (eqgRenormLocal q s * eulerProcessGenusOneFactor x
        * Complex.exp (-Q * x)) := by
    rw [eqgRenormLocal, eqgRenormLocal, hincr]
    have hshiftArg : (1 : ℂ) + (s + 1) = 1 + s + 1 := by ring
    rw [hshiftArg]
    calc (1 - Q) * (qGammaOn q (1 + s + 1)
          * (Complex.exp (-(eqgActivation q s)) * Complex.exp (-Q + (1 - Q) * x))
          * eulerProcessGenusOneFactor Q)
        = ((1 - Q) * qGammaOn q (1 + s + 1)) * Complex.exp (-(eqgActivation q s))
            * (Complex.exp (-Q + (1 - Q) * x) * eulerProcessGenusOneFactor Q) := by ring
      _ = ((1 - x) * qGammaOn q (1 + s)) * Complex.exp (-(eqgActivation q s))
            * (Complex.exp (-Q + (1 - Q) * x) * eulerProcessGenusOneFactor Q) := by
          rw [hjack]
      _ = qGammaOn q (1 + s) * Complex.exp (-(eqgActivation q s))
            * ((1 - x) * Complex.exp (-Q + (1 - Q) * x) * eulerProcessGenusOneFactor Q) := by
          ring
      _ = qGammaOn q (1 + s) * Complex.exp (-(eqgActivation q s))
            * ((1 - Q) * eulerProcessGenusOneFactor x * Complex.exp (-Q * x)) := by
          rw [hexch]
      _ = (1 - Q) * (qGammaOn q (1 + s) * Complex.exp (-(eqgActivation q s))
            * eulerProcessGenusOneFactor x * Complex.exp (-Q * x)) := by ring
  have hbne : (1 : ℂ) - Q ≠ 0 := by
    rw [← hbval]
    exact hb
  exact mul_left_cancel₀ hbne hstep

/-- **Equation (EQG.24), finite prime form.**  Over any finite set of primes the renormalised
translation ratio is a product of genus-one units and prime-zeta exponentials. -/
theorem eqgRenormLocal_exchange_finset (σ : EulerSigma) (I : Finset Nat.Primes) {s : ℂ}
    (hs : ∀ p ∈ I, 1 + s ∈ qHalfPlane) :
    (∏ p ∈ I, eqgRenormLocal (eqgNome σ p) (s + 1)
        * eulerProcessGenusOneFactor (((eqgNome σ p).val : ℂ)))
      = ∏ p ∈ I, (eqgRenormLocal (eqgNome σ p) s
        * eulerProcessGenusOneFactor (((eqgNome σ p).val : ℂ) ^ (1 + s))
        * Complex.exp (-((eqgNome σ p).val : ℂ) * ((eqgNome σ p).val : ℂ) ^ (1 + s))) := by
  refine Finset.prod_congr rfl fun p hp => ?_
  exact eqgRenormLocal_exchange (eqgNome σ p) (hs p hp)

end

end GaloisForLFunctions.HTGeometry
