import GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinDeterminantCollapse
import GaloisForLFunctions.RHTower.ArithmeticLogClockFiniteJetSaturation

/-!
# Holomorphic prime-log zero condensation for the rigged SC source

The neutral rigged-prime determinant is already known exactly on the real transverse coordinate:
it is a nonzero scalar times the product of the signed Gamma-Bockstein coefficients of the first
`m + 2` primes.  This file constructs its coefficient-faithful entire complexification and proves
a new obstruction to the surviving packet-growing scalar regularization.

For prime `p`, the complexified Bockstein is

`a_p (exp (-z log p) - exp (z log p))`.

Its real restriction is the existing signed Bockstein.  Its noncentral zero
`π i / log p` is the decisive extra datum.  Choosing the last prime in each growing packet gives
nonzero packet zeros tending to the wall origin.  Consequently, even a scalar regularizer with an
arbitrarily high central pole cannot yield locally uniform convergence to normalized centered Xi
if it remains finite at these moving noncentral zeros.

Thus a viable SC landing must introduce matching packet-dependent meromorphic singularities away
from the origin or break primewise determinant factorization through genuine cross-prime/operator
coupling.  No RH assumption or zero-location input is used.
-/

open Complex Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Entire coefficient-faithful complexification of the signed prime Gamma-Bockstein. -/
def preDivisorHolomorphicPrimeBockstein (z : ℂ) (p : Nat.Primes) : ℂ :=
  (primeActivationOccupancyFisherDensity p : ℂ) *
    (Complex.exp (-((Real.log (p : ℝ) : ℂ) * z)) -
      Complex.exp ((Real.log (p : ℝ) : ℂ) * z))

/-- The complexified signed prime Bockstein is entire. -/
theorem differentiable_preDivisorHolomorphicPrimeBockstein (p : Nat.Primes) :
    Differentiable ℂ (fun z => preDivisorHolomorphicPrimeBockstein z p) := by
  unfold preDivisorHolomorphicPrimeBockstein
  fun_prop

/-- Coefficient faithfulness: the entire complexification restricts to the exact corpus
Gamma-Bockstein on the real transverse line. -/
theorem preDivisorHolomorphicPrimeBockstein_ofReal
    (t : ℝ) (p : Nat.Primes) :
    preDivisorHolomorphicPrimeBockstein (t : ℂ) p =
      (primeGammaCofinalBocksteinCoefficient t p : ℂ) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [primeGammaCofinalBocksteinCoefficient,
    primeActivationOccupancyFisherTwist,
    primeActivationOccupancyFisherTwist,
    Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0]
  simp only [preDivisorHolomorphicPrimeBockstein, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
  rw [show -((Real.log (p : ℝ) : ℂ) * (t : ℂ)) =
      (Real.log (p : ℝ) : ℂ) * -(t : ℂ) by ring]
  ring

/-- Last ordinary prime of the packet indexed by `Fin (m + 2)`. -/
def preDivisorRiggedPrimeHolomorphicTerminalPrime (m : ℕ) : Nat.Primes :=
  nthPrimePoint (m + 1)

/-- First positive noncentral zero rate of the terminal signed Bockstein. -/
def preDivisorRiggedPrimeHolomorphicClockRate (m : ℕ) : ℝ :=
  Real.pi /
    Real.log ((preDivisorRiggedPrimeHolomorphicTerminalPrime m : Nat.Primes) : ℝ)

/-- First positive imaginary noncentral zero of the terminal signed Bockstein. -/
def preDivisorRiggedPrimeHolomorphicClockPoint (m : ℕ) : ℂ :=
  (preDivisorRiggedPrimeHolomorphicClockRate m : ℂ) * Complex.I

theorem log_preDivisorRiggedPrimeHolomorphicTerminalPrime_pos (m : ℕ) :
    0 < Real.log
      ((preDivisorRiggedPrimeHolomorphicTerminalPrime m : Nat.Primes) : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (preDivisorRiggedPrimeHolomorphicTerminalPrime m).prop.two_le

theorem preDivisorRiggedPrimeHolomorphicClockRate_pos (m : ℕ) :
    0 < preDivisorRiggedPrimeHolomorphicClockRate m := by
  exact div_pos Real.pi_pos
    (log_preDivisorRiggedPrimeHolomorphicTerminalPrime_pos m)

/-- The selected packet zero is genuinely noncentral at every finite stage. -/
theorem preDivisorRiggedPrimeHolomorphicClockPoint_ne_zero (m : ℕ) :
    preDivisorRiggedPrimeHolomorphicClockPoint m ≠ 0 := by
  exact mul_ne_zero
    (ofReal_ne_zero.mpr (preDivisorRiggedPrimeHolomorphicClockRate_pos m).ne')
    (by simp)

/-- Euler's identity at `π i` gives the terminal signed Bockstein's first noncentral zero. -/
theorem preDivisorHolomorphicPrimeBockstein_terminal_clockPoint_zero (m : ℕ) :
    preDivisorHolomorphicPrimeBockstein
      (preDivisorRiggedPrimeHolomorphicClockPoint m)
      (preDivisorRiggedPrimeHolomorphicTerminalPrime m) = 0 := by
  have hlogne : Real.log
      ((preDivisorRiggedPrimeHolomorphicTerminalPrime m : Nat.Primes) : ℝ) ≠ 0 :=
    (log_preDivisorRiggedPrimeHolomorphicTerminalPrime_pos m).ne'
  have harg :
      (Real.log
          ((preDivisorRiggedPrimeHolomorphicTerminalPrime m : Nat.Primes) : ℝ) : ℂ) *
          preDivisorRiggedPrimeHolomorphicClockPoint m =
        (Real.pi : ℂ) * Complex.I := by
    have hreal :
        Real.log
            ((preDivisorRiggedPrimeHolomorphicTerminalPrime m : Nat.Primes) : ℝ) *
            (Real.pi / Real.log
              ((preDivisorRiggedPrimeHolomorphicTerminalPrime m : Nat.Primes) : ℝ)) =
          Real.pi := by
      field_simp
    rw [preDivisorRiggedPrimeHolomorphicClockPoint,
      preDivisorRiggedPrimeHolomorphicClockRate, ← mul_assoc,
      ← Complex.ofReal_mul, hreal]
  rw [preDivisorHolomorphicPrimeBockstein, harg, Complex.exp_neg,
    Complex.exp_pi_mul_I]
  simp

/-- Entire finite product complexifying the exact neutral rigged-prime packet determinant. -/
def preDivisorRiggedPrimeHolomorphicPacket (m : ℕ) (z : ℂ) : ℂ :=
  ((1 - (m + 2 : ℕ) : ℝ) : ℂ) *
    ∏ i : Fin (m + 2),
      preDivisorHolomorphicPrimeBockstein z (nthPrimePoint i)

/-- Every coefficient-faithful holomorphic packet is entire. -/
theorem differentiable_preDivisorRiggedPrimeHolomorphicPacket (m : ℕ) :
    Differentiable ℂ (preDivisorRiggedPrimeHolomorphicPacket m) := by
  unfold preDivisorRiggedPrimeHolomorphicPacket
  refine (differentiable_const _).mul ?_
  have hfun :
      (fun z => ∏ i : Fin (m + 2),
        preDivisorHolomorphicPrimeBockstein z (nthPrimePoint i)) =
        ∏ i : Fin (m + 2),
          fun z => preDivisorHolomorphicPrimeBockstein z (nthPrimePoint i) := by
    funext z
    simp [Finset.prod_apply]
  rw [hfun]
  exact Differentiable.finsetProd
    (fun i _ => differentiable_preDivisorHolomorphicPrimeBockstein (nthPrimePoint i))

/-- Exact realification of the entire packet is the previously constructed neutral SC
determinant, not merely a function with the same sign or leading jet. -/
theorem preDivisorRiggedPrimeHolomorphicPacket_ofReal (m : ℕ) (t : ℝ) :
    preDivisorRiggedPrimeHolomorphicPacket m (t : ℂ) =
      (preDivisorRiggedPrimeNeutralPacketDeterminant m t : ℂ) := by
  rw [preDivisorRiggedPrimeNeutralPacketDeterminant_eq]
  simp only [preDivisorRiggedPrimeHolomorphicPacket,
    preDivisorHolomorphicPrimeBockstein_ofReal, Complex.ofReal_mul,
    Complex.ofReal_prod, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.ofReal_sub]

/-- Every packet contains the selected noncentral zero from its terminal prime factor. -/
theorem preDivisorRiggedPrimeHolomorphicPacket_clockPoint_zero (m : ℕ) :
    preDivisorRiggedPrimeHolomorphicPacket m
      (preDivisorRiggedPrimeHolomorphicClockPoint m) = 0 := by
  rw [preDivisorRiggedPrimeHolomorphicPacket]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ (Fin.last (m + 1)))
  simpa [preDivisorRiggedPrimeHolomorphicTerminalPrime] using
    preDivisorHolomorphicPrimeBockstein_terminal_clockPoint_zero m

/-- Terminal Bockstein clock rates shrink to zero as the packet prime tends to infinity. -/
theorem tendsto_preDivisorRiggedPrimeHolomorphicClockRate_zero :
    Tendsto preDivisorRiggedPrimeHolomorphicClockRate atTop (nhds 0) := by
  have hlog : Tendsto
      (fun m => Real.log
        ((preDivisorRiggedPrimeHolomorphicTerminalPrime m : Nat.Primes) : ℝ))
      atTop atTop := by
    change Tendsto
      (fun m => Real.log ((nthPrimePoint (m + 1)).1 : ℝ)) atTop atTop
    convert tendsto_log_nthPrimePoint_atTop.comp
      (Filter.tendsto_add_atTop_nat 1) using 1
    rfl
  exact tendsto_const_nhds.div_atTop hlog

/-- The selected noncentral packet zeros condense at the wall origin. -/
theorem tendsto_preDivisorRiggedPrimeHolomorphicClockPoint_zero :
    Tendsto preDivisorRiggedPrimeHolomorphicClockPoint atTop (nhds 0) := by
  have hcast : Tendsto
      (fun m => (preDivisorRiggedPrimeHolomorphicClockRate m : ℂ))
      atTop (nhds 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp
      tendsto_preDivisorRiggedPrimeHolomorphicClockRate_zero
  change Tendsto
    (fun m => (preDivisorRiggedPrimeHolomorphicClockRate m : ℂ) * Complex.I)
    atTop (nhds 0)
  simpa using hcast.mul (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => Complex.I) atTop (nhds Complex.I))

/-- **Prime-log zero-condensation law.**  The exact coefficient-faithful SC packets possess a
noncentral zero at every finite stage, and these zeros converge to the wall origin.  This is the
positive structural survivor exposed by scalar regularization failure. -/
theorem preDivisorRiggedPrimeHolomorphicPacket_zeroCondensation :
    (∀ m,
      preDivisorRiggedPrimeHolomorphicClockPoint m ≠ 0 ∧
      preDivisorRiggedPrimeHolomorphicPacket m
        (preDivisorRiggedPrimeHolomorphicClockPoint m) = 0) ∧
    Tendsto preDivisorRiggedPrimeHolomorphicClockPoint atTop (nhds 0) := by
  exact ⟨fun m =>
    ⟨preDivisorRiggedPrimeHolomorphicClockPoint_ne_zero m,
      preDivisorRiggedPrimeHolomorphicPacket_clockPoint_zero m⟩,
    tendsto_preDivisorRiggedPrimeHolomorphicClockPoint_zero⟩

/-- **Packet-growing central-pole scalar regularization no-go.**  Let `F m` be arbitrary candidate
regularized packets and `G m` arbitrary complex-valued scalar profiles.  Suppose their
factorization by the exact holomorphic SC packet holds only away from the wall origin, so `G m`
may encode an arbitrarily high packet-dependent central pole.  The moving noncentral packet zero
remains, because `G m` has a finite complex value there.  Local uniform convergence would transfer
those zeros to the origin, contradicting `XiC(0) / XiC(0) = 1`.

Consequently a viable scalar landing must also be singular at the moving noncentral prime-log
zeros, whose set condenses at the wall, or must break primewise determinant factorization by
cross-prime/operator coupling. -/
theorem not_tendstoLocallyUniformly_normalizedXiC_of_holomorphicPacket_scalarFactor
    (F G : ℕ → ℂ → ℂ)
    (hfactor : ∀ m z, z ≠ 0 →
      F m z = G m z * preDivisorRiggedPrimeHolomorphicPacket m z) :
    ¬ TendstoLocallyUniformly F (fun z => XiC z / XiC 0) atTop := by
  intro hconv
  have hzeros : ∀ m,
      F m (preDivisorRiggedPrimeHolomorphicClockPoint m) = 0 := by
    intro m
    rw [hfactor m (preDivisorRiggedPrimeHolomorphicClockPoint m)
      (preDivisorRiggedPrimeHolomorphicClockPoint_ne_zero m),
      preDivisorRiggedPrimeHolomorphicPacket_clockPoint_zero, mul_zero]
  have hconvOn : TendstoLocallyUniformlyOn
      F (fun z => XiC z / XiC 0) atTop Set.univ :=
    tendstoLocallyUniformlyOn_univ.mpr hconv
  have harg : Tendsto preDivisorRiggedPrimeHolomorphicClockPoint
      atTop (𝓝[Set.univ] 0) := by
    simpa only [nhdsWithin_univ] using
      tendsto_preDivisorRiggedPrimeHolomorphicClockPoint_zero
  have hcomp : Tendsto
      (fun m => F m (preDivisorRiggedPrimeHolomorphicClockPoint m)) atTop
      (nhds (XiC 0 / XiC 0)) :=
    hconvOn.tendsto_comp
      (XiC_differentiable.div_const _).continuous.continuousWithinAt
      (Set.mem_univ 0) harg
  have hzero : Tendsto
      (fun m => F m (preDivisorRiggedPrimeHolomorphicClockPoint m))
      atTop (nhds 0) := by
    simpa only [hzeros] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))
  have hbad : XiC 0 / XiC 0 = 0 := tendsto_nhds_unique hcomp hzero
  rw [div_self XiC_zero_ne] at hbad
  exact one_ne_zero hbad

end
end RHTower
