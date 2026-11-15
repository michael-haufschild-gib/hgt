import GaloisForLFunctions.TransHorizonIncidenceMechanics.Moments.FermiImpulseMemory
import GaloisForLFunctions.HTGeometry.Moments.EntireResponseMemory

/-!
# Entire Fermi impulses with unbounded differential order

The native dyadic impulse sequence is the derivative sequence at zero of a
canonical entire exponential polynomial. Delaying the impulse preserves the sum
of squared derivatives, exactly `4 / 3`, but raises the minimum nonzero
constant-coefficient ODE order to `d + 1`.

Thus a uniform bound on this derivative-jet energy cannot bound differential
order, even inside the entire exponential polynomials. The explicit global
operator is `D^(d+1) - (1/2) D^d`; the matching lower bound already holds for an
equation on a neighborhood of zero.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry
open _root_.HTGeometry.FiniteHankel

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

/-- The complexified native impulse is the delayed geometric sequence of ratio `1/2`. -/
theorem fermiDyadicImpulse_cast_eq_delayedGeometric (d : ℕ) :
    (fun n => (fermiDyadicImpulse d n : ℂ)) = delayedGeometric (1 / 2 : ℂ) d := by
  funext n
  rw [fermiDyadicImpulse_eq_delayedGeometric]
  by_cases h : d ≤ n <;> simp [delayedGeometric, h]

/-- Canonical entire realization of the native dyadic impulse. -/
noncomputable def fermiDyadicEntireImpulse (d : ℕ) : ℂ → ℂ :=
  responseTaylorFun (fun n => (fermiDyadicImpulse d n : ℂ))

/-- The canonical entire impulse is the delayed response at ratio `1/2`. -/
theorem fermiDyadicEntireImpulse_eq_delayed (d : ℕ) :
    fermiDyadicEntireImpulse d = delayedEntireResponse (1 / 2) d := by
  simp only [fermiDyadicEntireImpulse, fermiDyadicImpulse_cast_eq_delayedGeometric,
    delayedEntireResponse]

/-- Every entire dyadic impulse is an exponential polynomial. -/
theorem fermiDyadicEntireImpulse_mem_expPolySpaceC (d : ℕ) :
    fermiDyadicEntireImpulse d ∈ expPolySpaceC := by
  rw [fermiDyadicEntireImpulse_eq_delayed]
  exact delayedEntireResponse_mem_expPolySpaceC _ _

/-- The dyadic impulse realization is analytic on the whole complex plane. -/
theorem fermiDyadicEntireImpulse_entire (d : ℕ) (z : ℂ) :
    AnalyticAt ℂ (fermiDyadicEntireImpulse d) z :=
  analyticAt_of_mem_expPolySpaceC (fermiDyadicEntireImpulse_mem_expPolySpaceC d) z

/-- Its full derivative sequence at zero recovers the native discrete impulse. -/
theorem fermiDyadicEntireImpulse_jets (d : ℕ) :
    respSeq (fermiDyadicEntireImpulse d) = fun n => (fermiDyadicImpulse d n : ℂ) := by
  rw [fermiDyadicEntireImpulse_eq_delayed, delayedEntireResponse_jets,
    fermiDyadicImpulse_cast_eq_delayedGeometric]

/-- The derivative of order `n` is exactly the native dyadic impulse at `n`. -/
theorem fermiDyadicEntireImpulse_jet (d n : ℕ) :
    iteratedDeriv n (fermiDyadicEntireImpulse d) 0 = (fermiDyadicImpulse d n : ℂ) :=
  congrFun (fermiDyadicEntireImpulse_jets d) n

/-- The sum of squared raw derivatives at zero is `4/3`, independently of delay. -/
theorem fermiDyadicEntireImpulse_jetEnergy (d : ℕ) :
    HasSum (fun n => Complex.normSq (iteratedDeriv n (fermiDyadicEntireImpulse d) 0))
      (4 / 3 : ℝ) := by
  simpa only [fermiDyadicEntireImpulse_jet, Complex.normSq_ofReal, pow_two] using
    fermiDyadicImpulse_square_hasSum d

/-- The global differential equation has order `d + 1` and coefficient `1/2`. -/
theorem fermiDyadicEntireImpulse_ode (d : ℕ) (z : ℂ) :
    iteratedDeriv (d + 1) (fermiDyadicEntireImpulse d) z =
      (1 / 2 : ℂ) * iteratedDeriv d (fermiDyadicEntireImpulse d) z := by
  rw [fermiDyadicEntireImpulse_eq_delayed]
  exact delayedEntireResponse_ode _ _ _

/-- The displayed global ODE has minimum possible order, even among local equations. -/
theorem fermiDyadicEntireImpulse_minimalODE (d : ℕ) :
    (∃ p : Polynomial ℂ, p.Monic ∧ p.natDegree = d + 1 ∧
      ∀ z, odeSum p.coeff p.natDegree (fermiDyadicEntireImpulse d) z = 0) ∧
    (∀ p : Polynomial ℂ, p ≠ 0 →
      (∀ᶠ z in 𝓝 (0 : ℂ), odeSum p.coeff p.natDegree (fermiDyadicEntireImpulse d) z = 0) →
      d + 1 ≤ p.natDegree) := by
  rw [fermiDyadicEntireImpulse_eq_delayed]
  exact delayedEntireResponse_minimalODE _ _

/-- Fixed derivative-jet energy does not bound constant-coefficient differential order. -/
theorem fixed_jetEnergy_unbounded_ODE_order (B : ℕ) :
    ∃ f : ℂ → ℂ, f ∈ expPolySpaceC ∧
      HasSum (fun n => Complex.normSq (iteratedDeriv n f 0)) (4 / 3 : ℝ) ∧
      (∃ p : Polynomial ℂ, p.Monic ∧ p.natDegree = B + 1 ∧
        ∀ z, odeSum p.coeff p.natDegree f z = 0) ∧
      (∀ p : Polynomial ℂ, p ≠ 0 →
        (∀ᶠ z in 𝓝 (0 : ℂ), odeSum p.coeff p.natDegree f z = 0) → B < p.natDegree) := by
  refine ⟨fermiDyadicEntireImpulse B, fermiDyadicEntireImpulse_mem_expPolySpaceC B,
    fermiDyadicEntireImpulse_jetEnergy B, (fermiDyadicEntireImpulse_minimalODE B).1, ?_⟩
  intro p hp hode
  have h := (fermiDyadicEntireImpulse_minimalODE B).2 p hp hode
  omega

#print axioms fermiDyadicEntireImpulse_jetEnergy
#print axioms fermiDyadicEntireImpulse_ode
#print axioms fixed_jetEnergy_unbounded_ODE_order

end GaloisForLFunctions.TransHorizonIncidenceMechanics
