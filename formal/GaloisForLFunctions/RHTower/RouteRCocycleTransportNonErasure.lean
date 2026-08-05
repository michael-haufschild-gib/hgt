import GaloisForLFunctions.HTGeometry.TraceDerivationCyclicCocycleLaw
import GaloisForLFunctions.RHTower.RouteRKummerCyclicOneCocycleDetector

/-!
# Transport of the Kummer cocycle and non-erasure of the ordinary prime atom

The zero-adele trace and the logarithmic Kummer derivation of the rational adelic cyclic source are
an instance of the general trace/derivation pair: the trace is cyclic, the derivation satisfies
Leibniz, and the trace annihilates the derivation.  So the Kummer detector is the universal
trace-derivation cyclic one-cocycle specialised to this pair, and all of its structural properties
are inherited rather than model-specific.

The transport law then converts the comparison obligation into two equations.  Any additive,
multiplicative comparison of the cyclic source into another ring which intertwines the derivations
and pulls the target trace back to the zero-adele trace automatically preserves the cocycle, and
therefore cannot annihilate either leg of the retained ordinary-prime atom: its cocycle value is
`-log p`, which is nonzero for every prime.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The minimal unitisation carrying the cyclic source. -/
abbrev CyclicSource : Type := CCMRationalAdelicCyclicSourceAlgebra

/-- The zero-adele trace, as an additive map. -/
def ccmEpsilonZeroAdd : CyclicSource →+ ℂ :=
  (ccmRationalAdelicEpsilonZero : CyclicSource →ₗ[ℂ] ℂ).toAddMonoidHom

/-- The logarithmic Kummer derivation, as an additive map. -/
def ccmKummerDerivAdd : CyclicSource →+ CyclicSource :=
  (RHTower.ccmRationalAdelicKummerDerivation).toAddMonoidHom

@[simp]
theorem ccmEpsilonZeroAdd_apply (x : CyclicSource) :
    ccmEpsilonZeroAdd x = ccmRationalAdelicEpsilonZero x := rfl

@[simp]
theorem ccmKummerDerivAdd_apply (x : CyclicSource) :
    ccmKummerDerivAdd x = RHTower.ccmRationalAdelicKummerDerivation x := rfl

theorem ccmEpsilonZeroAdd_isAlgebraTrace : IsAlgebraTrace ccmEpsilonZeroAdd :=
  fun a b => ccmRationalAdelicEpsilonZero_isTrace a b

theorem ccmKummerDerivAdd_isAlgebraDerivation : IsAlgebraDerivation ccmKummerDerivAdd :=
  fun a b => RHTower.ccmRationalAdelicKummerDerivation_mul a b

theorem ccmEpsilonZeroAdd_kummerDerivAdd (x : CyclicSource) :
    ccmEpsilonZeroAdd (ccmKummerDerivAdd x) = 0 :=
  RHTower.ccmRationalAdelicEpsilonZero_kummerDerivation x

/-- The Kummer detector is the universal trace-derivation cocycle of the pair `(ε₀, ∂log)`. -/
def ccmKummerTraceDerivCocycle (a b : CyclicSource) : ℂ :=
  traceDerivCocycle ccmEpsilonZeroAdd ccmKummerDerivAdd a b

theorem ccmKummerTraceDerivCocycle_antisymm (a b : CyclicSource) :
    ccmKummerTraceDerivCocycle a b = -ccmKummerTraceDerivCocycle b a :=
  traceDerivCocycle_antisymm ccmEpsilonZeroAdd_isAlgebraTrace
    ccmKummerDerivAdd_isAlgebraDerivation ccmEpsilonZeroAdd_kummerDerivAdd a b

theorem ccmKummerTraceDerivCocycle_boundary (a b c : CyclicSource) :
    ccmKummerTraceDerivCocycle (a * b) c - ccmKummerTraceDerivCocycle a (b * c) +
      ccmKummerTraceDerivCocycle (c * a) b = 0 :=
  traceDerivCocycle_boundary ccmEpsilonZeroAdd_isAlgebraTrace
    ccmKummerDerivAdd_isAlgebraDerivation a b c

/-! ## The retained ordinary prime atom -/

/-- Forward leg of the ordinary prime atom inside the unitised cyclic source. -/
def primeAtomForward (p : Nat.Primes) : CyclicSource :=
  (RHTower.ccmRationalAdelicPrimeCycleForward p : CyclicSource)

/-- Backward leg of the ordinary prime atom inside the unitised cyclic source. -/
def primeAtomBackward (p : Nat.Primes) : CyclicSource :=
  (RHTower.ccmRationalAdelicPrimeCycleBackward p : CyclicSource)

/-- Exact cocycle value on the retained ordinary prime atom. -/
theorem ccmKummerTraceDerivCocycle_primeAtom (p : Nat.Primes) :
    ccmKummerTraceDerivCocycle (primeAtomForward p) (primeAtomBackward p) =
      -(Real.log (p : ℝ) : ℂ) := by
  have h := RHTower.ccmRationalAdelicKummerCyclicOneCocycle_primeAtom p
  rw [RHTower.ccmRationalAdelicOrdinaryPrimeCycleAtom,
    RHTower.ccmRationalAdelicKummerCyclicOneCocycle_tprod] at h
  rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ] at h
  simpa [ccmKummerTraceDerivCocycle, traceDerivCocycle, primeAtomForward,
    primeAtomBackward] using h

theorem ccmKummerTraceDerivCocycle_primeAtom_ne_zero (p : Nat.Primes) :
    ccmKummerTraceDerivCocycle (primeAtomForward p) (primeAtomBackward p) ≠ 0 := by
  rw [ccmKummerTraceDerivCocycle_primeAtom, neg_ne_zero, Complex.ofReal_ne_zero]
  exact Real.log_ne_zero_of_pos_of_ne_one
    (by exact_mod_cast p.2.pos) (by exact_mod_cast p.2.ne_one)

/-! ## The comparison obligation -/

variable {B : Type*} [NonUnitalRing B]

/-- **Cocycle transport.**  A comparison that is additive and multiplicative, intertwines the two
derivations, and pulls the target trace back to the zero-adele trace preserves the Kummer
cocycle. -/
theorem ccmKummerTraceDerivCocycle_transport (τB : B →+ ℂ) (DB : B →+ B)
    (f : CyclicSource →+ B) (hmul : ∀ a a' : CyclicSource, f (a * a') = f a * f a')
    (hD : ∀ a : CyclicSource, DB (f a) = f (ccmKummerDerivAdd a))
    (hτ : ∀ a : CyclicSource, τB (f a) = ccmEpsilonZeroAdd a) (a b : CyclicSource) :
    traceDerivCocycle τB DB (f a) (f b) = ccmKummerTraceDerivCocycle a b :=
  traceDerivCocycle_comp f hmul hD hτ a b

/-- **Non-erasure of the ordinary prime atom.**  Under the transport hypotheses neither leg of the
retained atom can be annihilated, and its transported cocycle value is still nonzero.  The
coefficient-faithfulness requirement on a source-to-target comparison therefore reduces to the two
intertwining identities, with no further information about the comparison. -/
theorem primeAtom_not_erased (τB : B →+ ℂ) (DB : B →+ B)
    (f : CyclicSource →+ B) (hmul : ∀ a a' : CyclicSource, f (a * a') = f a * f a')
    (hD : ∀ a : CyclicSource, DB (f a) = f (ccmKummerDerivAdd a))
    (hτ : ∀ a : CyclicSource, τB (f a) = ccmEpsilonZeroAdd a) (p : Nat.Primes) :
    f (primeAtomForward p) ≠ 0 ∧ f (primeAtomBackward p) ≠ 0 ∧
      traceDerivCocycle τB DB (f (primeAtomForward p)) (f (primeAtomBackward p)) ≠ 0 := by
  have hne := ccmKummerTraceDerivCocycle_primeAtom_ne_zero p
  exact ⟨ne_zero_of_traceDerivCocycle_ne_zero_left f hmul hD hτ hne,
    ne_zero_of_traceDerivCocycle_ne_zero_right f hmul hD hτ hne,
    traceDerivCocycle_image_ne_zero f hmul hD hτ hne⟩

/-- The transported value is exactly `-log p`. -/
theorem primeAtom_transported_value (τB : B →+ ℂ) (DB : B →+ B)
    (f : CyclicSource →+ B) (hmul : ∀ a a' : CyclicSource, f (a * a') = f a * f a')
    (hD : ∀ a : CyclicSource, DB (f a) = f (ccmKummerDerivAdd a))
    (hτ : ∀ a : CyclicSource, τB (f a) = ccmEpsilonZeroAdd a) (p : Nat.Primes) :
    traceDerivCocycle τB DB (f (primeAtomForward p)) (f (primeAtomBackward p)) =
      -(Real.log (p : ℝ) : ℂ) := by
  rw [ccmKummerTraceDerivCocycle_transport τB DB f hmul hD hτ,
    ccmKummerTraceDerivCocycle_primeAtom]

end

end GaloisForLFunctions.RHTower
