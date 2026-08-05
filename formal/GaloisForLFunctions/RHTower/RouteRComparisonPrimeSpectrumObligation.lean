import GaloisForLFunctions.RHTower.RouteRCocycleTransportNonErasure

/-!
# The prime-logarithm spectrum forced on any admissible comparison target

The logarithmic Kummer derivation acts on the two legs of the ordinary prime atom by the scalars
`± log p`.  A comparison of the rational adelic cyclic source into another algebra that intertwines
the derivations therefore transports these eigenvalue equations, and non-erasure of the atom
guarantees the images are nonzero.

Hence any target of an intertwining, trace-compatible comparison carries the entire prime-logarithm
spectrum in the point spectrum of its own derivation, with explicit eigenvectors.  Distinct primes
give distinct eigenvalues, so the eigenvectors are linearly independent and the target cannot be
finite-dimensional: no finite-rank model can receive the comparison.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Kummer derivation scales the forward prime leg by `log p`. -/
theorem ccmKummerDerivAdd_primeAtomForward (p : Nat.Primes) :
    ccmKummerDerivAdd (primeAtomForward p) =
      ((Real.log (p : ℝ) : ℂ)) • primeAtomForward p := by
  change (RHTower.ccmRationalAdelicKummerDerivationNonunital
      (RHTower.ccmRationalAdelicPrimeCycleForward p) : CyclicSource) = _
  rw [RHTower.ccmRationalAdelicPrimeCycleForward,
    RHTower.ccmRationalAdelicKummerDerivationNonunital_single,
    RHTower.ccmRationalAdelicKummerLogWeight_primeScaling]
  apply Unitization.ext <;> simp [primeAtomForward, RHTower.ccmRationalAdelicPrimeCycleForward]

/-- The Kummer derivation scales the backward prime leg by `-log p`. -/
theorem ccmKummerDerivAdd_primeAtomBackward (p : Nat.Primes) :
    ccmKummerDerivAdd (primeAtomBackward p) =
      (-(Real.log (p : ℝ) : ℂ)) • primeAtomBackward p :=
  RHTower.ccmRationalAdelicKummerDerivation_primeBackward p

/-- The prime logarithms are pairwise distinct. -/
theorem primeLog_injective :
    Function.Injective fun p : Nat.Primes => ((Real.log (p : ℝ) : ℂ)) := by
  intro p q hpq
  have hreal : Real.log (p : ℝ) = Real.log (q : ℝ) := Complex.ofReal_inj.mp hpq
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.2.pos
  have : ((p : ℕ) : ℝ) = ((q : ℕ) : ℝ) := by
    have := congrArg Real.exp hreal
    rwa [Real.exp_log hp, Real.exp_log hq] at this
  exact Subtype.ext (by exact_mod_cast this)

variable {B : Type*} [NonUnitalRing B] [Module ℂ B]

/-- **Forced eigenvalue on the forward leg.**  An intertwining, trace-compatible comparison sends
the forward prime leg to a nonzero eigenvector of the target derivation with eigenvalue `log p`. -/
theorem hasEigenvector_primeAtomForward (τB : B →+ ℂ) (DB : B →ₗ[ℂ] B)
    (f : CyclicSource →ₗ[ℂ] B)
    (hmul : ∀ a a' : CyclicSource, f (a * a') = f a * f a')
    (hD : ∀ a : CyclicSource, DB (f a) = f (ccmKummerDerivAdd a))
    (hτ : ∀ a : CyclicSource, τB (f a) = ccmEpsilonZeroAdd a) (p : Nat.Primes) :
    Module.End.HasEigenvector DB ((Real.log (p : ℝ) : ℂ)) (f (primeAtomForward p)) := by
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · rw [hD, ccmKummerDerivAdd_primeAtomForward, map_smul]
  · exact (primeAtom_not_erased τB DB.toAddMonoidHom f.toAddMonoidHom hmul hD hτ p).1

/-- **Forced eigenvalue on the backward leg.** -/
theorem hasEigenvector_primeAtomBackward (τB : B →+ ℂ) (DB : B →ₗ[ℂ] B)
    (f : CyclicSource →ₗ[ℂ] B)
    (hmul : ∀ a a' : CyclicSource, f (a * a') = f a * f a')
    (hD : ∀ a : CyclicSource, DB (f a) = f (ccmKummerDerivAdd a))
    (hτ : ∀ a : CyclicSource, τB (f a) = ccmEpsilonZeroAdd a) (p : Nat.Primes) :
    Module.End.HasEigenvector DB (-(Real.log (p : ℝ) : ℂ)) (f (primeAtomBackward p)) := by
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · rw [hD, ccmKummerDerivAdd_primeAtomBackward, map_smul]
  · exact (primeAtom_not_erased τB DB.toAddMonoidHom f.toAddMonoidHom hmul hD hτ p).2.1

/-- **Prime-logarithm point spectrum.**  Every prime logarithm and its negative belong to the point
spectrum of the target derivation. -/
theorem hasEigenvalue_primeLog (τB : B →+ ℂ) (DB : B →ₗ[ℂ] B) (f : CyclicSource →ₗ[ℂ] B)
    (hmul : ∀ a a' : CyclicSource, f (a * a') = f a * f a')
    (hD : ∀ a : CyclicSource, DB (f a) = f (ccmKummerDerivAdd a))
    (hτ : ∀ a : CyclicSource, τB (f a) = ccmEpsilonZeroAdd a) (p : Nat.Primes) :
    Module.End.HasEigenvalue DB ((Real.log (p : ℝ) : ℂ)) ∧
      Module.End.HasEigenvalue DB (-(Real.log (p : ℝ) : ℂ)) :=
  ⟨Module.End.hasEigenvalue_of_hasEigenvector
      (hasEigenvector_primeAtomForward τB DB f hmul hD hτ p),
    Module.End.hasEigenvalue_of_hasEigenvector
      (hasEigenvector_primeAtomBackward τB DB f hmul hD hτ p)⟩

/-- **Independence of the transported prime atoms.**  The forward legs are linearly independent in
the target, because they are eigenvectors for pairwise distinct eigenvalues. -/
theorem linearIndependent_primeAtomForward_image (τB : B →+ ℂ) (DB : B →ₗ[ℂ] B)
    (f : CyclicSource →ₗ[ℂ] B)
    (hmul : ∀ a a' : CyclicSource, f (a * a') = f a * f a')
    (hD : ∀ a : CyclicSource, DB (f a) = f (ccmKummerDerivAdd a))
    (hτ : ∀ a : CyclicSource, τB (f a) = ccmEpsilonZeroAdd a) :
    LinearIndependent ℂ fun p : Nat.Primes => f (primeAtomForward p) :=
  Module.End.eigenvectors_linearIndependent' DB
    (fun p : Nat.Primes => ((Real.log (p : ℝ) : ℂ)))
    primeLog_injective _ (hasEigenvector_primeAtomForward τB DB f hmul hD hτ)

/-- **No finite-dimensional target.**  A comparison that intertwines the derivations and pulls back
the zero-adele trace cannot land in a finite-dimensional space: the transported prime atoms form an
infinite linearly independent family. -/
theorem not_module_finite_of_comparison (τB : B →+ ℂ) (DB : B →ₗ[ℂ] B)
    (f : CyclicSource →ₗ[ℂ] B)
    (hmul : ∀ a a' : CyclicSource, f (a * a') = f a * f a')
    (hD : ∀ a : CyclicSource, DB (f a) = f (ccmKummerDerivAdd a))
    (hτ : ∀ a : CyclicSource, τB (f a) = ccmEpsilonZeroAdd a) :
    ¬ Module.Finite ℂ B := by
  intro hfin
  exact Module.Finite.not_linearIndependent_of_infinite
    (fun p : Nat.Primes => f (primeAtomForward p))
    (linearIndependent_primeAtomForward_image τB DB f hmul hD hτ)

/-- The identity comparison satisfies every transport hypothesis, so the obligations above are not
vacuous; specialising to it shows the cyclic source itself is infinite-dimensional. -/
theorem cyclicSource_not_module_finite : ¬ Module.Finite ℂ CyclicSource :=
  not_module_finite_of_comparison ccmEpsilonZeroAdd
    RHTower.ccmRationalAdelicKummerDerivation LinearMap.id
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

end

end GaloisForLFunctions.RHTower
