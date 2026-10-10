import GaloisForLFunctions.HTGeometry.PaperMoebiusPrimeLSeries
import GaloisForLFunctions.RHTower.FiniteAbscissaArithmeticUnits

/-!
# Individual-time rigidity of prime-core transport in ambient arithmetic algebras

The source's additive action is defined on the terminating core. Even a single
nontrivial time cannot be realized by an endomorphism of the full arithmetic
algebra, or of the entire finite-abscissa algebra. More precisely, two transported
Möbius sources can be connected by such an endomorphism exactly when their times
coincide. This uses the corpus's proven scalar-character classification, without
continuity or any assumption about a family of endomorphisms.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every endomorphism of the full arithmetic algebra preserves coefficient one. -/
theorem paperArithmeticEndomorphism_augmentation
    (F : ArithmeticFunction ℂ →ₐ[ℂ] ArithmeticFunction ℂ) (f : ArithmeticFunction ℂ) :
    F f 1 = f 1 :=
  _root_.RHTower.arithmeticFunctionAlgHom_apply
    (_root_.RHTower.arithmeticFunctionAugmentation.comp F) f

/-- Distinct prime-core times lie in different orbits of all ambient endomorphisms. -/
theorem paperMoebiusPrimeTransport_ambient_orbit_iff (p : Nat.Primes) (t u : ℂ) :
    (∃ F : ArithmeticFunction ℂ →ₐ[ℂ] ArithmeticFunction ℂ,
      F (paperMoebiusPrimeTransport p t) = paperMoebiusPrimeTransport p u) ↔ t = u := by
  constructor
  · rintro ⟨F, hF⟩
    have h := congrArg (fun f : ArithmeticFunction ℂ => f 1) hF
    rw [paperArithmeticEndomorphism_augmentation, paperMoebiusPrimeTransport_one,
      paperMoebiusPrimeTransport_one] at h
    linear_combination -h
  · rintro rfl
    exact ⟨AlgHom.id ℂ (ArithmeticFunction ℂ), rfl⟩

/-- The exact ambient extension boundary is time zero, not merely exclusion of time one. -/
theorem paperMoebiusPrimeTransport_ambient_extension_iff (p : Nat.Primes) (t : ℂ) :
    (∃ F : ArithmeticFunction ℂ →ₐ[ℂ] ArithmeticFunction ℂ,
      F ArithmeticFunction.moebius = paperMoebiusPrimeTransport p t) ↔ t = 0 := by
  have hz : paperMoebiusPrimeTransport p 0 = ArithmeticFunction.moebius := by
    simp [paperMoebiusPrimeTransport_eq]
  rw [← hz, paperMoebiusPrimeTransport_ambient_orbit_iff]
  exact eq_comm

/-- The literal transported source belongs to the native finite-abscissa algebra. -/
def paperMoebiusPrimeFiniteSource (p : Nat.Primes) (t : ℂ) :
    finiteAbscissaArithmeticSubalgebra := by
  refine ⟨paperMoebiusPrimeTransport p t, 1, ?_⟩
  intro y hy
  exact paperMoebiusPrimeTransport_LSeriesSummable p t ⟨(y : ℂ), by simpa using hy⟩

/-- Coefficient one is also invariant under every endomorphism of the analytic source algebra. -/
theorem paperFiniteAbscissaEndomorphism_augmentation
    (F : finiteAbscissaArithmeticSubalgebra →ₐ[ℂ] finiteAbscissaArithmeticSubalgebra)
    (f : finiteAbscissaArithmeticSubalgebra) : (F f).val 1 = f.val 1 :=
  _root_.RHTower.FiniteAbscissaUnits.algHom_apply
    (_root_.RHTower.arithmeticFunctionAugmentation.comp
      (finiteAbscissaArithmeticSubalgebra.val.comp F)) f

/-- Passing to all sources with finite convergence abscissa does not remove time rigidity. -/
theorem paperMoebiusPrimeTransport_finiteAbscissa_orbit_iff (p : Nat.Primes) (t u : ℂ) :
    (∃ F : finiteAbscissaArithmeticSubalgebra →ₐ[ℂ] finiteAbscissaArithmeticSubalgebra,
      F (paperMoebiusPrimeFiniteSource p t) = paperMoebiusPrimeFiniteSource p u) ↔ t = u := by
  constructor
  · rintro ⟨F, hF⟩
    have h := congrArg (fun f : finiteAbscissaArithmeticSubalgebra => f.val 1) hF
    rw [paperFiniteAbscissaEndomorphism_augmentation] at h
    change paperMoebiusPrimeTransport p t 1 = paperMoebiusPrimeTransport p u 1 at h
    rw [paperMoebiusPrimeTransport_one, paperMoebiusPrimeTransport_one] at h
    linear_combination -h
  · rintro rfl
    exact ⟨AlgHom.id ℂ finiteAbscissaArithmeticSubalgebra, rfl⟩

end

end GaloisForLFunctions.HTGeometry
