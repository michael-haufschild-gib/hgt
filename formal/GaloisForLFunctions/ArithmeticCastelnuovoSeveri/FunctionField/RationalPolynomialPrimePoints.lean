import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPolynomialPrimeFibers

/-!
# Rational normalization primes and algebra points

A map to the constant field is surjective and its kernel has constant
quotient. Conversely, a prime with constant quotient supplies exactly one
such map. This identifies rational normalization primes with algebra points
without choosing residue-field embeddings separately.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (K B : Type*) [Field K] [CommRing B] [Algebra K B]

/-- The kernel of a constant-valued algebra point is a rational prime. -/
def rationalPolynomialPointPrime (f : B →ₐ[K] K) : RationalPolynomialPrimes K B := by
  refine ⟨RingHom.ker f, RingHom.ker_isPrime f, ?_⟩
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨f b, ?_⟩
  change Ideal.Quotient.mk (RingHom.ker f) (algebraMap K B (f b)) =
    Ideal.Quotient.mk (RingHom.ker f) b
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change f (algebraMap K B (f b) - b) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (f.commutes (f b))

/-- A rational algebra point is determined by its prime kernel. -/
theorem rationalPolynomialPointPrime_injective :
    Function.Injective (rationalPolynomialPointPrime K B) := by
  intro f g h
  have hker : RingHom.ker f = RingHom.ker g := congrArg Subtype.val h
  apply AlgHom.ext
  intro b
  have hm : b - algebraMap K B (f b) ∈ RingHom.ker f := by
    change f (b - algebraMap K B (f b)) = 0
    rw [map_sub, f.commutes]
    exact sub_self _
  rw [hker] at hm
  change g (b - algebraMap K B (f b)) = 0 at hm
  rw [map_sub, g.commutes] at hm
  exact (sub_eq_zero.mp hm).symm

/-- Every prime whose quotient consists of constants is the kernel of a constant-valued algebra point. -/
theorem rationalPolynomialPointPrime_surjective :
    Function.Surjective (rationalPolynomialPointPrime K B) := by
  intro P
  letI := P.property.1
  let e : K ≃ₐ[K] B ⧸ P.val :=
    AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ P.val))
      ⟨(algebraMap K (B ⧸ P.val)).injective, P.property.2⟩
  let f := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K P.val)
  refine ⟨f, Subtype.ext ?_⟩
  ext b
  change e.symm (Ideal.Quotient.mk P.val b) = 0 ↔ b ∈ P.val
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact e.symm.injective (h.trans (map_zero e.symm).symm)
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

/-- Rational algebra points and constant-residue prime ideals are equivalent. -/
def rationalPolynomialPointEquiv : (B →ₐ[K] K) ≃ RationalPolynomialPrimes K B :=
  Equiv.ofBijective (rationalPolynomialPointPrime K B)
    ⟨rationalPolynomialPointPrime_injective K B, rationalPolynomialPointPrime_surjective K B⟩

/-- Finiteness of rational primes gives finiteness of the actual algebra-point set. -/
instance rationalPolynomialPoints_finite [Finite (RationalPolynomialPrimes K B)] :
    Finite (B →ₐ[K] K) :=
  Finite.of_equiv (RationalPolynomialPrimes K B) (rationalPolynomialPointEquiv K B).symm

/-- Rational prime counts equal counts of constant-valued algebra maps. -/
theorem rationalPolynomialPrimes_card_algHom :
    Nat.card (RationalPolynomialPrimes K B) = Nat.card (B →ₐ[K] K) :=
  (Nat.card_congr (rationalPolynomialPointEquiv K B)).symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
