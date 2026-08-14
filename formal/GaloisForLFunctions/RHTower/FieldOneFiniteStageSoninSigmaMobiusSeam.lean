import GaloisForLFunctions.RHTower.FieldOneFiniteStageSoninSigma
import GaloisForLFunctions.RHTower.GibbsMoebiusAnchor

/-!
# The literal finite-stage Sonin source is the critical Möbius source

For a subset `T` of finite places, put exponent `-1` at exactly the places in
`T`.  The literal field-one Sonin vector then evaluates on that `S`-unit orbit
as

`mu(n_T) / n_T`,

where `n_T` is the product of the retained rational primes.  Thus the Sonin
finite-place source and the critical Möbius source are not merely analogous:
their labeled coefficients agree exactly.  Since the Sonin vector is fixed by
finite Fourier transform, the final theorem identifies both source transports
at the same literal orbit point while retaining every prime label.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain
open _root_.RHTower

/-- Exponent `-1` on a chosen finite-place packet and `0` elsewhere. -/
def fieldOneFiniteStageSquarefreeExponent
    {S : Finset (HeightOneSpectrum ℤ)} (T : Finset ↥S) : ↥S → ℤ := by
  classical
  exact fun v => if v ∈ T then -1 else 0

/-- Literal positive `S`-unit with inverse-prime support exactly `T`. -/
def fieldOneFiniteStageSquarefreeSUnit
    {S : Finset (HeightOneSpectrum ℤ)} (T : Finset ↥S) :
    fieldOneSUnitSubgroup S :=
  ⟨fieldOneSUnitProduct S (fieldOneFiniteStageSquarefreeExponent T),
    fieldOneSUnitProduct_mem S (fieldOneFiniteStageSquarefreeExponent T)⟩

/-- Rational-prime support of a finite-place packet. -/
def fieldOneFiniteStagePrimeSupport
    {S : Finset (HeightOneSpectrum ℤ)} (T : Finset ↥S) : Finset ℕ :=
  T.image fun v => (Rat.HeightOneSpectrum.primesEquiv v.1 : ℕ)

/-- Squarefree integer labeled by a finite-place packet. -/
def fieldOneFiniteStageSquarefreeInteger
    {S : Finset (HeightOneSpectrum ℤ)} (T : Finset ↥S) : ℕ :=
  ∏ p ∈ fieldOneFiniteStagePrimeSupport T, p

private theorem fieldOneFiniteStage_primeMap_injective
    {S : Finset (HeightOneSpectrum ℤ)} :
    Function.Injective
      (fun v : ↥S => (Rat.HeightOneSpectrum.primesEquiv v.1 : ℕ)) := by
  intro v w h
  apply Subtype.ext
  exact Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext h)

theorem fieldOneFiniteStagePrimeSupport_card
    {S : Finset (HeightOneSpectrum ℤ)} (T : Finset ↥S) :
    (fieldOneFiniteStagePrimeSupport T).card = T.card := by
  rw [fieldOneFiniteStagePrimeSupport, Finset.card_image_iff.mpr]
  exact fieldOneFiniteStage_primeMap_injective.injOn

theorem fieldOneFiniteStagePrimeSupport_prime
    {S : Finset (HeightOneSpectrum ℤ)} (T : Finset ↥S) :
    ∀ p ∈ fieldOneFiniteStagePrimeSupport T, p.Prime := by
  intro p hp
  rw [fieldOneFiniteStagePrimeSupport, Finset.mem_image] at hp
  obtain ⟨v, _, rfl⟩ := hp
  exact (Rat.HeightOneSpectrum.primesEquiv v.1).2

theorem fieldOneFiniteStageSquarefreeInteger_eq_prod
    {S : Finset (HeightOneSpectrum ℤ)} (T : Finset ↥S) :
    fieldOneFiniteStageSquarefreeInteger T =
      ∏ v ∈ T, (Rat.HeightOneSpectrum.primesEquiv v.1 : ℕ) := by
  classical
  rw [fieldOneFiniteStageSquarefreeInteger,
    fieldOneFiniteStagePrimeSupport, Finset.prod_image]
  intro v _ w _ h
  exact fieldOneFiniteStage_primeMap_injective h

/-- Möbius sign of the packet product, with no quotient of prime labels. -/
theorem moebius_fieldOneFiniteStageSquarefreeInteger
    {S : Finset (HeightOneSpectrum ℤ)} (T : Finset ↥S) :
    (ArithmeticFunction.moebius
        (fieldOneFiniteStageSquarefreeInteger T) : ℤ) = (-1) ^ T.card := by
  rw [fieldOneFiniteStageSquarefreeInteger,
    _root_.RHTower.GibbsGas.moebius_prod_primes
      (fieldOneFiniteStagePrimeSupport_prime T),
    fieldOneFiniteStagePrimeSupport_card]

/-- The Sonin orbit coefficient on an inverse-prime packet is its full labeled
product, including Möbius sign and one inverse factor for each retained prime. -/
theorem fieldOneFiniteStageSoninSigmaOrbitCoefficient_squarefree_prod
    {S : Finset (HeightOneSpectrum ℤ)} (T : Finset ↥S) :
    fieldOneFiniteStageSoninSigmaOrbitCoefficient S
        (fieldOneFiniteStageSquarefreeSUnit T) =
      ∏ v ∈ T, -((Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ)⁻¹) := by
  classical
  unfold fieldOneFiniteStageSoninSigmaOrbitCoefficient
  change (∏ v : ↥S,
      if fieldOneSUnitExponent S
          ⟨fieldOneSUnitProduct S (fieldOneFiniteStageSquarefreeExponent T),
            fieldOneSUnitProduct_mem S (fieldOneFiniteStageSquarefreeExponent T)⟩ v = 0
      then 1
      else if fieldOneSUnitExponent S
          ⟨fieldOneSUnitProduct S (fieldOneFiniteStageSquarefreeExponent T),
            fieldOneSUnitProduct_mem S (fieldOneFiniteStageSquarefreeExponent T)⟩ v = -1
      then -((Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ)⁻¹)
      else 0) = _
  rw [fieldOneSUnitExponent_product]
  calc
    (∏ v : ↥S,
        if fieldOneFiniteStageSquarefreeExponent T v = 0 then 1
        else if fieldOneFiniteStageSquarefreeExponent T v = -1 then
          -((Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ)⁻¹)
        else 0) =
        ∏ v : ↥S, if v ∈ T then
          -((Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ)⁻¹) else 1 := by
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ T <;>
        simp [fieldOneFiniteStageSquarefreeExponent, hv]
    _ = ∏ v ∈ T, -((Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ)⁻¹) := by
      have hT : S.attach ∩ T = T := by
        ext v
        simp
      simp [hT]

/-- **Coefficient-faithful source seam.**  The literal finite-place Sonin
coefficient is exactly the unnormalized critical Möbius amplitude
`mu(n_T) / n_T`. -/
theorem fieldOneFiniteStageSoninSigmaOrbitCoefficient_eq_moebius_div
    {S : Finset (HeightOneSpectrum ℤ)} (T : Finset ↥S) :
    fieldOneFiniteStageSoninSigmaOrbitCoefficient S
        (fieldOneFiniteStageSquarefreeSUnit T) =
      ((ArithmeticFunction.moebius
          (fieldOneFiniteStageSquarefreeInteger T) : ℤ) : ℂ) /
        (fieldOneFiniteStageSquarefreeInteger T : ℂ) := by
  classical
  rw [fieldOneFiniteStageSoninSigmaOrbitCoefficient_squarefree_prod,
    moebius_fieldOneFiniteStageSquarefreeInteger,
    fieldOneFiniteStageSquarefreeInteger_eq_prod]
  rw [Int.cast_pow, Int.cast_neg, Int.cast_one, Nat.cast_prod]
  rw [div_eq_mul_inv]
  calc
    (∏ v ∈ T, -((Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ)⁻¹)) =
        ∏ v ∈ T, (-1 : ℂ) *
          (Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ)⁻¹ := by
      apply Finset.prod_congr rfl
      intro v _
      ring
    _ = (-1 : ℂ) ^ T.card *
        (∏ v ∈ T, (Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ))⁻¹ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.prod_inv_distrib]

/-- Literal orbit evaluation of the Sonin vector is the Möbius amplitude and
is independent of the angular representative. -/
theorem fieldOneFiniteStageSoninSigma_sunitAngular_squarefree_eq_moebius_div
    {S : Finset (HeightOneSpectrum ℤ)} (T : Finset ↥S)
    (k : FieldOneFiniteStageModuleOneClass S) :
    (fieldOneFiniteStageSoninSigma S).1
        (fun v =>
          algebraMap ℚ (v.1.adicCompletion ℚ)
              ((fieldOneFiniteStageSquarefreeSUnit T).1 : ℚ) *
            fieldOneFiniteStageAngularFiniteEmbedding S k v) =
      ((ArithmeticFunction.moebius
          (fieldOneFiniteStageSquarefreeInteger T) : ℤ) : ℂ) /
        (fieldOneFiniteStageSquarefreeInteger T : ℂ) := by
  rw [fieldOneFiniteStageSoninSigma_sunitAngular,
    fieldOneFiniteStageSoninSigmaOrbitCoefficient_eq_moebius_div]

/-- **Same-carrier two-transport identification.**  Source and finite Fourier
transport have the same exact Möbius coefficient at the same literal orbit
point.  No relabeling, bounded scalarization, or quotient by multiplicity is
used. -/
theorem fieldOneFiniteStageSoninSigma_fourierPair_squarefree_eq_moebius_div
    {S : Finset (HeightOneSpectrum ℤ)} (T : Finset ↥S)
    (k : FieldOneFiniteStageModuleOneClass S) :
    ((fieldOneFiniteStageFiniteBruhatFourierLinear S
        (fieldOneFiniteStageSoninSigma S)).1
          (fun v =>
            algebraMap ℚ (v.1.adicCompletion ℚ)
                ((fieldOneFiniteStageSquarefreeSUnit T).1 : ℚ) *
              fieldOneFiniteStageAngularFiniteEmbedding S k v) =
        ((ArithmeticFunction.moebius
            (fieldOneFiniteStageSquarefreeInteger T) : ℤ) : ℂ) /
          (fieldOneFiniteStageSquarefreeInteger T : ℂ)) ∧
      ((fieldOneFiniteStageSoninSigma S).1
          (fun v =>
            algebraMap ℚ (v.1.adicCompletion ℚ)
                ((fieldOneFiniteStageSquarefreeSUnit T).1 : ℚ) *
              fieldOneFiniteStageAngularFiniteEmbedding S k v) =
        ((ArithmeticFunction.moebius
            (fieldOneFiniteStageSquarefreeInteger T) : ℤ) : ℂ) /
          (fieldOneFiniteStageSquarefreeInteger T : ℂ)) := by
  constructor
  · rw [fieldOneFiniteStageFiniteBruhatFourier_soninSigma]
    exact fieldOneFiniteStageSoninSigma_sunitAngular_squarefree_eq_moebius_div T k
  · exact fieldOneFiniteStageSoninSigma_sunitAngular_squarefree_eq_moebius_div T k

end

end GaloisForLFunctions.RHTower
