import GaloisForLFunctions.RHTower.SquarefreeEulerModularCoronaCurvatureColligation
import GaloisForLFunctions.HTGeometry.ExteriorOrderedProduct

/-!
# The finite squarefree determinant line is the exterior-horizon occupation line

Occupation configurations of a finite prime packet are exactly its squarefree subsets, so the
coordinate space of the determinant line is canonically identified with the exterior algebra of the
one-particle space `E_S`, an occupation configuration going to the increasing wedge of its occupied
primes.  Under this identification the unnormalized signed source is the ordered exterior product

```text
φ_S(σ) = ∏_{p ∈ S}^∧ (1 - p^{-σ/2} e_p),
```

whose Plücker coordinate at a squarefree subset `T` is `∏_{p ∈ T} (-√q_p)`: the Möbius sign is the
parity of the occupation number and the modulus is the half-density of the Gibbs weight.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Primes are linearly ordered by their underlying natural number; this fixes the increasing
order used by the exterior wedges. -/
local instance squarefreeExteriorPrimeLinearOrder : LinearOrder Nat.Primes :=
  LinearOrder.lift' (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective

/-! ## Occupation configurations are squarefree subsets -/

/-- The occupied set of an occupation configuration. -/
def squarefreeOccupationFinset {S : Finset Nat.Primes} (x : SquarefreeBitConfig S) :
    Finset ↥S :=
  Finset.univ.filter fun p => x p = 1

/-- **Occupation configurations are exactly the squarefree subsets of the packet.** -/
def squarefreeOccupationEquiv (S : Finset Nat.Primes) :
    SquarefreeBitConfig S ≃ Finset ↥S where
  toFun := squarefreeOccupationFinset
  invFun T := fun p => if p ∈ T then 1 else 0
  left_inv x := by
    funext p
    by_cases h : x p = 1
    · simp [squarefreeOccupationFinset, h]
    · have h0 : x p = 0 := by omega
      simp [squarefreeOccupationFinset, h0]
  right_inv T := by
    ext p
    simp [squarefreeOccupationFinset]

theorem mem_squarefreeOccupationFinset {S : Finset Nat.Primes} (x : SquarefreeBitConfig S)
    (p : ↥S) : p ∈ squarefreeOccupationFinset x ↔ x p = 1 := by
  simp [squarefreeOccupationFinset]

/-- The occupation number is the cardinality of the occupied set. -/
theorem sum_bit_eq_card_squarefreeOccupationFinset {S : Finset Nat.Primes}
    (x : SquarefreeBitConfig S) :
    (∑ p : ↥S, (x p : ℕ)) = (squarefreeOccupationFinset x).card := by
  rw [squarefreeOccupationFinset, Finset.card_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : x p = 1
  · simp [h]
  · have h0 : x p = 0 := by omega
    simp [h0]

/-- The additive Hamiltonian is the energy of the occupied set. -/
theorem finiteSquarefreeHamiltonian_eq_sum_occupation {S : Finset Nat.Primes}
    (x : SquarefreeBitConfig S) :
    finiteSquarefreeHamiltonian S x =
      ∑ p ∈ squarefreeOccupationFinset x, squarefreePrimeEnergy p := by
  rw [finiteSquarefreeHamiltonian, squarefreeBitEnergy, squarefreeOccupationFinset,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : x p = 1
  · simp [h]
  · have h0 : x p = 0 := by omega
    simp [h0]

/-! ## The source coefficient is a Plücker coordinate -/

/-- The one-particle amplitude of a prime aperture, `-√q_p`. -/
def squarefreePrimeAmplitude (sigma : ℝ) (p : Nat.Primes) : ℂ :=
  ((-Real.sqrt (squarefreePrimeNome sigma p) : ℝ) : ℂ)

theorem exp_neg_half_energy_eq_sqrt_nome (sigma : ℝ) (p : Nat.Primes) :
    Real.exp (-sigma * squarefreePrimeEnergy p / 2) =
      Real.sqrt (squarefreePrimeNome sigma p) := by
  rw [squarefreePrimeNome_eq_exp, ← Real.exp_half]

/-- **Plücker form of the unnormalized signed source coefficient.** -/
theorem finiteSquarefreeRawSourceCoefficient_eq_prod (S : Finset Nat.Primes) (sigma : ℝ)
    (x : SquarefreeBitConfig S) :
    finiteSquarefreeRawSourceCoefficient S sigma x =
      ∏ p ∈ squarefreeOccupationFinset x, squarefreePrimeAmplitude sigma (p : Nat.Primes) := by
  have hexp : Real.exp (-sigma * finiteSquarefreeHamiltonian S x / 2) =
      ∏ p ∈ squarefreeOccupationFinset x,
        Real.sqrt (squarefreePrimeNome sigma (p : Nat.Primes)) := by
    rw [finiteSquarefreeHamiltonian_eq_sum_occupation,
      show -sigma * (∑ p ∈ squarefreeOccupationFinset x, squarefreePrimeEnergy (p : Nat.Primes))
          / 2 =
          ∑ p ∈ squarefreeOccupationFinset x,
            -sigma * squarefreePrimeEnergy (p : Nat.Primes) / 2 by
        rw [Finset.mul_sum, Finset.sum_div],
      Real.exp_sum]
    exact Finset.prod_congr rfl fun p _ => exp_neg_half_energy_eq_sqrt_nome sigma _
  have hsplit : (∏ p ∈ squarefreeOccupationFinset x,
        (-Real.sqrt (squarefreePrimeNome sigma (p : Nat.Primes)))) =
      (-1 : ℝ) ^ (squarefreeOccupationFinset x).card *
        ∏ p ∈ squarefreeOccupationFinset x,
          Real.sqrt (squarefreePrimeNome sigma (p : Nat.Primes)) := by
    rw [show (fun p : ↥S => -Real.sqrt (squarefreePrimeNome sigma (p : Nat.Primes))) =
        fun p : ↥S => (-1 : ℝ) * Real.sqrt (squarefreePrimeNome sigma (p : Nat.Primes)) from
      funext fun p => by ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hcast : (∏ p ∈ squarefreeOccupationFinset x,
        squarefreePrimeAmplitude sigma (p : Nat.Primes)) =
      ((∏ p ∈ squarefreeOccupationFinset x,
          (-Real.sqrt (squarefreePrimeNome sigma (p : Nat.Primes))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    rfl
  rw [hcast, finiteSquarefreeRawSourceCoefficient, finiteSquarefreeMobiusSign,
    sum_bit_eq_card_squarefreeOccupationFinset, ← Complex.ofReal_mul]
  congr 1
  rw [hsplit, hexp]

/-! ## The exterior-horizon identification -/

/-- The one-particle space of a finite prime packet. -/
abbrev SquarefreeOneParticle (S : Finset Nat.Primes) := ↥S → ℂ

/-- The exterior-horizon Fock space of a finite prime packet. -/
abbrev SquarefreeExteriorHorizon (S : Finset Nat.Primes) :=
  ExteriorAlgebra ℂ (SquarefreeOneParticle S)

/-- The one-particle coordinate basis of the packet. -/
def squarefreeOneParticleBasis (S : Finset Nat.Primes) :
    Module.Basis ↥S ℂ (SquarefreeOneParticle S) :=
  Pi.basisFun ℂ ↥S

/-- **The exterior-horizon identification.**  The determinant-line coordinate space is the
exterior algebra of the one-particle space, an occupation configuration going to the increasing
wedge of its occupied primes. -/
def squarefreeExteriorIdentification (S : Finset Nat.Primes) :
    EuclideanSpace ℂ (SquarefreeBitConfig S) ≃ₗ[ℂ] SquarefreeExteriorHorizon S :=
  (EuclideanSpace.basisFun (SquarefreeBitConfig S) ℂ).toBasis.equiv
    (squarefreeOneParticleBasis S).ExteriorAlgebra (squarefreeOccupationEquiv S)

theorem squarefreeExteriorIdentification_basis (S : Finset Nat.Primes)
    (x : SquarefreeBitConfig S) :
    squarefreeExteriorIdentification S
        ((EuclideanSpace.basisFun (SquarefreeBitConfig S) ℂ).toBasis x) =
      HTGeometry.orderedWedge (R := ℂ) (squarefreeOneParticleBasis S)
        (squarefreeOccupationFinset x) := by
  rw [squarefreeExteriorIdentification, Module.Basis.equiv_apply,
    HTGeometry.orderedWedge_eq_basis]
  rfl

/-- The unnormalized signed source as a vector of the determinant-line coordinate space. -/
def finiteSquarefreeRawSource (S : Finset Nat.Primes) (sigma : ℝ) :
    EuclideanSpace ℂ (SquarefreeBitConfig S) :=
  WithLp.toLp 2 (finiteSquarefreeRawSourceCoefficient S sigma)

/-- The ordered exterior product of the one-particle source factors. -/
def squarefreeExteriorSource (S : Finset Nat.Primes) (sigma : ℝ) :
    SquarefreeExteriorHorizon S :=
  HTGeometry.orderedPluckerProduct (R := ℂ) (squarefreeOneParticleBasis S)
    (fun p => squarefreePrimeAmplitude sigma (p : Nat.Primes)) Finset.univ

theorem squarefreeExteriorSource_eq_sum (S : Finset Nat.Primes) (sigma : ℝ) :
    squarefreeExteriorSource S sigma =
      ∑ T : Finset ↥S,
        (∏ p ∈ T, squarefreePrimeAmplitude sigma (p : Nat.Primes)) •
          HTGeometry.orderedWedge (R := ℂ) (squarefreeOneParticleBasis S) T := by
  rw [squarefreeExteriorSource, HTGeometry.orderedPluckerProduct_eq_sum, Finset.powerset_univ]

/-- **The finite source is the ordered exterior product.**  Under the exterior-horizon
identification the unnormalized signed determinant-line source is exactly
`∏_{p ∈ S}^∧ (1 - p^{-σ/2} e_p)`. -/
theorem squarefreeExteriorIdentification_rawSource (S : Finset Nat.Primes) (sigma : ℝ) :
    squarefreeExteriorIdentification S (finiteSquarefreeRawSource S sigma) =
      squarefreeExteriorSource S sigma := by
  have hrepr : ∀ x : SquarefreeBitConfig S,
      (EuclideanSpace.basisFun (SquarefreeBitConfig S) ℂ).toBasis.repr
          (finiteSquarefreeRawSource S sigma) x =
        finiteSquarefreeRawSourceCoefficient S sigma x := fun x => rfl
  have hsum := Module.Basis.sum_repr
    (EuclideanSpace.basisFun (SquarefreeBitConfig S) ℂ).toBasis
    (finiteSquarefreeRawSource S sigma)
  calc
    squarefreeExteriorIdentification S (finiteSquarefreeRawSource S sigma)
        = squarefreeExteriorIdentification S
            (∑ x : SquarefreeBitConfig S,
              finiteSquarefreeRawSourceCoefficient S sigma x •
                (EuclideanSpace.basisFun (SquarefreeBitConfig S) ℂ).toBasis x) := by
          rw [show (∑ x : SquarefreeBitConfig S,
              finiteSquarefreeRawSourceCoefficient S sigma x •
                (EuclideanSpace.basisFun (SquarefreeBitConfig S) ℂ).toBasis x) =
              ∑ x : SquarefreeBitConfig S,
                ((EuclideanSpace.basisFun (SquarefreeBitConfig S) ℂ).toBasis.repr
                  (finiteSquarefreeRawSource S sigma)) x •
                  (EuclideanSpace.basisFun (SquarefreeBitConfig S) ℂ).toBasis x from
            Finset.sum_congr rfl fun x _ => by rw [hrepr x]]
          rw [hsum]
    _ = ∑ x : SquarefreeBitConfig S,
          finiteSquarefreeRawSourceCoefficient S sigma x •
            HTGeometry.orderedWedge (R := ℂ) (squarefreeOneParticleBasis S)
              (squarefreeOccupationFinset x) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun x _ => by
            rw [map_smul, squarefreeExteriorIdentification_basis]
    _ = squarefreeExteriorSource S sigma := by
          rw [squarefreeExteriorSource_eq_sum]
          refine Fintype.sum_equiv (squarefreeOccupationEquiv S) _ _ fun x => ?_
          rw [finiteSquarefreeRawSourceCoefficient_eq_prod]
          rfl

end RHTower
