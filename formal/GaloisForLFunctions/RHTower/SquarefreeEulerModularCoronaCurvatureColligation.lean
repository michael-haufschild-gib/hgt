import GaloisForLFunctions.RHTower.MobiusChannelCriticalMassEscape
import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentHilbertLift
import GaloisForLFunctions.RHTower.MobiusIncidenceClockGiniFisherFourUnit
import GaloisForLFunctions.RHTower.EulerLaurentResidueDouble
import GaloisForLFunctions.RHTower.EulerFisherCurvature
import GaloisForLFunctions.RHTower.HighExponentShellOrthogonalDivisorReplication
import GaloisForLFunctions.RHTower.MobiusPlueckerNormalConeDiagonalLift
import GaloisForLFunctions.RHTower.SquarefreeFixedCurrentLocalization
import GaloisForLFunctions.HTGeometry.FredholmDeterminantZeta
import GaloisForLFunctions.RHTower.FermionicFockIsospectrality
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Squarefree Euler modular-corona curvature colligation

This file formalizes the complete unconditional content of the paper card with the same name.
The finite part is developed in actual two-state prime coordinates.  The infinite part separates
the holomorphic Hilbert field from its unbounded first-trace codiagonal, identifies the safe
Hilbert--Schmidt determinant, and records the ordinary-Fock escape at the Euler boundary.

No RH transgression hypothesis is introduced here.  In particular, this module does not identify
the first-trace corona with an anti-causal second fundamental form.
-/

open Complex Filter Topology Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-! ## Finite Bernoulli tensor packets -/

/-- Occupation configurations of a finite set of two-state apartments. -/
abbrev SquarefreeBitConfig {α : Type*} [DecidableEq α] (S : Finset α) :=
  ↥S → Fin 2

/-- Dependent-function presentation used by the exact insert-one-apartment equivalence. -/
def squarefreeBitConfigDepEquiv {α : Type*} [DecidableEq α] (S : Finset α) :
    SquarefreeBitConfig S ≃ ((i : α) → i ∈ S → Fin 2) where
  toFun x i hi := x ⟨i, hi⟩
  invFun x i := x i i.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Adding one new apartment is literally a product with `Fin 2`. -/
def squarefreeInsertBitEquiv {α : Type*} [DecidableEq α]
    {S : Finset α} {a : α} (ha : a ∉ S) :
    SquarefreeBitConfig (insert a S) ≃ Fin 2 × SquarefreeBitConfig S :=
  (squarefreeBitConfigDepEquiv (insert a S)).trans <|
    (Finset.insertPiProdEquiv (fun _ => Fin 2) ha).trans <|
      Equiv.prodCongr (Equiv.refl (Fin 2))
        (squarefreeBitConfigDepEquiv S).symm

/-- Additive occupation energy. -/
def squarefreeBitEnergy {α : Type*} [DecidableEq α] (S : Finset α)
    (energy : α → ℝ) (x : SquarefreeBitConfig S) : ℝ :=
  ∑ i : ↥S, ((x i : ℕ) : ℝ) * energy i

/-- Independent Bernoulli product law in occupation coordinates. -/
def squarefreeBitWeight {α : Type*} [DecidableEq α] (S : Finset α)
    (r : α → ℝ) (x : SquarefreeBitConfig S) : ℝ :=
  ∏ i : ↥S, if x i = 0 then 1 - r i else r i

/-- Bernoulli energy mean. -/
def squarefreeBitMean {α : Type*} [DecidableEq α] (S : Finset α)
    (r energy : α → ℝ) : ℝ :=
  ∑ i : ↥S, r i * energy i

/-- Bernoulli energy variance. -/
def squarefreeBitVariance {α : Type*} [DecidableEq α] (S : Finset α)
    (r energy : α → ℝ) : ℝ :=
  ∑ i : ↥S, r i * (1 - r i) * energy i ^ 2

theorem squarefreeBitEnergy_insert_symm
    {α : Type*} [DecidableEq α] {S : Finset α} {a : α}
    (ha : a ∉ S) (energy : α → ℝ) (b : Fin 2)
    (x : SquarefreeBitConfig S) :
    squarefreeBitEnergy (insert a S) energy
        ((squarefreeInsertBitEquiv ha).symm (b, x)) =
      ((b : ℕ) : ℝ) * energy a + squarefreeBitEnergy S energy x := by
  rw [squarefreeBitEnergy, squarefreeBitEnergy]
  let eS := Finset.subtypeInsertEquivOption ha
  rw [Fintype.sum_equiv eS
    (fun i : ↥(insert a S) =>
      (((squarefreeInsertBitEquiv ha).symm (b, x) i : ℕ) : ℝ) * energy i)
    (fun o : Option ↥S => match o with
      | none => ((b : ℕ) : ℝ) * energy a
      | some i => ((x i : ℕ) : ℝ) * energy i)
    (fun i => by
      by_cases hia : (i : α) = a
      · simp [eS, squarefreeInsertBitEquiv, Finset.subtypeInsertEquivOption,
          Finset.insertPiProdEquiv, Finset.prodPiInsert,
          squarefreeBitConfigDepEquiv, hia]
      · simp [eS, squarefreeInsertBitEquiv, Finset.subtypeInsertEquivOption,
          Finset.insertPiProdEquiv, Finset.prodPiInsert,
          squarefreeBitConfigDepEquiv, hia])]
  simp

theorem squarefreeBitWeight_insert_symm
    {α : Type*} [DecidableEq α] {S : Finset α} {a : α}
    (ha : a ∉ S) (r : α → ℝ) (b : Fin 2)
    (x : SquarefreeBitConfig S) :
    squarefreeBitWeight (insert a S) r
        ((squarefreeInsertBitEquiv ha).symm (b, x)) =
      (if b = 0 then 1 - r a else r a) * squarefreeBitWeight S r x := by
  rw [squarefreeBitWeight, squarefreeBitWeight]
  let eS := Finset.subtypeInsertEquivOption ha
  rw [Fintype.prod_equiv eS
    (fun i : ↥(insert a S) =>
      if (squarefreeInsertBitEquiv ha).symm (b, x) i = 0
        then 1 - r i else r i)
    (fun o : Option ↥S => match o with
      | none => if b = 0 then 1 - r a else r a
      | some i => if x i = 0 then 1 - r i else r i)
    (fun i => by
      by_cases hia : (i : α) = a
      · simp [eS, squarefreeInsertBitEquiv, Finset.subtypeInsertEquivOption,
          Finset.insertPiProdEquiv, Finset.prodPiInsert,
          squarefreeBitConfigDepEquiv, hia]
      · simp [eS, squarefreeInsertBitEquiv, Finset.subtypeInsertEquivOption,
          Finset.insertPiProdEquiv, Finset.prodPiInsert,
          squarefreeBitConfigDepEquiv, hia])]
  simp

/-- Every finite Bernoulli tensor packet has total mass one. -/
theorem sum_squarefreeBitWeight {α : Type*} [DecidableEq α]
    (S : Finset α) (r : α → ℝ) :
    ∑ x : SquarefreeBitConfig S, squarefreeBitWeight S r x = 1 := by
  induction S using Finset.induction_on with
  | empty => simp [squarefreeBitWeight]
  | @insert a S ha ih =>
      rw [← (squarefreeInsertBitEquiv ha).symm.sum_comp,
        Fintype.sum_prod_type]
      simp_rw [squarefreeBitWeight_insert_symm]
      rw [Fin.sum_univ_two]
      simp only [Fin.isValue, if_pos, show (1 : Fin 2) ≠ 0 by decide, if_false]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ih]
      ring

/-- Exact first Bernoulli energy moment. -/
theorem sum_squarefreeBitWeight_mul_energy
    {α : Type*} [DecidableEq α] (S : Finset α) (r energy : α → ℝ) :
    ∑ x : SquarefreeBitConfig S,
        squarefreeBitWeight S r x * squarefreeBitEnergy S energy x =
      squarefreeBitMean S r energy := by
  induction S using Finset.induction_on with
  | empty => simp [squarefreeBitWeight, squarefreeBitEnergy, squarefreeBitMean]
  | @insert a S ha ih =>
      rw [← (squarefreeInsertBitEquiv ha).symm.sum_comp,
        Fintype.sum_prod_type]
      simp_rw [squarefreeBitWeight_insert_symm,
        squarefreeBitEnergy_insert_symm]
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_add, if_pos,
        Fin.val_one, Nat.cast_one, one_mul,
        show (1 : Fin 2) ≠ 0 by decide, if_false]
      have hzero :
          (∑ x : SquarefreeBitConfig S,
            (1 - r a) * squarefreeBitWeight S r x *
              squarefreeBitEnergy S energy x) =
            (1 - r a) * squarefreeBitMean S r energy := by
        calc
          _ = (1 - r a) *
              (∑ x : SquarefreeBitConfig S,
                squarefreeBitWeight S r x *
                  squarefreeBitEnergy S energy x) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x _
                ring
          _ = _ := by rw [ih]
      have hone :
          (∑ x : SquarefreeBitConfig S,
            r a * squarefreeBitWeight S r x *
              (energy a + squarefreeBitEnergy S energy x)) =
            r a * (energy a + squarefreeBitMean S r energy) := by
        calc
          _ = ∑ x : SquarefreeBitConfig S,
              (r a * energy a * squarefreeBitWeight S r x +
                r a * (squarefreeBitWeight S r x *
                  squarefreeBitEnergy S energy x)) := by
                  apply Finset.sum_congr rfl
                  intro x _
                  ring
          _ = r a * energy a *
                (∑ x : SquarefreeBitConfig S, squarefreeBitWeight S r x) +
              r a *
                (∑ x : SquarefreeBitConfig S,
                  squarefreeBitWeight S r x *
                    squarefreeBitEnergy S energy x) := by
                  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ = _ := by rw [sum_squarefreeBitWeight S r, ih]; ring
      rw [hzero, hone]
      rw [squarefreeBitMean, squarefreeBitMean]
      rw [Fintype.sum_equiv (Finset.subtypeInsertEquivOption ha)
        (fun i : ↥(insert a S) => r i * energy i)
        (fun o : Option ↥S => match o with
          | none => r a * energy a
          | some i => r i * energy i)
        (fun i => by
          by_cases hia : (i : α) = a
          · simp [Finset.subtypeInsertEquivOption, hia]
          · simp [Finset.subtypeInsertEquivOption, hia])]
      simp
      ring

/-- Exact second Bernoulli energy moment. -/
theorem sum_squarefreeBitWeight_mul_energy_sq
    {α : Type*} [DecidableEq α] (S : Finset α) (r energy : α → ℝ) :
    ∑ x : SquarefreeBitConfig S,
        squarefreeBitWeight S r x * squarefreeBitEnergy S energy x ^ 2 =
      squarefreeBitMean S r energy ^ 2 +
        squarefreeBitVariance S r energy := by
  induction S using Finset.induction_on with
  | empty =>
      simp [squarefreeBitWeight, squarefreeBitEnergy,
        squarefreeBitMean, squarefreeBitVariance]
  | @insert a S ha ih =>
      rw [← (squarefreeInsertBitEquiv ha).symm.sum_comp,
        Fintype.sum_prod_type]
      simp_rw [squarefreeBitWeight_insert_symm,
        squarefreeBitEnergy_insert_symm]
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_add, if_pos,
        Fin.val_one, Nat.cast_one, one_mul,
        show (1 : Fin 2) ≠ 0 by decide, if_false]
      have hcross :
          (∑ x : SquarefreeBitConfig S,
            squarefreeBitWeight S r x *
              (energy a + squarefreeBitEnergy S energy x) ^ 2) =
          energy a ^ 2 + 2 * energy a * squarefreeBitMean S r energy +
            (squarefreeBitMean S r energy ^ 2 +
              squarefreeBitVariance S r energy) := by
        calc
          _ = energy a ^ 2 *
                (∑ x : SquarefreeBitConfig S, squarefreeBitWeight S r x) +
              2 * energy a *
                (∑ x : SquarefreeBitConfig S,
                  squarefreeBitWeight S r x *
                    squarefreeBitEnergy S energy x) +
              ∑ x : SquarefreeBitConfig S,
                squarefreeBitWeight S r x *
                  squarefreeBitEnergy S energy x ^ 2 := by
                  simp_rw [add_sq, mul_add]
                  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                    Finset.mul_sum, Finset.mul_sum]
                  have hconst :
                      (∑ x : SquarefreeBitConfig S,
                        squarefreeBitWeight S r x * energy a ^ 2) =
                      ∑ x : SquarefreeBitConfig S,
                        energy a ^ 2 * squarefreeBitWeight S r x := by
                    apply Finset.sum_congr rfl
                    intro x _
                    ring
                  rw [hconst]
                  ring
          _ = _ := by
            rw [sum_squarefreeBitWeight S r,
              sum_squarefreeBitWeight_mul_energy, ih]
            ring
      have hzero :
          (∑ x : SquarefreeBitConfig S,
            (1 - r a) * squarefreeBitWeight S r x *
              squarefreeBitEnergy S energy x ^ 2) =
            (1 - r a) *
              (squarefreeBitMean S r energy ^ 2 +
                squarefreeBitVariance S r energy) := by
        calc
          _ = (1 - r a) *
              (∑ x : SquarefreeBitConfig S,
                squarefreeBitWeight S r x *
                  squarefreeBitEnergy S energy x ^ 2) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro x _
                  ring
          _ = _ := by rw [ih]
      have hone :
          (∑ x : SquarefreeBitConfig S,
            r a * squarefreeBitWeight S r x *
              (energy a + squarefreeBitEnergy S energy x) ^ 2) =
            r a *
              (energy a ^ 2 +
                2 * energy a * squarefreeBitMean S r energy +
                (squarefreeBitMean S r energy ^ 2 +
                  squarefreeBitVariance S r energy)) := by
        calc
          _ = r a *
              (∑ x : SquarefreeBitConfig S,
                squarefreeBitWeight S r x *
                  (energy a + squarefreeBitEnergy S energy x) ^ 2) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro x _
                    ring
          _ = _ := by rw [hcross]
      rw [hzero, hone]
      rw [squarefreeBitMean, squarefreeBitMean,
        squarefreeBitVariance, squarefreeBitVariance]
      rw [Fintype.sum_equiv (Finset.subtypeInsertEquivOption ha)
        (fun i : ↥(insert a S) => r i * energy i)
        (fun o : Option ↥S => match o with
          | none => r a * energy a
          | some i => r i * energy i)
        (fun i => by
          by_cases hia : (i : α) = a
          · simp [Finset.subtypeInsertEquivOption, hia]
          · simp [Finset.subtypeInsertEquivOption, hia])]
      rw [Fintype.sum_equiv (Finset.subtypeInsertEquivOption ha)
        (fun i : ↥(insert a S) => r i * (1 - r i) * energy i ^ 2)
        (fun o : Option ↥S => match o with
          | none => r a * (1 - r a) * energy a ^ 2
          | some i => r i * (1 - r i) * energy i ^ 2)
        (fun i => by
          by_cases hia : (i : α) = a
          · simp [Finset.subtypeInsertEquivOption, hia]
          · simp [Finset.subtypeInsertEquivOption, hia])]
      simp
      ring

/-- Exact centered second moment, hence exact Fisher/variance identity. -/
theorem sum_squarefreeBitWeight_mul_centeredEnergy_sq
    {α : Type*} [DecidableEq α] (S : Finset α) (r energy : α → ℝ) :
    ∑ x : SquarefreeBitConfig S, squarefreeBitWeight S r x *
        (squarefreeBitEnergy S energy x - squarefreeBitMean S r energy) ^ 2 =
      squarefreeBitVariance S r energy := by
  have hdecomp :
      (∑ x : SquarefreeBitConfig S, squarefreeBitWeight S r x *
        (squarefreeBitEnergy S energy x - squarefreeBitMean S r energy) ^ 2) =
        (∑ x : SquarefreeBitConfig S,
          squarefreeBitWeight S r x * squarefreeBitEnergy S energy x ^ 2) -
          2 * squarefreeBitMean S r energy *
            (∑ x : SquarefreeBitConfig S,
              squarefreeBitWeight S r x * squarefreeBitEnergy S energy x) +
          squarefreeBitMean S r energy ^ 2 *
            (∑ x : SquarefreeBitConfig S, squarefreeBitWeight S r x) := by
    calc
      _ = ∑ x : SquarefreeBitConfig S,
          (squarefreeBitWeight S r x * squarefreeBitEnergy S energy x ^ 2 -
            (2 * squarefreeBitMean S r energy) *
              (squarefreeBitWeight S r x * squarefreeBitEnergy S energy x) +
            squarefreeBitMean S r energy ^ 2 * squarefreeBitWeight S r x) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum, Finset.mul_sum]
  rw [hdecomp, sum_squarefreeBitWeight_mul_energy_sq,
    sum_squarefreeBitWeight_mul_energy, sum_squarefreeBitWeight]
  ring

/-- Exact centered first moment.  This is the scalar horizontality identity used below. -/
theorem sum_squarefreeBitWeight_mul_centeredEnergy
    {α : Type*} [DecidableEq α] (S : Finset α) (r energy : α → ℝ) :
    ∑ x : SquarefreeBitConfig S, squarefreeBitWeight S r x *
        (squarefreeBitEnergy S energy x - squarefreeBitMean S r energy) = 0 := by
  calc
    _ = (∑ x : SquarefreeBitConfig S,
          squarefreeBitWeight S r x * squarefreeBitEnergy S energy x) -
        squarefreeBitMean S r energy *
          (∑ x : SquarefreeBitConfig S, squarefreeBitWeight S r x) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = 0 := by
      rw [sum_squarefreeBitWeight_mul_energy,
        sum_squarefreeBitWeight]
      ring

/-- The Gibbs form of the independent Bernoulli law, with its full partition denominator. -/
theorem squarefreeBitWeight_logistic_eq
    {α : Type*} [DecidableEq α] (S : Finset α) (sigma : ℝ)
    (energy : α → ℝ) (x : SquarefreeBitConfig S) :
    squarefreeBitWeight S
        (fun i => Real.exp (-sigma * energy i) /
          (1 + Real.exp (-sigma * energy i))) x =
      Real.exp (-sigma * squarefreeBitEnergy S energy x) /
        ∏ i : ↥S, (1 + Real.exp (-sigma * energy i)) := by
  have hnum :
      Real.exp (-sigma * squarefreeBitEnergy S energy x) =
        ∏ i : ↥S,
          if x i = 0 then 1 else Real.exp (-sigma * energy i) := by
    rw [squarefreeBitEnergy]
    calc
      Real.exp (-sigma * ∑ i : ↥S, ((x i : ℕ) : ℝ) * energy i) =
          Real.exp (∑ i : ↥S,
            -sigma * (((x i : ℕ) : ℝ) * energy i)) := by
              congr 1
              rw [Finset.mul_sum]
      _ = ∏ i : ↥S,
          Real.exp (-sigma * (((x i : ℕ) : ℝ) * energy i)) := by
            simpa only using Real.exp_sum Finset.univ
              (fun i : ↥S => -sigma * (((x i : ℕ) : ℝ) * energy i))
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : x i = 0
        · simp [hi]
        · rw [Fin.eq_one_of_ne_zero (x i) hi]
          simp
  rw [squarefreeBitWeight, hnum, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : x i = 0
  · simp only [hi, if_pos]
    have hne : 1 + Real.exp (-sigma * energy i) ≠ 0 := by positivity
    field_simp
    ring
  · simp only [hi, if_false]

/-! ## Prime specialization: determinant line, current, curvature, and tangent -/

/-- Prime energy `log p`. -/
def squarefreePrimeEnergy (p : Nat.Primes) : ℝ := Real.log (p : ℝ)

/-- Local squarefree nome `q_p = p^{-sigma}`. -/
def squarefreePrimeNome (sigma : ℝ) (p : Nat.Primes) : ℝ :=
  primeSchurWeight sigma p

/-- Local Bernoulli occupation `q_p/(1+q_p)`. -/
def squarefreePrimeOccupation (sigma : ℝ) (p : Nat.Primes) : ℝ :=
  squarefreePrimeNome sigma p / (1 + squarefreePrimeNome sigma p)

/-- Finite squarefree determinant metric `Z_S`. -/
def finiteSquarefreePartition (S : Finset Nat.Primes) (sigma : ℝ) : ℝ :=
  ∏ p : ↥S, (1 + squarefreePrimeNome sigma p)

/-- Additive Hamiltonian on a finite prime occupation packet. -/
def finiteSquarefreeHamiltonian (S : Finset Nat.Primes)
    (x : SquarefreeBitConfig S) : ℝ :=
  squarefreeBitEnergy S squarefreePrimeEnergy x

/-- Born law of the normalized signed source. -/
def finiteSquarefreeBornWeight (S : Finset Nat.Primes) (sigma : ℝ)
    (x : SquarefreeBitConfig S) : ℝ :=
  squarefreeBitWeight S (squarefreePrimeOccupation sigma) x

/-- Connection/current `J_S`. -/
def finiteSquarefreeCurrent (S : Finset Nat.Primes) (sigma : ℝ) : ℝ :=
  squarefreeBitMean S (squarefreePrimeOccupation sigma) squarefreePrimeEnergy

/-- Hessian/Fisher curvature `V_S`. -/
def finiteSquarefreeCurvature (S : Finset Nat.Primes) (sigma : ℝ) : ℝ :=
  squarefreeBitVariance S (squarefreePrimeOccupation sigma) squarefreePrimeEnergy

/-- Logarithmic determinant metric in an additive form convenient for differentiation. -/
def finiteSquarefreeLogPartition (S : Finset Nat.Primes) (sigma : ℝ) : ℝ :=
  ∑ p : ↥S, Real.log (1 + squarefreePrimeNome sigma p)

/-- Möbius parity of an occupation configuration. -/
def finiteSquarefreeMobiusSign {S : Finset Nat.Primes}
    (x : SquarefreeBitConfig S) : ℝ :=
  (-1 : ℝ) ^ (∑ p : ↥S, (x p : ℕ))

/-- Unnormalized signed determinant-line coefficient. -/
def finiteSquarefreeRawSourceCoefficient (S : Finset Nat.Primes) (sigma : ℝ)
    (x : SquarefreeBitConfig S) : ℂ :=
  (finiteSquarefreeMobiusSign x : ℂ) *
    Real.exp (-sigma * finiteSquarefreeHamiltonian S x / 2)

/-- Normalized signed source coefficient.  Additive log normalization avoids a square-root branch. -/
def finiteSquarefreeSourceCoefficient (S : Finset Nat.Primes) (sigma : ℝ)
    (x : SquarefreeBitConfig S) : ℂ :=
  (finiteSquarefreeMobiusSign x : ℂ) *
    Real.exp (-sigma * finiteSquarefreeHamiltonian S x / 2 -
      finiteSquarefreeLogPartition S sigma / 2)

/-- The finite signed source as an actual vector in the coordinate tensor Hilbert space. -/
def finiteSquarefreeSource (S : Finset Nat.Primes) (sigma : ℝ) :
    EuclideanSpace ℂ (SquarefreeBitConfig S) :=
  WithLp.toLp 2 (finiteSquarefreeSourceCoefficient S sigma)

/-- Horizontal calibrated Fisher tangent. -/
def finiteSquarefreeTangent (S : Finset Nat.Primes) (sigma : ℝ) :
    EuclideanSpace ℂ (SquarefreeBitConfig S) :=
  WithLp.toLp 2 fun x =>
    ((-2 * (sigma - 1) *
      (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma) : ℝ) : ℂ) *
      finiteSquarefreeSourceCoefficient S sigma x

theorem squarefreePrimeNome_eq_exp
    (sigma : ℝ) (p : Nat.Primes) :
    squarefreePrimeNome sigma p =
      Real.exp (-sigma * squarefreePrimeEnergy p) := rfl

theorem squarefreePrimeNome_pos (sigma : ℝ) (p : Nat.Primes) :
    0 < squarefreePrimeNome sigma p := primeSchurWeight_pos sigma p

theorem squarefreePrimeOccupation_pos (sigma : ℝ) (p : Nat.Primes) :
    0 < squarefreePrimeOccupation sigma p := by
  rw [squarefreePrimeOccupation]
  exact div_pos (squarefreePrimeNome_pos sigma p)
    (by linarith [squarefreePrimeNome_pos sigma p])

theorem squarefreePrimeOccupation_lt_one (sigma : ℝ) (p : Nat.Primes) :
    squarefreePrimeOccupation sigma p < 1 := by
  rw [squarefreePrimeOccupation]
  exact (div_lt_one (by linarith [squarefreePrimeNome_pos sigma p])).2
    (by linarith [squarefreePrimeNome_pos sigma p])

theorem finiteSquarefreePartition_pos (S : Finset Nat.Primes) (sigma : ℝ) :
    0 < finiteSquarefreePartition S sigma := by
  apply Finset.prod_pos
  intro p hp
  linarith [squarefreePrimeNome_pos sigma p]

/-- Additive and multiplicative determinant metrics agree exactly. -/
theorem exp_finiteSquarefreeLogPartition
    (S : Finset Nat.Primes) (sigma : ℝ) :
    Real.exp (finiteSquarefreeLogPartition S sigma) =
      finiteSquarefreePartition S sigma := by
  rw [finiteSquarefreeLogPartition, finiteSquarefreePartition]
  calc
    Real.exp (∑ p : ↥S, Real.log (1 + squarefreePrimeNome sigma p)) =
        ∏ p : ↥S, Real.exp (Real.log (1 + squarefreePrimeNome sigma p)) := by
      simpa only using Real.exp_sum Finset.univ
        (fun p : ↥S => Real.log (1 + squarefreePrimeNome sigma p))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Real.exp_log]
      linarith [squarefreePrimeNome_pos sigma p]

theorem finiteSquarefreeLogPartition_eq_log
    (S : Finset Nat.Primes) (sigma : ℝ) :
    finiteSquarefreeLogPartition S sigma =
      Real.log (finiteSquarefreePartition S sigma) := by
  rw [← exp_finiteSquarefreeLogPartition S sigma,
    Real.log_exp]

/-- Born law is the Gibbs weight divided by the finite determinant metric. -/
theorem finiteSquarefreeBornWeight_eq
    (S : Finset Nat.Primes) (sigma : ℝ) (x : SquarefreeBitConfig S) :
    finiteSquarefreeBornWeight S sigma x =
      Real.exp (-sigma * finiteSquarefreeHamiltonian S x) /
        finiteSquarefreePartition S sigma := by
  change squarefreeBitWeight S
      (fun i => Real.exp (-sigma * squarefreePrimeEnergy i) /
        (1 + Real.exp (-sigma * squarefreePrimeEnergy i))) x =
    Real.exp (-sigma * squarefreeBitEnergy S squarefreePrimeEnergy x) /
      ∏ i : ↥S, (1 + Real.exp (-sigma * squarefreePrimeEnergy i))
  exact squarefreeBitWeight_logistic_eq S sigma squarefreePrimeEnergy x

/-- Squared source coefficient is exactly the independent squarefree Born law. -/
theorem norm_finiteSquarefreeSourceCoefficient_sq
    (S : Finset Nat.Primes) (sigma : ℝ) (x : SquarefreeBitConfig S) :
    ‖finiteSquarefreeSourceCoefficient S sigma x‖ ^ 2 =
      finiteSquarefreeBornWeight S sigma x := by
  have hsign : ‖(finiteSquarefreeMobiusSign x : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    simp [finiteSquarefreeMobiusSign]
  rw [finiteSquarefreeSourceCoefficient, norm_mul, hsign, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_nat_mul]
  norm_num
  rw [show (2 : ℝ) *
      (-(sigma * finiteSquarefreeHamiltonian S x) / 2 -
        finiteSquarefreeLogPartition S sigma / 2) =
      -sigma * finiteSquarefreeHamiltonian S x -
        finiteSquarefreeLogPartition S sigma by ring]
  rw [Real.exp_sub, exp_finiteSquarefreeLogPartition]
  exact (finiteSquarefreeBornWeight_eq S sigma x).symm

/-- The normalized determinant-line source is a unit vector. -/
theorem norm_finiteSquarefreeSource_sq
    (S : Finset Nat.Primes) (sigma : ℝ) :
    ‖finiteSquarefreeSource S sigma‖ ^ 2 = 1 := by
  rw [finiteSquarefreeSource, EuclideanSpace.norm_sq_eq]
  change ∑ x : SquarefreeBitConfig S,
      ‖finiteSquarefreeSourceCoefficient S sigma x‖ ^ 2 = 1
  simp_rw [norm_finiteSquarefreeSourceCoefficient_sq]
  exact sum_squarefreeBitWeight S (squarefreePrimeOccupation sigma)

theorem norm_finiteSquarefreeSource
    (S : Finset Nat.Primes) (sigma : ℝ) :
    ‖finiteSquarefreeSource S sigma‖ = 1 := by
  nlinarith [norm_finiteSquarefreeSource_sq S sigma,
    norm_nonneg (finiteSquarefreeSource S sigma)]

/-- The unnormalized source metric is exactly `Z_S`. -/
theorem sum_norm_finiteSquarefreeRawSourceCoefficient_sq
    (S : Finset Nat.Primes) (sigma : ℝ) :
    ∑ x : SquarefreeBitConfig S,
        ‖finiteSquarefreeRawSourceCoefficient S sigma x‖ ^ 2 =
      finiteSquarefreePartition S sigma := by
  have hpoint : ∀ x : SquarefreeBitConfig S,
      ‖finiteSquarefreeRawSourceCoefficient S sigma x‖ ^ 2 =
        finiteSquarefreePartition S sigma * finiteSquarefreeBornWeight S sigma x := by
    intro x
    have hsign : ‖(finiteSquarefreeMobiusSign x : ℂ)‖ = 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      simp [finiteSquarefreeMobiusSign]
    rw [finiteSquarefreeRawSourceCoefficient, norm_mul, hsign, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      ← Real.exp_nat_mul]
    norm_num
    rw [show (2 : ℝ) *
        (-(sigma * finiteSquarefreeHamiltonian S x) / 2) =
        -sigma * finiteSquarefreeHamiltonian S x by ring,
      finiteSquarefreeBornWeight_eq]
    field_simp [ne_of_gt (finiteSquarefreePartition_pos S sigma)]
  calc
    _ = ∑ x : SquarefreeBitConfig S,
        finiteSquarefreePartition S sigma * finiteSquarefreeBornWeight S sigma x := by
          apply Finset.sum_congr rfl
          intro x _
          exact hpoint x
    _ = finiteSquarefreePartition S sigma *
        (∑ x : SquarefreeBitConfig S, finiteSquarefreeBornWeight S sigma x) := by
          rw [Finset.mul_sum]
    _ = _ := by
      change finiteSquarefreePartition S sigma *
        (∑ x : SquarefreeBitConfig S,
          squarefreeBitWeight S (squarefreePrimeOccupation sigma) x) = _
      rw [sum_squarefreeBitWeight S (squarefreePrimeOccupation sigma)]
      ring

/-- Normalization is literally division of the raw determinant source by `sqrt Z_S`. -/
theorem finiteSquarefreeSourceCoefficient_eq_raw_div_sqrt_partition
    (S : Finset Nat.Primes) (sigma : ℝ) (x : SquarefreeBitConfig S) :
    finiteSquarefreeSourceCoefficient S sigma x =
      finiteSquarefreeRawSourceCoefficient S sigma x /
        Real.sqrt (finiteSquarefreePartition S sigma) := by
  rw [finiteSquarefreeSourceCoefficient, finiteSquarefreeRawSourceCoefficient]
  change (finiteSquarefreeMobiusSign x : ℂ) *
      (Real.exp (-sigma * finiteSquarefreeHamiltonian S x / 2 -
        finiteSquarefreeLogPartition S sigma / 2) : ℂ) =
    ((finiteSquarefreeMobiusSign x : ℂ) *
      (Real.exp (-sigma * finiteSquarefreeHamiltonian S x / 2) : ℂ)) *
        (Real.sqrt (finiteSquarefreePartition S sigma) : ℂ)⁻¹
  have hsqrt : Real.sqrt (finiteSquarefreePartition S sigma) =
      Real.exp (finiteSquarefreeLogPartition S sigma / 2) := by
    rw [← exp_finiteSquarefreeLogPartition S sigma, ← Real.exp_half]
  have hinv : (Real.sqrt (finiteSquarefreePartition S sigma))⁻¹ =
      Real.exp (-finiteSquarefreeLogPartition S sigma / 2) := by
    rw [hsqrt, ← Real.exp_neg]
    congr 1
    ring
  have hinvC : (Real.sqrt (finiteSquarefreePartition S sigma) : ℂ)⁻¹ =
      (Real.exp (-finiteSquarefreeLogPartition S sigma / 2) : ℂ) := by
    exact_mod_cast hinv
  rw [hinvC, mul_assoc]
  congr 1
  push_cast
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The finite current is the Born expectation of the prime Hamiltonian. -/
theorem finiteSquarefreeCurrent_eq_expectation
    (S : Finset Nat.Primes) (sigma : ℝ) :
    ∑ x : SquarefreeBitConfig S,
        finiteSquarefreeBornWeight S sigma x * finiteSquarefreeHamiltonian S x =
      finiteSquarefreeCurrent S sigma := by
  exact sum_squarefreeBitWeight_mul_energy S
    (squarefreePrimeOccupation sigma) squarefreePrimeEnergy

/-- The finite curvature is exactly the Hamiltonian variance. -/
theorem finiteSquarefreeCurvature_eq_variance
    (S : Finset Nat.Primes) (sigma : ℝ) :
    ∑ x : SquarefreeBitConfig S, finiteSquarefreeBornWeight S sigma x *
        (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma) ^ 2 =
      finiteSquarefreeCurvature S sigma := by
  exact sum_squarefreeBitWeight_mul_centeredEnergy_sq S
    (squarefreePrimeOccupation sigma) squarefreePrimeEnergy

/-- Calibrated tangent norm is exactly `4 (sigma-1)^2 V_S`. -/
theorem norm_finiteSquarefreeTangent_sq
    (S : Finset Nat.Primes) (sigma : ℝ) :
    ‖finiteSquarefreeTangent S sigma‖ ^ 2 =
      4 * (sigma - 1) ^ 2 * finiteSquarefreeCurvature S sigma := by
  rw [finiteSquarefreeTangent, EuclideanSpace.norm_sq_eq]
  change (∑ x : SquarefreeBitConfig S,
    ‖(((-2 * (sigma - 1) *
      (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma) : ℝ) : ℂ) *
      finiteSquarefreeSourceCoefficient S sigma x)‖ ^ 2) = _
  rw [← finiteSquarefreeCurvature_eq_variance]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [norm_mul, mul_pow, norm_finiteSquarefreeSourceCoefficient_sq,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
    mul_pow, mul_pow]
  norm_num
  ring

/-- Centering makes the normalized source line horizontal to its calibrated tangent. -/
theorem inner_finiteSquarefreeSource_tangent_eq_zero
    (S : Finset Nat.Primes) (sigma : ℝ) :
    inner ℂ (finiteSquarefreeSource S sigma)
      (finiteSquarefreeTangent S sigma) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  simp only [finiteSquarefreeSource, finiteSquarefreeTangent, PiLp.toLp_apply,
    Pi.star_apply]
  rw [show (∑ x : SquarefreeBitConfig S,
      (((-2 * (sigma - 1) *
        (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma) : ℝ) : ℂ) *
          finiteSquarefreeSourceCoefficient S sigma x) *
        star (finiteSquarefreeSourceCoefficient S sigma x)) =
      ((-2 * (sigma - 1) : ℝ) : ℂ) *
        ∑ x : SquarefreeBitConfig S,
          ((finiteSquarefreeBornWeight S sigma x *
            (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma) : ℝ) : ℂ) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    have hnorm :
        finiteSquarefreeSourceCoefficient S sigma x *
            star (finiteSquarefreeSourceCoefficient S sigma x) =
          (finiteSquarefreeBornWeight S sigma x : ℂ) := by
      rw [← starRingEnd_apply]
      calc
        _ = ((‖finiteSquarefreeSourceCoefficient S sigma x‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (finiteSquarefreeSourceCoefficient S sigma x)
        _ = _ := by
          rw [← Complex.ofReal_pow,
            norm_finiteSquarefreeSourceCoefficient_sq]
    rw [mul_assoc, hnorm]
    push_cast
    ring]
  rw [← Complex.ofReal_sum]
  have hcentered : (∑ x : SquarefreeBitConfig S,
      finiteSquarefreeBornWeight S sigma x *
        (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma)) = 0 := by
    exact sum_squarefreeBitWeight_mul_centeredEnergy S
      (squarefreePrimeOccupation sigma) squarefreePrimeEnergy
  rw [hcentered]
  simp

/-- Derivative of the local nome. -/
theorem hasDerivAt_squarefreePrimeNome
    (sigma : ℝ) (p : Nat.Primes) :
    HasDerivAt (fun t => squarefreePrimeNome t p)
      (-squarefreePrimeEnergy p * squarefreePrimeNome sigma p) sigma := by
  change HasDerivAt
    (fun t : ℝ => Real.exp (-t * squarefreePrimeEnergy p))
    (-squarefreePrimeEnergy p *
      Real.exp (-sigma * squarefreePrimeEnergy p)) sigma
  have hlin : HasDerivAt (fun t : ℝ => -t * squarefreePrimeEnergy p)
      (-squarefreePrimeEnergy p) sigma := by
    simpa only [id_eq, one_mul, mul_one, mul_neg, neg_mul, mul_comm] using!
      (hasDerivAt_id sigma).const_mul (-squarefreePrimeEnergy p)
  exact hlin.exp.congr_deriv (by ring)

/-- Derivative of the local Bernoulli occupation. -/
theorem hasDerivAt_squarefreePrimeOccupation
    (sigma : ℝ) (p : Nat.Primes) :
    HasDerivAt (fun t => squarefreePrimeOccupation t p)
      (-squarefreePrimeEnergy p * squarefreePrimeOccupation sigma p *
        (1 - squarefreePrimeOccupation sigma p)) sigma := by
  change HasDerivAt
    (fun t => squarefreePrimeNome t p / (1 + squarefreePrimeNome t p))
    (-squarefreePrimeEnergy p *
      (squarefreePrimeNome sigma p / (1 + squarefreePrimeNome sigma p)) *
      (1 - squarefreePrimeNome sigma p / (1 + squarefreePrimeNome sigma p))) sigma
  have hq := hasDerivAt_squarefreePrimeNome sigma p
  have hden : 1 + squarefreePrimeNome sigma p ≠ 0 := by
    linarith [squarefreePrimeNome_pos sigma p]
  have hquot := hq.div (hasDerivAt_const sigma 1 |>.add hq) hden
  have hder :
      (-squarefreePrimeEnergy p * squarefreePrimeNome sigma p *
          (1 + squarefreePrimeNome sigma p) -
        squarefreePrimeNome sigma p *
          (-squarefreePrimeEnergy p * squarefreePrimeNome sigma p)) /
          (1 + squarefreePrimeNome sigma p) ^ 2 =
      -squarefreePrimeEnergy p *
        (squarefreePrimeNome sigma p / (1 + squarefreePrimeNome sigma p)) *
        (1 - squarefreePrimeNome sigma p /
          (1 + squarefreePrimeNome sigma p)) := by
    field_simp [hden]
    ring
  simpa only [Pi.add_apply, Pi.one_apply, zero_add, hder] using! hquot

/-- The determinant connection is `-d log Z_S`. -/
theorem hasDerivAt_finiteSquarefreeLogPartition
    (S : Finset Nat.Primes) (sigma : ℝ) :
    HasDerivAt (finiteSquarefreeLogPartition S)
      (-finiteSquarefreeCurrent S sigma) sigma := by
  change HasDerivAt
    (fun t => ∑ p : ↥S, Real.log (1 + squarefreePrimeNome t p))
    (-(∑ p : ↥S,
      squarefreePrimeOccupation sigma p * squarefreePrimeEnergy p)) sigma
  have hlocal : ∀ p : ↥S,
      HasDerivAt (fun t : ℝ => Real.log (1 + squarefreePrimeNome t p))
        (-squarefreePrimeEnergy p * squarefreePrimeNome sigma p /
          (1 + squarefreePrimeNome sigma p)) sigma := by
    intro p
    have hq := hasDerivAt_squarefreePrimeNome sigma p
    have hden : 1 + squarefreePrimeNome sigma p ≠ 0 := by
      linarith [squarefreePrimeNome_pos sigma p]
    have h := (hasDerivAt_const sigma 1 |>.add hq).log hden
    simpa only [Pi.add_apply, Pi.one_apply, zero_add] using! h
  have hlocal' : ∀ p : ↥S,
      HasDerivAt (fun t : ℝ => Real.log (1 + squarefreePrimeNome t p))
        (-(squarefreePrimeOccupation sigma p * squarefreePrimeEnergy p)) sigma := by
    intro p
    convert hlocal p using 1
    rw [squarefreePrimeOccupation]
    ring
  rw [show (fun t : ℝ =>
      ∑ p : ↥S, Real.log (1 + squarefreePrimeNome t p)) =
      ∑ p : ↥S, (fun t : ℝ => Real.log (1 + squarefreePrimeNome t p)) by
        funext t
        simp]
  simpa only [Finset.sum_neg_distrib] using!
    HasDerivAt.sum (u := Finset.univ) (fun p _ => hlocal' p)

theorem hasDerivAt_log_finiteSquarefreePartition
    (S : Finset Nat.Primes) (sigma : ℝ) :
    HasDerivAt (fun t => Real.log (finiteSquarefreePartition S t))
      (-finiteSquarefreeCurrent S sigma) sigma := by
  convert hasDerivAt_finiteSquarefreeLogPartition S sigma using 1
  funext t
  exact (finiteSquarefreeLogPartition_eq_log S t).symm

/-- The current derivative is minus the Fisher curvature. -/
theorem hasDerivAt_finiteSquarefreeCurrent
    (S : Finset Nat.Primes) (sigma : ℝ) :
    HasDerivAt (finiteSquarefreeCurrent S)
      (-finiteSquarefreeCurvature S sigma) sigma := by
  change HasDerivAt
    (fun t => ∑ p : ↥S,
      squarefreePrimeOccupation t p * squarefreePrimeEnergy p)
    (-(∑ p : ↥S, squarefreePrimeOccupation sigma p *
      (1 - squarefreePrimeOccupation sigma p) * squarefreePrimeEnergy p ^ 2)) sigma
  have hlocal : ∀ p : ↥S,
      HasDerivAt
        (fun t : ℝ => squarefreePrimeOccupation t p * squarefreePrimeEnergy p)
        (-(squarefreePrimeOccupation sigma p *
          (1 - squarefreePrimeOccupation sigma p) * squarefreePrimeEnergy p ^ 2)) sigma := by
    intro p
    apply ((hasDerivAt_squarefreePrimeOccupation sigma p).mul_const
      (squarefreePrimeEnergy p)).congr_deriv
    ring
  rw [show (fun t : ℝ => ∑ p : ↥S,
      squarefreePrimeOccupation t p * squarefreePrimeEnergy p) =
      ∑ p : ↥S, (fun t : ℝ =>
        squarefreePrimeOccupation t p * squarefreePrimeEnergy p) by
          funext t
          simp]
  simpa only [Finset.sum_neg_distrib] using!
    HasDerivAt.sum (u := Finset.univ) (fun p _ => hlocal p)

/-- The normalized projective metric is one quarter of the Fisher curvature. -/
theorem finiteSquarefreeProjectiveMetric_eq
    (S : Finset Nat.Primes) (sigma : ℝ) :
    finiteSquarefreeCurvature S sigma / 4 =
      (1 / 4 : ℝ) * finiteSquarefreeCurvature S sigma := by ring

/-- Uncalibrated derivative coefficient of the unit source. -/
def finiteSquarefreeSourceDerivativeCoefficient
    (S : Finset Nat.Primes) (sigma : ℝ)
    (x : SquarefreeBitConfig S) : ℂ :=
  (((-1 / 2 : ℝ) *
    (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma) : ℝ) : ℂ) *
      finiteSquarefreeSourceCoefficient S sigma x

/-- Uncalibrated derivative vector of the unit source. -/
def finiteSquarefreeSourceDerivative (S : Finset Nat.Primes) (sigma : ℝ) :
    EuclideanSpace ℂ (SquarefreeBitConfig S) :=
  WithLp.toLp 2 (finiteSquarefreeSourceDerivativeCoefficient S sigma)

theorem hasDerivAt_finiteSquarefreeSourceCoefficient
    (S : Finset Nat.Primes) (sigma : ℝ) (x : SquarefreeBitConfig S) :
    HasDerivAt (fun t : ℝ => finiteSquarefreeSourceCoefficient S t x)
      (finiteSquarefreeSourceDerivativeCoefficient S sigma x) sigma := by
  have hexponent : HasDerivAt
      (fun t : ℝ => -t * finiteSquarefreeHamiltonian S x / 2 -
        finiteSquarefreeLogPartition S t / 2)
      ((-1 / 2 : ℝ) *
        (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma)) sigma := by
    have hfirst : HasDerivAt
        (fun t : ℝ => -t * finiteSquarefreeHamiltonian S x / 2)
        (-finiteSquarefreeHamiltonian S x / 2) sigma := by
      simpa only [id_eq, one_mul, mul_one, mul_neg, neg_mul, mul_comm] using!
        ((hasDerivAt_id sigma).const_mul
          (-finiteSquarefreeHamiltonian S x) |>.div_const 2)
    exact (hfirst.sub
      ((hasDerivAt_finiteSquarefreeLogPartition S sigma).div_const 2)).congr_deriv
        (by ring)
  have hexp := hexponent.exp
  have hcast := hexp.ofReal_comp
  rw [show (fun t : ℝ => finiteSquarefreeSourceCoefficient S t x) =
      fun t : ℝ => (finiteSquarefreeMobiusSign x : ℂ) *
        (Real.exp (-t * finiteSquarefreeHamiltonian S x / 2 -
          finiteSquarefreeLogPartition S t / 2) : ℂ) by rfl]
  apply (hcast.const_mul (finiteSquarefreeMobiusSign x : ℂ)).congr_deriv
  rw [finiteSquarefreeSourceDerivativeCoefficient,
    finiteSquarefreeSourceCoefficient]
  push_cast
  ring

/-- The explicit coefficient derivative is the actual derivative in finite tensor Hilbert space. -/
theorem hasDerivAt_finiteSquarefreeSource
    (S : Finset Nat.Primes) (sigma : ℝ) :
    HasDerivAt (finiteSquarefreeSource S)
      (finiteSquarefreeSourceDerivative S sigma) sigma := by
  rw [hasDerivAt_iff_hasFDerivAt, ← hasFDerivWithinAt_univ]
  apply (hasFDerivWithinAt_piLp (p := (2 : ENNReal))).2
  intro x
  have hx :=
    (hasDerivAt_finiteSquarefreeSourceCoefficient S sigma x).hasFDerivAt.hasFDerivWithinAt
      (s := Set.univ)
  simpa only [finiteSquarefreeSource, finiteSquarefreeSourceDerivative,
    PiLp.toLp_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using! hx

/-- Exact covariant-derivative calibration `chi_S = 4 (sigma-1) nabla psi_S`. -/
theorem finiteSquarefreeTangent_eq_four_mul_sourceDerivative
    (S : Finset Nat.Primes) (sigma : ℝ) :
    finiteSquarefreeTangent S sigma =
      (4 * (sigma - 1) : ℝ) • finiteSquarefreeSourceDerivative S sigma := by
  apply PiLp.ext
  intro x
  simp only [finiteSquarefreeTangent, finiteSquarefreeSourceDerivative,
    finiteSquarefreeSourceDerivativeCoefficient, PiLp.toLp_apply,
    PiLp.smul_apply, Complex.real_smul]
  push_cast
  ring

/-! ## Exact adjacent-prime boundary colligation -/

theorem squarefreeBitMean_insert
    {α : Type*} [DecidableEq α] {S : Finset α} {a : α}
    (ha : a ∉ S) (r energy : α → ℝ) :
    squarefreeBitMean (insert a S) r energy =
      r a * energy a + squarefreeBitMean S r energy := by
  rw [squarefreeBitMean, squarefreeBitMean]
  rw [Fintype.sum_equiv (Finset.subtypeInsertEquivOption ha)
    (fun i : ↥(insert a S) => r i * energy i)
    (fun o : Option ↥S => match o with
      | none => r a * energy a
      | some i => r i * energy i)
    (fun i => by
      by_cases hia : (i : α) = a
      · simp [Finset.subtypeInsertEquivOption, hia]
      · simp [Finset.subtypeInsertEquivOption, hia])]
  simp

theorem squarefreeBitVariance_insert
    {α : Type*} [DecidableEq α] {S : Finset α} {a : α}
    (ha : a ∉ S) (r energy : α → ℝ) :
    squarefreeBitVariance (insert a S) r energy =
      r a * (1 - r a) * energy a ^ 2 +
        squarefreeBitVariance S r energy := by
  rw [squarefreeBitVariance, squarefreeBitVariance]
  rw [Fintype.sum_equiv (Finset.subtypeInsertEquivOption ha)
    (fun i : ↥(insert a S) => r i * (1 - r i) * energy i ^ 2)
    (fun o : Option ↥S => match o with
      | none => r a * (1 - r a) * energy a ^ 2
      | some i => r i * (1 - r i) * energy i ^ 2)
    (fun i => by
      by_cases hia : (i : α) = a
      · simp [Finset.subtypeInsertEquivOption, hia]
      · simp [Finset.subtypeInsertEquivOption, hia])]
  simp

theorem finiteSquarefreeLogPartition_insert
    {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S) (sigma : ℝ) :
    finiteSquarefreeLogPartition (insert p S) sigma =
      Real.log (1 + squarefreePrimeNome sigma p) +
        finiteSquarefreeLogPartition S sigma := by
  rw [finiteSquarefreeLogPartition, finiteSquarefreeLogPartition]
  rw [Fintype.sum_equiv (Finset.subtypeInsertEquivOption hp)
    (fun i : ↥(insert p S) => Real.log (1 + squarefreePrimeNome sigma i))
    (fun o : Option ↥S => match o with
      | none => Real.log (1 + squarefreePrimeNome sigma p)
      | some i => Real.log (1 + squarefreePrimeNome sigma i))
    (fun i => by
      by_cases hip : (i : Nat.Primes) = p
      · simp [Finset.subtypeInsertEquivOption, hip]
      · simp [Finset.subtypeInsertEquivOption, hip])]
  simp

theorem finiteSquarefreeCurrent_insert
    {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S) (sigma : ℝ) :
    finiteSquarefreeCurrent (insert p S) sigma =
      finiteSquarefreeCurrent S sigma +
        squarefreePrimeEnergy p * squarefreePrimeOccupation sigma p := by
  rw [finiteSquarefreeCurrent, finiteSquarefreeCurrent,
    squarefreeBitMean_insert hp]
  ring

theorem finiteSquarefreeCurvature_insert
    {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S) (sigma : ℝ) :
    finiteSquarefreeCurvature (insert p S) sigma =
      finiteSquarefreeCurvature S sigma +
        squarefreePrimeEnergy p ^ 2 * squarefreePrimeNome sigma p /
          (1 + squarefreePrimeNome sigma p) ^ 2 := by
  rw [finiteSquarefreeCurvature, finiteSquarefreeCurvature,
    squarefreeBitVariance_insert hp]
  rw [squarefreePrimeOccupation]
  have hden : 1 + squarefreePrimeNome sigma p ≠ 0 := by
    linarith [squarefreePrimeNome_pos sigma p]
  field_simp [hden]
  ring

/-- Normalized one-prime source symbol `v_p`. -/
def squarefreePrimeSourceCoefficient
    (sigma : ℝ) (p : Nat.Primes) (b : Fin 2) : ℂ :=
  (((-1 : ℝ) ^ (b : ℕ) : ℝ) : ℂ) *
    Real.exp (-sigma * ((b : ℕ) : ℝ) * squarefreePrimeEnergy p / 2 -
      Real.log (1 + squarefreePrimeNome sigma p) / 2)

/-- Horizontal outgoing one-prime tangent `chi_p`. -/
def squarefreePrimeTangentCoefficient
    (sigma : ℝ) (p : Nat.Primes) (b : Fin 2) : ℂ :=
  ((-2 * (sigma - 1) * squarefreePrimeEnergy p *
    (((b : ℕ) : ℝ) - squarefreePrimeOccupation sigma p) : ℝ) : ℂ) *
      squarefreePrimeSourceCoefficient sigma p b

def squarefreePrimeSource (sigma : ℝ) (p : Nat.Primes) :
    EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (squarefreePrimeSourceCoefficient sigma p)

def squarefreePrimeTangent (sigma : ℝ) (p : Nat.Primes) :
    EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (squarefreePrimeTangentCoefficient sigma p)

theorem norm_squarefreePrimeSourceCoefficient_sq
    (sigma : ℝ) (p : Nat.Primes) (b : Fin 2) :
    ‖squarefreePrimeSourceCoefficient sigma p b‖ ^ 2 =
      if b = 0 then 1 - squarefreePrimeOccupation sigma p
      else squarefreePrimeOccupation sigma p := by
  have hsign : ‖((((-1 : ℝ) ^ (b : ℕ) : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    simp
  rw [squarefreePrimeSourceCoefficient, norm_mul, hsign, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ← Real.exp_nat_mul]
  norm_num
  by_cases hb : b = 0
  · subst b
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_mul, if_pos]
    rw [show (2 : ℝ) *
      (-0 / 2 - Real.log (1 + squarefreePrimeNome sigma p) / 2) =
      -Real.log (1 + squarefreePrimeNome sigma p) by ring]
    rw [Real.exp_neg, Real.exp_log]
    · rw [squarefreePrimeOccupation]
      have hden : 1 + squarefreePrimeNome sigma p ≠ 0 := by
        linarith [squarefreePrimeNome_pos sigma p]
      field_simp [hden]
      ring
    · linarith [squarefreePrimeNome_pos sigma p]
  · rw [Fin.eq_one_of_ne_zero b hb]
    simp only [Fin.val_one, Nat.cast_one,
      show (1 : Fin 2) ≠ 0 by decide, if_false]
    rw [show (2 : ℝ) *
      (-(sigma * 1 * squarefreePrimeEnergy p) / 2 -
        Real.log (1 + squarefreePrimeNome sigma p) / 2) =
      -sigma * squarefreePrimeEnergy p -
        Real.log (1 + squarefreePrimeNome sigma p) by ring,
      Real.exp_sub, Real.exp_log]
    · rw [← squarefreePrimeNome_eq_exp, squarefreePrimeOccupation]
    · linarith [squarefreePrimeNome_pos sigma p]

theorem norm_squarefreePrimeSource_sq (sigma : ℝ) (p : Nat.Primes) :
    ‖squarefreePrimeSource sigma p‖ ^ 2 = 1 := by
  rw [squarefreePrimeSource, EuclideanSpace.norm_sq_eq]
  change ∑ b : Fin 2, ‖squarefreePrimeSourceCoefficient sigma p b‖ ^ 2 = 1
  rw [Fin.sum_univ_two]
  simp [norm_squarefreePrimeSourceCoefficient_sq]

/-- The new-prime source symbol is horizontal to its outgoing tangent. -/
theorem inner_squarefreePrimeSource_tangent_eq_zero
    (sigma : ℝ) (p : Nat.Primes) :
    inner ℂ (squarefreePrimeSource sigma p)
      (squarefreePrimeTangent sigma p) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  simp only [squarefreePrimeSource, squarefreePrimeTangent, PiLp.toLp_apply,
    squarefreePrimeTangentCoefficient, Pi.star_apply]
  rw [Fin.sum_univ_two]
  have hnorm (b : Fin 2) :
      squarefreePrimeSourceCoefficient sigma p b *
          star (squarefreePrimeSourceCoefficient sigma p b) =
        ((if b = 0 then 1 - squarefreePrimeOccupation sigma p
          else squarefreePrimeOccupation sigma p : ℝ) : ℂ) := by
    rw [← starRingEnd_apply]
    calc
      _ = ((‖squarefreePrimeSourceCoefficient sigma p b‖ : ℂ) ^ 2) :=
        RCLike.mul_conj (squarefreePrimeSourceCoefficient sigma p b)
      _ = _ := by
        rw [← Complex.ofReal_pow,
          norm_squarefreePrimeSourceCoefficient_sq]
  simp only [mul_assoc, hnorm]
  simp only [Fin.val_zero, Nat.cast_zero, Fin.val_one, Nat.cast_one,
    if_pos, show (1 : Fin 2) ≠ 0 by decide, if_false]
  push_cast
  ring_nf

/-- Exact one-prime Fisher energy of the outgoing transverse tangent. -/
theorem norm_squarefreePrimeTangent_sq
    (sigma : ℝ) (p : Nat.Primes) :
    ‖squarefreePrimeTangent sigma p‖ ^ 2 =
      4 * (sigma - 1) ^ 2 * squarefreePrimeEnergy p ^ 2 *
        squarefreePrimeOccupation sigma p *
          (1 - squarefreePrimeOccupation sigma p) := by
  rw [squarefreePrimeTangent, EuclideanSpace.norm_sq_eq]
  change (∑ b : Fin 2,
      ‖squarefreePrimeTangentCoefficient sigma p b‖ ^ 2) = _
  rw [Fin.sum_univ_two]
  simp only [squarefreePrimeTangentCoefficient, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs,
    norm_squarefreePrimeSourceCoefficient_sq, Fin.val_zero, Nat.cast_zero,
    Fin.val_one, Nat.cast_one, if_pos,
    show (1 : Fin 2) ≠ 0 by decide, if_false, sq_abs]
  ring_nf

theorem norm_squarefreePrimeTangent_sq_eq_nome
    (sigma : ℝ) (p : Nat.Primes) :
    ‖squarefreePrimeTangent sigma p‖ ^ 2 =
      4 * (sigma - 1) ^ 2 * squarefreePrimeEnergy p ^ 2 *
        squarefreePrimeNome sigma p /
          (1 + squarefreePrimeNome sigma p) ^ 2 := by
  rw [norm_squarefreePrimeTangent_sq, squarefreePrimeOccupation]
  have hden : 1 + squarefreePrimeNome sigma p ≠ 0 := by
    linarith [squarefreePrimeNome_pos sigma p]
  field_simp [hden]
  ring

theorem finiteSquarefreeHamiltonian_insert_symm
    {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S)
    (b : Fin 2) (x : SquarefreeBitConfig S) :
    finiteSquarefreeHamiltonian (insert p S)
        ((squarefreeInsertBitEquiv hp).symm (b, x)) =
      ((b : ℕ) : ℝ) * squarefreePrimeEnergy p +
        finiteSquarefreeHamiltonian S x :=
  squarefreeBitEnergy_insert_symm hp squarefreePrimeEnergy b x

theorem finiteSquarefreeMobiusSign_insert_symm
    {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S)
    (b : Fin 2) (x : SquarefreeBitConfig S) :
    finiteSquarefreeMobiusSign
        ((squarefreeInsertBitEquiv hp).symm (b, x)) =
      (-1 : ℝ) ^ (b : ℕ) * finiteSquarefreeMobiusSign x := by
  rw [finiteSquarefreeMobiusSign, finiteSquarefreeMobiusSign]
  have hsum := squarefreeBitEnergy_insert_symm hp (fun _ => (1 : ℝ)) b x
  simp only [squarefreeBitEnergy, mul_one] at hsum
  have hnat :
      (∑ i : ↥(insert p S),
        ((((squarefreeInsertBitEquiv hp).symm (b, x)) i : ℕ))) =
      (b : ℕ) + ∑ i : ↥S, (x i : ℕ) := by
    exact_mod_cast hsum
  rw [hnat, pow_add]

/-- Exact source tensor factorization under insertion of one prime. -/
theorem finiteSquarefreeSourceCoefficient_insert_symm
    {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S)
    (sigma : ℝ) (b : Fin 2) (x : SquarefreeBitConfig S) :
    finiteSquarefreeSourceCoefficient (insert p S) sigma
        ((squarefreeInsertBitEquiv hp).symm (b, x)) =
      finiteSquarefreeSourceCoefficient S sigma x *
        squarefreePrimeSourceCoefficient sigma p b := by
  rw [finiteSquarefreeSourceCoefficient,
    finiteSquarefreeSourceCoefficient, squarefreePrimeSourceCoefficient,
    finiteSquarefreeHamiltonian_insert_symm hp,
    finiteSquarefreeMobiusSign_insert_symm hp,
    finiteSquarefreeLogPartition_insert hp]
  push_cast
  rw [show
    -(sigma : ℂ) * (((b : ℕ) : ℂ) * (squarefreePrimeEnergy p : ℂ) +
        (finiteSquarefreeHamiltonian S x : ℂ)) / 2 -
      ((Real.log (1 + squarefreePrimeNome sigma p) : ℂ) +
        (finiteSquarefreeLogPartition S sigma : ℂ)) / 2 =
      (-((sigma : ℂ) * (finiteSquarefreeHamiltonian S x : ℂ)) / 2 -
        (finiteSquarefreeLogPartition S sigma : ℂ) / 2) +
      (-((sigma : ℂ) * ((b : ℕ) : ℂ) * (squarefreePrimeEnergy p : ℂ)) / 2 -
        (Real.log (1 + squarefreePrimeNome sigma p) : ℂ) / 2) by ring,
    Complex.exp_add]
  ring

/-- Exact tangent Leibniz/colligation identity in prime tensor coordinates. -/
theorem finiteSquarefreeTangent_insert_symm
    {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S)
    (sigma : ℝ) (b : Fin 2) (x : SquarefreeBitConfig S) :
    finiteSquarefreeTangent (insert p S) sigma
        ((squarefreeInsertBitEquiv hp).symm (b, x)) =
      finiteSquarefreeTangent S sigma x *
          squarefreePrimeSourceCoefficient sigma p b +
        finiteSquarefreeSourceCoefficient S sigma x *
          squarefreePrimeTangentCoefficient sigma p b := by
  simp only [finiteSquarefreeTangent, PiLp.toLp_apply,
    squarefreePrimeTangentCoefficient,
    finiteSquarefreeHamiltonian_insert_symm hp,
    finiteSquarefreeCurrent_insert hp,
    finiteSquarefreeSourceCoefficient_insert_symm hp]
  push_cast
  ring

/-! ## Actual tensor branches and one-dimensional transverse width -/

/-- Coordinate tensor product, pulled back through the insert-one-prime equivalence. -/
def squarefreeTensorPullback
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (e : K ≃ J × I) (u : EuclideanSpace ℂ I) (v : EuclideanSpace ℂ J) :
    EuclideanSpace ℂ K :=
  WithLp.toLp 2 fun k => u (e k).2 * v (e k).1

/-- Hermitian products factor exactly under the coordinate tensor pullback. -/
theorem inner_squarefreeTensorPullback
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (e : K ≃ J × I)
    (u u' : EuclideanSpace ℂ I) (v v' : EuclideanSpace ℂ J) :
    inner ℂ (squarefreeTensorPullback e u v)
        (squarefreeTensorPullback e u' v') =
      inner ℂ u u' * inner ℂ v v' := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  simp only [squarefreeTensorPullback, PiLp.toLp_apply, Pi.star_apply, star_mul]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, dotProduct]
  simp only [Pi.star_apply]
  calc
    (∑ j, ∑ i, (u' i * v' j) * (star (v j) * star (u i))) =
        ∑ j, (∑ i, u' i * star (u i)) * (v' j * star (v j)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (∑ i, u' i * star (u i)) *
        (∑ j, v' j * star (v j)) := by
      rw [Finset.mul_sum]

/-- Squared norms multiply exactly under the coordinate tensor pullback. -/
theorem norm_squarefreeTensorPullback_sq
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (e : K ≃ J × I) (u : EuclideanSpace ℂ I) (v : EuclideanSpace ℂ J) :
    ‖squarefreeTensorPullback e u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp only [squarefreeTensorPullback, PiLp.toLp_apply, norm_mul, mul_pow]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  calc
    (∑ j, ∑ i, ‖u i‖ ^ 2 * ‖v j‖ ^ 2) =
        ∑ j, (∑ i, ‖u i‖ ^ 2) * ‖v j‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
    _ = (∑ i, ‖u i‖ ^ 2) * (∑ j, ‖v j‖ ^ 2) := by
      rw [Finset.mul_sum]

/-- Lower-system part of the enlarged horizontal tangent. -/
def finiteSquarefreeLowerTangentBranch
    {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S) (sigma : ℝ) :
    EuclideanSpace ℂ (SquarefreeBitConfig (insert p S)) :=
  squarefreeTensorPullback (squarefreeInsertBitEquiv hp)
    (finiteSquarefreeTangent S sigma) (squarefreePrimeSource sigma p)

/-- New-prime outgoing part of the enlarged horizontal tangent. -/
def finiteSquarefreePrimeTangentBranch
    {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S) (sigma : ℝ) :
    EuclideanSpace ℂ (SquarefreeBitConfig (insert p S)) :=
  squarefreeTensorPullback (squarefreeInsertBitEquiv hp)
    (finiteSquarefreeSource S sigma) (squarefreePrimeTangent sigma p)

/-- Equation (9): the enlarged normalized source is the exact source tensor product. -/
theorem finiteSquarefreeSource_insert
    {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S) (sigma : ℝ) :
    finiteSquarefreeSource (insert p S) sigma =
      squarefreeTensorPullback (squarefreeInsertBitEquiv hp)
        (finiteSquarefreeSource S sigma) (squarefreePrimeSource sigma p) := by
  apply PiLp.ext
  intro y
  change finiteSquarefreeSourceCoefficient (insert p S) sigma y =
    finiteSquarefreeSourceCoefficient S sigma
        ((squarefreeInsertBitEquiv hp y).2) *
      squarefreePrimeSourceCoefficient sigma p
        ((squarefreeInsertBitEquiv hp y).1)
  have h := finiteSquarefreeSourceCoefficient_insert_symm hp sigma
    (squarefreeInsertBitEquiv hp y).1 (squarefreeInsertBitEquiv hp y).2
  have hy : (squarefreeInsertBitEquiv hp).symm
      ((squarefreeInsertBitEquiv hp y).1,
        (squarefreeInsertBitEquiv hp y).2) = y := by
    rw [show ((squarefreeInsertBitEquiv hp y).1,
      (squarefreeInsertBitEquiv hp y).2) = squarefreeInsertBitEquiv hp y by rfl,
      Equiv.symm_apply_apply]
  rwa [hy] at h

/-- Equation (10): exact vector-valued adjacent-prime tangent colligation. -/
theorem finiteSquarefreeTangent_insert
    {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S) (sigma : ℝ) :
    finiteSquarefreeTangent (insert p S) sigma =
      finiteSquarefreeLowerTangentBranch hp sigma +
        finiteSquarefreePrimeTangentBranch hp sigma := by
  apply PiLp.ext
  intro y
  change finiteSquarefreeTangent (insert p S) sigma y =
    finiteSquarefreeTangent S sigma ((squarefreeInsertBitEquiv hp y).2) *
        squarefreePrimeSourceCoefficient sigma p
          ((squarefreeInsertBitEquiv hp y).1) +
      finiteSquarefreeSourceCoefficient S sigma
          ((squarefreeInsertBitEquiv hp y).2) *
        squarefreePrimeTangentCoefficient sigma p
          ((squarefreeInsertBitEquiv hp y).1)
  have h := finiteSquarefreeTangent_insert_symm hp sigma
    (squarefreeInsertBitEquiv hp y).1 (squarefreeInsertBitEquiv hp y).2
  have hy : (squarefreeInsertBitEquiv hp).symm
      ((squarefreeInsertBitEquiv hp y).1,
        (squarefreeInsertBitEquiv hp y).2) = y := by
    rw [show ((squarefreeInsertBitEquiv hp y).1,
      (squarefreeInsertBitEquiv hp y).2) = squarefreeInsertBitEquiv hp y by rfl,
      Equiv.symm_apply_apply]
  rwa [hy] at h

/-- The two actual tangent branches in the colligation are orthogonal. -/
theorem inner_finiteSquarefreeTangentBranches_eq_zero
    {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S) (sigma : ℝ) :
    inner ℂ (finiteSquarefreeLowerTangentBranch hp sigma)
      (finiteSquarefreePrimeTangentBranch hp sigma) = 0 := by
  rw [finiteSquarefreeLowerTangentBranch, finiteSquarefreePrimeTangentBranch,
    inner_squarefreeTensorPullback,
    inner_squarefreePrimeSource_tangent_eq_zero]
  simp

/-- Equation (11): the vector colligation obeys the exact one-particle Pythagorean law. -/
theorem norm_finiteSquarefreeTangent_insert_sq
    {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S) (sigma : ℝ) :
    ‖finiteSquarefreeTangent (insert p S) sigma‖ ^ 2 =
      ‖finiteSquarefreeTangent S sigma‖ ^ 2 +
        ‖squarefreePrimeTangent sigma p‖ ^ 2 := by
  rw [finiteSquarefreeTangent_insert hp]
  calc
    ‖finiteSquarefreeLowerTangentBranch hp sigma +
        finiteSquarefreePrimeTangentBranch hp sigma‖ ^ 2 =
      ‖finiteSquarefreeLowerTangentBranch hp sigma‖ ^ 2 +
        ‖finiteSquarefreePrimeTangentBranch hp sigma‖ ^ 2 := by
          simpa only [pow_two] using
            norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
              (finiteSquarefreeLowerTangentBranch hp sigma)
              (finiteSquarefreePrimeTangentBranch hp sigma)
              (inner_finiteSquarefreeTangentBranches_eq_zero hp sigma)
    _ = _ := by
      rw [finiteSquarefreeLowerTangentBranch,
        finiteSquarefreePrimeTangentBranch,
        norm_squarefreeTensorPullback_sq,
        norm_squarefreeTensorPullback_sq,
        norm_finiteSquarefreeSource_sq,
        norm_squarefreePrimeSource_sq]
      ring

/-- For `sigma > 1`, every local outgoing tangent is genuinely nonzero. -/
theorem squarefreePrimeTangent_ne_zero
    {sigma : ℝ} (hsigma : 1 < sigma) (p : Nat.Primes) :
    squarefreePrimeTangent sigma p ≠ 0 := by
  have henergy : 0 < squarefreePrimeEnergy p := by
    exact Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hepsilon : 0 < sigma - 1 := sub_pos.mpr hsigma
  have hnome : 0 < squarefreePrimeNome sigma p :=
    squarefreePrimeNome_pos sigma p
  have hden : 0 < 1 + squarefreePrimeNome sigma p := by linarith
  have hnorm : 0 < ‖squarefreePrimeTangent sigma p‖ ^ 2 := by
    rw [norm_squarefreePrimeTangent_sq_eq_nome]
    positivity
  intro hzero
  rw [hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hnorm
  exact (lt_irrefl 0 hnorm)

/-- Uniform transverse width is exactly one at every prime aperture. -/
theorem squarefreePrimeTransverseWidth_eq_one
    {sigma : ℝ} (hsigma : 1 < sigma) (p : Nat.Primes) :
    Module.finrank ℂ (ℂ ∙ squarefreePrimeTangent sigma p) = 1 :=
  finrank_span_singleton (squarefreePrimeTangent_ne_zero hsigma p)

end RHTower
