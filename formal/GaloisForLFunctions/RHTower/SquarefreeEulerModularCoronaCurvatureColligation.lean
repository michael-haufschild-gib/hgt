import GaloisForLFunctions.RHTower.MobiusChannelCriticalMassEscape
import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentHilbertLift
import GaloisForLFunctions.RHTower.MobiusIncidenceClockGiniFisherFourUnit
import GaloisForLFunctions.RHTower.EulerLaurentResidueDouble
import GaloisForLFunctions.RHTower.EulerFisherCurvature
import GaloisForLFunctions.RHTower.HighExponentShellOrthogonalDivisorReplication
import GaloisForLFunctions.RHTower.MobiusPlueckerNormalConeDiagonalLift
import GaloisForLFunctions.RHTower.SquarefreeFixedCurrentLocalization
import GaloisForLFunctions.RHTower.FredholmDeterminantZeta
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
    convert (hasDerivAt_id sigma).const_mul (-squarefreePrimeEnergy p) using 1
    · funext t
      ring
    · ring
  convert hlin.exp using 1 <;> ring

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
  simpa only [Pi.add_apply, Pi.one_apply, zero_add, hder] using hquot

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
    change HasDerivAt
      (fun t : ℝ => Real.log (1 + squarefreePrimeNome t p))
      ((-squarefreePrimeEnergy p * squarefreePrimeNome sigma p) /
        (1 + squarefreePrimeNome sigma p)) sigma at h
    convert h using 1
    ring
  have hlocal' : ∀ p : ↥S,
      HasDerivAt (fun t : ℝ => Real.log (1 + squarefreePrimeNome t p))
        (-(squarefreePrimeOccupation sigma p * squarefreePrimeEnergy p)) sigma := by
    intro p
    convert hlocal p using 1
    rw [squarefreePrimeOccupation]
    ring
  simpa only [Finset.sum_neg_distrib] using
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
    convert (hasDerivAt_squarefreePrimeOccupation sigma p).mul_const
      (squarefreePrimeEnergy p) using 1
    ring
  simpa only [Finset.sum_neg_distrib] using
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
      convert ((hasDerivAt_id sigma).const_mul
        (-finiteSquarefreeHamiltonian S x) |>.div_const 2) using 1
      · funext t
        ring
      · ring
    convert hfirst.sub
      ((hasDerivAt_finiteSquarefreeLogPartition S sigma).div_const 2) using 1
    ring
  have hexp := hexponent.exp
  have hcast := hexp.ofReal_comp
  change HasDerivAt
    (fun t : ℝ => (finiteSquarefreeMobiusSign x : ℂ) *
      (Real.exp (-t * finiteSquarefreeHamiltonian S x / 2 -
        finiteSquarefreeLogPartition S t / 2) : ℂ))
    (finiteSquarefreeSourceDerivativeCoefficient S sigma x) sigma
  convert hcast.const_mul (finiteSquarefreeMobiusSign x : ℂ) using 1
  change ((-1 / 2 : ℝ) *
      (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma) : ℂ) *
        ((finiteSquarefreeMobiusSign x : ℂ) *
          (Real.exp (-sigma * finiteSquarefreeHamiltonian S x / 2 -
            finiteSquarefreeLogPartition S sigma / 2) : ℂ)) = _
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
  simpa only [finiteSquarefreeSource, finiteSquarefreeSourceDerivative,
    PiLp.toLp_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hx

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

end RHTower
