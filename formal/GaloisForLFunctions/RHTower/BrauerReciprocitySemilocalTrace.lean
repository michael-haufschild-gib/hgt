/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntCircleCharacter
import GaloisForLFunctions.RHTower.ConnesTateFiniteStage
import GaloisForLFunctions.RHTower.SoninSemilocalPoissonExpansion
import GaloisForLFunctions.RHTower.PadicBrauerUnramifiedTate

/-!
# ABHN reciprocity transported to semilocal Tate trace and positivity

A finite prime profile carries local `ℚ/ℤ` Brauer invariants together with their zero-sum
reciprocity proof. The standard circle character turns this into a product-one holonomy law.
Those phases twist an actual finite Connes--Tate integral. Its Hermitian square is a strictly
positive product of inverse Euler densities and has an exact bilateral Poisson expansion.

Reciprocity contributes the nontrivial phase cancellation in the product of critical weights.
Strict positivity itself comes from taking a Hermitian square; this module does not identify that
positive density with the global Weil distribution and therefore does not assert RH.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry.ABHN
open _root_.RHTower

/-- Finite nonarchimedean invariant profile carrying global reciprocity as data. -/
structure ReciprocalFinitePrimeBrauerProfile (n : ℕ) where
  prime : Fin n → Nat.Primes
  invariant : Fin n → RatModInt
  reciprocity : ∑ i, invariant i = 0

namespace ReciprocalFinitePrimeBrauerProfile

variable {n : ℕ} (B : ReciprocalFinitePrimeBrauerProfile n)

/-- Local unit-circle phase selected by the local Brauer invariant. -/
noncomputable def brauerPhase (i : Fin n) : ℂ :=
  ratModIntStdAddChar (B.invariant i)

theorem norm_brauerPhase (i : Fin n) : ‖B.brauerPhase i‖ = 1 := by
  change ‖((Circle.coeHom.compAddChar
    (AddCircle.toCircle_addChar.compAddMonoidHom ratModIntToUnitAddCircle))
      (B.invariant i) : ℂ)‖ = 1
  exact Circle.norm_coe _

/-- Additive ABHN reciprocity is the multiplicative product-one phase law. -/
theorem prod_brauerPhase_eq_one : ∏ i, B.brauerPhase i = 1 := by
  classical
  have hmap : ratModIntStdAddChar (∑ i, B.invariant i) =
      ∏ i, ratModIntStdAddChar (B.invariant i) := by
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha,
          ratModIntStdAddChar.map_add_eq_mul, ih]
  change (∏ i, ratModIntStdAddChar (B.invariant i)) = 1
  rw [← hmap, B.reciprocity]
  exact ratModIntStdAddChar.map_zero_eq_one

/-- Critical-line unit phase: Brauer holonomy times prime logarithmic rotation. -/
noncomputable def criticalPhase (t : ℝ) (i : Fin n) : ℂ :=
  B.brauerPhase i * semilocalPrimePhase (B.prime i) t

theorem norm_criticalPhase (t : ℝ) (i : Fin n) :
    ‖B.criticalPhase t i‖ = 1 := by
  rw [criticalPhase, norm_mul, B.norm_brauerPhase,
    norm_semilocalPrimePhase, one_mul]

/-- Critical-line Euler weight with radial part `p⁻¹/²`. -/
noncomputable def criticalWeight (t : ℝ) (i : Fin n) : ℂ :=
  (semilocalPrimePoissonRatio (B.prime i) : ℂ) * B.criticalPhase t i

theorem norm_criticalWeight_lt_one (t : ℝ) (i : Fin n) :
    ‖B.criticalWeight t i‖ < 1 := by
  rw [criticalWeight, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (semilocalPrimePoissonRatio_pos (B.prime i).property).le,
    B.norm_criticalPhase, mul_one]
  exact semilocalPrimePoissonRatio_lt_one (B.prime i).property

/-- Actual finite-product Connes--Tate integral twisted by the reciprocal Brauer phases. -/
noncomputable def tateTrace (t : ℝ) : ℂ :=
  ∫ x : (i : Fin n) → ℚ_[((B.prime i : Nat.Primes) : ℕ)]ˣ,
    ∏ i, connesPadicRadial ((B.prime i : Nat.Primes) : ℕ)
      (connesPadicUnitBallProfile (B.criticalWeight t i)) (x i)
    ∂(Measure.pi fun i =>
      fieldOnePadicMultiplicativeHaar ((B.prime i : Nat.Primes) : ℕ))

/-- Reciprocal Brauer trace is the corresponding finite twisted Euler product. -/
theorem tateTrace_eq_eulerProduct (t : ℝ) :
    B.tateTrace t = ∏ i, (1 - B.criticalWeight t i)⁻¹ := by
  exact connes_tate_finiteStage_prod B.prime (B.criticalWeight t)
    (B.norm_criticalWeight_lt_one t)

/-- Reciprocity cancels total Brauer holonomy from the product of critical weights. -/
theorem prod_criticalWeight_eq_radial_mul_primePhase (t : ℝ) :
    ∏ i, B.criticalWeight t i =
      (∏ i, (semilocalPrimePoissonRatio (B.prime i) : ℂ)) *
        ∏ i, semilocalPrimePhase (B.prime i) t := by
  classical
  rw [show (∏ i, B.criticalWeight t i) =
      (∏ i, (semilocalPrimePoissonRatio (B.prime i) : ℂ)) *
        ∏ i, B.criticalPhase t i by
    simp only [criticalWeight, Finset.prod_mul_distrib]]
  rw [show (∏ i, B.criticalPhase t i) =
      (∏ i, B.brauerPhase i) *
        ∏ i, semilocalPrimePhase (B.prime i) t by
    simp only [criticalPhase, Finset.prod_mul_distrib]]
  rw [B.prod_brauerPhase_eq_one, one_mul]

/-- Hermitian Euler density attached to the actual Tate trace. -/
noncomputable def tateDensity (t : ℝ) : ℝ :=
  ∏ i, (Complex.normSq (1 - B.criticalWeight t i))⁻¹

theorem one_sub_criticalWeight_ne_zero (t : ℝ) (i : Fin n) :
    1 - B.criticalWeight t i ≠ 0 := by
  intro hzero
  have hone : B.criticalWeight t i = 1 := (sub_eq_zero.mp hzero).symm
  have hlt := B.norm_criticalWeight_lt_one t i
  rw [hone, norm_one] at hlt
  exact (lt_irrefl 1 hlt)

theorem tateDensity_pos (t : ℝ) : 0 < B.tateDensity t := by
  classical
  unfold tateDensity
  apply Finset.prod_pos
  intro i _
  exact inv_pos.mpr (Complex.normSq_pos.mpr (B.one_sub_criticalWeight_ne_zero t i))

theorem normSq_tateTrace_eq_tateDensity (t : ℝ) :
    Complex.normSq (B.tateTrace t) = B.tateDensity t := by
  rw [B.tateTrace_eq_eulerProduct]
  classical
  have hprod : ∀ s : Finset (Fin n),
      Complex.normSq (∏ i ∈ s, (1 - B.criticalWeight t i)⁻¹) =
        ∏ i ∈ s, (Complex.normSq (1 - B.criticalWeight t i))⁻¹ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha,
          Complex.normSq_mul, Complex.normSq_inv, ih]
  change Complex.normSq (∏ i, (1 - B.criticalWeight t i)⁻¹) =
    ∏ i, (Complex.normSq (1 - B.criticalWeight t i))⁻¹
  exact hprod Finset.univ

/-- Local Poisson expansion of each Brauer-twisted positive Euler density. -/
theorem local_tateDensity_poisson (t : ℝ) (i : Fin n) :
    (Complex.normSq (1 - B.criticalWeight t i) : ℂ)⁻¹ =
      (1 - (semilocalPrimePoissonRatio (B.prime i) : ℂ) ^ 2)⁻¹ *
        ∑' m : ℤ, semilocalBilateralPoissonTerm
          (semilocalPrimePoissonRatio (B.prime i)) (B.criticalPhase t i) m := by
  exact semilocalOnePrimePoissonExpansion
    (semilocalPrimePoissonRatio_pos (B.prime i).property).le
    (semilocalPrimePoissonRatio_lt_one (B.prime i).property)
    (B.norm_criticalPhase t i)

/-- Product Poisson expansion of the reciprocal Brauer semilocal density. -/
theorem tateDensity_poissonProduct (t : ℝ) :
    (B.tateDensity t : ℂ) =
      (∏ i, (1 - (semilocalPrimePoissonRatio (B.prime i) : ℂ) ^ 2)⁻¹) *
        ∏ i, ∑' m : ℤ, semilocalBilateralPoissonTerm
          (semilocalPrimePoissonRatio (B.prime i)) (B.criticalPhase t i) m := by
  classical
  rw [tateDensity]
  push_cast
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact B.local_tateDensity_poisson t i

end ReciprocalFinitePrimeBrauerProfile

/-- Actual `p`-adic Brauer classes whose currently chosen full local invariants satisfy the
finite global reciprocity relation. Packaging reciprocity in the carrier leaves every downstream
theorem unconditional. -/
structure ChosenReciprocalFinitePadicBrauerClasses (n : ℕ) where
  prime : Fin n → Nat.Primes
  brauerClass : (i : Fin n) → BrauerGroup ℚ_[((prime i : Nat.Primes) : ℕ)]
  reciprocity : ∑ i,
    nonarchimedeanLocalBrauerGroupAddEquivRatModInt
      ℚ_[((prime i : Nat.Primes) : ℕ)] (brauerClass i) = 0

namespace ChosenReciprocalFinitePadicBrauerClasses

variable {n : ℕ} (B : ChosenReciprocalFinitePadicBrauerClasses n)

/-- Forget actual local classes only after evaluating their chosen local Brauer invariants. -/
noncomputable def toInvariantProfile : ReciprocalFinitePrimeBrauerProfile n where
  prime := B.prime
  invariant i := nonarchimedeanLocalBrauerGroupAddEquivRatModInt
    ℚ_[((B.prime i : Nat.Primes) : ℕ)] (B.brauerClass i)
  reciprocity := B.reciprocity

/-- Profile phase is exactly the already constructed `p`-adic Brauer phase. -/
theorem toInvariantProfile_brauerPhase (i : Fin n) :
    B.toInvariantProfile.brauerPhase i =
      padicBrauerInvariantStdAddChar ((B.prime i : Nat.Primes) : ℕ)
        (B.brauerClass i) := rfl

/-- Actual local Brauer classes with reciprocal chosen invariants produce a strictly positive
semilocal Tate density on every critical-line frequency. -/
theorem tateDensity_pos (t : ℝ) :
    0 < B.toInvariantProfile.tateDensity t :=
  B.toInvariantProfile.tateDensity_pos t

/-- Their actual finite Connes--Tate trace has that positive density as Hermitian square. -/
theorem normSq_tateTrace_eq_positiveDensity (t : ℝ) :
    Complex.normSq (B.toInvariantProfile.tateTrace t) =
        B.toInvariantProfile.tateDensity t ∧
      0 < B.toInvariantProfile.tateDensity t :=
  ⟨B.toInvariantProfile.normSq_tateTrace_eq_tateDensity t,
    B.toInvariantProfile.tateDensity_pos t⟩

end ChosenReciprocalFinitePadicBrauerClasses

end

end GaloisForLFunctions.RHTower
