import GaloisForLFunctions.RHTower.DeningerBigWittPrimeSeamDirichletTransport
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Big-Witt Frobenius-two prime-seam transgression

This module resolves the ghost-degree mismatch left by the prime-seam
Dirichlet source.  It constructs the degree-two big-Witt norm directly from
the literal series model

`f(T) ↦ f(T) f(-T) ∈ A[[T²]]`,  `F₂(f)_n = [T²ⁿ](f(T)f(-T))`.

The construction is division-free and natural over every commutative ring;
nilpotents and additive torsion are retained.  Its first ghost is proved
unconditionally to equal the input second ghost, and Teichmüller elements map
to their squares.

For the Deninger prime seam, a polarized complex source retains conjugate
phase before norm extraction. Functional-equation reflection reverses its
ordered prime pair. Its finite aggregate is reflection-invariant, while
Frobenius two moves the exact physical Dirichlet energy from ghost degree two
to ghost degree one. The normalized first ghost has cofinal residue
`-4 * orbitwisePrimeSeamWeightedNormSq rho`.

This removes ghost-degree mismatch. Remaining Route L frontier is geometric:
identify this explicit first-ghost object as an actual strict Green/BV
boundary with a source-side submass estimate; no such estimate is assumed
here.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

open PowerSeries

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Division-free series norm defining the degree-two big-Witt Frobenius
operation over an arbitrary commutative ring. -/
def deningerBigWittFrobeniusTwoNormSeries
    (w : DeningerBigWittRing A) : PowerSeries A :=
  let f := deningerBigWittRingSeries w
  PowerSeries.mk fun n =>
    PowerSeries.coeff (2 * n) (f * PowerSeries.rescale (-1 : A) f)

@[simp] theorem deningerBigWittFrobeniusTwoNormSeries_constantCoeff
    (w : DeningerBigWittRing A) :
    PowerSeries.constantCoeff (deningerBigWittFrobeniusTwoNormSeries w) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [deningerBigWittFrobeniusTwoNormSeries,
    deningerBigWittRingSeries, PowerSeries.coeff_mul]

/-- Degree-two Frobenius norm on the literal canonical big-Witt carrier. -/
def deningerBigWittFrobeniusTwo
    (w : DeningerBigWittRing A) : DeningerBigWittRing A :=
  ⟨Additive.ofMul
    (deningerBigWittOfSeries
      (deningerBigWittFrobeniusTwoNormSeries w)
      (deningerBigWittFrobeniusTwoNormSeries_constantCoeff w))⟩

@[simp] theorem deningerBigWittRingSeries_frobeniusTwo
    (w : DeningerBigWittRing A) :
    deningerBigWittRingSeries (deningerBigWittFrobeniusTwo w) =
      deningerBigWittFrobeniusTwoNormSeries w := by
  rfl

theorem deningerBigWittGhost_one_eq_neg_coeff_one
    (w : DeningerBigWittRing A) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one w =
      -PowerSeries.coeff 1 (deningerBigWittRingSeries w) := by
  let x := (deningerBigWittEulerEquiv A).symm
    (Additive.toMul w.additiveVal)
  have hw : deningerBigWittRingSeries w = deningerBigWittEulerSeries x := by
    rw [deningerBigWittRingSeries, show Additive.toMul w.additiveVal =
      deningerBigWittEulerEquiv A x from
        ((deningerBigWittEulerEquiv A).apply_symm_apply _).symm,
      deningerBigWittSeries_eulerEquiv]
  change deningerBigWittGhostCoeff (Additive.toMul w.additiveVal) 1 = _
  rw [show Additive.toMul w.additiveVal = deningerBigWittEulerEquiv A x from
    ((deningerBigWittEulerEquiv A).apply_symm_apply _).symm,
    deningerBigWittGhostCoeff_euler x Nat.zero_lt_one]
  rw [hw]
  simp [deningerBigWittEulerGhost, deningerBigWittEulerSeries_coeff,
    deningerBigWittEulerPartial, deningerBigWittFactor]

theorem deningerBigWittGhost_two_eq_coeff_formula
    (w : DeningerBigWittRing A) :
    deningerBigWittGhostComponent 2 (by norm_num) w =
      PowerSeries.coeff 1 (deningerBigWittRingSeries w) ^ (2 : ℕ) -
        2 * PowerSeries.coeff 2 (deningerBigWittRingSeries w) := by
  let x := (deningerBigWittEulerEquiv A).symm
    (Additive.toMul w.additiveVal)
  have hw : deningerBigWittRingSeries w = deningerBigWittEulerSeries x := by
    rw [deningerBigWittRingSeries, show Additive.toMul w.additiveVal =
      deningerBigWittEulerEquiv A x from
        ((deningerBigWittEulerEquiv A).apply_symm_apply _).symm,
      deningerBigWittSeries_eulerEquiv]
  change deningerBigWittGhostCoeff (Additive.toMul w.additiveVal) 2 = _
  rw [show Additive.toMul w.additiveVal = deningerBigWittEulerEquiv A x from
    ((deningerBigWittEulerEquiv A).apply_symm_apply _).symm,
    deningerBigWittGhostCoeff_euler x (by norm_num)]
  rw [hw]
  have hc1 : PowerSeries.coeff 1 (deningerBigWittEulerSeries x) = -x 0 := by
    simp [deningerBigWittEulerSeries_coeff, deningerBigWittEulerPartial,
      deningerBigWittFactor]
  have hc2 : PowerSeries.coeff 2 (deningerBigWittEulerSeries x) = -x 1 := by
    rw [deningerBigWittEulerSeries_coeff]
    rw [show deningerBigWittEulerPartial x 2 =
        deningerBigWittFactor (x 0) 1 * deningerBigWittFactor (x 1) 2 by
      norm_num [deningerBigWittEulerPartial, Finset.prod_range_succ]]
    rw [coeff_mul_deningerBigWittFactor_self]
    simp [deningerBigWittFactor]
  rw [hc1, hc2]
  have hg : deningerBigWittEulerGhost x 2 = x 0 ^ (2 : ℕ) + 2 * x 1 := by
    norm_num [deningerBigWittEulerGhost, Finset.sum_range_succ]
  rw [hg]
  ring

/-- The source second ghost becomes the transgressed first ghost.  This proof
uses coefficients only, so no torsion-freeness or ghost injectivity enters. -/
theorem deningerBigWittFrobeniusTwo_ghost_one
    (w : DeningerBigWittRing A) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittFrobeniusTwo w) =
      deningerBigWittGhostComponent 2 (by norm_num) w := by
  rw [deningerBigWittGhost_one_eq_neg_coeff_one,
    deningerBigWittRingSeries_frobeniusTwo,
    deningerBigWittFrobeniusTwoNormSeries,
    PowerSeries.coeff_mk,
    deningerBigWittGhost_two_eq_coeff_formula]
  rw [PowerSeries.coeff_mul]
  simp only [Nat.mul_one]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_rescale]
  norm_num [Finset.sum_range_succ]
  rw [show PowerSeries.constantCoeff (deningerBigWittRingSeries w) = 1 by
    exact deningerBigWittSeries_constantCoeff _]
  ring

theorem deningerBigWittFrobeniusTwoNormSeries_natural
    (f : A →+* B) (w : DeningerBigWittRing A) :
    PowerSeries.map f (deningerBigWittFrobeniusTwoNormSeries w) =
      deningerBigWittFrobeniusTwoNormSeries (deningerBigWittRingMap f w) := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map, deningerBigWittFrobeniusTwoNormSeries,
    PowerSeries.coeff_mk]
  have hs : deningerBigWittRingSeries (deningerBigWittRingMap f w) =
      PowerSeries.map f (deningerBigWittRingSeries w) := by
    rfl
  rw [hs, show (-1 : B) = f (-1 : A) by simp,
    PowerSeries.rescale_map, ← map_mul, PowerSeries.coeff_map]

/-- Frobenius-two norm commutes with every base-ring homomorphism. -/
theorem deningerBigWittFrobeniusTwo_natural
    (f : A →+* B) (w : DeningerBigWittRing A) :
    deningerBigWittRingMap f (deningerBigWittFrobeniusTwo w) =
      deningerBigWittFrobeniusTwo (deningerBigWittRingMap f w) := by
  apply deningerBigWittRingSeries_injective
  rw [deningerBigWittRingSeries_frobeniusTwo]
  change PowerSeries.map f
      (deningerBigWittFrobeniusTwoNormSeries w) = _
  exact deningerBigWittFrobeniusTwoNormSeries_natural f w

theorem deningerBigWittFrobeniusTwoNormSeries_teichmuller (a : A) :
    deningerBigWittFrobeniusTwoNormSeries
        (deningerBigWittRingTeichmuller a) =
      deningerBigWittFactor (a ^ (2 : ℕ)) 1 := by
  let h : PowerSeries A :=
    deningerBigWittFactor a 1 *
      PowerSeries.rescale (-1 : A) (deningerBigWittFactor a 1)
  have hh : h = PowerSeries.expand 2 (by norm_num)
      (deningerBigWittFactor (a ^ (2 : ℕ)) 1) := by
    dsimp only [h]
    have hC : PowerSeries.rescale (-1 : A) (PowerSeries.C a) =
        PowerSeries.C a := by
      apply PowerSeries.ext
      intro n
      by_cases hn : n = 0
      · subst n
        simp [PowerSeries.coeff_rescale]
      · simp [PowerSeries.coeff_rescale, PowerSeries.coeff_C, hn]
    have hneg : PowerSeries.rescale (-1 : A)
        (deningerBigWittFactor a 1) =
        1 + PowerSeries.C a * PowerSeries.X := by
      rw [deningerBigWittFactor, map_sub, map_one, map_mul, hC,
        pow_one, PowerSeries.rescale_X]
      simp only [map_neg, map_one]
      ring
    have hexpand : PowerSeries.expand 2 (by norm_num)
        (deningerBigWittFactor (a ^ (2 : ℕ)) 1) =
        1 - PowerSeries.C (a ^ (2 : ℕ)) * PowerSeries.X ^ (2 : ℕ) := by
      rw [deningerBigWittFactor, map_sub, map_one, map_mul,
        PowerSeries.expand_C, pow_one, PowerSeries.expand_X]
    rw [hneg, hexpand]
    rw [deningerBigWittFactor, map_pow]
    ring
  apply PowerSeries.ext
  intro n
  rw [deningerBigWittFrobeniusTwoNormSeries,
    deningerBigWittRingSeries_teichmuller]
  rw [PowerSeries.coeff_mk]
  change PowerSeries.coeff (2 * n) h = _
  rw [hh, PowerSeries.coeff_expand_mul]

/-- Frobenius two squares Teichmüller representatives over every ring. -/
@[simp] theorem deningerBigWittFrobeniusTwo_teichmuller (a : A) :
    deningerBigWittFrobeniusTwo (deningerBigWittRingTeichmuller a) =
      deningerBigWittRingTeichmuller (a ^ (2 : ℕ)) := by
  apply deningerBigWittRingSeries_injective
  rw [deningerBigWittRingSeries_frobeniusTwo,
    deningerBigWittFrobeniusTwoNormSeries_teichmuller,
    deningerBigWittRingSeries_teichmuller]

theorem deningerBigWittTeichmullerCrossEffect_comm (a b : A) :
    deningerBigWittTeichmullerCrossEffect a b =
      deningerBigWittTeichmullerCrossEffect b a := by
  simp only [deningerBigWittTeichmullerCrossEffect]
  rw [add_comm a b, add_comm (deningerBigWittRingTeichmuller a)
    (deningerBigWittRingTeichmuller b)]

theorem deningerBigWittTeichmullerCrossEffect_ghost_two_scaled_conj
    (u v : ℝ) (z : ℂ) :
    deningerBigWittGhostComponent 2 (by norm_num)
        (deningerBigWittTeichmullerCrossEffect
          ((u : ℂ) * z) ((v : ℂ) * (starRingEnd ℂ) z)) =
      ((-2 * u * v * ‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [deningerBigWittTeichmullerCrossEffect]
  simp only [map_sub, map_add,
    deningerBigWittGhostComponent_teichmuller]
  rw [← Complex.normSq_eq_norm_sq]
  push_cast
  rw [← Complex.mul_conj]
  ring

/-- Ordered prime-pair source retaining the seam difference and its conjugate
before the quadratic ghost is extracted. -/
def deningerBigWittPolarizedPrimeSeamPairSource
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    DeningerBigWittRing ℂ :=
  let d := a p - a q
  deningerBigWittTeichmullerCrossEffect
    (((1 / (p : ℝ) : ℝ) : ℂ) * d)
    (((1 / (q : ℝ) : ℝ) : ℂ) * (starRingEnd ℂ) d)

theorem deningerBigWittPolarizedPrimeSeamPairSource_ghost_one
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittPolarizedPrimeSeamPairSource a p q) = 0 := by
  exact deningerBigWittTeichmullerCrossEffect_ghost_one _ _

theorem deningerBigWittPolarizedPrimeSeamPairSource_ghost_two
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerBigWittGhostComponent 2 (by norm_num)
        (deningerBigWittPolarizedPrimeSeamPairSource a p q) =
      ((-2 * deningerBigWittPrimePairExtendedPhysicalAtom p q *
        ‖a p - a q‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [deningerBigWittPolarizedPrimeSeamPairSource]
  rw [deningerBigWittTeichmullerCrossEffect_ghost_two_scaled_conj]
  congr 2
  rw [deningerBigWittPrimePairExtendedPhysicalAtom_eq]
  ring

theorem deningerBigWittPolarizedPrimeSeamPairSource_negStar_reverse
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerBigWittPolarizedPrimeSeamPairSource
        (fun r => -(starRingEnd ℂ) (a r)) p q =
      deningerBigWittPolarizedPrimeSeamPairSource a q p := by
  rw [deningerBigWittPolarizedPrimeSeamPairSource,
    deningerBigWittPolarizedPrimeSeamPairSource]
  simp only [map_sub, map_neg, Complex.conj_conj]
  rw [deningerBigWittTeichmullerCrossEffect_comm]
  congr 1 <;> push_cast <;> ring

/-- Functional-equation reflection is literal reversal of the ordered prime
pair at the source-object level. -/
theorem deningerBigWittPolarizedPrimeSeamPairSource_one_sub_reverse
    (rho : ℂ) (p q : Nat.Primes) :
    deningerBigWittPolarizedPrimeSeamPairSource
        (fun r : Nat.Primes =>
          orbitwiseNatPrimeSeamCharge (r : ℕ) (1 - rho)) p q =
      deningerBigWittPolarizedPrimeSeamPairSource
        (fun r : Nat.Primes =>
          orbitwiseNatPrimeSeamCharge (r : ℕ) rho) q p := by
  have hfun :
      (fun r : Nat.Primes =>
        orbitwiseNatPrimeSeamCharge (r : ℕ) (1 - rho)) =
      (fun r : Nat.Primes =>
        -(starRingEnd ℂ) (orbitwiseNatPrimeSeamCharge (r : ℕ) rho)) := by
    funext r
    exact orbitwiseNatPrimeSeamCharge_one_sub
      (r : ℕ) r.prop.pos rho
  rw [hfun]
  exact deningerBigWittPolarizedPrimeSeamPairSource_negStar_reverse _ _ _

/-- Finite polarized source summed over all ordered prime pairs. -/
def deningerBigWittPolarizedPrimeSeamAggregateSource
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    DeningerBigWittRing ℂ :=
  ∑ p ∈ s, ∑ q ∈ s,
    deningerBigWittPolarizedPrimeSeamPairSource a p q

theorem deningerBigWittPolarizedPrimeSeamAggregateSource_ghost_one
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittPolarizedPrimeSeamAggregateSource a s) = 0 := by
  simp [deningerBigWittPolarizedPrimeSeamAggregateSource,
    deningerBigWittPolarizedPrimeSeamPairSource_ghost_one]

theorem deningerBigWittPolarizedPrimeSeamAggregateSource_ghost_two
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 2 (by norm_num)
        (deningerBigWittPolarizedPrimeSeamAggregateSource a s) =
      ((-2 * deningerBigWittPrimeSeamSourceEnergy a s : ℝ) : ℂ) := by
  calc
    deningerBigWittGhostComponent 2 (by norm_num)
        (deningerBigWittPolarizedPrimeSeamAggregateSource a s) =
        ∑ p ∈ s, ∑ q ∈ s,
          deningerBigWittGhostComponent 2 (by norm_num)
            (deningerBigWittPolarizedPrimeSeamPairSource a p q) := by
      simp [deningerBigWittPolarizedPrimeSeamAggregateSource]
    _ = ∑ p ∈ s, ∑ q ∈ s,
          ((-2 * deningerBigWittPrimePairExtendedPhysicalAtom p q *
            ‖a p - a q‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact deningerBigWittPolarizedPrimeSeamPairSource_ghost_two a p q
    _ = ((-2 * deningerBigWittPrimeSeamSourceEnergy a s : ℝ) : ℂ) := by
      rw [deningerBigWittPrimeSeamSourceEnergy, Finset.mul_sum]
      push_cast
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- Pair reversal makes the full polarized aggregate invariant under the
functional equation. -/
theorem deningerBigWittPolarizedPrimeSeamAggregateSource_one_sub
    (rho : ℂ) (s : Finset Nat.Primes) :
    deningerBigWittPolarizedPrimeSeamAggregateSource
        (fun r : Nat.Primes =>
          orbitwiseNatPrimeSeamCharge (r : ℕ) (1 - rho)) s =
      deningerBigWittPolarizedPrimeSeamAggregateSource
        (fun r : Nat.Primes =>
          orbitwiseNatPrimeSeamCharge (r : ℕ) rho) s := by
  rw [deningerBigWittPolarizedPrimeSeamAggregateSource,
    deningerBigWittPolarizedPrimeSeamAggregateSource]
  simp_rw [deningerBigWittPolarizedPrimeSeamPairSource_one_sub_reverse]
  rw [Finset.sum_comm]

/-- Frobenius-two transgression puts exact physical prime-seam energy in the
first ghost, with no comparison constant or RH-equivalent premise. -/
theorem deningerBigWittFrobeniusTwo_polarizedAggregate_ghost_one
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittFrobeniusTwo
          (deningerBigWittPolarizedPrimeSeamAggregateSource a s)) =
      ((-2 * deningerBigWittPrimeSeamSourceEnergy a s : ℝ) : ℂ) := by
  rw [deningerBigWittFrobeniusTwo_ghost_one,
    deningerBigWittPolarizedPrimeSeamAggregateSource_ghost_two]

/-- After Frobenius-two transgression, the normalized physical first ghost
has the exact nonzero cofinal residue `-4 ‖δ(ρ)‖²`. -/
theorem tendsto_deningerBigWittFrobeniusTwo_polarizedAggregate_ghost_one_div_mass
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Filter.Tendsto
      (fun s : Finset Nat.Primes =>
        Complex.re
            (deningerBigWittGhostComponent 1 Nat.zero_lt_one
              (deningerBigWittFrobeniusTwo
                (deningerBigWittPolarizedPrimeSeamAggregateSource
                  (fun p : Nat.Primes =>
                    orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s))) /
          primeReciprocalMass s)
      Filter.atTop
      (nhds (-4 * orbitwisePrimeSeamWeightedNormSq rho)) := by
  have hneg :=
    (tendsto_deningerBigWittPrimeSeamSourceEnergy_div_mass hstrip).neg
  have h := hneg.add hneg
  convert h using 1
  · funext s
    rw [deningerBigWittFrobeniusTwo_polarizedAggregate_ghost_one]
    change
      (-2 * deningerBigWittPrimeSeamSourceEnergy
          (fun p : Nat.Primes =>
            orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s) /
          primeReciprocalMass s =
        -(deningerBigWittPrimeSeamSourceEnergy
              (fun p : Nat.Primes =>
                orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s /
            primeReciprocalMass s) +
          -(deningerBigWittPrimeSeamSourceEnergy
              (fun p : Nat.Primes =>
                orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s /
            primeReciprocalMass s)
    ring
  · ring_nf

end

end RHTower
