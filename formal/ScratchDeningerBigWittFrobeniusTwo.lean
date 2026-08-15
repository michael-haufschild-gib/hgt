import GaloisForLFunctions.RHTower.DeningerGammaSixBigWittStokesSource
import GaloisForLFunctions.RHTower.DeningerBigWittPrimeSeamDirichletTransport
import Mathlib.RingTheory.PowerSeries.Expand

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

open PowerSeries

variable {A B : Type*} [CommRing A] [CommRing B]

def scratchBigWittFrobeniusTwoNormSeries
    (w : DeningerBigWittRing A) : PowerSeries A :=
  let f := deningerBigWittRingSeries w
  PowerSeries.mk fun n =>
    PowerSeries.coeff (2 * n) (f * PowerSeries.rescale (-1 : A) f)

@[simp] theorem scratchBigWittFrobeniusTwoNormSeries_constantCoeff
    (w : DeningerBigWittRing A) :
    PowerSeries.constantCoeff (scratchBigWittFrobeniusTwoNormSeries w) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [scratchBigWittFrobeniusTwoNormSeries,
    deningerBigWittRingSeries, PowerSeries.coeff_mul]

def scratchBigWittFrobeniusTwo
    (w : DeningerBigWittRing A) : DeningerBigWittRing A :=
  ⟨Additive.ofMul
    (deningerBigWittOfSeries
      (scratchBigWittFrobeniusTwoNormSeries w)
      (scratchBigWittFrobeniusTwoNormSeries_constantCoeff w))⟩

@[simp] theorem scratchBigWittRingSeries_frobeniusTwo
    (w : DeningerBigWittRing A) :
    deningerBigWittRingSeries (scratchBigWittFrobeniusTwo w) =
      scratchBigWittFrobeniusTwoNormSeries w := by
  rfl

theorem scratch_ghost_one_eq_neg_coeff_one
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

theorem scratch_ghost_two_eq_coeff_formula
    (w : DeningerBigWittRing A) :
    deningerBigWittGhostComponent 2 (by norm_num) w =
      PowerSeries.coeff 1 (deningerBigWittRingSeries w) ^ 2 -
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
  have hg : deningerBigWittEulerGhost x 2 = x 0 ^ 2 + 2 * x 1 := by
    norm_num [deningerBigWittEulerGhost, Finset.sum_range_succ]
  rw [hg]
  ring

theorem scratch_frobeniusTwo_ghost_one
    (w : DeningerBigWittRing A) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (scratchBigWittFrobeniusTwo w) =
      deningerBigWittGhostComponent 2 (by norm_num) w := by
  rw [scratch_ghost_one_eq_neg_coeff_one,
    scratchBigWittRingSeries_frobeniusTwo,
    scratchBigWittFrobeniusTwoNormSeries,
    PowerSeries.coeff_mk,
    scratch_ghost_two_eq_coeff_formula]
  rw [PowerSeries.coeff_mul]
  simp only [Nat.mul_one]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_rescale]
  norm_num [Finset.sum_range_succ]
  rw [show PowerSeries.constantCoeff (deningerBigWittRingSeries w) = 1 by
    exact deningerBigWittSeries_constantCoeff _]
  ring

theorem scratchBigWittFrobeniusTwoNormSeries_natural
    (f : A →+* B) (w : DeningerBigWittRing A) :
    PowerSeries.map f (scratchBigWittFrobeniusTwoNormSeries w) =
      scratchBigWittFrobeniusTwoNormSeries (deningerBigWittRingMap f w) := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map, scratchBigWittFrobeniusTwoNormSeries,
    PowerSeries.coeff_mk]
  have hs : deningerBigWittRingSeries (deningerBigWittRingMap f w) =
      PowerSeries.map f (deningerBigWittRingSeries w) := by
    rfl
  rw [hs, show (-1 : B) = f (-1 : A) by simp,
    PowerSeries.rescale_map, ← map_mul, PowerSeries.coeff_map]

theorem scratchBigWittFrobeniusTwo_natural
    (f : A →+* B) (w : DeningerBigWittRing A) :
    deningerBigWittRingMap f (scratchBigWittFrobeniusTwo w) =
      scratchBigWittFrobeniusTwo (deningerBigWittRingMap f w) := by
  apply deningerBigWittRingSeries_injective
  rw [scratchBigWittRingSeries_frobeniusTwo]
  change PowerSeries.map f
      (scratchBigWittFrobeniusTwoNormSeries w) = _
  exact scratchBigWittFrobeniusTwoNormSeries_natural f w

theorem scratchBigWittFrobeniusTwoNormSeries_teichmuller (a : A) :
    scratchBigWittFrobeniusTwoNormSeries
        (deningerBigWittRingTeichmuller a) =
      deningerBigWittFactor (a ^ 2) 1 := by
  let h : PowerSeries A :=
    deningerBigWittFactor a 1 *
      PowerSeries.rescale (-1 : A) (deningerBigWittFactor a 1)
  have hh : h = PowerSeries.expand 2 (by norm_num)
      (deningerBigWittFactor (a ^ 2) 1) := by
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
        (deningerBigWittFactor (a ^ 2) 1) =
        1 - PowerSeries.C (a ^ 2) * PowerSeries.X ^ 2 := by
      rw [deningerBigWittFactor, map_sub, map_one, map_mul,
        PowerSeries.expand_C, pow_one, PowerSeries.expand_X]
    rw [hneg, hexpand]
    rw [deningerBigWittFactor, map_pow]
    ring
  apply PowerSeries.ext
  intro n
  rw [scratchBigWittFrobeniusTwoNormSeries,
    deningerBigWittRingSeries_teichmuller]
  rw [PowerSeries.coeff_mk]
  change PowerSeries.coeff (2 * n) h = _
  rw [hh, PowerSeries.coeff_expand_mul]

@[simp] theorem scratchBigWittFrobeniusTwo_teichmuller (a : A) :
    scratchBigWittFrobeniusTwo (deningerBigWittRingTeichmuller a) =
      deningerBigWittRingTeichmuller (a ^ 2) := by
  apply deningerBigWittRingSeries_injective
  rw [scratchBigWittRingSeries_frobeniusTwo,
    scratchBigWittFrobeniusTwoNormSeries_teichmuller,
    deningerBigWittRingSeries_teichmuller]

theorem scratchBigWittTeichmullerCrossEffect_comm (a b : A) :
    deningerBigWittTeichmullerCrossEffect a b =
      deningerBigWittTeichmullerCrossEffect b a := by
  simp only [deningerBigWittTeichmullerCrossEffect]
  rw [add_comm a b, add_comm (deningerBigWittRingTeichmuller a)
    (deningerBigWittRingTeichmuller b)]

theorem scratchBigWittTeichmullerCrossEffect_ghost_two_scaled_conj
    (u v : ℝ) (z : ℂ) :
    deningerBigWittGhostComponent 2 (by norm_num)
        (deningerBigWittTeichmullerCrossEffect
          ((u : ℂ) * z) ((v : ℂ) * (starRingEnd ℂ) z)) =
      ((-2 * u * v * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [deningerBigWittTeichmullerCrossEffect]
  simp only [map_sub, map_add,
    deningerBigWittGhostComponent_teichmuller]
  rw [← Complex.normSq_eq_norm_sq]
  push_cast
  rw [← Complex.mul_conj]
  ring

def scratchBigWittPolarizedPrimeSeamPairSource
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    DeningerBigWittRing ℂ :=
  let d := a p - a q
  deningerBigWittTeichmullerCrossEffect
    (((1 / (p : ℝ) : ℝ) : ℂ) * d)
    (((1 / (q : ℝ) : ℝ) : ℂ) * (starRingEnd ℂ) d)

theorem scratchBigWittPolarizedPrimeSeamPairSource_ghost_one
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (scratchBigWittPolarizedPrimeSeamPairSource a p q) = 0 := by
  exact deningerBigWittTeichmullerCrossEffect_ghost_one _ _

theorem scratchBigWittPolarizedPrimeSeamPairSource_ghost_two
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerBigWittGhostComponent 2 (by norm_num)
        (scratchBigWittPolarizedPrimeSeamPairSource a p q) =
      ((-2 * deningerBigWittPrimePairExtendedPhysicalAtom p q *
        ‖a p - a q‖ ^ 2 : ℝ) : ℂ) := by
  rw [scratchBigWittPolarizedPrimeSeamPairSource]
  rw [scratchBigWittTeichmullerCrossEffect_ghost_two_scaled_conj]
  congr 2
  rw [deningerBigWittPrimePairExtendedPhysicalAtom_eq]
  ring

theorem scratchBigWittPolarizedPrimeSeamPairSource_negStar_reverse
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    scratchBigWittPolarizedPrimeSeamPairSource
        (fun r => -(starRingEnd ℂ) (a r)) p q =
      scratchBigWittPolarizedPrimeSeamPairSource a q p := by
  rw [scratchBigWittPolarizedPrimeSeamPairSource,
    scratchBigWittPolarizedPrimeSeamPairSource]
  simp only [map_sub, map_neg, Complex.conj_conj]
  rw [scratchBigWittTeichmullerCrossEffect_comm]
  congr 1 <;> push_cast <;> ring

theorem scratchBigWittPolarizedPrimeSeamPairSource_one_sub_reverse
    (rho : ℂ) (p q : Nat.Primes) :
    scratchBigWittPolarizedPrimeSeamPairSource
        (fun r : Nat.Primes =>
          orbitwiseNatPrimeSeamCharge (r : ℕ) (1 - rho)) p q =
      scratchBigWittPolarizedPrimeSeamPairSource
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
  exact scratchBigWittPolarizedPrimeSeamPairSource_negStar_reverse _ _ _

def scratchBigWittPolarizedPrimeSeamAggregateSource
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    DeningerBigWittRing ℂ :=
  ∑ p ∈ s, ∑ q ∈ s,
    scratchBigWittPolarizedPrimeSeamPairSource a p q

theorem scratchBigWittPolarizedPrimeSeamAggregateSource_ghost_one
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (scratchBigWittPolarizedPrimeSeamAggregateSource a s) = 0 := by
  simp [scratchBigWittPolarizedPrimeSeamAggregateSource,
    scratchBigWittPolarizedPrimeSeamPairSource_ghost_one]

theorem scratchBigWittPolarizedPrimeSeamAggregateSource_ghost_two
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 2 (by norm_num)
        (scratchBigWittPolarizedPrimeSeamAggregateSource a s) =
      ((-2 * deningerBigWittPrimeSeamSourceEnergy a s : ℝ) : ℂ) := by
  calc
    deningerBigWittGhostComponent 2 (by norm_num)
        (scratchBigWittPolarizedPrimeSeamAggregateSource a s) =
        ∑ p ∈ s, ∑ q ∈ s,
          deningerBigWittGhostComponent 2 (by norm_num)
            (scratchBigWittPolarizedPrimeSeamPairSource a p q) := by
      simp [scratchBigWittPolarizedPrimeSeamAggregateSource]
    _ = ∑ p ∈ s, ∑ q ∈ s,
          ((-2 * deningerBigWittPrimePairExtendedPhysicalAtom p q *
            ‖a p - a q‖ ^ 2 : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact scratchBigWittPolarizedPrimeSeamPairSource_ghost_two a p q
    _ = ((-2 * deningerBigWittPrimeSeamSourceEnergy a s : ℝ) : ℂ) := by
      rw [deningerBigWittPrimeSeamSourceEnergy, Finset.mul_sum]
      push_cast
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

theorem scratchBigWittPolarizedPrimeSeamAggregateSource_one_sub
    (rho : ℂ) (s : Finset Nat.Primes) :
    scratchBigWittPolarizedPrimeSeamAggregateSource
        (fun r : Nat.Primes =>
          orbitwiseNatPrimeSeamCharge (r : ℕ) (1 - rho)) s =
      scratchBigWittPolarizedPrimeSeamAggregateSource
        (fun r : Nat.Primes =>
          orbitwiseNatPrimeSeamCharge (r : ℕ) rho) s := by
  rw [scratchBigWittPolarizedPrimeSeamAggregateSource,
    scratchBigWittPolarizedPrimeSeamAggregateSource]
  simp_rw [scratchBigWittPolarizedPrimeSeamPairSource_one_sub_reverse]
  rw [Finset.sum_comm]

theorem scratchBigWittFrobeniusTwo_polarizedAggregate_ghost_one
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (scratchBigWittFrobeniusTwo
          (scratchBigWittPolarizedPrimeSeamAggregateSource a s)) =
      ((-2 * deningerBigWittPrimeSeamSourceEnergy a s : ℝ) : ℂ) := by
  rw [scratch_frobeniusTwo_ghost_one,
    scratchBigWittPolarizedPrimeSeamAggregateSource_ghost_two]

/-- After Frobenius-two transgression, the normalized physical first ghost
has the exact nonzero cofinal residue `-4 ‖δ(ρ)‖²`. -/
theorem scratch_tendsto_frobeniusTwo_polarizedAggregate_ghost_one_div_mass
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Filter.Tendsto
      (fun s : Finset Nat.Primes =>
        Complex.re
            (deningerBigWittGhostComponent 1 Nat.zero_lt_one
              (scratchBigWittFrobeniusTwo
                (scratchBigWittPolarizedPrimeSeamAggregateSource
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
    rw [scratchBigWittFrobeniusTwo_polarizedAggregate_ghost_one]
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
  · ring

#check Complex.mul_conj
#check Complex.normSq_eq_norm_sq
#check deningerBigWittRingMap
#check PowerSeries.coeff_map

end

end RHTower
