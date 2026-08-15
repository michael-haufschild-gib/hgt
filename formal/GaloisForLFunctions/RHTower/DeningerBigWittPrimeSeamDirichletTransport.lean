import GaloisForLFunctions.RHTower.DeningerBigWittCrossPrimeIncidenceHorizon
import GaloisForLFunctions.RHTower.XiPrimeSeamPairAsymptotics

/-!
# Big-Witt source transport to the physical prime-seam Dirichlet form

The canonical reciprocal-prime Big-Witt codiagonal at an ordered pair
`(p,q)` has quadratic atom `1/(p*q)`.  This module proves that these literal
source atoms generate, without renormalization, the finite reciprocal-prime
Dirichlet energies of the actual Xi seam.  Uniform boundedness on every Xi
divisor fibre is consequently equivalent to RH by the established seam
rigidity theorem.

The coefficient must be used as energy rather than Hilbert amplitude.  Its
positive square root has nonsummable squared norm, so no vector in the
cross-prime `ell^2` packet can realize all physical atoms as coordinate
energies.  The source-pure `1/(p*q)` packet remains square summable only
because its Hilbert energy is the square of the physical weight.  Thus the
remaining source estimate belongs to a singular/cofinal Dirichlet-form
transport, not another bounded Hilbert comparison.

No boundedness premise or zero-location conclusion is asserted.
-/

open Complex Function Set Topology Filter
open scoped ENNReal BigOperators

namespace RHTower

noncomputable section

private abbrev deningerBigWittTwoPrime : Nat.Primes :=
  ⟨2, Nat.prime_two⟩

private abbrev deningerBigWittThreePrime : Nat.Primes :=
  ⟨3, Nat.prime_three⟩

def deningerBigWittHalfDensitySliceIndex (p : Nat.Primes) :
    DeningerCalderonWittCrossPrimePacketIndex :=
  if hp : p = deningerBigWittTwoPrime then
    ⟨(p, deningerBigWittThreePrime), by
      intro h
      have hv := congrArg Subtype.val h
      simp [hp] at hv⟩
  else
    ⟨(p, deningerBigWittTwoPrime), hp⟩

private theorem deningerBigWittHalfDensitySliceIndex_first (p : Nat.Primes) :
    (deningerBigWittHalfDensitySliceIndex p).1.1 = p := by
  rw [deningerBigWittHalfDensitySliceIndex]
  split <;> rfl

theorem deningerBigWittHalfDensitySliceIndex_injective :
    Function.Injective deningerBigWittHalfDensitySliceIndex := by
  intro p q h
  have hv := congrArg
    (fun i : DeningerCalderonWittCrossPrimePacketIndex => i.1.1) h
  simpa [deningerBigWittHalfDensitySliceIndex_first] using hv

def deningerBigWittCrossPrimePhysicalAtom
    (i : DeningerCalderonWittCrossPrimePacketIndex) : ℝ :=
  ((deningerBigWittCrossPrimeAtom i : ℚ) : ℝ)

def deningerBigWittCrossPrimeHalfDensity
    (i : DeningerCalderonWittCrossPrimePacketIndex) : ℝ :=
  Real.sqrt (deningerBigWittCrossPrimePhysicalAtom i)

theorem deningerBigWittCrossPrimePhysicalAtom_pos
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    0 < deningerBigWittCrossPrimePhysicalAtom i := by
  have hp : 0 < ((i.1.1 : ℕ) : ℚ) := by
    exact_mod_cast i.1.1.2.pos
  have hq : 0 < ((i.1.2 : ℕ) : ℚ) := by
    exact_mod_cast i.1.2.2.pos
  rw [deningerBigWittCrossPrimePhysicalAtom,
    deningerBigWittCrossPrimeAtom, deningerBigWittPrimeFace]
  norm_cast
  exact mul_pos (inv_pos.mpr hp) (inv_pos.mpr hq)

@[simp] theorem deningerBigWittCrossPrimeHalfDensity_sq
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPrimeHalfDensity i ^ 2 =
      deningerBigWittCrossPrimePhysicalAtom i := by
  exact Real.sq_sqrt (deningerBigWittCrossPrimePhysicalAtom_pos i).le

theorem deningerBigWittCrossPrimePhysicalAtom_slice
    (p : Nat.Primes) (hp : p ≠ deningerBigWittTwoPrime) :
    deningerBigWittCrossPrimePhysicalAtom
        (deningerBigWittHalfDensitySliceIndex p) =
      (1 / 2 : ℝ) * (1 / (p : ℝ)) := by
  rw [deningerBigWittHalfDensitySliceIndex, dif_neg hp]
  simp only [deningerBigWittCrossPrimePhysicalAtom,
    deningerBigWittCrossPrimeAtom, deningerBigWittPrimeFace]
  push_cast
  norm_num
  ring

theorem not_summable_deningerBigWittCrossPrimePhysicalAtom :
    ¬ Summable (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
      deningerBigWittCrossPrimePhysicalAtom i) := by
  intro hsum
  have hslice : Summable (fun p : Nat.Primes =>
      deningerBigWittCrossPrimePhysicalAtom
        (deningerBigWittHalfDensitySliceIndex p)) :=
    hsum.comp_injective deningerBigWittHalfDensitySliceIndex_injective
  have hevent :
      (fun p : Nat.Primes =>
        deningerBigWittCrossPrimePhysicalAtom
          (deningerBigWittHalfDensitySliceIndex p)) =ᶠ[cofinite]
        (fun p : Nat.Primes => (1 / 2 : ℝ) * (1 / (p : ℝ))) := by
    filter_upwards [Filter.eventually_cofinite_ne deningerBigWittTwoPrime] with p hp
    exact deningerBigWittCrossPrimePhysicalAtom_slice p hp
  have hhalf : Summable (fun p : Nat.Primes =>
      (1 / 2 : ℝ) * (1 / (p : ℝ))) :=
    (summable_congr_cofinite hevent).mp hslice
  have hone : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) := by
    have htwo := hhalf.mul_left (2 : ℝ)
    exact htwo.congr (fun p => by ring)
  exact Nat.Primes.not_summable_one_div hone

theorem not_summable_sq_deningerBigWittCrossPrimeHalfDensity :
    ¬ Summable (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
      deningerBigWittCrossPrimeHalfDensity i ^ 2) := by
  simpa only [deningerBigWittCrossPrimeHalfDensity_sq] using
    not_summable_deningerBigWittCrossPrimePhysicalAtom

theorem no_deningerBigWittPhysicalHalfDensity_packet :
    ¬ ∃ z : DeningerCalderonWittCrossPrimePacketHilbert,
      ∀ i : DeningerCalderonWittCrossPrimePacketIndex,
        ‖z i‖ ^ 2 = deningerBigWittCrossPrimePhysicalAtom i := by
  rintro ⟨z, hz⟩
  apply not_summable_deningerBigWittCrossPrimePhysicalAtom
  have hnorm : Summable (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
      ‖z i‖ ^ 2) := by
    simpa using (lp.memℓp z).summable (by norm_num)
  exact hnorm.congr (fun i => hz i)

/-! ## Source-derived physical Dirichlet transport -/

/-- Reciprocal-prime atom extended harmlessly across the diagonal.  The
diagonal never contributes to a difference energy. -/
def deningerBigWittPrimePairExtendedPhysicalAtom
    (p q : Nat.Primes) : ℝ :=
  (((deningerBigWittPrimeFace p * deningerBigWittPrimeFace q : ℚ) : ℝ))

theorem deningerBigWittPrimePairExtendedPhysicalAtom_eq
    (p q : Nat.Primes) :
    deningerBigWittPrimePairExtendedPhysicalAtom p q =
      (1 / (p : ℝ)) * (1 / (q : ℝ)) := by
  simp [deningerBigWittPrimePairExtendedPhysicalAtom,
    deningerBigWittPrimeFace, one_div]

/-- Away from the zero-energy diagonal, the extended weight is literally
the quadratic atom of the canonical Big-Witt codiagonal source. -/
theorem deningerBigWittPrimePairExtendedPhysicalAtom_offDiagonal
    (p q : Nat.Primes) (hpq : p ≠ q) :
    deningerBigWittPrimePairExtendedPhysicalAtom p q =
      deningerBigWittCrossPrimePhysicalAtom ⟨(p, q), hpq⟩ := by
  rfl

/-- Finite physical Dirichlet energy generated by the quadratic atoms of
the canonical reciprocal-prime Big-Witt codiagonals. -/
def deningerBigWittPrimeSeamSourceEnergy
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ s, ∑ q ∈ s,
    deningerBigWittPrimePairExtendedPhysicalAtom p q *
      ‖a p - a q‖ ^ 2

/-- The source-defined Big-Witt quadratic energy is exactly the physical
reciprocal-prime seam energy, with no normalization or comparison constant. -/
theorem deningerBigWittPrimeSeamSourceEnergy_eq_primePairDifferenceEnergy
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittPrimeSeamSourceEnergy a s =
      primePairDifferenceEnergy a s := by
  rw [deningerBigWittPrimeSeamSourceEnergy, primePairDifferenceEnergy]
  apply Finset.sum_congr rfl
  intro p hp
  rw [primePairDifferenceRow]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [deningerBigWittPrimePairExtendedPhysicalAtom_eq]
  ring

/-- Uniform finite-window control of the source-defined Big-Witt seam
Dirichlet energy. -/
def DeningerBigWittPrimeSeamSourceEnergyBounded
    (a : Nat.Primes → ℂ) : Prop :=
  ∃ B : ℝ, ∀ s : Finset Nat.Primes,
    deningerBigWittPrimeSeamSourceEnergy a s ≤ B

theorem deningerBigWittPrimeSeamSourceEnergyBounded_iff
    (a : Nat.Primes → ℂ) :
    DeningerBigWittPrimeSeamSourceEnergyBounded a ↔
      PrimePairDifferenceEnergyBounded a := by
  simp only [DeningerBigWittPrimeSeamSourceEnergyBounded,
    PrimePairDifferenceEnergyBounded,
    deningerBigWittPrimeSeamSourceEnergy_eq_primePairDifferenceEnergy]

/-- Source-energy boundedness has only the constant prime potentials in its
radical. -/
theorem deningerBigWittPrimeSeamSourceEnergyBounded_iff_constant
    (a : Nat.Primes → ℂ) :
    DeningerBigWittPrimeSeamSourceEnergyBounded a ↔
      ∃ c : ℂ, ∀ p, a p = c := by
  rw [deningerBigWittPrimeSeamSourceEnergyBounded_iff,
    primePairDifferenceEnergyBounded_iff_constant]

/-- Actual Xi seam boundedness measured by the canonical Big-Witt source
energy. -/
def DeningerBigWittXiPrimeSeamSourceEnergyBounded : Prop :=
  ∀ rho : XiDivisorSupport,
    DeningerBigWittPrimeSeamSourceEnergyBounded
      (fun p : Nat.Primes =>
        orbitwiseNatPrimeSeamCharge (p : ℕ) (rho : ℂ))

/-- Exact source-to-physical endpoint: uniform boundedness of the canonical
Big-Witt Dirichlet transport on the actual Xi divisor is equivalent to RH. -/
theorem deningerBigWittXiPrimeSeamSourceEnergyBounded_iff_riemannHypothesis :
    DeningerBigWittXiPrimeSeamSourceEnergyBounded ↔ RiemannHypothesis := by
  have hident :
      DeningerBigWittXiPrimeSeamSourceEnergyBounded ↔
        XiPrimeSeamPairEnergyBounded := by
    constructor
    · intro h rho
      exact (deningerBigWittPrimeSeamSourceEnergyBounded_iff _).mp
        (h rho)
    · intro h rho
      exact (deningerBigWittPrimeSeamSourceEnergyBounded_iff _).mpr
        (h rho)
  exact hident.trans xiPrimeSeamPairEnergyBounded_iff_riemannHypothesis

/-! ## Canonical cofinal residue -/

/-- The singular Big-Witt source transport has an exact cofinal residue:
after division by reciprocal-prime mass, it converges to twice the full
one-particle seam square energy. -/
theorem tendsto_deningerBigWittPrimeSeamSourceEnergy_div_mass
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Filter.Tendsto
      (fun s : Finset Nat.Primes =>
        deningerBigWittPrimeSeamSourceEnergy
            (fun p : Nat.Primes =>
              orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s /
          primeReciprocalMass s)
      Filter.atTop
      (nhds (2 * orbitwisePrimeSeamWeightedNormSq rho)) := by
  simpa only [deningerBigWittPrimeSeamSourceEnergy_eq_primePairDifferenceEnergy]
    using tendsto_orbitwisePrimeSeamPairEnergy_div_mass hstrip

/-- Submass growth of the source-defined Big-Witt seam form on one strip
fibre.  This is strictly weaker than a uniform energy bound. -/
def OrbitwiseDeningerBigWittPrimeSeamSourceEnergySubmass
    (rho : ℂ) : Prop :=
  Filter.Tendsto
    (fun s : Finset Nat.Primes =>
      deningerBigWittPrimeSeamSourceEnergy
          (fun p : Nat.Primes =>
            orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s /
        primeReciprocalMass s)
    Filter.atTop (nhds 0)

/-- The cofinal Big-Witt residue vanishes exactly on the critical line. -/
theorem orbitwiseDeningerBigWittPrimeSeamSourceEnergySubmass_iff_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    OrbitwiseDeningerBigWittPrimeSeamSourceEnergySubmass rho ↔
      rho.re = 1 / 2 := by
  simpa only [OrbitwiseDeningerBigWittPrimeSeamSourceEnergySubmass,
    OrbitwisePrimeSeamPairEnergySubmass,
    deningerBigWittPrimeSeamSourceEnergy_eq_primePairDifferenceEnergy]
    using orbitwisePrimeSeamPairEnergySubmass_iff_re_eq_half hstrip

/-- Submass growth of the canonical Big-Witt source form on every actual Xi
divisor fibre. -/
def DeningerBigWittXiPrimeSeamSourceEnergySubmass : Prop :=
  ∀ rho : XiDivisorSupport,
    OrbitwiseDeningerBigWittPrimeSeamSourceEnergySubmass (rho : ℂ)

/-- Global weakened endpoint: sublinear, rather than uniformly bounded,
Big-Witt source energy on the Xi divisor is already equivalent to RH. -/
theorem deningerBigWittXiPrimeSeamSourceEnergySubmass_iff_riemannHypothesis :
    DeningerBigWittXiPrimeSeamSourceEnergySubmass ↔
      RiemannHypothesis := by
  simpa only [DeningerBigWittXiPrimeSeamSourceEnergySubmass,
    XiPrimeSeamPairEnergySubmass,
    OrbitwiseDeningerBigWittPrimeSeamSourceEnergySubmass,
    OrbitwisePrimeSeamPairEnergySubmass,
    deningerBigWittPrimeSeamSourceEnergy_eq_primePairDifferenceEnergy]
    using xiPrimeSeamPairEnergySubmass_iff_riemannHypothesis

/-- Pair source whose two faces are scaled by the physical seam difference. -/
def deningerBigWittPrimeSeamPairStokesSource
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    DeningerBigWittRing ℝ :=
  let d := ‖a p - a q‖
  deningerBigWittTeichmullerCrossEffect
    (d * (1 / (p : ℝ))) (d * (1 / (q : ℝ)))

theorem deningerBigWittPrimeSeamPairStokesSource_ghost_one
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittPrimeSeamPairStokesSource a p q) = 0 := by
  exact deningerBigWittTeichmullerCrossEffect_ghost_one _ _

theorem deningerBigWittPrimeSeamPairStokesSource_ghost_two
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerBigWittGhostComponent 2 (by norm_num)
        (deningerBigWittPrimeSeamPairStokesSource a p q) =
      -2 * deningerBigWittPrimePairExtendedPhysicalAtom p q *
        ‖a p - a q‖ ^ 2 := by
  rw [deningerBigWittPrimeSeamPairStokesSource,
    deningerBigWittTeichmullerCrossEffect]
  simp only [map_sub, map_add,
    deningerBigWittGhostComponent_teichmuller]
  rw [deningerBigWittPrimePairExtendedPhysicalAtom_eq]
  ring

/-- Single finite Big-Witt source obtained before extracting its physical
quadratic ghost. -/
def deningerBigWittPrimeSeamAggregateStokesSource
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    DeningerBigWittRing ℝ :=
  ∑ p ∈ s, ∑ q ∈ s,
    deningerBigWittPrimeSeamPairStokesSource a p q

theorem deningerBigWittPrimeSeamAggregateStokesSource_ghost_one
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittPrimeSeamAggregateStokesSource a s) = 0 := by
  simp [deningerBigWittPrimeSeamAggregateStokesSource,
    deningerBigWittPrimeSeamPairStokesSource_ghost_one]

/-- Second ghost of one finite aggregate source is exactly minus twice the
physical source Dirichlet energy. -/
theorem deningerBigWittPrimeSeamAggregateStokesSource_ghost_two
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 2 (by norm_num)
        (deningerBigWittPrimeSeamAggregateStokesSource a s) =
      -2 * deningerBigWittPrimeSeamSourceEnergy a s := by
  calc
    deningerBigWittGhostComponent 2 (by norm_num)
        (deningerBigWittPrimeSeamAggregateStokesSource a s) =
        ∑ p ∈ s, ∑ q ∈ s,
          deningerBigWittGhostComponent 2 (by norm_num)
            (deningerBigWittPrimeSeamPairStokesSource a p q) := by
      simp [deningerBigWittPrimeSeamAggregateStokesSource]
    _ = ∑ p ∈ s, ∑ q ∈ s,
          -2 * deningerBigWittPrimePairExtendedPhysicalAtom p q *
            ‖a p - a q‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact deningerBigWittPrimeSeamPairStokesSource_ghost_two a p q
    _ = -2 * deningerBigWittPrimeSeamSourceEnergy a s := by
      rw [deningerBigWittPrimeSeamSourceEnergy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

theorem deningerBigWittPrimeSeamAggregateStokesSource_ne_zero_of_energy_ne_zero
    {a : Nat.Primes → ℂ} {s : Finset Nat.Primes}
    (henergy : deningerBigWittPrimeSeamSourceEnergy a s ≠ 0) :
    deningerBigWittPrimeSeamAggregateStokesSource a s ≠ 0 := by
  intro hsource
  have hghost := congrArg
    (deningerBigWittGhostComponent 2 (by norm_num)) hsource
  rw [deningerBigWittPrimeSeamAggregateStokesSource_ghost_two,
    map_zero] at hghost
  apply henergy
  exact (mul_eq_zero.mp hghost).resolve_left (by norm_num)

theorem exists_nonzero_deningerBigWittPrimeSeamAggregateStokesSource_of_re_ne_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hoff : rho.re ≠ 1 / 2) :
    ∃ s : Finset Nat.Primes,
      deningerBigWittPrimeSeamAggregateStokesSource
        (fun p : Nat.Primes =>
          orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s ≠ 0 := by
  obtain ⟨s, hs⟩ := orbitwisePrimeSeamPairEnergy_unbounded_of_re_ne_half
    hstrip hoff 0
  refine ⟨s,
    deningerBigWittPrimeSeamAggregateStokesSource_ne_zero_of_energy_ne_zero
      ?_⟩
  rw [deningerBigWittPrimeSeamSourceEnergy_eq_primePairDifferenceEnergy]
  exact ne_of_gt hs

theorem deningerBigWittPrimeSeamAggregateStokesSource_eq_zero_of_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hre : rho.re = 1 / 2) (s : Finset Nat.Primes) :
    deningerBigWittPrimeSeamAggregateStokesSource
      (fun p : Nat.Primes =>
        orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s = 0 := by
  have hcoherent : OrbitwisePrimeSeamChargesCoherent rho :=
    (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half hstrip).mpr hre
  have htwo : orbitwiseNatPrimeSeamCharge 2 rho = 0 := by
    rw [orbitwiseNatPrimeSeamCharge_two_eq_firstPrime]
    exact (orbitwiseFirstPrimeSeamCharge_eq_zero_iff rho).mpr hre
  have hzero : ∀ p : Nat.Primes,
      orbitwiseNatPrimeSeamCharge (p : ℕ) rho = 0 := by
    intro p
    exact (hcoherent (p : ℕ) 2 p.prop (by norm_num)).trans htwo
  have hpair : ∀ p q : Nat.Primes,
      deningerBigWittPrimeSeamPairStokesSource
        (fun r : Nat.Primes =>
          orbitwiseNatPrimeSeamCharge (r : ℕ) rho) p q = 0 := by
    intro p q
    rw [deningerBigWittPrimeSeamPairStokesSource,
      hzero p, hzero q, sub_self, norm_zero, zero_mul]
    simp [deningerBigWittTeichmullerCrossEffect]
  rw [deningerBigWittPrimeSeamAggregateStokesSource]
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  exact hpair p q

/-- Every finite aggregate Big-Witt seam source vanishes on every actual Xi
divisor fibre. -/
def DeningerBigWittXiPrimeSeamAggregateStokesSourcesVanish : Prop :=
  ∀ rho : XiDivisorSupport, ∀ s : Finset Nat.Primes,
    deningerBigWittPrimeSeamAggregateStokesSource
      (fun p : Nat.Primes =>
        orbitwiseNatPrimeSeamCharge (p : ℕ) (rho : ℂ)) s = 0

/-- A single honest Big-Witt source family now carries the full RH detector:
all its finite Xi-divisor aggregates vanish exactly under RH. -/
theorem deningerBigWittXiPrimeSeamAggregateStokesSourcesVanish_iff_riemannHypothesis :
    DeningerBigWittXiPrimeSeamAggregateStokesSourcesVanish ↔
      RiemannHypothesis := by
  constructor
  · intro hsource
    apply deningerBigWittXiPrimeSeamSourceEnergyBounded_iff_riemannHypothesis.mp
    intro rho
    refine ⟨0, ?_⟩
    intro s
    have hghost := congrArg
      (deningerBigWittGhostComponent 2 (by norm_num)) (hsource rho s)
    rw [deningerBigWittPrimeSeamAggregateStokesSource_ghost_two,
      map_zero] at hghost
    have henergy : deningerBigWittPrimeSeamSourceEnergy
        (fun p : Nat.Primes =>
          orbitwiseNatPrimeSeamCharge (p : ℕ) (rho : ℂ)) s = 0 :=
      (mul_eq_zero.mp hghost).resolve_left (by norm_num)
    rw [henergy]
  · intro hRH rho s
    have hstrip := xi_divisor_support_re_mem_open_unit rho
    apply deningerBigWittPrimeSeamAggregateStokesSource_eq_zero_of_re_eq_half
      hstrip
    exact (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half hstrip).mp
      (xiPrimeSeamChargesCoherent_iff_riemannHypothesis.mpr hRH rho)

theorem DAC_DENINGER_BIG_WITT_PHYSICAL_HALF_DENSITY_WALL :
    Summable (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
      ‖deningerBigWittCrossPrimePacketRawCoefficient i‖ ^ 2) ∧
      (∀ i : DeningerCalderonWittCrossPrimePacketIndex,
      deningerBigWittCrossPrimeHalfDensity i ^ 2 =
        deningerBigWittCrossPrimePhysicalAtom i) ∧
      ¬ Summable (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
        deningerBigWittCrossPrimeHalfDensity i ^ 2) ∧
      ¬ ∃ z : DeningerCalderonWittCrossPrimePacketHilbert,
        ∀ i : DeningerCalderonWittCrossPrimePacketIndex,
          ‖z i‖ ^ 2 = deningerBigWittCrossPrimePhysicalAtom i := by
  exact ⟨summable_norm_sq_deningerBigWittCrossPrimePacketRawCoefficient,
    deningerBigWittCrossPrimeHalfDensity_sq,
    not_summable_sq_deningerBigWittCrossPrimeHalfDensity,
    no_deningerBigWittPhysicalHalfDensity_packet⟩

theorem DAC_DENINGER_BIG_WITT_PRIME_SEAM_DIRICHLET_TRANSPORT :
    (∀ (a : Nat.Primes → ℂ) (s : Finset Nat.Primes),
      deningerBigWittPrimeSeamSourceEnergy a s =
        primePairDifferenceEnergy a s) ∧
      (∀ (a : Nat.Primes → ℂ) (s : Finset Nat.Primes),
        deningerBigWittGhostComponent 2 (by norm_num)
            (deningerBigWittPrimeSeamAggregateStokesSource a s) =
          -2 * deningerBigWittPrimeSeamSourceEnergy a s) ∧
      (DeningerBigWittXiPrimeSeamAggregateStokesSourcesVanish ↔
        RiemannHypothesis) ∧
      (DeningerBigWittXiPrimeSeamSourceEnergyBounded ↔
        RiemannHypothesis) ∧
      (DeningerBigWittXiPrimeSeamSourceEnergySubmass ↔
        RiemannHypothesis) ∧
      ¬ ∃ z : DeningerCalderonWittCrossPrimePacketHilbert,
        ∀ i : DeningerCalderonWittCrossPrimePacketIndex,
          ‖z i‖ ^ 2 = deningerBigWittCrossPrimePhysicalAtom i := by
  exact ⟨deningerBigWittPrimeSeamSourceEnergy_eq_primePairDifferenceEnergy,
    deningerBigWittPrimeSeamAggregateStokesSource_ghost_two,
    deningerBigWittXiPrimeSeamAggregateStokesSourcesVanish_iff_riemannHypothesis,
    deningerBigWittXiPrimeSeamSourceEnergyBounded_iff_riemannHypothesis,
    deningerBigWittXiPrimeSeamSourceEnergySubmass_iff_riemannHypothesis,
    no_deningerBigWittPhysicalHalfDensity_packet⟩

end

end RHTower
