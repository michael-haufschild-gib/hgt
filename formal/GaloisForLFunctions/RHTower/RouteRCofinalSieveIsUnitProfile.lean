import GaloisForLFunctions.RHTower.RouteRCofinalSieveHarmonicResidue
import GaloisForLFunctions.HTGeometry.CofinalUnitProfileResidue

/-!
# The restarted Euler sieve is a bounded cofinal unit profile

The restarted sieve densities, transported from the tail index to the primes themselves, form a
family of weights in `[0,1]` of unit prime-harmonic mass whose supports escape every finite set of
primes.  That is exactly the abstract hypothesis of the cofinal reading law, and the sieve reporter
is the corresponding profile average.

Consequently the sieve's coefficient-recovery theorem is an instance of the universal law rather than
an independent construction: what the Euler sieve contributes is one concrete admissible device, not
a new mechanism.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Transporting the sieve density to the primes -/

/-- The restarted sieve density read as a weight on the primes: the prime at tail
position `n` carries the density remaining after sieving the first `n` tail
primes, and the primes before the restart carry nothing. -/
def routeRCofinalSieveProfile (e : ℕ ≃ Nat.Primes) (N : ℕ) (p : Nat.Primes) : ℝ :=
  if N ≤ e.symm p then routeRCofinalSieveDensity e N (e.symm p - N) else 0

/-- Enumeration of the primes carried by the stage restarted at `N`. -/
def routeRCofinalSieveIndex (e : ℕ ≃ Nat.Primes) (N : ℕ) : ℕ → Nat.Primes :=
  fun n => e (N + n)

theorem routeRCofinalSieveIndex_injective (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    Function.Injective (routeRCofinalSieveIndex e N) := by
  intro m n hmn
  have h := e.injective hmn
  omega

@[simp] theorem routeRCofinalSieveProfile_index (e : ℕ ≃ Nat.Primes) (N n : ℕ) :
    routeRCofinalSieveProfile e N (routeRCofinalSieveIndex e N n) =
      routeRCofinalSieveDensity e N n := by
  rw [routeRCofinalSieveProfile, routeRCofinalSieveIndex, Equiv.symm_apply_apply,
    if_pos (Nat.le_add_right N n)]
  congr 1
  omega

theorem routeRCofinalSieveProfile_eq_zero_of_notMem_range
    (e : ℕ ≃ Nat.Primes) (N : ℕ) {p : Nat.Primes}
    (hp : p ∉ Set.range (routeRCofinalSieveIndex e N)) :
    routeRCofinalSieveProfile e N p = 0 := by
  rw [routeRCofinalSieveProfile, if_neg]
  intro hle
  exact hp ⟨e.symm p - N, by
    rw [routeRCofinalSieveIndex, show N + (e.symm p - N) = e.symm p by omega,
      Equiv.apply_symm_apply]⟩

theorem routeRCofinalSieveProfile_nonneg (e : ℕ ≃ Nat.Primes) (N : ℕ)
    (p : Nat.Primes) : 0 ≤ routeRCofinalSieveProfile e N p := by
  rw [routeRCofinalSieveProfile]
  split_ifs
  · exact (routeRCofinalSieveDensity_pos e N _).le
  · exact le_rfl

theorem routeRCofinalSieveProfile_le_one (e : ℕ ≃ Nat.Primes) (N : ℕ)
    (p : Nat.Primes) : routeRCofinalSieveProfile e N p ≤ 1 := by
  rw [routeRCofinalSieveProfile]
  split_ifs
  · exact routeRCofinalSieveDensity_le_one e N _
  · exact zero_le_one

/-! ## The sieve profile is a bounded cofinal unit profile -/

theorem hasSum_routeRCofinalSieveProfile_mass (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    HasSum (fun p : Nat.Primes =>
      routeRCofinalSieveProfile e N p * primeHarmonicWeight p) 1 := by
  refine ((routeRCofinalSieveIndex_injective e N).hasSum_iff
    (f := fun p : Nat.Primes =>
      routeRCofinalSieveProfile e N p * primeHarmonicWeight p)
    (fun p hp => by
      rw [routeRCofinalSieveProfile_eq_zero_of_notMem_range e N hp, zero_mul])).mp ?_
  refine (hasSum_routeRCofinalSieveWeight e N).congr_fun fun n => ?_
  rw [Function.comp_apply, routeRCofinalSieveProfile_index,
    routeRCofinalSieveIndex, primeHarmonicWeight, routeRCofinalSieveWeight,
    div_eq_mul_inv]

/-- **The restarted Euler sieve is a bounded cofinal unit profile.** -/
theorem isCofinalUnitProfile_routeRCofinalSieveProfile (e : ℕ ≃ Nat.Primes) :
    IsCofinalUnitProfile primeHarmonicWeight (routeRCofinalSieveProfile e) := by
  refine ⟨fun N p => routeRCofinalSieveProfile_nonneg e N p,
    fun N p => routeRCofinalSieveProfile_le_one e N p,
    fun N => hasSum_routeRCofinalSieveProfile_mass e N, fun s => ?_⟩
  filter_upwards [eventually_gt_atTop (s.sup fun p : Nat.Primes => e.symm p)]
    with N hN p hp
  have hlt : e.symm p < N :=
    lt_of_le_of_lt (Finset.le_sup (f := fun q : Nat.Primes => e.symm q) hp) hN
  rw [routeRCofinalSieveProfile, if_neg (by omega)]

/-! ## The sieve reporter is the profile average -/

theorem profileAverage_routeRCofinalSieveProfile (e : ℕ ≃ Nat.Primes) (N : ℕ)
    (a : Nat.Primes → ℂ) :
    profileAverage (routeRCofinalSieveProfile e) N a =
      routeRCofinalSieveHarmonicReporter e N a := by
  have hsupp : Function.support
      (fun p : Nat.Primes => (routeRCofinalSieveProfile e N p : ℂ) * a p) ⊆
        Set.range (routeRCofinalSieveIndex e N) := by
    intro p hp
    by_contra hmem
    refine hp ?_
    show ((routeRCofinalSieveProfile e N p : ℝ) : ℂ) * a p = 0
    rw [routeRCofinalSieveProfile_eq_zero_of_notMem_range e N hmem]
    simp
  have hkey := (routeRCofinalSieveIndex_injective e N).tsum_eq hsupp
  rw [routeRCofinalSieveHarmonicReporter, profileAverage]
  refine (Eq.trans ?_ hkey).symm
  exact tsum_congr fun n => by
    rw [routeRCofinalSieveProfile_index e N n]
    rfl

/-- **The sieve reporter's coefficient recovery is an instance of the universal
reading law.**  Nothing about the Euler product is used: only that the sieve
weights are bounded, of unit prime-harmonic mass, and cofinally escaping. -/
theorem tendsto_routeRCofinalSieveHarmonicReporter_of_residue
    (e : ℕ ≃ Nat.Primes) {a : Nat.Primes → ℂ} {c : ℂ}
    (hres : HasReferenceResidue primeHarmonicWeight a c) :
    Tendsto (fun N => routeRCofinalSieveHarmonicReporter e N a) atTop (nhds c) := by
  refine (tendsto_profileAverage (isCofinalUnitProfile_routeRCofinalSieveProfile e)
    hres).congr fun N => ?_
  exact profileAverage_routeRCofinalSieveProfile e N a

/-- The sieve reporter also reads the enlarged domain `ell^1 + negligible`, which
its own development does not cover. -/
theorem tendsto_routeRCofinalSieveHarmonicReporter_of_residueMod
    (e : ℕ ≃ Nat.Primes) {a : Nat.Primes → ℂ} {c : ℂ}
    (hres : HasReferenceResidueMod primeHarmonicWeight a c) :
    Tendsto (fun N => routeRCofinalSieveHarmonicReporter e N a) atTop (nhds c) := by
  refine (tendsto_profileAverage_mod primeHarmonicWeight_nonneg
    (isCofinalUnitProfile_routeRCofinalSieveProfile e) hres).congr fun N => ?_
  exact profileAverage_routeRCofinalSieveProfile e N a

end

end RHTower
