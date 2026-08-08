import GaloisForLFunctions.HTGeometry.WeldClassTable
import GaloisForLFunctions.RHTower.SuzukiCriticalWallFieldSquareRootWeld

/-!
# Prime-power source rank obstruction for Route-J phase nodes

The finite full-turn Route-J escape hides the Fourier sine rows by placing every active source
atom at a carrier phase node.  This module tests that singular mechanism against actual arithmetic
source provenance.

Distinct prime logarithms are integer-linearly independent.  Consequently, at any nonzero carrier,
two prime-power delays with distinct prime bases cannot both be phase nodes.  Every phase-node
multiplier on the prime-power source therefore has active prime-base support of cardinality at
most one.  In particular, the uncensored Suzuki/von-Mangoldt far-hinge source cannot be a
phase-node singular Route-J source: its weight is strictly positive on every prime-power atom.

This is a source-class no-go, not a no-go for all singular measures.  A censored source supported
on one prime-power tower remains possible and is the exact surviving boundary.
-/

open Real

namespace RHTower

noncomputable section

/-- Two nonzero integer-scaled logarithms of distinct primes cannot simultaneously lie in one
nonzero carrier's sine-node lattice. -/
theorem routeJ_scaledPrimeLog_phaseNodes_incompatible
    {u : ℝ} (hu : u ≠ 0)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ¬ (Real.sin (u * (a : ℝ) * Real.log p) = 0 ∧
      Real.sin (u * (b : ℝ) * Real.log q) = 0) := by
  rintro ⟨hpnode, hqnode⟩
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hpnode
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hqnode
  have hscaled :
      u * (((a : ℝ) * (n : ℝ)) * Real.log p -
        ((b : ℝ) * (m : ℝ)) * Real.log q) = 0 := by
    calc
      u * (((a : ℝ) * (n : ℝ)) * Real.log p -
          ((b : ℝ) * (m : ℝ)) * Real.log q) =
          (n : ℝ) * (u * (a : ℝ) * Real.log p) -
            (m : ℝ) * (u * (b : ℝ) * Real.log q) := by ring
      _ = (n : ℝ) * ((m : ℝ) * π) -
            (m : ℝ) * ((n : ℝ) * π) := by rw [← hm, ← hn]
      _ = 0 := by ring
  have hrel :
      ((((a : ℤ) * n : ℤ) : ℝ) * Real.log p) +
        (((-((b : ℤ) * m) : ℤ) : ℝ) * Real.log q) = 0 := by
    have hinner :
        ((a : ℝ) * (n : ℝ)) * Real.log p -
          ((b : ℝ) * (m : ℝ)) * Real.log q = 0 :=
      (mul_eq_zero.mp hscaled).resolve_left hu
    push_cast
    linarith
  have hind := GaloisForLFunctions.RHTower.two_prime_log_indep hp hq hpq
    ((a : ℤ) * n) (-((b : ℤ) * m)) hrel
  have hn0 : n = 0 := by
    have haZ : (a : ℤ) ≠ 0 := by omega
    exact (mul_eq_zero.mp hind.1).resolve_left haZ
  have hm0 : m = 0 := by
    have hbZ : (b : ℤ) ≠ 0 := by omega
    have hbm : (b : ℤ) * m = 0 := neg_eq_zero.mp hind.2
    exact (mul_eq_zero.mp hbm).resolve_left hbZ
  have hlogp : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  rw [hm0, Int.cast_zero, zero_mul] at hm
  have hua : u * (a : ℝ) = 0 :=
    (mul_eq_zero.mp hm.symm).resolve_right hlogp
  exact hu ((mul_eq_zero.mp hua).resolve_right (by exact_mod_cast ha.ne'))

/-- Prime-power specialization of the scaled two-prime obstruction. -/
theorem routeJ_primePowerLog_phaseNodes_incompatible
    {u : ℝ} (hu : u ≠ 0)
    (p q : Nat.Primes) (hpq : p ≠ q) (e d : ℕ) :
    ¬ (Real.sin
          (u * Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) = 0 ∧
      Real.sin
          (u * Real.log (xiGammaEulerValuationNat (q, d) : ℝ)) = 0) := by
  rw [xiGammaEulerValuationNat, xiGammaEulerValuationNat,
    Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
  push_cast
  have hraw := routeJ_scaledPrimeLog_phaseNodes_incompatible hu
    p.property q.property (fun h => hpq (Subtype.ext h)) (Nat.succ_pos e)
      (Nat.succ_pos d)
  simpa [Nat.cast_succ, mul_assoc] using hraw

/-- A prime-power atom is a phase node for carrier `u`. -/
def routeJPrimePowerPhaseNodeAt
    (u : ℝ) (pe : Nat.Primes × ℕ) : Prop :=
  Real.sin
    (u * Real.log (xiGammaEulerValuationNat pe : ℝ)) = 0

/-- Prime bases on which a prime-power multiplier has at least one active depth. -/
def routeJPrimePowerActivePrimeSet
    (a : Nat.Primes × ℕ → ℝ) : Set Nat.Primes :=
  {p | ∃ e : ℕ, a (p, e) ≠ 0}

/-- Every active atom of the multiplier lies on the carrier's phase-node locus. -/
def RouteJPrimePowerPhaseNodeMultiplier
    (u : ℝ) (a : Nat.Primes × ℕ → ℝ) : Prop :=
  ∀ pe, a pe ≠ 0 → routeJPrimePowerPhaseNodeAt u pe

/-- Any phase-node subset of the prime-power wall has prime-base support of cardinality at most
one. -/
theorem routeJ_primePowerPhaseNode_primeSupport_subsingleton
    {u : ℝ} (hu : u ≠ 0)
    {S : Set (Nat.Primes × ℕ)}
    (hnode : ∀ pe ∈ S, routeJPrimePowerPhaseNodeAt u pe) :
    (Prod.fst '' S).Subsingleton := by
  rintro p ⟨⟨p', e⟩, hpe, rfl⟩ q ⟨⟨q', d⟩, hqd, rfl⟩
  by_contra hpq
  exact routeJ_primePowerLog_phaseNodes_incompatible hu p' q' hpq e d
    ⟨hnode (p', e) hpe, hnode (q', d) hqd⟩

/-- Multiplier form of prime-base rank-one rigidity. -/
theorem routeJ_primePowerPhaseNodeMultiplier_activePrimeSet_subsingleton
    {u : ℝ} (hu : u ≠ 0)
    {a : Nat.Primes × ℕ → ℝ}
    (ha : RouteJPrimePowerPhaseNodeMultiplier u a) :
    (routeJPrimePowerActivePrimeSet a).Subsingleton := by
  rintro p ⟨e, hpe⟩ q ⟨d, hqd⟩
  by_contra hpq
  exact routeJ_primePowerLog_phaseNodes_incompatible hu p q hpq e d
    ⟨ha (p, e) hpe, ha (q, d) hqd⟩

/-- A phase-node multiplier must censor at least one atom from every pair of distinct prime
bases. -/
theorem routeJ_primePowerPhaseNodeMultiplier_censors_distinctPrime
    {u : ℝ} (hu : u ≠ 0)
    {a : Nat.Primes × ℕ → ℝ}
    (ha : RouteJPrimePowerPhaseNodeMultiplier u a)
    {p q : Nat.Primes} (hpq : p ≠ q) (e d : ℕ) :
    a (p, e) = 0 ∨ a (q, d) = 0 := by
  by_contra h
  push Not at h
  exact routeJ_primePowerLog_phaseNodes_incompatible hu p q hpq e d
    ⟨ha (p, e) h.1, ha (q, d) h.2⟩

/-- Literal Suzuki/von-Mangoldt far-hinge weight on the prime-power source. -/
def routeJSuzukiFarHingeSourceWeight
    (pe : Nat.Primes × ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat pe) /
    Real.sqrt (xiGammaEulerValuationNat pe : ℝ)

/-- Every atom of the literal far-hinge source is active. -/
theorem routeJSuzukiFarHingeSourceWeight_pos
    (pe : Nat.Primes × ℕ) :
    0 < routeJSuzukiFarHingeSourceWeight pe := by
  exact suzukiCriticalFarHingeWeight_pos pe.1 pe.2

/-- **Actual-source no-go.** At every nonzero carrier, the uncensored Suzuki/von-Mangoldt
far-hinge source has active atoms on at least the prime-two and prime-three rays, so it cannot be
a phase-node multiplier. -/
theorem routeJ_suzukiFarHingeSource_not_all_phaseNodes
    {u : ℝ} (hu : u ≠ 0) :
    ¬ RouteJPrimePowerPhaseNodeMultiplier u
      routeJSuzukiFarHingeSourceWeight := by
  intro hall
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  let p3 : Nat.Primes := ⟨3, by norm_num⟩
  have hpq : p2 ≠ p3 := by
    intro h
    have := congrArg Subtype.val h
    norm_num [p2, p3] at this
  exact routeJ_primePowerLog_phaseNodes_incompatible hu p2 p3 hpq 0 0
    ⟨hall (p2, 0) (routeJSuzukiFarHingeSourceWeight_pos (p2, 0)).ne',
      hall (p3, 0) (routeJSuzukiFarHingeSourceWeight_pos (p3, 0)).ne'⟩

end

end RHTower
