import GaloisForLFunctions.RHTower.SemilocalCompressedEulerOrientation
import GaloisForLFunctions.RHTower.XiHurwitzRationalFiberSeam

/-!
# Cofinal anchored Euler commutators suffice for RH

The full finite-packet essential-commutation condition is much stronger than the top-down
argument needs.  Fix the first prime `2`.  On each Xi divisor fibre it is enough that the
two-prime compressed source commutator for `{2, q}` be compact for arbitrarily large primes `q`.

Finite quadratic Calkin faithfulness then identifies the `q`-seam charge with the `2`-seam
charge at every such prime.  The former tends to zero as `q` tends to infinity, so the anchored
charge vanishes.  The existing first-prime seam criterion closes RH.

This replaces all finite packets, all prime pairs, uniform estimates, and the all-prime aggregate
by a cofinal family of `2 x 2` compactness events.  No zero enumeration, positivity hypothesis,
or limiting divisor measure is used.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The two-prime packet anchored at the first rational prime. -/
def firstPrimeAnchoredPacket (q : ℕ) : Fin 2 → ℕ := ![2, q]

theorem firstPrimeAnchoredPacket_prime {q : ℕ} (hq : q.Prime) :
    ∀ i, (firstPrimeAnchoredPacket q i).Prime := by
  intro i
  fin_cases i
  · norm_num [firstPrimeAnchoredPacket]
  · simpa [firstPrimeAnchoredPacket] using hq

theorem firstPrimeAnchoredPacket_injective {q : ℕ} (hq : 2 < q) :
    Function.Injective (firstPrimeAnchoredPacket q) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [firstPrimeAnchoredPacket]

/-- The seam-weighted/unweighted compressed Euler commutator for the anchored pair `{2, q}`. -/
def firstPrimeAnchoredEulerCompressionCommutator
    (a : ℝ) (rho : ℂ) (q : ℕ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  let p := firstPrimeAnchoredPacket q
  let u : Fin 2 → ℂ := fun i ↦ orbitwiseNatPrimeSeamCharge (p i) rho
  finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) u *
      finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) (fun _ ↦ 1) -
    finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) (fun _ ↦ 1) *
      finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) u

/-- One anchored commutator is compact exactly when its two prime-seam charges agree. -/
theorem firstPrimeAnchoredEulerCompressionCommutator_isCompactOperator_iff
    {a : ℝ} (ha : 0 < a) {rho : ℂ} {q : ℕ}
    (hq : q.Prime) (hq2 : 2 < q) :
    IsCompactOperator
        (firstPrimeAnchoredEulerCompressionCommutator a rho q) ↔
      orbitwiseNatPrimeSeamCharge 2 rho =
        orbitwiseNatPrimeSeamCharge q rho := by
  let p := firstPrimeAnchoredPacket q
  let u : Fin 2 → ℂ := fun i ↦ orbitwiseNatPrimeSeamCharge (p i) rho
  have hp : ∀ i, (p i).Prime := firstPrimeAnchoredPacket_prime hq
  have hinj : Function.Injective p := firstPrimeAnchoredPacket_injective hq2
  have hbase :=
    finitePrimeArchimedeanEulerCompression_commutator_isCompactOperator_iff
      a ha p hp hinj u
  change IsCompactOperator
      (finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) u *
          finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) (fun _ ↦ 1) -
        finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) (fun _ ↦ 1) *
          finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) u) ↔ _
  rw [hbase]
  constructor
  · intro hall
    simpa [p, u, firstPrimeAnchoredPacket] using hall (0 : Fin 2) (1 : Fin 2)
  · intro hanchor i j
    fin_cases i <;> fin_cases j <;>
      simp_all [p, u, firstPrimeAnchoredPacket]

/-- The anchored compactness event is equivalently one equality between two finite rational
Hurwitz fibre defects, all evaluated in the half-plane of absolute convergence. -/
theorem firstPrimeAnchoredEulerCompressionCommutator_isCompactOperator_iff_hurwitzFiber
    {a : ℝ} (ha : 0 < a) {rho : ℂ} {q : ℕ}
    (hq : q.Prime) (hq2 : 2 < q)
    (hstrip : 0 < rho.re ∧ rho.re < 1) :
    IsCompactOperator
        (firstPrimeAnchoredEulerCompressionCommutator a rho q) ↔
      rationalHurwitzFiberReflectionSeam 2 rho =
        rationalHurwitzFiberReflectionSeam q rho := by
  rw [firstPrimeAnchoredEulerCompressionCommutator_isCompactOperator_iff ha hq hq2,
    rationalHurwitzFiberReflectionSeam_eq_primeSeamCharge (n := 2) (by norm_num) hstrip,
    rationalHurwitzFiberReflectionSeam_eq_primeSeamCharge (n := q) hq.pos hstrip]

/-- On one open-strip fibre, cofinally many compact anchored commutators force the first-prime
seam charge to vanish. -/
theorem firstPrimeSeamCharge_eq_zero_of_cofinal_anchored_commutators
    {a : ℝ} (ha : 0 < a) {rho : ℂ}
    (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hcofinal : ∀ N : ℕ, ∃ q : ℕ, q.Prime ∧ max N 2 < q ∧
      IsCompactOperator
        (firstPrimeAnchoredEulerCompressionCommutator a rho q)) :
    orbitwiseFirstPrimeSeamCharge rho = 0 := by
  rw [← orbitwiseNatPrimeSeamCharge_two_eq_firstPrime]
  by_contra hne
  have hdist : 0 < dist (orbitwiseNatPrimeSeamCharge 2 rho) 0 :=
    dist_pos.mpr hne
  have hlim := tendsto_orbitwiseNatPrimeSeamCharge hstrip
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim)
    (dist (orbitwiseNatPrimeSeamCharge 2 rho) 0) hdist
  obtain ⟨q, hq, hNq, hcompact⟩ := hcofinal N
  have hq2 : 2 < q := (le_max_right N 2).trans_lt hNq
  have hqN : N ≤ q := (le_max_left N 2).trans (le_of_lt hNq)
  have heq : orbitwiseNatPrimeSeamCharge 2 rho =
      orbitwiseNatPrimeSeamCharge q rho :=
    (firstPrimeAnchoredEulerCompressionCommutator_isCompactOperator_iff
      ha hq hq2).mp hcompact
  have hlt := hN q hqN
  rw [← heq] at hlt
  exact (lt_irrefl _ hlt).elim

/-- On every Xi divisor fibre, compact anchored commutators occur at arbitrarily large primes. -/
def XiCofinalFirstPrimeEulerCompressionEssentiallyCommuting (a : ℝ) : Prop :=
  ∀ (rho : XiDivisorSupport) (N : ℕ), ∃ q : ℕ,
    q.Prime ∧ max N 2 < q ∧
      IsCompactOperator
        (firstPrimeAnchoredEulerCompressionCommutator a (rho : ℂ) q)

/-- The all-finite-packet source condition implies the strictly smaller cofinal anchored target. -/
theorem xiCofinalFirstPrimeEulerCompressionEssentiallyCommuting_of_finite
    {a : ℝ}
    (hfinite : XiFiniteEulerCompressionEssentiallyCommuting a) :
    XiCofinalFirstPrimeEulerCompressionEssentiallyCommuting a := by
  intro rho N
  obtain ⟨q, hqN, hq⟩ := Nat.exists_infinite_primes (max N 2 + 1)
  have hmax : max N 2 < q := by omega
  let p := firstPrimeAnchoredPacket q
  have hp : ∀ i, (p i).Prime := firstPrimeAnchoredPacket_prime hq
  have hinj : Function.Injective p :=
    firstPrimeAnchoredPacket_injective ((le_max_right N 2).trans_lt hmax)
  refine ⟨q, hq, hmax, ?_⟩
  simpa [firstPrimeAnchoredEulerCompressionCommutator, p] using
    hfinite rho 2 p hp hinj

/-- **Cofinal anchored commutator criterion.**  Arbitrarily large compact `2 x 2` source
commutators on every Xi divisor fibre are equivalent to RH. -/
theorem xiCofinalFirstPrimeEulerCompressionEssentiallyCommuting_iff_riemannHypothesis
    (a : ℝ) (ha : 0 < a) :
    XiCofinalFirstPrimeEulerCompressionEssentiallyCommuting a ↔
      RiemannHypothesis := by
  constructor
  · intro hsource
    apply riemannHypothesis_of_xiPrimeSeamChargesCoherent
    apply xiPrimeSeamChargesCoherent_iff_firstPrimeSeamChargesVanish.mpr
    intro rho
    exact firstPrimeSeamCharge_eq_zero_of_cofinal_anchored_commutators
      ha (xi_divisor_support_re_mem_open_unit rho) (hsource rho)
  · intro hRH rho N
    obtain ⟨q, hqN, hq⟩ := Nat.exists_infinite_primes (max N 2 + 1)
    have hmax : max N 2 < q := by omega
    have hq2 : 2 < q := (le_max_right N 2).trans_lt hmax
    refine ⟨q, hq, hmax, ?_⟩
    apply (firstPrimeAnchoredEulerCompressionCommutator_isCompactOperator_iff
      ha hq hq2).mpr
    have hcoherent : XiPrimeSeamChargesCoherent :=
      xiPrimeSeamChargesCoherent_iff_riemannHypothesis.mpr hRH
    exact hcoherent rho 2 q (by norm_num) hq

end

end RHTower
