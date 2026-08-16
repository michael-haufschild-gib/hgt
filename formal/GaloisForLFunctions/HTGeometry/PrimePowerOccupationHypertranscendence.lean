import GaloisForLFunctions.HTGeometry.PrimeLinearOccupationHypertranscendence

/-!
# Finite prime occupation products at integer temperature

At temperature `r` the occupation modes of a finite prime packet `S` contribute the zeros `n^r`
for the `S`-smooth positive integers `n`, so the packet product is the genus-zero canonical product

`Φ_{S,r}(x) = ∏_{ν ∈ ℕ^S} (1 - x ∏_{p ∈ S} p^{-r ν_p})`.

Its nomes are the `r`-th reciprocal prime powers, which are the elliptic nomes of the periods
`i r log p / (2π)`.  Scaling an integrally independent family by a nonzero integer keeps it
integrally independent, so two distinct primes still produce a rank-three period minor and the
period-rank law makes the backward all-order multiple elliptic Gamma product hypertranscendental in
its additive variable.  That product is `Φ_{S,r}` read in the multiplicative coordinate, so
hypertranscendence descends to the packet product itself.
-/

open Complex Set
open scoped BigOperators

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

namespace HTGeometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The period whose elliptic nome is the `r`-th reciprocal power of the prime. -/
def primePowerNomePeriod (r : ℕ) (q : ι → Nat.Primes) : ι → ℂ :=
  fun i => (r : ℂ) * primeNomePeriod q i

omit [Fintype ι] [DecidableEq ι] in
theorem primePowerNomePeriod_im (r : ℕ) (q : ι → Nat.Primes) (i : ι) :
    (primePowerNomePeriod r q i).im = r * (primeNomePeriod q i).im := by
  rw [primePowerNomePeriod, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul,
    add_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem primePowerNomePeriod_im_pos {r : ℕ} (hr : 1 ≤ r) (q : ι → Nat.Primes) (i : ι) :
    0 < (primePowerNomePeriod r q i).im := by
  rw [primePowerNomePeriod_im]
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  exact mul_pos hrpos (primeNomePeriod_im_pos q i)

omit [Fintype ι] [DecidableEq ι] in
/-- **The nome of the scaled prime period is the reciprocal prime power.** -/
theorem ellipticNome_primePowerNomePeriod (r : ℕ) (q : ι → Nat.Primes) (i : ι) :
    ellipticNome (primePowerNomePeriod r q i) = ((((q i : ℕ) : ℂ))⁻¹) ^ r := by
  rw [← ellipticNome_primeNomePeriod q i, ellipticNome, ellipticNome, primePowerNomePeriod]
  rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((r : ℂ) * primeNomePeriod q i)
      = (r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * primeNomePeriod q i) from by ring]
  exact Complex.exp_nat_mul _ r

omit [DecidableEq ι] in
/-- Scaling an integrally independent period family by a nonzero integer keeps it integrally
independent. -/
theorem periodsIntegrallyIndependent_natCast_mul {τ : ι → ℂ}
    (h : PeriodsIntegrallyIndependent τ) {r : ℕ} (hr : r ≠ 0) :
    PeriodsIntegrallyIndependent (fun i => (r : ℂ) * τ i) := by
  intro m n hrel
  have hrel' : (m : ℂ) + ∑ i, (((r : ℤ) * n i : ℤ) : ℂ) * τ i = 0 := by
    refine Eq.trans ?_ hrel
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  obtain ⟨hm, hn⟩ := h m (fun i => (r : ℤ) * n i) hrel'
  refine ⟨hm, fun i => ?_⟩
  have hi := hn i
  have hrz : (r : ℤ) ≠ 0 := by exact_mod_cast hr
  exact (mul_eq_zero.mp hi).resolve_left hrz

omit [DecidableEq ι] in
theorem periodsIntegrallyIndependent_primePowerNomePeriod {q : ι → Nat.Primes}
    (hq : Function.Injective q) {r : ℕ} (hr : r ≠ 0) :
    PeriodsIntegrallyIndependent (primePowerNomePeriod r q) :=
  periodsIntegrallyIndependent_natCast_mul (periodsIntegrallyIndependent_primeNomePeriod hq) hr

end HTGeometry

/-! ### The occupation face at integer temperature -/

/-- The `r`-th reciprocal power of a prime, the nome of one occupation mode at temperature `r`. -/
def primePowerNome (r : ℕ) (p : Nat.Primes) : ℂ := (primeLinearNome p) ^ r

theorem primePowerNome_ne_zero (r : ℕ) (p : Nat.Primes) : primePowerNome r p ≠ 0 :=
  pow_ne_zero _ (primeLinearNome_ne_zero p)

theorem norm_primePowerNome_lt_one {r : ℕ} (hr : 1 ≤ r) (p : Nat.Primes) :
    ‖primePowerNome r p‖ < 1 := by
  rw [primePowerNome, norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) (norm_primeLinearNome_lt_one p) (by omega)

/-- The occupation face of a finite prime source at temperature `r`. -/
def primeOccupationFacePow (r : ℕ) (S : Finset Nat.Primes) (t : ℂ) : ℂ :=
  HTGeometry.infiniteMultipleEllipticGamma 0 (fun p : S => primePowerNome r (p : Nat.Primes)) t

theorem primeOccupationFacePow_eq_tprod (r : ℕ) (S : Finset Nat.Primes) (t : ℂ) :
    primeOccupationFacePow r S t
      = ∏' ν : S →₀ ℕ,
          (1 - t * HTGeometry.nomeMonomial (fun p : S => primePowerNome r (p : Nat.Primes)) ν) := by
  rw [primeOccupationFacePow, HTGeometry.infiniteMultipleEllipticGamma,
    HTGeometry.canonicalWeightProduct]
  exact tprod_congr fun ν => primaryFactor_zero_genus _

theorem analyticOnNhd_primeOccupationFacePow {r : ℕ} (hr : 1 ≤ r) (S : Finset Nat.Primes) :
    AnalyticOnNhd ℂ (primeOccupationFacePow r S) Set.univ :=
  HTGeometry.infiniteMultipleEllipticGamma_analytic 0
    (fun p : S => primePowerNome r (p : Nat.Primes))
    (fun p => primePowerNome_ne_zero r p) (fun p => norm_primePowerNome_lt_one hr p)
    Summable.of_finite

theorem contDiff_primeOccupationFacePow {r : ℕ} (hr : 1 ≤ r) (S : Finset Nat.Primes) :
    ContDiff ℂ (⊤ : ℕ∞) (primeOccupationFacePow r S) :=
  contDiffOn_univ.1 ((analyticOnNhd_primeOccupationFacePow hr S).contDiffOn uniqueDiffOn_univ)

/-- The backward multiple elliptic Gamma product at the reciprocal prime-power periods is the
occupation face at temperature `r`, read in the multiplicative coordinate. -/
theorem multipleEllipticGammaBackwardProduct_primePowerNomePeriod (r : ℕ)
    (S : Finset Nat.Primes) :
    multipleEllipticGammaBackwardProduct
        (HTGeometry.primePowerNomePeriod r (fun p : S => (p : Nat.Primes)))
      = fun z => primeOccupationFacePow r S (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) := by
  classical
  funext z
  have hnome :
      (fun i : S =>
          ellipticNome (HTGeometry.primePowerNomePeriod r (fun p : S => (p : Nat.Primes)) i))
        = fun p : S => primePowerNome r (p : Nat.Primes) := by
    funext i
    rw [HTGeometry.ellipticNome_primePowerNomePeriod, primePowerNome]
    rfl
  rw [multipleEllipticGammaBackwardProduct_eq_infiniteMultipleEllipticGamma, hnome]
  rfl

/-- **Every finite prime packet with at least two primes has a hypertranscendental occupation face
at every positive integer temperature.** -/
theorem hypertranscendental_primeOccupationFacePow {r : ℕ} (hr : 1 ≤ r) (S : Finset Nat.Primes)
    (hS : 2 ≤ S.card) : Hypertranscendental (primeOccupationFacePow r S) := by
  classical
  set q : S → Nat.Primes := fun p => (p : Nat.Primes) with hq
  set τ : S → ℂ := HTGeometry.primePowerNomePeriod r q with hτ
  have hqinj : Function.Injective q := Subtype.val_injective
  have hcard : 2 ≤ Fintype.card S := by simpa using hS
  have hτim : ∀ i, 0 < (τ i).im := HTGeometry.primePowerNomePeriod_im_pos hr q
  have hminor : MultipleEllipticGammaHasRankThreeMinor τ :=
    multipleEllipticGammaHasRankThreeMinor_of_periodsIntegrallyIndependent τ
      (HTGeometry.periodsIntegrallyIndependent_primePowerNomePeriod hqinj (by omega)) hcard
  have hBHT : Hypertranscendental (multipleEllipticGammaBackwardProduct τ) :=
    hypertranscendental_multipleEllipticGammaBackwardProduct_of_rankThreeMinor τ hτim hminor
  rw [hτ, hq, multipleEllipticGammaBackwardProduct_primePowerNomePeriod r S] at hBHT
  exact HTGeometry.hypertranscendental_of_comp_exp (contDiff_primeOccupationFacePow hr S)
    twoPiI_ne_zero hBHT

/-- **The reflected occupation face at temperature `r` is hypertranscendental as well.** -/
theorem hypertranscendental_primeOccupationFacePow_neg {r : ℕ} (hr : 1 ≤ r)
    (S : Finset Nat.Primes) (hS : 2 ≤ S.card) :
    Hypertranscendental (fun t : ℂ => primeOccupationFacePow r S (-t)) := by
  intro hDA
  have hback := hDA.comp_const_mul_uncond (by norm_num : (-1 : ℂ) ≠ 0)
  have hrw : (fun z : ℂ => primeOccupationFacePow r S (-(-1 * z)))
      = primeOccupationFacePow r S := by
    funext z
    congr 1
    ring
  rw [hrw] at hback
  exact hypertranscendental_primeOccupationFacePow hr S hS hback

end

end GaloisForLFunctions
