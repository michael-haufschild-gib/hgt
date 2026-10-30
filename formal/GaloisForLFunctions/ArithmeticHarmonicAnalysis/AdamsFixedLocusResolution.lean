import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TorsionArithmeticResolution
import GaloisForLFunctions.ArithmeticGaugeTheory.TheAdamsOperations

/-!
# Arithmetic coefficient recovery on Adams fixed loci

The finite prime torsion grid embeds in the existing gauge torus and is fixed
by the Adams operation `ψ^(q+1)`. Its Fourier samples therefore give a sharp
vanishing threshold for actual arithmetic auxiliaries on that fixed locus:
length below `2^q` forces the zero auxiliary, while `χ(2^q) - 1` attains the
boundary. No assertion about higher multiplicity or prime counts is used.
-/

open Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open HTGeometry ArithmeticCorrelationGeometry ArithmeticGaugeTheory

variable (q : ℕ) [NeZero q]

/-- A finite torsion grid embedded by its active prime coordinates. -/
def torsionGauge (P : Finset ℕ) (t : P → ZMod q) : GaugeTorus :=
  fun p => if hp : p ∈ P then ZMod.toAddCircle (t ⟨p, hp⟩) else 0

/-- Every embedded grid point has order dividing `q`. -/
theorem torsionGauge_nsmul (P : Finset ℕ) (t : P → ZMod q) :
    q • torsionGauge q P t = 0 := by
  funext p
  change q • (torsionGauge q P t p) = 0
  by_cases hp : p ∈ P
  · rw [torsionGauge, dif_pos hp, ← map_nsmul, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul, map_zero]
  · rw [torsionGauge, dif_neg hp, smul_zero]

/-- The finite grid consists of actual Adams fixed points. -/
theorem isAdamsFixed_torsionGauge (P : Finset ℕ) (t : P → ZMod q) :
    IsAdamsFixed (q + 1) (torsionGauge q P t) := by
  intro n _
  rw [adams, add_nsmul, one_nsmul, torsionGauge_nsmul, zero_add]

private theorem fourier_toAddCircle (k : ℕ) (z : ZMod q) :
    fourier (k : ℤ) (ZMod.toAddCircle z) = ZMod.stdAddChar (z * k) := by
  rw [fourier_apply, ← map_zsmul]
  change (ZMod.toCircle ((k : ℤ) • z) : ℂ) = (ZMod.toCircle (z * k) : ℂ)
  congr 2
  simp only [natCast_zsmul, nsmul_eq_mul, mul_comm]

/-- Torsion-grid evaluation reads precisely the prime valuations modulo `q`. -/
theorem twist_torsionGauge (P : Finset ℕ) (t : P → ZMod q) (n : ℕ)
    (hn : n.factorization.support ⊆ P) :
    twist (torsionGauge q P t) n = torsionPhase q (valuationResidue q P n) t := by
  rw [twist, torusCharacter_apply_of_subset (by simpa only [support_expVec] using hn)]
  have hprod : (∏ p ∈ P, fourier (expVec n p) (torsionGauge q P t p)) =
      ∏ p : P, ZMod.stdAddChar (t p * (n.factorization p : ZMod q)) := by
    rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro p _
    rw [torsionGauge, dif_pos p.property, expVec_apply, fourier_toAddCircle]
  exact hprod

private theorem short_factorization_support (n : ℕ) (hn : n ∈ Ioo 0 (2 ^ q)) :
    n.factorization.support ⊆ shortPrimes q := by
  intro p hp
  have hpf : p ∈ n.primeFactors := by
    simpa only [Nat.support_factorization] using hp
  have hprime := Nat.prime_of_mem_primeFactors hpf
  have hpn := Nat.le_of_dvd (mem_Ioo.mp hn).1 (Nat.dvd_of_mem_primeFactors hpf)
  exact Nat.mem_primesBelow.mpr ⟨hpn.trans_lt (mem_Ioo.mp hn).2, hprime⟩

/-- The sampled polynomial is the original arithmetic auxiliary at a gauge point. -/
theorem shortTorsionPolynomial_eq_twistSum (c : ℕ → ℂ)
    (t : shortPrimes q → ZMod q) :
    shortTorsionPolynomial q c t =
      twistSum (Ioo 0 (2 ^ q)) c (torsionGauge q (shortPrimes q) t) := by
  unfold shortTorsionPolynomial torsionPolynomial twistSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [twist_torsionGauge q _ _ n (short_factorization_support q n hn)]

/-- Vanishing on the entire Adams fixed locus below length `2^q` forces every coefficient to vanish. -/
theorem short_adams_auxiliary_vanishes_iff (c : ℕ → ℂ) :
    (∀ x : GaugeTorus, IsAdamsFixed (q + 1) x →
      twistSum (Ioo 0 (2 ^ q)) c x = 0) ↔
      ∀ n ∈ Ioo 0 (2 ^ q), c n = 0 := by
  constructor
  · intro h
    apply (short_torsion_vanishing_iff q c).mp
    intro t
    rw [shortTorsionPolynomial_eq_twistSum]
    exact h _ (isAdamsFixed_torsionGauge q _ t)
  · intro h x _
    unfold twistSum
    apply Finset.sum_eq_zero
    intro n hn
    rw [h n hn, zero_mul]

/-- At the boundary, the nonzero arithmetic binomial vanishes at every Adams fixed point. -/
theorem adams_boundary_binomial :
    (1 : ℕ) ≠ 2 ^ q ∧
      ∀ x : GaugeTorus, IsAdamsFixed (q + 1) x → twist x (2 ^ q) - twist x 1 = 0 := by
  constructor
  · exact (one_lt_pow₀ (by omega : 1 < (2 : ℕ)) (NeZero.ne q)).ne
  · intro x hx
    have hpow := (isAdamsFixed_iff (by omega : 1 ≤ q + 1) x).mp hx 2 (by omega)
    rw [Nat.add_sub_cancel] at hpow
    rw [twist_pow_index x (by omega : (2 : ℕ) ≠ 0), hpow, twist_one, sub_self]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
