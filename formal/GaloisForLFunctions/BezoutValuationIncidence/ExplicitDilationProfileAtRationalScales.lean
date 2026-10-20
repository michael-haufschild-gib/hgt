import GaloisForLFunctions.BezoutValuationIncidence.CotangentSawtoothFormOfThePronicGram
import GaloisForLFunctions.BezoutValuationIncidence.TwoPrimeDilationProfileIdentityAndPrimeStarShearCancellation

/-!
# The dilation profile at rational scales is a finite cotangent–sawtooth sum

Write `C(p, q) = φ(p)φ(q)/4 - (π/2) Σ_{(a,p)=1} Σ_{(b,q)=1} (cot(πa/p) + cot(πb/q)) ((a/p + b/q))`
for the cotangent–sawtooth form of the mean-centered pronic Gram. The three Grams of the theory
differ by rank-one terms in `Λ(q)` and `D(q) = φ(q)/2 - Λ(q)`:

`G^{ec}(p, q) = C(p, q) - D(p) D(q)`,  `G(p, q) = C(p, q) - D(p) D(q) + Λ(p) Λ(q)`.

The continuous dilation profile `Φ_r(c) = ⟨f_r, D_c f_r⟩` of the Ramanujan step vector satisfies
the four-term identity `G(pr, qr) + G(pr, r) + G(qr, r) + G(r, r) = √(pq) Φ_r(p/q)` for primes
`p, q ∤ r`. Hence at every prime ratio the profile is explicit:

`√(pq) Φ_r(p/q) = Σ_{(e, e') ∈ {(pr, qr), (pr, r), (qr, r), (r, r)}} G(e, e')`

with each `G(e, e')` a finite sum of cotangents and sawtooth values. Diophantine lag sectors
approximate the profile; this formula evaluates it.
-/

open Finset ArithmeticFunction RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The cotangent–sawtooth form `C(p, q)`. -/
def cotangentSawtoothForm (p q : ℕ) : ℝ :=
  (p.totient : ℝ) * q.totient / 4 - Real.pi / 2 *
    ∑ a ∈ (range p).filter (fun a => a.Coprime p), ∑ b ∈ (range q).filter (fun b => b.Coprime q),
      (Real.cot (Real.pi * (a / p)) + Real.cot (Real.pi * (b / q))) *
        sawtooth ((a : ℝ) / p + (b : ℝ) / q)

theorem pmRamanujanMeanCenteredGram_eq_cotangentSawtoothForm {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    pmRamanujanMeanCenteredGram p q = cotangentSawtoothForm p q :=
  pmRamanujanMeanCenteredGram_eq_cotangent_sawtooth hp hq

/-- **The energy-centered Gram.** `G^{ec}(p, q) = C(p, q) - D(p) D(q)`. -/
theorem pmRamanujanEnergyCenteredGram_eq_cotangentSawtoothForm {p q : ℕ} (hp : 2 ≤ p)
    (hq : 2 ≤ q) :
    pmRamanujanEnergyCenteredGram p q =
      cotangentSawtoothForm p q - sieveCenteringDiscrepancy p * sieveCenteringDiscrepancy q := by
  have h := pmRamanujanMeanCenteredGram_eq_energyCentered_add_rankOne (by omega : 1 < p)
    (by omega : 1 < q)
  rw [pmRamanujanMeanCenteredGram_eq_cotangentSawtoothForm hp hq] at h
  linarith

/-- **The uncentered Gram.** `G(p, q) = C(p, q) - D(p) D(q) + Λ(p) Λ(q)`. -/
theorem pmRamanujanPrimitiveGram_eq_cotangentSawtoothForm {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    pmRamanujanPrimitiveGram p q =
      cotangentSawtoothForm p q - sieveCenteringDiscrepancy p * sieveCenteringDiscrepancy q +
        vonMangoldt p * vonMangoldt q := by
  rw [pmRamanujanPrimitiveGram_eq_energyCentered (by omega) (by omega),
    pmRamanujanEnergyCenteredGram_eq_cotangentSawtoothForm hp hq]
  ring

/-- The uncentered Gram in closed form. -/
def explicitPrimitiveGram (p q : ℕ) : ℝ :=
  cotangentSawtoothForm p q - sieveCenteringDiscrepancy p * sieveCenteringDiscrepancy q +
    vonMangoldt p * vonMangoldt q

/-- **The dilation profile at prime ratios.** For primes `p, q ∤ r`,
`√p √q Φ_r(p/q)` is the finite sum of the four explicit Gram entries. -/
theorem pmRamanujanDilationProfile_eq_explicit {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : 1 < r) (hpr : ¬ p ∣ r) (hqr : ¬ q ∣ r) :
    Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) * pmRamanujanDilationProfile r hr ((p : ℝ) / q) =
      explicitPrimitiveGram (p * r) (q * r) + explicitPrimitiveGram (p * r) r +
        explicitPrimitiveGram (q * r) r + explicitPrimitiveGram r r := by
  have hpr2 : 2 ≤ p * r := le_trans hp.two_le (Nat.le_mul_of_pos_right p (by omega))
  have hqr2 : 2 ≤ q * r := le_trans hq.two_le (Nat.le_mul_of_pos_right q (by omega))
  rw [← pmRamanujanPrimitiveGram_two_prime_mul_eq_dilationProfile hp hq hr hpr hqr]
  simp only [explicitPrimitiveGram]
  rw [pmRamanujanPrimitiveGram_eq_cotangentSawtoothForm hpr2 hqr2,
    pmRamanujanPrimitiveGram_eq_cotangentSawtoothForm hpr2 (by omega),
    pmRamanujanPrimitiveGram_eq_cotangentSawtoothForm hqr2 (by omega),
    pmRamanujanPrimitiveGram_eq_cotangentSawtoothForm (by omega) (by omega)]

/-- The profile itself, dividing by `√(pq) > 0`. -/
theorem pmRamanujanDilationProfile_eq_explicit_div {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : 1 < r) (hpr : ¬ p ∣ r) (hqr : ¬ q ∣ r) :
    pmRamanujanDilationProfile r hr ((p : ℝ) / q) =
      (explicitPrimitiveGram (p * r) (q * r) + explicitPrimitiveGram (p * r) r +
        explicitPrimitiveGram (q * r) r + explicitPrimitiveGram r r) /
          (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) := by
  have hpos : 0 < Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) :=
    mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)) (Real.sqrt_pos.mpr (by exact_mod_cast hq.pos))
  rw [eq_div_iff hpos.ne', mul_comm, pmRamanujanDilationProfile_eq_explicit hp hq hr hpr hqr]

end

end GaloisForLFunctions.BezoutValuationIncidence
