# The Mertens mean and the prime-harmonic residue agree (2026-08-07)

Module `RHTower/PrimeReaderCompatibility.lean`, `lake build` green (8661 jobs), axioms
`[propext, Classical.choice, Quot.sound]`, in the RHTower umbrella. Ties together
`mem:mertens_prime_mean_reader_2026_08_07` and
`mem:route_r/analytic_abscissa_reader_formalized_2026_08_07`.

## The comparison

The two readers act on different objects and annihilate different ideals:

| reader | weight | normaliser | ideal |
|---|---|---|---|
| Mertens mean | `log p / p` | `log X` | `M_0` (⊇ `T_1`) |
| prime-harmonic residue | `1 / p` | unit mass, or `-log(s-1)` | `ℓ¹ + o(1/p)` |

They are compatible because `log p ≥ log 2` on the primes, so critical summability is STRONGER than
plain harmonic summability:

- `summable_primes_of_memCriticalSummableLayer` — transports `T_1` from the ℕ index to `Nat.Primes`
  via `Function.Injective.summable_iff` (the indicator vanishes off the range of the coercion).
- `summable_primeHarmonic_of_memCriticalSummableLayer` — **`T_1` implies `∑_p |b_p|/p < ∞`**, by
  dividing out the logarithmic weight against `Real.log 2`.
- `rescaledPrimeField b p = ((b p / p : ℝ) : ℂ)`, and
  `hasReferenceResidue_rescaledPrimeField` — if `b - c ∈ T_1` then that rescaled field has
  prime-harmonic residue `c`.
- `mertensPrimeMean_and_abscissaReader_agree` — both devices report the same `c`.
- `tendsto_profileAverage_rescaledPrimeField` — and so does every bounded cofinal unit profile.

## Why it matters

The "universal reading law" now has two independent instances *and* a proof that they are consistent
on the overlap. Without this, nothing ruled out the two devices disagreeing on a field both can read.

## Lean notes

- Casting `(b p / p : ℝ) : ℂ` minus `c * ((p⁻¹ : ℝ) : ℂ)` into a single `ofReal`: state the identity
  as a `have hEq` with `((p:ℕ):ℝ)⁻¹` written out (NOT via `primeHarmonicWeight`, or the later
  `rw [primeHarmonicWeight]` breaks the match), then `push_cast; ring`.
- Chaining `← Complex.ofReal_natCast, ← Complex.ofReal_inv, …` to fuse casts fails with an
  instance-transparency type error; the `hEq` route is robust.
- `field_simp` sometimes closes a `show` goal outright — a trailing `ring` then errors with
  "No goals to be solved".
