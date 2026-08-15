# Compressed prime-shift arithmetic complement — formalized closure

- **ID:** `ccm-compressed-prime-shift-arithmetic-complement-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-compressed-prime-shift-arithmetic-complement-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

- `GaloisForLFunctions.RHTower.CCMCompressedShiftIndependence`

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(2)` | `weightedShift`, `weightedShift_comp` | the weighted translation `S h f x = e^h f(x-h)` and the semigroup law `S h ∘ S k = S(h+k)` |
| `(3)` | `compressedShift` | the aperture compression `T A h = P_A S h P_A` |
| `(4)`–`(8)` | `linearIndependent_compressedShift` | stated more strongly than the card: the shifts need only be *injective* with values in `[0,A)`, no ordering. The separating interval length may be chosen after fixing the coefficient to be isolated, so the single global `ε` of `(6)` is unnecessary. Witness: the indicator of `[0,ε]`, evaluated at `h j₀ + ε/2` |
| `(8a)` | `linearIndependent_weightedShift_apply` | the pointed cyclic strengthening. The card proves it by Fourier transform plus the identity theorem for exponential polynomials; the Lean proof uses the rightmost point of the support — at the largest shift with nonzero coefficient every other term has already left `sSup (support f)`. Needs only `HasCompactSupport f` and `f ≠ 0`, and avoids the Fourier interface |
| `(10)`–`(11)` | `linearIndependent_compressedShift_primes`, `linearIndependent_rat_compressedShift_primes`, `linearIndependent_rat_logPrimes` | distinct prime logarithms below the aperture give compressed shifts independent over `ℂ`, hence over `ℚ`: injectivity of `J_(A,N)` and faithfulness of the prime-log operator carrier. The `ℚ` half transports the corpus theorem `GaloisForLFunctions.linearIndependent_log_primes` along the prime family |
| `(16c)` | `kreinBlock_identity` | with weights `a n` and feature maps `√(a n)(T n ± c v)`, the difference of squared norms is `4c` times the weighted real part of the diagonal pairings — the parallelogram identity carrying the indefinite factorization `(16d)`, for an arbitrary complex inner-product space and arbitrary finite index set |
| `(14)` | `quotientEquivRangeQuotient` | an injective linear map identifies `V/D` with `J(V)/J(D)`, so `A_N` is canonically the operator quotient |
| `(10)`, `(16)` | `finrank_quotient_add_finrank_submodule`, `finrank_le_finrank_quotient_add`, `finrank_span_logPrimes`, `finrank_primeLog_le_quotient_add` | the prime-log space of `r` distinct primes has dimension exactly `r`, and a phase subspace of dimension at most `b` leaves `dim_ℚ A_N ≥ r - b` |

Every independence statement of the card is pointwise, so the shifts are realized as linear maps on
functions and the proofs use no measure theory: the weighted `L²` translation representation the
earlier decision waited for is not needed.

## Axioms

`#print axioms` on every theorem returns exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Deliberately outside the Lean statement

Not theorems of this card: the operator-norm identity `‖S h‖ = e^{h/2}` on `L²(ℝ, e^{-x} dx)`, which
needs that weighted measure; and the signed-Gamma orbit-charge bound `(15)`, an imported result of
`signed-archimedean-gamma-orbit-charge-phase-law.md` that enters `(16)` only as the numerical value
of `b`.

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.
