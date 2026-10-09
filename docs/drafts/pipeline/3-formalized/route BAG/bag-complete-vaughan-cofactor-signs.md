# Complete Vaughan cofactor signs

- **Stage:** 3-formalized

Continuation01am, BAG full signed axes route. This closes a false extension
of the prime-subfamily alias obstruction, not the signed cubic estimate.

If V<n<=2V, every proper divisor d of n satisfies d<=n/2<=V. The full
Möbius divisor sum is zero since n>1. Consequently the truncated divisor
sum through V is -mu(n), so the actual short coefficient
1-zeta*mu_(<=V) equals mu(n). The squarefree restriction changes nothing:
mu(n) already vanishes outside squarefree integers.

If U>=1 and n<=2UV, each active Type-II term has prime d>U, m=n/d<=2V.
Terms m<=V vanish by the existing support law. Every remaining term is
log(d)*mu(m). The exact coprimality mask is retained. This classifies the
ENTIRE Type-II source on this support, including composite cofactors.

For every odd prime V, mu(2V)=mu(2)mu(V)=1. Thus the actual short coefficient
at 2V is positive. Euclid's theorem supplies such prime cutoffs above every
threshold. No eventual nonpositivity claim about the full short source can
follow from its prime-cofactor values -1.

Positive survivor: exact signed Möbius classification of the full seam
source and a cofinal family of positive actual coefficients. All four
statements are formalized and audited in ChiPrimeGaussianCubicPrimeOnlyVaughan.
No whole-alias cancellation, physical cubic saving, or RH proof follows.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicPrimeOnlyVaughan` | `vaughanSquarefreePart_vonMangoldt`, `vaughanPrimeTypeII_eq`, `vaughanPrimeCoefficient_eq`, `vaughanPrimeTypeII_eq_of_le_sq`, `sum_primes_eq_vaughanPrimeCoefficient`, `vaughanPrimeShort_eq_moebius_seam`, `vaughanPrimeTypeII_eq_moebius_seam`, `vaughanPrimeShort_twice_prime`, `exists_vaughanPrimeShort_positive_after`, `primeGaussianCubicOffDiagonal_eq_primeOnlyVaughan` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
