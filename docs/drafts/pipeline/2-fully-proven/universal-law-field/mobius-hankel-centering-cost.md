# Global centering has a divergent Gamma--Hankel compatibility cost

- ID: ULF-MHBR-001-S1
- Parent: `../../1-in-progress/universal-law-field/mobius-hankel-bounded-returns.md`
- Status: dependency-closed paper proof; Lean verification pending.
- Scope: quantitative obstruction to transporting a bounded energy estimate by global centering;
  neither a disproof nor a proof of Möbius bounded returns.

## Exact theorem

For real coefficients a=(a_1,...,a_N), let
E_N(a;r)=Gamma(r) sum_(1<=m,n<=N) a_m a_n/(m+n)^r.
For r>0, N>=1 and real b,

    E_N(a;r)+E_N(a-b;r)
      >= b^2 E_N(1;r)/2
      >= Gamma(r) b^2 N^2 / (2(2N)^r).

The first constant 1/2 is sharp: equality holds for a_n=b/2.
Here a-b means subtraction from every physical coefficient, not merely removal of a tail.

Put P_N=prod_(p<=N)(1-1/p), b_N=P_N^2. For every fixed 0<r<2 and every
triangular array a_(N,n),

    E_N(a_N;r)+E_N(a_N-b_N;r) -> +infinity.

Consequently, for every A,B, eventually E_N(a_N;r)>A or E_N(a_N-b_N;r)>B.
Neither energy individually is asserted to diverge. In particular, the assertion applies
unconditionally to the actual Möbius coefficients and to all r_k=1+1/(k+2), k>=0.

## Proof

1. The corpus identity `integral_finiteRealLaplacePencil_sq` represents E_N as
   integral_0^infinity x^(r-1) (sum a_n exp(-nx))^2 dx. It proves E_N>=0 for r>0.
2. Expand the quadratic form, retaining all signed cross terms:

       2 E_N(a;r)+2 E_N(a-b;r)=E_N(2a-b;r)+b^2 E_N(1;r).

   Positivity of the first term on the right gives the first inequality. For a=b/2 it vanishes,
   proving sharpness without a source-dependent hypothesis.
3. Since 2<=m+n<=2N and r>0, each of the N^2 flat-source entries is at least (2N)^(-r).
   Multiplication by the positive Gamma(r) gives the second inequality.
4. `tendsto_mertensPrimeProduct_mul_log` gives P_N log N -> exp(-EulerGamma)>0.
   For s=2-r>0, (log N)^4/N^s ->0. Therefore

       P_N^4 N^s = (P_N log N)^4 / ((log N)^4/N^s) -> +infinity.

   The lower bound in step 3 is Gamma(r)/(2*2^r) times this expression. Its coefficient
   is positive, so comparison proves the asserted divergence and eventual disjunction.

## Meaning and limits

- `PrimeSquareMobiusSectorFracture` proves the finite periodic Euler clock has mean
  prod_(p in P)(1-1/p)^2 and agrees with mu where P covers the prime factors of the index.
  Choosing P={p<=N} makes this mean exactly b_N and matches the first N physical coefficients.
- Subtracting this periodic mean globally incurs a coherent error of order at least
  N^(2-r)/(log N)^4 in the sum of the two energies. Centered clocks are therefore not
  bounded-energy substitutes for their matching physical prefixes in the critical range.
- This is a classical quadratic identity plus an existing unconditional Mertens asymptotic,
  newly applied to the proposed repair. No novelty beyond that application is claimed.
- Tail-only changes, alternative source-faithful constructions, and the original signed
  covariance bound are not excluded. No general ban on positivity is inferred.
