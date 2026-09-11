# PW-B reciprocal endpoint moments and Gamma normalization

- **ID:** PW-B-GAMMA-RECIPROCAL-MOMENTS-2026-09-11
- **Status:** Paper proof, all thirteen public Lean theorems and targeted leaf build passed; formal lint passed.
- **Route:** PW-B remains live. RH is not proved.
- **Continuation:** [actual reversible pairing](../1-in-progress/pw-b-gamma-reversible-pairing.md).

For a>0, k a natural number, let

`I_(k+2)(a) = integral_(x>0) exp(-x-a/x)/x^(k+3) dx`,

and `R_k(a)=I_(k+2)(a)/(k+1)!`. These are the higher reciprocal
endpoint moments of the actual positive response modes.

## Closed paper argument

The positive-ray map x -> a/x is an involution, with absolute derivative
a/x^2. Applying the actual one-dimensional integral change of variables gives

`I_(k+2)(a) = a^(-k-2) * integral_(x>0) exp(-x-a/x)*x^(k+1) dx`.

All integrals are admitted. For every natural l, the exponential-series
bound exp(-y)<=m!/y^m, with m=k+3+l, gives

`0 < exp(-x-a/x)/x^(k+3)`

and

`exp(-x-a/x)/x^(k+3) <= (k+3+l)!*a^(-k-3-l)*exp(-x)*x^l`.

Consequently

`0 < I_(k+2)(a) <= (k+3+l)!*l!*a^(-k-3-l)`.

After inversion, apply 1-a/x<=exp(-a/x)<=1. Integrating the two
ordinary Gamma weights and using (k+1)!=(k+1)*k! yields

`a^(-k-2)*(1-a/(k+1)) <= R_k(a) <= a^(-k-2)`.

The lower bound can be negative; the actual moment is strictly positive.
At a=1 this gives `|R_k(1)-1|<=1/(k+1)` and hence R_k(1)->1.
For a>1, the upper bound is geometric and gives R_k(a)->0.
No numerical evaluation of Gamma or the integral is used.

## Complete signed-source step

The original coefficient is
`c_n(z)=mu(n+2)*sqrt(n+2)*exp(-z*log(n+2))`, with mode a=n+1.
Choose a natural N with norm(z)<=N. The existing source theorem gives
`norm(c_n(z)) <= (n+2)^(N+1) <= 2^(N+1)*(n+1)^(N+1)`.
For k>=N+1, the normalized terms therefore have the fixed summable bound
`norm(c_n(z)*R_k(n+1)) <= 2^(N+1)/(n+1)^2`.
This is the precise admission needed to pass the high-order limit through
the full signed series. Its limit is
`c_0(z)=-sqrt(2)*exp(-z*log(2))`, which is nonzero for every z.
The bound with arbitrary l additionally admits each fixed unnormalized
arithmetic moment before taking any high-order limit.

The [complete signed-source theorem](pw-b-gamma-moment-detector.md) now
proves this limit, its exact original-source integral identity, absolute
admission at every order and eventual nonvanishing in Lean scratch. The original cutoff integral's
all-order expansion must also be proved before extracting these moments
from the all-power current flatness in the
[ground-boundary theorem](pw-b-gamma-ground-boundary.md). This card does
not prove the corrected scalar-ansatz obstruction, actual Xi occurrence,
complete adjoint domains, or independently forced Ward balance.

## Corpus and literature

Two deep/method searches used reciprocal integral substitution and high-order
coefficient recovery as queries. Both returned partial coverage of 730683
indexed declarations, with a reranking deadline and incomplete compiler
metadata. Every returned candidate and source-argument statement was
inspected. The exact Gamma integral, Jacobian substitution and dominated
series-limit APIs were checked against their source. The generated
geometric-decay plan involving filled Julia-set volume does not establish
arithmetic moment recovery. Raw results are retained in
[pw-b-gamma-reciprocal-moments-searches.json](../1-in-progress/pw-b-gamma-reciprocal-moments-searches.json).

Broad curvature and drift searches included recent September 2026 arXiv
listings. [Wink, A Thorpe trick for the Bochner technique](https://arxiv.org/html/2609.11653v1),
Proposition 2.4 and Theorem 2.7, preserve a curvature pairing by corrections
in its exact orthogonal annihilator and characterize improved positivity.
A possible transfer would require an independently established annihilator
of the full PW source pairing and appropriate cone/domain hypotheses;
those are not supplied by the paper. Further broad subordination/rigidity
queries returned old or unrelated hits; the direct subordination listing
returned HTTP 429. No literature result is being treated as a Ward proof.

## Verification

Scratch passed with exit code 0 and no diagnostics. Exact scratch source is promoted in `ThetaCuspHawkingParikhWilczekGammaReciprocalMoments`, with one umbrella import. The targeted leaf build passed in 61 seconds, with only this leaf built. Formal lint passed.
No further axiom-print checks: user explicitly stopped that workflow.
