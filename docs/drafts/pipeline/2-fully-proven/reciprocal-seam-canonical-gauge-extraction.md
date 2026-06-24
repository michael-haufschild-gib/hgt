# Reciprocal Seam Canonical Gauge Extraction

- **ID:** reciprocal-seam-canonical-gauge-extraction
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-domain normalization
- **Source:** `even-seam-finite-part-canonicality.md`,
  `seam-log-hankel-rh-equivalence.md`,
  `docs/consolidated/gpt/proof9.md`
- **Statement:** The reciprocal seam moments extracted from the completed
  logarithmic derivative are diagonal under zero-free even gauge changes:
  `Xi(w) -> exp(q(w^2)) Xi(w)` shifts only `T_k`, by
  `2k(-1)^{k+1}a_k` when `q(w^2)=sum a_r w^{2r}`. Thus the shifted Hankel
  tower is source-defined only after fixing the canonical completed `xi`
  representative or subtracting this explicit local Hankel counterterm.

## Setup

Let

`Xi(w)=xi(1/2+w)`.

It is even, so a nonzero zero orbit is `{a,-a}`. Set

`y_a=-a^{-2}`.

The folded reciprocal moments are

`T_k=sum_{[a]} 2 m_a y_a^k`, for `k>=1`.

Equivalently,

`Xi'(w)/Xi(w)=sum_{n>=0} (-1)^n T_{n+1} w^{2n+1}`

in the canonical divisor expansion near `w=0`.

Define the monomial seam extractor

`h_k(w)=2(-w^{-2})^k=2(-1)^k w^{-2k}`

and

`E_k(F)=FP_{w=0}[-(1/2) h_k(w) F'(w)/F(w) dw]`.

The finite part is read in the canonical even seam sense of
`even-seam-finite-part-canonicality.md`.

## Theorem

For the canonical completed function,

`E_k(Xi)=T_k`.

If

`F_q(w)=exp(q(w^2))F(w)`, with `q(w^2)=sum_{r>=1} a_r w^{2r}`,

then

`E_k(F_q)=E_k(F)+2k(-1)^{k+1}a_k`.

Consequently, on the shifted `Q_0` Hankel tower

`H^{(0)}_{ij}=T_{i+j+1}`,

the zero-free gauge counterterm is

`(Delta_q H^{(0)})_{ij}
 = 2(i+j+1)(-1)^{i+j+2} a_{i+j+1}`.

This counterterm is Hankel and completely local in the seam gauge coefficients.

## Proof

For one folded zero orbit `{a,-a}`,

`1/(w-a)+1/(w+a)=2w/(w^2-a^2)`.

Since `y_a=-a^{-2}`,

`2w/(w^2-a^2)=2w y_a/(1+y_a w^2)
 = 2 sum_{n>=0} (-1)^n y_a^{n+1} w^{2n+1}`.

Summing over folded orbits gives

`Xi'(w)/Xi(w)=sum_{n>=0} (-1)^n T_{n+1} w^{2n+1}`.

Multiplying by `-(1/2)h_k(w)` gives

`-(1/2) 2(-1)^k w^{-2k}
 sum_{n>=0} (-1)^n T_{n+1} w^{2n+1}`.

The residue term occurs only at `n=k-1`, and its coefficient is `T_k`.
Therefore `E_k(Xi)=T_k`.

Now apply a zero-free even gauge. Since

`F_q'(w)/F_q(w)=F'(w)/F(w)+d/dw q(w^2)`,

and

`d/dw q(w^2)=sum_{r>=1} 2r a_r w^{2r-1}`,

the change in the extractor is the residue of

`-(1/2) 2(-1)^k w^{-2k}
 sum_{r>=1} 2r a_r w^{2r-1}`.

A residue occurs only when `2r-1-2k=-1`, hence only when `r=k`.
The coefficient is

`-2k(-1)^k a_k = 2k(-1)^{k+1}a_k`.

Thus

`E_k(F_q)=E_k(F)+2k(-1)^{k+1}a_k`.

Finally, `Q_0[p]=sum_{i,j} b_i b_j T_{i+j+1}`. Substituting the moment shift
with `k=i+j+1` gives

`(Delta_q H^{(0)})_{ij}
 = 2(i+j+1)(-1)^{i+j+2}a_{i+j+1}`,

which depends only on `i+j`, so it is Hankel.

## Consequence for the RH Route

The source-built shifted tower is not the raw Taylor jet of an arbitrary
zero-free representative of the completed function. It is the canonical
completed `xi` representative, or an equivalent representative corrected by the
explicit diagonal law above.

This closes a false route: one cannot alter low-order or all-order seam moments
with a zero-free even multiplier, read the resulting Hankel positivity, and call
that a source proof. The multiplier moves no zero; its effect is a local Hankel
counterterm, not divisor information.

The remaining RH-bearing work is unchanged: after canonical extraction, prove
the source-built shifted tower lies in the Stieltjes/Markov cone, equivalently
prove the all-degree scalar boundary-Weyl sign.

## Theatre Test

For any proof using reciprocal seam moments:

1. Which representative of the zero-free even gauge class is being used?
2. If it is not the canonical completed `xi`, what are the coefficients `a_k`?
3. Has the counterterm `2k(-1)^{k+1}a_k` been subtracted from every `T_k`?
4. Is positivity proved after canonical extraction, rather than created by the
   chosen gauge?

## Gates

- [x] 0 -> 1 in-progress: reciprocal seam gauge ambiguity isolated.
- [x] 1 -> 2 fully-proven: extractor law and Hankel counterterm proved.
- [ ] 2 -> 3 formalized: optional Laurent-series residue theorem.

## Log

- 2026-06-24 -- Codex: created to promote the reciprocal-seam version of the
  canonical-gauge law already present in consolidated proof notes.
