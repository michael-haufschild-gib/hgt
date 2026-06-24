# Even Seam Finite-Part Canonicality

- **ID:** even-seam-finite-part-canonicality
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-domain normalization
- **Source:** `xf1-square-tests-outside-weil-class.md`,
  `docs/consolidated/gpt/proof7.md`,
  `docs/consolidated/revision01/bridge-theorem.md`
- **Statement:** The singular reciprocal Weil pullback has a canonical
  regulator-independent Hadamard finite part once the seam source distribution
  is even and completed. The resulting bilinear form is necessarily Hankel in
  the polynomial coefficients. This proves the finite-part domain is not a
  cutoff-choice artifact; it does not prove the scalar Weyl sign.

## Setup

Let `W` be an even source distribution on the spectral variable `t` satisfying:

1. near `t=0`, `W` is represented by an even smooth germ

   `W(t) ~ sum_{r>=0} omega_{2r} t^{2r}`;

2. at infinity, pairings with functions `O(t^-2)` have the standard completed
   explicit-formula tail bound `O(log R / R)` after the large window is removed.

For real polynomials

`p(y)=sum_i c_i y^i`, `q(y)=sum_j d_j y^j`,

write

`p(y)q(y)=sum_n b_n y^n`, where `b_n=sum_{i+j=n} c_i d_j`.

The singular reciprocal pullback is

`h_{p,q}(t)=t^-2 p(t^-2)q(t^-2)=sum_n b_n t^{-2n-2}`.

Choose even cutoffs `eta, psi` with `eta(u)=0` near `0`, `eta(u)=1` away from
`0`, `psi(u)=1` near `0`, and `psi` compactly supported. Define

`h_{p,q}^{eps,R}(t)=h_{p,q}(t) eta(t/eps) psi(t/R)`.

For every `eps>0` and finite `R`, this is an admissible smooth compactly
supported even test.

## Theorem

For fixed `R`, as `eps -> 0`,

`<W,h_{p,q}^{eps,R}>
 = sum_m A_m[p,q;eta] eps^{-m} + C_R[p,q;eta,psi] + o(1)`,

where `m` ranges over odd positive integers at most
`2 deg(pq)+1`. There is no logarithmic term in the even seam normalization.

The finite constant

`C_R[p,q;eta,psi] =
 FP_{eps=0}<W,h_{p,q}^{eps,R}>`

is independent of the seam cutoff `eta`. If the infinite-window limit exists by
the tail hypothesis, then

`F[p,q]=lim_{R->infty} C_R[p,q;eta,psi]`

is also independent of the large-window cutoff `psi`.

Moreover `F` is a Hankel bilinear form:

`F[p,q]=sum_{i,j} c_i d_j f_{i+j}`

for a sequence `f_n` determined by the completed source distribution and the
chosen canonical gauge.

## Proof

The local divergent part comes only from `t` comparable to `eps`, because
`psi(t/R)=1` near the seam. Pair the Laurent monomial `b_n t^{-2n-2}` with the
local jet `omega_{2r} t^{2r}`:

`b_n omega_{2r} t^{2r-2n-2}`.

For `0 <= r <= n`, integration over the punctured seam produces the negative
power

`eps^{-(2n+1-2r)}`.

Thus the divergent powers are

`eps^{-(2n+1)}, eps^{-(2n-1)}, ..., eps^{-1}`.

All exponents are odd. A logarithmic term would require a local `t^-1` term,
equivalently

`2r - 2n - 2 = -1`.

This has no integer solution. Therefore the even seam-normalized expansion has
no logarithmic divergence.

Now compare two seam cutoffs `eta` and `tilde_eta`. Their difference is
supported where `t` is comparable to `eps`. After substituting `t=eps u`, the
local contribution is a finite sum of terms

`b_n omega_{2r} eps^{2r-2n-1}
 int u^{2r-2n-2}(eta(u)-tilde_eta(u)) du`

plus terms vanishing with `eps`. The negative powers are precisely the local
counterterms subtracted in the Hadamard finite part. A finite cutoff-dependent
constant could occur only in the same missing case

`2r - 2n - 2 = -1`.

Since that equation has no integer solution, the finite part is independent of
the seam cutoff.

For the large window, two choices of `psi` differ only where `t` is comparable
to `R`. Since

`h_{p,q}(t)=p(0)q(0)t^-2 + O(t^-4)`

and the completed source tail is `O(log R / R)` on `O(t^-2)` tests, the
difference of the corresponding finite constants tends to `0` as `R -> infinity`.
Hence the infinite-window finite part, when the stated tail hypothesis holds,
is independent of `psi`.

Finally, every local coefficient and every finite constant depends on `p` and
`q` through the product coefficients

`b_n=sum_{i+j=n}c_i d_j`.

Therefore the limiting bilinear form has the Hankel shape

`F[p,q]=sum_n f_n b_n=sum_{i,j}c_i d_j f_{i+j}`.

## Gauge Note

At the seam-residue level, a zero-free even gauge change
`Xi(w) -> exp(q(w^2)) Xi(w)` changes the extracted reciprocal moments by a local
diagonal/Hankel counterterm. Thus this finite-part lemma must be used after
fixing the completed `xi` normalization, or after subtracting the corresponding
local gauge counterterm. It does not license arbitrary finite-part
normalizations.

## Consequence for the RH Route

`xf1-square-tests-outside-weil-class.md` proves that the raw reciprocal square
tests cannot be inserted directly into the standard Weil test class. This theorem
shows the next source-domain step is mathematically well-defined: the even
seam finite part is canonical under the completed source hypotheses and produces
a Hankel boundary form.

The remaining RH-bearing work is not regulator choice. It is the separate
source theorem identifying this canonical finite-part boundary form with the
rank-one Gamma/Uvarov bulk form and proving the scalar Weyl sign for all degrees.

## Theatre Test

For any proposed regularized Weil-pullback proof, ask:

1. Is the seam regulator even and tied to the fixed point `s=1/2`?
2. Are all divergent powers subtracted as local source counterterms?
3. Is there a logarithmic or gauge term, and if so is it explicitly removed by
   the canonical `xi` normalization?
4. Does the proof establish the scalar sign from the source form, rather than
   choosing a finite part that makes the sign true?

## Gates

- [x] 0 -> 1 in-progress: finite-part canonicality extracted from the
  singular Weil-pullback route.
- [x] 1 -> 2 fully-proven: local expansion, cutoff independence, window
  independence, and Hankel form proved under stated source/tail hypotheses.
- [ ] 2 -> 3 formalized: optional distribution-free lemma for even Laurent
  finite parts and cutoff independence.

## Log

- 2026-06-24 -- Codex: created to separate the proved finite-part domain
  canonicality from the still-open scalar Weyl positivity theorem.

## 2026-06-24 reciprocal gauge specialization

`reciprocal-seam-canonical-gauge-extraction.md` records the exact zero-free gauge law for the moments extracted by this finite-part domain. The finite part is regulator-canonical, but a different zero-free even representative of the completed function changes the extracted reciprocal tower by a local Hankel counterterm.

Thus the finite-part construction must be paired with the canonical completed `xi` normalization, or with the explicit diagonal subtraction in that card.
