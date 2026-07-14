# Xi endpoint source height gap

- **ID:** `xi-endpoint-source-height-gap`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / VALUE-RELATION CONSEQUENCE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean file:** `formal/GaloisForLFunctions/RHTower/XiEndpointSourceHeightGap.lean`
- **Statement:** The completed endpoint value forces every Xi zero to satisfy
  \[
  1<|\operatorname{Im}\rho|,
  \]
  and therefore the centered completed function is zero-free on the explicit closed slab
  \[
  |\operatorname{Re}z|\le 1\quad\Longrightarrow\quad \Xi_C(z)\ne0.
  \]

## Goal

Turn the exact endpoint source value

\[
C_\Xi=2+\gamma-\log(4\pi)<\frac12
\]

into a reusable, explicit source regularity domain.  The corpus previously supplied only a
qualitative existential lower height gap by compactness and the absence of real Xi zeros.  The
endpoint value gives the concrete bound `1 < |Im rho|` directly and without choosing or
enumerating any zero.

This closes the following lower proof chain:

\[
C_\Xi<\frac12
\longrightarrow
\frac1{C_\Xi}-1>1
\longrightarrow
(\operatorname{Im}\rho)^2>1
\longrightarrow
|\operatorname{Im}\rho|>1
\longrightarrow
\Xi_C(z)\ne0\ \text{for }|\operatorname{Re}z|\le1.
\]

It does not orient the Xi divisor horizontally and hence does not prove RH.  Its contribution is
an unconditional pole-free domain for later continued-source, Cauchy, Taylor, and local transfer
arguments.

## Proof

The already formalized endpoint source-height inequality is

\[
\frac1{C_\Xi}-1\le (\operatorname{Im}\rho)^2
\]

for every multiplicity copy of every Xi divisor point.  Positivity of `C_Xi` and the exact strict
bound `C_Xi < 1/2` give `2 < 1/C_Xi`, so the right-hand side is strictly larger than one.  A first
multiplicity copy exists at every support point because the Xi divisor order is positive there;
this removes the copy index.  The equivalence between Xi zeros and divisor support removes the
support wrapper.

Finally,

\[
\Xi_C(z)=\xi\!\left(\frac12+iz\right),
\qquad
\operatorname{Im}\!\left(\frac12+iz\right)=\operatorname{Re}z.
\]

Thus a zero of `XiC` in `|Re z| <= 1` would contradict the explicit height gap.

No RH assumption, zero enumeration, real-rootedness, anti-Herglotz positivity, or limiting
measure is used.

## Literature calibration

The Laurent expansion and the appearance of Euler's constant are classical; see
[DLMF §25.2](https://dlmf.nist.gov/25.2).  The bound here is valuable as an internally derived,
source-pure Lean theorem, not as the strongest known numerical zero-free height.  Platt and
Trudgian rigorously verified RH through height `3,000,175,332,800` using interval arithmetic and
Turing's method; see [arXiv:2004.09765](https://arxiv.org/abs/2004.09765).  Their theorem is a
large finite computation.  The present result instead derives the fixed symbolic slab directly
from the exact completed endpoint value already used elsewhere in the formal corpus.

## Lean certificate

The public declarations are:

```text
xiZeroCopy_one_lt_im_sq
xiZeroCopy_one_lt_abs_im
xiDivisorSupport_one_lt_im_sq
xiDivisorSupport_one_lt_abs_im
one_lt_im_sq_of_xi_eq_zero
one_lt_abs_im_of_xi_eq_zero
xi_ne_zero_of_abs_im_le_one
XiC_ne_zero_of_abs_re_le_one
```

The module is imported by `GaloisForLFunctions.RHTower`.

## Gates

- [x] 0 → 1 in-progress: explicit endpoint-to-height consequence identified
- [x] 1 → 2 fully-proven: source-height proof complete
- [x] 2 → 3 formalized: Lean module is placeholder-free and umbrella-wired
- [ ] 3 → 4 publication-ready: not proposed; this is a classical quantitative bridge
