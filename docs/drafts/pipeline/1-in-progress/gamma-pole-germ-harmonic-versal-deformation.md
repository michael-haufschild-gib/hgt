# Harmonic versality of the Gamma factorial pole germ

- **ID:** `gamma-pole-germ-harmonic-versal-deformation`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM
- **Scientific status:** `[CONJECTURE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The exact Gamma factorial pole germs form a separating deformation of the
  reciprocal germ: no nonzero differential polynomial over `ℂ(x)` vanishing at `-1/x` vanishes
  coefficientwise on every Gamma pole germ.

## Goal

Prove injectivity of the complete intrinsic residue map attached to

\[
  g_n(x)=\Gamma\!\left(-n+\frac{(-1)^{n+1}}{n!}x\right).
\]

This is the missing local theorem for differential descent through the positive Gamma-iterate
tower.  The deformation parameters are not arbitrary constants: the exact product formula makes
their coefficients triangular expressions in the generalized harmonic sequences
`H_n, H_n^(2), ...`, together with factorial and parity data.

## Prior-theory boundary

Ablinger--Schneider prove that the sequence realizations of quasi-shuffle basis harmonic sums are
algebraically independent over rational sequences with the alternating sequence adjoined.  In
particular, the depth-one generalized harmonic sums are candidate independent parameters for the
Gamma pole germ.  That theorem is input, not novelty.  The prospective new result is that these
parameters enter the differential jet of the Gamma pole germ triangularly enough to separate the
entire reciprocal differential ideal, and hence make composition-depth descent injective.

## Exact source identity

With `s_n=(-1)^(n+1)/n!` and `u=s_n x`,

\[
  g_n(x)=-\frac1x\,
  \frac{\Gamma(1+u)}{\prod_{j=1}^{n}(1-u/j)}.
\]

Its formal logarithmic coefficients are

\[
  [x] \log\!\left(\frac{g_n(x)}{-1/x}\right)=s_n(H_n-\gamma),
\]

and, for `k≥2`,

\[
  [x^k] \log\!\left(\frac{g_n(x)}{-1/x}\right)
   =\frac{s_n^k}{k}\bigl(H_n^{(k)}+(-1)^k\zeta(k)\bigr).
\]

The signs are fixed by the displayed Euler product and must be verified formally before use.

## Proposed algebraic mechanism

1. Work with a finite truncated formal unit
   `U(x)=exp(Σ_{k=1}^N A_k x^k/k)` over a polynomial coefficient ring.
2. Prove a triangular jet theorem: for every nonzero differential polynomial in the reciprocal
   differential ideal, substitution `y=-U/x` has a nonzero coefficient polynomial in the largest
   parameter `A_k` that occurs.
3. Specialize `A_k` to the exact Gamma coefficients.  Algebraic independence of the generalized
   harmonic sequences prevents that coefficient from vanishing eventually, while factorial order
   and parity separate distinct `s_n` powers.
4. Feed the resulting local injectivity theorem into composition-depth descent.

## Falsifiers

- A nonzero differential polynomial that vanishes for `-U/x` for every formal unit `U` retires the
  versality claim.  This should be impossible because every invertible germ is of this form, but
  the coefficient-level statement must account for finite truncation and denominators.
- Failure of triangularity after specializing the `A_k` to Gamma data may leave cancellations
  between factorial orders or between harmonic basis monomials.
- If the required depth-one generalized harmonic sequences are not among the algebraically
  independent quasi-shuffle basis sequences in the precise published sequence ring, the proposed
  specialization argument is invalid.
- A published theorem already proving differential independence of the positive Gamma-iterate
  tower retires novelty even if this proof route is correct.

## Gates

- [x] 0 → 1 in-progress: source-pure exact identity, prior-theory boundary, attack, and falsifiers
  isolated
- [ ] 1 → 2 fully-proven: formal-germ separation, Gamma specialization, and differential descent
  proved on paper
- [ ] 2 → 3 formalized: unconditional local injectivity and joint iterate theorem in Lean, with
  targeted builds and axiom audits
- [ ] 3 → 4 publication-ready: independent specialist novelty review and standalone paper complete

## Log

- 2026-07-15 — opened after the all-order parity-tail ladder closed coordinatewise detection.  The
  remaining obstruction is product cancellation inside the reciprocal differential ideal.

