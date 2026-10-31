# Harmonic Gram remainders have a logarithmic plateau

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Q1/O1](../1-in-progress/three-frontier-questions-full-solutions.md);
  [quadratic tail](harmonic-ramanujan-gram-has-a-logarithmic-operator-bound.md).

Put `M=sum_(m≤Q)a_m²`,
`A_N=sum_(n≤N)(sum_(m≤Q)a_m u_m(n))²/n`, and
`T=sum_(m,l≤Q)a_m a_l I(m,l)/sqrt(phi(m)phi(l))`.
For every `Q≥2`, every `N≥0`, and every real coefficient vector,

`|A_N−H_N M+T|`
`≤min{Q(Q−1)/(N+1), 6log Q+log4+5} M`.

## Proof

The first bound is already formalized. For `N≥Q²`, it is at most `M`.
For `N≤Q²`, positivity gives `0≤A_N≤A_(Q²)` and
`0≤H_N≤H_(Q²)≤1+2log Q`. The remainder at `Q²` is at most `M`.
Thus the remainder at `N` is at most `(2+2log Q)M`.
Its lower bound follows from
`|T|≤(4log Q+log4+4)M`, giving `−(6log Q+log4+5)M`.

This removes the artificial quadratic blowup at short quotient horizons.
The exact remainder still decays as `Q²/N` at long horizons. Its weighted
prime sum is a candidate input to a uniform finite-part operator identity;
that transfer and the complete Weil comparison remain separate.

## Lean

`SuccessorShellArithmetic.Conductor.HarmonicGramLogarithmicPlateau` proves
`abs_harmonicGram_torsion_remainder_le_log` and
`abs_harmonicGram_torsion_remainder_le_min`.
Direct production audit passed; both dependency closures contain only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import present.
