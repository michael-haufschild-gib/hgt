# The sharp Schur row bound on the atomic lattice

- **ID:** atomic-lattice-sharp-schur-row-bound
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0411 §2.1, A28.

## Target and reduction

For the von Mangoldt operator on atoms indexed by `1≤m≤N`, prove
`|⟨Λg,g⟩|≤(log N)/2 · Σ_{m≤N}g(m)²/m`.

Retaining the cutoff `d≤N/m` in the existing AM–GM proof gives the row weight

`r_N(m)=Σ_{d≤N/m}Λ(d)/d + Σ_{d|m}Λ(d)
       =Σ_{d≤N/m}Λ(d)/d + log m`.

Thus the exact inequality `Σ_{d≤x}Λ(d)/d≤log x` for all `x≥1` would give
`r_N(m)≤log N` and finish the target. The existing theorem
`abs_integral_windowRep_vonMangoldt_atomic_le` replaces every cutoff by `N`
and yields the weaker bound `(Σ_{d≤N}Λ(d)/d+log N)/2`.

## Gap

The exact finite Mangoldt inequality has not been formalized here. Located corpus
bounds retain an additive constant; the asymptotic difference `−γ` alone does
not settle every finite cutoff.

Balazard's appendix to [Ramaré–Zuniga-Alterman, Theorem 1.3](https://arxiv.org/html/2312.05138)
proves it using `ψ(x)≤x log 3`, integrated Stirling, and the exact negative-part
integral `(1−γ)/2` of `α(u)=⌊u⌋(⌊u⌋+1)/u²−1`. These yield

`M(x)−log x ≤ (3−γ)log(3)/2−3/2 + log(2π)/x + log(x)/(4x²)`.

This is negative for `x≥12`; the eight prime-power cutoffs below 12 finish the proof.
Formalization needs these analytic inputs, or a replacement proof. No theorem is
claimed with a missing input as a premise.

[Hanson's Chebyshev proof](https://doi.org/10.4153/CMB-1972-007-7) uses a factorial
quotient from the Sylvester sequence, then a table check below 1300. Neither that
table nor the quoted bound is a formalized input here.
