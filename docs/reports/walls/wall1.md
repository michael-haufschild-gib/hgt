## What is wall 1?
Wall 1 is the square-root barrier in prime counting. Every producer route eventually needs an unconditional statement of the form "a prime or Möbius sum up to x has error of size x^{1/2+ε}". That statement is RH itself. Equivalent forms: ψ(x) − x = O(x^{1/2+ε}), or M(x) = Σ_{n≤x} μ(n) = O(x^{1/2+ε}), or Σ_{n≤x} μ(n)/n = O(x^{−1/2+ε}). Each one implies RH by the Mellin integral, and RH implies each one by the explicit formula.

Everything unconditional stops far short of this. Sieves, the de la Vallée Poussin and Vinogradov–Korobov zero-free regions, and exponential-sum methods give savings of the shape exp(−c (log x)^{3/5}), which is weaker than any power saving. A power saving x^{θ} for any θ < 1 is already a zero-free half-plane Re s > θ, and no such half-plane is known. So a route hits Wall 1 the moment its remaining obligation is a prime sum with a power saving. One-sided producers, like Robin's or Nicolas's inequalities or sieve-weight positivity, need the full exponent 1/2 before they trigger at all, which is why the catalogue lists them under this wall.

In FZZ-P the wall appears in three concrete places.

- The raw Möbius approximant is exact on (1/(N+1), 1] and its error energy is (N+1)·H_N²/6 with H_N = Σ_{d≤N} μ(d)/d. Making this vanish is square-root cancellation of H_N.
- The log-Möbius head error is (ψ(x) − 2ψ(x/2))/log N, and its energy in dx/x² over [1, N] tends to zero only if ψ(x) − x has mean-square size x^{1/2}. By Landau's argument, energy O(X^{2κ}) already gives a zero-free half-plane Re s > 1/2 + κ.
- The superposition Ψ_ρ = −∫₁^∞ b^{ρ−1} φ_b db converges in L² exactly when Re ρ < 1/2, because ‖φ_b‖² = log 2/b. The Fubini swap fails on the line Re s = 1/2, and that failure is the wall in Mellin form.

The 2026-10-15 refxponent is forced.Under Poisson summation in t = e^y, a test function vanishiat the nodes log nctral content atfrequency about e^y with amplitude e^{−y/2}. That amplitudesquare-root size.  at √-cancellation, so every blind family loses a logarithmic margin against thpole weight e^{y/2on method caps atthe Nyquist density for the same reason.                   
The practical rule in the walls catalogue: before trying a producer, name thee exponent itneeds. If the exponent is 1/2, the route is a restatement of RH, not a step tow

## How to get the unconditional O(log x) bound?

The short answer first: an unconditional O(log x) bound for the band is not a step toward RH, it is RH, in both directions. The field can be expanded to make that equivalence exact and to say precisely what any mechanism must look like, but no expansion of receivers and producers can output the bound by itself. Here is why, and what the honest expansions are.

Why the band bound is RH itself

- Band ⟹ RH. If ∫_0^L Ẽ² ≤ C·L for all L, the Laplace transform of Ẽ converges absolutely on Re z > 0 (Cauchy–Schwarz against the dyadic blocks). The corpus identity criticalNormalizedChebyshevErrorLaplace_eq_logDeriv says this transform equals −(ζ'/ζ(z+½) + 1)/(z+½) on Re z > ½, so that function continues holomorphically to Re z > 0 and ζ has no zero with real part above one half. The corpus has this receiver pattern for the Weil lag function (riemannHypothesis_of_lagSquare_laplace) but not yet for Ẽ.
- RH ⟹ band. This is Cramér's mean square via the explicit formula and the local zero count. It is also not in Lean; the corpus only has von Koch's pointwise bound, which gives O(L⁵), not O(L).
- Beurling test. Every statement in modules 1–17, and every producer bound of the parallel programme, uses only Λ ≥ 0, Chebyshev and Mertens bounds. Those hold for Beurling systems, and RHTower/BeurlingRegularIntegersOffLineZeros builds such systems with zeros at any β in (½,1), for which the same band energy is at least of order x^{2β−1}. So any derivation of the band bound must contain a step that is false for Beurling systems. That step is the whole difficulty.

Where the wall sits in each coordinate of the field

- Frequency. The band is a Dirichlet polynomial of length x integrated over |t| ≤ √x. Montgomery–Vaughan's off-diagonal term Σ Λ(n)² is sharp for arbitrary coefficients and starts to dominate exactly at the band edge. In large-sieve language the single-character band carries a deficit factor of x/√x, and the hybrid large sieve (FiniteAdditiveHybridLargeSieve in the corpus) becomes sharp only once about x^{1/4} characters are averaged. In mollifier language, Λ = μ⋆log makes ν̂_N a mollified truncated −ζ′ with mollifier length x on height √x, that is θ = 2, against the Nyquist cap θ = 1 recorded in the bandwidth-one wall and the θ < 4/7 regime of the corpus's Levinson lane.
- Low frequency alone already carries it. Module 17 gives ν̂_N(0) = ½∫Ẽ + Ẽ(L) − 1 + O(e^{−L/2}). There is no unconditional partial band: every off-line zero leaks into every frequency through 1/(s−ρ).
- Scale. The chain inputs are the dyadic prime-count errors divided by √X. Their mean square being O(K) is square-root cancellation on average over dyadic blocks. The best unconditional savings are exp(−c√k) per block, so Σ_k r_k² diverges exponentially.
- Position. The module-16 quadratic form is diagonal in ψ(n), and expanding it returns Σ_{a,b≤x} Λ(a)Λ(b)/max(a,b); the required cancellation of its main terms to O(log x) is the same statement again.

Expansions that are honest, and what each buys

1. Make the equivalence a theorem of the field: both directions in Lean (two modules). This ends any hope that the band is weaker than RH and gives the field its sharpest receiver.
2. An x-free form. With R_∞ = Ẽ + (1−t)e^{−t/2} on all of [0,∞), set M(σ) = ∫_0^∞ e^{−(2σ−1)t} R_∞². Plancherel gives M(σ) = (1/2π)∫ |−ζ'/ζ − 1/(s−1) − 1/s|²/|s|² dt on Re s = σ > 1, and a Tauberian pair gives Wall 1 ⟺ M(σ) ≤ C/(2σ−1) on (½,1]. That is a Hardy-space growth law for one meromorphic function and could feed the corpus's de Branges lane. It is still a restatement of the zero set.
3. Möbius factorization of the atomic transform and the θ = 2 law, tying Wall 1 exactly to the mollifier terminus already audited in the corpus.
4. The family-averaged band: unconditional and sharp for Q ≥ x^{1/4} characters, by the hybrid large sieve. This isolates Wall 1 as "the trivial character is not exceptional" with an explicit exponent. Upgrading from the family to one member is Wall 7.
5. Sieve splits (Vaughan and Heath-Brown identities are in the corpus; the parallel agents' Barban–Vehov and ker P machinery is fresh). Type I pieces become mollified ζ moments, type II pieces become bilinear forms with both lengths between x^{2/7} and x^{5/7}. The bilinear piece on |t| ≤ √x is the wall again, and parity caps sieve upper bounds at a constant factor, never at O(1) precision.

What a delivering mechanism must satisfy

- It must fail for Beurling systems, so it must use the additive structure of ℕ.
- It must survive the degenerate point: one character, modulus one, shift zero.
- It must carry information beyond polynomial length equal to height at square-root precision.
- It must distinguish log 4 from log 6 (Wall 11).

Additive tools (large sieve, dispersion, Poisson) meet the first and third only after averaging over a family, and multiplicative tools are Beurling-invariant. No known tool meets all four at once.

