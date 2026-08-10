# First-entrance gate renewal/capacity frontier (2026-08-10)

Created paper-proved cards:
- `docs/drafts/pipeline/2-fully-proven/first-entrance-gate-renewal-prefix-law.md`
- `docs/drafts/pipeline/2-fully-proven/first-entrance-gate-capacity-discrepancy-law.md`

Updated live conjecture:
- `docs/drafts/pipeline/1-in-progress/synthesis-divergence-brown-law.md`

Exact proved results:
1. For any discounted Markov chain target A, occupation measure factors as entrance measure times return resolvent: `mu = nu (I-K)^-1`. For singleton y, `G_a(x,y)=F_a(x,y)/(1-R_a(y))`.
2. Right-extension gate-word first-hit language is prefix-free and `F_a=sum_first-hit (a/M)^|w|`, with Kraft mass <=1.
3. If C is robust word complexity, `(a/M)^C <= F_a <= a^C`; hence fixed-a first-hit surprisal is bilipschitz-equivalent to C and its zero-fugacity exponent equals C.
4. First-hit geometric-prior I-projection equals `-log((1-a)F_a)`; under the conditioned first-hit prior, `-log F=log(M/a) E|W|-H(W)`.
5. Complete union: `Pr(R and C<=s) <= (M/a)^s E[1_R F_a]`.
6. Exact recurrence collapse: if target tube contains seed, `F_a=1`.
7. Hostile correction: normalized raw Green and first-hit mass obey `(1-a)F_a <= Gbar_a <= F_a`; surprisals differ by at most `-log(1-a)`. Raw Green is not exact preparation, but is fixed-fugacity rate-equivalent. First entrance improves interpretation/capacity coordinate, not Brown exponent.
8. For finite reversible inverse-gate walk, first-hit h_A solves `h=1 on A, h=aPh off A`, uniquely minimizes `<h,(I-aP)h>`, and its energy is discounted capacity.
9. Stationary mean identity: `E_pi h_A=cap_a(A)/(1-a)`; capacity window `(1-a)pi(A)<=cap<=min(pi(A),1-a)`.
10. For target law nu, exact directional decomposition `E_nu h_A=cap/(1-a)+delta_A(nu)`.
11. Global negative-energy norm is wrong: `||nu-pi||_-1,a^2 >= chi^2(nu||pi)/(1+a)`, and support beta forces >=`(beta^-1-1)/(1+a)`. Non-Haar laws can have delta=0 exactly.
12. Inverse-word identity converts synthesis first entrance to backward inverse-gate equilibrium potential without target translation symmetry.

Live Brown core:
At O(n) geometric skeleton times, after one common return/carrier cut, prove the signed directional equilibrium-potential expectation (capacity baseline + delta) is <= `exp(-kappa r_n)(a/M)^s_j`, retaining fibre sheets and occupied endpoint image. Do not target global Haar/design/resolvent norm, minimum spectral gap, raw pseudodeterminant, source entropy, or smooth threshold contact jets.

Honest labels:
- All renewal, Kraft, KL, Dirichlet-capacity engines are classical; external priority for circuit/static composition is unverified.
- No static-local Brown growth or black-hole theorem proved.
- Lean deferred due active corpus refactor; no Lean process started.
