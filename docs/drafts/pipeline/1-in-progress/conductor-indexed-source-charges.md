# Conductor-indexed arithmetic source charges

- **ID:** critical-rigidity-conductor-indexed-charges
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Question:** Can conductor escape create an independent receiving charge in every fixed conductor?

## Exact arithmetic input

The corpus proves the divisor-jet expansion and the coprime product rule for Mangoldt-weighted dilation differences. For normalized modes, the predicted receiving coefficient is

`(G_Q a)_r = −tameDifferent(r)a_r + C_r(a)`,

`C_r(a)=Σ_(m≤Q,r|m) Λ(m/r)sqrt(φ(r)/φ(m)) a_m`.

Summing this triangular expansion and proving its complete-period Plancherel law would retain all coherent divisor fibres explicitly.

## Fixed receiving conductor

Restrict input to `m=rp`, with primes `p>r`. Coprimality gives `φ(rp)=φ(r)(p−1)` and `λ_(rp)=λ_r+λ_p`, where `λ_m=log m+tameDifferent(m)`. The squared relative norm of the receiving row is therefore

`Σ_p (log p)²/[(p−1)(λ_r+λ_p)]`.

Since `λ_p≥log 2`, each summand is at least

`[1/(1+λ_r/log 2)] log p/p`.

Prime Mertens growth predicts logarithmic amplification for every fixed `r`. For `r≥2`, both input and output have zero constant coefficient: `rp` has two distinct prime factors, so its Mangoldt mean vanishes. This would strengthen the parity-fibre candidate and exclude global output centering as a uniform remedy.

## Stronger concentration target

For coprime conductors, the literal generator should obey `G(e_r F)=e_r G(F)+(G e_r)F`. Coherent prime packets supported above every prime dividing `r` may then have vanishing adjunction energy while their output approaches `e_r` in complete-period square mean. Finite sums would expose a full family of independent receiving charges.

The product rule and explicit charge construction must be formalized before asserting this limit or any graph-closure classification. No statement about negative complete Weil states follows without the missing joint Gamma–pole–shell analysis.

## Positive survivor

A source-preserving concentration theory must identify which conductor charges survive and which cancel in the complete signed form. The finite triangular coefficient law and its exact norm decomposition are the first required tools; declaring charges as unconstrained interface fields would not establish the arithmetic limit.

## Existing harmonic control

`SuccessorShellArithmetic.HarmonicGramUniformRemainder.abs_harmonicGram_quadratic_torsion_remainder` already bounds the full packet's harmonic finite-part error by `Q(Q−1)M/(N+1)`. This quadratic remainder is existing work, not a new target. `HarmonicGramFinitePart.tendsto_divisorPacket_mul_harmonic_primeLocal` identifies the mixed finite part with the same prime-power divisor couplings predicted for receiving charges.

The prospective identity is therefore `harmonic finite part = γ⟨a,b⟩−L(a,b)−⟨Ga,b⟩−⟨a,Gb⟩`. A new contribution must use the literal-generator identification to derive a source-concentration classification or a joint complete-form estimate; merely restating the existing finite part would not suffice.
