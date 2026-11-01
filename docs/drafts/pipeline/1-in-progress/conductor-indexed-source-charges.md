# Conductor-indexed arithmetic source charges

- **ID:** critical-rigidity-conductor-indexed-charges
- **Stage:** 1-in-progress
- **Disposition:** Paused with the parent programme. No further research authorized.
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

The leading coefficient should also be one. The displayed summand is exactly

`(log p/p)·λ_p/(λ_r+λ_p)`.

For any fixed tolerance, remove a fixed initial prime segment so that the last factor is arbitrarily close to one, then use Mertens divergence. The universal upper sector bound `B_Q+8` supplies the opposite asymptotic inequality. Thus each fixed receiving row is expected to retain the full leading logarithmic cost. Removing any fixed initial set of output conductors would leave the same leading scale in the first retained row.

## Stronger concentration target

For coprime conductors, the literal generator should obey `G(e_r F)=e_r G(F)+(G e_r)F`. Coherent prime packets supported above every prime dividing `r` may then have vanishing adjunction energy while their output approaches `e_r` in complete-period square mean. Finite sums would expose a full family of independent receiving charges.

A precise stronger target is: every fixed finite conductor packet `F` is approximable by generator outputs `G U` with `L(U)` arbitrarily small. Choose a coherent prime packet `H` supported above all conductors of `F`, and put `U=FH`. Unique coprime conductor factorization predicts

`L(FH)=L(F)M(H)+M(F)L(H)` and `G(FH)=F G(H)+(GF)H`.

Complete-period product orthogonality then transfers `L(H)→0`, `G(H)→1` to `L(U)→0`, `G(U)→F`. Proving these literal product identities and the prime-tail charge construction would determine the entire finite receiving-charge space, rather than only parity. The positive structure to retain is the full arithmetic gradient with its exact square energy; summing all prime currents into one generator can lose this continuity.

The product rule and explicit charge construction must be formalized before asserting this limit or any graph-closure classification. No statement about negative complete Weil states follows without the missing joint Gamma–pole–shell analysis.

For the exact topology, use the full coefficient norm `Σ(1+λ_m)a_m²`, so conductor one is retained rather than quotiented ambiguously. Prime escape has coefficient mass at most `L/(2log 2)`. If every finite receiving charge is constructed as above, the closure of the generator graph in this input Hilbert space times coefficient `ℓ²` is the full product: first add vanishing-input charge corrections to each finite packet, then use density of finite packets. This predicts a completely multivalued graph limit, not merely failure of a uniform norm bound.

There is a second route to that classification. For fixed `r` and primes `p>r`, the adjoint's `rp` coordinate contains `log p/sqrt(p−1)·b_r`. Its squared energy-dual mass diverges like `Σ log p/p` whenever `b_r≠0`. The remaining coordinates involve only finitely many `b_(dp)` with `d|r`, and should have finite dual mass for `b∈ℓ²`. Establishing these exact adjoint formulas would force its domain to be zero. This is a candidate proof, not an established operator theorem.

The positive replacement is concrete: retain the complete family of dilation differences in the Mangoldt-weighted square space. Its norm is exactly `L`, already proved in the corpus. Thus the gradient has an energy-continuous extension even if its aggregate receiving generator has a full vertical graph. The missing complete-form question is which charge combinations cancel before this aggregation.

If both constant and parity charges are independently realizable at vanishing energy, they could cancel `G e_2=log 2·(1−e_2)` while leaving input near parity. Since parity has zero successor approximation error when the approximating packet is free, this would distinguish the aggregate generator from the individual dilation-square energy in joint rigidity. It would not contradict rigidity for the literal successor difference or the proved joint successor–dyadic square gap.

## Positive survivor

A source-preserving concentration theory must identify which conductor charges survive and which cancel in the complete signed form. The finite triangular coefficient law and its exact norm decomposition are the first required tools; declaring charges as unconstrained interface fields would not establish the arithmetic limit.

## Existing harmonic control

`SuccessorShellArithmetic.HarmonicGramUniformRemainder.abs_harmonicGram_quadratic_torsion_remainder` already bounds the full packet's harmonic finite-part error by `Q(Q−1)M/(N+1)`. This quadratic remainder is existing work, not a new target. `HarmonicGramFinitePart.tendsto_divisorPacket_mul_harmonic_primeLocal` identifies the mixed finite part with the same prime-power divisor couplings predicted for receiving charges.

The prospective identity is therefore `harmonic finite part = γ⟨a,b⟩−L(a,b)−⟨Ga,b⟩−⟨a,Gb⟩`. A new contribution must use the literal-generator identification to derive a source-concentration classification or a joint complete-form estimate; merely restating the existing finite part would not suffice.

## Formal interfaces

`CoprimeModeTransport.lean` now drafts the all-row normalized source sum, its exact coprime derivation law, and additive adjunction weights. It uses the already-proved Mangoldt product rule and the packet source sum; verification is pending. Prime-band normalization, coefficient-product Plancherel, and the receiving-charge approximation remain to be implemented.
