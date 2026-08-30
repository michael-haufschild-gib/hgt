# FZZ-P real-slice holomorphic Fermi-generator conjecture

- **ID:** FZZ-P-REAL-SLICE-HOLO-FERMI-GENERATOR
- **Stage:** 2-paper-proof-complete; Lean formalization in progress
- **Type:** ROUTE NO-GO + POSITIVE MEROMORPHIC SURVIVOR
- **Source:** read-only `rh-current-frontier-map.md`, FZZ-P `DYN`; successor to the source-global horizontal-profile no-go

## Goal and RH chain

Close or kill the surviving analytic source-deformation chain

`literal FZZ parity-Mellin analyticity → holomorphic continuation of exact real-source information dynamics → source-changing divisor transport → FZZ/Deninger/PW Ward equilibrium → RH`.

The previous no-go required the generator's horizontal component to depend only on `Re z`. The present conjecture removes that restriction completely: only agreement with the exact physical velocity on the real source slice remains.

## Frozen conjecture

Let

`S = {z : ℂ | 0 < Re z < 1}`

and

`V(σ) = fzzCigarParityReflectedFermiInformationVelocity(σ)`.

**Conjecture FZZ-P-D2 `[FROZEN]`.** There exists a function `G : ℂ → ℂ`, holomorphic on `S`, such that

`G(σ) = V(σ)`

for every real `0 < σ < 1`.

No condition is imposed on `G(x+iy)` away from the real slice. In particular, its horizontal component may depend arbitrarily on ordinate. The claim is the minimal source-global analyticity premise needed to continue the literal real Fermi information dynamics into the complex FZZ spectral parameter.

## Why this would close proof burden

The corpus already proves:

1. the literal parity-delay Mellin amplitude is holomorphic for `Re s > 0` and has exactly the Xi divisor in `S`;
2. the exact real Fermi velocity is strictly inward with unique equilibrium `σ=1/2`;
3. FZZ equilibrium, PW balance, and Deninger reflect-gauge Ward cancellation are the same copywise condition up to positive factors;
4. universal equilibrium is exactly RH.

FZZ-P-D2 would make the real information force the boundary-free analytic source generator acting before divisor selection. A source-derived zero-transport identity for this generator would therefore discharge the shared FZZ-P/PW-B Ward producer.

## Universal-shadow map

| Established corpus item | Shadow of FZZ-P-D2 |
|---|---|
| Holomorphic literal FZZ parity Mellin transform | Analytic carrier of `G` |
| Real reflected-Fermi Jeffreys gradient | Physical real-slice restriction of `G` |
| Deninger/PW positive transmutation | Arithmetic/scattering gauge of the same generator |
| D1 horizontal-profile holomorphic no-go | Off-axis ordinate dependence is essential |
| Same-source divisor-flow rigidity | The source itself must deform |

**Ontological reversal.** The real information force is treated as the physical slice of one complex source response, not as an externally attached scalar orientation.

**Risky consequence.** The exact real Fermi velocity must admit a pole-free holomorphic continuation through every FZZ/Xi mode in the open strip.

## Hostile attack and falsifiers

1. Identify the unique analytic continuation forced by the real interval using the logarithmic derivatives of the literal FZZ parity Mellin transform.
2. Determine its meromorphic order at a source-defined FZZ/Xi zero without assuming RH or simplicity.
3. Falsify D2 if any unavoidable pole occurs at an unconditional open-strip zero.
4. If falsified, extract the strongest positive survivor: the exact complexified information force as a divisor-sensing meromorphic connection, including its sharp principal order and multiplicity law.

Falsifiers:

- an open-strip zero where the forced continuation has negative meromorphic order;
- failure of the real-slice identity with the exact statistical force;
- an alternative holomorphic continuation not equal to the forced one, which would contradict identity-theorem uniqueness.

## Conjecturing loop

- **D1:** source-global holomorphic generator with horizontally stratified real part — `[FALSIFIED] [LEAN-PROVED]`.
- **D2:** holomorphic generator agreeing only on the physical real slice — `[FALSIFIED] [PAPER-PROVED]`; Lean formalization in progress.
- **If D2 fails:** replace holomorphic flow by the exact meromorphic divisor connection; test whether its residues create a source law or merely reconstruct the already-known divisor. If only reconstructive, kill that producer and force a singular/nonmeromorphic or divisor-indexed successor.

## Internal and external frontier

- `[CORPUS]` `fzzCigarParityMellin` is source-defined and holomorphic on `Re s>0`; its open-strip divisor is exactly Xi.
- `[CORPUS]` real Fermi mean and variance are the first two logarithmic responses of the positive Mellin normalizer.
- `[CORPUS]` `logDeriv_xi_pole_iff` and exact meromorphic-order tools classify logarithmic-derivative poles, but no theorem complexifies the exact reflected-Fermi force or applies it to FZZ-P-D2.
- `[LITERATURE]` standard Fermi-Dirac references identify the Mellin integral with Gamma/polylogarithmic or zeta expressions; FZZ literature establishes duality and correlator equivalence. The audited sources do not state this information-gradient generator, its Xi-divisor meromorphic order, or the FZZ/PW/RH no-go.

## Log

- 2026-08-30 — corpus and primary-literature audit completed; FZZ-P-D2 frozen before paper-proof work.

## Dependency-closed paper proof of the D2 no-go

Write `M(s)` for the literal source-defined `fzzCigarParityMellin`, `ξ(s)` for completed Xi, and

`U(s) = Γ(s) (1 - 2^(1-s)) / archFactor(s)`.

On the open critical strip, `Γ`, the dyadic eta factor, and `archFactor` are holomorphic and nonzero. The source closed form and `ξ = archFactor · ζ` therefore give the source-native unit factorization

`M(s) = U(s) ξ(s)`.

Let `a = U'/U`, `b = a'`, `L = ξ'/ξ`, and `Q = L'`. Both `a` and `b` are holomorphic on the strip. Away from the common source/Xi divisor,

`M'/M = L + a`,

`(M'/M)' = Q + b`.

The Xi functional equation gives `L(1-s) = -L(s)` and `Q(1-s) = Q(s)`. Hence the unique meromorphic continuation of the exact reflected Fermi information force is

`Φ(s) = 4L(s) + 2(a(s)-a(1-s)) + (2s-1)(2Q(s)+b(s)+b(1-s))`.

Its negative `Ψ = -Φ` is the continued velocity.

### Exact real-slice identification

For every real `σ>0`, corpus source equality gives `M(σ)=Z(σ)>0`, where `Z` is the Fermi Mellin normalizer. Restricting the holomorphic derivative of `M` to the real axis and differentiating the equality gives

`(M'/M)(σ) = Z'(σ)/Z(σ) = fermiLogMean(σ)`.

The first identity is complex-to-real derivative transfer; the second is the proved first response of `log Z`. Differentiating once more on the positive real axis gives

`(M'/M)'(σ) = fermiLogVariance(σ)`.

Substitution at `σ` and `1-σ` proves

`Φ(σ) = fzzCigarParityReflectedFermiInformationForce(σ)`

and therefore `Ψ(σ)=V(σ)` for every `0<σ<1`.

### Exact divisor pole law and cancellation audit

Let `ρ` be any Xi zero in the open strip, of analytic multiplicity `m≥1`. The corpus gives exact orders

`ord_ρ(L)=-1`, `ord_ρ(Q)=-2`.

Moreover `2ρ-1≠0`, since `ξ(1/2)≠0`. Therefore the term `2(2s-1)Q(s)` has exact order `-2`. Every other term of `Φ` has order at least `-1`: `4L` has order exactly `-1`, while the completion-unit terms are holomorphic. Unequal-order addition forbids cancellation, so

`ord_ρ(Φ)=ord_ρ(Ψ)=-2`.

The local principal coefficients are

`Φ(s) = -2m(2ρ-1)/(s-ρ)^2 + O((s-ρ)^(-1))`,

`Ψ(s) =  2m(2ρ-1)/(s-ρ)^2 + O((s-ρ)^(-1))`.

Thus the positive survivor records both full multiplicity and centered displacement of every literal FZZ/Xi divisor point.

### Holomorphic-extension contradiction without punctured-strip topology

Assume D2 and let `G` be holomorphic on the strip with `G(σ)=V(σ)` on the physical real interval. Clear the only divisor denominator by `ξ²`. The products

`ξ²L = ξξ'`,

`ξ²Q = ξξ''-(ξ')²`

hold off the divisor, so `ξ²Ψ` has a holomorphic pole-cleared numerator on the entire strip. Consequently the pole-cleared difference

`H = ξ²G - ξ²Ψ`

has a holomorphic representative throughout the strip. It vanishes on `0<σ<1`; the identity theorem on the convex strip forces `H≡0`. In a deleted neighbourhood of any Xi zero, `ξ≠0`, hence `G=Ψ`. This would make the exact double pole of `Ψ` removable, contradicting `ord_ρ(Ψ)=-2`.

An unconditional open-strip Xi zero exists, so D2 is false without RH, simplicity, or any hypothesis.

## Route consequence

`[FZZ-P-D2 ROUTE KILL]`: exact real reflected-Fermi velocity cannot be promoted to any pole-free holomorphic generator on the full critical strip, even with unrestricted ordinate dependence. Therefore it cannot be the pre-divisor source-changing Ward flow required by the stated FZZ-P/Deninger/PW chain.

`[POSITIVE SURVIVOR]`: the unique continuation is instead a source-defined meromorphic connection with an exact double pole at every FZZ/Xi mode and leading coefficient `2m(2ρ-1)` for velocity. It is divisor-reconstructive: it reads the existing divisor and cannot act as a holomorphic producer before divisor selection. Any surviving producer must be singular/meromorphic, divisor-indexed, or abandon this exact real Fermi generator.

## Hostile-audit closure

- Reflection cancellation fails: Xi functional equation doubles, rather than cancels, curvature.
- Multiple zeros remain detected: coefficient is proportional to full `m`, with no simplicity premise.
- Center cancellation is impossible: `ξ(1/2)≠0` excludes `2ρ-1=0` at a divisor point.
- No connectedness theorem for strip minus zeros is used: `ξ²` pole-clearing moves uniqueness to the full convex strip.
- No numerical evidence or computation enters proof.

## Novelty audit

- Internal research found source Mellin continuation, Fermi response derivatives, Xi log-derivative pole laws, and functional-equation reflection separately, but no exact complexification of this reflected-Fermi force, no double-pole multiplicity law for it, and no D2 no-go.
- DLMF §25.12 and standard Fermi-Dirac literature give Gamma/polylogarithm/zeta representations, not this reflected information connection or pole law.
- FZZ duality and boundary-FZZ papers establish dual descriptions/correlators, not this source-information-gradient continuation or RH-route obstruction.
- Targeted searches through 2026-08-30 found no published statement of D2, its no-go, or coefficient `2m(2ρ-1)`.

- 2026-08-30 — FZZ-P-D2 falsified on paper; exact double-pole divisor connection extracted as positive survivor; all cancellation and topology falsifiers closed.
