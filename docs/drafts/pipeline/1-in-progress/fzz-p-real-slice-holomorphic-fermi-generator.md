# FZZ-P real-slice holomorphic Fermi-generator conjecture

- **ID:** FZZ-P-REAL-SLICE-HOLO-FERMI-GENERATOR
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
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
- **D2:** holomorphic generator agreeing only on the physical real slice — `[FROZEN]`, current hostile target.
- **If D2 fails:** replace holomorphic flow by the exact meromorphic divisor connection; test whether its residues create a source law or merely reconstruct the already-known divisor. If only reconstructive, kill that producer and force a singular/nonmeromorphic or divisor-indexed successor.

## Internal and external frontier

- `[CORPUS]` `fzzCigarParityMellin` is source-defined and holomorphic on `Re s>0`; its open-strip divisor is exactly Xi.
- `[CORPUS]` real Fermi mean and variance are the first two logarithmic responses of the positive Mellin normalizer.
- `[CORPUS]` `logDeriv_xi_pole_iff` and exact meromorphic-order tools classify logarithmic-derivative poles, but no theorem complexifies the exact reflected-Fermi force or applies it to FZZ-P-D2.
- `[LITERATURE]` standard Fermi-Dirac references identify the Mellin integral with Gamma/polylogarithmic or zeta expressions; FZZ literature establishes duality and correlator equivalence. The audited sources do not state this information-gradient generator, its Xi-divisor meromorphic order, or the FZZ/PW/RH no-go.

## Log

- 2026-08-30 — corpus and primary-literature audit completed; FZZ-P-D2 frozen before paper-proof work.
