# CCM all-frequency Fock Gram-positivity no-go

- **ID:** ccm-all-frequency-fock-gram-positivity-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** One exact all-frequency coherent-Fock kernel is PSD on every mixed-frequency finite packet while each literal prime-power projective reporter takes both signs; mixed-frequency Gram positivity alone cannot produce the source Ward sign.

## Goal

Kill

`mixed-frequency PSD Gram constraints -> nonnegative exact source reporter -> fixed Ward orientation -> shared HB/FZZ-P/PW-B/RBH endpoint -> RH`.

## Gates

- [x] 0 → 1 in-progress: exact source-pure statement, attack, route passport
- [x] 1 → 2 fully-proven: complete paper proof, `[PAPER-PROVED]`
- [x] 2 → 3 formalized: exact Lean theorem and audit
- [ ] 3 → 4 publication-ready

## Frontier and hostile verdict

- `[CORPUS]` Fixed-frequency projective Fock kernels are PSD and their half-log probe ratios equal the intact oriented source symbol.
- `[CORPUS]` Every prime-power ratio is above one at `xi=1/log n` and below one at `xi=1/(2 log n)`, but current theorem uses two fixed-frequency kernels.
- `[LITERATURE]` Positive-kernel/coherent-state theory makes the joint feature-map kernel routine; PSD itself is `[REDISCOVERED]`.
- Exact all-frequency arithmetic sign-straddle/no-go was absent from corpus and audited RH literature.
- Verdict: `SURVIVES PRELIMINARY ATTACK` only as a route-class obstruction, not as a new generic kernel theorem.

## Proposed exact claim

Index one kernel by arithmetic atoms and positive/negative probes carrying their own real frequencies. Map each index to the existing three-dimensional actual matched feature and use the exponential inner-product kernel. Prove:

1. the resulting single kernel is PSD on arbitrary mixed-frequency finite packets;
2. its same-frequency projective ratio is `exp(2 Re Z_n(xi))`;
3. for every literal prime power `n`, the same kernel has ratio `> 1` at `1/log n` and `< 1` at `1/(2 log n)`;
4. therefore no implication from all-frequency Gram positivity alone to reporter nonnegativity or ratio `>= 1` exists.

## Positive survivor sought

Any viable nonlocal source extraction must use more than positivity of all mixed-frequency Gram minors: an oriented/signed cross-frequency law, a connection preserving extra source structure, or independent source/Gamma Ward naturality.

## Proof `[PAPER-PROVED]`

Let `V=R^3` be the existing actual matched projective feature space. Index atoms and their positive/negative probes by pairs `(n,xi)`. Send them respectively to the existing vectors

`A(n,xi)`, `P(n,xi)`, `-P(n,xi)`

and define `K(a,b)=exp(<Phi(a),Phi(b)>)`, viewed in `C`. Every finite mixed-frequency restriction is an exponential inner-product Gram matrix, hence PSD by its symmetric Fock expansion. Therefore `K` is one PSD kernel on all arithmetic-frequency labels.

Restricting labels to one fixed `xi` gives exactly the previously constructed fixed-frequency kernel: feature maps and exponential entries agree definitionally. In particular, for the same label `(n,xi)`,

`K(A(n,xi),P(n,xi))=exp(Re Z_n(xi))`,

`K(A(n,xi),-P(n,xi))=exp(-Re Z_n(xi))`.

Thus their projective ratio is `R(n,xi)=exp(2 Re Z_n(xi))`, and `(1/2)log R=Re Z_n(xi)`.

For a literal prime power `n`, `n>1`, its critical Mellin weight is positive, and `log n>0`. At `xi+=1/log n`, the outer phase in the exact source formula is `2pi`, so `Re Z_n(xi+)=C_n(xi+)>0`. At `xi-=1/(2 log n)`, it is `pi`, so `Re Z_n(xi-)=-C_n(xi-)<0`; strict positivity of `C_n` follows from positive atom weight and nonzero frequency. Consequently the same kernel `K` has `R(n,xi+)>1` and `R(n,xi-)<1` for every prime power.

Since `K` itself already satisfies every finite mixed-frequency Gram-positivity constraint, neither nonnegativity of its exact reporter nor `R>=1` follows from that information. The fixed-frequency restriction identity is the positive survivor: all source phases do assemble faithfully into one carrier, but orientation is extra structure not encoded by PSD order. ∎

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedAllFrequencyFockGramPositivityNoGo`
- Positive survivor: `ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockPrimePowerReporterSignStraddle`
- Route kills: `ccmActualHeadMatchedPhaseAllFrequencyFockGramReporterPositivityRouteKilled`, `ccmActualHeadMatchedPhaseAllFrequencyFockGramRatioLowerBoundRouteKilled`
- Direct check and target-only build: pass.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Wired into `GaloisForLFunctions.RHTower`.
- Global lint sees this module through its umbrella; remaining failures are unrelated unwired concurrent modules.
