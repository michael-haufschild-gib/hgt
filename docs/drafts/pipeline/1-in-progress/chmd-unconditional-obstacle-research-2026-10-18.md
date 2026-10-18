# CHMD: unconditional obstacle research

Status: in progress. Goal: one significant unconditional mathematical contribution overcoming a hard CHMD obstacle.

## Constraints

Use current Lean corpus and documented research search; no external search, numerical experiments, or external novelty audit. Frontier map is read-only. No new axioms or unproved analytic premises. Prove the exact claim on paper before formalizing. Build only needed modules, one foreground build at a time; final audit with `lake env lean`, targeted `--old` dependency builds, formal lint, scratch-only axiom checks, and umbrella wiring.

## Plan

1. Establish actual corpus frontier and select an exact, falsifiable conjecture.
2. Attack conjecture; record failures and positive survivors; repeat until a significant result survives.
3. Complete dependency-closed paper proof and formalize exact result.
4. Audit mathematical scope, Lean compilation, axioms, lint, imports, and cleanup.

## Initial evidence

Read CHMD frontier-map section and current module declarations. Existing results identify the primitive bound-state obstruction and give nodal decompositions, stationary positivity, and a prime-shift/chiral-drift disk inequality. No complete actual-prime sign or quantitative odd half-bound follows. First search examines nodal eigenstates, prime jumps, and ground potential.

## Conjecture loop

1. Strict prime-jump positivity alone supplies the needed uniform lower bound: rejected. Strictness does not imply a gap. The corpus's summable-spectrum almost-periodicity theorem exposes arbitrarily late simultaneous prime-phase recurrences. Formalizing that observation alone would be a bridge, not the requested advance.
2. Arbitrary signed perturbations can preserve the even and odd Euler–Poisson sources through cancellation: attack by separating the two directed theta waves. The existing `EulerPoissonChiralDriftAndPrimeShiftRigidity` treats ordered perturbations only. Selected positive survivor: exact recovery of every signed coefficient from integer samples of the forward theta wave, with a quantitative superexponential tail estimate.

## Exact selected statement and paper proof

Let `Theta` be the corpus's Riemann kernel and `E(y)=exp(9y/2-pi*exp(2y))`. Existing unconditional envelope bounds give `L E(y) <= Theta(y) <= U E(y)` for `y>0`, with fixed positive `L,U`. Index arithmetic sites by `q_n=n+2`; define `A_n(x)=Theta(x+log q_n)/E(log q_n)` and take arbitrary real data `a` in the concrete space of absolutely summable sequences. This permits arbitrary signed arithmetic weights `c_n=a_n/E(log q_n)`, including the actual von Mangoldt atoms.

For `x>=0`, put `d(x)=exp(2x)-1`. Exact envelope algebra gives

`E(x+log q_n)/E(log q_n)=exp(9x/2-pi*q_n^2*d(x))`.

Consequently `A_n(x)>0`, the wave `F_a(x)=sum a_n A_n(x)` converges absolutely, and for `n>=m`,

`A_n(x)/A_m(x) <= (U/L)*exp(-pi*(q_n^2-q_m^2)*d(x))`.

For the tail starting at `m`, subtract its leading coefficient after normalizing by `A_m`. Every remaining index has `q_n^2-q_m^2 >= 2m+5`. Absolute convergence and the triangle inequality give

`| (sum_{n>=m} a_n A_n(x))/A_m(x) - a_m | <= (U/L)*exp(-pi*(2m+5)*d(x))*sum_{n>m}|a_n|`.

The bound tends to zero as the integer sample `x=N` tends to infinity. This recovers `a_m` recursively after subtracting the finite known head. If two sampled waves agree, induction on `m` proves equality of every coefficient. No positivity of `a`, RH, zero exclusion, or unproved analytic estimate is used. The proof also shows that agreement on every sufficiently late integer sample suffices.

For actual weights, absolute admissibility follows from `summable_primeShift_right 0` and the lower envelope. Subtracting the odd source from the even source gives twice the forward wave. Thus any admissible signed replacement preserving both source identities has exactly the original arithmetic coefficients. The positive theorem is reconstruction and quantitative isolation; the no-go for signed repair is a consequence.

## Scope audit

This does not prove a complete Weil sign or RH. It addresses arithmetic identifiability and the possibility of changing signed prime weights while retaining both source equations. No external novelty claim is made. Corpus searches include the complete Lean inventory; one semantic query timed out, so exhaustive source-name/text checks supplement it. Formal verification remains pending.

## Sharpened cancellation classification (paper proof)

The corpus already contains `CHMDPrimeTailSelection.primeTail_selects_first` for the actual von Mangoldt tail. The new target therefore is not that special-case limit: it is unrestricted signed identification and its sharp order law. Existing `EulerPoissonChiralDriftAndPrimeShiftRigidity` excludes coefficientwise upward perturbations; it does not exclude signed cancellations.

Let `a,b` be distinct normalized summable coefficient sequences and let `m` be their first differing index. Subtract their two recovery formulas. Their finite heads agree exactly, so

`(wave b(N) - wave a(N))/atom m(N) → b_m-a_m`.

The denominator is strictly positive. A nonzero limit has its limiting sign eventually. Thus the eventual strict order of the two waves is exactly the lexicographic order of their coefficient sequences. Consequences: every nonzero signed perturbation has a fixed sign sufficiently far into the cusp; equality on any unbounded set of integer samples forces equality of all coefficients. This supplies a positive, sharp survivor to the obstruction against source-preserving arithmetic reweighting, rather than only a negative statement.

Admissibility has a direct mathematical meaning: `a_n=c_n E(log(n+2))` is in real `ell^1` iff the original arithmetic series at zero is absolutely summable. Indeed `L E(log(n+2)) <= Theta(log(n+2)) <= U E(log(n+2))`, with fixed positive `L,U`. There is no polynomial-growth restriction or coefficient sign restriction. Formalize the direct theorem for arbitrary real coefficients whose source converges absolutely at zero.

This addresses cancellation and arithmetic identification. It does not establish the primitive half-threshold energy bound. The possible Landau argument for eventual signs of *resolvent eigenvectors* remains a separate, unproved conjecture; no theorem currently claims it.

## Complete even/odd Euler–Poisson repair obstruction (paper proof)

For signed weights `w` on integers at least two, write `F_w(x)=sum w_n Theta(x+log n)` and `B_w(x)=sum w_n Theta(x-log n)`. The existing symmetric and chiral readouts are exactly `S_w=F_w+B_w`, `O_w=B_w-F_w`. Absolute convergence of the symmetric series implies convergence of each directed series because the two theta factors are positive. Hence `(S_w-O_w)/2=F_w`.

If both full Euler–Poisson readouts agree with their actual values on any unbounded integer sample set, their forward sources agree there. The signed source uniqueness theorem forces every `w_n` to equal `Lambda(n)/sqrt(n)`. No compensating signed perturbation can preserve both identities. The values at zero and one must be set to zero: both have logarithm zero in Lean, so without the arithmetic support convention these two slots would have a genuine artificial ambiguity. The formal statement includes this support convention and the actual symmetric-series convergence requirement.

Positive survivor: exact recovery and eventual order of every admissible signed coefficient perturbation, not merely impossibility of a preferred modification. This closes the signed-cancellation loophole in the existing coefficientwise-order rigidity result. It does not prove either parity identity alone rigid, and it does not remove the reflected-prime collar from the unchanged original energy.
