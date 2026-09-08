# HB: original QNM frequency continuation

- **Stage:** in progress.
- **Goal:** unconditional RH proof/falsification; open.
- **Frontier map:** read-only.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and physical left-QNM pairing → independent Hawking-clock
extinction → RH.

The complete-source original joint causal response and its operator-domain
Laplace identity are constructed. Its full physical continuation and left
pairing remain open. Energy-space inversion on the opposite frequency
half-plane does not establish the required causal continuation.

## Closed radial continuation

[Original radial Green germs at every Xi QNM](../3-formalized/hb-original-qnm-frequency-germs.md)
contains the original Gauss-family frequency holomorphy, including terminating
numerators, dressed solutions, connection coefficient, and pointwise normalized
source-integrand germs at every Xi QNM.

[Original endpoint Green response at fundamental Xi QNMs](../3-formalized/hb-original-fundamental-qnm-endpoint-continuation.md)
contains eight audited leaves and 22 new public theorems. Both actual endpoint
moments of the native radial source family are continued, with equality to the
original Green response in its convergence chamber. The horizon moment uses
first Taylor subtraction with its exact source coefficient restored; its
remainder is analytic for `Re w > -2`, off the real axis. The actual outer
endpoint integral is entire before connection/source-pole normalization.

The assembled original radial response is meromorphic on that larger nonreal
strip and at both fundamental QNM frequencies for every Xi copy. Physical power
factors, source amplitudes and angular coefficients, the full connection
normalization, and the fixed smooth-onset correction are retained. This does not
assert pole survival, identify a physical left residue, or establish extinction.
Higher overtones require further endpoint Taylor orders.

[Original continued forced radial master](../3-formalized/hb-original-continued-radial-master.md)
contains eight audited leaves and 31 new public theorems. The continued native
response satisfies the original forced radial equation with actual first and
second spatial derivatives as a frequency germ at both fundamental QNMs for
every Xi copy. The proof extends the exact physical Wronskian normalization
across both nonreal half-planes, differentiates the restored horizon moment and
the true outer moment, and derives punctured-neighborhood nonvanishing of the
original connection coefficient. No nonresonance premise is supplied to the
QNM germ theorem.

## Closed complete residual admission

[Complete continued cusp-source admission](../3-formalized/hb-complete-continued-cusp-source-admission.md)
contains ten audited leaves and 40 public theorems. The actual continued radial
response is transported through the tortoise chart into the original principal
differences, full-square lift, and all three cutoff commutators. The explicit
field has actual radial derivatives and its actual metric angular Laplacian.
It agrees with the original explicit field in the source convergence chamber.

Each principal difference satisfies its original forced ODE. The potential
and native source obey `|p(t)| ≤ A exp(2t)` and
`|f(t)| ≤ B exp((Re w+2)t)`. Weighted energy of the actual channels `U'±wU`
gives `|U(t)| ≤ C exp(Re w*t)` from one interior value. This retains the
Green/lift cancellation. Multiplication by the literal horizon coordinate
recovers two powers of decay. Thus all three cutoff coefficients belong to the
original radial L² space for nonreal `w` with `-2 < Re w ≤ 0`.

Together with the already admitted native reduced coefficient and the actual
angular L² bounds, this proves admission of the complete cusp residual in the
joint L² space. `continuedOriginalSource_allXi_fundamental_admitted_germ`
proves simultaneous admission and the full original source equation on one
punctured frequency neighborhood of both fundamental QNMs for every Xi copy.
No admission, endpoint, continuation, or nonresonance premise is supplied to
that all-Xi capstone. Admission concerns the residual after subtracting the
explicit field, not the unrenormalized original angular source.

## Closed complete source meromorphy

[Complete source meromorphy in the original joint L² space](../3-formalized/hb-complete-cusp-source-l2-meromorphy.md)
contains eighteen audited leaves and 52 public theorems. The explicit
undivided source numerators and their actual interior jets are
frequency-analytic. Compactness gives uniform bounds for those jets and the
complete original forcing. A continuous explicit energy coefficient then
bounds the same original principal solution by `C exp(-|Re w|t)`: the two
signs of the free frequency are used only in the estimate of that solution.
The actual cutoff coordinate restores two powers of horizon decay.

One common L² majorant therefore controls each cleared cutoff family on a
frequency neighborhood inside `Im w≠0`, `|Re w|<2`. A new complex-parameter
Cauchy/dominated-convergence theorem proves differentiability in the actual L²
norm, including the analytic numerators at connection zeros. Restoring the
original denominators and applying the existing continuous separated-product
map proves meromorphy of the **complete** residual in the original joint L²
space. All three cutoff commutators and the native squared-source remainder
are retained.

`continuedCuspResidualL2_original_corridor` joins every point of that band to
the original principal Green chamber while preserving imaginary part and
ending at real part `7/4`. The exact continued source class equals the original
`cuspResidualVector` in that chamber. The strict Xi strip places both
fundamental QNMs in the band.
`continuedOriginalSource_allXi_fundamental_meromorphic_germ` combines their
actual joint L²-valued meromorphy with admission and the original field
equation on one punctured germ, without additional admission, continuation,
nonresonance, or RH premises.

## Current hard target

Continue the **original causal joint response** to this now-constructed
meromorphic source in its outgoing weighted domain, then identify the
physical advanced/adjoint left residue. Start from the existing causal
response and its proved operator-domain Laplace identity. Construct the
outgoing continuation with the original radial endpoint condition and full
modular angular operator retained; prove agreement with `jointWaveResponse`
on its original positive-frequency overlap. Source meromorphy is available;
meromorphy or continuation of the response inverse is not.

The source corridor reaches the original Green convergence chamber. This
batch does not add global L² holomorphy throughout the unbounded right
half-plane or extend the existing causal Bochner identity's stated domain.
The original pointwise source continuation and causal transform identities
remain available when identifying the same physical response.

The energy inverse selected independently on the opposite half-plane does
not identify the outgoing continuation. Its physical left-source projection
must retain the complete residual, every cutoff commutator, and the restored
horizon contribution. Neither pole survival nor vanishing of that projection
has been proved. Normalized scalar residues alone do not supply the physical
advanced/adjoint pairing.

Full joint angular/metric and spin-two/AIME reconstruction, independent
Hawking-clock extinction, and RH remain open. No numerical experiment is
indicated: the live obstacle is the actual outgoing operator domain and its
source-dependent continuation and physical pairing. Frontier map remains
read-only.

### Outgoing horizon-domain construction in progress

The original compact radial coordinate is `b=sech(t)^2`, with horizon `b=0`.
For a full angular-dependent field, remove the literal original phase by
`U=b^(w/2)V`. The full wave expression should become `-b^(w/2+1) P_w V`, where

```text
P_w V = 4b(1-b) V_bb + [4(w+1)-(4w+6)b] V_b
        + Delta_H V - w(w+1)V.
```

This keeps the entire original modular angular operator. A fixed C² extension
of V at the horizon admits the original Gauss branch. The opposite homogeneous
branch has stripped form `b^(-w) H_(-w)(b)` with `H_(-w)(0)=1`; for nonreal
`w` with `Re w>-2`, its second derivative prevents such an extension. The
planned exact two-branch classification is a boundary-domain selection, not
existence of the full forced joint inverse. Its proof and the displayed
full-field conjugation are in progress. The joint existence, modular cusp
condition, and agreement with the original causal transform still require
proof after this radial domain is fixed.
