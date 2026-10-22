# RP-57: complete residual and logarithmic mixed work

Route RP; active hard-frontier trial. RP-56 made no frontier progress.
Negative coprime-work payment at each positive damping, signed high-LCM
control and both native history debts remain open.

Attack the complete signed short quadratic action through its exact
residual coefficients, retaining the physical product cutoff. At a
square cutoff x=N^2, write M_N(s)=sum_(n<=N) mu(n)n^(-s),
Z_N=zeta*M_N, and L_N=M_N'+log(N)*M_N. The logarithmic partner zeta*L_N
has +Lambda coefficients on 1<n<=N. The product with Z_N is not a
modulus square. The finite contour boundary and the pole-at-one source
must stay in the estimate.

First test: exploit the complete residual support gap together with the
Lambda short coefficients before taking any absolute values. Seek a
bound for the actual mixed long-range work, not another support or
reconstruction identity. No theorem or critical estimate claimed yet.

## Trial 1: residual-prime mixing

The actual residual E_N is the existing moebiusZetaDefect, with
E_N(n)=0 for n<=N. CCMPrimeDeficitResidualPrimeForce.lean already proves
that its logarithmic partner is E_N*Lambda, including its entry at
2(N+1). This is not new knowledge.

Let c=delta-E_N be the coefficient sequence of Z_N, and h the sequence
of zeta*L_N. Coefficient differentiation gives

    h(n)=log(N/n)*c(n)+(c*Lambda)(n).

For n<(N+1)^2, E_N*E_N vanishes and the complete mixed coefficient is

    (c*h)(n)=log(N)*delta(n)+(log(n)-2log(N))*E_N(n)
               +Lambda(n)-2*(E_N*Lambda)(n).

Thus the apparently new signed term is the complete E_N*Lambda
correlation, not a square of the short +Lambda coefficients. For
N<n<=2N the residual itself is mu(n), because every proper divisor is
at most N. Its short prime partner does not cancel this shell.

At T=2log N, inserting this mixed coefficient into RP-56's integrated
derivative formula cancels its quadratic time weights exactly. If G is
the exponential ramp and D=G-Dilation_Lambda(linear ramp), the result is
D-2*Dilation_(E_N)D. The short linear source is D-Dilation_(E_N)D;
their complete combination returns D. Hence this algebra gives the
existing reconstruction, with no residual gain or induction contraction.

The smaller physical arguments in Dilation_(E_N)D are at most N, but
the signed coefficients have no proved critical operator bound. Taking
absolute values removes the cancellation being sought. No new Lean
module was made for this restatement.

## Trial 2: integrate with the actual moving square cutoff

The physical lower integration endpoint for a,b is max(a,b)^2, not a*b.
Put m=max(a,b), n=min(a,b), r=log(m/n), and Y>=m^2. Direct paper
integration of the exponential and linear causal ramps gives, for
real s different from 0 and 1,

    K_G(a,b;Y) = (m^(2-2s)-Y^(1-s))/((s-1)*a*b)
                   -(m^(-2s)-Y^(-s))/s,
    K_L(a,b;Y) = m^(-2s)*(r/s+1/s^2)
                   -Y^(-s)*(log(Y/(a*b))/s+1/s^2).

For s>1 the full-ray exponential kernel, after factoring (a*b)^(-s),
is exp(-(s-1)*|r|)/(s-1)-exp(-s*|r|)/s. Its Fourier multiplier is
2/((s-1)^2+w^2)-2/(s^2+w^2), nonnegative. For s>0 the linear kernel
has multiplier 4*s/(s^2+w^2)^2, also nonnegative. These elementary
paper facts concern the separate ramps, not the complete signed divisor
source or critical admission.

In the finite exponential quadratic, the retained terminal terms are

    -Y^(1-s)/(s-1)*(sum_(a<=sqrt(Y)) mu(a)/a)^2
       +Y^(-s)/s*(sum_(a<=sqrt(Y)) mu(a))^2.

They are not negligible from the currently available moment estimates
in 0<s<1. The full source also retains its logarithmic mixed pairing.
For a source divisor k, the correct lower endpoint is
max(m^2,a*b*k); the two branches meet at k=m/n. Replacing that maximum
by either branch globally drops part of the physical source. No sign
or critical bound for the combined expression was proved.

## Trial 3: cutoff innovations and complete Neumann order

The retrieved residue martingale has a proved bounded innovation part,
while all possible unbounded growth remains in its predictable drift
(EulerDeletionResidueMartingale.lean:396). This is already known and
does not make the physical cutoff increments orthogonal. The actual
weighted cutoff successor retains its signed mixed source term and
positive square remainder (MobiusDivisorWeightedCutoffDiagonal.lean).

MobiusNeumannOrderBounds.lean supplies genuine unconditional arithmetic
order. With R=zeta-delta, mu*R^2=zeta-2delta+mu is coefficientwise
nonnegative, and multiplying by R preserves this sign. Complete odd
Neumann polynomials lie below mu and positive even polynomials above.
Applying this order to the nonnegative unit head preserves all signs,
but gives no uniform critical bound for the growing-degree polynomial.
The crude weighted absolute tail is a geometric series in zeta(s)-1;
its contraction condition is not known at the critical source exponent.
The finite support threshold 2^K still forces a growing degree.

The separate CCM finite-Neumann remainder results apply to specified
aperture Hilbert vectors, with an exponential source budget. They do
not identify those vectors with the native RP physical head or supply
its missing budget. No such identification or transfer is assumed.

The inverse-vector distinction is essential: the remainder theorem
controls B_a*u_a, where u_a is the finite inverse vector, not B_a*p_a
for the original source p_a. Its reconstruction is p_a=(c_a+B_a)u_a
plus a small error, with c_a growing exponentially. Replacing the
original native source by u_a without transporting the complete history
form would change the target. This observation directs the next trial
to the missing ordered-history transfer, with the shift term retained.

## Corpus audit and checkpoint

Documented deep searches, each with module RHTower and budget300:

| Mechanism | Session / exit | Query generation | Coverage / current | Files | Partial |
|---|---|---|---|---|---|
| short residual/logarithmic signed cancellation | 79722 / 0 | 1215359 | 1215360 / 1215361 | 64998 | false |
| native high-LCM cutoff increments | 65833 / 0 | 1215368 | 1215373 / 1215377 | 65000 | false |
| moving square-cutoff ramp kernel | 14822 / 0 | 1215373 | 1215383 / 1215384 | 65001 | false |
| finite Mobius Neumann remainder order | 45900 / 0 | 1215394 | 1215412 / 1215413 | 65003 | true |

All candidate_lemmas, source_arguments, proof_ideas and ingredient_sets
were inspected. Relevant hits were source-only; no compiler applicability
was inferred. Inventories complete, zero pending files, older coverage
snapshot, semantic coverage unavailable/unmeasured, background refresh
incomplete. Last query's filter_and_judge returned incomplete/malformed
JSON; available results used, no restart or absence inference. Other
queries reported no errors or unfinished stages. Suggested ingredient
sets involving quadratic characters, unrelated nonnegative cutoffs and
square-root floor bounds do not supply the required signed estimate.

No new frontier theorem or critical bound. Paper kernel identities were
used to test proposed estimates, not promoted to Lean progress. No Lean
edits or builds, no new umbrella entry, no subagents or numerical
experiment. The scoped whitespace check passed. This does not retire
Route RP or prove a no-go. RH remains unproved and unfalsified.

Next hard trial: construct the coefficient-faithful ordered-history
transfer to the finite inverse source using the current source-uniform
remainder result, retaining c_a, every original weight, both debts and
the physical terminal boundary. Test its actual scale before making a
formalization commitment. The prior Xi-norm lower-bound obstruction
still applies; no bounded Xi-norm intertwiner is asserted. Positive-
damping negative-work payment and signed high-LCM control remain open.
Goal active, no external blocker.
