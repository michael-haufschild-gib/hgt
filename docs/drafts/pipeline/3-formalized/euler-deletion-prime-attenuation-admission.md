# Prime attenuation and literal deletion admission

**Stage:** 3-formalized. **Type:** source-domain theorem and exact repair.
**RH implication:** none. **Novelty:** not certified; elementary Euler-factor parents.

## Research question

The paired-prime finite countermodels leave open whether similar changes preserve the
actual infinite deletion construction. A finite Euler-factor quotient preserves zeta zeros
where it is regular and nonzero. This does not establish convergence of the modified
literal deletion sums. Test the distinction on one globally positive, contractive,
completely multiplicative coefficient family.

For prime `p`, `0<=c<=1`, set `b(n)=c^(v_p(n))` for positive `n`, and `b(0)=0`.
Write `S(N)=sum_(1<=n<=N)b(n)`. Exact divisibility splitting gives

`S(N)=N-floor(N/p)+c*S(floor(N/p))`.

Put `R(N)=(p-c)*S(N)-(p-1)*N`. Then

`R(N)=c*R(floor(N/p))+(1-c)*(N mod p)` and `0<=R(N)<=p-1`.

The last bounds follow by strong induction from `0<=c<=1` and `N mod p<=p-1`.
Thus the summatory density is exactly `(p-1)/(p-c)`, with a bounded remainder.
This is a literal digit recurrence, not an asserted regularity hypothesis.

For a proposed deletion coefficient `1-lambda*[p|n]`, its weighted sum is

`D_lambda(N)=S(N)-lambda*c*S(floor(N/p))`.

At the cutoffs `p*M`, the exact identity is

`(p-c)*D_lambda(p*M)=(p-1)*(p-lambda*c)*M+c*(1-lambda)*R(M)`.

The last term is bounded. Bounded deletion prefixes therefore force `lambda*c=p`.
Conversely that equality gives the sharper exact formula

`D_lambda(N)=N mod p-R(floor(N/p))`, hence `|D_lambda(N)|<=p-1`.

Thus boundedness is equivalent to `lambda*c=p`. In particular, keeping the literal coefficient `lambda=p` after a
nontrivial attenuation leaves nonzero linear drift; the unique repair changes the
deletion coefficient to `p/c`. A zero-preserving analytic quotient therefore does not
by itself preserve the original source construction.

At harmonic exponent one there is a direct lower bound. Let
`H(N)=sum_(1<=n<=N)1/n` and `B(N)=sum_(1<=n<=N)b(n)/n`.
Because `b=1` off the multiples of `p`,
`B(N)>=H(N)-H(floor(N/p))/p>=(1-1/p)*H(N)`.
The literal harmonic deletion is `B(N)-c*B(floor(N/p))`, hence at least
`(1-c)*(1-1/p)*H(N)`. It diverges for `c<1`.
Convergence at any complex exponent with real part below one would imply convergence
at real exponent one by the ordinary Dirichlet convergence theorem, a contradiction.

## Repaired admission and analytic comparison

The repaired coefficients have uniformly bounded ordinary prefixes, so the corpus's Abel
summation theorem gives ordinary convergence throughout `Re(s)>0`. The explicit case
`p=5,c=1/5` has unique multiplier 25 and prefix bound 4; the original multiplier 5 fails
at every `Re(s)<1`. The coefficients remain positive and at most one on every positive
integer, and completely multiplicative on all naturals.

For clarity, the analytic-continuation motivation has a separate elementary proof. In
`Re(s)>1`, split positive integers uniquely as `p^k*m` with `p` not dividing `m`, and sum
the absolutely convergent geometric series. The un-deleted series is

`F(s)=zeta(s)*(1-p^(-s))/(1-c*p^(-s))`.

For `0<=c<1`, the quotient is holomorphic and nonzero on `Re(s)>0`, so it preserves
zeta's zero divisor there. Literal deletion has far-right value
`(1-p*c*p^(-s))*F(s)`; its pole at one survives when `c<1`. Repaired deletion has factor
`1-p*p^(-s)`, which cancels that pole. The Lean proof of nonconvergence uses the direct
harmonic lower bound, not this continuation argument. The Euler-quotient identification is itself
Lean-closed, together with the holomorphic zero-free quotient, the zero-divisor preservation on
`Re(s)>0`, the surviving residue `(1-c)` times the local factor for the retained multiplier, and
the finite limit `log p` times the local factor under the repair.

## Formal status and scope

Every recurrence, remainder bound, normalization classification, harmonic drift,
open-strip nonconvergence statement, and repaired convergence statement above is
Lean-closed in `EulerDeletionPrimeAttenuation`; the Euler-quotient identity, the holomorphic
zero-free local factor, the zero-divisor preservation, the far-right deletion values and both pole
statements are Lean-closed in `EulerDeletionAttenuationEuler`. The concrete
`fifth_attenuation_admission_separation` is a premise-free capstone. See
the Lean certificate below.

These statements concern changing the source; they do not produce the missing relation
for the unchanged `n^(-s)` weights at a zeta zero. The broader attempt to classify
positive multiplicative weights from monotonicity has a classical parent:
Everett Howe, *A New Proof of Erdos's Theorem on Monotone Multiplicative Functions*,
American Mathematical Monthly 93 (1986), 593–595,
[paper](https://www.uaemath.com/uploaded/1/2322314.pdf). It is not a new RH architecture.

Corpus queries included `deletion pole`, `prime perturbation residue`, `normalization
multiplicative`, `monotone multiplicative`, and `deletion bounded rigidity`, paired with
`rg` of the literal deletion, valuation and Dirichlet-convergence statements. No search
miss certifies novelty. No mathematical computation is needed for this gate.

## Lean certificate

**Stage:** 3-formalized. **RH implication:** none. **Novelty:** not certified.

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionPrimeAttenuation.lean`.
Namespace: `RHTower.DeletionPrimeAttenuation`.

For a prime `p` and `0<=c<=1`, the actual coefficient is `b(n)=c^(v_p(n))` on positive
integers, extended by zero at zero. Lean proves complete multiplicativity, the upper bound
one, and strict positivity when `c>0`.

The exact summatory recurrence has bounded digit remainder
`R(N)=(p-c)*sum_(n<=N)b(n)-(p-1)*N`, with `0<=R(N)<=p-1`.
The general classification `bounded_deletion_iff` says that the coefficients
`(1-ell*[p|n])*b(n)` have bounded prefixes exactly when `ell*c=p`. At that normalization,
their prefix equals `N mod p-R(floor(N/p))`, with bound `p-1`.

`harmonicDeletion_tendsto` proves divergence to positive infinity at exponent one when
`c<1` and the original multiplier `p` is retained. Ordinary Dirichlet convergence propagates
to exponents further right; consequently `literal_not_convergent_of_re_lt_one` excludes
convergence at **every complex exponent with real part below one**. Conversely
`repaired_converges` admits the uniquely repaired coefficients throughout `Re(s)>0`.

The premise-free `fifth_attenuation_admission_separation` packages the concrete example
`p=5,c=1/5`: globally positive contractive multiplicative coefficients, unique multiplier
25, prefix bound 4, repaired positive-half-plane convergence, and failed literal convergence
at every `Re(s)<1`. No statement is made about other points on the boundary `Re(s)=1`.

`lake env lean /tmp/hgt-attenuation-LEwD86/Audit.lean` passed. Six axiom audits covering the
remainder, classification, divergence, two admission statements, and capstone report only
`propext`, `Classical.choice`, and `Quot.sound`. Production matches the audited scratch body.
The narrow final `lake build GaloisForLFunctions.RHTower.EulerDeletionPrimeAttenuation`
passed. Its umbrella import is wired; no full or umbrella build ran. Repository-wide
`scripts/formal_tools.py lint` failed solely on concurrent work outside this module:
`HTGeometry/QuarticJensenDispersionTransfer.lean` was unreachable from its theorem-area
umbrella. No lint error named this module. Output: `/tmp/hgt-attenuation-LEwD86/lint.log`.
That historical lint failure was cleared in the subsequent compatible-curvature audit:
repository-wide lint passed, with output `/tmp/hgt-compatible-curvature-Pe4gsu/lint.log`.

The paper proof also explains the motivating Euler quotient. That quotient identification is now a
separate Lean-closed module, `EulerDeletionAttenuationEuler`, namespace
`RHTower.DeletionAttenuationEuler`. From the literal finite dilation identity
`attenuatedPrefix_dilation` it proves `attenuatedSum_mul_denom` and the closed form
`attenuatedSum_eq`: in `Re s > 1` the attenuated Dirichlet series is exactly
`zeta(s)*(1-p^(-s))/(1-c*p^(-s))`. `differentiableAt_localFactor` and `localFactor_ne_zero` make
the Euler quotient holomorphic and zero-free on `Re s > 0`, so
`zeta_mul_localFactor_eq_zero_iff` preserves the zeta zero divisor there exactly.
`deletionPrefixC_tendsto` gives the far-right value `(1-ell*c*p^(-s))` times that product for the
literal deletion coefficients. `deletionFarRight_residue` together with
`deletionFarRight_residue_ne_zero` shows that the pole at one survives, with residue `(1-c)` times
the local factor, whenever the original multiplier `p` is retained and `c<1`; and
`repairedFarRight_tendsto` shows that under the repair `ell*c=p` the far-right value has the finite
limit `log p` times the local factor at one, so the pole is cancelled. Six axiom audits of these
statements report only `propext`, `Classical.choice` and `Quot.sound`; `lake env lean` and the
narrow `lake build` passed, the module is wired into the `RHTower` umbrella, and the repository-wide `scripts/formal_tools.py lint` passes; a later rerun failed only on another session's unwired module `RHTower.Sieve.MenonHarmonicBlockLevelSplitHM`. No computational experiment or certificate
was used.

This closes the [one-prime attenuation shortcut](../5-failed/euler-deletion-prime-attenuation-shortcut.md)
for extending finite coefficient countermodels to the infinite deletion source, with an
exact positive repair. It does not establish a relation forced by
an actual zeta zero, exclude off-line zeros, or qualify as a new RH architecture.
