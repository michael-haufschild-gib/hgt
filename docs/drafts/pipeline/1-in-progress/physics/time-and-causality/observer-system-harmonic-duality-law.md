# Observer--system harmonic duality law of quantum return

- **ID:** `observer-system-harmonic-duality-law`
- **Stage:** 1-in-progress
- **Type:** FROZEN MASTER CONJECTURE / EXACT RECURRENCE INFORMATION LAW
- **Freeze date:** 2026-07-30
- **Scientific status:** `[CONJECTURE FROZEN AFTER CORPUS AUDIT]`
  `[KINEMATIC CORE AND OPERATIONAL COLLISION EXTREMALITY LEAN-PROVED]`
  `[TWO-AXIS REPLICA RECIPROCITY LEAN-PROVED]`
  `[LOCAL GENERATOR PAPER-PROVED, LEAN OPEN]`
  `[NOVELTY AND NATURE GATES OPEN]`
- **Manuscript rule:** formal verification is internal correctness control.
  It is never mentioned and contributes nothing to novelty or significance.

## The jump

> **Quantum return is not a property of a system alone. It is a harmonic
> duality between what the system can repeat and what the observer calls
> time.**

The raw energy law and raw clock law are not physical invariants of a
survival-return experiment. Every such experiment factors through exactly
two quotient laws:

\[
  \nu_\mu=\mu*\widetilde\mu ,
  \qquad
  \sigma_\rho=\frac{\rho+\widetilde\rho}{2}.
\]

Here \(\nu_\mu\) is the system's energy-autocorrelation law and
\(\sigma_\rho\) is the observer's unoriented clock law. The conjectural
master interpretation is:

> **Every stationary quantum-recurrence law is a consequence of the pairing
> between \(\nu_\mu\) and \(\sigma_\rho\); every recurrence obstruction is
> information destroyed before that pairing, and every recurrence phase is
> geometry retained by it.**

This hunch was not chosen because its proof was visible. It was formed after
the corpus repeatedly exposed the same failures: energy origin is invisible,
time orientation is invisible, homometric spectra are indistinguishable,
finite histories miss global completion, continuous spectra erase collision
mass, dissipation deletes transient directions, and interaction destroys
additive resonances. The claim is that these are shadows of one two-sided
quotient, not separate facts.

## Exact proposed law

Let \(\mu\) be any probability energy law on \(\mathbb R\), let \(\rho\) be
any probability law of clock readings, and let
\[
 F_\mu(t)=|\widehat\mu(t)|^2=\widehat{\nu_\mu}(t).
\]
The complete observed return law is
\[
 \mathcal R(\mu,\rho)=(F_\mu)_*\rho .
\]
Its moments obey, for every \(n\geq0\),
\[
 \boxed{
 \int F_\mu(t)^n\,d\rho(t)
 =
 \int \widehat{\sigma_\rho}(x)\,
      d\nu_\mu^{*n}(x).
 }
 \tag{HD}
\]

The frozen conjecture asserts that `(HD)` is the master law in the following
strong sense.

1. **Double maximality.** Two systems give the same complete return law for
   every clock exactly when their autocorrelation laws agree. Two clocks give
   the same complete return law for every system exactly when their
   orientation quotients agree. No further system or clock information is
   universally observable by survival return.
2. **Minimal universal reporters.** Universal system equivalence is decided
   by first moments at deterministic times. Universal clock equivalence is
   decided by first moments of balanced two-level systems.
3. **Exact infinity threshold.** No finite deterministic-time schedule can
   decide universal system equivalence, and no finite two-level gap schedule
   can decide universal clock equivalence. One fixed countable dense rational
   schedule decides each exactly.
4. **Replica completion.** The powers \(\nu_\mu^{*n}\) give the entire
   observed return distribution. Uniform long-time observation extracts
   their zero-collision masses.
5. **Temporal geometry.** The rational support-difference group of the atomic
   part of \(\nu_\mu\) is the compact recurrent temporal hull. Its rank is
   observer-visible temporal dimension; its Haar target volume gives return
   density.
6. **Loss boundary.** Finite contractive dynamics first restricts to its
   peripheral spectral law. Transient mass fixes the exact late-return
   ceiling; `(HD)` governs everything that survives.
7. **Interaction extremality.** Generic nearest-neighbour interaction moves
   the system quotient to maximal projective rank and therefore to the
   simultaneous minimum of every nontrivial replica-collision moment at fixed
   spectral weights.
8. **Completion boundary.** Local moments, Krylov data, perturbative jets and
   finite histories fail precisely when they do not determine
   \(\nu_\mu\). Exact global return data determine \(\nu_\mu\), but can never
   determine a phase-retrieval representative \(\mu\) inside its homometric
   fibre.

Clauses 1--4 are already unconditional theorems for arbitrary probability
laws. Clauses 5--6 are existing unconditional corpus theorems in their exact
domains. Clause 7 is paper-proved for open qudit paths but lacks formal
closure. Clause 8 is proved through explicit global-completion and
phase-retrieval counterexamples, but its fully abstract “precisely” wording
requires a single factorization theorem before manuscript use.

## What everyone has been looking at separately

| Prior phenomenon | Shadow cast by the dual law |
|---|---|
| Poincaré recurrence | Compact atomic part of \(\nu_\mu\) |
| Spectral form factor | One statistic of \(\widehat{\nu_\mu}\) |
| Higher no-resonance | Absence of nontrivial atoms at zero in \(\nu_\mu^{*n}\) |
| Observer-dependent time | Reporter-dependent quotient of \(\nu_\mu\)'s support group |
| Integrable/interacting fracture | Low-rank versus maximal-rank support arithmetic |
| Continuous-spectrum nonreturn | Atomless face of the autocorrelation cone |
| Dissipative return ceiling | Peripheral restriction before harmonic pairing |
| Clock-reversal blindness | Passage \(\rho\mapsto\sigma_\rho\) |
| Energy-origin blindness | Passage \(\mu\mapsto\nu_\mu\) |
| Homometric ambiguity | Nontrivial fibre of \(\mu\mapsto\nu_\mu\) |
| Failure of finite prediction | No finite set separates the quotient cone |
| Countable exact tomography | Continuity plus Fourier uniqueness |

## What the new mathematics must solve

The master object is not the raw Hamiltonian. It is the paired geometry of:

\[
 \mathcal A
 =\{\mu*\widetilde\mu:\mu\in\operatorname{Prob}(\mathbb R)\},
 \qquad
 \mathcal S
 =\{\sigma\in\operatorname{Prob}(\mathbb R):\sigma=\widetilde\sigma\}.
\]

The missing mathematics is the geometry of the autocorrelation cone
\(\mathcal A\), its homometric fibres, and the separating power of the
Fourier pairing between \(\mathcal A\) and \(\mathcal S\). A satisfactory
theory must:

1. characterize which symmetric probability laws are autocorrelation laws;
2. classify or sharply bound the fibres of
   \(\mu\mapsto\mu*\widetilde\mu\);
3. identify extreme and collision-minimizing strata;
4. give stability moduli for finite noisy restrictions of the pairing;
5. prove how tensor-local interaction moves physical spectral families
   through those strata.

The current master paper does not need to solve the entire range problem.
It must answer its stated physics questions completely using the exact
maximal quotient, sharp finite/countable threshold, replica hierarchy, and
local-interaction extremality. Unsolved range classification cannot appear
as an open question in the paper.

## New theorem forced by the antagonist audit

The collision language is now connected directly to the measured
finite-spectrum survival probability. For every finite real spectrum
\((E_j)\), every real weight vector \(p\), every replica order \(n\), and
every symmetric window radius \(T\), define
\[
 A(t)=\sum_jp_j e^{itE_j},
 \qquad
 \mathcal M_n(T)=\frac1{2T}\int_{-T}^{T}|A(t)|^{2n}\,dt .
\]
The exact finite-window expansion is
\[
 \mathcal M_n(T)
 =
 \sum_{\substack{|k|=n\\|\ell|=n}}
 {n\choose k}{n\choose\ell}
 \prod_jp_j^{k_j+\ell_j}
 \operatorname{sinc}\!\left(
 T\left[\sum_jk_jE_j-\sum_j\ell_jE_j\right]\right).
 \tag{OR}
\]
Consequently,
\[
 \lim_{T\to\infty}\mathcal M_n(T)
 =
 \sum_{\substack{|k|=n,\ |\ell|=n\\
 \sum_jk_jE_j=\sum_j\ell_jE_j}}
 {n\choose k}{n\choose\ell}\prod_jp_j^{k_j+\ell_j}.
 \tag{OC}
\]
For full-support positive weights, this yields the observable equivalence
\[
 \boxed{
 \text{maximal projective rational spectral rank}
 \iff
 \text{every long-time return moment attains its permutation floor}.
 }
 \tag{OE}
\]
Every nontrivial balanced integer energy relation therefore has an
operational signature: it creates a strictly positive excess in a finite
replica moment. This closes the previous gap between an arithmetic rank
statement and an actual time-averaged quantum observable.

Formal closure:

- `formal/GaloisForLFunctions/HTGeometry/ReplicaCollisionExtremality.lean`
  proves `(OR)`, `(OC)`, and `(OE)` without positivity, normalization, or
  genericity assumptions beyond those explicitly needed by the equality
  classification.

## Reciprocal hierarchy: no privileged system/clock label

The one-axis law `(HD)` is the \(m=1\) boundary of a symmetric two-axis
object. For arbitrary probability laws \(\alpha,\beta\) on \(\mathbb R\),
define
\[
 \mathfrak H_{m,n}(\alpha,\beta)
 =
 \int \widehat\beta(t)^n\,d\alpha^{*m}(t).
 \]
Then, for every \(m,n\geq0\),
\[
 \boxed{
 \mathfrak H_{m,n}(\alpha,\beta)
 =
 \mathfrak H_{n,m}(\beta,\alpha).
 }
 \tag{RR}
\]
Applying this to the visible gap laws of two probability spectra
\(\mu,\lambda\) gives a mutual recurrence hierarchy
\[
 \mathfrak R_{m,n}(\mu,\lambda)
 =
 \int |\widehat\lambda(t)|^{2n}\,
 d\nu_\mu^{*m}(t)
 =
 \mathfrak R_{n,m}(\lambda,\mu).
 \tag{MR}
\]
Thus “system” and “clock” are not primitive labels in the harmonic
recurrence hierarchy. Each spectrum can supply the visible gap law against
which the other spectrum's return is sampled, and exchanging the roles is
an exact symmetry when the replica axes are exchanged.

Formal closure:

- `formal/GaloisForLFunctions/RHTower/ObserverRecurrenceDistributionLaw.lean`
  proves `(RR)` and `(MR)` for every pair of real probability laws and every
  pair of natural replica orders.

## What this is telling us

The missed object is not a Hamiltonian orbit in an external time coordinate.
It is a **paired collision hierarchy**:
\[
 \boxed{
 \text{observed recurrence}
 =
 \text{clock transfer}
 \;\langle\!\langle\;
 \text{system gap collisions}.
 }
\]
This changes the interpretation of every earlier result.

1. A system does not possess an observer-independent return law. It possesses
   a visible gap hierarchy; a clock chooses a harmonic reporter on it.
2. A clock does not merely add measurement noise. Its unoriented law is the
   second physical argument of recurrence.
3. Energy origin, spectral phase and clock orientation disappear because
   they lie in the kernels of the two canonical quotient maps.
4. Replica moments count equal-energy histories. Rational spectral rank is
   exactly the condition that only permutation-identical histories collide.
5. Temporal dimension is the rank of the character group that survives both
   quotients, not a count of spatial coordinates and not automatically a
   count of Hamiltonian parameters.
6. Interaction matters because it can destroy all nontrivial equal-energy
   histories at once, thereby maximizing visible temporal rank and minimizing
   every long-time return moment at fixed weights.

This is the candidate worldview shift:

> **Quantum time is the character geometry of mutually observable
> collisions. Recurrence is relational because neither the spectrum nor the
> clock has a return law alone.**

## Antagonist finding on the new reciprocity

`(RR)` alone is not a Nature result. Mathematically it is powered by Fubini,
convolution and Fourier multiplication. A hostile reviewer can correctly
call the bare identity a repackaging of classical harmonic analysis.

Its value is structural: it identifies the two-dimensional object of which
the previous system-only, clock-only, long-time, finite-probe and collision
laws are boundary slices. Nature-level significance still requires a
nonclassical consequence that the hierarchy makes possible. The strongest
surviving candidate is:

\[
 \boxed{
 \text{arbitrarily weak generic bounded-range interaction activates }
 q^n-1
 \text{ temporal characters and simultaneously removes every excess
 replica collision.}
 }
\]

That local generator theorem is paper-proved but remains unauthorized for
the manuscript until its tensor-local spectral witness is formally closed.

## Public meaning

> **A quantum system does not carry a recurrence clock by itself. Repetition
> is created jointly by its energy differences and the observer's clock.**

Three exact consequences are understandable without the mathematics:

1. asking only “has it returned?” can never reveal the origin of energy or
   the direction of time;
2. no finite universal return schedule identifies everything that return can
   reveal, although one countable universal schedule does;
3. generic local interaction removes every accidental replica resonance and
   makes whole-system return as rare as quantum unitarity permits.

The stronger black-hole sentence is only a certification law:

> **Entropy does not determine a black hole's recurrence. Its visible
> autocorrelation law and replica collisions do.**

No real-black-hole prediction is licensed without a gravitational spectral
bridge.

## Hard falsifiers

Retire the master interpretation if any one occurs.

1. A survival-return experiment distinguishes two systems with equal
   autocorrelation laws.
2. A survival-return experiment distinguishes two clocks with equal
   orientation quotients.
3. A finite universal probe family separates all system or clock quotient
   laws.
4. Rational first-moment probes fail to separate either quotient.
5. Some continuous return statistic is not fixed by the replica moments.
6. Local maximal projective rank fails on a positive-measure subset of the
   stated nearest-neighbour path family without enforced symmetry.
7. A prior source states the same double-maximal quotient, exact
   finite/countable threshold, replica completion and local-interaction
   extremality as one law.
8. Hostile review shows that removing the local-interaction theorem leaves
   the paper's main physical conclusion unchanged.

## Current hostile verdict

The duality is a stronger and cleaner master organization than the
replica-collision law alone. It explains why system, clock and reporter
obstructions come in matched pairs and adds an exact finite/countable
completeness transition.

It has not yet earned a Nature claim:

- Wiener--Khinchin, phase retrieval, characteristic-function uniqueness and
  Fourier duality are classical parents;
- the double-maximality and sharp universal probe threshold appear absent
  from the checked recurrence literature, but absence is not priority;
- the only currently plausible new physics anchor remains generic
  nearest-neighbour all-order collision extremality;
- a finite-horizon experimentally measurable consequence of that extremality
  remains necessary.

**Verdict:** `STRONG MASTER CONJECTURE; KINEMATIC CORE CLOSED; NEW PHYSICS
ANCHOR AND NATURE SIGNIFICANCE NOT YET CLOSED`.

## Deeper audit: survival, returnability and observer action

The finite peripheral theory does not itself supply the missing universal
interpretation. In infinite dimension, persistent norm and returnability
separate: a unilateral shift preserves norm while moving a localized state
away from itself. Thus
\[
 \text{survival}\neq\text{return}
\]
outside finite pure-point dynamics. Any master law that calls persistent mass
the universal recurrence invariant is false beyond its finite domain.

The surviving common object is instead the **observer action**
\[
 A=T\lambda ,
\]
where \(T\) is the clock horizon and \(\lambda\) is a real detuning for a
unitary character or a complex left-half-plane mode for a contractive
semigroup. The corpus already proves both exact kernels:

- unitary characters are reported by the clock characteristic function,
  with uniform clocks giving the sinc kernel;
- contractive modes are reported by
  \(\Phi(A)=(e^A-1)/A\), with \(\Phi(0)=1\);
- finite action survives, while unbounded contractive action is erased;
- analytic birth valuation, local connected-spanning cost and replica height
  determine which actions can become visible at which horizons.

This supports a stronger interpretation than “recurrence is a property of a
Hamiltonian”:

> **Observable quantum time is the quotient of spectral characters by
> observer action. Recurrence is the collision readout of that quotient.**

The statement is genuinely broader than closed dynamics, but its bare kernel
identities remain classical Fourier/Laplace analysis. It becomes a new
physical law only when a nontrivial local generator theorem calculates the
action quotient for a broad Hamiltonian class.

## Local generator: first formal relation-destruction interface

The distinct-pole algebraic step was already present for finite Cauchy
packets. The missing endpoint-extension argument required an arbitrary finite
index version and the graph propagation that turns residue equalities into
trace-only rigidity. These are now closed in
`formal/GaloisForLFunctions/HTGeometry/LocalSpectralExtensionRelationRigidity.lean`:

1. `distinctNodePacketNumerator_eq_zero_iff` proves injectivity of every
   finite simple-pole numerator over an arbitrary finite index type.
2. `crossLayer_eq_of_distinctPole_identity` turns the cleared second-order
   residue identity into cross-layer coefficient equality when transition
   weights are nonzero.
3. `hasSpareLabel_of_three_le_card` isolates the exact \(q\geq3\) local
   combinatorics.
4. `crossLayerEquality_constant` proves that connected transition geometry
   then leaves only one constant coefficient packet, i.e. the trace
   direction.

Foreground verification passed warning-free. The remaining physical bridge
is now narrower and explicit:

\[
 \boxed{
 \text{derive the second-order eigenbranch residue identity for an actual
 Hermitian endpoint coupling.}
 }
\]

After that bridge, the genericity layer must still convert one relation-free
local witness into the dense full-measure \(G_\delta\) theorem.

## Local generator: analytic bridge closed

The formerly missing perturbation input is now derived from the
characteristic equation itself.

`ComplexDeterminantSecondJet.lean` proves:

1. complex determinant first and second jets through the finite Leibniz
   expansion;
2. singular Jacobi first variation in adjugate form;
3. zero determinant two-jet for every actual analytic characteristic-root
   branch;
4. zero first eigenvalue velocity for a simple diagonal level under every
   zero-diagonal affine perturbation.

`AffineEigenbranchSecondOrderLaw.lean` then constructs the canonical
adjugate-column eigenvector germ and proves, without a perturbation-theory
hypothesis,
\[
 \lambda_x''(0)
 =
 2\sum_{y\ne x}
 \frac{V_{xy}V_{yx}}{E_x-E_y}.
\]
It also proves the finite relation-response law: every branchwise linear
spectral relation annihilates the corresponding sum of second-order gap
responses.

`LocalSpectralExtensionRelationRigidity.lean` now additionally proves that a
simple-pole identity on any infinite pole-free parameter set clears to the
zero numerator and hence forces every nonzero-weight cross-layer coefficient
equality.

All three direct foreground checks pass warning-free. The analytic
second-order bridge recorded above is closed.

Remaining generator obligations:

1. instantiate the affine response law for the endpoint tensor coupling and
   reorganize its finite sum into the cross-layer pole packet;
2. prove ordered-gap pole injectivity from maximal projective rank;
3. assemble the \(q\ge3\) endpoint induction and generic relation
   polynomials;
4. close the separate \(q=2\) witness/parity route;
5. derive a finite-horizon observable separating maximal temporal rank from
   symmetry-protected low rank.

Current interpretation:

> **Local interaction is a relation eraser: it converts spatially bounded
> couplings into new independent observable time characters.**

If the generator theorem closes, the master law becomes:

> **Observer action decides which characters exist operationally; local
> interaction creates their dimension; collision geometry fixes every
> recurrence statistic.**

This is the first candidate found in this route that can explain observer
quotients, resonance obstructions, all-order collision laws, recurrence
scarcity and the commuting-to-interacting rank jump as consequences of one
mechanism. Nature-level status remains withheld until the remaining
generator and finite-horizon obligations close.

### Ordered-pole label closed

`ReplicaCollisionExtremality.lean` now proves
`maximallyProjectiveEnergy_orientedGap_injective`: maximal projective rank
makes
\[
 (a,b)\longmapsto E_a-E_b,\qquad a\ne b,
\]
injective on ordered transitions. Gap equality reduces to replica rigidity
at order two; nonzero-gap orientation rules out the reversed multiset
pairing. Direct foreground verification passes warning-free.

The second remaining generator obligation is closed. The next open core is
the finite tensor-coupling sum reorganization that feeds these ordered poles
into `crossLayer_eq_of_rational_identity`.

## Interaction-lift law and exact endpoint bridge

The finite tensor-coupling reorganization is now closed in
`LocalTwoLayerSpectralResponse.lean`. For a shifted two-level extension it
proves the exact identity
\[
\sum_i c_i\sum_{j\ne i}
\frac{V_{ij}V_{ji}}{\mathcal E_i-\mathcal E_j}
=
\sum_{\alpha,\beta}
\frac{(c_{\alpha,0}-c_{\beta,1})
A_{\alpha\beta}A_{\beta\alpha}}
{z+E_\alpha-E_\beta}.
\]
No diagonal term was silently discarded: all \(\alpha=\beta\) terms share
the zero-gap pole, and
`coefficients_eq_zero_of_shifted_rational_identity_with_zeroPole` proves
that this repeated pole cannot conceal any distinct nonzero-gap residue.

The same module now proves:

1. the forbidden layer shifts form a finite set, so collision-free shifts
   are infinite;
2. maximal projective rank makes the old spectrum simple and every
   oriented transition pole distinct;
3. every actual analytic eigenbranch relation yields the exact residue
   packet;
4. every nonzero forward-backward transition product therefore forces the
   corresponding cross-layer coefficient equality.

The more universal object exposed by this proof is the **interaction lift**
\[
 \widetilde G_\rho:
 \qquad
 (\alpha,r)\sim(\beta,s)
 \iff
 \alpha\sim_G\beta\ \text{and}\ r\ne s .
\]
`LocalSpectralExtensionRelationRigidity.lean` proves:

- vanishing of all distinct-pole response packets is equivalent to the
  coefficient function being a component-constant \(0\)-cochain on
  \(\widetilde G_\rho\);
- the nontrace relation space has exact dimension
  \[
  \dim \widetilde H^0(\widetilde G_\rho;\mathbb C)
  =
  \#\pi_0(\widetilde G_\rho)-1;
  \]
- for \(q\ge3\), a connected old transition graph makes every coefficient
  constant by the spare-label mechanism;
- for \(q=2\), a connected graph containing a triangle removes the parity
  obstruction and again leaves only the trace direction.

This replaces the earlier slogan with a precise candidate universal law:

> **Local interaction creates independent observable time characters
> exactly by killing reduced \(H^0\) of its interaction lift.**

It explains the previously separate \(q\ge3\) success, qubit parity
obstruction, odd-cycle repair, trace survivor and rank jump through one
invariant. Direct foreground checks of both modules pass warning-free.

Remaining before the nearest-neighbour theorem is formal:

1. formalize endpoint-observable path witnesses and the induction that
   supplies connected lift geometry;
2. formalize symmetric relation polynomials and the dense full-measure
   \(G_\delta\) genericity step;
3. derive finite-horizon observable consequences.

Nature-level status remains withheld. The interaction-lift law is genuine
new organizing mathematics, but the physical locality-to-genericity
assembly and a discriminating observable are still required.

### Arbitrary local dimension closed at the analytic bridge

`LocalSelectedLayerSpectralResponse.lean` now selects any distinct
\(r,s\) inside an arbitrary finite local alphabet and proves:

1. all unselected layers disappear exactly from second-order response;
2. the selected pair produces the same oriented-gap residue packet as the
   Boolean extension;
3. every analytic spectral relation for the full product spectrum forces
   \(c_{\alpha,r}=c_{\beta,s}\) on every nonzero transition.

Thus the local analytic theorem is no longer a qubit statement. Local
dimension changes only connectivity of the interaction lift. The separate
\(q=2\) and \(q\ge3\) arguments are now recognized as two topological ways
to make the same reduced-\(H^0\) obstruction vanish.

Direct foreground verification passes warning-free. The first remaining
generator obligation above is closed.

## Hostile novelty correction and master-kernel target

Three tempting headlines fail priority:

1. generic doubly-exponential quantum recurrence already appears in Campos
   Venuti (2015);
2. rigorous dimension-dependent recurrence-time bounds and random-Hamiltonian
   saturation now appear in Kotowski--Oszmaniec (accepted PRL, 2026);
3. connectivity and the Boolean parity split of the categorical graph product
   are classical (Weichsel, 1962).

Therefore neither recurrence scarcity, dimension scaling, nor interaction
lift connectivity is the new law.

The stronger surviving target is one exact projective relation kernel
\(\mathcal R\).  Its shadows are:

- \(\operatorname{rank}(L/\mathcal R)\): operational dimension of time;
- cosets of \(\mathcal R\): observationally indistinguishable phase histories;
- replica pairs whose difference lies in \(\mathcal R\): all return-moment
  excess above the permutation floor;
- the local-response tangent kernel: component-constant cochains on the
  interaction lift;
- \(\widetilde H^0\) of that lift: exact number of nontrace relations that
  local interaction fails to erase.

The intended master statement is:

> **Quantum recurrence is the return law of an observer-visible projective
> character quotient.  Observer action selects the quotient; local
> interaction changes it by killing reduced interaction-lift cohomology; all
> recurrence statistics are Fourier moments of the resulting quotient.**

This is not yet a theorem merely because each noun is formalized elsewhere.
The next required bridge is an all-order observer-action recurrence
projection proving that every return moment, not only the quadratic mean, is
the corresponding finite sum of character-action coefficients.  Only after
that composition, the local-Hamiltonian generator, and a finite-horizon
discriminator close may the earlier results be presented as corollaries of
one kernel law.
