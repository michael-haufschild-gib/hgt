# Euler--triptic continuation anomaly and source-framed curvature isotropy

- **ID:** `euler-triptic-continuation-anomaly-rh`
- **Stage:** 5-failed/retired as an RH producer; proved bridge content retained
- **Type:** RETIRED CONJECTURE with proved bridge and no-go theorems
- **Scientific status:** `[ANTI-THEATRE FAIL] [PARENT BRIDGE] [NOT AN RH PROOF]`
- **HT source:**
  - `../2-fully-proven/new_scientific_knowledge/triptic-orbit-residue-reciprocity.md`
  - `../2-fully-proven/new_scientific_knowledge/archimedean-relative-prime-cocycle-curvature.md`
  - `../3-formalized/multiple-elliptic-gamma-parity-inversion.md`
- **RH consumer:**
  - `../3-formalized/not_new_scientific_knowledge/gamma-mertens-orbit-coboundary-rh.md`
  - `calibrated-gamma-mertens-zero-orbit-comparison-rh.md`
- **Statement:** The prime-local hermitian gamma-gerbe curvatures have a universal reflection-null
  wall but no arithmetic content at finite Euler level.  Construct the source-canonical secondary
  current produced when the all-prime Euler diagonal is meromorphically continued, and prove that
  its framed FE/Schwarz boundary trace is curvature-isotropic.  Equality of the two resulting
  Mertens support curvatures forces every Xi zero onto `Re(s)=1/2`.

## Medalist lens

The triptic residue theorem is a finite, algebraic compatibility law.  RH requires an infinite,
metric statement.  The question is therefore not whether elliptic gamma can repackage zeta, but:

```text
where does arithmetic first enter after every prime-local triptic class
and every prime-local hermitian curvature has been divided out?
```

The answer cannot be the primary divisor, mixed cocycle, reflection law, or curvature.  All four
are either universal or parent theory.  The only live location is the noncommutation of the
all-prime limit, diagonal pullback, and meromorphic continuation.  The target is a secondary,
source-framed current at that failure of commutation.

## Candidate moves and verdicts

1. `[CONJECTURE -- BOHR TRIPTIC CURRENT]` Replace the missing common period in the global `s`
   coordinate by the prime Bohr compactification.  **Preliminary verdict:** Jessen--Tornehave and
   almost-periodic divisor theory are the parent; without a new source metric this produces a mean
   divisor current, not RH positivity.  The positive residue is the aperiodicity theorem below:
   the global Euler diagonal is faithful, so mean currents rather than compact elliptic divisors
   are the correct infinite-place objects.
2. `[CONJECTURE -- TRANSVERSE COMPLETION CLASS]` Vary the reflection center and differentiate at the
   completed center.  **Preliminary verdict:** the first variation is a logarithmic-derivative /
   explicit-formula bridge.  The positive residue is that the zeta divisor appears as a first-order
   continuation anomaly of a locally zero-free Euler family.
3. `[CONJECTURE -- RAW HERMITIAN TRIPTIC ISOTROPY]` Use the hermitian gamma-gerbe curvature directly.
   **Killed below:** after normalization it is identical for every finite prime set.  The positive
   theorem is the exact universal affine null-wall law.
4. `[CONJECTURE -- SOURCE-FRAMED CONTINUATION ISOTROPY]` Remove the universal primary curvature and
   retain the secondary continuation current, with its safe-half-plane framing.  **Retired as
   presently stated:** no finite-prime identity was found, and the asserted isotropy is the RH
   conclusion after the universal curvature calculation.  The only positive survivor is the
   ambiguity-classification problem for source-framed continuation currents.

## Medalist re-audit: why the conjectural RH step is retired

The universal lift, aperiodic Euler diagonal, and hermitian curvature are correct, but all lie in
named parent theories or are direct specializations.  The proposed current `(15)` was never
constructed independently of meromorphic continuation, and `(16)` says exactly that the two
supports have equal curvature.  Equation `(11)` then turns it immediately into
`2 Re(rho)-1=0`.  Without a finite-prime identity that forces `(16)`, this is an RH criterion in
gerbe language, not a source theorem.

The stronger saturation attempt also fails for the structural reason proved in
`../2-fully-proven/not_new_scientific_knowledge/da-gauge-ht-divisor-blindness.md`: the localized HT
boundary matroid is invariant under rational divisor gauges, whereas the desired continuation
current must change under them.  A divisor-sensitive current cannot factor through that quotient.

The nontrivial positive residue is exact.  The global Euler object belongs on an aperiodic product
of prime tori; its primary normalized curvature is universal; and any arithmetic continuation
invariant must be a pointed extension over, not a realization of, the gauge-invariant HT boundary
class.  The remaining ambiguity-torsor classification is mathematically meaningful, but it is no
longer advertised as the current RH producer.

## Universal reflected double lift `[PROVED HERE] [BRIDGE]`

Let `a,b>0`, put `A=a+b`, and let `G` be meromorphic with

```text
G(s)=1+O(exp(-c Re(s)))
```

uniformly on right translates of compact vertical sets, with the corresponding local condition
for reciprocal factors.  Define

```text
Y_G(s;a,b)
 = product_(j,k>=0) G(s+ja+kb)/G(A+ja+kb-s).                 (1)
```

The double product converges normally away from the translated divisor of `G`, hence defines a
meromorphic function.  It satisfies

```text
Y_G(A-s;a,b)=Y_G(s;a,b)^(-1),                                (2)

Y_G(s+A)Y_G(s)/(Y_G(s+a)Y_G(s+b))=G(s)/G(-s).                (3)
```

For `(2)`, reflection exchanges the two products.  For `(3)`, write

```text
H(s)=product_(j,k>=0)G(s+ja+kb),   Y_G(s)=H(s)/H(A-s).
```

The forward quadrant has mixed multiplicative boundary `G(s)`, while the reflected backward
quadrant has mixed boundary `G(-s)`; their quotient gives `(3)`.

Consequently the existence of a reflected two-shift primitive is not selective: every sufficiently
right-decaying meromorphic source has one.  Reflection plus the mixed equation cannot prove RH.
This is the exact anti-theatre failure of the naive elliptic-gamma Euler-product proposal.

For `G=zeta`, Euler factorization in a common right half-plane gives

```text
Y_zeta(s;a,b)
 = product_p Gamma_e(p^(-s);p^(-a),p^(-b))
 = product_(j,k>=0) zeta(s+ja+kb)/zeta(A+ja+kb-s),           (4)

Y_zeta(s+A)Y_zeta(s)/(Y_zeta(s+a)Y_zeta(s+b))
 = zeta(s)/zeta(-s).                                        (5)
```

Indeed the local elliptic-gamma mixed character is

```text
Gamma_e(p^(-(s+A)))Gamma_e(p^(-s))
 / (Gamma_e(p^(-(s+a)))Gamma_e(p^(-(s+b))))
 = -p^s,
```

and `-p^s=(1-p^s)/(1-p^(-s))` is exactly the local Euler factor of
`zeta(s)/zeta(-s)`.  Thus analytic continuation, not an arbitrary regularization, converts the
divergent all-prime character into the meromorphic zeta ratio.

This construction lies in the parent family of higher Riemann zeta functions, multiple Euler
products, multiple sine functions, and absolute tensor products.  It is infrastructure, not new
scientific knowledge.

## No common period on the Euler diagonal `[PROVED HERE] [BRIDGE]`

For distinct rational primes `p,q`, there is no nonzero `h in C` such that

```text
p^(-h)=q^(-h)=1.                                            (6)
```

If `(6)` held, then `h log p` and `h log q` would lie in `2 pi i Z`.  For nonzero `h`, their ratio
would make `log p/log q` rational, hence `p^m=q^n` for nonzero integers `m,n`, contradicting unique
factorization.  Therefore `h=0`.

Each prime-local gamma factor is periodic in its own additive coordinate, but two distinct primes
have no common nonzero period on the diagonal `s`-line.  The periodic triptic reciprocity theorem
therefore cannot be applied directly to the global product.  The positive statement is structural:
Euler assembly replaces compact triptic orbit divisors by a faithful aperiodic diagonal in a
product of prime tori.  Any global reciprocity law must be a restricted-product or mean-current
law and must state what survives diagonal pullback.

## Prime-local hermitian curvature `[PROVED HERE] [BRIDGE]`

Felder--Henriques--Rossi--Zhu construct a hermitian structure on the gamma gerbe.  In their
additive coordinates, for `t=Im(tau)>0`, `u=Im(sigma)>0`, `y=Im(z)`, its scalar metric factor is

```text
h_3(z,tau,sigma)=exp(-(2 pi/3) R_3(y,t,u)),

R_3(y,t,u)
 = y^3/(tu) -(3/2)(1/t+1/u)y^2
   +(t/(2u)+u/(2t)+3/2)y -(t+u)/4.                         (7)
```

Hence

```text
d^2 R_3/dy^2 = 6(y-(t+u)/2)/(tu).                          (8)
```

Restrict the metric to the Euler coordinate for a prime `p`:

```text
lambda_p=log(p)/(2 pi),
z=i lambda_p s,   tau=i lambda_p a,   sigma=i lambda_p b.  (9)
```

For `x=Re(s)`, the vertical fibre component of the Chern curvature pulls back to

```text
kappa_p(s)
 = i log(p)/(4 pi a b) * (A/2-x) ds wedge dbar(s).         (10)
```

The sign changes at the reflection wall and nowhere else.  For `A=1`, the null wall is precisely
`Re(s)=1/2`.

The Mertens pole supports attached to an Xi zero `rho`,

```text
u_rho=-rho,   v_rho=conjugate(rho)-1,
```

obey the exact curvature comparison

```text
kappa_p(u_rho)-kappa_p(v_rho)
 = i log(p)/(4 pi a b) * (2 Re(rho)-1) ds wedge dbar(s).   (11)
```

Thus equality of the two canonically pulled-back curvatures is equivalent to the critical-line
condition.  Equation `(11)` is a consumer, not a source theorem.

## Raw-curvature no-go and positive theorem `[PROVED HERE]`

For a finite prime set `S`, put `theta(S)=sum_(p in S) log p`.  Additivity of hermitian curvature
gives

```text
kappa_S(s)
 = i theta(S)/(4 pi a b) * (A/2-Re(s)) ds wedge dbar(s),   (12)

kappa_S/theta(S)
 = i/(4 pi a b) * (A/2-Re(s)) ds wedge dbar(s).            (13)
```

The normalized curvature is independent of `S`, of the distribution of primes, and even of
whether the selected integers are prime.  It is pure reflection kinematics.  Therefore the
critical null wall in `(10)` is not yet arithmetic evidence and cannot be treated as progress
toward RH.

The nontrivial positive conclusion is:

> In an infinite constrained hypertranscendental source, the primary hermitian curvature may be
> universal even when the meromorphic divisor is arithmetic.  The arithmetic invariant, if it
> exists, is a secondary continuation transgression after the universal curvature is removed.

This separates three layers which the naive proposal conflated:

```text
primary HT orbit divisor       -- finite and algebraic;
primary hermitian curvature    -- metric but universal on the Euler diagonal;
secondary continuation current -- potentially arithmetic and divisor-sensitive.   (14)
```

## Retired conjecture: source-framed continuation isotropy

Let `Y_X` be the finite product in `(4)` over `p<=X`, equipped with the pulled-back hermitian
gamma-gerbe metric.  Let `Y_zeta` be the meromorphic continuation of the right-half-plane limit in
the zeta-product presentation of `(4)`.

`[CONJECTURE -- CANONICAL CONTINUATION CURRENT]` There is a unique finite-part current

```text
Omega_(a,b)
 = FP_(X->infinity) (
     PL(Y_zeta)-PL(Y_X)-the universal bulk counterterm from (12))       (15)
```

characterized entirely by:

1. agreement with the convergent Euler product on one safe right half-plane;
2. the hermitian gamma-gerbe connective structure and its Bernoulli curvature counterterm;
3. the completed Gamma asymptotic normalization;
4. compatibility with the functional equation and Schwarz involution;
5. no divisor input and no cutoff-dependent additive current.

Here `PL` denotes the Poincare--Lelong current of the metrized meromorphic section.  Formula `(15)`
is schematic until the finite-part topology and counterterm are proved unique; declaring them by
analytic continuation alone is not enough.

`[RETIRED CONJECTURE -- FRAMED ISOTROPY]` The FE and Schwarz boundary traces of `Omega_(a,b)` at every Xi
zero have equal fibre curvature at the two Mertens support germs:

```text
Xi(rho)=0  ==>  kappa_p(-rho)=kappa_p(conjugate(rho)-1)    (16)
```

for one, hence every, prime `p`.  Equivalently, the framed trace supplies the finite shift-two
orbit coboundary already isolated in the Lean RH consumer.

By `(11)`, `(16)` gives `Re(rho)=1/2`; applying it to every zero proves RH.

## Anti-theatre requirements on the open core

The conjecture is rejected unless all of the following are met.

1. **Pre-divisor construction.** `Omega_(a,b)` is built on the safe Euler half-plane and continued
   without using a zero, zero enumeration, or divisor Hilbert space.
2. **Finite-prime precursor.** Isotropy must be the limit of a stated finite-prime identity or
   inequality.  A direct assertion of `(16)` is RH in new notation.
3. **Framing.** A symmetric rational quartet changes the safe-anchor trivialization.  If `(15)` is
   invariant under that insertion, it is the already formalized unframed-cohomology blindness and
   the route is dead.
4. **No imported Weil positivity.** Identifying the resulting form with the Weil form is allowed;
   assuming its positivity is not.  Positivity must follow from the hermitian gerbe construction.
5. **Counterterm uniqueness.** If two source-compatible finite parts differ by a current capable of
   moving a free zero quartet, the construction has only renamed the boundary-condition ambiguity.
6. **Parent-theory gate.** Hermitian gamma gerbes, higher zeta products, Poincare--Lelong, Jessen
   currents, and the Weil explicit formula are parents.  Only the source-canonical finite part and
   a proof of framed isotropy could constitute new scientific knowledge.

## Further attacks and positive successors

1. **Universal-lift no-go.** Every decaying meromorphic source has `(1)`.
   **Positive successor:** source selection must live in the continuation finite part, not in
   solvability of the mixed constraint.
2. **Aperiodicity no-go.** Distinct primes have no common diagonal period.
   **Positive successor:** the global HT object is a restricted-product current on the faithful
   prime diagonal, not an elliptic divisor on one curve.
3. **Raw-curvature no-go.** Equation `(13)` forgets the primes after one scalar normalization.
   **Positive successor:** arithmetic first appears as a secondary curvature anomaly.
4. **Hermitian-parent no-go.** The gamma gerbe already has a canonical hermitian structure and
   computed curvature.
   **Positive successor:** the genuinely unanswered question is its all-prime Euler transgression,
   not construction of another metric.
5. **Reflection/unitarity no-go.** A reciprocal reflection law or unit modulus on the fixed line
   does not constrain off-line Blaschke/rational-quartet zeros.
   **Positive successor:** the trace must retain the source anchor and distinguish trivial bulk
   gerbe gauge from nontrivial boundary trivialization.
6. **HT-independence no-go.** Differential-algebraic independence does not prevent independent
   functions from sharing prescribed isolated zeros; multiplying independent functions by the
   same rational factor preserves independence over `C(s)`.
   **Positive successor:** an RH proof needs a divisor-to-constraint incidence law, not more
   transcendence degree.
7. **Anomaly-class no-go.** A Dixmier--Douady or cohomology class alone is unchanged by a boundary
   rational gauge.
   **Positive successor:** the invariant must be a *framed differential character*—bulk class,
   hermitian connection, and calibrated boundary trivialization together.
8. **Failure of finite-part uniqueness.** If `(15)` is scheme-dependent, this route dies.
   **Positive theorem to retain:** classify the ambiguity group and prove that its action is exactly
   the group of symmetric divisor insertions; this would identify, for general HT sources, the
   precise obstruction to recovering global divisors from local constraints.
9. **Failure of isotropy after a canonical finite part.** If the canonical current exists but is not
   isotropic, the RH route dies.
   **Positive theorem to retain:** its nonzero paired curvature charge is then a source-defined
   quantitative measure of FE/Schwarz separation, a new global invariant of infinite Euler-type HT
   sources even without an RH consequence.

## Parent and novelty audit

- Kurokawa--Wakayama, Akatsuka, and Momotani place `(1)`--`(5)` in the parent world of higher
  Riemann zeta functions, multiple Euler products, absolute tensor products, and multiple sine
  regularization.
- Felder--Varchenko and Felder--Henriques--Rossi--Zhu supply the elliptic-gamma modular identities,
  gamma gerbe, hermitian structure, and curvature.  Equations `(7)`--`(13)` are specializations and
  consequences, not a new metric theory.
- Jessen--Tornehave theory is the parent for almost-periodic mean divisor currents.
- Poincare--Lelong and Weil's explicit formula are the parent current and RH-positivity mechanisms.

No source-canonical current satisfying `(15)` and no finite-prime proof of `(16)` has been located.
The route is retired rather than left as a vague open producer: its concrete content is parent
bridge material, while its decisive line is currently only an RH-equivalent isotropy assertion.

## Smallest generative next move

Define the finite-prime metrized section and its Poincare--Lelong current on the product of the
prime-local triptic curves, then prove or refute:

```text
the difference between the two face transgressions is an exact boundary current
whose diagonal pullback has a cutoff-independent finite part.                  (17)
```

The first falsifier is a symmetric rational quartet: compute its change in the calibrated finite
part without using its zeros as construction data.  If the change vanishes, `(17)` is too coarse.
If it is the nonzero safe-anchor charge already seen by the rational-gauge theorem, the framing has
survived and the next step is to compare `(17)` with the Mertens shift-two boundary.

## Gates

- [x] 0 -> 1: exact Euler--elliptic-gamma lift and mixed zeta-ratio source derived
- [x] 0 -> 1: direct application of periodic triptic reciprocity killed by prime-diagonal aperiodicity
- [x] 0 -> 1: hermitian gamma-gerbe parent located and exact Euler pullback curvature derived
- [x] 0 -> 1: raw curvature killed as arithmetic selector; universal normalized law proved
- [x] 0 -> 1: every no-go assigned a nontrivial positive successor and a general-HT interpretation
- [x] anti-theatre re-audit: present isotropy formulation retired as an RH restatement
- [ ] positive successor: ambiguity torsor of source-compatible finite parts classified
- [ ] 1 -> 2: canonical finite-part current constructed with uniqueness proof
- [ ] 1 -> 2: rational-quartet framing test passed
- [ ] 1 -> 2: finite-prime face-transgression identity proved
- [ ] 1 -> 2: framed isotropy proved without imported Weil positivity
- [ ] 1 -> 2: RH deduced on paper
- [ ] 1 -> 2: independent novelty and significance audit
- [ ] 2 -> 3: only the decisive, non-parent theorem formalized in Lean
- [ ] 3 -> 4: standalone preprint and independent expert audit

## Primary sources checked

- G. Felder and A. Varchenko, *The elliptic gamma function and `SL(3,Z) x Z^3`*, Advances in
  Mathematics 156 (2000), 44--76, arXiv `math/9907061`.
- G. Felder, A. Henriques, C. A. Rossi, and C. Zhu, *A gerbe for the elliptic gamma function*,
  Duke Mathematical Journal 141 (2008), 1--74, arXiv `math/0601337`.
- H. Akatsuka, *Euler Product Expression of Triple Zeta Functions*, International Journal of
  Mathematics 16 (2005), 111--136, DOI `10.1142/S0129167X05002825`.
- N. Kurokawa and M. Wakayama, *Absolute Tensor Products*, International Mathematics Research
  Notices 2004(5), 249--260, DOI `10.1155/S1073792804132327`.
- T. Momotani, *Regularized product expressions of higher Riemann zeta functions*, arXiv
  `math/0504218`.

## Log

- 2026-07-15 -- opened after the anti-theatre audit killed the direct application of triptic
  orbit-residue reciprocity to the all-prime diagonal.  Derived the universal lift, zeta-ratio mixed
  source, diagonal aperiodicity, hermitian curvature null wall, and raw-curvature blindness.  The
  source-framed secondary continuation current is the sole surviving conjectural mechanism.
- 2026-07-15 -- medalist re-audit retired that mechanism as an RH producer: no finite-prime
  isotropy identity was found, the primary metric is universal, and the localized HT class is
  rational-gauge blind.  Retained the exact bridge theorems and the ambiguity-torsor problem.
