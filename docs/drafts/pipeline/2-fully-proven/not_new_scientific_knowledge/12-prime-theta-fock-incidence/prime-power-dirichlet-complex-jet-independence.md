# Prime-feature polarization forces complex-shift jet independence

- **ID:** `prime-power-dirichlet-complex-jet-independence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — `[PROVED HERE] [UNCONDITIONAL] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** An ordinary Dirichlet series with no constant term, supported on prime powers,
  and with nonzero coefficients at all but finitely many primes has a differentially algebraically
  independent family of all complex translates.  More strongly, every finite family of arbitrary
  complex translates together with arbitrary derivative jets is algebraically independent over
  Nagoshi's small-growth meromorphic field `F_s`.

## General theorem

Let

`F(s)=sum_(n>=2) a_n n^(-s)`

have finite abscissa of absolute convergence.  Assume:

1. `a_n=0` unless `n=p^r` is a prime power;
2. `a_p!=0` for all but finitely many primes `p`.

Let `F_s` denote the field of meromorphic functions `phi` with Nevanlinna characteristic
`T(r,phi)=o(r)`.  For arbitrary distinct complex shifts `h_1,...,h_m` and arbitrary nonnegative
integers `nu_1,...,nu_m`, define the finite jet family

`Y_(j,k)(s)=D^kF(s+h_j)`, `1<=j<=m`, `0<=k<=nu_j`.       (1)

Then the functions in (1) are algebraically independent over `F_s`.

Equivalently, the full complex translation orbit `{F(s+h):h in C}` is differentially
algebraically independent over `F_s`, hence over `C(s)`.

## Prime feature vectors

Let

`M=sum_j(nu_j+1)`

and index `C^M` by the pairs `(j,k)`.  At a prime `p`, the Dirichlet coefficient vector of the jet
family is

`v(p)_(j,k)=a_p(-log p)^k p^(-h_j)`.                       (2)

### Tail-span lemma `[PROVED HERE]`

For every finite set of excluded primes `P_0`, the vectors

`{v(p):p prime, p notin P_0}`

span `C^M`.

Suppose a nonzero linear functional `c=(c_(j,k))` annihilated a cofinite prime tail.  Since `a_p`
is nonzero there, this would give

`E(log p)=0`

for all sufficiently large primes, where

`E(x)=sum_(j,k)c_(j,k)(-x)^k exp(-h_jx)`.                  (3)

Distinct `h_j` make the polynomial-coefficient exponential polynomial (3) nonzero.  It is entire
of exponential type up to a polynomial factor.  Jensen's formula gives only `O(R)` zeros in
`|z|<=R`, while the points `log p<=R` number `pi(exp R)`, which grows like `exp(R)/R`.  Therefore
(3) cannot vanish at every sufficiently large prime logarithm.  This proves the tail-span lemma.

## Constant-coefficient algebraic independence `[PROVED HERE]`

Assume a nonzero polynomial relation

`P((Y_(j,k)))=0`                                             (4)

with complex constant coefficients.  Let `L>=1` be the total degree of `P`, and let `P_L` be its
nonzero highest homogeneous part.  Let `B_L` be the symmetric `L`-linear polarization of `P_L`,
normalized so that

`P_L(z)=B_L(z,...,z)`.

Choose `L` distinct sufficiently large primes `p_1,...,p_L`.  Compare in (4) the Dirichlet
coefficient at the squarefree integer

`n=p_1...p_L`.

Every jet series has zero coefficient at `1` and is supported on prime powers.  A product of fewer
than `L` jet factors can involve fewer than `L` distinct prime divisors, so no lower-degree term of
`P` contributes to this coefficient.  A product of exactly `L` factors contributes only by
assigning the `L` distinct primes bijectively to those factors.  Consequently the coefficient is

`L! B_L(v(p_1),...,v(p_L))`.                                (5)

Equation (4) therefore implies

`B_L(v(p_1),...,v(p_L))=0`                                  (6)

for every tuple of distinct sufficiently large primes.

Fix `p_1,...,p_(L-1)`.  As the last prime varies outside this finite set, (6) and the tail-span
lemma show that the last-slot linear functional

`z -> B_L(v(p_1),...,v(p_(L-1)),z)`

vanishes on all of `C^M`.  Now vary `p_(L-1)` over another cofinite tail and apply tail spanning in
that slot.  Iterating backwards through all slots gives `B_L=0`, contradicting `P_L!=0`.

Thus no nonzero constant-coefficient polynomial relation exists.

## Small-growth coefficient upgrade `[PROVED HERE]`

Suppose instead that

`sum_(alpha) phi_alpha(s) Y(s)^alpha=0`,                    (7)

where the finite coefficient family `phi_alpha` lies in `F_s` and is not identically zero.
Every monomial `Y^alpha` is an ordinary Dirichlet series on a common right half-plane.

Chiang--Feng's coefficient-separation lemma says that if finitely many ordinary Dirichlet series
`A_i(s)=sum_n a_i(n)n^(-s)` satisfy

`sum_i phi_i(s)A_i(s)=0`, `T(r,phi_i)=o(r)`,

then for every `n`,

`sum_i a_i(n)phi_i(s)=0` identically.                       (8)

Choose a point `S` at which not all `phi_alpha(S)` vanish.  Evaluating (8) at `S` for every `n`
produces the nonzero constant-coefficient relation

`sum_alpha phi_alpha(S)Y(s)^alpha=0`,

contradicting the preceding section.  Hence (7) is impossible and the jet family is algebraically
independent over `F_s`.

## Structural interpretation

The theorem uses two independent constraints:

1. **prime-power support** turns the coefficient at a squarefree product of `L` primes into the
   exact polarization of the highest-degree relation, with all lower degrees absent;
2. **prime-feature tail span** prevents a nonzero exponential-polynomial filter from annihilating
   a cofinite set of prime features.

Together they promote linear prime exposure to full nonlinear differential-algebraic independence.
This is not a value-density or universality argument and does not require the shifts to be real.

## Completed xi source specialization `[PROVED HERE]`

The exposed completed-logarithmic source

`F_xi(s)=sum_(n>=2)Lambda(n)(1-n^(-2))n^(-s)`              (9)

is supported on prime powers.  At `p^r` its coefficient is

`log(p)(1-p^(-2r))`,

which is nonzero for every prime and every `r>=1`.  Therefore every finite family

`D^kF_xi(s+h_j)`, `h_j in C`,

is algebraically independent over `F_s`.

The formalized identity

`(T_2-1)(xi'/xi)-r=F_xi`,

with rational `r`, lets the atomic-increment primitive theorem apply with the full complex
translation group.  Hence:

**Completed-xi complex-orbit theorem.** Every finite family of distinct complex translates

`(xi'/xi)(s+h_1),...,(xi'/xi)(s+h_m)`

is differentially algebraically independent over `F_s`.  The same is true for the translates
`xi(s+h_j)` themselves, because each logarithmic derivative belongs to the differential field
generated by its corresponding nonzero translate of `xi`.

Thus neither `xi'/xi` nor `xi` satisfies any nontrivial algebraic differential-difference equation
involving finitely many arbitrary complex shifts.

## Exact RH-route consequences

The completed-xi theorem excludes every concrete implementation whose decisive step closes the
actual completed carrier into a finite algebraic differential state system built from finitely many
complex shifts.  It allows nonlinear equations, arbitrary finite derivative orders, and nonlattice
complex shifts.  This covers that exact finite-state pattern inside Li/Keiper, Hilbert--Polya,
Connes, de Branges/canonical-system, explicit-formula/Weil, and Nyman--Beurling proposals.

It does not exclude any full RH-equivalent or infinite-dimensional route.  A route remains live if
it retains unbounded fresh prime/divisor information rather than asserting a finite
differential-difference closure of the completed carrier.

## Attack as false

1. **General class `D` is insufficient for this proof.** Class `D` only asks that infinitely many
   primes divide supported indices.  Squarefree polarization requires the stronger prime-power
   support hypothesis.
2. **Nonzero coefficients at infinitely many primes are insufficient.** Tail spanning uses a
   cofinite prime set.  A thinner prime set would require a separate sampling theorem.
3. **Repeated shifts must be merged.** If two `h_j` coincide, their polynomial jet blocks combine;
   the theorem is stated after taking distinct shifts.
4. **The field `F_s` matters only in the last step.** Constant algebraic independence follows
   without Nevanlinna theory; variable small-growth coefficients use Chiang--Feng's separation
   lemma.
5. **No complex universality is claimed.** The proof is coefficient-theoretic and does not extend
   Voronin density to large complex shifts.

## Candidate competition

1. Linear complex-shift HT from exponential-polynomial sampling — proved bridge, strictly weaker.
2. Real-shift nonlinear independence from Nagoshi — known parent scope.
3. Arbitrary complex algebraic shift independence of `zeta` without derivatives — Chiang--Feng.
4. Prime-power arbitrary-complex shift-and-derivative algebraic independence — theorem here.
5. Completed `xi'/xi` and `xi` arbitrary-complex differential orbit independence — consequence.

## Novelty and significance gate

### Significance `[PASS AS A ROUTE BOUNDARY]`

The theorem upgrades linear HT to the full nonlinear differential matroid and removes the real-shift
restriction.  Its completed-xi consequence excludes every finite algebraic
differential-difference state law with arbitrary complex shifts, the broadest exact finite-handle
no-go obtained in this lane.

### Novelty `[FAIL]`

- Nagoshi proves shift-and-derivative independence for real shifts of class-`D` series.
- Chiang--Feng proves arbitrary-complex algebraic shift independence for `zeta`, without
  derivatives, using Euler-product coefficients and an exponential-polynomial prime lemma.
- No exact primary theorem was found for arbitrary complex shift-and-derivative jets of a
  prime-power-supported Dirichlet series or for the completed xi logarithmic derivative.

Nevertheless, the parent-theory test fails.  Chiang--Feng already isolate highest-degree monomials
at squarefree products of distinct primes and repeatedly use the exponential-polynomial prime
lemma to recover all monomial coordinates.  Replacing their prime feature `p^(-h_j)` by the jet
feature `(-log p)^k p^(-h_j)` changes only the same exponential-polynomial lemma from constant to
polynomial coefficients; Jensen's `O(R)` zero count is unchanged.  The polarization notation
compresses their coefficient argument but introduces no new scientific mechanism.  Extending the
same proof from the zeta local feature to an arbitrary prime-power-supported coefficient sequence
with cofinite nonzero prime coefficients is direct.  The exact statement is useful and apparently
unprinted, but it is a routine parent corollary and therefore a bridge.

## Formalization status

`PrimeShiftJetIndependence.lean` now proves the analytic prime-feature tail-span theorem from the
exponential-type zero count, the squarefree common-layer polarization theorem, and differential
independence of every finite family of distinct complex translates of a general prime-power source
over `ℂ` and over the genuine upper-end rational-coordinate field.

`PrimePowerDirichletComplexJetIndependence.lean` records the card's literal heterogeneous jet
shape: each shift has an arbitrary independent derivative cutoff.  It proves this for general
finite-abscissa prime-power sources and specializes it to the actual filtered von Mangoldt carrier
exposed by the completed-Xi `+2` increment.  Direct check, targeted leaf build, and axiom audits
pass; audits use only `propext`, `Classical.choice`, and `Quot.sound`.

The card remains at Stage 2.  Exact completion still requires formalizing Chiang--Feng coefficient
separation for Nagoshi's small-growth meromorphic field `F_s`, then transferring the source-family
result through the completed logarithmic-derivative increment to the full translate families of
`xi'/xi` and `xi`.  The present theorem is unconditional but over `ℂ(s)`, not the card's stronger
coefficient field; that distinction is not erased by the finite polarization shell.

## Gates

- [x] Tail-span lemma proved for arbitrary complex shifts and derivative blocks.
- [x] Squarefree top-degree coefficient extraction proved.
- [x] Polarization argument proves constant algebraic independence.
- [x] Chiang--Feng lemma upgrades coefficients to `F_s`.
- [x] Completed xi source satisfies every hypothesis.
- [x] Atomic-increment transfer gives full complex orbit independence of `xi'/xi` and `xi`.
- [x] Exact finite-state route scope separated from full RH-equivalent routes.
- [x] Audit Ostrowski/Postnikov scope: the classical algebraic difference--differential theorem is
  formulated for real shifts; it does not supply the complex statement directly.
- [x] Audit Chiang--Feng's proof mechanism: its squarefree coefficient argument extends routinely
  to polynomial-exponential jet features and prime-power sources.
- [x] Complete the internal paper-proof audit and move to stage 2.
- [x] Classify into `not_new_scientific_knowledge` under the routine-parent gate.
- [ ] Formalize the complete theorem before any move to stage 3.

## Primary parents under audit

1. Y.-M. Chiang and S.-J. Feng, *Difference independence of the Riemann zeta function*, Acta
   Arith. 125 (2006), 317--329, arXiv:math/0610479.
2. H. Nagoshi, *Hypertranscendence of L-functions for GL_m(A_Q)*, Bull. Aust. Math. Soc. 93
   (2016), 388--399.
3. A. Ostrowski, *Uber Dirichletsche Reihen und algebraische Differentialgleichungen* (1920).
4. A. G. Postnikov, *On the differential independence of Dirichlet series* (1949) and
   *Generalization of one of the Hilbert problems* (1956).
5. B. Ya. Levin, *Distribution of Zeros of Entire Functions* (1980 English edition), for
   exponential-type zero counting.

## Log

- 2026-07-11 -- Derived after separating Nagoshi's real-shift derivative theorem from
  Chiang--Feng's arbitrary-complex zeta difference theorem.  Prime-power support isolates the top
  homogeneous relation on squarefree coefficients; prime-feature tail span kills its polarization.
  Applied the result to the formally exposed completed-xi source and obtained full complex
  differential-orbit independence of `xi'/xi` and `xi`.
- 2026-07-11 -- Internal proof audit closed every analytic and algebraic step.  Primary comparison
  confirms that Ostrowski/Reich/Nagoshi restrict the difference--differential theorem to real
  shifts, while Chiang--Feng treats arbitrary complex zeta shifts without derivative jets.  Moved
  the unconditional paper theorem to stage 2 `needs-audit`; novelty classification remains open.
- 2026-07-11 -- Severe parent-theory audit failed novelty.  Chiang--Feng's squarefree coefficient
  proof already contains the mechanism; polynomial-exponential derivative features and general
  prime-power coefficients are a direct extension.  Retained the theorem as the strongest proved
  nonlinear complex-shift bridge and moved it to `not_new_scientific_knowledge`.
