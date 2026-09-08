# CCM-FU: uniform transport of actual successor envelopes

- **Stage:** 3-formalized; exact-file and new-declaration axiom checks passed, Lake packaging pending.
- **Parent:** [exact successor extension](../1-in-progress/ccm-fu-exact-successor-extension.md).
- **Closed:** Complete copied-field mass, polynomial quotient energy and gain bounds, full successor-envelope transport, arbitrary finite-batch transport, sharper original diagonal, and an explicit prime threshold for failed extensions with quadratic reserve.
- **Open:** Source production and renewal of reserve, extension near zero reserve, exhaustive compatible selection, the uniform signed Abel bound, and RH.

## Uniform source statements

Let Q_P be the literal retained energy at cutoff M,
B=Q_empty, Psi(P)=max(Q_P, all available immediate successor energies),
and L_p=floor(M/p). For every processed finite set P and every active
unprocessed prime p, Lean proves

`sum_R |F_P(R+p)| <= (3/5)sqrt(M)L_p`,

`J_p=sum_R F_P(R+p)^2 <= (9/25)M L_p^2`,

`|Q_(P+p)-Q_P| <= (6/5)L_p sqrt(M Q_P)`,

`Psi(P+p)<=Psi(P)+(6/5)L_p sqrt(M Psi(P))`.

Every p-free source label R occurs in these sums. No sign, processed-size,
current-energy bound, or fixed quotient-depth hypothesis is assumed.
The mass and child-energy bounds remain true when p is already processed.

The previous small-core estimate can be smaller when the processed quotient
core is sparse. The new estimate complements it by replacing the worst-case
exponential quotient factor with a polynomial bound even at growing depths.
It retains all overlapping labels.

The same comparison gives

`sqrt(Psi(P+p))<=sqrt(Psi(P))+(3/5)sqrt(M)L_p`.

For every finite set T of active primes, whether or not some are already in P,

`sqrt(Psi(P union T))<=sqrt(Psi(P))+(3/5)sqrt(M) sum_(p in T)L_p`.

Applying this theorem to each subset of T bounds every prefix of every
ordering by the total displayed source cost. The cost is explicit and
additive; it is not claimed to be bounded as all source primes are consumed.

The complete original diagonal also has the sharper ceiling

`B<=(9/25)M^2`.

Finally, if delta>0 and Psi(P)+delta*M^2<=B, every available prime p whose
successor exceeds B satisfies

`delta*p < (18/25)sqrt(M)`.

Equivalently, any available prime above that threshold preserves admission.
This is a source-derived sufficient rule with an explicit reserve scale.
It does not assert that a qualifying prime remains or that the reserve exists.

## Dependency-closed paper proof

For any finite indexed coefficients, grouping by disjoint labels cannot
increase their total absolute mass. Apply the triangle inequality inside
each fibre, exchange the two finite sums, and note that each original
coefficient appears at most once.

Every p-containing fibre consists only of original channels with indices
n divisible by p. Prime-factor membership proves this directly, without any
assumption on the other processed labels. Insert-p labels are injective on
p-free labels, so grouping all of them gives

`sum_R |F_P(R+p)|<=sum_(1<=n<=M, p divides n)|C_n(M)|`.

Reindex n=p*d. There are floor(M/p) terms, including the harmless zero
terminal channel when p divides M. The already proved unsigned ceiling and
|mu(n)|<=1 give |C_n(M)|<=(3/5)sqrt(M). This proves the complete mass bound.
For nonnegative numbers, sum of squares is at most the square of their sum;
therefore J_p<=(9/25)M L_p^2.

The exact actual-source merger identity is

`Q_(P+p)-Q_P=2 sum_R F_P(R)F_P(R+p)`.

The p-free parent square sum is at most Q_P. Cauchy gives the squared gain
bound (36/25)M L_p^2 Q_P and then its absolute-value form above. No mixed
term or intermediate sign defect is discarded.

For the envelope, Q_(P+p)<=Psi(P) by definition. If q is available after p,
then q was available at P and p remains available at P+q. Apply the same
source gain theorem at P+q, where Q_(P+q)<=Psi(P), and use monotonicity of
the square root. This bounds every Q_(P+p+q) simultaneously. Taking the
finite maximum proves the full envelope inequality, including all overlaps.

Put c=(3/5)sqrt(M)L_p. The resulting bound is at most
`Psi(P)+2c sqrt(Psi(P))+c^2=(sqrt(Psi(P))+c)^2`.
Taking nonnegative roots proves the additive one-prime cost. Induction over
T gives the batch theorem; an already processed prime changes no state and
has a nonnegative charged cost.

For the original diagonal, the exact empty-state identity is
`B=sum_(n=1..M) C_n(M)^2`. Bound each term by (9/25)M and count M terms.
This improves the earlier 722M^2 ceiling through the newer channel estimate.

Multiplying the envelope increment by p and using p*floor(M/p)<=M gives

`p*(Psi(P+p)-Psi(P))<=(6/5)M sqrt(M Psi(P))`.

Under the stated reserve, Psi(P)<=B<=(9/25)M^2, so the right side is at
most (18/25)M^2 sqrt(M). A failed successor has increment greater than
delta*M^2. Cancel positive M^2 to obtain the strict prime threshold.

## Remaining arithmetic obstacle

Positive reserve localizes possible failures to a square-root prime range
with explicit dependence on the reserve fraction. As that fraction shrinks,
the range grows; at zero reserve this theorem gives no selection rule.
A schedule still needs source control of those smaller primes and enough
reserve after repeated operations. The additive batch cost cannot be reset
without proving fresh energy release. Neither the exact extension candidate
nor the least-energy candidate is closed by this result.

A bounded remainder after subtracting the unsigned square-root leading term
is not assumed. The existing exact source expansion retains a moving terminal
modular residue. The proof here uses the established amplitude bound directly.
No numerical computation was needed or run.

## Lean surface and audit

The module is
[MobiusDivisorUniformSuccessorTransport](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorUniformSuccessorTransport.lean).
Its ten public theorems, all in namespace RHTower, are:

- `sum_abs_mobiusDivisorPrimeFibre_le_quotient`.
- `sum_mobiusDivisorPrimeFibre_sq_le_quotient`.
- `sq_mobiusDivisorSelectionEnergy_insert_le_quotient`.
- `abs_mobiusDivisorSelectionEnergy_insert_le_quotient`.
- `mobiusDivisorSuccessorEnvelope_insert_le_quotient`.
- `sqrt_mobiusDivisorSuccessorEnvelope_insert_le_quotient`.
- `sqrt_mobiusDivisorSuccessorEnvelope_union_le_quotient_sum`.
- `mul_mobiusDivisorSuccessorEnvelope_insert_sub_le`.
- `mobiusDivisorSelectionEnergy_empty_le_nine_twentyFifths_sq`.
- `mobiusDivisorSuccessorEnvelope_failure_prime_bound`.

The complete scratch file and installed exact file passed `lake env lean`
without warnings; only the new leaf olean was emitted. One external scratch
audit checked these ten new declarations once: only `propext`,
`Classical.choice`, and `Quot.sound`. No old declaration was re-audited.
The new module is wired into RHTower; no umbrella build ran.
Targeted Lake packaging remains pending rather than retriggering the known
unrelated prerequisite rebuild. These checks do not claim a successful
`lake build` audit or completion of the RH goal.

Generated corpus indexes include the new module. Formal lint passed with
existing size warnings after a concurrent module's temporary proof debt
and missing import were resolved by its owner. No unrelated source was
edited here. Own whitespace and documentation links passed checks; owned
scratch files were removed and no owned Lean process remained. The frontier
map was kept read-only.
