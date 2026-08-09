# Competitive work envelope, cycle birth, and scalar-integrability rigidity law

- **ID:** ULF-DDE-2A
- **Stage:** 2-fully-proven
- **Type:** MECHANISM THEOREM / COMPOSITION LAW
- **Source:** source-revealed work integrability programme
- **Statement:** Conjunctively combining two exact scalar work laws by their pointwise maximum is
  scalar-integrable only when the parent laws are gauge-equivalent; every genuine disagreement
  creates a positive two-step work cycle. Pointwise minimum remains scalar-integrable.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT] [ROUTE-INDEPENDENT]
  [PARENT: DIFFERENCE CONSTRAINTS / CYCLIC MONOTONICITY] [LEAN-PROVED] [NOT RH]

## 1. Setup

Let `I` be any type of constitutive states. A scalar action is a function

\[
 A:I\to\mathbb R.
\]

Its exact directed work law is

\[
 dA(i,j)=A(j)-A(i).
\tag{1}
\]

For two exact laws `dA,dB`, define two parallel composition mechanisms:

\[
 \omega_\wedge(i,j)=\max\{dA(i,j),dB(i,j)\},
\tag{2}
\]

\[
 \omega_\vee(i,j)=\min\{dA(i,j),dB(i,j)\}.
\tag{3}
\]

Equation `(2)` is conjunctive: a successor action must meet both lower work requirements.
Equation `(3)` is permissive: meeting either requirement is enough.

A directed work law `omega` is scalar-integrable when some `H:I->R` satisfies

\[
 \omega(i,j)\le H(j)-H(i)
 \qquad(i,j\in I).
\tag{4}
\]

No topology, metric, route, or endpoint is part of these definitions.

## 2. Exact two-cycle identity

### Theorem 2.1 -- competitive two-cycle law

For every `i,j in I`,

\[
 \boxed{
 \omega_\wedge(i,j)+\omega_\wedge(j,i)
 =\left|(A-B)(j)-(A-B)(i)\right|.}
\tag{5}
\]

### Proof

Put

\[
 x=dA(i,j),\qquad y=dB(i,j).
\]

Then `dA(j,i)=-x` and `dB(j,i)=-y`. Therefore

\[
 \begin{aligned}
 \omega_\wedge(i,j)+\omega_\wedge(j,i)
 &=\max(x,y)+\max(-x,-y)\\
 &=\max(x,y)-\min(x,y)\\
 &=|x-y|.
 \end{aligned}
\]

Finally

\[
 x-y=(A-B)(j)-(A-B)(i).
\]

This proves `(5)`. QED.

## 3. Scalar-integrability rigidity

### Theorem 3.1 -- conjunction is integrable only in one gauge class

The following are equivalent:

1. `omega_wedge` is scalar-integrable;
2. `dA(i,j)=dB(i,j)` for every `i,j`;
3. after choosing any base state `b`,
   \[
   A(i)-B(i)=A(b)-B(b)
   \qquad(i\in I).
   \tag{6}
   \]

When these conditions hold,

\[
 \omega_\wedge=dA=dB,
\]

so either parent action is a scalar realization.

### Proof

Assume `(4)` for `omega_wedge`. Applying it to `i->j` and `j->i`, then adding, gives

\[
 \omega_\wedge(i,j)+\omega_\wedge(j,i)
 \le [H(j)-H(i)]+[H(i)-H(j)]=0.
\tag{7}
\]

By `(5)`, the left side is nonnegative. It must vanish, so

\[
 dA(i,j)=dB(i,j)
\]

for every pair. Taking `i=b` gives `(6)`. Conversely `(6)` makes all increments equal, so the
maximum in `(2)` is simply `dA`, which is realized by `A`. QED.

### Corollary 3.2 -- minimal history-birth witness

If one pair `i,j` has

\[
 dA(i,j)\ne dB(i,j),
\]

then its two-step history `i->j->i` has strictly positive conjunctive work:

\[
 \boxed{
 \omega_\wedge(i,j)+\omega_\wedge(j,i)>0.}
\tag{8}
\]

Hence no scalar renormalization and no alternative scalar action can integrate the combined law.
The obstruction is already visible on a two-cycle; long histories are unnecessary.

### Theorem 3.3 -- no strict scalar-integrable strengthening

The competitive theorem is a special case of a stronger order law. Let `omega` be any directed
work law satisfying

\[
 dA(i,j)\le\omega(i,j)
 \qquad(i,j\in I).
\tag{8a}
\]

Then

\[
 \boxed{
 \omega\text{ is scalar-integrable}
 \Longleftrightarrow
 \omega=dA.}
\tag{8b}
\]

Indeed, if `omega<=dH` for another scalar action `H`, then `dA<=dH`. Applying this inequality to
`j->i` and negating gives `dH(i,j)<=dA(i,j)`. Hence `dA=dH`, and `(8a)` sandwiches `omega` between
equal endpoints. Conversely `dA` is integrated by `A`.

Thus exact directed work laws are maximal elements among scalar-integrable lower-bound laws. Any
strict mandatory strengthening creates non-scalar history, independently of how that strengthening
was generated.

## 4. Asymmetric survivor

### Theorem 4.1 -- permissive composition remains integrable

For every `A,B`, the disjunctive law `omega_vee` is scalar-integrable. Indeed,

\[
 \omega_\vee(i,j)\le dA(i,j)=A(j)-A(i),
\]

so `A` is a scalar realization. The same argument uses `B`.

Thus conjunction and disjunction of exact laws behave asymmetrically:

\[
 \boxed{
 \begin{array}{c|c}
 \text{parallel operation}&\text{scalar integrability}\\
 \hline
 \min(dA,dB)&\text{always survives}\\
 \max(dA,dB)&\text{survives iff }A-B\text{ is constant.}
 \end{array}}
\tag{9}
\]

## 5. Constitutive interpretation

This theorem supplies a mechanism absent from optimizer-first exactification:

1. **Exact parent laws need not compose exactly.** Each parent is conservative, yet their
   conjunctive envelope can be nonconservative.
2. **Selection can create history.** Edgewise winner selection erases which parent supplied each
   work requirement. Switching winners around a two-cycle produces the positive residue `(5)`.
3. **Gauge is classified exactly.** Addition of constants to `A` or `B` changes no increment. The
   only harmless competition is therefore competition between the same gauge class.
4. **Irreversibility is not inserted.** Positive cyclic work is generated by composition of two
   reversible exact laws, not declared as a new primitive.
5. **The response nerve must retain branch history.** An observer recording only the maximum
   forgets the active parent label; any exact lift must retain enough history to distinguish the
   competing branches.
6. **Exact reversible work is order-maximal.** The issue is not peculiar to `max`: no strict
   pointwise strengthening of an exact directed law can remain scalar-integrable.

The last sentence is a design consequence, not a minimal-memory theorem.

## 6. Hostile conjecture loops

### Loop A -- exact laws are closed under pointwise conjunction

**False.** Equation `(5)` gives a positive two-cycle whenever the parent increments disagree.

**Positive survivor.** Closure holds exactly inside one additive-gauge class.

### Loop B -- changing scalar normalization repairs the cycle

**False.** Constants cancel from every increment. The defect `(5)` is gauge-invariant.

**Positive survivor.** A successful repair must retain branch/history data or weaken the
conjunctive rule; it cannot be another scalar offset.

### Loop C -- every envelope destroys scalar integrability

**False.** The pointwise minimum is always dominated by each exact parent work law.

**Positive survivor.** The theorem classifies an exact asymmetry between permissive and mandatory
parallel composition.

### Loop D -- long or cofinal histories are needed to expose competition

**False.** One disagreeing edge and its reverse already give a strict positive cycle.

**Positive survivor.** Two-cycle tests are a complete local gate for conjunctive composition of
two exact scalar laws.

## 7. Parent boundary and scope

Difference constraints, conservative edge weights, revealed preference, and cyclic monotonicity
are classical parents. This card makes no priority claim. Its role in Constitutive Process
Mathematics is to provide an exact higher-slot composition law: mandatory competition between
individually scalar-exact processes creates a history sector unless they were the same law up to
gauge.

The theorem does not construct source responses, choose which composition is physically legal,
prove a minimal dilation theorem, handle infinite suprema, or imply RH. Every application must
derive `A`, `B`, and the conjunctive rule before observing the desired outcome.

## 8. Field prediction

When two independently valid repair doctrines are combined by enforcing the stronger directed
requirement at every intervention, exactly one of two things happens:

- their work responses agree up to gauge, so no new law was added; or
- a positive two-cycle is born, so the combined doctrine necessarily needs directed history or a
  non-scalar constitutive state.

This is falsifiable before any route specialization.
