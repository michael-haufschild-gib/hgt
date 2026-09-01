# Critical-wall nilpotent monodromy, reflection energy, and cofinal memory law

## Status

- **Label:** ULF-NIMM-1
- **Paper status:** fully proved
- **Lean status:** formalized in `RHTower.RouteRNilpotentMonodromy`
- **Scope:** exact fusion of derived-selection monodromy, Route-R critical-wall corona,
  functional-equation reflection, positive energy, and cofinal shift
- **RH claim:** none

## 1. Higher-law interpretation

Corpus does not present off-wall displacement as an ordinary scalar surviving every completion.
It presents a first-order class which survives modulo summable tails, whose square is summable,
whose orientation reverses under functional equation, and whose cofinal prime-tail history is
stationary.  Correct common mechanism is therefore **nonreduced infinitesimal monodromy**:

\[
  h(a)^2=0,\qquad q(a)=1+h(a).
\]

Here `h(a)` is not invented data.  It is the existing Route-R critical-wall class in the
summable Hadamard corona.  This makes three previously separate shadows literal images of one law:

1. functional equation sends monodromy to its inverse;
2. positive reflected energy sees only the square of wall displacement and therefore vanishes;
3. cofinal shift preserves the unsquared oriented displacement.

Thus positivity is a phase quotient in a precise algebraic sense: on a square-zero thickening it
forgets all first-order wall information.  This is explanatory geometry, not a selection proof.

## 2. Corpus premises

Let

\[
 A=\ell^\infty(\mathbb N,\mathbb C)/\ell^1(\mathbb N,\mathbb C)
\]

with pointwise multiplication, in the exact bounded-tail form already constructed in the corpus.
For real grade `a`, write

\[
 h_a=\operatorname{routeRPrimeGammaCriticalWallSummableHadamardClass}(a)\in A.
\]

The existing Lean corpus proves:

\[
\begin{aligned}
 h_a^2&=0,\\
 h_a\ne0&\Longleftrightarrow a\ne0,\\
 h_{-a}&=-h_a,\\
 S(h_a)&=h_a,
\end{aligned}
\tag{NIMM.1}
\]

where `S` is cofinal deletion of one prime-tail coordinate.  It also proves that every ring map
from `A` to a reduced commutative ring kills `h_a`.  Independently, derived-selection geometry
defines

\[
 E(q,v)=q+v-2,\qquad K(q,v)=q-v
\tag{NIMM.2}
\]

for inverse monodromy legs `qv=1`, and proves `qE=(q-1)^2`.

These facts were located before formulation with

```text
scripts/formal_tools.py research
  "square-zero monodromy reflection energy cofinal shift critical wall summable Hadamard corona"
```

The search returns the four statements in `(NIMM.1)`, the constitutive-corona injection, and the
reduced-receiver annihilation theorem.  It does not return their monodromy specialization or the
joint conservation law below.

## 3. Abstract infinitesimal-monodromy law

### Theorem 3.1

Let `R` be a commutative ring and let `h in R` satisfy `h^2=0`.  Put

\[
 q=1+h,\qquad v=1-h.
\]

Then

\[
 qv=vq=1,\qquad E(q,v)=0,\qquad K(q,v)=2h.
\tag{NIMM.3}
\]

Consequently `q` is a unit with inverse `v`, and the Laurent monodromy ring admits a unique
specialization sending its coordinate to this unit.

#### Proof

Commutativity and `h^2=0` give

\[
 (1+h)(1-h)=1-h+h-h^2=1.
\]

The reverse product is identical.  Direct substitution gives

\[
 E=(1+h)+(1-h)-2=0,
 \qquad
 K=(1+h)-(1-h)=2h.
\]

The Laurent specialization is the universal property of `R[q,q^{-1}]`. QED.

### Corollary 3.2 — exact information split

For square-zero wall displacement, the pair

\[
 (E,K)=(0,2h)
\tag{NIMM.4}
\]

is an exact separation of even positive response from odd oriented response.  If multiplication by
`2` is injective, then

\[
 K=0\Longleftrightarrow h=0\Longleftrightarrow q=1.
\tag{NIMM.5}
\]

#### Proof

Equation `(NIMM.4)` is Theorem 3.1.  If `2h=0` and multiplication by `2` is injective, then `h=0`.
The reverse implication is immediate.  Also `1+h=1` exactly when `h=0`. QED.

## 4. Critical-wall specialization

Define in `A`

\[
 q_a=1+h_a,\qquad q_a^{\sigma}=1-h_a.
\tag{NIMM.6}
\]

### Theorem 4.1 — four-organ fusion law

For every real `a`:

\[
\begin{aligned}
 q_aq_a^{\sigma}&=1,
 &q_{-a}&=q_a^{\sigma}=q_a^{-1},\\
 E(q_a,q_a^{\sigma})&=0,
 &K(q_a,q_a^{\sigma})&=2h_a,\\
 S(q_a)&=q_a,
 &S(q_a^{\sigma})&=q_a^{\sigma},\\
 q_a=1&\Longleftrightarrow a=0,
 &K(q_a,q_a^{\sigma})=0&\Longleftrightarrow a=0.
\end{aligned}
\tag{NIMM.7}
\]

Moreover the Laurent specialization `Phi_a` defined by `Phi_a(q)=q_a` satisfies

\[
 \Phi_a(q^{-1})=q_a^{\sigma},\qquad
 \Phi_a(E)=0,\qquad
 \Phi_a(K)=2h_a.
\tag{NIMM.8}
\]

#### Proof

Apply Theorem 3.1 to `h_a` using `(NIMM.1)`.  Reflection follows from
`h_{-a}=-h_a`.  Shift invariance follows because a ring automorphism preserves `1`, negation, and
the already proved equality `S(h_a)=h_a`.  The corona is a complex algebra, so multiplication by
`2` is invertible.  The last two equivalences follow from `(NIMM.1)` and Corollary 3.2.  Finally
`(NIMM.8)` follows from the Laurent specialization and `(NIMM.3)`. QED.

## 5. What this explains

This theorem fuses structurally different organs without replacing any of them by an analogy.

| Organ | Exact shadow of `h_a` |
|---|---|
| Derived-selection geometry | infinitesimal monodromy `q_a=1+h_a` |
| Functional equation | inverse action `q_a -> q_a^{-1}=q_{-a}` |
| Positive/Fitting observer | `E=0` because it starts at second order |
| Odd orientation observer | `K=2h_a`, hence faithful at first order |
| Cofinal recurrence | closed observed state `S(q_a)=q_a` with retained tail memory |
| Reduced completion | annihilates `h_a`, hence cannot certify source vanishing |

This is stronger than saying that positivity “loses sign.”  It computes the lost information:
positive reflection energy is identically zero on the entire first infinitesimal neighbourhood,
while odd curvature reconstructs that neighbourhood up to multiplication by the unit `2`.

## 6. Exact RH closure and remaining gate

For each completed-Xi zero, corpus grade is centered displacement

\[
 a(\rho)=\Re\rho-\tfrac12
\]

up to the already fixed normalization used by the relevant route.  The theorem gives the
pointwise selection chain

\[
 q_{a(\rho)}=1
 \Longleftrightarrow h_{a(\rho)}=0
 \Longleftrightarrow a(\rho)=0
 \Longleftrightarrow \Re\rho=\tfrac12.
\tag{NIMM.9}
\]

Therefore a global theorem proving source monodromy is the identity at every completed-Xi divisor
would close RH immediately.  But `(NIMM.9)` is not that producer: it identifies the exact producer
still missing.

Required law is **source effectivity in the nonreduced category**:

> Construct the arithmetic source action whose induced Laurent specialization is `Phi_a`, then
> prove internally that its first-order monodromy is trivial, while the comparison to `A` remains
> faithful on the square-zero tangent.

Mapping to a reduced target cannot supply this law: corpus already proves every such map kills
`h_a` for all `a`, including off-wall grades.  Any proposed “global formation/properness” theorem
whose conclusion is merely reduced landing is therefore disqualified before proof.  Valid closure
must kill the tangent in the source, not hide it in the receiver.

## 7. Anti-theatre boundary

Proved here:

- one literal class already present in the corpus drives all five shadows;
- functional-equation reflection lifts to actual inversion;
- positive energy is exactly information-neutral on that class;
- odd curvature reconstructs the class;
- recurrence preserves it;
- vanishing is exactly neutral grade.

Not proved here:

- source effectivity;
- identity monodromy at completed-Xi divisors;
- RH.

The next conjecture is not “find another receiver.”  Before any conjecture is stated, corpus search
must locate an arithmetic source action with a faithful square-zero tangent comparison and show
exactly which source law could force its monodromy to be the identity.
