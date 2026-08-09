# Competitive path variation, observer descent, and history-production law

- **ID:** ULF-DDE-2B
- **Stage:** 2-fully-proven
- **Type:** MECHANISM THEOREM / HIGHER-SLOT COMPOSITION LAW
- **Source:** source-revealed work integrability programme
- **Statement:** Mandatory and permissive parallel composition of two scalar-exact work laws are
  the positive and negative variation halves of their relative law. On a closed reversible
  history, mandatory competition produces exactly half the total variation of the relative
  potential. An observer retains this memory exactly when the relative potential descends through
  its attained range.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT] [ROUTE-INDEPENDENT]
  [PARENT: TROPICAL/MAX-PLUS ENVELOPES AND CYCLIC MONOTONICITY] [LEAN TARGET] [NOT RH]

## 1. Setup

Let `I` be a type of constitutive states. Two scalar actions

\[
 A,B:I\to\mathbb R
\]

produce exact directed work laws

\[
 dA(i,j)=A(j)-A(i),\qquad dB(i,j)=B(j)-B(i).
\tag{1}
\]

Their mandatory and permissive parallel compositions are

\[
 \omega_\wedge(i,j)=\max\{dA(i,j),dB(i,j)\},
\tag{2}
\]

\[
 \omega_\vee(i,j)=\min\{dA(i,j),dB(i,j)\}.
\tag{3}
\]

For a finite history

\[
 \gamma=(x_0,x_1,\ldots,x_n),
\]

write

\[
 W_\wedge(\gamma)=\sum_{k=0}^{n-1}\omega_\wedge(x_k,x_{k+1}),
 \qquad
 W_\vee(\gamma)=\sum_{k=0}^{n-1}\omega_\vee(x_k,x_{k+1}).
\tag{4}
\]

Put `D=A-B` and define its path variation

\[
 \operatorname{Var}_\gamma(D)
 =\sum_{k=0}^{n-1}|D(x_{k+1})-D(x_k)|.
\tag{5}
\]

The history is closed when `x_n=x_0`. Empty and one-state histories have zero work and variation.

## 2. Exact path decomposition

### Theorem 2.1 -- competitive path Jordan law

Every finite history satisfies

\[
 \boxed{
 2W_\wedge(\gamma)
 =[A(x_n)-A(x_0)]+[B(x_n)-B(x_0)]
 +\operatorname{Var}_\gamma(A-B).}
\tag{6}
\]

and

\[
 \boxed{
 2W_\vee(\gamma)
 =[A(x_n)-A(x_0)]+[B(x_n)-B(x_0)]
 -\operatorname{Var}_\gamma(A-B).}
\tag{7}
\]

Hence

\[
 \boxed{W_\wedge(\gamma)-W_\vee(\gamma)
 =\operatorname{Var}_\gamma(A-B),}
\tag{8}
\]

while

\[
 W_\wedge(\gamma)+W_\vee(\gamma)
 =[A(x_n)-A(x_0)]+[B(x_n)-B(x_0)].
\tag{9}
\]

### Proof

For real numbers `a,b`,

\[
 2\max(a,b)=a+b+|a-b|,
 \qquad
 2\min(a,b)=a+b-|a-b|.
\tag{10}
\]

Apply `(10)` on each edge with `a=dA(x_k,x_{k+1})` and
`b=dB(x_k,x_{k+1})`. The two exact-work sums telescope:

\[
 \sum_k dA(x_k,x_{k+1})=A(x_n)-A(x_0),
\]

\[
 \sum_k dB(x_k,x_{k+1})=B(x_n)-B(x_0).
\]

The absolute-difference term is

\[
 |dA-dB|
 =|(A-B)(x_{k+1})-(A-B)(x_k)|.
\]

Summing gives `(6)` and `(7)`. Adding and subtracting them gives `(8)` and `(9)`. QED.

## 3. Closed histories

### Corollary 3.1 -- total variation is generated history

If `gamma` is closed, endpoint terms vanish and

\[
 \boxed{W_\wedge(\gamma)=\frac12\operatorname{Var}_\gamma(A-B)\ge0,}
\tag{11}
\]

\[
 \boxed{W_\vee(\gamma)=-\frac12\operatorname{Var}_\gamma(A-B)\le0.}
\tag{12}
\]

Therefore mandatory and permissive parallel composition polarize one relative law into equal and
opposite history sectors.

### Corollary 3.2 -- exact zero criterion

For a closed history,

\[
 W_\wedge(\gamma)=0
 \quad\Longleftrightarrow\quad
 D(x_0)=D(x_1)=\cdots=D(x_n).
\tag{13}
\]

Indeed, a finite sum of nonnegative absolute increments vanishes exactly when every increment
vanishes.

For the two-edge history `(i,j,i)`, `(11)` reduces to

\[
 W_\wedge(i,j,i)=|D(j)-D(i)|,
\tag{14}
\]

recovering ULF-DDE-2A as the minimal case.

### Corollary 3.3 -- subdivision and common-gauge invariance

The closed-history quantity in `(11)` has three exact invariances:

1. adding constants independently to `A` and `B` changes nothing;
2. adding a common potential `C` to both actions changes every edge work by `dC`, whose closed sum
   is zero;
3. subdividing an edge through a state whose relative value lies monotonically between the endpoint
   relative values leaves total variation unchanged.

Arbitrary subdivision can increase variation. Thus history production is presentation-invariant
under gauge and monotone refinement, not under every insertion of states.

## 4. Observer descent

Let

\[
 q:I\to Q
\]

be an observer. Say the relative law descends through the attained range of `q` when a function

\[
 \bar D:\operatorname{range}(q)\to\mathbb R
\]

satisfies

\[
 D=\bar D\circ q
\]

on source states.

### Theorem 4.1 -- memory-descent equivalence

The following are equivalent:

1. `D=A-B` descends through the attained range of `q`;
2. `D` is constant on every observer fibre;
3. every source two-cycle collapsed to one observed state has zero mandatory history:
   \[
   q(i)=q(j)
   \quad\Longrightarrow\quad
   W_\wedge(i,j,i)=0.
   \tag{15}
   \]

### Proof

Factorization through the attained range is equivalent to constancy on observer fibres: one
direction is immediate; in the other, choose any source representative of each attained value and
use fibre constancy to make the definition independent of that choice.

By `(14)`,

\[
 W_\wedge(i,j,i)=|D(j)-D(i)|,
\]

which vanishes exactly when `D(i)=D(j)`. This proves the equivalence. QED.

### Corollary 4.2 -- exact invisible-memory witness

If `D` does not descend through `q`, there exist `i,j` with identical observation but

\[
 W_\wedge(i,j,i)>0.
\tag{16}
\]

The observer sees a stationary two-step history, while the source carries positive mandatory work.
No downstream function of the same observer output can reconstruct that work. Retaining the
relative-law mark `D` repairs this particular loss exactly.

This is a quantitative strengthening of the generic kernel-pair factorization law: the obstruction
is not only nonfactorization but the exact absolute amount erased on each collapsed pair.

## 5. Mechanism interpretation

This theorem isolates one general mechanism.

1. **Parallel selection transduces law disagreement into memory.** The exact output is total
   variation, not an analogy to curvature.
2. **Endpoint work and generated history separate canonically.** Equations `(6)`--`(7)` split a
   path response into a conservative endpoint term and a nonnegative relative-variation term.
3. **Observer loss has an exact local test.** A quotient is adequate precisely when its fibres have
   zero relative variation.
4. **History is composition-generated.** Neither parent law contains cyclic work. The max/min
   operation creates opposite history sectors.
5. **Gauge is not the issue.** The invariant depends only on `A-B` modulo a constant and survives a
   common change of scalar presentation.
6. **The theorem is not a universal explanation of the RH frontier.** It addresses competitive
   selection and observer descent. Singular completion, whole-space coercivity, positive-carrier
   birth, and all-prime cancellation require other mechanism laws.

## 6. Hostile conjecture loops

### Loop A -- closed-cycle history depends on which parent is called first

**False.** Swapping `A,B` replaces `D` by `-D`, leaving total variation unchanged.

**Survivor.** Competitive history is an invariant of the unordered pair of gauge classes.

### Loop B -- endpoint data determine mandatory history

**False.** Closed histories have identical endpoints and can have arbitrary positive variation.

**Survivor.** Endpoint response plus relative-law variation is sufficient and exact by `(6)`.

### Loop C -- every path has half-variation work

**False.** Open paths retain the endpoint terms in `(6)`.

**Survivor.** Half-variation is exactly the closed-history specialization.

### Loop D -- the result extends unchanged to three or more parents

**False as stated.** A family envelope `max_a dA_a` still has nonnegative closed-cycle work and is
scalar-integrable only when all parent increments agree, but no single scalar difference has a
canonical total variation representing every multi-branch switch.

**Survivor.** The correct multi-parent quantity is a tropical support-variation functional. Its
minimal-memory classification remains an open higher-slot problem.

### Loop E -- any subdivision preserves history

**False.** Inserting a relative value outside the interval between adjacent endpoint values
strictly increases variation.

**Survivor.** Monotone subdivision, not arbitrary refinement, is the exact invariant class.

### Loop F -- fibre collision is harmless when endpoints agree observationally

**False.** Equation `(16)` gives positive source memory on an observed stationary loop.

**Survivor.** Relative-law factorization through the observer is necessary and sufficient.

## 7. Parent boundary and scope

Max-plus/min-plus envelopes, difference constraints, total variation, switched Lyapunov functions,
and cyclic monotonicity are classical parents. The elementary identity `(10)` is not claimed as a
new isolated fact. Its role in Constitutive Process Mathematics is the combined mechanism:
parallel law selection produces an exact pathwise Jordan split, whose positive cyclic part is also
the complete obstruction to observer descent of the relative law.

The theorem does not select `A` or `B`, prove that max/min is physically mandatory, derive an
observer from a source, construct a multi-parent minimal dilation, imply hypertranscendence, or
prove RH. It must be validated only after a source independently supplies competing work laws and
legal interventions.

## 8. Field prediction

Whenever two exact source laws are enforced competitively on a reversible finite history, a
complete response record must contain one of two equivalent data:

- the relative potential along the history, modulo a constant; or
- the positive/negative path-variation split.

Any observer collapsing states with unequal relative potential necessarily reports zero motion for
some positive-work source cycle. This prediction is route-independent and falsifiable before any
endpoint specialization.
