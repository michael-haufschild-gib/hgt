# Representation, operational novelty, four chambers, and diagonal inertness law

- **ID:** ULF-REE-1
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Statement:** Representability and operational novelty are logically independent; operational
  novelty is exactly fibre splitting, the anti-diagonal criterion is diagonal variation inside a
  row-profile fibre, and every finite strict-order diagonal stage is representationally new but
  operationally inert.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [FOUR-CHAMBER CLASSIFICATION] [DIAGONAL FEEDBACK NO-GO]
  [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [NOT RH]

## 1. Two independent notions of birth

Let `X` be a set and let

\[
 E:X\times X\longrightarrow\{0,1\}
\]

be a Boolean self-evaluator. Its complete row-profile reporter is

\[
 R_E(x)=E(x,-)\in\{0,1\}^X.
\tag{REE.1}
\]

For a Boolean challenge `c:X->\{0,1\}`, say:

- `c` is **represented** when `c=E(a,-)` for some `a in X`;
- `c` is **operationally inert** when it descends through `R_E`, equivalently
  `R_E(x)=R_E(y)` implies `c(x)=c(y)`;
- `c` is **operationally effective** otherwise.

Equivalently, effectiveness means that adjoining `c` to `R_E` excludes an intervention
`u:X->X` which previously preserved every row profile.

## 2. Exact exchange theorem

### Theorem 2.1 -- fibre-splitting criterion

For every evaluator `E` and challenge `c`, the following are equivalent:

1. `c` is operationally effective;
2. there exist `x,y in X` such that

   \[
   E(x,z)=E(y,z)\quad\text{for every }z\in X,
   \qquad c(x)\ne c(y);
   \tag{REE.2}
   \]

3. there is `u:X->X` preserving `R_E` but not the paired reporter `(R_E,c)`.

When `(REE.2)` holds, `u` may be chosen to overwrite only `x`, sending it to `y` and fixing every
other state.

### Proof

Conditions 1 and 2 are the definition of failure of fibrewise descent. If `(REE.2)` holds, define

\[
 u(z)=\begin{cases}y,&z=x,\\z,&z\ne x.\end{cases}
\]

The changed point remains in the same `R_E`-fibre, so `R_Eu=R_E`; but `c(ux)=c(y)\ne c(x)`, so
the pair is not preserved. Conversely, if some `u` preserves `R_E` but not `(R_E,c)`, choose `x`
with `c(ux)\ne c(x)` and put `y=ux`. Then `R_E(x)=R_E(y)` and `(REE.2)` holds. QED.

## 3. Anti-diagonal classification

Define the complemented diagonal

\[
 \delta_E(x)=1-E(x,x).
\tag{REE.3}
\]

### Theorem 3.1 -- diagonal effectiveness criterion

The anti-diagonal is operationally effective exactly when

\[
 \boxed{
 \exists x,y:\ E(x,-)=E(y,-)\ \text{and}\ E(x,x)\ne E(y,y).}
\tag{REE.4}
\]

It is never represented by an existing row.

### Proof

The nonrepresentation statement is the diagonal contradiction: if `E(a,-)=delta_E`, evaluate at
`a`. For effectiveness, apply Theorem 2.1 to `c=delta_E`. Boolean complementation is injective, so
`delta_E(x) ne delta_E(y)` exactly when `E(x,x) ne E(y,y)`. QED.

### Corollary 3.2 -- faithful-profile inertness

If `R_E` is injective, every challenge is operationally inert. In particular the anti-diagonal can
still be unrepresented while failing to change any current invisible intervention.

### Proof

Equal row profiles imply equal states, after which every challenge has equal values. QED.

## 4. Four sharp two-state chambers

Let `B={0,1}`.

### Projection evaluator

Put

\[
 P(x,y)=y.
\tag{REE.5}
\]

Both rows are the identity function, so `R_P` is constant.

- The challenge `c(y)=y` is represented by every row and is operationally effective.
- The anti-diagonal `delta_P(y)=1-y` is unrepresented and operationally effective.

Both split the unique two-point row-profile fibre.

### Strict-order evaluator

Put

\[
 L(x,y)=1\iff y<x.
\tag{REE.6}
\]

Its two rows are distinct, so `R_L` is injective.

- The challenge `c=L(0,-)` is represented and operationally inert.
- The anti-diagonal is unrepresented and operationally inert.

Therefore every combination of represented/unrepresented and effective/inert occurs on a
two-state evaluator. Neither axis determines the other.

## 5. The diagonal-genesis tower is semantically inert at each finite stage

For `n>=0`, let

\[
 E_n(i,j)=1\iff j<i
\]

on `Fin n`.

### Theorem 5.1 -- unrepresented/inert tower

For every `n`:

1. `R_(E_n)` is injective;
2. `delta_(E_n)` is not any row;
3. `delta_(E_n)` is nevertheless determined by `R_(E_n)`;
4. adjoining it does not contract the current invisible-intervention doctrine.

### Proof

If `i<j`, evaluate the two rows at column `i`: row `i` has value zero while row `j` has value one.
The case `j<i` is symmetric, so equal rows force `i=j`. Clause 1 follows. Clause 2 is the diagonal
theorem. Clauses 3--4 follow from Corollary 3.2 and Theorem 2.1. QED.

## 6. Mechanism consequences

1. **Representation is not law genesis.** A challenge may force carrier growth without changing
   current legal transformations.
2. **Operational genesis need not add a representer.** An already represented row can split a
   row-profile fibre.
3. **Source-normality is insufficient.** Canonical production still needs a semantic-transport
   certificate.
4. **Diagonal succession is not yet reflexive feedback.** It creates absent rows, but its finite
   strict-order tower has already faithful row semantics.
5. **Immediate inertness does not imply permanent inertness.** A prospective claim requires a
   specified future history and a survival proof; it cannot be inferred from representability.

## 7. Hostile boundaries and parent collision

The fibre-splitting theorem is an elementary instance of predicate refinement, observational
equivalence, and the operation--relation Galois criterion already certified in ULF-EST-1. The
anti-diagonal nonrepresentation theorem is Lawvere/Cantor. Therefore the package is a `[BRIDGE]`,
not a new parent theorem.

Its field leverage is corrective: two previously certified formation mechanisms occupy independent
axes. Any future ERM claim must prove both representer birth and semantic transport, and must name
which old-invisible intervention becomes illegal. No RH route, endpoint, topology, probability,
positivity, or analytic premise enters.

## 8. Lean target

Lean module
`GaloisForLFunctions.HTGeometry.ConstitutiveRepresentationExecutionExchange` certifies:

1. row-profile reporter and representation/effectiveness definitions;
2. exact fibre-splitting and anti-diagonal criteria;
3. faithful-profile inertness;
4. all four two-state chambers;
5. injectivity and inertness of every finite strict-order stage;
6. one unconditional capstone and Universal Law Field umbrella import.

Direct elaboration passes. The leaf build completes 8,666 jobs and the Universal Law Field umbrella
build completes 11,582 jobs. Axiom prints on both exchange criteria, the four-chamber theorem, the
finite diagonal-stage law, and the closed capstone report only `propext`, `Classical.choice`, and
`Quot.sound`. No computation, `sorry`, `admit`, project axiom, `opaque`, or `unsafe` declaration is
used.
