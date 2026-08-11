# Polynomial law context production, nested repair, and interaction ancestry law

- **ID:** ULF-DLG-1
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Statement:** A marked site in a polynomial law execution canonically produces a one-hole
  context. Composite failures produce nested contexts whose plugging is local and restorative;
  failure pairs partition exactly by common outer ancestry, which a coarse observer can erase.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN-PROVED]
  [CONTEXT-PRODUCTION LAW] [OBSERVER ANCESTRY NO-GO] [CLASSICAL PARENTS] [NOT RH]

## 1. Setup

A polynomial law signature is a pair

\[
 C=(S_C,P_C),
 \qquad P_C:S_C\to\mathbf{Set},
 \tag{PC.1}
\]

where `S_C` is the type of law shapes and `P_C(s)` is the type of input positions of shape `s`.
Its executions on a value type `X` are

\[
 \operatorname{Ext}_C(X)
 =\coprod_{s\in S_C} X^{P_C(s)}.
 \tag{PC.2}
\]

A one-hole context is

\[
 \partial C(X)
 =\coprod_{s\in S_C}\coprod_{p\in P_C(s)}
   X^{P_C(s)\setminus\{p\}}.
 \tag{PC.3}
\]

Concretely an element is `(s,p,k)`, where `k(q)` is supplied for every `q != p`. Define

\[
 \operatorname{plug}(s,p,k;x)
 =(s,\ q\mapsto \begin{cases}x,&q=p,\\k(q),&q\ne p.\end{cases}).
 \tag{PC.4}
\]

No finiteness, topology, linearity, positivity, or arithmetic hypothesis is used.

## 2. Context-production theorem

### Theorem 2.1 — marked context restoration

Let `e=(s,f)` be an execution and let `p in P_C(s)`. The marked execution produces the canonical
context

\[
 \operatorname{ctx}(e,p)=(s,p,f|_{P_C(s)\setminus\{p\}}).
 \tag{PC.5}
\]

Then

\[
 \boxed{\operatorname{plug}(\operatorname{ctx}(e,p);f(p))=e.}
 \tag{PC.6}
\]

Moreover plugging `x` agrees with `f` at every `q != p` and takes value `x` at `p`.

### Proof

Both executions have shape `s`. At `p`, equation `(PC.4)` gives `f(p)`. Away from `p`, it gives the
restricted value `f(q)`. Function extensionality proves `(PC.6)`. The same case split proves the two
locality statements. QED.

## 3. Composite failure and nested repair

Let `P=(S_P,P_P)` and `Q=(S_Q,P_Q)`. Write a composite execution as

\[
 e=(s,(e_p)_{p\in P_P(s)}),
 \qquad e_p\in\operatorname{Ext}_Q(X).
 \tag{PC.7}
\]

A leaf failure site is a dependent pair

\[
 z=(p,q),
 \qquad p\in P_P(s),\quad q\in P_Q(\operatorname{shape}(e_p)).
 \tag{PC.8}
\]

It canonically exposes:

- the outer context of the `P`-execution at `p`;
- the inner context of the `Q`-execution `e_p` at `q`.

Define nested repair by plugging `x` into the inner context and then plugging the repaired inner
execution into the outer context.

### Theorem 3.1 — nested context chain law

For every composite execution `e` and marked leaf `z=(p,q)`,

\[
 \boxed{
 \operatorname{repair}(e,z;e_p(q))=e.}
 \tag{PC.9}
\]

For every replacement `x` and every outer position `p' != p`,

\[
 \boxed{
 \operatorname{repair}(e,z;x)_{p'}=e_{p'}.
 }
 \tag{PC.10}
\]

### Proof

Theorem 2.1 first restores the inner execution when its original leaf value is plugged. The same
theorem then restores the outer execution when the restored inner execution is plugged. This proves
`(PC.9)`. For `(PC.10)`, the outer plug definition selects the old branch whenever `p' != p`. QED.

The theorem is the smallest literal chain law for failure-generated repair contexts. It does not
choose the replacement `x`.

## 4. Binary interaction ancestry

For two marked composite sites

\[
 z_1=(p_1,q_1),\qquad z_2=(p_2,q_2),
\]

define:

- **same-outer interaction:** `p_1=p_2`;
- **split-outer interaction:** `p_1!=p_2`.

### Theorem 4.1 — exact interaction partition

Every ordered failure pair has exactly one of these two ancestry types:

\[
 (p_1=p_2\ \lor\ p_1\ne p_2)
 \quad\text{and}\quad
 \neg(p_1=p_2\ \land\ p_1\ne p_2).
 \tag{PC.11}
\]

### Proof

Apply excluded middle to equality of the two outer positions. The two alternatives cannot coexist
because the second is the negation of the first. QED.

The elementary logic is load-bearing: the alternatives are not labels attached later. They are
forced by the ancestry map from composite leaf sites to outer sites. Higher finite failure families
should be classified by the partition induced by that map.

## 5. Sharp ancestry-loss countermodel

Take one outer shape with two positions `Fin 2`, and at each position one inner shape with one
position. There are two ordered pairs:

\[
 z_{\mathrm{same}}=((0,*),(0,*)),
 \qquad
 z_{\mathrm{split}}=((0,*),(1,*)).
 \tag{PC.12}
\]

The first is same-outer and the second split-outer. The constant observer to the one-point type,
which forgets all ancestry, sends both pairs to the same value.

### Corollary 5.1 — coarse residual equality does not determine genesis

No datum factoring only through that ancestry-blind observation can decide whether the two failures
generate an inner same-branch challenge or a cross-branch interaction challenge.

### Proof

The observer values are definitionally equal, while `(PC.12)` has opposite outer-equality status.
Any factor through equal observer values assigns the same output to both. QED.

## 6. Mechanism consequences

1. **Failure can generate challenge type.** Once execution syntax and a marked site are source data,
   the one-hole context is canonical; it is not a fitted reporter.
2. **Composition types repair.** A composite leaf cannot be repaired by a flat unidentified
   residual. Its outer/inner plugging order is forced.
3. **Locality is exact.** Nested repair cannot change an unrelated outer branch.
4. **Interaction is ancestry, not count.** Two failures with the same coarse multiplicity may
   generate different successor grammar.
5. **Observation can manufacture false equivalence.** A residual scalar that forgets ancestry may
   identify different law-birth mechanisms.

## 7. Hostile audit and parent boundary

- McBride's regular-type derivative and Abbott--Altenkirch--Ghani's derivatives of containers
  establish one-hole contexts and plugging as classical machinery.
- Polynomial functors, species, zippers, operads, and functor calculus supply broader chain and
  Faà-di-Bruno laws.
- Therefore ULF-DLG-1 is not a priority claim for container differentiation.
- New corpus leverage is the exact interpretation as a failure-to-challenge producer with an
  ancestry-erasure no-go.
- Arbitrary source syntax can encode arbitrary dynamics. Source marking and invariance under
  accepted presentation changes remain open.
- The theorem produces repair location and grammar, not replacement selection, semantic
  effectiveness, positivity, topology, recurrence, hypertranscendence, or an RH consequence.

## 8. No-go closure

- **Killed conjecture:** a coarse failure value or failure count determines the kind of successor
  interaction.
- **Exact killing mechanism:** the two-branch model has equal ancestry-blind observation but
  opposite ancestry class.
- **Strongest positive survivor:** source-marked polynomial composition canonically generates
  one-hole contexts, nested repair, strict locality, and a common-ancestry partition.
- **New insight:** the missing source law may be a context-production grammar, not a hidden endpoint
  object or another scalar obstruction.

## 9. Lean certification

Module:

`GaloisForLFunctions.HTGeometry.ConstitutiveLawDerivativeGenesis`

Certified declarations:

- `LawContainer`, `LawContainer.Extension`, `LawContainer.OneHoleContext`;
- `contextOfMarked`, `plug`, and restoration/locality;
- `CompositeExtension`, `CompositeSite`, outer/inner contexts, and `nestedRepair`;
- nested restoration and outer locality;
- exact binary interaction partition;
- smallest ancestry-blind countermodel;
- closed capstone theorem.

Direct foreground elaboration and the owned-module build pass without warnings. `#print axioms`
on restoration, nested repair, locality, interaction partition, ancestry erasure, and the capstone
reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. No project axiom,
placeholder, unsafe declaration, or computational proof is used.

## Log

- 2026-08-10 — theorem and countermodel dependency-closed on paper after whole-corpus audit found no
  existing context-production theorem in the Universal Law Field stack.
- 2026-08-10 — exact theorem formalized, axiom-audited, and wired into the Universal Law Field
  umbrella.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.
