# Primitive-spectrum relabeling invariance and presentation-gate law

- **ID:** ULF-SELM-5
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT NATURALITY THEOREM
- **Status:** [PAPER-PROVED] [LEAN-CERTIFIED] [DEPENDENCY-CLOSED] [RELABELING-INVARIANT]
  [PRESENTATION GATE] [NOT MORITA INVARIANCE] [NOT RH]
- **Parents:** ULF-SELM-1--4

## 1. Purpose

ULF-SELM-4 gives a cofinal primitive-degree spectrum.  It is meaningful only if coordinate names
do not create or destroy primitive degrees.  This card proves exact invariance under arbitrary
resource relabeling.  It is the first presentation gate for Symbolic--Execution Law Mechanics.

It is deliberately not called full presentation invariance: adding redundant resources, changing
failure generators, quotienting, completion, or Morita equivalence can change more than labels.

## 2. Transport

Let `e:I≃J` be a bijection.  For a failure kernel `K⊆I`, failure family `H`, and weight
`a:I→N`, define

\[
 e_*K=\{e(i):i\in K\},\qquad
 e_*H=\{e_*K:K\in H\},\qquad
 (e_*a)(j)=a(e^{-1}j).
 \tag{PT.1}
\]

The map `K→e_*K` is a bijection of finite sets and therefore

\[
 \sum_{j\in e_*K}(e_*a)(j)=\sum_{i\in K}a(i).
 \tag{PT.2}
\]

## 3. Transport theorem

### Theorem 3.1 -- local admission is invariant

For every grade `m`,

\[
 \boxed{
 \operatorname{Local}_H(m,a)
 \iff
 \operatorname{Local}_{e_*H}(m,e_*a).
 }
 \tag{PT.3}
\]

### Proof

Each inequality on `K∈H` is, by `(PT.2)`, exactly the corresponding inequality on
`e_*K∈e_*H`.  Applying `e^{-1}` gives the converse. ∎

### Theorem 3.2 -- dominated splitting is invariant

\[
 \boxed{
 \operatorname{Split}_H(m,a)
 \iff
 \operatorname{Split}_{e_*H}(m,e_*a).
 }
 \tag{PT.4}
\]

### Proof

Transport a split `(m_1,m_2,a_1,a_2)` by `e`.  The grade equation and positivity are unchanged;
Theorem 3.1 transports both local laws; and

\[
 a_1(i)+a_2(i)\leq a(i)
 \iff
 (e_*a_1)(e i)+(e_*a_2)(e i)\leq(e_*a)(e i).
\]

Transport by `e^{-1}` for the converse. ∎

### Corollary 3.3 -- primitivity is invariant

\[
 \boxed{
 \operatorname{Primitive}_H(m,a)
 \iff
 \operatorname{Primitive}_{e_*H}(m,e_*a).
 }
 \tag{PT.5}
\]

### Proof

Primitivity is positive local admission together with absence of a dominated positive split.
Apply Theorems 3.1 and 3.2. ∎

## 4. Primitive-spectrum theorem

Define

\[
 \operatorname{Spec}_{\rm prim}(H)
 =\{m:\exists a\;\operatorname{Primitive}_H(m,a)\}.
 \tag{PT.6}
\]

### Theorem 4.1 -- relabeling invariance

\[
 \boxed{
 \operatorname{Spec}_{\rm prim}(e_*H)
 =\operatorname{Spec}_{\rm prim}(H).
 }
 \tag{PT.7}
\]

### Proof

Transport a primitive witness by `e` for one inclusion and by `e^{-1}` for the other.  Equation
`(PT.5)` proves both directions. ∎

Consequently the unbounded spectrum in ULF-SELM-4 cannot be removed by renaming coordinates or
reordering apertures.

## 5. Constitutive law and scope

### SELM Law V -- primitive degree is a marked combinatorial invariant

Within a fixed failure presentation, primitive degree measures a law's minimum indecomposable
execution grade rather than its coordinate spelling.  Any source realization may change labels
without changing the spectrum.

Sharp boundaries:

1. `e` is a bijection.  Forgetful maps, quotients, duplications, or added dummy coordinates are not
   covered.
2. Equality of primitive spectra does not imply isomorphism of failure systems.
3. This proves no invariance under Tietze moves, derived/Morita equivalence, completion, or change
   of observer doctrine.
4. A route realization still must show that its coordinate changes are literal transports of the
   declared source failure family.
5. No topology, positivity, recurrence, HT, analytic continuation, zero statement, or RH
   implication occurs.

The next presentation gate is stable redundancy: identify exact source moves that add derived or
semantically redundant generators while preserving executable-law content, then test whether the
primitive spectrum or a corrected stable spectrum survives.

## 6. Lean certification

Formalized in

`formal/GaloisForLFunctions/HTGeometry/ConstitutivePrimitiveSpectrumTransport.lean`

without project axioms, `sorry`, `admit`, `opaque`, `unsafe`, or computation proofs.  The module
certifies:

1. kernel, family, and weight transport;
2. forward/backward local admission;
3. forward/backward dominated splitting;
4. primitivity equivalence;
5. primitive-degree occurrence equivalence;
6. one unconditional relabeling capstone imported by `HTGeometry.UniversalLawField`.

Direct foreground elaboration passes.  Axiom inspection of the capstone and its transport
dependencies reports only `propext`, `Classical.choice`, and `Quot.sound`.  Repository lint reports
no target error; its nonzero global exit is caused by unrelated unwired modules.  Final foreground
umbrella audit passes:

```text
Build completed successfully (11603 jobs).
```

## Log

- 2026-08-10 -- derived as the first anti-theatre presentation gate after ULF-SELM-4.  Paper proof
  dependency-closed and Lean-certified.  Stable redundancy and Morita-style invariance remain
  open.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.
