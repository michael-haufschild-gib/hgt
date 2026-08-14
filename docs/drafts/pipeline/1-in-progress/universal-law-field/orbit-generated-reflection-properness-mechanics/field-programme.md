# Orbit-Generated Reflection Properness Mechanics — field programme

- **ID:** ULF-OGRPM-0
- **Stage:** 1-in-progress
- **Type:** MECHANISM-FIRST FIELD PROGRAMME / GENERATED POLYREFLECTION
- **Source:** Constitutive Reflection-Space Mechanics, Source-Response Signature Mechanics,
  functional-equation packet formation, and recurrent lifted-history laws
- **Status:** `[ACTIVE] [MECHANISM NOT OBJECT] [FINITE/SHIFT CORE PAPER-PROVED]
  [SOURCE REALIZATION OPEN] [NOT RH]`

## 1. Pivot

Constitutive Reflection-Space Mechanics showed that one functional reversal leaves a large odd
sector, while several reversals may select it through a joint Gramian.  Its open Gate C asked the
source to supply several independent reversals.  That demand was too rigid.

One neutral reversal and one legal source evolution already generate a whole family:

\[
  J_k=U^kJ_0U^{-k}.
  \tag{OGR.1}
\]

The field question is therefore not “how many symmetries were given?” but:

> Does legal source evolution move one functional reversal through enough independent source
> directions that its conjugacy orbit becomes a proper reporter?

This is a generation law.  Functional equation remains information-neutral at each instant.  New
leverage comes from the source-generated orbit of its defect, not from the isolated symmetry.

## 2. Primitive laws

Let `H` be a Hilbert space, `U` unitary, and `P` an orthogonal projection.  Put

\[
  J_0=2P-I,
  \qquad P_k=U^kPU^{-k},
  \qquad J_k=2P_k-I.
  \tag{OGR.2}
\]

### Law I — evolution generates reversals

Every `J_k` is a self-adjoint unitary involution and

\[
  J_{k+1}=UJ_kU^{-1}.
  \tag{OGR.3}
\]

No second reversal is inserted.

### Law II — reversal defects are an orbit-analysis operator

Since `I+J_k=2P_k`,

\[
  \sum_k\|(I+J_k)x\|^2
  =4\sum_k\|PU^{-k}x\|^2.
  \tag{OGR.4}


Thus the joint-reversal Gramian is exactly four times the orbit-observability/fusion-frame
operator.  Its kernel is

\[
  \bigcap_k\ker(I+J_k)
  =\overline{\operatorname{span}}\{U^k\operatorname{ran}P\}^{\perp}.
  \tag{OGR.5}


Selection is source-orbit completeness; stable selection is the lower fusion-frame bound.

### Law III — wandering formation gives exact properness

If the translates `U^k ran(P)` form an orthogonal decomposition of `H`, then

\[
  \sum_k\|(I+J_k)x\|^2=4\|x\|^2.
  \tag{OGR.6}


The properness constant is exact and independent of aperture.  This is the global formation law:
one wandering source sector generates a complete tight polyreflection reporter.

### Law IV — recurrence and selection coexist through lifted action

On a finite cyclic source of period `N`, `J_{k+N}=J_k`.  The observer is exactly recurrent.  But
the marked execution remembers the number of completed cycles, and

\[
  \sum_{m=0}^{qN-1}\|(I+J_m)x\|^2=4q\|x\|^2.
  \tag{OGR.7}


Hence bounded lifted action forces `x=0`, although every endpoint reporter repeats.  Recurrence is
not opposed to properness; forgetting the execution lift is what loses selection.

### Law V — common recovery is neutral

Any common isometric recovery embedding intertwining `U` and `P` preserves `(OGR.4)` term by term.
Split Markov packet formation independently preserves KL and Jeffreys information.  Recovery can
transport the generated reversal orbit but cannot improve or destroy its frame bound.

## 3. Hostile conjecture loops

### Loop A — one neutral reversal can never select

`[FALSIFIED]`.  Its source-conjugacy orbit can be jointly proper.  The cyclic coordinate theorem
has exact bound four.

### Loop B — every conjugacy orbit selects

`[FALSIFIED]`.  Equation `(OGR.5)` leaves the orthogonal complement of the orbit-generated source
sector.  If `U` commutes with `P`, the family is constant and nothing new is generated.

**Survivor:** orbit completeness is necessary and sufficient.

### Loop C — completeness gives stable selection

`[FALSIFIED]` in infinite dimension.  For the bilateral shift on `ell^2(Z)`, the orbit of
`phi=e_0-e_1` is complete because its Fourier multiplier `1-z` is nonzero almost everywhere, but
its frame energy has multiplier `|1-z|^2` and no positive lower bound.

**Survivor:** stable selection is exactly the orbit-frame lower bound, not injectivity.

### Loop D — a periodic observer has bounded history cost

`[FALSIFIED]` by `(OGR.7)`.  Endpoint recurrence and accumulated marked work live on different
quotients.

### Loop E — common recovery supplies the missing bound

`[FALSIFIED]`.  Exact recovery isometry preserves the existing bound and its failure.

### Loop F — the mechanism is new frame theory

`[REDISCOVERED/BRIDGE]`.  Fusion frames, group-generated frames, dynamical sampling, observability
Gramians, and wandering-subspace decompositions are established mathematics.  The field delta is
the constitutive ordering: source evolution generates a family of functional reversals, whose
defects become the properness reporter.  No priority claim is made for the operator theorem.

## 4. Relation to the full frontier

| corpus organ | generated-reflection law |
|---|---|
| functional equation | seed involution `J_0` |
| legal intervention/evolution | conjugation by `U^k` |
| positive carrier | orbit-defect Gramian |
| recurrence | periodic/projected reversal orbit |
| open history | marked execution count |
| completion wall | complete orbit without lower frame bound |
| hypertranscendence/prolongation | possible need for an unbounded commutator/orbit tower |
| global selection | bounded lifted action under a proper orbit frame |

The mechanism does not assert that any current RH source already supplies a wandering functional
reversal.  It replaces “find several independent route symmetries” with one exact source question:

\[
  \boxed{\text{Does one legal source orbit of the functional reversal form a proper fusion frame?}}
  \tag{OGR.8}


## 5. External parents

- Calderbank--Casazza--Heinecke--Kutyniok--Pezeshki, *Fusion Frames: Existence and Construction*,
  <https://arxiv.org/abs/0906.5606>.
- Iverson, *Frames generated by compact group actions*,
  <https://arxiv.org/abs/1509.06802>.
- Christensen--Hasannasab, *A survey on frame representations via dynamical sampling*,
  <https://arxiv.org/abs/2201.00038>.
- Robinson, *Julia operators and Halmos dilations*,
  <https://arxiv.org/abs/1803.09329>.

## 6. Gates

- [x] exact orbit-defect identity and kernel classification
- [x] exact wandering-sector tightness
- [x] finite recurrent observer/open-action properness theorem
- [x] infinite complete-but-nonproper countermodel
- [ ] literal pre-zero source evolution `U` on the same complete response space as functional reversal
- [ ] source proof that the functional fixed/odd sector is a wandering or framed orbit sector
- [ ] transport to the physical current before divisor specialization
- [ ] RH selection consequence

## Log

- 2026-08-14 — independent-reversal premise replaced by source-generated conjugacy orbit.
- 2026-08-14 — fusion-frame collision accepted; exact recurrent/open-action selection survivor kept.
