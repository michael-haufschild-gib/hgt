# Exponential-admission escape mechanics

- **ID:** ULF-EAEM-1
- **Stage:** 1-in-progress
- **Type:** FIELD PROGRAMME / MECHANISM AND LAWS
- **Statement:** Source formation must distinguish topology-small remote mass from
  exponentially visible analytic mass. Functional equation, positivity, common recovery, and
  global properness do not do so; an exponential-admission or variation-diminishing law is the
  missing kind of mechanism.
- **Status:** `[MECHANISM, NOT OBJECT] [PRE-RH] [EXACT COUNTERMODEL PROVED]`

## 1. Why this programme exists

The universal-law-field corpus already supplies:

1. source formation and recovery;
2. functional-equation actions lifted through common recovery kernels;
3. exact information conservation;
4. positive work and global properness;
5. finite and cofinal reconstruction mechanisms.

Yet none selects the functional-equation fixed locus. The failure is not another missing carrier.
It is a mismatch between two notions of smallness:

\[
 \boxed{
 \text{small in source topology}
 \quad\not\Rightarrow\quad
 \text{small for exponential continuation reporters}.}
 \tag{EAEM.1}
\]

A packet translated to distance `R` and scaled by `e^{-aR}` vanishes in every Schwartz seminorm,
but its bilateral Laplace value at real displacement `a` remains order one. This single mechanism
explains why formation, positivity, recovery, recurrence, and properness can all be exact while
analytic zero placement remains uncontrolled.

## 2. Primitive laws

The programme uses laws, not a proposed universal object.

### Law I — remote-packet escape

For `a>0`, topology with only polynomially weighted seminorms cannot continuously observe the
exponential character `x |-> e^{ax}`. Remote mass can escape every source seminorm while retaining
finite nonzero exponential response.

### Law II — involutive closure

Even formation turns one off-axis Laplace zero `z` into the full quartet

\[
 z,\quad -z,\quad \bar z,\quad -\bar z.
\]

Functional equation therefore propagates the defect; it does not remove it.

### Law III — smoothing neutrality

Convolution with a positive even Gaussian multiplies bilateral Laplace transforms by a nowhere-zero
factor. It converts a positive atomic witness into a strictly positive even Schwartz source without
moving any zero.

### Law IV — recovery neutrality

Attaching any parameter-independent Markov recovery kernel is an information isometry. It preserves
the source counterexample and cannot repair exponential escape.

### Law V — properness nonselection

The exponential-tilt family of every nondegenerate positive even source has strictly positive
reflected Jeffreys work away from the center. Hence proper work is compatible with off-axis zeros.
Properness controls escape in the chosen parameter; it does not control which analytic source was
formed.

### Law VI — admission must dominate the reporter

To make evaluation at `z=a+i tau` continuous, source admission must control at least an
`e^{a|x|}` moment, or impose a stronger nonlocal law such as total positivity / variation
diminution. A topology that only sees polynomial tails cannot support robust nonvanishing at `z`.

## 3. Exact fusion already obtained

The Stage-2 theorem

`positive-even-schwartz-off-axis-zero-density-and-formation-properness-no-go.md`

constructs one literal source simultaneously realizing four structurally different organs:

| organ | exact realization |
|---|---|
| functional equation | even bilateral Laplace transform, hence reflection quartet |
| positivity/statistics | strictly positive Schwartz density and exponential family |
| recovery/information | arbitrary common split-recovery kernel, exact KL isometry |
| topology/admission | Schwartz-small remote packets with order-one exponential response |

It also retains strictly positive reflected Jeffreys work. Thus the theorem is not a route analogy:
one source satisfies every generic formation/properness axiom while violating zero selection.

## 4. Fourth-organ prediction

The density theorem predicts an exact topology law:

> In the ordinary Schwartz topology, the positive even sources whose bilateral Laplace transform
> vanishes at any fixed off-axis point are dense. Therefore no open, Schwartz-stable admission
> condition can imply nonvanishing at that point.

This prediction is independent of the Hasse recovery construction and applies to every formation
whose analytic reporter contains a nonzero real exponential character.

The source topology must therefore be changed before an RH selection theorem is possible. Candidate
mechanisms are:

1. exponential weighted bornologies indexed by horizontal displacement;
2. Pólya-frequency / total-positivity constraints;
3. source-generated variation-diminishing semigroups;
4. arithmetic lineage conditions not stable under remote positive packet insertion;
5. a projective family of exponential admissions whose intersection remains source-generated.

These are research directions, not assumptions to be fitted after seeing the divisor.

## 5. Formation/properness repair

The existing global formation/properness theorem remains valid. Its role changes:

\[
 \text{formation properness}
 \quad+\quad
 \text{reporter-dominating admission}
 \quad+\quad
 \text{source lineage}
 \quad\Longrightarrow\quad
 \text{possible selection}. 
 \tag{EAEM.2}
\]

Without the middle two terms, properness is only a parameter-space theorem. The new theorem proves
that this omission is fatal, not cosmetic.

## 6. Relation to parent mathematics

Schwartz spaces, bilateral Laplace transforms, translation estimates, and Gaussian convolution are
classical. Pólya-frequency functions and Schoenberg total positivity provide a known stronger class
whose Laplace-transform zeros are constrained. Useful modern entry points are:

- Apoorva Khare, *Multiply positive functions, critical exponent phenomena, and the
  Jain--Karlin--Schoenberg kernel*, <https://arxiv.org/abs/2008.05121>;
- Doug Pickrell, *A Question About Total Positivity and Newman's Fourier Transforms with Real
  Zeroes*, <https://arxiv.org/abs/2104.05143>.

The programme does not claim those ingredients are new. Its claim is operational: the corpus's
repeated selection failures are instances of one topology/reporter incompatibility, and any viable
universal field must contain a law preventing that incompatibility.

## 7. Gates

- [x] exact remote-packet escape sequence
- [x] explicit positive even two-shell off-axis zero
- [x] Gaussian smoothing preserving positivity, Schwartz regularity, and zero quartet
- [x] density of zero-bearing sources in the positive even Schwartz cone
- [x] fusion with functional equation, split recovery, KL conservation, and proper work
- [x] exact nonselection theorem for generic formation/properness axioms
- [ ] construct source-generated exponential admission for the Euler/theta source
- [ ] prove admission is preserved by the full formation grammar
- [ ] derive a variation-diminishing or total-positive constitutive law from source operations
- [ ] prove strict-right nonvanishing before Xi specialization
- [ ] RH selection consequence

## 8. Lean scope

The finite algebraic core is to be certified in

`ConstitutivePositiveEvenLaplaceEscape.lean`:

- positive two-shell weights;
- exact off-axis cancellation;
- involutive zero quartet at the algebraic transform level.

The Schwartz density theorem remains paper-proved until the required translated-Schwartz and
bilateral-Laplace infrastructure is built.

## Log

- 2026-08-14 — programme opened after functional-equation split recovery proved information-neutral
  but nonselective. Corpus audit showed generic formation/properness was already complete; the new
  obstruction is exponential reporter discontinuity, not another recovery object.
