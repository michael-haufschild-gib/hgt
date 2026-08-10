# Coefficient-refinement transgression mechanics

- **ID:** ULF-CRT-1
- **Stage:** 1-in-progress
- **Type:** NEW-FIELD MECHANISM PROGRAMME
- **Founding claim:** Refining a coefficient doctrine can convert a closed law of arity `n` into an
  unavoidable coherence law of arity `n+1`.  The conversion is governed by a lift-transgression,
  not by a fitted choice of carrier.
- **Status:** [MECHANISM NOT OBJECT] [DEGREE-TWO CORE PAPER-PROVED]
  [DEGREE-TWO CORE LEAN-CERTIFIED] [GENERAL TOWERS OPEN] [NOT RH]

## 1. Higher question

Obstruction--Promotion Mechanics currently separates strict, extension/history, higher-arity, and
singular/admission promotion.  Its decisive open gate is an exchange law between those modes.

Coefficient-refinement transgression supplies one such law:

\[
 \text{law closed after coarse observation}
 \longrightarrow
 \text{attempted fine lift}
 \longrightarrow
 \text{kernel-valued next coherence}.
 \tag{CRT.1}
\]

This is not a request for a universal object.  It is a production mechanism.  A law at one level
becomes the source of the next law when its legal coefficient resolution is refined.

## 2. Founding laws

### Law I -- coarse closure does not imply fine closure

For a coefficient extension

\[
 0\to K\xrightarrow{i}A\xrightarrow{q}B\to0,
 \tag{CRT.2}
\]

a `B`-valued cocycle may have no `A`-valued cocycle lift.  Observation through `q` can therefore
report exact closure while every fine representative remains nonclosed.

### Law II -- failed lift raises arity

Choose any fine lift of an `n`-cocycle.  Its differential lands in `K` and is an `(n+1)`-cocycle.
The next law is produced by the failed lift itself.

### Law III -- choice changes representatives, not obstruction

Changing the lift by a `K`-valued `n`-cochain changes the higher defect by its coboundary.  Hence the
obstruction class is coefficient-extension data, not splitting theatre.

### Law IV -- vanishing is a strictification theorem

The higher class vanishes exactly when a fine cocycle lift exists.  This is a converse, not merely
a necessary obstruction.

### Law V -- split refinements cannot generate higher law

If `q` has an additive section, every coarse cocycle lifts through that section.  Nontrivial arity
birth therefore requires nonsplit coefficient refinement or an additional admission restriction.

### Law VI -- iterated refinement creates a law spectral sequence

For a tower of coefficient doctrines, successive failed lifts should produce successive
transgressions.  Their pages record which arities become legal after each refinement.  This is the
main open generalization; no spectral-sequence universality is asserted yet.

## 3. Why this is a higher pivot

Existing ULF laws prove:

- a compensator's differential selects central closure versus higher associator;
- observation transports that differential and can hide it in a kernel;
- admission restriction can forbid an otherwise associative central promotion.

Coefficient-refinement transgression adds the missing converse exchange:

> a binary history law that closes in a quotient may be intrinsically unable to close in the
> refined coefficient doctrine; the exact obstruction is then a canonical higher law.

Thus central/history promotion and higher-arity promotion are consecutive phases of one lifting
mechanism in this sector, not unrelated choices.

## 4. Closed laboratories

### 4.1 Finite multiplicative laboratory

For `G=(Z/2)^2`, `A=Z/4`, `B=Z/2`, and

\[
 \kappa_B(x,y)=x_1y_2,
\]

the coarse compensator is a cocycle.  No `Z/4`-valued cocycle lifts it.  The binary-digit lift has
associator `2` on an explicit triple, hence kernel-valued higher defect `1 in Z/2`.

### 4.2 Linear differential laboratory

On the two-term complex with `A=Z/4` and differential `d(a)=2a`, the quotient `B=Z/2` has zero
differential.  Its class `1` is closed, but every lift is odd and has differential `2`; no closed
lift exists.  The same production law appears without group multiplication or central extensions.

These laboratories are structurally different: one is associativity/history, the other ordinary
linear exactness.

## 5. Research programme

1. Formalize the degree-`n` cochain version and its naturality under maps of coefficient extensions.
2. Classify when iterated transgressions terminate, become periodic, or survive to a limit.
3. Add admission/topology: distinguish algebraic lift, continuous lift, and admitted lift.
4. Prove an exchange law between coefficient transgression and Hausdorff separation.
5. Develop multiplicative compatibility: cup products, derivations, and Leibniz rules for born
   higher laws.
6. Determine whether positivity sends a transgression to a quadratic secondary operation rather
   than erasing it.
7. Seek one nontrivial three-mode coherence involving history lift, higher birth, and completion.

## 6. Death criteria

Retire this programme as field core if:

- all useful examples require a coefficient sequence chosen after seeing the target;
- general towers add no predictions beyond ordinary long exact sequences;
- admission and completion destroy naturality of the connecting class without a replacement law;
- no second exchange law couples transgression to another certified ULF mechanism.

## 7. Parent mathematics

The algebra is classical connecting-homomorphism/Bockstein theory.  Central extensions are
classified by degree-two cohomology, and degree-three classes govern 2-groups and lift obstructions.
Relevant modern parents include:

- Rumynin--Vakhrameev--Westaway, *Covering groups of nonconnected topological groups and 2-groups*,
  [arXiv:1709.09728](https://arxiv.org/abs/1709.09728);
- Ionescu--Kumjian, *Obstructions to lifting cocycles on groupoids and the associated C*-algebras*,
  [arXiv:1612.07257](https://arxiv.org/abs/1612.07257);
- Joshi--Spallone, *Central Extensions and Cohomology*,
  [arXiv:2307.14658](https://arxiv.org/abs/2307.14658).

Field content is the reinterpretation as a law of law genesis and its required exchange programme,
not a claim that Bockstein theory itself is new.

## Log

- 2026-08-10 -- central-history versus higher-promotion gate reframed as coefficient-refinement
  transgression; degree-two theorem, converse, split boundary, and two laboratories closed.
