# Anexact Geometry: phase topology of incompatible exactifications

- **ID:** `ngd-anexact-geometry-polarized-law-amplitudes`
- **Stage:** 1 — in progress
- **Working field:** **Anexact Geometry**
- **Type:** FROZEN FIELD CONJECTURE / GEOMETRY AND TOPOLOGY OF LAW
- **Status:** `[GR-LEVEL FIELD CORE CANDIDATE] [PRELIMINARY] [EXACT LOCAL THEOREMS]`
  `[SOURCE DYNAMICS OPEN] [NOT RH] [NO LEAN WRITTEN]`
- **Relationship to NGD:** NGD supplies source-indexed reduction spacetime.  Anexact Geometry is
  the proposed geometric field carried on it: amplitudes, polarizations, exactness
  trivializations, phase holonomy, and composition curvature.

## 0. Public sentence

> A mathematical law is the phase-bearing way several individually exact descriptions fit
> together; when no choice makes all descriptions exact simultaneously, that incompatibility is
> geometry.

The familiar arithmetic object, spectral operator, positive form, topology, recurrence record,
or boundary state is not the whole law.  Each is a polarization of one source-framed family of
exactness amplitudes and their compatible trivializations.

## 1. Ontological reversal

Current route mechanics treats complexes, operators, positive forms, completions, and clocks as
fixed arenas, then searches for an object satisfying every condition.  Anexact Geometry reverses
this:

```text
Newtonian route mechanics             Anexact Geometry
-------------------------             -----------------
object obeys several equations        law is compatibility of exactifications
one preferred exact complex           no preferred exactness polarization
defect is a bad vector                 defect is transition amplitude/curvature
positive norm is more information     positivity is a phase-forgetting square
completion finishes construction      completion may cross an exactness horizon
time is one parameter                  time is holonomy plus executed lift history
selection chooses object              source dynamics chooses a global trivialization
```

The “Heisenberg” phenomenon in the corpus becomes exact: an unsquared equation retains
coorientation but may have trivial singularity theory; its positive square creates a nontrivial
singularity while erasing phase.  Making one face fully precise changes what the other face can
possibly observe.

## 2. Primitive: polarized exactness field

Let `B_src` be the source-indexed bivariant reduction equipment of NGD.  An **anexact field** over
`B_src` provisionally consists of:

1. a source-framed stable/curved coefficient stack `E`;
2. for each presentation `x`, an exactness amplitude or potential section

   \[
    s_x\in\Gamma(X_x,\mathcal L_x)
   \tag{AE.1}
   \]

   in an oriented line, perfect complex, or higher invertible object;
3. a dagger/polarization producing an energy shadow

   \[
    g_x=s_x^\dagger s_x;
   \tag{AE.2}
   \]

4. the derived zero/horizon `Z^der(s_x)` and the possibly nonreduced positive horizon
   `Z^der(g_x)`;
5. a groupoid or `2`-groupoid `Triv_x` of admissible exactness trivializations;
6. for each legal reduction, transport of amplitudes and trivializations, with canonical
   Beck--Chevalley exchange cells;
7. a phase connection on `Triv` and a separate Lawvere/quantale cost on executed lifts;
8. a source current/intervention law that constrains the transition cells before target
   specialization.

No scalar line is required globally.  In higher-rank charts `mathcal L_x` is a determinant,
orientation, Tate, or Picard object extracted from a full deformation--obstruction complex.  The
amplitude is therefore a **polarized law object**, not one universal number.

### Exactification phase space

For a presentation `x`, define

\[
 \mathfrak P_x=\operatorname{Triv}(s_x)/\text{source-preserving gauge}.
\tag{AE.3}
\]

`mathfrak P_x` is the phase space of exactifications.  It may be a torsor, stack, gerbe,
non-Hausdorff relation, or empty.  A reduction sees one of the following shadows:

| Shadow | What it retains | What it loses |
|---|---|---|
| amplitude/source residue | sign, phase, coorientation | positivity and often boundedness |
| energy/Witt/Fitting | nonnegative size, inertia, support | `U(1)` or `mu_m` phase |
| derived zero/singularity | nilpotent thickness, Tor/Ext | ambient source selection |
| cyclic/paracyclic homology | boundary/trivialization classes | target-side exactness may be automatic |
| connection/holonomy | phase transport and recurrence | executed cost unless Moore history retained |
| completion/relation | limiting admission and closure | single-valued reconstruction |
| cost/capacity | operational difficulty | algebraic rank and phase unless linked by theorem |

## 3. Founding local theorems

The Pipeline-2 card
`polarized-exactness-horizon-and-relative-connes-phase-law.md` proves:

1. for a DVR uniformizer `a`, the reduced horizon `a=0` is regular and every finite matrix
   factorization of `a` is contractible;
2. the doubled horizon `a^2=0` has nontrivial singularity theory;
3. its `mu_2` automorphism fixes `a^2` but reverses the conormal generator `[a]`;
4. rank-one positive quantum observation has `U(1)` fibres and loses exactly the phase tangent;
5. in a parachain complex, target monodromy is always Connes-null-homotopic;
6. the real source obstruction is the relative lift class of that null-homotopy.

The Pipeline-2 card
`source-normal-hochschild-maurer-cartan-clock-curvature-law.md` further proves:

1. inner corrections preserve every trace--derivation cyclic period;
2. product trace measures a normalized clock Hochschild boundary;
3. for `kappa=chi-1`,

   \[
    \kappa(mn)-\kappa(m)-\kappa(n)=\kappa(m)\kappa(n);
   \tag{AE.4}
   \]

4. no inner-corrected first-order/additive clock law can represent finite holonomy off the neutral
   character;
5. the quadratic composition representative is an ordinary group coboundary for every character,
   so its useful content is secondary and primitive-sensitive rather than an `H^2` class.

These results are the first dynamics-relevant leverage: the live source-dagger producer is not a
unary Bockstein or target null-homology.  It must act on binary law composition.

The Pipeline-2 cards
`half-density-route-l-odd-weil-connection-weld.md` and
`odd-euler-comb-tempered-admission-wall.md` prove the first coefficient-changing field theorem:

\[
 \mathcal L(A_a^- -A_a^+)\mathcal L^{-1}=C_{D_{a+1/2}},
 \qquad
 \left.\partial_a\right|_0D_{a+1/2}=XK_{\rm pr},
\]

with prime coefficient `-(log p)^2/sqrt(p)`. They also prove `D_b` is tempered exactly for
`b>=1`. Hence Route-L operator connection, odd Weil/Stokes current, and strict admission horizon
are exact coefficient shadows of one arithmetic family. Completion cofiber is nevertheless zero
in distributions and absent below the tempered wall. The still-missing carrier is a source-native
relative admission class, not another absolute defect.

## 4. Frozen universal conjecture

### `SOURCE-POLARIZED-EXACTIFICATION-DESCENT`

For the completed zeta source there exists a source-defined anexact field `A_zeta` over the legal
reduction equipment such that:

1. its arithmetic amplitude realization is the literal cyclic residue/conormal line;
2. its positive realization is the Stokes--Witt/Fitting energy and its unique central rank port;
3. its spectral realization contains the strict Mellin/Fourier/Gamma exchange and reflection-odd
   Weil tangent;
4. its homological realization contains the relative Connes-lift class whose connecting boundary
   is the measured paracyclic defect;
5. its binary composition curvature is the source-normal Maurer--Cartan term `(AE.4)`;
6. its topology retains the all-prime phase/Tate transition object rather than scalarizing it;
7. its source intervention law is fixed before divisor specialization and gives an independent
   Bianchi/Stokes constraint on binary composition curvature;
8. the arithmetic, spectral, positive, and phase realizations are jointly conservative on the
   source-generated exactification class.

This conjecture does **not** say that all curvature vanishes.  It says that actual route organs are
polarizations of one phase-bearing exactification field and that source dynamics constrains their
composition before any zero is inspected.

## 5. Field equations

### Law A — amplitude/energy polarization

Every positive route defect claimed to descend from a source amplitude must factor through a
declared dagger square `(AE.2)`.  Its phase kernel is part of the field, not gauge garbage unless
the literal source gauge identifies it.

### Law B — exactness relativity

An exactification is local to a polarization.  Transport between two polarizations is flat only
when its canonical exchange cell is invertible **and** its exactness trivializations are
compatible.  Target exactness alone is insufficient.

### Law C — composition Maurer--Cartan

Finite transition amplitudes compose nonlinearly.  In a multiplicative clock chart the first
curvature is `(AE.4)`, not the additive derivation.  Higher composition is encoded by coherent
`A_infinity`/parachain/`2`-categorical cells rather than forced into one chain complex.

### Law D — relative uncurving

If a target admits a canonical contracting or Connes homotopy, the observable source class is the
relative obstruction to lifting that homotopy through the source-realizable subcomplex.  Absolute
target null-homology is not selection.

### Law E — phase-history time

Thin path transport records exactification holonomy; Moore paths record duration and executed
cost.  State or energy recurrence may close in the observer quotient while the lifted
exactification history remains nontrivial.

### Law F — source dynamics

Source identities constrain binary and higher composition cells.  They are not consequences of
the geometry.  A candidate field equation must be natural before target specialization, preserve
an independent source detector, and defeat explicit off-line/generalized-source countermodels.

## 6. Route and corpus shadows

| Corpus organ | Anexact interpretation | Exact status |
|---|---|---|
| Route R / arithmetic dagger | `q-1` amplitude; squared Stokes energy; relative Connes lift | local trichotomy proved; binary source law open |
| Route L / Deninger | flat Euler source represented in two Fourier/Mellin polarizations; strict admission boundary | exact half-density weld and admission wall proved; relative strict class open |
| Route E | source relation and directed capacity are extra polarization data, not implied by current | nonselection countermodel proved |
| Mass trace route | arithmetic amplitude becomes chain boundary plus outgoing class; filling cost diverges | finite boundary law proved |
| C1 / Hedenmalm | positive/Hilbert polarization and source domain fail to share a bounded exactification | dense/nonclosed and domain no-gos proved |
| G / Suzuki | meromorphic/holonomy realization retains phase beyond scalar energy | operator-limit selection remains open |
| N/O | source admission and whole-ground exhaustion are exactification-domain horizons | corpus no-gos proved |
| Stokes/Witt | one timelike/central port is energy shadow of one orientation line | publication theorem proved |
| cyclic/Cartier/Kummer | boundary, conormal, and period are distinct grades of exactification | literal source infrastructure proved |
| hypertranscendental families | prolongation changes exactification rank; finite observers see only bounded jet faces | atlas placement; mixed theorem still open |
| quantum recurrence | monodromy amplitude, fidelity/energy, phase holonomy, and executed history differ | finite phase/history separation proved |
| black-hole boundary | positive/reduced boundary observer may lose relative phase/edge modes | split perturbative edge chart only |
| wormhole interior | candidate is nonproduct phase-history lift with conjugate charge and independent length | conjectural; no arithmetic wormhole claimed |

The table is not proof of the field.  Rows become one theory only through named coefficient-changing
exchange theorems. The strict Route-L coefficient theorem is now proved and simultaneously
falsifies completion cofiber as its carrier. The binary source-curvature and relative-admission
theorems are the next tests.

## 7. Phase geometry, recurrence, and horizons

The exact finite quantum chart gives the right physical picture without overclaiming gravity.
Boundary density is a positive square, so the common pure-state fibre is a phase torus.  Winding,
Berry holonomy, Fisher/Fubini--Study action, recovery defect, and endpoint Krylov complexity are
different shadows.  A closed boundary state can therefore carry nonzero lifted history.

Anexact Geometry predicts the same architecture at a genuine holographic horizon only after:

1. source-supported boundary/interior reconstruction maps;
2. a nonproduct relative phase fibre;
3. conjugate edge charge or symplectic pairing;
4. modular/history transport;
5. independently normalized bulk length/work;
6. an operator intertwiner and higher-cumulant agreement.

Without those items, “wormhole phase” is metaphor.  Brown--Susskind growth motivates the executed-
history valuation; it does not identify that valuation with the arithmetic source amplitude.

## 8. Constraint uncertainty becomes a theorem schema

For a local law amplitude `a`, the pair

\[
 \bigl(a,\ a^\dagger a\bigr)
\tag{AE.5}
\]

cannot be replaced by either entry alone:

- the unsquared entry retains orientation but may have no singularity category;
- the squared entry creates nonreduced singularity but is invariant under phase reversal;
- exactifying target monodromy may be canonical, while lifting that exactification to source is a
  nonzero relative class;
- finite additive response is the tangent of multiplicative holonomy, not its composition law.

This is the mathematical content of “making one part precise makes another imprecise.”  It is not
an information inequality; it is a change of coefficient type and automorphism group.

## 9. Risky predictions

1. **Quadratic-port prediction.** Every corpus port with exact quadratic positive vanishing and a
   claimed source origin must admit a pre-positive weight-one phase/conormal realization.  Absence
   of such a realization falsifies common-source descent.
2. **Relative-Connes prediction.** Any paracyclic target-nullhomology argument that does not compute
   a relative source-lift class is selection-blind.
3. **Binary-clock prediction.** A genuine source-normal Stokes producer must control
   `kappa(m)kappa(n)` and cannot factor through a unary derivation, ordinary Bockstein, inner
   connection correction, determinant-one balance, or radial-gauge invariant.
4. **Route-L coefficient prediction — confirmed.** The strict Mellin/Fourier comparison satisfies
   `L(A_a^- -A_a^+)L^-1=C_{D_{a+1/2}}`, and its normal derivative at `a=0` is the odd
   Weil/Stokes prime current with coefficient `-(log p)^2/sqrt(p)`. The same calculation proves
   that completion cofiber is zero or absent; the surviving carrier must be relative admission.
5. **Phase-history prediction.** Exact recurrence of every positive state observable cannot bound
   executed phase-history length without a separately declared history/cost structure.
6. **Horizon prediction.** When positive squaring turns a smooth amplitude wall into a doubled
   singularity, its singularity invariants are phase-even; any claimed recovery of source
   orientation from them alone must fail naturality under the local `mu_2` action.

## 10. Conjecture/proof/fail loops

1. **One universal scalar obstruction.** Failed: coefficients are irreducibly heterogeneous.
2. **Beck--Chevalley curvature alone is the field.** Failed: it describes exchange kinematics but
   not which exactness trivialization is source-selected.
3. **Curved DG/matrix factorization of the unsquared law.** Failed locally: a smooth Cartier
   potential has contractible finite factorization theory.
4. **Positive square/singularity category supplies selection.** Failed: it retains thickness but
   erases `mu_2` phase/coorientation.
5. **Target paracyclic null-homology supplies selection.** Failed: Connes uncurving makes it
   automatic.
6. **Kummer/derivation plus inner correction supplies finite holonomy.** Failed: prime period is
   invariant and finite composition has quadratic curvature.
7. **Ordinary binary group cohomology supplies higher selection.** Failed: the quadratic term is
   `-d_grp(kappa)` for every character and its class is always zero.
8. **Metaplectic phase torsor alone forces the critical line.** Failed: nonunitary radial holonomy
   and adelic splitting countermodels survive.
9. **Survivor.** A source-normal, binary and higher exactification law must constrain the relative
   phase-lift class across Euler, Poisson/Fourier, and Gamma polarizations.

## 11. Falsifiers

Anexact Geometry, as applied here, fails if any of the following occurs:

1. the Route-L coefficient identity does not preserve the same source labels/parity as the Route-R
   amplitude;
2. a positive doubled horizon canonically recovers a nonzero oriented generator despite its phase
   automorphism;
3. an inner-corrected unary derivation comparison reproduces finite multiplicative composition;
4. a claimed binary source law also holds in the explicit off-line group-algebra character
   countermodel;
5. the source reporter domain assumes zero aperture, critical-line support, or vanishing of the
   physical class;
6. the quantum/physical transfer equates phase fibre with interior length without an independent
   operator/charge normalization;
7. no coefficient-changing theorem links two nonisomorphic route organs after exhaustive attack.

## 12. Immediate research programme

1. Finish the strict Route-L Mellin/Fourier admission theorem and compute its exact odd Weil
   derivative.
2. Construct the binary rational-adelic/Gamma exchange cell in
   `binary-source-stokes-exchange-flatness.md`.
3. Define the source-realizable homotopy subcomplex and compute the relative Connes class on the
   trace-one prime simplex.
4. Test whether Euler--Poisson--Gamma triple comparison supplies an **outer** phase-weight-one
   reporter rather than another radial-gauge invariant.
5. Build a non-zeta calibration family with nonzero vacuum/phase curvature and zero source
   curvature, testing that field laws are not target-fitted.
6. Only after one source law constrains the binary class should any RH implication return to Lean.

## 13. Literature boundary

Anexact Geometry deliberately fuses known ingredients: curved DG and matrix-factorization theory,
paracyclic/para-`S` normalization, bivariant exchange, derived zero loci, determinant/orientation
lines, Berry phase, and Lawvere cost.  User instruction removes ingredient-level novelty as a gate.
The criterion is whether this fusion forces exact cross-coefficient theorems and rules out false
producer classes.

Current primary anchors include:

- paracyclic Dold--Kan normalization: <https://arxiv.org/abs/2602.08158>;
- curved DG/matrix factorizations: <https://arxiv.org/abs/2606.10146>;
- curved cyclic filtered `A_infinity` geometry: <https://arxiv.org/abs/2606.12257>;
- para-`S` modules and perturbation: <https://arxiv.org/abs/1810.04835>;
- source-indexed Beck--Chevalley/span machinery: <https://arxiv.org/abs/2505.19192>.

## 14. Lean-return note

No Lean code was written or built.  This is a field conjecture.  Only the two dependency-closed
Pipeline-2 theorem cards are eligible for later formalization, after explicit user authorization
and local declaration research.

## Log

- 2026-08-08 — frozen after curvature-only NGD remained classificatory.  DVR
  orientation/singularity complementarity, relative Connes uncurving, and binary clock curvature
  identified the phase-bearing exactification field as the missing geometric primitive.
