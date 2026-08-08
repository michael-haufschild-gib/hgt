# Anexact Geometry: phase topology of incompatible exactifications

- **ID:** `ngd-anexact-geometry-polarized-law-amplitudes`
- **Stage:** 1 — in progress
- **Working field:** **Anexact Geometry**, now a local subtheory of Lawspace Twistor Geometry
- **Type:** POLARIZED LOCAL MODEL / GEOMETRY OF DAGGER EXACTIFICATION
- **Status:** `[PRECURSOR SUBTHEORY] [PRELIMINARY] [EXACT LOCAL THEOREMS]`
  `[NOT WHOLE-CORPUS PRIMITIVE] [NOT RH] [NO LEAN WRITTEN]`
- **Relationship to NGD/CLG/LTG:** NGD supplies source-indexed reduction spacetime. Constitutive
  Lawstack Geometry is the broader candidate field; Lawspace Twistor Geometry is an optional
  nonabelian-Hodge enhancement. Anexact Geometry describes dagger-symmetric amplitude/phase
  charts; relations, differential matroids, nonlinear observers, and costs require named
  modalities and cannot be reconstructed from one amplitude.

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

## 2. Local primitive: polarized exactness field

Fix a declared dagger symmetric-monoidal coefficient fibre `(C,tensor,1,dagger)` over the
source-indexed reduction equipment. An **anexact chart** provisionally consists of:

1. a source-framed stable/curved coefficient stack `E`;
2. for each presentation `x`, a dualizable law object `L_x` and exactness amplitude

   \[
    s_x:\mathbf1\longrightarrow\mathcal L_x
   \tag{AE.1}
   \]

   in that fixed dagger fibre;
3. a dagger/polarization producing an energy shadow

   \[
    g_x=s_x^\dagger s_x;
   \tag{AE.2}
   \]

4. only when separately declared, nonlinear modalities sending these objects to derived zeros,
   singularities, relations, ranks, or costs;
5. a groupoid or `2`-groupoid `Triv_x` of admissible exactness trivializations;
6. for each legal reduction, transport of amplitudes and trivializations, with canonical
   Beck--Chevalley exchange cells;
7. a phase connection on `Triv` and a separate Lawvere/quantale cost on executed lifts;
8. a source current/intervention law that constrains the transition cells before target
   specialization.

No scalar line is required globally. In higher-rank charts `L_x` may be a determinant,
orientation, Tate, or Picard object extracted by a named functor from a deformation--obstruction
complex. Kernel pairs, differential matroids, closed relations, method exponents, and costs do not
follow from `(AE.1)` without additional functors. This limitation is why Anexact Geometry is now a
local LTG chart rather than the field primitive.

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
`source-normal-hochschild-maurer-cartan-clock-curvature-law.md` further proves and classifies:

1. inner corrections preserve every trace--derivation cyclic period;
2. product trace measures a normalized clock Hochschild boundary;
3. for `kappa=chi-1`,

   \[
    \kappa(mn)-\kappa(m)-\kappa(n)=\kappa(m)\kappa(n);
   \tag{AE.4}
   \]

4. the raw coordinate `kappa` cannot itself be additive off the neutral character;
5. the quadratic composition representative is an ordinary group coboundary for every character;
6. `log(1+kappa)=log chi` linearizes the law for every positive radial character, so the
   quadratic term is not invariant curvature and does not force a binary producer.

These results close two false producers: neither inner unary correction nor raw binary
nonadditivity supplies coordinate-free selection geometry.

The Pipeline-2 cards
`half-density-route-l-odd-weil-connection-weld.md` and
`odd-euler-comb-tempered-admission-wall.md` prove the first coefficient-changing field theorem:

\[
 \mathcal L(A_a^- -A_a^+)\mathcal L^{-1}=C_{D_{a+1/2}},
 \qquad
 \left.\partial_a\right|_0D_{a+1/2}=XK_{\rm pr},
\]

with prime coefficient `-(log p)^2/sqrt(p)`. They also prove `D_b` is tempered exactly for
`b>=1`. Hence Route-L operator connection and odd atomic current are exact coefficient shadows of
one arithmetic family, with a sharp admission horizon. Completion cofiber is nevertheless zero
in distributions and absent below the tempered wall. A relative-admission construction remains a
Route-L calibration problem, not the field core.

## 4. Frozen local zeta calibration conjecture

### `SOURCE-POLARIZED-EXACTIFICATION-DESCENT`

For the completed zeta source there exists a source-defined anexact chart `A_zeta` over the legal
reduction equipment such that:

1. its arithmetic amplitude realization is the literal cyclic residue/conormal line;
2. its positive realization is the Stokes--Witt/Fitting energy and its unique central rank port;
3. its spectral realization contains the strict Mellin/Fourier/Gamma exchange and reflection-odd
   Weil tangent;
4. its homological realization contains the relative Connes-lift class whose connecting boundary
   is the measured paracyclic defect;
5. its composition data are invariant under admissible law-coordinate changes; in particular the
   logarithmic coordinate trivializes the raw term `(AE.4)` and must extend or fail for a named
   global reason;
6. its topology retains the all-prime phase/Tate transition object rather than scalarizing it;
7. its source intervention law is fixed before divisor specialization and gives an independent
   stability/descent constraint;
8. the arithmetic, spectral, positive, and phase realizations are jointly conservative on the
   source-generated exactification class.

Items 7--8 carry the RH-bearing burden. This is a local zeta calibration conjecture, not the
foundation of the field and not current explanatory evidence. Lawspace Twistor Geometry must first
exist and pass a non-RH three-face calibration.

## 5. Field equations

### Law A — amplitude/energy polarization

Every positive route defect claimed to descend from a source amplitude must factor through a
declared dagger square `(AE.2)`.  Its phase kernel is part of the field, not gauge garbage unless
the literal source gauge identifies it.

### Law B — exactness relativity

An exactification is local to a polarization.  Transport between two polarizations is flat only
when its canonical exchange cell is invertible **and** its exactness trivializations are
compatible.  Target exactness alone is insufficient.

### Law C — reparametrization-invariant composition

Finite transition amplitudes may compose nonlinearly in a chosen coordinate. Raw nonlinear terms
are not curvature unless they survive admissible coordinate change. In the positive radial clock
chart, `log(1+kappa)` makes composition additive. Invariant content must instead lie in failure of
such coordinates, daggers, admissions, or exactness frames to glue globally.

### Law D — relative uncurving

If a target admits a canonical contracting or Connes homotopy, the observable source class is the
relative obstruction to lifting that homotopy through the source-realizable subcomplex.  Absolute
target null-homology is not selection.

### Law E — phase-history time

Thin path transport records exactification holonomy; Moore paths record duration and executed
cost.  State or energy recurrence may close in the observer quotient while the lifted
exactification history remains nontrivial.

### Law F — source dynamics

Source identities constrain transition and stability data. They are not consequences of local
amplitude geometry. A candidate law must be natural before target specialization, invariant under
admissible coordinates, preserve an independent source detector, and defeat explicit generalized-
source countermodels.

## 6. Route and corpus shadows

| Corpus organ | Anexact interpretation | Exact status |
|---|---|---|
| Route R / arithmetic dagger | `q-1` amplitude; squared Stokes energy; relative Connes lift | local trichotomy proved; global descent open |
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

The table is not proof of the field. Rows become one theory only through presentation-invariant
descent and stability theorems. The strict Route-L coefficient theorem is a calibration and
simultaneously falsifies completion cofiber as its carrier. Lawspace Twistor Geometry now owns the
field-level construction programme.

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

## 8. One-way phase loss theorem schema

For a local law amplitude `a`, the pair

\[
 \bigl(a,\ a^\dagger a\bigr)
\tag{AE.5}
\]

contains exactly the information of `a`, since first projection recovers it. The nontrivial
forgetful map is one-way:

- the unsquared entry retains orientation but may have no singularity category;
- the squared entry creates nonreduced singularity but is invariant under phase reversal;
- exactifying target monodromy may be canonical, while lifting that exactification to source is a
  nonzero relative class;
- raw finite nonadditivity may disappear after logarithmic reparametrization.

Thus the theorem is not a symmetric uncertainty relation. It says the positive observer
`a -> a^dagger a` is generally nonconservative and changes the automorphism group. Any stronger
complementarity must come from incompatible global descent or stability, not from the pair itself.

## 9. Risky predictions

1. **Quadratic-port prediction.** Every corpus port with exact quadratic positive vanishing and a
   claimed source origin must admit a pre-positive weight-one phase/conormal realization.  Absence
   of such a realization falsifies common-source descent.
2. **Relative-Connes prediction.** Any paracyclic target-nullhomology argument that does not compute
   a relative source-lift class is selection-blind.
3. **Coordinate-invariance prediction.** Any genuine Stokes/source obstruction must survive
   `kappa -> log(1+kappa)` wherever that coordinate is admitted. Therefore it must be a failure of
   global logarithm, integral/real structure, stability, admission, or exactification descent—not
   raw binary nonadditivity.
4. **Route-L coefficient prediction — confirmed.** The strict Mellin/Fourier comparison satisfies
   `L(A_a^- -A_a^+)L^-1=C_{D_{a+1/2}}`, and its normal derivative at `a=0` is the odd
   Weil/Stokes prime current with coefficient `-(log p)^2/sqrt(p)`. The same calculation proves
   that completion cofiber is zero or absent; a possible Route-L successor carrier is relative
   admission, not a necessity of the whole field.
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
6. **Kummer/derivation plus inner correction makes raw `kappa` additive.** Failed: prime period is
   invariant and raw finite composition has a quadratic term.
7. **Ordinary binary group cohomology supplies higher selection.** Failed: the quadratic term is
   `-d_grp(kappa)` for every character and its class is always zero.
8. **Raw quadratic term forces a binary producer.** Failed: logarithm linearizes it for every
   positive radial character.
9. **Metaplectic phase torsor alone forces the critical line.** Failed: nonunitary radial holonomy
   and adelic splitting countermodels survive.
10. **Survivor.** The reparametrization-invariant lift stack of exactness frames across
    arithmetic, spectral, positive, and topological polarizations is the next universal object.

## 11. Falsifiers

Anexact Geometry, as applied here, fails if any of the following occurs:

1. the Route-L coefficient identity does not preserve the same source labels/parity as the Route-R
   amplitude;
2. a positive doubled horizon canonically recovers a nonzero oriented generator despite its phase
   automorphism;
3. a claimed invariant curvature disappears under an admitted analytic coordinate change;
4. a claimed global descent obstruction also occurs in a source-trivial calibration with a global
   exactness frame;
5. the source reporter domain assumes zero aperture, critical-line support, or vanishing of the
   physical class;
6. the quantum/physical transfer equates phase fibre with interior length without an independent
   operator/charge normalization;
7. no coefficient-changing theorem links two nonisomorphic route organs after exhaustive attack.

## 12. Immediate research programme

1. Treat the strict Route-L weld and relative Connes class as local calibration theorems only.
2. Construct the reparametrization-invariant exactification descent fibre
   `fib(Triv_src -> holim Triv_alpha)` in a typed non-RH model.
3. Prove its presentation invariance and compute two nonisomorphic boundary invariants.
4. Embed this local dagger chart into the pro-wild twistor stack proposed by Lawspace Twistor
   Geometry.
5. Build a non-zeta three-face calibration linking arithmetic/graded, spectral/flat, and
   positive/topological data through one stability wall.
6. Only after that field exists should zeta or any RH implication return to the programme.

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

No Lean code was written or built. This is a local subtheory. Only dependency-closed Pipeline-2
theorems are eligible for later formalization, after explicit user authorization and local
declaration research.

## Log

- 2026-08-08 — frozen after curvature-only NGD remained classificatory.  DVR
  orientation/singularity complementarity, relative Connes uncurving, and binary clock curvature
  identified the phase-bearing exactification field as the missing geometric primitive.
- 2026-08-08 — hostile review found logarithmic linearization of raw clock curvature and proved
  amplitude geometry too narrow for relation, matroid, topology, and cost organs. Demoted to local
  dagger subtheory of Lawspace Twistor Geometry.
