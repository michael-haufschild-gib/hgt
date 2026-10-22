# Deninger--Mertens adiabatic exponential corner

- **ID:** `deninger-mertens-adiabatic-exponential-corner`
- **Stage:** 1-in-progress
- **Type:** SOURCE THEOREM + RH-BEARING COMPLETION CONJECTURE
- **Scientific status:** `[PAPER-PROVED TWO-SCALE LAW]`
  `[LEAN-FORMALIZED SOURCE CORE]`
  `[CORPUS SYNTHESIS]` `[EXTERNAL NOVELTY UNVERIFIED]`
  `[CONJECTURAL THIRD COMPLETION]` `[NOT RH]`
- **Parents:**
  - `deninger-poisson-mertens-boundary-jet-fracture`
  - `deninger-tate-poisson-pro-hodge-rigging`
  - `../3-formalized/new_scientific_knowledge/prime-first-trace-exponential-flat-graph-fracture`
  - `../2-fully-proven/not_new_scientific_knowledge/mertens-logarithmic-corona-differential-tower`
  - `../2-fully-proven/not_new_scientific_knowledge/burnol-prime-dilation-copoisson-quotient-law`
  - `source-curved-prime-torus-conormal-temperedness`
  - `multiplicative-wold-gamma-anomaly-purity-rh`
- **Statement:** Common Tate--Poisson regularization, Euler horizontal
  translation, the reciprocal-prime Hardy kernel, the complete Mertens
  logarithmic jet, and the formalized exponential first-trace fracture are
  the finite, zero, and infinite faces of one exact two-scale kernel
  \(\exp(-he/\varepsilon_p)\), where
  \(\varepsilon_p=1/\log p\).  The missing third completion must therefore
  be an arithmetic adiabatic blow-up of the corner
  \((h,\varepsilon)=(0,0)\), enhanced by an exponential/transseries
  associated graded.  A one-parameter Hilbert scale, formal jet space, or
  ordinary hyperfunction boundary alone loses one of the proved faces.

## 1. Exact two-scale source kernel

For a prime \(p\), put

\[
 L_p=\log p,\qquad \varepsilon_p=L_p^{-1}.               \tag{1}
\]

For Euler translation \(h\ge0\) and positive valuation/Fourier depth
\(e\ge1\), define

\[
 K_p(h,e)
 =
 p^{-he}
 =
 \exp\left(-{he\over\varepsilon_p}\right).               \tag{2}
\]

Equation `(2)` is not a fitted asymptotic.  By
`deninger-poisson-mertens-boundary-jet-fracture`, it is exactly the
\(e\)-th analytic Fourier coefficient of the source-curved Poisson
smoothing of the point conormal on Deninger's transverse prime orbit.
The orbit and its oriented Fourier lattice supply the identification
between positive prime-power depth and positive character depth.

Introduce the blow-up coordinate

\[
 \tau={h\over\varepsilon_p}=h\log p.                    \tag{3}
\]

Then

\[
 K_p(h,e)=e^{-\tau e}.                                  \tag{4}
\]

Thus all prime dependence disappears on the front face of the
\((h,\varepsilon)\)-corner.

## 2. Four already-proved faces

### A. Finite front face: common Tate--Poisson time

The Tate-normalized transverse generator has eigenvalue \(2\pi e\).
Common Tate time \(r>0\) corresponds to

\[
 h=2\pi r\,\varepsilon_p,
 \qquad \tau=2\pi r.                                    \tag{5}
\]

Equations `(2)`--`(5)` give

\[
 K_p(2\pi r\varepsilon_p,e)=e^{-2\pi re}.               \tag{6}
\]

This is exactly the place-independent spectrum used by the
positive-time all-prime Green-form theorem.  Common Tate time is
therefore not a separate normalization: it is finite projective
coordinate on the adiabatic front face.

### B. Arithmetic time-one face: Gamma/Möbius Hardy kernel

At \(h=1\),

\[
 K_p(1,e)=p^{-e}.                                       \tag{7}
\]

Including \(e=0\) gives

\[
 (K_p(1,e))_{e\ge0}=(1,p^{-1},p^{-2},\ldots),           \tag{8}
\]

the reciprocal-prime Hardy kernel.  The Gamma half-shifted valuation
frame and Möbius Schur difference frame are exact nonzero diagonal
multiples of `(8)`.

### C. Zero face: complete logarithmic Mertens jet

For every \(k\ge0\),

\[
 \partial_h^k K_p(h,e)|_{h=0}
 =
 (-e\log p)^k.                                          \tag{9}
\]

At \(e=1\), the \(k\)-th coefficient field is
\((-\log p)^k\).  The graded Mertens theorem proves that its class is
nonzero in grade \(k\), while every \(h>0\) translate is zero in every
corona grade.  Hence the entire polynomial/conormal associated graded
of the corner is

\[
 Q_{\rm gr}=\mathbb C[L][u_0].                          \tag{10}
\]

### D. Infinite front-face end: exponential first-trace grade

For fixed \(h>0\) and \(e\ge1\), `(2)` is flat to every algebraic order
as \(\varepsilon_p\to0\):

\[
 \varepsilon_p^{-N}K_p(h,e)\longrightarrow0
 \qquad(N\ge0).                                         \tag{11}
\]

Nevertheless its WKB action is exact:

\[
 -\varepsilon_p\log K_p(h,e)=he.                        \tag{12}
\]

The formalized actual-prime first-trace witness has source size \(a_p\)
and response error \(b_p\) satisfying

\[
 (\log p)a_p\longrightarrow1,\qquad
 {\log b_p\over\log p}\longrightarrow-1,\qquad
 a_p(-\log b_p)\longrightarrow1.                        \tag{13}
\]

Thus \(a_p\sim\varepsilon_p\), and `(13)` is exactly the \(h=e=1\)
action in `(12)`.  The formalized exponential graph fracture is the
infinite end of the same Deninger--Mertens front face, not an unrelated
rate phenomenon.

## 3. Adiabatic corner theorem

`[THEOREM] [DAC_DENINGER_MERTENS_ADIABATIC_CORNER_LAW]`

The following five structures are faces of the one kernel `(2)`:

1. common Tate--Poisson Hilbert regularization: finite
   \(\tau=2\pi r\);
2. local arithmetic Gamma/Möbius valuation data: \(h=1\);
3. the complete Mertens prime-log clock: the conormal face \(h=0\);
4. positive-translation corona erasure: fixed \(h>0\),
   \(\varepsilon\to0\); and
5. the prime-first-trace exponential rate-normal: the WKB associated
   graded at \(\tau=\infty\).

### Proof `[PROVED HERE]`

Equations `(5)`--`(8)` are substitutions in `(2)` combined with the
proved prime-orbit Poisson--valuation weld.  Equation `(9)` follows by
differentiating the exponential.  The Mertens quotient statements in
`(10)` are the exact graded-corona theorem.  For `(11)`, write
\(x=1/\varepsilon_p\); every fixed power of \(x\) times
\(e^{-hex}\) tends to zero.  Equation `(12)` is literal.  Equation
`(13)` is Lean-formalized in
`PrimeFirstTraceExponentialFlatGraphFracture.lean`.

No Xi zero, continuation, numerical experiment, or positivity
assumption enters this theorem.

## 4. Why all previous completion categories are individually too
##    small

### One Hilbert completion

It sees finite \(\tau>0\) but loses the conormal class at \(\tau=0\),
or retains an ambient continuous spectrum in which divisor fibres are
not vectors.

### A projective family of positive times

It may recover distributional boundary values only after adding a
boundary-value functor.  After the Mertens vanishing-tail quotient,
continuous descent is impossible because every \(h>0\) class is zero
and the \(h=0\) class is nonzero.

### A formal all-jet/Rees completion

It retains `(9)`--`(10)` but cannot distinguish `(11)` from zero:
\(\exp(-he/\varepsilon)\) is flat at \(\varepsilon=0\) for fixed
\(h>0\).  The formalized rate-normal grade `(13)` is invisible.

### A one-variable hyperfunction at \(h=0\)

It can carry infinitely many \(h\)-jets and two chiral boundary
values, but it does not by itself retain the exponential action at the
\(\varepsilon=0,\tau=\infty\) end.

### An ordinary smooth real blow-up

The coordinate \(\tau=h/\varepsilon\) resolves finite front-face
directions, but \(e^{-\tau e}\) is flat at \(\tau=\infty\).  Ordinary
smooth structure again loses the action `(12)`.

The proved corpus therefore forces both:

\[
 \text{real adiabatic blow-up}
 \quad+\quad
 \text{exponential/transseries associated graded}.      \tag{14}
\]

## 5. Frozen jump: arithmetic exponential adiabatic Hodge
##    completion

`[CONJECTURE] [DAC_ARITHMETIC_EXPONENTIAL_ADIABATIC_HODGE_COMPLETION]`

Let \(\mathscr B_{\rm arith}\) be the closure of the source-selected
points

\[
 (\varepsilon_p,h)
 =
 ((\log p)^{-1},h)
\]

in the real oriented blow-up of the two-sided corner
\((\varepsilon,h)=(0,0)\).  The completed Euler--Gamma/co-Poisson
complex admits a canonical sheaf \(\mathscr E_{\exp}\) over
\(\mathscr B_{\rm arith}\) with:

1. **finite-front-face Hardy realization:** its \(\tau>0\) fibres are
   the Tate-normalized prime-orbit Poisson/Hardy spaces `(6)`;
2. **conormal associated graded:** its \(\tau=0\) boundary is the
   complete Mertens module `(10)`;
3. **exponential associated graded:** its \(\tau=\infty\) boundary
   retains the WKB action `(12)` and the canonical first-trace normal
   `(13)`;
4. **two-sided reflection:** functional-equation reflection exchanges
   the two \(h\)-charts and Gamma calibration fixes their common
   affine origin;
5. **source Cauchy conservativity:** every co-Poisson zero-evaluation
   class and multiplicity jet survives in the derived boundary
   cohomology of \(\mathscr E_{\exp}\);
6. **positive boundary Green form:** the renormalized
   Green--Stokes/Paugam residue is positive definite on the
   source-harmonic quotient; and
7. **prime-dilation isometry:** normalized prime dilation acts
   isometrically on that positive boundary form.

Items 1--3 are forced local/asymptotic interfaces.  Items 4--7 are
the global RH-bearing construction and may not be inserted as abstract
axioms.

## 6. Exact RH consumer on the exponential face

Burnol's co-Poisson quotient already supplies, at every nontrivial
zeta zero \(\rho\), a nonzero generalized eigenclass for normalized
prime dilation with character

\[
 \lambda_p(\rho)
 =
 p^{\rho-1/2}
 =
 \exp\left({\rho-1/2\over\varepsilon_p}\right).          \tag{15}
\]

Its WKB modulus action is

\[
 \varepsilon_p\log|\lambda_p(\rho)|
 =
 \Re\rho-\frac12.                                       \tag{16}
\]

If items 5--7 of the conjecture place this nonzero class in the
positive boundary space and make normalized dilation isometric, then

\[
 |\lambda_p(\rho)|=1.
\]

Equation `(16)` forces \(\Re\rho=1/2\).  Applying this to every
nontrivial zero proves RH.

This consumer is not new and is not the proof.  New work is to derive
the positive isometric lift from the full corner geometry rather than
postulate it on the zero quotient.

## 7. How hypertranscendence enters

The corpus has separately proved:

1. every finite clock/jet truncation leaves maximal-HT freedom;
2. finite differential-translation repairs are corona-blind;
3. the raw infinite Hardy graph saturates;
4. the Cholesky/Schur marking becomes meaningful only cofinally; and
5. first-trace response is exponentially flat beyond every finite
   algebraic order.

Hence HT is not a decorative label on \(\mathscr E_{\exp}\).  It
forces its observables to include the complete conormal tower and its
exponential action filtration.  A finite-order analytic, DA, or
ordinary Fréchet completion cannot be conservative.

The new HT problem is:

> prove that the completed Euler--Gamma source relation is closed and
> support-faithful in the exponential adiabatic sheaf even though its
> projection to every finite differential order is dense.

That statement is not presently in the corpus or literature.

## 8. Hostile audit and falsifiers

1. **Not a proof by terminology.**  “Adiabatic,” “transseries,” and
   “Hodge” provide no conclusion until the sheaf, boundary maps, and
   positive form are explicit.
2. **Not ordinary semiclassical analysis.**  The arithmetic points
   \(\varepsilon_p=1/\log p\), Mertens quotient, Gamma/Möbius Hardy
   frame, and co-Poisson zero classes must all be realized by the same
   maps.
3. **Not a formal-jet proof.**  Equation `(11)` proves formal jets
   alone erase the critical exponential grade.
4. **Not a local Gamma-Stokes repair.**  The corpus proves local
   Gamma Stokes factors are projectively scalar.  The exponential
   grade must be global Euler--Gamma/co-Poisson data.
5. **Not abstract unitarization.**  Any invertible character can be
   unitarized after choosing a fitted norm.  Item 6 must be the
   source-derived Green residue and item 7 must follow from its chain
   invariance.
6. **Off-line Euler fakes remain a mandatory test.**  Positive Euler
   density, functional equation, entire completion,
   hypertranscendence, and unsquared Cauchy orientation already admit
   explicit off-line systems.  The proposed corner theorem must fail
   on those systems through its source-specific Gamma/co-Poisson
   boundary map.
7. **Support faithfulness remains open.**  Real blow-up resolves
   directions but does not automatically prevent the completed
   comparison from collapsing distinct affine supports.

The conjecture fails if no source-defined exponential sheaf can
simultaneously realize `(6)`, `(10)`, and `(13)`, or if its Green
residue is indefinite/nonconservative on the Burnol zero classes.

## 9. Smallest next theorem

Do not construct an unrelated coefficient sheaf.  The corpus already
has the arithmetic Tate--Milnor coefficient, the strict
Poisson--zeta comparison, and the finite derived Lagrangian
intersection.  The next theorem must enhance that existing object.

For a finite prime packet \(P\), form the exponential enhanced object
whose valuation component \(e=(e_p)_{p\in P}\) has phase
\[
 -h\sum_{p\in P}{e_p\over\varepsilon_p}
 =
 -h\log\!\left(\prod_{p\in P}p^{e_p}\right).              \tag{17}
\]
External tensor product adds phases, so `(17)` is compatible with
integer multiplication before completion.  Verdier duality reverses
the phase and supplies the reflected counterface.  The actual first
source-specific theorem is:

1. lift the analytic Calderón leg and the full relative
   Tate--Milnor Sullivan conormal leg to this enhanced exponential
   category;
2. prove their derived intersection commutes with finite-prime
   enlargement, residue/corestriction, and real orientation;
3. compute its moderate/rapid-decay nearby-cycle pair on the real
   adiabatic blow-up;
4. identify the moderate boundary with the already-constructed
   Poisson--zeta arithmetic complex, not merely with a new abstract
   sheaf; and
5. prove the source principal conormal maps conservatively into that
   moderate boundary.

Items 1--3 have substantial parent theory at each finite holonomic
stage.  Items 4--5 are the arithmetic, infinite-rank, RH-bearing
content.  In particular, merely constructing exponential enhanced
sheaves or invoking irregular-Hodge strictness would be theatre.

## 10. Novelty boundary

Real blow-ups, adiabatic deformation spaces, Poisson semigroups, WKB
actions, transseries, Hardy kernels, and Mertens asymptotics are parent
mathematics.  Exponential twists, irregular Hodge filtrations, wild
polarized twistor \(D\)-modules, enhanced ind-sheaves, and
moderate/rapid-decay nearby cycles on real oriented blow-ups are also
parent mathematics.  In particular, Sabbah--Yu prove strictness for
projective pushforward of exponentially twisted mixed Hodge modules,
and Hepler--Hohl construct moderate and rapid-decay nearby cycles of
enhanced ind-sheaves.  These results cover the category shape of a
finite exponential face; they do not cover the countable
ordinary-prime Ind-limit, Tate--Milnor incidence, Meyer comparison, or
source-conormal conservativity.

Candidate new mathematical knowledge is the exact two-scale synthesis
in Sections 1--3 and, if constructed, the source-selected
all-prime enhanced Tate--Milnor/Calderón nearby-cycle comparison.

## 11. Lean certificate

The dependency-closed scalar and finite-sequence core is formalized in
`GaloisForLFunctions.RHTower.Deninger.DeningerMertensAdiabaticCorner`.
It includes:

- \(\varepsilon_p=1/\log p\) and \(K_p(h,e)=p^{-he}\);
- finite-front, common-Tate-time, time-one, and boundary-jet
  identities;
- exact complex-valued derivative and WKB-action formulas; and
- flatness beyond every fixed logarithmic power along an abstract
  prime sequence.

The direct check

```text
lake env lean formal/GaloisForLFunctions/RHTower/Deninger/DeningerMertensAdiabaticCorner.lean
```

passes.  The final target audit

```text
lake build GaloisForLFunctions.RHTower.Deninger.DeningerMertensAdiabaticCorner
```

passes.  A separate `#print axioms` audit shows only
`propext`, `Classical.choice`, and `Quot.sound`.  The formal lint tool
finds no violation in this module; its repository-wide failure is due
to unrelated newly added modules not yet reachable from umbrella
imports.

## Gates

- [x] identify the arithmetic semiclassical parameter
      \(\varepsilon_p=1/\log p\)
- [x] prove the exact two-scale kernel
- [x] identify common Tate time as finite front-face coordinate
- [x] identify Mertens logarithmic grades as the zero-face conormal
- [x] identify formalized first-trace rate as the infinite-face WKB
      action
- [x] prove each prior one-category completion loses a proved face
- [x] freeze the exponential adiabatic completion conjecture
- [x] formalize the dependency-closed adiabatic corner theorem
- [x] identify enhanced irregular Riemann--Hilbert/nearby-cycle
      machinery as finite-stage parent theory
- [ ] independent specialist literature/priority audit
- [ ] lift the existing Tate--Milnor/Calderón intersection to the
      enhanced adiabatic category
- [ ] construct its strict countable-prime Ind-limit
- [ ] compute moderate/rapid boundary and Gamma transgression
- [ ] prove Meyer/co-Poisson Cauchy conservativity
- [ ] construct positive Green--Stokes boundary residue
- [ ] prove prime-dilation isometry
- [ ] prove RH

## Log

- 2026-07-28 — Introduced
  \(\varepsilon_p=1/\log p\) and proved that common Tate time,
  reciprocal-prime Hardy valuation, Mertens boundary jets, positive
  Euler corona erasure, and the Lean-certified first-trace
  rate-distortion grade are the finite/zero/infinite faces of
  \(\exp(-he/\varepsilon_p)\).  Froze the arithmetic exponential
  adiabatic Hodge-completion conjecture.
- 2026-07-28 — Formalized the dependency-closed two-scale source core
  and completed direct-file, axiom, and final module-build audits.
  Corrected the novelty boundary: exponential twists, wild polarized
  twistor modules, enhanced ind-sheaves, and moderate/rapid nearby
  cycles are parent theory.  Replaced the redundant “new coefficient
  sheaf” target by an enhanced lift of the already-constructed
  Tate--Milnor/Calderón derived intersection.

## Cross-card discharge note (2026-07-31)

The gate "construct its strict countable-prime Ind-limit" is discharged **at the moderate
level** by the moderation-selector card's formalized layer
(`RHTower/BilateralAllPrimeIndLimit.lean`): the strict countable-prime Ind-limit of the
bilateral gauge structure exists, suffers no countable-product moderation loss
(`allPrimeModerate_conormalFamily_iff`), and is rigid — the simultaneous sewing solution
space is one-dimensional (`allPrimeSewing_rigidity`), so the cofinal gauge trivializations
create no spurious moderate classes. What this card's rung still demands beyond that is the
**enhanced** (exponential/transseries) sector lift of the Tate–Milnor/Calderón intersection —
the part that must carry the flat-but-nonzero WKB data of face D, which the moderate sector
provably cannot see. The remaining ladder (moderate/rapid boundary, conservativity,
Green–Stokes residue, dilation isometry, RH) is the programme's declared conjectural core,
shared with `deninger-bilateral-prime-angle-moderation-selector` §6 and
`deninger-two-halves-do-not-compose` §10.

- 2026-07-31 — Cross-linked the moderate-sector Ind-limit discharge; verified
  `DeningerMertensAdiabaticCorner.lean` present, umbrella-registered (12 theorems).
