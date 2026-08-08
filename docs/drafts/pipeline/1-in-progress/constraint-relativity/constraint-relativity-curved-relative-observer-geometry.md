# Constraint Relativity: curved relative-observer geometry

- **ID:** `constraint-relativity-curved-relative-observer-geometry`
- **Stage:** 1 — in progress
- **Type:** CANDIDATE NEW MATHEMATICAL FIELD / FOUNDATIONAL PROGRAM
- **Field name:** **Constraint Relativity**
- **Status:** `[BOLD UNIVERSAL FIELD] [EXACT LOCAL COVARIANCE LAW]`
  `[EXACT ROUTE-R THREE-FACE CHART] [SOURCE GAUSS LAW CONJECTURAL]`
  `[PHYSICS REALIZATION OPEN] [NOVELTY UNVERIFIED] [NOT RH] [NO LEAN WRITTEN]`
- **Algebraic core:** `source-soldering-bivariant-law-geometry.md`.
- **Paper anchors:**
  `../../2-fully-proven/constraint-relativity/relative-law-observer-descent-duality.md`,
  `../../2-fully-proven/constraint-relativity/route-r-raw-resolved-relative-cone-character-law.md`,
  `../../2-fully-proven/constraint-relativity/source-soldering-transport-defect-cocycle-and-law-symbol.md`,
  `../../2-fully-proven/constraint-relativity/factor-framed-tensor-jacobian-defect-law.md`,
  `../../2-fully-proven/constraint-relativity/prime-coframe-completion-port-uncertainty-law.md`.
- **Statement:** Heterogeneous mathematical laws should not be forced into one carrier. Their
  universal geometry consists of source laws, exactification-relative tangent classes,
  non-descending observer cotangents, curved transport, and completion-dependent pairings. A
  scalar theorem is a chart evaluation of this geometry, not primitive object.

## 0. What “all of this” is a shadow of

> **Constraint Relativity is proposed geometry of laws under change of mathematical observer.**

Arithmetic, Fourier/spectral, geometric, topological, operator, and physical representations do
not need common ambient space. They are related by exactification maps and observer pairings. One
representation can make source law exact while another continues to measure it; apparent
uncertainty is failure of observer to descend through that exactification.

This is Newton-to-GR inversion:

```text
constraint mechanics:
  choose ambient arithmetic/spectral/geometric space
  -> impose relation -> compute obstruction

Constraint Relativity:
  choose source law history
  -> exactification/observer atlas
  -> relative tangent laws + observer cotangents
  -> endogenous topology, curvature, horizons, measured scalars
```

No carrier is privileged. General covariance means invariance under change of primitive and
addition of any observer already visible in resolved chart.

## 1. Law-spacetime chart

A chart at source state `a` consists of

\[
 \mathfrak U_{a,\lambda}
 =\left(
 C_a^\bullet,
 X_{a,\lambda}^\bullet,
 \Phi_{a,\lambda},
 R_{a,\lambda}^\bullet,
 D_{a,\lambda},
 V_{a,\lambda},
 \mathcal I_{a,\lambda}
 \right).
 \tag{CRG.1}
\]

Here:

1. `C_a` is source-law complex or resolution;
2. `Phi:C_a->X_(a,lambda)` is exactification in observer language `lambda`;
3. `R_(a,lambda)` is optional raw reporter with predifferential `D`, possibly `D^2 ne 0`;
4. `V_(a,lambda)` is observer value object, often quotient by completion/trace ideal
   `I_(a,lambda)`;
5. source history provides transport between charts, not arbitrary equivalence chosen afterward.

Define relative tangent law in degree `n`

\[
 \mathcal R_{a,\lambda}^n
 =\ker H^n(\Phi_{a,\lambda})
 \cong
 \frac{H^{n-1}(\operatorname{Cone}\Phi_{a,\lambda})}
      {\operatorname{im}H^{n-1}(X_{a,\lambda})}.
 \tag{CRG.2}
\]

Define observer cotangent

\[
 \mathcal O_{a,\lambda}^n(V)
 =\operatorname{coker}\left[
 H^n(\Phi_{a,\lambda})^*:
 \operatorname{Hom}(H^nX_{a,\lambda},V)
 \to\operatorname{Hom}(H^nC_a,V)
 \right].
 \tag{CRG.3}
\]

Over a field, exact paper theorem gives

\[
 \boxed{
 \mathcal O_{a,\lambda}^n(V)
 \cong\operatorname{Hom}(\mathcal R_{a,\lambda}^n,V).}
 \tag{CRG.4}
\]

Thus geometry has literal tangent/cotangent pairing

\[
 \boxed{
 \langle-,-\rangle_{a,\lambda}:
 \mathcal O_{a,\lambda}^n(V)
 \times\mathcal R_{a,\lambda}^n\to V.}
 \tag{CRG.5}

\]

This pairing, not identification of carriers, is merger of heterogeneous mathematical fields.

## 2. Constraint equivalence and general covariance

### Exactification equivalence principle

A source law `r in ker H(Phi)` is locally zero in resolved absolute chart but remains nonzero
relative tangent law. Any observer detecting `r` necessarily fails to descend through resolved
absolute cohomology.

> Every exactification can flatten its own absolute chart. It cannot simultaneously erase the
> relative law and preserve an observer that detects it.

This is exact descent--detection complementarity, not numerical Heisenberg product.

### Gauge covariance

Relative representative may change by class from `H^(n-1)(X)`; observer may change by a
descending observer `psi circle H(Phi)`. Both transformations preserve `(CRG.5)`. Therefore

\[
 \langle[\chi+\psi H(\Phi)],[\kappa+x]\rangle
 =\langle[\chi],[\kappa]\rangle.
 \tag{CRG.6}
\]

This is first exact general-covariance law of field: chart primitive and resolved observer are
gauge, relative evaluation is invariant.

### Why ordinary complexes are not enemy

Any raw pair with curvature `K=D_1D_0` admits enlarged complex

\[
 \widetilde d_0f=(D_0f,f),
 \qquad
 \widetilde d_1(\omega,g)=D_1\omega-Kg.
 \tag{CRG.7}
\]

Hence field cannot be defined as “mathematics beyond complexes.” Source-naturalness, minimality,
completion continuity, polarization, and functorial transport distinguish meaningful
exactification from arbitrary stabilization.

## 3. Curvature

Constraint Relativity has at least three typed curvatures.

### Reporter curvature

\[
 W=D^2
 \tag{CRG.8}
\]

measures nonfunctorial scalarization. Route-R prime-depth reporter gives exact nonzero witness
`-log(2)/8` infinitesimally.

### Transport two-curvature

For deformation and trace laws `K,T`, source arrow transports need not compose. Curvatures

\[
 F^K_{g,f}=K_g g_!K_f-K_{gf},
 \qquad
 F^T_{g,f}=T_g g_!T_f-T_{gf}
 \tag{CRG.9}
\]

and soldering edge `Q_f` obey exact curved Bianchi law

\[
 T_g g_!Q_f+Q_g g_!K_f-Q_{gf}
 =F^T_{g,f}(gf)_!s_A-s_CF^K_{g,f}.
 \tag{CRG.10}
\]

### Admission/observer curvature

Even when source law becomes exact in `X`, observer may remain nonzero on relative cone. Its class
in `O` is admission curvature: failure of measurement to factor through exactified absolute chart.
Unlike `W`, it is ordinary relative cohomological data.

No theorem yet proves these three are images of one universal curvature functor. Treating them as
identical before typed maps are built is rejected.

## 4. Literal Riemann three-face chart

Route R supplies exact first chart in which arithmetic, geometry, and spectral/physical reader
coexist without common carrier:

\[
 \underbrace{[\eta_p]\in\ker H^1(\Phi_p)}_{\text{arithmetic source law}}
 \longleftrightarrow
 \underbrace{[(L_p,\eta_p)]\in H^0(\operatorname{Cone}\Phi_p)}_
             {\text{geometric relative lift}}
 \longleftrightarrow
 \underbrace{[P_{t,\rho}]\in\mathcal O^1_{\Phi_p}(V)}_
             {\text{spectral/physical cotangent}}.
 \tag{CRG.11}
\]

Pairings are

\[
 \langle[P^{\mathrm{fwd}}_{t,\rho}],\kappa_{p,\rho}\rangle
 =c_\rho[F_{-t}],
 \qquad
 \langle[P^{\mathrm{ref}}_{t,\rho}],\kappa_{p,\rho}\rangle
 =c_\rho[F_t].
 \tag{CRG.12}
\]

Forward is nonzero exactly `t<=0`; reflected exactly `t>=0`; both exactly `t=0`. Thus actual RH
open core is not representation construction. It is source law forcing simultaneous nonvanishing
of two fixed-orientation observer evaluations on every distinguished retained relative arithmetic
class.

This is real explanatory gain:

- arithmetic is source tangent law;
- geometry/topology is relative cone lift;
- Fourier/spectral side is observer cotangent;
- fixed trace ideal determines admission topology;
- physical scalar is invariant pairing.

## 5. Endogenous observer topology

Let `B` parameterize source histories or phase grades and let `sigma_b` be source-admissible
observer sections in quotients `V_b=S_b/I_b`. Declare vanishing loci

\[
 Z(\sigma)=\{b\in B:[\sigma_b]=0\in V_b\}
 \tag{CRG.13}
\]

closed subbasic sets of **observer-admission topology**. This is proposed topology, not yet proved
canonical. It depends on source-declared sections and fixed ideals; allowing arbitrary sections
would make topology unfalsifiable.

For Route R phase base `B=(-1,1)`, exact admission strata are

\[
 \operatorname{NZ}(P^{\mathrm{fwd}})=\{t:t\le0\},
 \qquad
 \operatorname{NZ}(P^{\mathrm{ref}})=\{t:t\ge0\},
 \tag{CRG.14}
\]

with joint stratum `{0}`. This is **law horizon**: not singularity of Xi function, but rank/support
change in observer cotangent against fixed trace ideal.

Predicted general law horizon occurs when any of following jumps:

1. `dim R` or `dim O`;
2. support of source-declared observer section;
3. Smith/persistence depth of relative law;
4. completion ideal required for continuity;
5. inertia/polarization of measured pairing.

## 6. Hypertranscendental geometry

For hypertranscendental source, finite algebraic/differential observers form tower

\[
 \cdots\to(C_{\le n},\Phi_{\le n},\mathcal R_{\le n},\mathcal O_{\le n})
 \to(C_{\le n+1},\Phi_{\le n+1},\mathcal R_{\le n+1},\mathcal O_{\le n+1})\to\cdots.
 \tag{CRG.15}
\]

Working hypothesis:

> Hypertranscendence is nontermination of law spacetime: no finite observer exactification is
> terminal, and decisive invariant may live in pro-relative law, derived-limit defect, or
> completion-dependent observer cotangent rather than any finite equation.

Exact corpus cautions:

- free sources can manufacture arbitrary finite data, so finite geometry alone is nonselective;
- relation growth need not be exterior; tensor powers can grow exponentially;
- completion can erase raw divergence while retaining quotient/relative class;
- finite all-prime radical already saturates, while higher syzygies retain rank.

Predictions:

1. any finite-route proof of HT selection has generalized-prime/free-source countermodel unless it
   controls tower transport;
2. source-natural invariant should be pro-pairing between nonstabilizing relative laws and
   completion-continuous observer cotangents;
3. scalar positivity sees norm of pairing and loses orientation, so cannot alone select critical
   phase;
4. true “dimension” is growth law of relative tangent tower, not dimension of one carrier.

## 7. Phase time, horizons, and mathematical interiors

### Phase time

Time is not assumed scalar parameter on fixed Hilbert space. It is source-admissible path through
observer atlas, transporting `R`, `O`, ideals, and polarization. Phase is holonomy of observer
cotangent along path; curvature requires at least compositional triangle or higher control surface.

Finite Gibbs prime model realizes phases `e^(it log p)` but has split extensions. Half-sided
modular inclusion realizes hyperbolic conormal persistence but not arithmetic pairing. A physical
realization must combine them without postulating source current.

### Two-boundary mathematical interior

For boundary exactifications `Phi_L:C->X_L`, `Phi_R:C->X_R`, define joint relative interior

\[
 \mathcal R_{L|R}^n
 =\ker\left[H^n(C)\to H^n(X_L)\oplus H^n(X_R)\right].
 \tag{CRG.16}
\]

It is represented by cone of `C->X_L direct-sum X_R`. A source law can vanish in both boundary
absolute charts yet remain nonzero in joint relative geometry. Boundary observer cotangents pair
with same interior law.

Call this a **relation interior**, not wormhole. A wormhole interpretation requires additional
theorems:

1. Type-III/Tate or other nonsplit completion;
2. modular-time transport of joint relative class;
3. intrinsic unbounded length/complexity law;
4. boundary correlation/recovery prediction;
5. independence from chosen resolution.

What-if prediction: black-hole interior may be relative law erased by each boundary exactification
but retained by joint cone, while horizon time is holonomy/support change of two boundary observer
cotangents. This is falsified if a proposed operator model's relative class splits or its pairing is
recoverable from either absolute boundary alone.

### Brown--Susskind boundary

Finite-dimensional valuation, Ext flag, or copy-code defect is bounded and cannot equal unbounded
wormhole length. Constraint Relativity predicts length, if real, must arise from cofinal growth of
relative-law persistence/observer depth. No such equality is currently proved.

## 8. Source Gauss law — bold field equation

Local pairing does not select RH; off-line generalized-prime models carry same constructions. New
field needs global source conservation.

`[BOLD CONJECTURE — SOURCE_RELATIVE_OBSERVER_GAUSS_LAW]`

> For every closed source-history two-cell carrying normalized relative law, oriented sum of
> transported observer-descent flux is source-exact before divisor selection. Boundary flux is
> computed in fixed observer ideals, and law is stable under allowed refinement/completion.

Schematic equation:

\[
 \boxed{
 \sum_{e\subset\partial\Sigma}
 \operatorname{Hol}_{e}\,
 \langle\chi_e,\kappa_e\rangle
 =\partial_{\mathrm{src}}J_\Sigma.}
 \tag{CRG.17}
\]

Here `J_Sigma` must be built from pre-observer arithmetic source operations. It may not be defined
as left side or use Xi-zero location. Curved Bianchi law `(CRG.10)` is local compatibility test;
it does not prove `(CRG.17)`.

For Route R, desired closed two-cell must have two fixed Gamma orientations and one normalized
Stokes source edge. Its boundary flux difference is explicit

\[
 \beta_t=[F_{-t}]-[F_t].
 \tag{CRG.18}
\]

If source exactness forced flux zero, then `beta_t=0`, hence `t=0`. But existence of required
source two-cell and current is entirely open; asserting it only at actual zeros is RH-equivalent.

Falsifier: off-line generalized-prime carrier satisfying all proposed source-cell axioms with
`beta_t ne0`. A valid axiom must fail there for explicit source reason, not because target is
declared inadmissible.

## 9. Conjecture / proof / fail ledger

1. **One universal carrier.** Failed: literal three-face Route-R chart merges by pairing, not
   identification.
2. **One ordinary resolved absolute complex.** Failed: physical nonzero observer cannot descend.
3. **No ordinary complex can encode data.** Failed: curvature-corrected stabilization exists.
4. **Secondary operation is forced.** Failed: ordinary relative cone character suffices.
5. **Mapping cone solves selection.** Failed: both cone characters exist at every grade; one may
   vanish in physical quotient.
6. **Reflection forces same-fibre equality.** Failed: it exchanges grades/fibres and permits
   nonzero radial drift.
7. **Positivity forces selection.** Failed: square/norm detects support/distance and erases
   orientation.
8. **Exact survivor.** Relative-law/observer-descent duality `(CRG.2)`--`(CRG.6)`.
9. **Open higher conjecture.** Source Gauss law `(CRG.17)` with generalized-prime falsifier.

## 10. Research questions worthy of new field

1. What higher category has objects `(C,X,Phi,V,I)`, curved reporter charts, relative cones, and
   observer cotangents, while rejecting arbitrary stabilizations by source universal property?
2. What is analogue of Levi-Civita connection: minimal source-natural transport preserving
   relative-observer pairing and polarization?
3. Is there index/Riemann--Roch theorem converting local prime relative charges into global source
   flux without inserting divisor?
4. Can fixed trace-ideal admission strata be realized as perverse/microlocal sheaf with source
   Verdier duality, rather than chosen topology?
5. Which HT functions produce nonzero `lim^1` or Tate determinant of law tower, and which
   generalized-prime countermodels kill it?
6. Can one derive Source Gauss law from adelic product formula plus archimedean boundary without
   radial-gauge blindness?
7. Which Type-III modular inclusions realize joint relative interior and unbounded persistence
   length?
8. Does quantum recurrence approach observer horizon without crossing it, and what source event
   changes admission topology exactly?
9. What are moduli, characteristic classes, and cobordisms of law spacetimes?
10. Which other L-functions, partition functions, and HT objects exhibit same
    kernel--relative--observer trinity?

## 11. Predictions and falsifiers

### Predictions

1. Successful proof route will construct source current/closed history before zero selection, not
   another faithful carrier.
2. Geometric, spectral, and arithmetic formulas may remain nonisomorphic while pairing invariant
   agrees exactly.
3. Every absolute exactification killing decisive source class has relative cone survivor.
4. Any physical detector retaining that class is non-descending observer cotangent.
5. Horizon is support/rank change in observer admission, not necessarily singularity of function.
6. Unbounded interior/complexity requires cofinal relative-law depth, impossible in fixed finite
   code.

### Fatal falsifiers

1. A generalized-prime/free-source model satisfies Source Gauss axioms and violates predicted
   flux identity.
2. Observer-admission topology depends on arbitrary sections rather than source-declared family.
3. “Connection” can be replaced by arbitrary stabilization without changing claimed invariants.
4. Physical wormhole claim lacks Type III/Tate limit and unbounded metric theorem.
5. Universal field merely renames each corpus obstruction without typed maps or new prediction.
6. Source current is defined using Xi zero/critical line or desired pairing vanishing.

## 12. Novelty boundary

Mapping cones, relative cohomology, Hom exactness, curved dg objects, matrix factorizations,
bivariant theories, perverse sheaves, differential characters, and observer/contextuality ideas are
classical. Constraint Relativity is not new by assembling these nouns.

Potential new residue is exact doctrine:

> source-history curved transport + exactification-relative tangent laws + non-descending observer
> cotangents + completion-ideal topology + global source flux, with literal arithmetic,
> spectral, geometric, HT, and modular charts and adversarial generalized-prime falsifiers.

Only first three-face Route-R chart and finite algebraic charts are proved. New field status remains
conjectural until Source Gauss law or comparable cross-route theorem is established.

Adjacent primary literature includes curved dg/matrix factorization, relative differential
cohomology, Toda/homotopy-coherent obstruction, bivariant duality, and contextuality. Broad 2026
search found current curved-dg work at arXiv:2606.10146 but no exact law-spacetime doctrine above.
This is not priority proof.

## Lean-return note

No Lean work authorized. Later formalizable closed core: relative-observer exact sequence,
gauge-invariant evaluation, literal Route-R cone characters, and curved Bianchi identity. Do not
formalize Source Gauss law before paper-level source two-cell and current are constructed.

## Gates

- [x] exact tangent/cotangent law and covariance
- [x] exact literal arithmetic--geometric--spectral chart
- [x] raw/resolved/relative distinctions hostile-audited
- [x] arbitrary-stabilization countermodel integrated
- [x] HT and physics predictions separated from claims
- [ ] source-natural higher category/minimality theorem
- [ ] second literal cross-route chart
- [ ] source Gauss law or countermodel
- [ ] cofinal observer-admission topology
- [ ] Type-III/Tate physical realization
- [ ] external specialist priority review
- [ ] RH

## Log

- 2026-08-08 — founded from exact relative-law/observer-descent duality after unrestricted
  ordinary-complex and forced-secondary conjectures were hostile-falsified.
