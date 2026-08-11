# Norming-face fusion mechanics

- **ID:** `ulf-nffm-field-programme`
- **Stage:** 1 — in progress
- **Type:** UNIVERSAL-LAW-FIELD MECHANISM PROGRAMME
- **Status:** `[MECHANISM FIRST] [FULL-FRONTIER GRAMMAR] [ONE PROVED FINITE CORE] [RH SELECTION OPEN]`
- **Frontier source:** `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`

## 1. Pivot

The live routes do not ask for one missing object. They repeat one operation pattern:

1. a source intervention generates several marked effects before normalization;
2. each route fuses some effects and forgets their separate provenance;
3. a calibrator certifies a direction, sign, boundary value, or admissible cone;
4. one calibrator may certify each effect separately but fail to certify them jointly;
5. completion or scalarization records the fused resultant and loses the incompatibility;
6. a cofinal route can pass every fixed test while its required calibrator dimension escapes.

The proposed field mechanism studies this **generation--calibration--fusion exchange**.  Norms,
cones, phases, moment matrices, boundary currents, and positive carriers are local gauges of the
mechanism, not its definition.

## 2. Grammar extracted from the full frontier

For a generated finite packet `(v_i)` in a normed real vector space, define

\[
E(v)=\sum_i\|v_i\|,\qquad
R(v)=\left\|\sum_i v_i\right\|,\qquad
\Delta(v)=E(v)-R(v).
\tag{NFF.1}
\]

`E` is source-marked generation envelope. `R` is coherently fused execution. `Delta` is fusion
defect. A calibrator is a dual functional `phi` with `||phi||<=1`; its local residual is

\[
\rho_\phi(v_i)=\|v_i\|-\phi(v_i)\ge0.
\tag{NFF.2}
\]

This vocabulary compresses the five frontier classes without identifying their receivers:

| Frontier class | Generated effects | Local calibrator | Fusion failure |
|---|---|---|---|
| singular source descent | prime/depth and reflected boundary components | bounded source functional compatible with fixed landing | individually retained components have no joint source annihilator |
| all-prime oscillatory transport | centered prime or Möbius amplitudes | phase/cut functional | absolute envelope survives while coherent sum lacks uniform cancellation |
| adaptive spectral orientation | signed rank-one or hyperedge responses | contraction/sign operator | current positive faces do not jointly orient the self-selected next face |
| whole-space coercivity | ground-profile escape components | norming ground-state witness | each seed is controlled but no common coercive calibration controls all profiles |
| positive carrier existence | finite positive approximants | probability/Markov norming functional | local carriers exist without one tight common carrier |

The repeated open question is therefore not “find another source-native object.” It is:

> Which source law forces a common calibrator for a generated packet, how does incompatibility
> move under fusion and observation, and when must calibrator complexity escape every finite
> receiver?

## 3. Candidate laws

### Law I — calibration variational law

The fusion defect is the least total residual of one calibrator:

\[
\Delta(v)=\min_{\|\phi\|\le1}\sum_i\rho_\phi(v_i).
\tag{NFF.3}
\]

Consequently `Delta(v)=0` exactly when all generated effects share one norming functional.

### Law II — refinement conservation

For any partition into blocks `B_j`, with block resultants `s_j=sum_(i in B_j)v_i`,

\[
\Delta(v)=\sum_j\Delta(v|_{B_j})+\Delta((s_j)_j).
\tag{NFF.4}
\]

Local cancellation plus cancellation between locally fused resultants exactly conserves total
fusion defect. Reparenthesizing a construction changes where defect is registered, not its total.

### Law III — observer exchange

For a linear contraction `T`, put `L_T(x)=||x||-||Tx||`. Then

\[
\Delta(v)-\Delta(Tv)
=\sum_iL_T(v_i)-L_T\!\left(\sum_i v_i\right).
\tag{NFF.5}
\]

An observer may erase or create apparent incompatibility. The exact exchange term records whether
it loses more norm separately or after fusion.

### Law IV — bounded witness arity

Let `dim V=d`. The norming sets

\[
N(v_i)=\{\phi:\|\phi\|\le1,\ \phi(v_i)=\|v_i\|\}
\tag{NFF.6}
\]

are nonempty compact convex faces of the dual ball. Helly's theorem therefore gives:

\[
\Delta(v)>0
\Longrightarrow
\text{some subpacket of size at most }d+1\text{ has positive defect}.
\tag{NFF.7}
\]

Every minimally defective packet in a `d`-dimensional receiver has at most `d+1` effects.

### Law V — calibration-dimension escape

If a cofinal family has minimally defective packets of unbounded cardinality, no fixed
finite-dimensional normed receiver can represent its legality by common norming functionals.
Every faithful receiver family has unbounded dimension. Any common normed receiver is
infinite-dimensional, so its closed unit ball is not norm compact.

This is a precise mechanism by which all-degree generation or hypertranscendental prolongation can
force noncompactness. Hypertranscendence is not declared equal to noncompactness; unbounded
minimal calibration arity is the typed bridge.

## 4. Three exact local gauges and one prediction

### 4.1 Oscillatory gauge

Take `V=C` as a real Euclidean plane. A calibrator is
`phi_u(z)=Re(conj(u)z)`, `|u|<=1`. Perfect fusion means all nonzero amplitudes have one phase.
`Delta=sum|a_i|-|sum a_i|` is exact phase-cancellation budget.

### 4.2 Incidence/transport gauge

Take `V=l1(P)` on a finite port set and effects
`v_e=q_e(delta_(head e)-delta_(tail e))`, `q_e>0`. Then

\[
\Delta=2\sum_e q_e-\|\operatorname{div}q\|_1.
\tag{NFF.8}
\]

A common calibrator is a potential in the `l_infinity` unit ball taking value `-1` at every active
tail and `+1` at every active head. A directed two-edge path already obstructs such a calibration
at its middle vertex. This is exact capacity/boundary fusion, not a phase analogy.

### 4.3 Spectral/null-face gauge

Take self-adjoint matrices with trace norm. For rank-one signed responses
`A_i=s_i u_i u_i^*`, a common calibrator is a self-adjoint contraction acting by `+1` on every
positive feature and `-1` on every negative feature. Such a calibrator exists exactly when the
positive and negative feature spans are orthogonal. The trace-norm fusion defect measures exact
spectral cancellation between incompatible signed responses.

### 4.4 Fourth-organ prediction

An all-degree adaptive hyperedge obstruction, all-prime cancellation obstruction, or whole-ground
escape that is irreducible on packets of unbounded size cannot be controlled by a fixed finite
moment matrix, fixed finite frequency band, or fixed finite port space. It must manifest as
unbounded calibration dimension or failure of compactness/admission in the limit.

This is falsifiable. One fixed finite-dimensional common-calibrator realization of such an
unbounded minimal-obstruction family kills the programme.

## 5. Hostile failures and survivors

1. **Arbitrary failure kernels have a Helly law — false.** The corpus realizes every finite
   clutter as a static failure system. Law IV survives only because norming sets are convex faces
   generated by one shared norm.
2. **A positive defect has a universal quantitative gap — false.** In `C`, the packet
   `(1,exp(i epsilon))` has no common calibrator for nonzero `epsilon`, but its defect tends to zero.
   Quantitative bounds require a modulus of convexity, a separation margin, or another sourced
   metric.
3. **Positive observation can only reduce defect — false.** A contraction may lose more after
   fusion than before or conversely. Only the exact exchange identity `(NFF.5)` is universal.
4. **Positivity or Gram form supplies orientation — false.** Pure positive matrices share the
   identity calibrator and have zero defect. Orientation appears only when signed/generated
   components are retained before positive fusion.
5. **Bounded witness arity holds in infinite dimension — false.** The Helly number grows with
   calibration dimension. Infinite-dimensional quantitative replacement requires additional
   geometry; current work on Helly approximation properties confirms this boundary.
6. **Common calibration selects RH — false.** It becomes RH-bearing only after one literal
   pre-divisor source packet and its route landings are constructed independently of zero
   location.

## 6. Research programme

1. Construct coefficient-faithful intervention maps from one pre-zero arithmetic source into at
   least three live organs.
2. Prove their generated effects share one source norm or support functional before completion.
3. Compute refinement and observer-exchange defects under route comparisons.
4. Prove a cofinal lower bound on minimal incompatible-packet arity or exhibit a global common
   calibrator.
5. Only then ask whether the source-selected common calibrator forces horizontal neutrality.

## 7. RH selection gate

The finite law does not prove RH. The exact remaining selection theorem has the following shape:

> Build a pre-divisor arithmetic packet whose generated effects include the retained R/L
> orientations, centered T/E transport, and adaptive U/C1 boundary responses. Prove source laws
> make every finite packet jointly calibratable with a cofinally compatible calibrator. Prove any
> off-critical divisor creates one finite incompatible witness. Then `(NFF.7)` excludes that
> divisor.

The first two sentences are open. No endpoint equivalence may be used to define the norm,
calibrator, or packet.

## 8. Parent mathematics

Hahn--Banach norming functionals, subdifferentials of norms, triangle-equality geometry, and
Helly's theorem are classical. Quantitative infinite-dimensional extensions require additional
Banach geometry; current nearby work includes Ivanov's
[no-dimensional Helly theorem](https://arxiv.org/abs/2409.05744),
[Helly approximation property](https://arxiv.org/abs/2603.22743), and Ivanov--Kadets
[optimality results](https://arxiv.org/abs/2607.04093). The field claim is the source/intervention
interpretation and the demanded cross-organ arithmetic realization, not ownership of those
ingredients.
