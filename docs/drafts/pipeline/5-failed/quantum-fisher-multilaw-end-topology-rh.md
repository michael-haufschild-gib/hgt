# Failed quantum Fisher multi-law end topology for RH

- **ID:** `qfi-multilaw-end-topology`
- **Stage:** 5 — failed / retired
- **Type:** FAILED / BOTH CONTROLLED QFI CIRCLES ARE UNIVERSAL ON THE STRICT-LEFT STRIP
- **Statement:** Finite convolution overflow and continuation--recovery interaction form two
  separately sourced coordinates whose total is the formation/recovery defect.  Controlled
  relative phase converts their compensated escape into QFI limit `4`.  The proposed global route
  required that circle to occur only at zeros, so that an off-critical zero would create an
  exceptional two-cycle together with the universal formation-head/correction circle.  Lean proves
  the opposite: at every open-strip point with real part below `1/2`, zero or nonzero, overflow is
  not tail bounded and has a strict subsequence on which the interaction-to-overflow ratio tends to
  `-1` and relative-phase QFI tends to `4`.  Both leading circles therefore describe generic
  left-half escape.  No exceptional global QFI topology remains.  Extracting the finite zeta value
  from a subleading rescaling would only restate scalar cancellation, so the route is retired under
  its source and QFI-essentiality rules.

## Research question

Can the arithmetic source determine the **global topology of its QFI metric completion** strongly
enough that all joint formation/recovery failures occur at the fixed seam, without using a sign
inequality, a uniqueness principle, an operator-eigenvalue model, or a renamed zero-free condition?

The route is about two distinct infinities:

1. cutoff infinity, where finite arithmetic experiments assemble the completed process;
2. recovery infinity, where the Möbius channel leaves every finite-output chart.

The desired theorem says cutoff infinity may create seam-attached recovery ends but cannot create
closed recovery-end components in the interior of the reflected quotient.

## 1. Source processes, before zeros

Work on the open critical strip

```text
S = {s in C | 0 < Re(s) < 1},
tau(s) = 1 - conjugate(s),
Sigma = Fix(tau) = {Re(s)=1/2}.
```

Use four laws with different source meanings.

### Formation

`F_N(s)` is the literal finite arithmetic continuation already represented by
`finiteCutoffZeta N s`.  The corpus proves compact-local convergence to `zeta(s)` on
`Re(s)>0`, away from the pole.

### Recovery

At coefficient level, `1(n)=1` and `mu(n)` are specified independently and satisfy

```text
1 * mu = delta_1
```

under Dirichlet convolution.  In the absolute-convergence chamber their transforms satisfy

```text
F(s) R(s) = 1,       F(s)=zeta(s),       R(s)=sum mu(n)n^(-s).
```

The recovery germ on the punctured strip is therefore the unique meromorphic continuation of the
Möbius process, not an extra copy of the formation readout.  A valid route still needs a concrete
regularized family `R_N` derived from finite Möbius data and the same continuation operations used
for `F_N`.  Defining `R_N := 1/F_N` does **not** pass this source gate.

The literal head

```text
B_N(s) = sum_{1 <= n <= N} mu(n)n^(-s)
```

also fails.  At every nontrivial zero `rho`, its norm is at most `N`, while
`finiteCutoffZeta N rho` is `O(N^-2)`.  Hence

```text
finiteCutoffZeta N rho * B_N(rho) -> 0,
finiteCutoffZeta N rho * B_N(rho) - 1 -> -1.
```

This is now unconditional in Lean.  The failure is stronger.  For every fixed `k`, let

```text
B_N^[k](s) = sum_{1 <= n <= N} mu(n) (log n)^k n^(-s).
```

For any fixed `K` and fixed complex coefficients `a_0,...,a_K`, Lean proves at every nontrivial
zero `rho` that

```text
F_N(rho) * sum_{k <= K} a_k B_N^[k](rho) -> 0,
F_N(rho) * sum_{k <= K} a_k B_N^[k](rho) - 1 -> -1.
```

Thus no fixed finite differential jet of the raw recovery can generate recovery infinity.  A live
process must use cofinal order, a nonlocal cutoff interaction, or the full labelled overflow.  A
correction chosen merely to make the product converge to one would insert the target identity and
fails the source gate.

### Canonical two-component boundary law

Let `H_N` be the literal constant-coefficient Dirichlet head, `B_N` the Möbius head, and `O_N` the
complete rectangle-overflow term.  Let

```text
C_N = F_N - H_N,
V_N = (O_N, C_N B_N).
```

Finite convolution gives, for every `N` and every complex `s`, including the empty cutoff,

```text
H_N B_N = 1_{1 <= N} + O_N,
sum(V_N) = F_N B_N - 1_{1 <= N}.                         (QME.0)
```

Both identities are unconditional in Lean.  At every nontrivial zero,

```text
sum(V_N(rho)) -> -1.                                     (QME.0z)
```

This is first genuinely multi-law datum: `O_N` comes from multiplicative pairs crossing cutoff;
`C_N B_N` couples analytic continuation correction to independent Möbius recovery.  Their finite
total does **not** by itself prove either coordinate escapes.  Source arithmetic now proves more:
`O_N` is not tail bounded at every strict-left open-strip point, without a zero premise.  A strict
subsequence then gives compensated two-coordinate escape and balanced relative-phase QFI.  This
creates a genuine QFI end but also proves that its leading topology is zero-blind.

### Universal compensating infinity and its first-boundary no-go

There is a simpler pair whose escape can be proved completely.  Keep `H_N` and let

```text
C_N = F_N - H_N,
K_N(s) = (1-s) N^(s-1).
```

For every fixed point `s` of the open strip, Lean now proves

```text
K_N(s) H_N(s) -> 1,             |H_N(s)| -> infinity,
K_N(s) C_N(s) -> -1,            |C_N(s)| -> infinity,
H_N(s) + C_N(s) = F_N(s) -> zeta(s).                    (QME.U)
```

Thus formation head and continuation correction are two separately defined laws with genuine,
oppositely directed infinities.  At a nontrivial zero their finite compensated total additionally
darkens.  This is the first unconditional realization of the requested multiple-process failure
at infinity.

It also falsifies the naive topological claim.  The leading antidiagonal boundary in `(QME.U)` is
present over the entire open strip, not only over zeros.  Ordinary product-QFI completion therefore
adds a universal boundary family and cannot locate zeros from that first boundary alone.  Zero
information survives only in the finite compensated remainder.  A viable refinement must either
derive a QFI-native higher-contact boundary that retains this remainder without merely renaming
`F_N`, or return to the zero-specific escape problem for `(O_N,C_N B_N)`.

### Universal two-process escape on the strict-left half

The exact overflow pair escapes at every strict-left open-strip point.  Lean proves

```text
for every R and N_0, there is N >= N_0 such that
  |O_N(s)| > R,                                         0 < Re(s) < 1/2.
```

Proof is finite and coefficient-native.  If `O_N` were bounded on a tail, then
`H_N B_N = 1+O_N` would be bounded.  Combining this with
`(1-s)N^(s-1)H_N -> 1` forces `N^s B_N -> 0`.  The same holds with `(N+1)^s`.  But the exact
successor identity

```text
(N+1)^rho (B_(N+1)-B_N) = mu(N+1)
```

would force the Möbius values to vanish asymptotically, contradicting `mu(p)=-1` at arbitrarily
large primes.  Along an extracted strict subsequence, `|O_N| -> infinity`.  Since `F_N/H_N -> 0`
and `H_NB_N/O_N -> 1`, the actual continuation--recovery interaction satisfies

```text
(C_N(s)B_N(s))/O_N(s) -> -1,
I_rel(O_N(s), C_N(s)B_N(s)) -> 4.                       (QME.L)
```

No zero identity enters.  What first appeared to be an off-critical-zero end is the generic
leading end of the entire strict-left strip.  This is the route's decisive no-go.

### Gluing defect

For an admissible finite recovery family define

```text
D_N(s) = F_N(s) R_N(s) - 1.
```

`D_N` records failure of finite formation and recovery to realize their infinite convolution law.
The target regime is `D_N -> 0` away from recovery ends.  It must be proved from finite coefficient
identities, including the overflow terms created by truncation.

These are not scalar multiples of one analytic output.  Formation aggregates the constant
coefficient law, recovery aggregates the Möbius recurrence, overflow retains every crossed
multiplicative pair, and the continuation interaction records how the finite analytic correction
couples to recovery.  Equation `(QME.0)` proves their relation without identifying their source
roles.

## 2. Exact multi-law meaning of a zero

At every nontrivial zero `rho`, literal finite formation darkens quadratically and the exact
boundary charge remains nonzero:

```text
F_N(rho) -> 0,
sum(V_N(rho)) -> -1.
```

The intended joint failure has four parts:

1. formation loses invertibility;
2. rectangle overflow crosses every bounded output set cofinally;
3. continuation--recovery interaction crosses the same thresholds at the same cutoffs;
4. their sum retains finite charge `-1`.

Parts 1 and 4 hold at every nontrivial zero.  Parts 2 and 3 are Lean-proved at every strict-left
zero, hence at one member of every hypothetical off-critical orbit.  This is cofinal joint
noncompactness, not eventual escape or a QFI-Cauchy end.  The hard producer has moved: derive a
canonical quantum transition history from labelled cutoff updates, then determine its global QFI
completion without inferring history from endpoint values.

## 3. Finite-chart QFI completion: exact geometry, failed topology

For a finite complex boundary output `w`, put

```text
beta(w) = w / sqrt(1 + |w|^2),

Q(w) = 1/2 [ 1                  conjugate(beta(w)) ]
             [ beta(w)          1                  ].
```

Write `beta = r exp(i theta)`, `0 <= r < 1`.  The symmetric-logarithmic-derivative QFI line
element of this equatorial mixed-qubit family is

```text
ds_Q^2 = dr^2/(1-r^2) + r^2 dtheta^2.                    (QME.1)
```

Parameterize recovery magnitude by `R=|w|` and `u=arctan R`, so `r=sin u`.  Then

```text
ds_Q^2 = du^2 + sin(u)^2 dtheta^2,    0 <= u < pi/2.     (QME.2)
```

Consequences are exact:

- boundary infinity is at finite radial QFI distance `pi/2`;
- angular QFI tends to `dtheta^2`, rather than collapsing;
- metric completion adds one full phase circle;
- different asymptotic phases remain different boundary states.

Apply this chart separately to the exact boundary vector:

```text
Q2(V_N) = Q(O_N) tensor Q(C_N B_N).
```

Product QFI metric is the sum of the two line elements.  Its ambient completion adds a phase torus.
Along any source subsequence on which both coordinates tend to infinity and their sum remains
bounded, elementary complex geometry forces equal radial escape and phase difference tending to
`pi`.  Every convergent boundary subsequence therefore lands in the antidiagonal

```text
A_inf = {(exp(i theta), -exp(i theta)) : theta in R/2piZ},
```

The source-accessible boundary over a fixed parameter is only an unknown nonempty compact subset
of this circle.  Cofinal spikes do not show that the cutoff sequence tends to the boundary, do not
select one phase, and do not show that every phase occurs.

This finite-chart fork fails the QFI-necessity test.  With `u=arctan R`, the QFI completion is a
closed hemisphere and hence a closed disk; the ordinary closure of the ball coordinate is the same
closed disk with the same phase boundary.  The metric supplies exact distances but no new
topological obstruction.  Any live successor must use QFI on the canonical cutoff history itself
and prove that its completion topology changes when the information metric is removed.  Merely
charting `(O_N,C_NB_N)` is retired.

## 4. Controlled relative phase removes direction but also zero information

For any two complex process outputs `x,y`, use their squared norms as normalized weights and encode
one external control with opposite velocities:

```text
p_x = |x|^2/(|x|^2+|y|^2),
p_y = |y|^2/(|x|^2+|y|^2),
k = (+1,-1).
```

The phase-controlled pure state is

```text
psi_theta(x,y) = (e^(i theta) x, e^(-i theta) y) / sqrt(|x|^2+|y|^2).
```

Its QFI is four times the weighted variance of `k`, hence exactly

```text
I_rel(x,y) = 16 |x|^2 |y|^2 / (|x|^2+|y|^2)^2.           (QME.3)
```

If `|x_N| -> infinity` and `x_N+y_N` has a finite limit, then
`y_N/x_N -> -1`, so `I_rel(x_N,y_N) -> 4`.  This is stronger than choosing an accumulation phase:
the common phase of `(x_N,y_N)` is physically invisible, while varying `theta` sweeps the complete
relative-phase circle by construction.  The circle is an observer control orbit fixed before any
zero is selected, not an inferred set of arithmetic escape directions.

Lean closes two source instances.

1. For every open-strip point, the universal pair `(H_N,C_N)` has `I_rel -> 4`.
2. At every strict-left open-strip point, there is a strictly increasing cutoff subsequence on
   which `(O_N,C_NB_N)` jointly escapes, has ratio tending to `-1`, and has `I_rel -> 4`.

The first circle is a background information direction.  The second was conjectured to be
exceptional, but its proof never uses `zeta(s)=0`.  The Möbius successor obstruction and
strict-left scaling already force it over the whole left half-strip.  Controlled phase resolves
the unknown-direction problem by averaging away precisely the finite charge that distinguishes a
zero from a nonzero point.

This imposes a stronger no-go.  Neither balanced QFI circle, nor their product, can locate a zero:
both exist at every strict-left point.  Their incidence is generic and carries no zero-location
content.

## 5. Failed global topology of the reflected two-circle experiment

Let `B` denote the relative-phase control circle of `(H_N,C_N)` and `E` the corresponding circle of
`(O_N,C_NB_N)`.  `B` is present over the whole open strip.  The universal strict-left theorem now
places `E`, along a strict cutoff subsequence, over every point with `0 < Re(s) < 1/2`.  Therefore
the product `B x E` is not an exceptional fibre generated by an off-critical zero.  It is generic
left-half leading geometry.

Reflection can move or identify these generic fibres, but it cannot turn their mere existence into
a zero condition.  Any rule declaring interior two-cycles absent would contradict the unconditional
strict-left construction rather than prove RH.  Any rule retaining only the subleading finite total
would read `F_NB_N-1` and thereby return to scalar cancellation.

## 6. Retirement theorem and boundary of the no-go

The strongest surviving theorem is unconditional:

```text
0 < Re(s) < 1/2
  -> there is a strict cofinal subsequence with
     |O_N(s)| -> infinity,
     (C_N(s)B_N(s))/O_N(s) -> -1,
     I_rel(O_N(s), C_N(s)B_N(s)) -> 4.                  (QME.U2)
```

This sharply separates leading topology from subleading arithmetic charge.  Leading global QFI
topology sees a universal left-half end.  The zero condition survives only in the finite remainder
of the compensation.  Within this route's exclusions, no QFI-essential invariant remains:
rescaling the remainder to keep it visible reconstructs a scalar zeta-dependent readout, while
discarding it makes zeros indistinguishable from nonzeros.  The correct scientific conclusion is
retirement, not an assumed global law patched over the failed selector.

## 7. Conjecture -> attack -> failure -> pivot loops

### Loop A: many zero-mean dilation processes

**Conjecture.** Several periodic coefficient streams vanish together exactly at zeta zeros and
their joint QFI state changes topology.

**Failure.** Each transform contains the same zeta factor.  Homogeneous normalization erases that
factor, and the corpus already computes the corresponding common-factor Koszul homology.

**Meaning for whole route.** More channels do not mean more laws when one scalar divisor controls
all of them.  Multiple failures must involve different operations at infinity.

**Pivot.** Use formation, recovery, and gluing, whose failure types are zero, escape, and loss of a
finite joint realization.

### Loop B: finite analytic projective state

**Conjecture.** A finite analytic vector of observer amplitudes makes each common zero a projective
puncture.

**Failure.** Factor the least common vanishing order.  The projective map extends through the zero.

**Meaning for whole route.** Finite projective geometry cannot create the needed topology.

**Pivot.** Send the independently sourced recovery value to infinity and use the mixed-state QFI
completion, which retains an angular boundary.

### Loop C: ordinary boundary hit

**Conjecture.** A full-dimensional smooth state map can hit a state-space boundary at an isolated
interior point while retaining local differential rank.

**Failure.** Any local boundary coordinate has an interior extremum there, so its differential
vanishes.  Assuming nondegenerate QFI at the hit assumes away the event.

**Meaning for whole route.** Local rank cannot be the selector.

**Pivot.** Classify the global incidence of completion links after the reflection quotient.

### Loop D: generic failure nerve

**Conjecture.** Encode simultaneous process failures by the topology of their incidence nerve.

**Failure.** Failure-nerve and higher compatibility constructions already occupy that mechanism,
and a generic nerve supplies no new source-to-zero theorem.

**Meaning for whole route.** The invariant must use the QFI metric completion itself.

**Pivot.** Closed recovery-end circles versus seam-attached recovery-end intervals.

### Loop E: inverse value alone

**Conjecture.** `1/zeta` divergence already provides the source process and the proof route.

**Failure.** It is a divisor receiver and can be defined only after the target function is known.
The corpus already contains reciprocal-zeta blow-up identities and Möbius QFI boundary packages.

**Meaning for whole route.** QFI dressing of a reciprocal identity is forbidden and scientifically
empty.

**Pivot.** Require finite coefficient construction of `R_N`, exact overflow bookkeeping, and a
zero-independent end-localization theorem.  Failure of either requirement retires the route.

### Loop F: raw finite Möbius recovery

**Conjecture.** The literal Möbius Dirichlet head `B_N` supplies the independent recovery channel,
while the finite continuation `F_N` supplies formation.

**Proof failure.** At each nontrivial zero, `‖B_N‖ <= N` and `‖F_N‖ = O(N^-2)`, so `F_N B_N -> 0`
and its gluing defect tends to `-1`.  The theorem is closed in Lean and uses no zero-location
assumption.

**Meaning for whole route.** Independence of coefficient laws is insufficient: their chosen
cutoffs must share a continuation law.  Without a source-derived counterterm, recovery infinity is
not assembled by the finite experiments and the proposed QFI end is only a picture of the limiting
reciprocal.

**Pivot.** Derive the unique overflow contribution produced when truncated Dirichlet convolution
is passed through the same continuation operator as `F_N`; retire the route if this cannot be done
without inserting reciprocal zeta.

### Loop G: fixed finite logarithmic jets

**Conjecture.** A finite packet of parameter derivatives of the Möbius head supplies the missing
renormalization while retaining independent tangent information.

**Proof failure.** For each fixed jet order `k`, its norm is at most
`N (log N)^k`.  The quadratic decay of `F_N` at a zero therefore dominates it.  Lean proves product
limit zero and defect limit `-1` for every fixed jet and every fixed finite linear packet.

**Meaning for whole route.** Finite-order tangent enrichment cannot create the required infinity.
Formalizing more fixed derivatives would be theatre.  Any surviving state needs a genuinely
cofinal order or a nonlocal boundary coordinate.

**Pivot.** Retain the complete cutoff overflow and continuation interaction before compressing to
finite jets.

### Loop H: exact two-component boundary vector

**Conjecture.** Truncated convolution already supplies a canonical multi-law defect without a
chosen reciprocal.

**Proof success.** Equation `(QME.0)` is exact for every cutoff and parameter.  Lean also proves
that its total tends to `-1` at every nontrivial zero.

**Meaning for whole route.** Route now has a source-defined pair of distinct boundary processes.
It still lacks an infinity: bounded total does not imply either coordinate escapes.

**Pivot.** Attack cofinal noncompactness of the full labelled pair before formalizing more QFI
geometry.

### Loop I: exponentially damped Möbius recovery

**Conjecture.** Exponential damping of Möbius coefficients creates a source-native recovery whose
Mellin poles supply the required ends.

**Failure.** Corpus already develops Möbius--Laplace/Mellin continuation and natural-Abel singular
divisor tomography.  Its endpoint is a known singular-divisor receiver; its zero-free propagation
uses analytic uniqueness, and topology-only landing is already recorded as terminal.  Adding QFI
would redress occupied T2 and Möbius--Laplace routes.

**Meaning for whole route.** Source-native smoothing is not enough.  New content must live in the
finite labelled overflow pair, before scalar Mellin continuation.

**Pivot.** Exclude Abel-smoothed reciprocal constructions from this route.

### Loop J: coefficient head versus continuation correction

**Conjecture.** The direct formation head and continuation correction provide the missing pair of
compensating infinities, and their antidiagonal QFI boundary occurs only where formation darkens.

**Proof success.** For every open-strip point, both norms escape and the canonical normalized limits
are `+1` and `-1`.  Their exact finite sum converges to zeta; at every nontrivial zero it converges
to zero.  These statements are closed in Lean.

**Failure.** The leading antidiagonal boundary is universal across the open strip.  First-boundary
topology forgets the finite remainder and is blind to zero occurrence.

**Meaning for whole route.** Multiple compensating infinities are real, not hypothetical, but an
end component cannot be identified with a zero.  Further work on ordinary first-boundary QFI would
be theatre.  The scalar overflow pair remains the only present candidate for a zero-specific end.
A higher-contact construction survives only if QFI distance canonically retains the finite gluing
charge and yields a global obstruction unavailable from the unscaled identity itself.

**Pivot.** Falsify QFI-essentiality of the higher-contact boundary before formalizing it.  If its
complete invariant reduces to `lim (H_N+C_N)=zeta`, reject that fork as a redressing.  Otherwise
state the global bundle obstruction and then attack it without importing a zero-location theorem.

### Loop K: inverse QFI higher contact

**Conjecture.** Pulling the two universal boundary coordinates back through the QFI ball chart
retains a finer antidiagonal contact law that is not present in the finite scalar continuation.

**Proof failure.** The QFI ball coordinate is injective and odd.  Its two finite images have zero
antidiagonal defect exactly when `F_N(s)=0`, and the inverse-chart compensated charge equals
`F_N(s)` identically.  Lean closes both equivalences without assumptions.

**Meaning for whole route.** Inverse-chart contact is not a new law.  It is an exact coordinate
rewrite of finite continuation, so using it would violate the route's QFI-essentiality gate.
Universal first-boundary data and their inverse contact are both retired.  Only source-native
overflow can now create a zero-specific end.

**Pivot.** Attack cofinal noncompactness of `(O_N,C_N B_N)` directly.  First test strict-left zeros:
bounded overflow would force the rescaled Möbius head to vanish, while its consecutive-cutoff law
recovers the nonvanishing Möbius values at arbitrarily large primes.  If closed, this supplies an
actual arithmetic escape theorem rather than a compactification picture.

### Loop L: strict-left overflow escape

**Conjecture.** Bounded rectangle overflow at a strict-left zero is incompatible with the finite
Möbius successor law.

**Proof success.** Lean proves bounded overflow forces `N^rho B_N -> 0`, transports that limit to
the adjacent cutoff scale, and derives the impossible limit `mu(N+1) -> 0`.  Prime infinitude gives
the contradiction.  Since the two-coordinate total tends to `-1`, both coordinates exceed every
radius simultaneously at arbitrarily late cutoffs.  Functional-equation pairing gives such a
strict-left escape member for every off-critical zero orbit.

**Meaning for whole route.** Zero-specific source escape is no longer hypothetical.  The route has
crossed the prerequisite for information-geometric completion.  What remains is not another size
estimate: it is the global topology of all QFI boundary accumulation directions and their quotient
incidence with the seam.

**Pivot.** Construct the QFI boundary accumulation correspondence from `(QME.L)` and bounded total
charge.  Then test the decisive no-closed-interior-link law against exact finite successor
incidence.  Reject any formulation that inserts zero location or a preselected boundary phase.

### Loop M: cofinal spikes as a QFI circle

**Conjecture.** Simultaneous crossings of every radius, together with bounded total charge, force a
full antidiagonal QFI circle over a strict-left zero.

**Failure.** The Lean theorem supplies arbitrarily late joint spikes, not eventual escape.  From a
chosen spike sequence, compactness supplies a further subsequence converging to some antipodal
boundary phase.  Nothing forces all phases, connectedness, or even a unique phase.  A discrete
cutoff tail has no connectedness to transfer.  The corpus countermodel
`CofinalDirectionCountermodel` independently shows that exact finite provenance can coexist with
an arbitrarily selected limiting direction.  More decisively, the ambient mixed-qubit QFI
completion is topologically the ordinary closed disk, so its boundary circle survives unchanged
after deleting the information metric.

**Meaning for whole route.** Source noncompactness is real, but the product-chart end picture is
not a new QFI route.  Treating the ambient antidiagonal circle as source-occupied would manufacture
the missing topology.  The route now survives only if the actual cutoff history has a canonical
information-geometric completion with a global invariant absent from ordinary radial closure.

**Pivot.** Before adding Lean topology, construct the density-operator history and its canonical
successive transition law directly from the two finite source processes.  Derive its QFI path
metric, compare its Cauchy completion with trace-norm and radial completions, and demand an exact
source theorem that changes the resulting end incidence.  If all three completions have the same
topology, retire the whole route.

### Loop N: reconstruct cutoff history from QFI boundary data

**Conjecture.** Endpoint states, their QFI tangent metric, and their boundary phase determine the
history needed for the global completion.

**Failure.** The corpus theorem `framedHistory_typedSeparation` gives two histories with the same
radial boundary report, the same phase tangent metric, and the same Berry quotient but different
winding histories.  `twoLevel_zeroComplexity_historyLength_unbounded` is sharper metrically:
endpoint complexity can return to zero while executed information-geometric length becomes
arbitrarily large.

**Meaning for whole route.** A path chosen after seeing `(O_N,C_NB_N)` would add information absent
from the finite arithmetic experiment.  Neither QFI endpoint geometry nor holonomy recovers the
missing execution.  Source history must be part of the construction and must be fixed before any
zero is selected.

**Pivot.** Derive a cutoff-insertion quantum channel from the exact successor identities and the
labelled overflow shell.  Its action must reproduce both finite source coordinates at integer
times and specify the transition between them without a fitted phase or arbitrary interpolation.
Only then is QFI path completion a well-typed next object.

### Loop O: promote formation and recovery to a central process history

**Conjecture.** The exact finite laws canonically generate the missing executed history through
upper-unipotent process composition.  For

```text
X(a) = [[1,a,0],[0,1,0],[0,0,1]],
Y(b) = [[1,0,0],[0,1,b],[0,0,1]],
```

matrix multiplication gives

```text
X(a)Y(b) = [[1,a,ab],[0,1,b],[0,0,1]].
```

At every cutoff `N >= 1`, take `a=H_N` and `b=B_N`.  The central coordinate is
`H_NB_N=1+O_N`.  Prepending the continuation process gives

```text
X(C_N) X(H_N) Y(B_N) = X(F_N)Y(B_N),
central coordinate = F_NB_N = 1 + O_N + C_NB_N.
```

Thus a zeta zero makes the completed central coordinate tend to zero while, at every strict-left
zero, the two internal central contributions cross every radius together and compensate.  This is
an exact three-process description of failure at infinity.

**Failure.** Central promotion alone is not the new route.  The corpus already proves the generic
Heisenberg carry, its centrality, and loss under abelian projection in
`ConstitutiveExchangeCentralPromotion`; it also contains a different global triangular Xi
extension.  The displayed matrices merely represent the already proved product identities.  The
complex central coordinate has no source-defined lattice or quotient, and a normalized finite
endpoint state still loses executed history.  No QFI-dependent global topology follows.

**Meaning for whole route.** The algebra identifies the minimal ordered process record but fails
the novelty and QFI-necessity gates.  Formalizing matrix entries alone would be redressing.  A live
advance must place the entire three-stage path—not only its product—in an information-geometric
history space and exhibit a source-defined global invariant absent from generic central promotion.

**Pivot.** Compute the QFI of the canonical one-parameter subgroup stages and test whether their
concatenated path class survives endpoint normalization, changes under reflection, and has a
source-defined completion at cutoff infinity.  If the class is determined by the central carry or
by endpoint state data, retire this pivot without Lean formalization.

### Loop P: normalized-Choi QFI of one source stage

**Conjecture.** The normalized Choi state of an upper-unipotent source stage retains its complex
direction at coefficient infinity and therefore supplies the missing history boundary.

**Failure.** Let `v(t)=I+t a E_12` in the Hilbert--Schmidt realization of `3 x 3` matrices and put
`A=|a|^2`.  Direct substitution into pure-state QFI gives

```text
mass = 3+t^2 A,   overlap = t A,   speed^2 = A,
QFI(t) = 12 A / (3+t^2 A)^2.
```

The associated Fubini--Study stage length is

```text
integral_0^1 sqrt(QFI(t))/2 dt = arctan(|a|/sqrt(3)),
```

which saturates at `pi/2`.  More importantly, the normalized endpoint density tends to the same
rank-one `E_12` state for every phase of `a`: the phase becomes a global vector phase and is erased.
The finite projective process-state space is simply connected, so a concatenated one-dimensional
path supplies no winding class either.

**Meaning for whole route.** The most canonical finite-dimensional process QFI loses exactly the
direction needed by the global end argument.  Executed length distinguishes long histories from
endpoint returns, but length alone has no source link topology and does not locate zeros.  This
closes finite normalized-Choi path completion as a route.

**Pivot.** A surviving information-topology object must be higher-dimensional and source-filled,
not an endpoint or one path.  The only live test is whether independent formation and recovery
activations canonically generate a two-dimensional quantum process surface whose QFI completion
has a nontrivial global class and whose continuation surface cancels that class exactly at zeros.
Before formalization, prove that the surface is source-defined, not a freely filled parameter
square, and that its class is absent from generic central promotion.

### Loop Q: freely filled process surface, infinite projective limit, or process tensor

**Conjecture.** A two-parameter activation surface, an infinite projective completion, or a
multi-time process tensor supplies the missing global history topology.

**Failure.** Corpus audit closes all three generic moves.  `LiftedGluingFaces` explicitly records
that two free parameters are packaging.  `SeparableInfiniteProjectiveRecurrenceLaw` shows that an
arbitrarily weak separable interaction can realize every finite temporal rank and complete
projective recurrence without arithmetic input.  The universal-law corpus already treats process
tensors, quantum combs, causal breaks, derived limits, and finite-data fitting as occupied
receivers.  Generic curvature of a finite phase surface is also already identified with its Fisher
metric.

**Meaning for whole route.** Neither dimension, infinite projective recurrence, nor multi-time
tomography creates a source selector.  Formalizing any of them around the existing scalar defect
would be redressing.

**Pivot.** Use the finite source theorem already proved: compensated escape itself forces a
balanced relative-phase QFI when the phase control is inserted before the limit.  This changes the
question from reconstructing an unknown history to determining the global incidence of two
source-admitted control cycles.

### Loop R: controlled relative-phase QFI

**Conjecture.** A controlled relative phase removes dependence on the unknown common escape
direction and turns the strict-left overflow theorem into a complete information circle.

**Proof success.** For any compensated pair `(x_N,y_N)` with `|x_N| -> infinity` and finite total,
`y_N/x_N -> -1`.  Its relative-phase QFI is `(QME.3)` and tends to `4`.  Lean proves this generally,
proves the universal head/correction limit over every open-strip point, and extracts a strictly
increasing balanced-QFI escape subsequence for every strict-left zero.  No escape phase is chosen.

**Meaning for whole route.** The earlier missing-circle objection is solved operationally, but QFI
records only relative balance at leading order.  Whether overflow/recovery circle is truly
zero-specific is now the decisive question.

**Pivot.** Remove the zero premise from strict-left overflow proof and test whether source escape
and the QFI limit still follow.

### Loop S: is the overflow/recovery circle zero-specific?

**Conjecture.** Finite total at a zero is necessary for overflow/recovery balance, so the second
controlled circle is absent at generic strict-left points.

**Failure.** No zero premise is necessary.  For every strict-left open-strip point, bounded
overflow would force both `N^sB_N` and `(N+1)^sB_N` to tend to zero, contradicting the exact Möbius
successor shell at arbitrarily large primes.  A strict escape subsequence then satisfies
`H_NB_N/O_N -> 1` and `C_N/H_N -> -1`, hence `(C_NB_N)/O_N -> -1`.  Lean proves the resulting QFI
limit `4` at every such point.

**Meaning for whole route.** Both proposed information circles and their product are universal on
the strict-left half-strip.  The global two-cycle has no incidence relation with the zero set.  The
route's only surviving zero datum is subleading finite compensation, which fails the
QFI-essentiality gate.

**Retirement.** Do not build a global quotient around a selector already proved zero-blind.  A
renormalized subleading observable would reconstruct scalar cancellation and is outside this
route.  No admissible pivot remains.

## 8. Collision audit against current frontier

The route does **not** claim novelty for any of these available pieces:

- square-summability or Fisher admission at `Re(s)=1/2`;
- a Fisher-distance horizon;
- Fermi--Mellin zero orthogonality or its QFI lower bound;
- Möbius critical Fisher Gram limits;
- reciprocal-zeta blow-up identities;
- natural-Abel singular divisor tomography or Möbius--Laplace continuation;
- reflection/collision fibres, failure nerves, or history completion;
- common-factor homology;
- generic graph-end classification;
- a pointwise reformulation quantified over preselected zeros.

The proposed new content was this composite theorem:

```text
universal compensated pair -> background QFI control circle
strict-left zero -> exceptional overflow/recovery QFI control circle
both circles -> zero-selective global incidence.
```

The universal strict-left theorem breaks its second arrow: overflow/recovery circle exists at every
strict-left point.  The chain therefore has no zero-selective input from which global incidence
could be derived.  Generic polar phase geometry is existing infrastructure, and retaining the
finite compensated remainder would return to a scalar readout.  Collision-free formulation was
achieved, but the arithmetic selector was false.

## 9. External method transfers

- Capra--de Simone--Franzosi, *A Geometric Theory of Quantum Entanglement*, arXiv:2609.11720:
  global QFI can be obtained by tracing information geometry over a family of local operations.
  Transfer here: use a product experiment over formation, recovery, and defect operations, not a
  single normalized amplitude.
- Zhang et al., *MotionQ*, arXiv:2609.11818: forcing one common representation across changing
  observation operators can erase operator-specific information.  Transfer here: retain
  operator-conditioned recovery phase instead of quotienting all process outputs together.
- Chen--Jin--Liu, *Sensitivity of parameter estimation near the exceptional point of a
  non-Hermitian system*, arXiv:1809.05719: divergence of a raw susceptibility can be cancelled in
  exact QFI.  Transfer here: derive `(QME.1)` for the chosen mixed-state family; never infer a QFI
  end from reciprocal divergence alone.
- Vasoya--Ponson--Lazarus, *Beyond linear stability: Heterogeneity-induced fingering of crack
  fronts*, arXiv:2608.25314: a global compatibility class can disappear without a local pairwise
  collision.  Transfer here: target disappearance of a global finite joint realization, not a local
  eigenvalue or sign event.
- Płodzień--Chwedeńczuk, *Topological protection of local quantum Fisher information*,
  arXiv:2605.00770: a residual QFI plateau alone is not the topological diagnostic; asymmetry under
  two orthogonal encoding axes distinguishes boundary memory.  Transfer here: probe formation and
  recovery with a controlled relative phase, and treat one background QFI circle as nonselective.
- Yadalam--Mitchison, *Process-tensor approach to full counting statistics of charge transport in
  quantum many-body circuits*, arXiv:2603.28894: multi-time memory can survive endpoint
  compression.  Transfer here is only the warning to preserve cutoff order.  Generic process
  tensors remain occupied and are not the proposed invariant.

These are method transfers only.  None supplies an arithmetic theorem.

## 10. Lean program

`RHTower.FiniteMobiusRecoveryGluingNoGo` formalizes the first source-side falsifier:

- `finiteCutoffZeta_mul_finiteMobiusRecoveryHead_boundary_split` proves exact decomposition into
  rectangle overflow and continuation--recovery interaction for every cutoff and parameter;
- `tendsto_finiteMobiusBoundaryFailureTotal_at_zero` proves their total tends to `-1` at every
  nontrivial zero;
- `norm_finiteMobiusRecoveryHead_le` proves the unconditional linear bound;
- `tendsto_finiteCutoffZeta_mul_finiteMobiusRecoveryHead_at_zero` proves product convergence to
  zero at every nontrivial zero;
- `tendsto_finiteMobiusRecoveryGluingDefect_at_zero` proves defect convergence to `-1`;
- `norm_finiteMobiusRecoveryLogJet_le` gives the fixed logarithmic-jet bound;
- `tendsto_finiteCutoffZeta_mul_finiteMobiusRecoveryJetPacket_at_zero` and
  `tendsto_finiteMobiusRecoveryJetPacketGluingDefect_at_zero` close the no-go for every fixed finite
  linear jet packet.

This module rules out raw and fixed-finite-jet recovery while exposing the exact two-boundary split.
Escape of that pair is proved below; the universal strict-left theorem makes its proposed QFI
history selector false before any completion is built.

`RHTower.FiniteCutoffCompensatingInfinityNoGo` formalizes the universal infinity and its limitation:

- `tendsto_normalized_finiteZetaFormationHead` proves normalized head limit `+1` on the open strip;
- `tendsto_normalized_finiteCutoffContinuationCorrection` proves normalized correction limit `-1`;
- `tendsto_norm_finiteZetaFormationHead_atTop` and
  `tendsto_norm_finiteCutoffContinuationCorrection_atTop` prove both processes escape;
- `tendsto_finiteZetaFormationHead_add_continuationCorrection_at_zero` proves their finite total
  darkens at every nontrivial zero;
- `finiteCutoffCompensatingInfinityAtZero_closed` packages both escapes, opposite normalized
  directions, and darkening with no zero-location premise.

The same module proves both escapes and normalized directions for every open-strip point.  It
therefore closes the easy infinity producer and simultaneously rules out its ordinary first
boundary as a zero detector.

`RHTower.FiniteCutoffQFIHigherContactNoGo` closes the direct higher-contact falsifier:

- `qfiAntidiagonal_eq_zero_iff` proves that QFI-ball antidiagonal coincidence is ordinary additive
  cancellation;
- `finiteCutoffQFIAntidiagonalDefect_eq_zero_iff` specializes this to exact finite continuation;
- `qfiInverseCompensatedCharge_eq_finiteCutoffZeta` proves that inverse-chart contact reconstructs
  `finiteCutoffZeta` identically.

Thus no inverse use of this QFI chart supplies an independent arithmetic or topological law.

`RHTower.CofinalQFICircleNoGo` closes the full-circle inference even under stronger escape:

- `tendsto_norm_singlePhaseEscape` gives eventual escape along one fixed phase;
- `singlePhaseEscape_neg_sum` gives exact two-process compensation at every cutoff;
- `no_singlePhaseEscape_qfi_subsequence_tendsTo_I` proves no reindexing reaches phase `i`;
- `exists_eventual_joint_escape_exactly_compensated_single_qfi_phase` packages the countermodel.

Thus even eventual joint escape and exact bounded total do not make the QFI boundary a circle.

`RHTower.FiniteMobiusLeftOverflowEscape` closes the first zero-specific source escape:

- `finiteMobiusRecoveryHead_succ` and
  `natSucc_cpow_mul_finiteMobiusRecoveryHead_sub` give the exact cutoff increment and its recovered
  Möbius coefficient;
- `finiteMobiusOverflow_not_isBoundedUnder_at_strictLeftZero` proves overflow is not tail bounded;
- `finiteCorrectionRecoveryInteraction_not_isBoundedUnder_at_strictLeftZero` proves the matched
  continuation--recovery coordinate is not tail bounded;
- `exists_joint_overflow_escape_after` proves both coordinates cross every radius at the same
  arbitrarily late cutoffs;
- `offCriticalZeroOrbit_exists_joint_overflow_escape_after` transfers this joint escape to every
  hypothetical off-critical zero orbit through its strict-left member.

`RHTower.FiniteMobiusRelativePhaseQFI` turns compensated escape into a controlled QFI limit:

- `compensatedPairRelativePhaseQFI_eq` gives the exact two-channel formula `(QME.3)`;
- `tendsto_compensatedPairRelativePhaseQFI_of_ratio` proves that escape plus asymptotic ratio `-1`
  forces QFI limit `4`;
- `tendsto_compensatedPairRelativePhaseQFI_balanced` proves that any escaping first channel with a
  finite compensated total has relative-phase QFI tending to `4`;
- `tendsto_headCorrectionRelativePhaseQFI_balanced` proves the universal background circle over
  every open-strip point;
- `strictLeftZero_exists_balancedRelativePhaseQFI` extracts a strictly increasing cutoff
  subsequence with joint overflow/recovery escape and QFI limit `4` at every strict-left zero.

`RHTower.FiniteMobiusRelativePhaseQFIUniversalNoGo` closes the decisive selector failure:

- `finiteMobiusOverflow_not_isBoundedUnder_at_strictLeftPoint` removes the zero premise and proves
  overflow is not tail bounded throughout the strict-left open strip;
- `exists_finiteMobiusOverflow_norm_gt_after_at_strictLeftPoint` gives arbitrarily late threshold
  crossings;
- `strictLeftPoint_exists_overflowRecoveryRelativePhaseQFI_balanced` extracts one strict
  subsequence carrying overflow norm to infinity, actual interaction-to-overflow ratio to `-1`, and
  relative-phase QFI to `4` at every strict-left point.

Every theorem must be unconditional and axiom-clean.  Universal quantification is allowed; route
assumptions encoding end localization are not.  Scratch checks use `lake env lean <file>`.  Only a
finished leaf module receives `lake build <module>`, followed by wiring without an umbrella build.

Direct checks and leaf-only builds pass for `FiniteCutoffQFIHigherContactNoGo`,
`FiniteMobiusLeftOverflowEscape`, `CofinalQFICircleNoGo`, and
`FiniteMobiusRelativePhaseQFI` and `FiniteMobiusRelativePhaseQFIUniversalNoGo`; the
compensating-infinity dependency also rebuilt successfully.
Capstone axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.  Project lint
reports no owned error and stops on the pre-existing unrelated umbrella omission
`RHTower.Sieve.KloostermanGlobalCollisionCoprime`.  No umbrella build was run.

## 11. Retirement verdict and strongest survivor

The first retirement condition occurred in a stronger form: the two controlled loops need not be
identified with each other, because each already survives throughout the strict-left open strip.
Their global product is generic before zeros are selected.  Consequently:

1. leading relative-phase QFI topology cannot distinguish zero from nonzero points there;
2. reflection cannot repair an input family that already lacks a zero selector;
3. finite compensation is the only surviving zero datum;
4. magnifying that remainder recreates a scalar zeta-dependent observable and violates the route's
   QFI-essentiality gate.

The nontrivial survivor is `(QME.U2)`: a source-derived universal end theorem with exact phase-ratio
and QFI limits.  It is useful as a no-go boundary for future information-geometric work: any new
route must retain a global invariant beyond leading balanced escape and must prove zero selectivity
before constructing topology.  Under current exclusions, this card has no live next experiment.

## Log

- 2026-09-14 — Candidate created after five failed pivots.  Local QFI end geometry and quotient-link
  classification are closed on paper.  Source-native finite recovery, overflow convergence, and
  cofinal failure-end localization remain open.
- 2026-09-14 — Raw finite Möbius recovery failed: Lean proves its product with the literal finite
  continuation tends to zero, and its gluing defect tends to `-1`, at every nontrivial zero.
  Whole-route survivor narrowed to a source-derived renormalized recovery law.
- 2026-09-14 — Every fixed logarithmic Möbius jet and every fixed finite linear jet packet failed
  by the same mechanism, closed in Lean.  Exact truncated convolution nevertheless supplies a
  canonical two-component boundary vector; Lean proves its total equals the gluing defect and tends
  to `-1` at every nontrivial zero.  Boundary escape and global end localization remain open.
- 2026-09-14 — Exponentially damped Möbius recovery rejected after corpus audit: it collides with
  existing natural-Abel divisor and Möbius--Laplace continuation routes and would use excluded
  analytic uniqueness.  Route remains confined to finite labelled overflow topology.
- 2026-09-14 — Coefficient head and continuation correction give unconditional compensating
  infinities: normalized limits are `+1` and `-1` at every open-strip point, and their finite total
  darkens at every nontrivial zero.  Lean closes all limits.  Whole-route failure: leading QFI
  boundary is universal and therefore zero-blind.  Next gate is QFI-essential higher contact;
  otherwise only exact overflow pair remains live.
- 2026-09-14 — Inverse QFI higher contact failed: Lean proves finite antidiagonal coincidence is
  exactly finite-zeta cancellation and inverse-chart compensation is identically `F_N`.  This fork
  is retired as redressing.  Route returns to source-native overflow; strict-left escape via the
  Möbius successor law is the next proof target.
- 2026-09-14 — Strict-left source escape closed in Lean.  Rectangle overflow and the matched
  correction--recovery interaction jointly cross every radius at arbitrarily late cutoffs while
  their sum tends to `-1`; prime Möbius values obstruct boundedness.  Every off-critical zero orbit
  has such a strict-left member.  Remaining obstacle is global QFI boundary accumulation and the
  no-closed-interior-link law.
- 2026-09-14 — Full-circle inference failed.  Cofinal joint spikes give boundary subsequences, not
  eventual escape, phase coverage, connectedness, or a source link.  The finite mixed-qubit QFI
  completion is topologically the same closed disk as ordinary radial closure.  Whole-route
  survivor is narrowed to a source-history QFI completion demonstrably different from ordinary
  completion; absent that difference, route retires.
- 2026-09-14 — Endpoint reconstruction failed against existing Lean counterexamples: QFI tangent
  data and Berry quotient do not determine winding history, and endpoint returns can hide
  arbitrarily large executed QFI length.  Any live history must therefore be generated by the
  finite coefficient insertion law before zero selection.
- 2026-09-14 — Exact upper-unipotent promotion identifies a canonical ordered formation--recovery--
  continuation record whose central coordinates are `1+O_N` and `F_NB_N`.  Generic central
  promotion and other triangular completions already exist, so matrix representation alone is
  rejected.  Only a source-defined QFI path invariant not determined by its endpoint or central
  carry can survive.
- 2026-09-14 — Normalized-Choi process path failed.  Its exact one-stage QFI is
  `12|a|^2/(3+t^2|a|^2)^2`, its length saturates at `pi/2`, and every phase at coefficient infinity
  converges to the same rank-one density.  Finite-dimensional endpoint and path completions are
  retired; only a source-filled higher process surface remains eligible for testing.
- 2026-09-14 — Free process surfaces, infinite projective limits, generic process tensors, and
  ordinary derived completion failed the corpus collision audit.  Controlled relative phase then
  closed a new source theorem: every compensated escape has balanced QFI `4`; the universal pair
  supplies one background circle and every strict-left zero supplies a second overflow/recovery
  circle along a cofinal subsequence.  Remaining route is exactly the zero-free no-interior-two-
  cycle theorem `(QME.P)`.
- 2026-09-14 — The supposed exceptional circle is universal.  Lean removes the zero premise:
  every strict-left open-strip point has a strict subsequence on which overflow tends to infinity,
  actual continuation--recovery interaction divided by overflow tends to `-1`, and relative-phase
  QFI tends to `4`.  Meaning for whole route: both leading circles are zero-blind, so their global
  product cannot select critical-line zeros.  Subleading rescaling would return to scalar
  cancellation.  Route retired with `(QME.U2)` as strongest survivor.
