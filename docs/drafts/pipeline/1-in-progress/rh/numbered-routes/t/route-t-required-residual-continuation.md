# Route-T required residual continuation

- **ID:** `route-t-required-residual-continuation`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / THEOREM (Lean)
- **Source:** Route-T relative orbit leakage + prime-gap mesh continuation + Wold lower-Hardy
  renormalization
- **Statement:** After subtracting the canonical continued logarithmic mesh and static holonomy
  from the meromorphic Wold current, one obtains a source-defined continuation of the actual
  lower-Hardy residual. At every zeta zero right of the critical line this continuation retains
  the exact nonzero residue `-m`; hence neither mesh nor holonomy can carry the required
  compensating principal part.

## Heavy conjecture loop

### C0 — all regular Route-T terms cancel the Wold pole

Conjecture that logarithmic mesh, holonomy, and lower-Hardy residual all continue regularly to
`s = rho - 1`; then the safe identity would continue across the wall and contradict the Wold
residue.

**Failed.** Holonomy is entire and critical prime-gap energy makes the mesh regular, but the
lower-Hardy series is only analytic for `Re s > 0`. Its square-root-log coefficient decay gives
all boundary derivatives but does not overcome `p^{-s}` growth for `Re s < 0`. Regularity of the
residual continuation is exactly the missing RH-strength assertion.

### C1 — theta-Green boundedness supplies residual regularity

Conjecture that the Wold/theta-Green vertical-line bound identifies the lower-Hardy residual with
a compact-source analytic Green function across the Laplace wall.

**Failed.** Corpus proves boundedness and asymptotic carrier equality in vertical time, but no
coefficient-faithful equality with the Laplace residual on a complex neighbourhood. Treating the
two as equal would insert the missing source-to-physical specialization.

### C2 — define the forced continuation before asking for regularity

Define, under critical prime-gap energy,

```text
R_req(s) = W_cont(s) - M_cont(s) - H(s),
```

where `W_cont` is the four-shift valuation-one continuation, `M_cont` is the canonical mesh
continuation, and `H` is the static holonomy counterterm.

**Proved.** On `Re s > 0`, `W_cont` equals the Wold current and `M_cont` equals the original mesh
current. The exact renormalization identity therefore gives

```text
R_req(s) = lowerHardy(-i s).
```

If `zeta(rho)=0` and `Re rho>1/2`, the Wold term has residue `-m(rho)` at `s0=rho-1` with
`m(rho)>=1`. Mesh continuation and holonomy are continuous at `s0`, hence each has zero residue.
Subtracting their punctured-neighbourhood limits leaves residue `-m(rho)` in `R_req`.

### C3 — glue a reflected upper Hardy carrier by edge of the wedge

Conjecture that source reflection supplies an upper-half-plane mate with the same real-boundary
values as the bounded lower-Hardy residual. Edge-of-the-wedge would then continue the physical
residual through the Laplace wall.

**Failed.** The reflected theta packet is formally the negative of the original packet, not an
independent upper-Hardy germ. The residual coefficient bound is exponential in
`-sqrt(log p)`: it gives every polynomial boundary jet but only Gevrey-2-scale control, not a
quasianalytic boundary class. Thus smooth boundary agreement cannot manufacture the missing
continuation. The forced pole is naturally a Stokes jump of a square-root-frequency lift; killing
it requires a new source law, not ordinary reflection or finite jets.

### C4 — transport the simple Wold pole to a fixed Route-U contact

Conjecture that the multiplicity-exact first-order Wold pole forces one fixed finite
shifted-Hankel contact, thereby excluding Route-U's cofinal degree drift.

**Failed.** The Route-U reciprocal moments coalesce under large mass shift and scalarize away the
divisor label carried by the Wold residue. The corpus has no coefficient-faithful map from the
labeled Wold principal part to a fixed Hankel null face. Building that map as an assumption would
insert the missing producer. The surviving typed coupling is instead the formal quotient-orbit
head: it retains the same exact multiplicity and proves every off-line completion needs a nonzero
compensator.

## Theorem

Assume the already-isolated critical prime-gap energy is summable. Define

```text
requiredResidual(s)
  = xiHeatCassiniWoldLaplaceContinuation(s)
  - xiHeatCassiniLogMeshLaplaceContinuation(s)
  - xiHeatCassiniWoldLaplaceHolonomyCounterterm(s).
```

Then:

1. for every `Re s>0`, `requiredResidual(s)` is exactly
   `xiHeatCassiniWoldResidualLowerHardyKernel(-i*s)`;
2. for every zeta zero `rho` with `Re rho>1/2`, there is its exact multiplicity `m>=1` such that
   `(s-(rho-1))*requiredResidual(s) -> -m` on the punctured neighbourhood;
3. consequently the required residual continuation is not continuous at `rho-1` and cannot be
   replaced by any continuation having zero residue there.
4. under critical prime-gap energy, RH is equivalent to continuity of this one forced residual
   continuation at every possible right-half zeta pole.

## Proof

For (1), rewrite Wold continuation by its safe-side equality, mesh continuation by its
critical-energy continuation equality, and use the existing prime-zeta/mesh/holonomy normal form
of the lower-Hardy kernel.

For (2), take the multiplicity-exact Wold residue theorem. The mesh zero-residue theorem applies
because nontrivial zeta zeros satisfy `Re rho<1`, so `rho-1` lies in the open mesh continuation
half-strip and is nonzero. The holonomy counterterm is entire, hence also has zero residue.
The limit of the product with `requiredResidual` is therefore `-m-0-0=-m`.

For (3), continuity at the pole would make the product with the vanishing local coordinate tend
to zero, contradicting uniqueness of limits because `m>=1`.

For (4), use the corpus criterion `RH iff zeta has no zero with Re>1/2`. Under RH the regularity
condition is vacuous. Conversely, any such zero forces noncontinuity by (2)--(3), contradicting
the proposed regularity.

## New knowledge

Route T no longer has three undifferentiated possible compensators. Subject only to its explicit
prime-gap input, mesh and holonomy are proved incapable of compensation. The entire off-line
principal part is forced into one canonical, source-derived continuation of the physical
lower-Hardy residual. Thus the remaining producer is exact and coefficient-faithful:

```text
prove requiredResidual has zero principal part on the physical half-strip.
```

This statement simultaneously meets the formal quotient-orbit leakage law: off line, the
anti-reflected physical head requires nonzero compensating orbit charge, and analytically the
only surviving carrier of that charge is `requiredResidual`. Lean couples the two statements with
one existential multiplicity `m`, rather than merely proving separate nonvanishing results.

## RH status

Not an RH proof. Critical prime-gap energy remains an explicit input, and no unconditional theorem
yet kills the forced residual pole. The result removes mesh and holonomy from the open producer
and makes residual regularity the sole Route-T analytic gate.

## Formalization

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldRequiredResidualContinuation.lean`.
The preceding `XiHeatCassiniWoldRelativeOrbitLeakage` module owns the continuation and residue;
this module adds forced discontinuity, the conditional RH equivalence, and the analytic/formal
same-m compensator theorem without duplicating those declarations. Direct foreground elaboration
with `lake env lean` passes. The module is wired into the RHTower umbrella. Targeted module build
passes. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Global formal
lint reaches the module but fails on unrelated shared-tree umbrella reachability debt in existing
Deninger, Gauss-Hodge, Suzuki, and `CriticalSchurIdealInertiaTransport` modules.

## C5 — source-marked second-factorial Borel carrier

### Corpus derivation and full RH chain

`[CORPUS]` The lower-Hardy residual edge kernel is

```text
K(x) = sum_N R_N (exp(-i h_N x) - exp(-i h_(N+1) x)),
h_N = log p_N,
R_N = WoldPartialMass(N) - log p_N.
```

The corpus proves `R_N -> 0`, the unconditional decay
`|R_N| <= B exp(-c sqrt(h_N))`, lower-ray coefficient faithfulness, all boundary jets, and the
exact equivalence between RH and regularity of the forced residual continuation. It also proves
that compact-open scalar reporters erase source charge and that ordinary upper Hardy reflection
would require a false two-sided residual-variation bound. These results force any viable next
carrier to retain individual prime edges while exploiting the actual Gevrey-2 boundary scale.

Define the branch-free entire kernel

```text
Phi(u) = sum_{k >= 0} u^k / (k!)^2
```

and, for real boundary point `x`, the source-marked Borel germ

```text
B_x(xi) = sum_N R_N
  (exp(-i h_N x) Phi(-i h_N xi)
   - exp(-i h_(N+1) x) Phi(-i h_(N+1) xi)).
```

Its `k`th derivative at `xi = 0` is exactly the corpus residual edge jet divided by `k!`.
Thus it preserves every source-labelled prime edge instead of projecting the residual to a
scalar compact-open limit.

The intended proof chain is exact:

```text
source-marked Borel germ and exact jet recovery
  -> continuation along the positive normal Borel ray with uniform exponential type
  -> Borel-Laplace reconstruction through 0 < Im z < 1/2
  -> zero lateral Stokes jump for the physical lower-Hardy residual
  -> requiredResidual is regular at every possible off-line Wold pole
  -> riemannHypothesis_iff_requiredResidualContinuation_continuousAt
  -> RH.
```

This is not a generic summability program: the required zero-Stokes statement is source-marked,
and `XiHeatCassiniWoldRelativeOrbitLeakage` says that any off-line zero produces a nonzero residue
in precisely this forced residual.

### C5a — local carrier theorem

`[LEAN-PROVED]` There is a radius `r > 0`, independent of `x`, such that
the defining prime-edge series for `B_x(xi)` converges absolutely and locally uniformly on every
compact subset of `R x {xi : |xi| < r}`. Hence `B_x` is holomorphic in `xi` there and its Taylor
coefficients recover all lower-half residual edge jets with the second factorial normalization.

Paper proof. For `0 <= h <= H`, termwise subtraction and
`binom(2k,k) <= 4^k` give

```text
|Phi(-i h xi) - Phi(-i H xi)|
  <= 2 (H-h) |xi| exp(2 sqrt(H |xi|)).
```

Also `|Phi(-i H xi)| <= exp(2 sqrt(H |xi|))`. Splitting an edge atom as

```text
exp(-i h x) (Phi(-i h xi) - Phi(-i H xi))
  + (exp(-i h x) - exp(-i H x)) Phi(-i H xi)
```

bounds it on `|x| <= X` by

```text
C (H-h) (|xi| + X) exp(2 sqrt(H |xi|)).
```

Bertrand gives `H <= 2h` for consecutive prime logs, while corpus exponential-rate control gives
`|R_N| <= B exp(-c sqrt(h))`. Choose, for example, `r = c^2/32`; then the atom is dominated on
compact subdiscs by a constant times

```text
(H-h) exp(-(c/2) sqrt(h)).
```

The corpus reciprocal-height telescope proves this majorant summable. Weierstrass convergence
gives holomorphy. Absolute local uniform convergence of the differentiated series permits
termwise differentiation at zero, and `Phi^(k)(0) = 1/k!`, giving the exact jet identity.

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelCarrier.lean`.
The module proves a global square-root-exponential residual envelope, absolute summability of the
source-labelled two-index carrier on one source-independent disc, exact Fubini regrouping into
the complete residual jet series, and holomorphy on that disc. Direct foreground elaboration and
the targeted module build pass. Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. Global lint is blocked only by unrelated pre-existing umbrella reachability debt.

### C5a.5 — source-ordered safe-ray Borel--Laplace reconstruction

`[LEAN-PROVED]` The negative real ray of `Phi`, corresponding to the physical lower half-plane,
has a canonical global continuation only after preserving source order. For `s >= 0`, define

```text
B^-_x(s) = sum_N R_N
  (exp(-i h_N x) Phi(-h_N s)
   - exp(-i h_(N+1) x) Phi(-h_(N+1) s)).
```

There is `r>0` such that `B^-_x(s)=B_x(-i s)` for `0 <= s < r`; hence `B^-` is a genuine
continuation of C5a's local Borel germ, not a separately assigned sum. Moreover, for every
`x in R` and `y>=0`,

```text
integral_0^infinity exp(-t) B^-_x(y t) dt
  = xiHeatCassiniWoldResidualLowerHardyKernel(x - i y).
```

The key corpus-derived cancellation is the exact Bessel identity

```text
Phi(-r) = J_0(2 sqrt(r)),  r >= 0.
```

The corpus derivative recurrence and `|J_1(u)| <= |u|/2` imply the adjacent-height bound

```text
|Phi(-h s) - Phi(-H s)| <= 2 (H-h) s,  0 <= h <= H.
```

Together with the physical phase-chord bound this gives the source atom majorant

```text
|R_N| (h_(N+1)-h_N) (|x| + 2s).
```

Its source factor is summable by the existing Wold residual prime-log total-variation theorem;
after `s=yt`, its remaining factor is integrable against `exp(-t)`. Tonelli therefore applies in
source order. The scalar identity

```text
integral_0^infinity exp(-t) Phi(wt) dt = exp(w)
```

then reconstructs each lower-Hardy edge exactly. This also proves why raw coefficientwise Fubini
is the wrong global continuation: it destroys the adjacent-source gap before Bessel oscillation
can expose it.

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelBessel.lean`,
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelLaplace.lean`, and
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelSourceLaplace.lean`.
Direct foreground elaboration and targeted builds pass. Closed-axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

### C5b — remaining open core

`[OPEN CORE, SHARPENED]` The full safe negative-ray continuation and lower-half-plane
Borel--Laplace reconstruction are now closed by C5a.5. Prove continuation from the same local germ
along the positive normal Borel ray with the exponential-type control needed for
`0 < Im z < 1/2`, identify both lateral sums source-by-source, and prove their Stokes jump is zero.
This is now the first unproved arrow in the stated RH chain.

#### C5b.1 — absolute positive-ray Tonelli

`[LEAN-DISPROVED]` The direct analogue of C5a.5 on the positive ray cannot use atomwise absolute
Fubini. Let

```text
B^+_{N,x,y}(t) = exp(-t) R_N
  (exp(-i h_N x) Phi(h_N y t)
   - exp(-i h_(N+1) x) Phi(h_(N+1) y t)).
```

The positive real kernel `Phi(r)=sum_k r^k/(k!)^2` is monotone. At `x=0`, this fixes the sign of
every adjacent kernel difference, and the scalar Laplace identity gives the exact atom law

```text
integral_0^infinity |B^+_{N,0,y}(t)| dt
  = |xiHeatCassiniWoldResidualComplexPhaseConnectionAtom(i y,N)|.
```

Hence, for `0<y<=1`,

```text
Summable_N integral_0^infinity |B^+_{N,0,y}(t)| dt
  iff Summable (xiHeatCassiniWoldResidualUpperVariationAtom y).
```

At `y=1/2`, the corpus critical-graph no-go proves this upper variation cannot coexist with the
critical mesh energy required by Route T. Therefore sourcewise absolute positive-ray Tonelli is
not an unavailable estimate; it is a false proof architecture for this chain.

`[POSITIVE SURVIVOR, LEAN-PROVED]` Integrated absolute Borel mass and upper-Hardy edge mass are
identical source-by-source. Thus any viable C5b continuation must perform lateral cancellation or
renormalization before taking source absolute values. It cannot be obtained by strengthening a
majorant for the raw source family.

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelUpperTonelliNoGo.lean`.
Direct elaboration and targeted build pass; the closed-axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

#### C5b.2 — finite Borel Abel renormalization and exact terminal obstruction

`[LEAN-PROVED]` Corpus search exposed three identities that had not yet been combined at Borel
level: the residual recurrence

```text
R_(N+1) - R_N = woldCoeff_(N+1) - (h_(N+1)-h_N),
```

the physical finite Abel transport, and

```text
integral_0^infinity exp(-t) Phi(wt) dt = exp(w).
```

For the source node

```text
Q_N(x,xi) = exp(-i h_N x) Phi(-i h_N xi),
```

finite Abel transport now gives, without a limit or convergence premise,

```text
R_N Q_N + sum_(n<N) R_n (Q_n-Q_(n+1))
  = sum_(n<=N) woldCoeff_n Q_n
    - sum_(n<N) (h_(n+1)-h_n) Q_(n+1)
    - (h_0 + holonomy) Q_0.
```

On the positive normal ray `xi=i y t`, every node and every edge is individually Laplace
integrable. Integrating this finite identity yields exactly the finite
`Wold - logMesh - holonomy` current at

```text
s = i (x + i y) = -y + i x.
```

Thus the Borel construction lands on the same source-faithful approximants whose continuation
defines `requiredResidual`; it does not create a parallel compensator. More sharply, subtracting
the integrated raw edge cutoff from the renormalized cutoff leaves exactly one terminal:

```text
terminal_N(x,y) = R_N exp(-i h_N (x+i y)),
|terminal_N(x,y)| = |R_N| exp(y h_N).
```

Consequently convergence of the two finite-cutoff prescriptions to the same value is equivalent
to vanishing of this explicit weighted terminal. The corpus sharp half-density obstruction then
proves unconditionally that this terminal cannot tend to zero for any `y>1/2`. Hence the maximal
possible source-faithful Borel continuation sector is the strict sub-half strip; no wider-sector
lateral argument can prove RH and then restrict back.

The remaining C5b chain is now exact:

```text
same local Borel germ
  -> cancellation-first lateral continuation for every 0<y<1/2
  -> vanishing/controlled landing of |R_N| exp(y h_N)
  -> finite renormalized cutoffs land on requiredResidual at s=-y+i x
  -> zero Stokes principal part at every possible s=rho-1
  -> requiredResidual continuous at every possible off-line Wold pole
  -> riemannHypothesis_iff_requiredResidualContinuation_continuousAt
  -> RH.
```

First open arrow remains construction of the strict-sub-half lateral limit with enough
source-faithful control to identify it with the required continuation. Absolute Tonelli is false
by C5b.1; extending past half height is false by C5b.2. Any surviving proof must use conditional
cancellation inside the strict strip while retaining the exact terminal flux.

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelAbelRenormalization.lean`.
Direct foreground elaboration and targeted module build pass. Closed-axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

#### C5b.3 — forced rotated continuation and exact divisor charge

`[LEAN-PROVED]` Write the canonical required residual in the source coordinate `s = i z`:

```text
B_req(z) = requiredResidual(i z).
```

On `Im z < 0`, this is exactly the lower-Hardy residual and hence exactly the source-ordered
negative-ray Borel--Laplace sum proved in C5a.5. It is therefore the forced continuation reached
from the Borel germ, not an unrelated branch. If `rho` is an off-line zeta zero of multiplicity
`m`, the corpus required-residual residue `-m` rotates to

```text
lim_(z -> -i(rho-1)) (z+i(rho-1)) B_req(z) = i m.
```

Thus every off-line divisor carries a quantized nonzero imaginary source charge. Under critical
mesh energy, RH is equivalent to continuity of `B_req` at every rotated candidate pole. This
does not yet construct the missing positive-Borel-plane lateral continuation; it fixes exactly
what any such continuation must land on and what charge it must eliminate.

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelStokesCharge.lean`.
Direct elaboration and targeted build pass. Closed-axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

#### C5b.4 — strict-sub-half sector classification

`[LEAN-PROVED]` Corpus generalized von Koch control under RH transfers through the exact chain

```text
RH
  -> |theta(x)-x| = O_eps(x^(1/2+eps))
  -> Mertens prime-log discrepancy = O_eps(x^(-1/2+eps))
  -> centered Wold residual = O_eps(exp(-(1/2-eps) h_N)).
```

The second arrow uses the exact Abel identity against the theta-error density; the third uses the
exact Mertens-plus-positive-Euler-tail decomposition already present in the Wold corpus. Hence RH
forces

```text
|R_N| exp(y h_N) -> 0       for every 0 <= y < 1/2,
```

so the raw and Abel-renormalized finite positive-ray Borel prescriptions asymptotically agree
throughout the entire strict sub-half sector. More sharply, under critical mesh energy,

```text
RH
  iff for every 0 < y < 1/2, the raw residual edge current at i y
      is absolutely summable.
```

`[ROUTE CONSEQUENCE]` Strict-strip absolute convergence is not an easier preliminary estimate: it
already contains the complete RH burden once the independent mesh-energy channel is available.
This retires the plan "first prove raw absolute convergence for every strict height, then use it
to prove RH." A surviving C5b proof must instead produce cancellation-first lateral landing or
another source-faithful regularity mechanism; if it establishes raw absolute convergence on the
whole strict strip, it has in fact proved RH at that step.

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelSubhalfClassification.lean`.
Direct foreground elaboration and targeted module build pass. Closed-axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

#### C5b.5 — exact terminal-first classification

`[LEAN-PROVED]` The finite Abel identity leaves the literal positive-ray terminal

```text
T_N(y) = |R_N| exp(y h_N).
```

Corpus search supplied both directions of a new exact classification. RH gives `T_N(y) -> 0`
for every `0 < y < 1/2` by C5b.4. Conversely, assume this terminal vanishes throughout the
strict sector. For an arbitrary `0 < a < 1/2`, choose `a < c < 1/2`. Since `T_N(c) -> 0`, it is
eventually below one, hence

```text
|R_N| <= exp(-c h_N).
```

The corpus exponential-rate theorem then makes the raw residual edge series absolutely summable
at height `a`. Since `a` was arbitrary, the corpus cofinal source-strip ODE endpoint, together with
critical mesh energy, forces RH. Therefore

```text
RH
  iff for every 0 < y < 1/2, |R_N| exp(y h_N) -> 0
  iff for every x and 0 < y < 1/2,
      finiteRenormalizedCurrent_N(x,y) - finiteRawEdgeIntegral_N(x,y) -> 0.
```

`[ROUTE CONSEQUENCE]` A lateral proof cannot first show that the terminal disappears across the
strict sector and only afterwards identify the joint limit: that preliminary step already proves
RH. The surviving C5b problem is narrower and harder—regularize or identify the terminal-plus-edge
finite current as one object, without independently discarding its terminal flux.

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelTerminalClassification.lean`.
Direct foreground elaboration and the single targeted module build pass. Closed-axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`. Formal lint reaches the module via
the RHTower umbrella and reports only unrelated pre-existing umbrella reachability debt.

#### C5b.6 — unconditional natural Wold residual classification

`[LEAN-PROVED]` Corpus search exposed a stronger route than the mesh-conditional ordered-terminal
classification. Existing forward control gives every strict half-power rate for the centered
natural-cutoff Wold residual under RH. The previously open reverse transport is now closed by
the exact chain

```text
all strict natural Wold residual rates
  -> centered weighted Mertens rates, after subtracting the positive Euler trace tail
  -> exact inverse Abel identity
       theta(N) = N*mertensA(N) - sum_(k<N) mertensA(k)
  -> |theta(N)-N| = O_eps(N^(1/2+eps))
  -> real theta and psi power bounds
  -> ChebyshevErrorPowerSpectrum 0
  -> RH.
```

Consequently Lean proves, without critical mesh energy or another premise,

```text
RH iff every strict half-power rate holds for the natural Wold residual.
```

`[ROUTE CONSEQUENCE]` Natural-cutoff Wold decay across the strict half-range is itself the full RH
burden. This reduced terminal-first continuation to one exact coordinate bridge from ordered-prime
terminal decay to natural-cutoff rates. C5b.7 closes that bridge without critical mesh energy.

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualMertensInverseAbel.lean`.
Direct elaboration and the single targeted module build pass. Closed-axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

#### C5b.7 — unconditional positive-Borel terminal classification

`[LEAN-PROVED]` Corpus search supplied the missing ordered-to-natural bridge. Terminal decay at
`c` gives the ordered residual rate `exp(-c h_k)`. The corpus exact local-increment theorem then
forces the prime-log mesh gap to have every smaller rate `exp(-a h_k)`, `0<a<c`. For each natural
cutoff `N>=2`, construct the consecutive-prime bracket

```text
p_k <= N < p_(k+1).
```

Wold cumulative mass is constant inside this shell, yielding the new interpolation law

```text
|R_nat(N)| <= |R_ord(k)| + (log p_(k+1) - log p_k).
```

Bertrand's unit log-cell bound converts the right side uniformly to `O(N^(-a))`. Hence terminal
decay throughout the strict sector supplies every strict natural Wold rate, and C5b.6 forces RH.
The reverse implication was already C5b.4. Therefore, with no mesh-energy or other premise,

```text
RH
  iff for every 0 < y < 1/2, |R_k| exp(y h_k) -> 0
  iff for every x and 0 < y < 1/2,
      finiteRenormalizedCurrent_N(x,y) - finiteRawEdgeIntegral_N(x,y) -> 0.
```

`[ROUTE CONSEQUENCE]` C5b.5's critical-mesh hypothesis was inessential. Separate disappearance of
the exact positive-ray terminal across the strict sector is unconditionally RH-strength. The
terminal-first lateral route is now definitively retired: any viable continuation must keep
terminal and edge current coupled until final source-faithful landing.

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelTerminalUnconditionalClassification.lean`.
Direct elaboration and the single targeted module build pass. Closed-axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

#### C5b.8 — one-height terminal decay controls Xi zero width

`[LEAN-PROVED]` The unconditional ordered-to-natural bridge also classifies partial terminal
progress. For a single `0<c<1/2`, assume

```text
|R_k| exp(c h_k) -> 0.
```

For every `a<c`, C5b.7 gives natural Wold decay `O(N^(-a))`; inverse Abel then gives Chebyshev
exponent `1-a`. Letting `a` approach `c` through the all-epsilon source spectrum yields

```text
ChebyshevErrorPowerSpectrum (1/2-c)
  -> XiZeroHalfPlaneBound (1/2-c).
```

`[ROUTE CONSEQUENCE]` Positive-Borel terminal height measures literal Xi zero confinement:
gaining height `c` removes transverse zero width `c`. This rules out interpreting a fixed-height
terminal estimate as weak local regularity with no divisor consequence; it is already a global
zero-free-width theorem. Full strict-sector control is the width-zero/RH endpoint.

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelTerminalWidthBound.lean`.
Direct elaboration and the single targeted module build pass. Closed-axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

#### C5b.9 — exact all-width Wold Borel terminal spectrum

`[LEAN-PROVED]` Corpus search gave the full arbitrary-width chain but exposed two missing
transports: generalized Chebyshev width had not been pushed forward through centered Mertens and
Wold coordinates, and all strict terminal heights had not been closed back to the exact endpoint
width. Both are now proved.

For every `0 ≤ alpha < 1/2`, Lean proves

```text
XiZeroHalfPlaneBound alpha
  iff for every 0 < y < 1/2-alpha,
        |R_k| exp(y h_k) -> 0.
```

Forward direction is the unconditional chain

```text
Xi width alpha
  -> Chebyshev spectrum alpha
  -> theta exponent 1/2+alpha+delta
  -> centered Mertens rate 1/2-alpha-delta
  -> natural Wold rate
  -> ordered Wold rate
  -> terminal decay below complementary frontier.
```

Reverse direction uses C5b.8 at terminal heights cofinal below `1/2-alpha`. Height is chosen as
function of requested Chebyshev epsilon, recovering `ChebyshevErrorPowerSpectrum alpha` exactly;
the corpus square-window collision then gives `XiZeroHalfPlaneBound alpha`. No endpoint terminal
decay is assumed.

`[ROUTE CONSEQUENCE]` Positive-Borel terminal height is not merely one-way zero confinement: its
complete strict-height spectrum is exactly complementary to Xi zero width. The specialization
`alpha=0` is RH; partial progress at any width is quantitatively classified. Any proposed Route-T
producer can now be judged by its maximal terminal-height frontier, which converts without loss
into exact zero-free width.

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelTerminalWidthSpectrum.lean`.
Direct elaboration and single targeted build pass (`12540/12540`). Closed-axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

#### C5b.10 — exact all-width natural Wold residual spectrum

`[LEAN-PROVED]` The natural-cutoff invariant also has a complete partial-width law. Define
`WoldNatResidualPowerSpectrum alpha` to mean

```text
for every 0<c<1/2-alpha,
  |R_nat(N)| = O(N^(-c)).
```

For every `0 ≤ alpha < 1/2`, Lean proves

```text
XiZeroHalfPlaneBound alpha
  iff WoldNatResidualPowerSpectrum alpha.
```

Forward direction transports generalized von Koch through theta, exact Abel--Mertens, and Euler
trace correction. Reverse direction chooses natural power rates cofinally below
`1/2-alpha`, applies exact inverse Abel, then closes theta to psi and Xi width. No ordered-prime
gap interpolation or boundary exponent is assumed.

`[ROUTE CONSEQUENCE]` Natural cutoff is an exact zero-width coordinate at every partial width,
not merely RH endpoint. Any future local-average/Tauberian producer can target natural residual
decay directly; ordered mesh effects belong only to transport back to prime-indexed Borel
coordinates. The `alpha=0` specialization is RH.

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualNaturalWidthSpectrum.lean`.
Direct elaboration and single targeted build pass (`12541/12541`). Closed-axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

`[HOSTILE AUDIT]` C5a.5 removes safe-side reconstruction but cannot imply C5b. Gevrey-2 jets admit
flat ambiguity, so agreement on one ray does not determine continuation across the singular
normal direction or its lateral Stokes data. The Bessel gap estimate is oscillatory only on the
proved negative ray; replacing it by absolute growth on the positive ray loses summability.
Ordinary scalar reflection and compact-open limiting remain ruled out by corpus no-go theorems.
Conversely, any nonzero Stokes jump must be tested against the exact Wold-pole residue rather than
discarded: off line, that jump is the expected carrier of source charge.

### Novelty audit

`[SOTA, checked 2026-08-29]` Searches of primary literature found general factorial/moment
summability theory, Borel resummation and Stokes analysis for classical zeta transforms, and
Bessel identities for Dirichlet series with Hecke functional equations. No source found the
prime-edge Wold residual germ above, its exact jet-recovery law, or a Stokes/Wold-residue
correspondence. Relevant adjacent sources: Lastra--Sanz--Sendra (arXiv:1603.00689),
Jimenez-Garrido--Sanz (arXiv:1510.05844), Andersen (arXiv:2011.01110), and
Berndt--Dixit--Gupta--Zaharescu (arXiv:2204.09887).

#### C5b.11 — exact critical-window natural Wold local-mean spectrum

`[LEAN-PROVED]` Corpus search exposed a local Tauberian rigidity law specific to natural Wold
source. Its cumulative arithmetic mass is monotone, while centering subtracts `log N`; hence for
`M <= N`,

```text
R_nat(M) <= R_nat(N) + log N - log M.
```

A positive residual spike therefore persists to right and a negative spike persists to left. On
`Icc(N-sqrt(N), N+sqrt(N))`, logarithmic drift has critical size `O(N^(-1/2))`. Consequently, for
every `0 <= alpha < 1/2`, Lean proves exact equivalence

```text
XiZeroHalfPlaneBound alpha
  iff for every 0<c<1/2-alpha,
      average_(|n-N|<=sqrt(N)) n^c * |R_nat(n)| is eventually bounded.
```

Forward recovery uses already exact pointwise natural Wold spectrum. Reverse recovery is not a
hidden supremum estimate: center has relative mass `1/(2*sqrt(N)+1) -> 0`. Instead, half of
square-root window inherits each signed spike by one-sided persistence; mean controls that entire
half-window, and strict sub-half exponents absorb logarithmic drift. Specializing `alpha=0` yields
closed unconditional theorem

```text
RH iff WoldNatResidualSqrtMeanSpectrum 0.
```

`[ROUTE CONSEQUENCE]` A diffuse mesoscopic `L1` statistic, with no adaptive radius, mesh-energy
premise, ordered-prime gap input, or computation, carries complete Xi zero-width spectrum. This
supplies a source-specific local-to-pointwise Tauberian mechanism and a direct producer target for
Route T: any proof of critical square-root local means closes RH through C5b.10.

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualNaturalSqrtMeanSpectrum.lean`.
Direct elaboration and single targeted module build pass (`12542/12542`). Closed-axiom audit of
reverse equivalence, all-width theorem, and RH endpoint reports only `propext`,
`Classical.choice`, and `Quot.sound`. Global non-build lint recognizes module through RHTower
umbrella; its failure list contains only pre-existing unreachable modules elsewhere.
