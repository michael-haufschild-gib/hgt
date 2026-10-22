# Route J pure-incidence Hodge countertransport

- **ID:** route-j-pure-incidence-hodge-countertransport
- **Stage:** 1-in-progress
- **Type:** FALSIFIED + THEOREM (Lean)
- **Source:** `route-j-principal-relative-julia-current.md` · Sections 46--48
- **Statement:** Dual pure defect--defect and packet--packet incidence classes give a nonzero
  source-defined countertransport which is invisible to every mixed Gamma/Hardy reflection
  coordinate; its two-leg Gamma landing, actual admission, and uniform carrier capacity are
  unconditional, while descent of its Poincare readout to a bounded completed source functional
  is the remaining hard question.

## Goal

Test the finite pure-sector survivor exposed by cell-diagonal rigidity.  Construct it from the
actual Calderon--Witt degree-one source, not by projecting an arbitrary completion, and decide
whether its dual Hodge pairing supplies the missing principal-relative Julia current or whether
every completed readout is forced to remain singular.

## Gates

- [x] 0 → 1 in-progress: source-pure object, exact attack, Door passport
- [x] 1 → 2 fully-proven: completed Poincare readout class-completely excluded
- [ ] 2 → 3 formalized: every dependency-closed theorem in Lean; exact-module audit green
- [ ] 3 → 4 publication-ready: standalone theorem, proof, Lean certificate, external priority audit

## Frozen conjecture — pure-polarization transgression

`[FALSIFIED J-PIH]`

Let `d_i` and `w_i` be the normalized Calderon defect and rational-Witt packet generators in a
prime-power cell `i`.  For distinct cells `i,j`, put

```text
D_ij = d_i wedge d_j,
P_ij = w_i wedge w_j,
H(D_ij)=P_ij,  H(P_ij)=D_ij.
```

The arithmetic source, Gamma/co-Poisson packet transport, and the local Calderon--Witt cup pairing
construct a Hausdorff completion of the fixed pure Hodge line `C(D_ij+P_ij)` over the cofinal
prime/depth system.  On that completion, the dual Poincare coefficient pairing descends to one
closed source functional whose finite codiagonals are the primitive-promoted two-scale current and
whose norm is bounded by the source-normal pure-carrier capacity.

Physical meaning: two Gamma legs should be transported as two packet legs; their dual defect pair
supplies orientation and positivity without placing the mixed defect--packet witness outside the
actual admitted sector.

This was not `closedness` renamed.  It predicted a specific completion of a canonical pure Hodge
plane and a specific descended functional.  The continuous-linear no-go below supplies its stated
falsifier: every completion retaining the uniform carrier norm and exact finite Poincare
codiagonals forces divergent readout norm.

## Unconditional bridge A — pure incidence is a nonzero silent kernel

The cell cup is the alternating polarization of a defect/packet cross-effect.  Therefore

```text
d_i cup d_j = 0,
w_i cup w_j = 0
```

for all cells, and in particular `D_ij,P_ij` are exact cell Milnor incidences when `i!=j`.
Every actual ordered Gamma/Hardy reflection coordinate is also mixed:

```text
partial_a(X)(p,q)
 = gamma_a(p,q)
   (delta_p wedge pi_q)(X).
```

Hence, for every displacement `a` and every ordered boundary coordinate,

```text
partial_a(D_ij)=partial_a(P_ij)=0.                    (PIH-1)
```

Independent pure exterior coordinates give

```text
(delta_i wedge delta_j)(D_ij)=1,
(pi_i wedge pi_j)(P_ij)=1,                            (PIH-2)
```

so neither class is zero.  Thus finite actual admission has a genuine pure kernel at every
displacement; mixed-cell diagonal rigidity does not classify the whole incidence kernel.

## Unconditional bridge B — two packet legs give the missing two-leg landing

For an arbitrary cell coefficient family `c`, degree-one Gamma transport fixes defects and scales
packets.  Its exterior lift therefore satisfies

```text
T_c(D_ij)=D_ij,
T_c(P_ij)=c_i c_j P_ij.                               (PIH-3)
```

This is the first construction in this Route-J branch where the product of both primitive Gamma
amplitudes is produced by the source endomorphism itself.  It is not inserted as a scalar after a
mixed cup, which has only one packet leg.

With critical depth deattenuations `D(p,r)` and diagonal coefficients
`c_(p,r)=J_0(p,r)`, equation `(PIH-3)` gives exactly

```text
D(p,r)D(q,s)c_(p,r)c_(q,s)=J_0(p,0)J_0(q,0).          (PIH-4)
```

Thus equal spreading over `K(p)K(q)` actual depths produces the previously proved landed profile
`U_n(p,q,r,s)` without post-transport scalar fitting.  Concretely, the prelanding carrier has
defect--defect coefficient `U_n` and packet--packet coefficient

```text
2 kappa_n(p,q) D(p,r)D(q,s)/(K(p)K(q)),
```

where `kappa_n` is the source height/phase kernel before both primitive amplitudes.  The actual
packet-leg source endomorphism sends their full cofinal finite sum exactly to `(PIH-5)`.

## Unconditional bridge C — actual admission and uniform capacity

Pair the two pure sectors after landing:

```text
A_n(p,q,r,s)
 = U_n(p,q,r,s)(D_(p,r;q,s)+P_(p,r;q,s)).             (PIH-5)
```

The involution `H` exchanges the two displayed summands, so `(PIH-5)` is fixed.  Equation `(PIH-1)`
places it in the actual Gamma/Hardy admitted sector for every modular displacement, not merely in
the compensated finite-index profile sector.  Incidence Green retraction fixes it because both
pure summands have zero cell cup.

Counting both pure Hodge components gives capacity

```text
U_n^pure
 = 2 sum_(p,q,r,s) U_n(p,q,r,s)^2
 = 2 U_n
 <= 200 * 289^2.                                     (PIH-6)
```

The depth codiagonal of either component still recovers the original two-scale current.  Both the
prelanding and landed full finite sums lie in the actual admitted sector for every displacement;
the landed sum is fixed by the exact cell Green retraction.

## Hostile audit — exact open core

`(PIH-1)` is both the advantage and the obstruction.  Every readout factoring through the existing
Gamma/Hardy mixed boundary annihilates the entire pure carrier.  The algebraic Poincare coefficient
pairing detects it, but its finite codiagonal has the same norm-growth obstruction as the old mixed
carrier:

```text
anchoredTwoScaleEnergy(n)
 <= gain_n sqrt(U_n^pure)
 -> gain_n >= constant * n.                           (PIH-7)
```

Therefore finite pure admission plus uniform coefficient capacity does not close Route J.  In
fact `(PIH-7)` is class-complete for bounded linear descent.  If `x_n` are realizations in any
complex seminormed space with

```text
||x_n|| <= sqrt(U_n^pure)
```

and one continuous linear functional `L` has exact finite values

```text
L(x_n)=anchoredTwoScaleEnergy(n),
```

then its operator norm supplies one fixed `gain` in `(PIH-7)`, contradiction.  No normed
coefficient-faithful completion preserving `(PIH-6)` can regularize the codiagonal.  A different
topology can evade this only by losing the Route-J capacity bound or by leaving the scalar output
vertical/non-descended.

## No-go closure

- **Exact killing theorem/mechanism:** All existing mixed Gamma/Hardy consumers vanish on the pure
  sector.  Any exact scalar codiagonal has gain at least `(5/289)n`; the generic continuous-linear
  theorem excludes every normed completion retaining uniform carrier norm and exact finite
  readout.
- **Strongest positive survivor:** Canonical nonzero pure Hodge pair with two-leg source landing,
  actual admission for every displacement, Green fixedness, exact readout, and uniform carrier
  capacity.
- **New insight:** Actual cell admission is not finite-span rigid.  It decomposes into a detectable
  mixed sector and a boundary-silent dual-pure sector; only a secondary Poincare transgression can
  turn the latter into a Julia current.
- **Status:** Dependency-closed paper proof and unconditional Lean module
  `CCMFirstClockPrimitivePromotedPureHodgeCountertransport.lean`; final targeted audit pending.

## Log

- 2026-08-02 — Frozen `J-PIH`; extracted pure-sector survivor from mixed-coordinate rigidity and
  identified coefficient-faithful completed Poincare descent as exact open core.
- 2026-08-02 — Constructed complete prelanding and landed cofinal pure-Hodge carriers.  Proved
  exact two-packet Gamma landing, actual admission at every displacement, Green fixedness, exact
  codiagonal, and capacity `<=200*289^2`.  Falsified `J-PIH`: bounded readout gain grows at least
  `(5/289)n`, and no continuous linear functional on any normed uniform-capacity realization can
  retain all finite codiagonals.  Lean declarations are in
  `CCMFirstClockPrimitivePromotedPureHodgeCountertransport.lean`.
