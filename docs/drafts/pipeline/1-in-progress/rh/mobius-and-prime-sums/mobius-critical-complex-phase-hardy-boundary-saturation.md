# P-G160 — Complex Möbius Hardy boundary saturation and sharp four-unit budget

- **Route:** P / C47--C49 source metric and four-unit Ward boundary
- **Status:** paper proof complete; Lean scratch check passed and umbrella wired; axiom/lint audit pending; RH not proved
- **Lean:** `RHTower/MobiusCriticalComplexPhaseHardyBoundarySaturation.lean`
- **Statement:** the actual precritical arithmetic source/Fisher Gram converges entrywise to a
  universal positive Hardy/Fisher block, its two-node residual tends to zero, and four is the sharp
  universal bottom budget.

## Goal

Determine whether P-G159's positive complex source Gram leaves an independent orthogonal budget
for the strict-right Ward complement at the critical boundary. Preserve every non-diagonal phase;
do not divide by the singular Gamma/Xi graph normalizer.

## Gates

- [x] 0 → 1 in-progress: source-pure conjecture and exact critical profiles identified
- [x] 1 → 2 fully-proven: complete algebraic/limit proof, `[PROVED HERE]`, no RH premise
- [ ] 2 → 3 formalized: scratch check and umbrella complete; axiom/lint audit pending
- [ ] 3 → 4 publication-ready: external novelty limited; source--Ward incidence remains open

## Conjecture loop

### P-G160a — the critical source/Fisher block loses positivity

For inward nodes `Re u_i>=0`, augment the complex-damped source packet by the completed Fisher
tangent. At `sigma>1` this is an actual Hilbert Gram. Along `sigma→1+`, its blocks converge to

```text
K∞(u,v) = 1/(1+v+conj u),
g∞(u)   = 2u/(1+u)^2,
E∞      = 4.
```

**FALSIFIED.** Entrywise limits of finite PSD complex matrices are PSD. Hence every finite inward
packet has the unconditional boundary block

```text
[ K∞(u_i,u_j)   conj(g∞(u_i)) ]
[ g∞(u_j)              4       ] >= 0.                 (P-G160.1)
```

The proof uses only the exact arithmetic Gram P-G159, the already-proved complex Fisher-score
limit, and the already-proved four-unit tangent norm limit.

### P-G160b — the diagonal four contains positive orthogonal slack

Let `phi_u(y)=exp(-(1/2+u)y)` on the critical half-line. For real `t>0`, the two-feature
difference quotient

```text
h_t = (2-2/t) phi_0 + (2/t) phi_t
```

approximates the completed score source `2(1-y)exp(-y/2)`. Its augmented Gram residual is exactly

```text
Q(t) = 8 t^2 (2t+3) / ((1+t)^2(1+2t)) → 0.            (P-G160.2)
```

**FALSIFIED.** Thus source lies in closure of Cauchy-feature span and consumes whole four-unit
bottom budget. If common bottom budget is lowered to `B`, same quadratic becomes
`Q(t)+B-4`; for every `B<4`, some two-node packet has negative quadratic form. Therefore

```text
all finite inward packets PSD with budget B  ==>  4 <= B.       (P-G160.3)
```

This is sharp minimality, not a sufficient-bound restatement.

## No-go closure

- **Exact killing mechanism:** two-node difference quotients converge to completed Fisher source;
  residual `(P-G160.2)` tends to zero. Any fixed positive orthogonal allocation forces effective
  source budget below four and violates PSD by `(P-G160.3)`.
- **Strongest positive survivor:** exact universal matrix `(P-G160.1)`, exact residual
  `(P-G160.2)`, and sharp budget law `(P-G160.3)`.
- **New insight:** strict-right Ward complement cannot be attached as independent direct-sum
  channel. Only coherent source--complement cross terms in same graph-normal Hardy metric can keep
  total boundary budget four.
- **Status:** paper proof dependency-closed; Lean scratch check passed; umbrella wired
  cache completes.

## Hostile audit

- Classical half-plane Hardy theory already identifies `K(z,w)=1/(z+conj w)` and its Laplace/RKHS
  realization; see Galé--Matache--Miana--Sánchez-Lajusticia, *Hilbertian Hardy-Sobolev spaces on a
  half-plane*, <https://arxiv.org/abs/2401.16091>. Generic Cauchy-kernel positivity and derivative
  approximation are not claimed as external novelty.
- Internal corpus search found no prior theorem combining exact squarefree Möbius complex clock,
  completed Fisher row, entrywise arithmetic critical landing, explicit two-node residual, and
  sharp universal budget minimality.
- Corpus-new content is arithmetic identification and consequence for Route P: graph-normal source
  already exhausts four-unit boundary budget. External novelty of that combined statement remains
  unverified.

## Higher principle

Earlier attempts treated source and Ward complement as two energies to be bounded separately.
Critical boundary instead behaves as one saturated tangent vector in one Hardy RKHS. Separate
positivity destroys cancellation information; singular division then magnifies this mistake. Route
P must identify actual complement as coherent deformation of source vector and control full norm,
including cross term, before critical quotient.

## Exact next producer

In graph-normal metric, write strict-right Ward column as `g_sigma + c_sigma`, where `g_sigma` is
the exact Möbius Fisher source row. Prove or falsify one source-pure cross-term law

```text
2 Re <g_sigma,c_sigma> + ||c_sigma||^2 <= 4-||g_sigma||^2
```

uniformly on finite conjugate complex packets as `sigma→1+`. Independent bounds on `g_sigma` and
`c_sigma` are now ruled out by `(P-G160.3)`.

## Log

- 2026-08-14 — P-G160a no-go conjecture falsified: full arithmetic augmented Gram stays PSD at
  critical boundary.
- 2026-08-14 — P-G160b orthogonal-slack conjecture falsified by exact two-node residual; sharp
  four-unit minimality proved on paper and encoded in Lean.

### P-G160c — a coherent escaped-mass cross term can hide inside four units

The prior Fisher--Stein contact module already identifies `(1+u)⁻¹` as the critical escaped-mass
transform; that profile itself is not new.  What was open was whether it can occur as a coherent
cross term without increasing the saturated Fisher diagonal.  For `d∈ℂ`, replace the Fisher row by

```text
g_d(u) = 2u/(1+u)^2 + d/(1+u)
```

while keeping the diagonal equal to four.  Translate the two-node saturation coefficients by
`conj(d)` at node zero.  Direct expansion gives the exact quadratic

```text
Q_d(t) = 8 t^2(2t+3)/((1+t)^2(1+2t)) - |d|^2.        (P-G160.4)
```

**FALSIFIED.** For every `d≠0`, `Q_d(t)<0` for some finite `t>0`.  Hence positivity on only the
canonical two-node packets forces `d=0`.  This is stronger than budget minimality: it classifies
the escaped-mass tangent as forbidden at fixed four-unit energy unless its scalar coefficient
vanishes.

**Novelty boundary.** Critical mass profile and Fisher orthogonality were already present in
`MobiusCriticalFisherSteinContact.lean`.  Corpus-new content is exact fixed-diagonal Gram deficit
`(P-G160.4)`, finite negative witness, and two-node mass-mode rigidity.  Lean declarations are in
`MobiusCriticalComplexPhaseHardyBoundarySaturation.lean`; scratch validation passes and umbrella
wiring is complete.

Allowing bottom budget `B` sharpens `(P-G160.4)` to

```text
Q_(d,B)(t)=Q(t)+B-4-|d|^2,
all canonical two-node packets PSD  ==>  4+|d|^2 <= B.  (P-G160.5)
```

This is exact second-order curvature toll.  Therefore a first-order mass deformation `epsilon*d`
requires diagonal surplus at least `epsilon^2|d|^2`.  A same-diagonal positive graph-complement
extension is not generic positivity infrastructure; it is already rigidity forcing `d=0`.

- 2026-08-14 — full module scratch-checked; mass rigidity and `4+|d|²` toll close without
  placeholders; wired into `RHTower` umbrella.
