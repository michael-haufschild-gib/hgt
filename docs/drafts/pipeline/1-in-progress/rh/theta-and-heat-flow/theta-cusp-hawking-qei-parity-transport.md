# Theta-cusp Hawking QEI parity transport

- **ID:** `theta-cusp-hawking-qei-parity-transport`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / RH PRODUCER
- **Scientific status:** `[EXACT CLAIM] [RH-EQUIVALENT] [HAWKING BRIDGE LEAN-PROVED]`
  `[OPEN PRODUCER] [NOVELTY UNVERIFIED]`
- **Source:** `docs/reports/endpoints.md`; theta tilt-flux, Euler-safe observability,
  Weil-parity, reflected-Riccati, and horizon Schwarzian corpora
- **Statement:** The completed theta source obeys a source-native horizon complete-passivity/QEI
  law: every finite exterior Euler packet exports at least as much reflection-even modular energy
  as reflection-odd cross-horizon energy.

## Goal

Prove the literal theta tilt-flux endpoint

```text
forall d,c,w, Re(w_j)>1/2 -> d/da E_a(c,w)|_{a=0} >= 0,             (HQEI)
```

where `E_a = tiltCorrelation thetaCuspTiltSource c w a`.
Existing Lean proves `(HQEI) <-> RH`. A non-circular proof must construct the horizon state,
Bogoliubov/modular dynamics, and vacuum subtraction directly from the positive theta source and
prime--Gamma channel. It may not assume Xi zero locations, Weil positivity, critical-kernel PSD,
passive completed response, or the desired derivative sign.

`docs/reports/endpoints.md` is the canonical endpoint inventory. The theta tilt-flux endpoint is
selected over a renamed Hawking version of an RH wall because its source is already literal and
positive, its scalar and two-real-node sectors are unconditional, and its sole remaining content is
multi-mode cross-horizon coherence.

## Exact arithmetic horizon variables

Let

```text
k(x) = thetaCuspFullSource(x) > 0,
L(w) = integral_R k(x) exp(w x) dx = xiCent(w),
q_u(t) = 2 log k(u) - log k(u+t) - log k(u-t).
```

Then

```text
k(u+t) k(u-t) = k(u)^2 exp(-q_u(t)).                              (1)
```

Write `q_1,q_2,q_3` for the first three displacement jets. Existing Lean proves

```text
M_u(t) = 2 q_1(u,t) q_2(u,t) - q_3(u,t) >= 0    for t>=0.         (2)
```

For `C>=0`, define the source-normalized conformal ray by

```text
p_u'(t) = exp(2 q_u(t)),
kappa_u(t) = -p_u''(t)/p_u'(t) = -2 q_1(u,t).
```

Its Schwarzian conformal flux is

```text
F_C,u(t) = -C {p_u,t}
           = 2 C (q_1(u,t)^2 - q_2(u,t)),                         (3)

F_C,u'(t) = 2 C M_u(t) >= 0.                                     (4)
```

With `C=c/(24 pi)`, put `S_u=-(c/6)q_u`. Equation `(3)` is exactly the
Bianchi--Smerlak relation

```text
F_C,u = (1/(2 pi)) ((6/c) S_u'^2 + S_u'').                        (5)
```

Thus the global theta Riccati theorem is an unconditional monotone conformal-vacuum flux law, not
a metaphor. The flux includes the signed `-q_2` vacuum term that positive-supercarrier routes lack.

## Exact horizon form of the RH endpoint

For a finite packet

```text
f(r) = sum_j c_j exp(w_j r),       Re(w_j)>1/2,
```

let `B(w,v)=sourceBezoutian thetaCuspTiltSource w v`. The change of variables
`x=u+t`, `y=u-t`, followed by

```text
1/(w+conj(v)) = integral_0^infinity exp(-(w+conj(v))s) ds,
```

gives the source-only representation

```text
Re sum_j,l c_j conj(c_l) B(w_j,w_l)
 = 4 integral_{s>0} integral_R integral_R
       u k(u)^2 exp(-q_u(t))
       Re(f(u+t-s) conj(f(u-t-s))) dt du ds.                       (6)
```

Splitting at the horizon center `u=0` gives

```text
Q_Theta(f) = H_out(f) - H_in(f),                                  (7)
```

where

```text
H_out(f) = 4 integral_{s,u>0,t in R} u k(u)^2 exp(-q_u(t))
  Re(f( u+t-s) conj(f( u-t-s))) dt du ds,

H_in(f) = 4 integral_{s,u>0,t in R} u k(u)^2 exp(-q_u(t))
  Re(f(-u+t-s) conj(f(-u-t-s))) dt du ds.
```

Equation `(7)` identifies the established Weil even-minus-odd energy with an exterior-minus-
interior horizon correlation. The active claim is exactly

```text
H_in(f) <= H_out(f) for every finite exterior Euler packet f.      (8)
```

Existing endpoint chain gives `(8) <-> (HQEI) <-> RH`.

## Hawking/QEI producer under attack

Construct, without divisor data, a phase-sensitive chiral horizon channel satisfying all three
conditions:

1. outgoing one-particle covariance is the literal reflected theta kernel in `(1)`;
2. renormalized wedge modular-energy form is exactly `H_out-H_in`, including the signed
   Schwarzian vacuum term in `(3)`;
3. half-sided modular passivity or a sharp 2D CFT QEI proves the form nonnegative on the finite
   exponential packet domain.

Prime-log KMS channels supply candidate finite Hawking modes. The Gamma orientation phase supplies
the required clock/holonomy. Assembly must be a growing signed Bogoliubov/symplectic limit, not a
fixed positive spectral carrier.

First open core:

```text
THETA-HORIZON-WELD:
construct the source-explicit renormalized Bogoliubov/modular map whose quadratic modular-energy
form evaluates to equation (6), and prove implementability/passivity before any Xi specialization.
```

## Hostile audit

1. **Local-to-global gap.** `(4)` proves local displacement-flux monotonicity and existing work
   transports it to ordered three-point correlation positivity. It does not imply all finite
   packet positivity in `(8)`.
2. **Circular representation risk.** An abstract Hilbert-space factorization of `B` exists exactly
   when `B` is PSD. Calling that factorization a CFT state would restate RH. State and channel must
   be explicit from `k`, prime modes, and Gamma phase.
3. **Positive-carrier no-go.** Raw reflected Stokes mass already exceeds completed seam mass.
   Exact repair needs negative central/first-moment corrections. A dominating positive thermal
   measure cannot realize `(6)`.
4. **Fixed-finite no-go.** Fixed finite KMS/Wightman and thermal-moment realizations are excluded.
   Only a growing renormalized limit can survive.
5. **Phase loss.** Gamma intensity is differentially algebraic and does not recover orientation
   phase. Intensity-only Hawking data cannot control reflection-odd energy.
6. **Real-axis insufficiency.** Scalar packets and two ordered positive-real nodes are already
   nonnegative. Any failure is complex-node multi-mode interference localized near an off-line
   reflected Xi fibre.
7. **Novelty boundary.** Bianchi--Smerlak flux, sharp 2D CFT QEIs, Weil positivity, and scaling
   Hamiltonians are parent theories. No located source combines them with the completed theta
   source or formula `(6)`; absence from targeted search is not proof of novelty.

## Killed alternatives

- `Weil form = Hawking energy`: circular; Weil positivity is RH-equivalent.
- functional-equation reflection alone forces zero flux: false; reflection cancels vectors, not
  quadratic budgets.
- independent positive prime horizon channels: divergent critical `1/p` mass and missing
  cross-prime incidence.
- fixed two-light completion: phase leakage and divergent positive mass.
- raw natural-aperture Cauchy energy: grows linearly while Xi target has only square-root envelope;
  Ward defect tends to `-infinity` unconditionally.
- plain positive Stokes completion: impossible by zeroth- and first-moment excess.

## Gates

- [x] 0 -> 1 in-progress: exact RH endpoint, source-pure variables, Hawking bridge, kill tests,
  first open core
- [ ] 1 -> 2 fully-proven: dependency-closed construction and proof of `THETA-HORIZON-WELD`
- [ ] 2 -> 3 formalized: unconditional Lean theorem for complete-passivity producer; formal lint
  and axiom audit pass
- [ ] 3 -> 4 publication-ready: external priority audit, standalone mathematical paper, no physics
  claim beyond proved conformal-channel hypotheses

## Primary literature boundary

- E. Bianchi and M. Smerlak, *Entanglement entropy and negative energy in two dimensions*,
  <https://arxiv.org/abs/1404.0602>.
- C. J. Fewster and S. Hollands, *Quantum energy inequalities in two-dimensional conformal field
  theory*, <https://arxiv.org/abs/math-ph/0412028>.
- A. Connes and C. Consani, *The scaling Hamiltonian*,
  <https://arxiv.org/abs/1910.14368>.

## Formal dependencies

- `ThetaCuspGlobalReflectedRiccati.lean`
- `ThetaCuspReflectedHawkingFlux.lean`
- `ThetaCuspTiltFluxSourceWeld.lean`
- `ThetaCuspTiltFluxObservabilityWeld.lean`
- `ThetaCuspTiltFluxWeilParityWeld.lean`
- `ThetaCuspTiltFluxWeilParityCauchyLocalization.lean`
- `HorizonBogoliubovGammaObservability.lean`
- `PeelingSchwarzianFlux.lean`

## Log

- 2026-08-22 — selected from canonical endpoint inventory; positive-carrier and fixed-finite
  Hawking routes retired; exact theta Riccati/Bianchi--Smerlak flux bridge and horizon
  exterior-minus-interior representation isolated; `THETA-HORIZON-WELD` opened. Flux bridge
  formalized in `ThetaCuspReflectedHawkingFlux.lean`; targeted build passes and axiom audit reports
  only `propext`, `Classical.choice`, and `Quot.sound`.
