# Renormalized Biarithmetic Geometry (RBG)

Namespace `GaloisForLFunctions.RenormalizedBiarithmeticGeometry`; umbrella `RenormalizedBiarithmeticGeometry.lean`.

**Question.** Over $\mathbb F_q$ Weil uses one pairing on $C\times C$ that is *positive* (Hodge index), *Frobenius-equivariant*, *pinned to
the arithmetic point* (Lefschetz counts actual points) and *finite on the diagonal* ($\Delta^2=2-2g$). Over $\mathbb Z$ these four properties
live on four different objects. Which mechanism glues them back — which renormalization of the diagonal keeps positivity
through the scale limit, which coupling of $+1$ and $\times p$ pins the arithmetic point, which non-scaling invariant makes
amplification lossless, and which local geometry replaces the global extremum Weil never needed?

> Over $\mathbb Z$, positivity and scale equivariance separate only at divergent self-energies, and multiplicative data see the
> arithmetic point only through the successor. Positivity passes a scale limit exactly on the null cone of the counterterm;
> a theorem must say which cone that is, and must carry $(+1,\times p)$ holonomy before it claims selectivity.

---

## 1. Place in the research

All routes end at forcing reflection $\rho\mapsto1-\rho$ and conjugation $\rho\mapsto\bar\rho$ to agree. The exhaustion laws are projections of one
**fission** of Weil's pairing:

| Weil over $\mathbb F_q$ | Over $\mathbb Z$ | Where pieces separate |
|---|---|---|
| positivity + equivariance in one form | $D$ (positive) vs $W$ (equivariant), $\Re W=D-\Delta$ | symmetric Hecke defect $E_f(L)$ |
| finite $2-2g$ | torsion and archimedean energies equivariant only after a divergent counterterm | the counterterm and its null cone |
| Frobenius localizes and commutes | boosts, unipotent successor, elliptic $\sigma_\gamma$ | conductor horizon vs forcing threshold |
| pinned base | multiplicative forms gauge-blind; $\operatorname{Aff}(\mathbb Q)$ states split at the Kakutani wall | $(+1,\times p)$ survives only on finite horizons, cells, escape limits |

| Programme | Takes / adds |
|---|---|
| ConjugateDiagonalGeometry, ArithmeticPolarization | $D,W,\Delta,E_f(L)$, theta readings / dyadic amplification with fixed loss, Hecke moment problem |
| ArithmeticEffectivityTheory | Torsion orbits, Abel energy / survival law; torsion counterterm full rank |
| BiarithmeticGaugeGeometry | Gauge torus, successor connection, log-cells / gauge charge = square class; cells fix the gauge |
| ArithmeticCorrespondencePositivity | Terminals, outward rays / critical discs, terminal lens, Harnack |
| ArithmeticPositiveDuality | Kakutani wall / finite-horizon side of interior–boundary duality |
| ArithmeticDefectRigidity | Escape modules as boundary objects |
| RenormalizedArithmeticPotentialTheory, ArithmeticIntersectionTheory | Coupled survival, horizon regulator; anomaly |

---

## 2. Why: what RBG found

1. **The survival cone is the module of relations.** For a periodic Abel germ the counterterm is the Cesàro Gram of the modes;
   positivity survives on linear relations among them. Archimedean germ (all modes 1): the polar hyperplane, where the
   digamma Hankel form is positive. Torsion germ: identity counterterm, nothing survives, limit indefinite. The **pole node**
   (order-one orbit) completes the archimedean germ to a positive kernel. Ramanujan twins survive exactly on per-order
   relations, and their pole-node block carries the primes: entry $-\varphi(m)\Lambda(t)$ at orders $m,mt$ — a digamma sum at rational points.
2. **Lossless amplification.** $D(f)$ is a non-scaling invariant: $E(2^kL)\ge D(2\cosh(2^k\theta)-2)$ with loss $D$ independent of $k$; one upper bound at a
   large dyadic scale bounds all smaller ones; RH ⇔ sub-doubly-exponential dyadic growth.
3. **Gauge fixing by cells.** Lattice dilation is covariant at every gauge; dyadic cell dilation only at the Euler point, pinning
   primes up to $2X+1$ on $[1,X]$; the covariance defect counts charged cells (Liouville: sign changes $\lambda(2a)\ne\lambda(2a+1)$, at least $J$ below $8J^4$).
4. **Terminal geometry.** A reflected pair pulls $\Re\xi'/\xi$ negative exactly inside its critical disc; terminals are zeros outside
   every disc; each carries a zero-free lens with $\Re\xi'/\xi\ge0$; Harnack spreads the outward floor to discs.
5. **Chirality.** Positive deformations form a monoid with trivial units.
6. **Dilution and height.** A positive packet on $\mathbb Q$-independent ordinates buys at most its pole share; on harmonic progressions
   of length $\le M$, $M$ times; every finite lattice cloud has a finite purchase constant between (largest difference set − 1)
   and its minimal weighted height.
7. **Soft vs selective.** Dyadic amplification is soft (holds on every positive depth configuration); cells and the successor are
   selective; square-class criteria are blind.
8. **Exact strength.** The terminal ceiling at depth $a$ and the uniform one-scale Hecke bound with angle $a$ each equal the zero-free
   strip of width $a$; RH = no right terminals.

---

## 3. Objects and language

| Object | Lean |
|---|---|
| Regularized family $Q_r-s_rB\to A$, counterterm $B$, survival cone | `quad`, `survivalCone` |
| Lattice germ $G_r(z)=\sum r^k/(k+z)$; limit $-\psi-\gamma$ | `latticeGerm`, `latticeGermLimit_eq` |
| Torsion germ (identity counterterm) | `torsionGerm_regularized` |
| Periodic germ, Cesàro Gram, module of relations | `periodicGerm`, `mem_survivalCone_cesaroGram_iff` |
| Ramanujan twins; pole node | `ramanujanTwin_survival`, `harmonicKernel_nonneg` |
| Hecke defect, depth moments, Hankel forms | `heckeDefect_dyadic_ge`, `hankelForm_eq_tsum` |
| Integer theta readings | `reading_heckeDefect` |
| Gauge charge of a coupling $(n;a,b)$ | `realSignBlind_iff_isSquare` |
| Cell / lattice dilation; HS holonomy defect | `cellDilate`, `latticeDilate`, `hsDefect_eq` |
| Critical discs, terminals, terminal lens | `isTerminal_iff_outside_discs`, `xi_ne_zero_of_mem_terminalLens` |
| Positive deformations | `PositiveDeformation` |
| Packets, purchase constants | `sum_abs_le_of_packet_nonneg`, `exists_purchase_bound` |

**Distinctions to keep.** Before/after the limit; scheme vs cone (cone is scheme independent); prime vs archimedean place; gauge
blind (square class) vs charged; lattice vs cell; soft vs selective; detection vs ceiling; ray vs disc; deformation vs unit.

---

## 4. Mechanisms

1. **Survival law** with scheme independence and the Finsler–Debreu converse; identity counterterm realizes every form.
2. **Archimedean germ**: Cauchy levels, Tannery, digamma limit; counterterm $\mathbb 1\mathbb 1^\top$.
3. **Torsion germ dichotomy**: survival $\{0\}$, limit negative along $(1,t)$.
4. **Periodic germs**: Dirichlet test + Abel theorem; Cesàro Gram null cone = relations; digamma closed forms of every entry.
5. **Ramanujan orthogonality** $\sum_{k<q}c_m(k)c_n(k)=q\varphi(n)\delta_{mn}$; shifted twins = torsion energy.
6. **Pole-node completion**: $H(x)+H(y)-H(x+y)\ge0$, $H=\psi(1+\cdot)+\gamma$.
7. **Dyadic amplification**: two-scale rigidity doubles the angle; Hankel positivity and log-convex moments.
8. **Gauge charge = square class**; successor couplings never are.
9. **Cells**: Baumslag–Solitar relation $M_mS=S^mM_m$ for both dilations; cell dilation = lattice dilation spread over the successor orbit.
10. **Liouville cell defect** via $2a+1=(2u+1)^2$ at $a=2u(u+1)$; squares vs twice-squares force sign changes.
11. **Critical discs**: pair contribution has the sign of $x(x^2+(y-\gamma)^2-b^2)$; Harnack on the Carathéodory region.
12. **Kronecker dilution** and diagonal quadrature on the torus.

---

## 5. Pillar theorems (the eight laws)

I. **Split polarization and lossless amplification** (`heckeDefect_dyadic_ge`, `riemannHypothesis_iff_dyadic_subexp`,
   `zeroFreeStrip_iff_heckeDefect_bound`).
II. **Local trichotomy**: affine actions are boosts, unipotent or elliptic (APol, ACP).
III. **Gauge blindness = square class** (`realSignBlind_iff_isSquare`, `sourceForm_nonneg_twist_iff`, `successor_coupling_charged`).
IV. **Interior–boundary duality**: cells fix the gauge with reach $2X+1$; defect counts charged cells, fourth-root growth at Liouville
    (`cellDilate_two_covariant_on_horizon_iff`, `hsDefect_liouville_ge`).
V. **Self-energy survival**: cone = module of relations; prime place $\{0\}$; archimedean place polar hyperplane; pole node completes it;
   twins carry $-\varphi(m)\Lambda(t)$ (`survivalCone_eq_of_regularized`, `counterterm_rank_dichotomy`, `ramanujanTwin_carries_primes`,
   `totient_mul_vonMangoldt_eq_digamma_sum`).
VI. **Chirality, quantization, dilution** (`not_positiveDeformation_of_ne`, `sum_le_height_mul_of_packet_nonneg`, `exists_purchase_bound`).
VII. **Surface effectivity vs base non-extension** (AET).
VIII. **Terminal replacement of extrema**: RH ⇔ no right terminal; ceiling at depth $a$ ⇔ strip of width $a$
     (`riemannHypothesis_iff_no_right_terminal`, `zeroFreeStrip_iff_terminal_ceiling`, `exists_terminal_floor_spreads`).

Conjunction: `renormalized_biarithmetic_geometry_laws`.

---

## 6. Traps

| Trap | Truth |
|---|---|
| Positivity of $T_r$ for $r<1$ bounds Weil's prime form | Identity counterterm: every form is such a limit |
| A better scheme keeps torsion positivity | Survival cone is scheme independent, $\{0\}$ |
| Any continuum twin cancels the torsion divergence | Only shared modes create relations |
| The archimedean place is positive | Only on the polar hyperplane |
| A cleverer multiplicative weight separates $\zeta$ from Liouville | Square-class criteria accept $\Lambda$ iff $\lambda\Lambda$ |
| Discretizing to $\log n$ loses nothing | Lattice dilation is blind; only cells fix the gauge |
| Dyadic amplification is selective | It is soft; its content is transfer of a source bound |
| A weaker input than a strip bounds the one-scale defect uniformly | The uniform bound *is* the strip |
| Collective packets amortize pole cost | Bounded by (weighted height) × pole share |
| The terminal ray is one-dimensional information | Harnack spreads it to discs |

---

## 7. Open problems

1. **Matched torsion–continuum renormalization**: choose twin coefficients on per-order relations so the explicit twin inequality
   bounds short-cycle differences $W(g-T_{2^m}g)$ of the prime form.
2. **Terminal ceiling at some depth $a<\tfrac12$** (= a zero-free strip, nothing weaker).
3. **Arithmetic bound for prefix readings at one scale** $L\asymp\log n$ (again a strip).
4. **Linear cell holonomy**: positive lower density of $\lambda(2a)\ne\lambda(2a+1)$ (log-density form = two-point log-averaged Chowla).
5. **Exact purchase constant of a general cloud** (a Delsarte-type LP between the two bounds) and its use against clustered
   companion clouds of $\operatorname{ord}_{1/2}L(s,\mathrm{sym}^2u)$.

## 8. Tools to build

Explicit twin coefficients on per-order relations; a one-scale arithmetic prefix bound; density results for Liouville sign
changes along $(+1,\times2)$; LP purchase bounds.

## 9. Contribution standard

State regulator, counterterm and survival cone; state gauge charge and whether a criterion is soft or selective (test on the
Liouville twin and the Euler point); for geometric statements, ray vs disc, detection vs ceiling; record the exact strength
(which zero-free strip) of every target.
