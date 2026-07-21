# Suzuki residual-overcrowding and entire-pair closure

- **ID:** `suzuki-residual-overcrowding-entire-pair-closure`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Lane:** Suzuki cofinal Clark divisor; exact residual elimination
- **Parents:** `suzuki-compactified-inverse-phase-lattice-holography`,
  `suzuki-finite-aperture-hermite-biehler-normal-family`
- **Source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  [arXiv:2606.09096](https://arxiv.org/abs/2606.09096), together with the project's
  Livsic--Donoghue and global-phase consequences
- **RH used:** no
- **Computation used:** no

## Frontier problem

The compactified inverse-phase theorem decomposes every cofinal spectral limit as

```text
sigma=sigma_lab+sigma_res.                               (1)
```

It left `sigma_res` as a positive measure.  The point of this theorem is to identify its exact
analytic producer.  Interior residual is equivalent to spectral mass carried by unbounded phase
labels inside a bounded physical window.  That is local Clark-divisor overcrowding, not physical
escape.  Local entire-pair normality forbids it.  The only remaining residual can then lie at the
two projective endpoints, where it is exactly the linear Nevanlinna coefficient.

## Setup

Use the notation of the parent theorem:

```text
y_k=(2k-1)pi,
u_(n,k)=U_n(y_k),
p_(n,k)=2U_n'(y_k),
sigma_n=sum_k p_(n,k) delta_(u_(n,k)).                   (2)
```

After extraction,

```text
u_(n,k)->u_k,
p_(n,k)->p_k,
sigma_n=>sigma,
sigma_lab=sum_k p_k delta_(u_k),
sigma_res=sigma-sigma_lab>=0.                            (3)
```

Every `U_n` is odd and strictly increasing.  In particular `u_(n,k)` is strictly increasing in
`k` and reflection pairs `k` with `1-k`.

## Theorem A: the residual is exactly the escaped-label tail `[PROVED HERE]`

For every nonnegative continuous function `f` on `[-pi/2,pi/2]`,

```text
int f d sigma_res
 =lim_(K->infinity) lim_(n->infinity)
    sum_(|k|>K) p_(n,k) f(u_(n,k)).                      (4)
```

The inner limit exists for every fixed `K`.  Thus `sigma_res` is not an abstract defect added by
weak compactness: it is precisely probability whose phase label tends to infinity.

### Proof

For fixed `K`, weak convergence and finite-coordinate convergence give

```text
lim_n sum_(|k|>K) p_(n,k)f(u_(n,k))
 =int f d sigma-sum_(|k|<=K)p_k f(u_k).                  (5)
```

The finite heads on the right increase to `int f d sigma_lab`.  Monotone convergence turns `(5)`
into `(4)`.

## Theorem B: interior residual is local divisor overcrowding `[PROVED HERE]`

For `0<r<pi/2`, let

```text
N_n(r)=#{k in Z: |u_(n,k)|<=r}.                          (6)
```

If

```text
sup_n N_n(r)<infinity            for every r<pi/2,       (7)
```

then

```text
sigma_res restricted to (-pi/2,pi/2) = 0.               (8)
```

Contrapositively, every positive interior residual forces unbounded Clark zero count in one fixed
physical compact interval.

### Proof

Fix a compact interval `J` in the projective interior and enlarge it to the compact interval
joining `J` to zero.  Strict order and oddness imply that if a label `|k|` tending to infinity has
`u_(n,k)` in `J`, then all intervening central labels also lie in the enlarged interval.  Its count
therefore tends to infinity, contradicting `(7)`.  Consequently every compact interior interval
contains only a fixed finite label head.  Formula `(4)` then vanishes for every nonnegative
continuous `f` supported in that interval.  Exhausting the interior proves `(8)`.

This separates the two defects sharply:

```text
interior residual  <=> escaped labels remain physically bounded (overcrowding),
endpoint residual  <=> physical mass escapes to projective infinity. (9)
```

## Theorem C: entire-pair normality kills interior residual `[PROVED HERE]`

Let `W_(n,-1)` be the even-extension Suzuki characteristic function, whose simple real zeros are
the physical points

```text
x_(n,k)=tan u_(n,k).                                    (10)
```

Suppose that there are zero-free entire gauges `g_n` such that

```text
g_n W_(n,-1) -> W_(-1)                                  (11)
```

locally uniformly on `C`, where `W_(-1)` is not identically zero.  Then `(7)` holds and hence
`sigma_res` has no interior mass.

More generally, it is enough to have such convergence on a complex neighborhood of each real
compact interval.  A common-gauge locally uniform limit of the two parity functions

```text
(g_n W_(n,1),g_n W_(n,-1))->(W_1,W_(-1))                (12)
```

therefore closes the entire interior residual problem and also gives the meromorphic carrier

```text
m_n=-i W_(n,1)/W_(n,-1) -> -i W_1/W_(-1)                (13)
```

away from the limiting poles.

### Proof

Choose a rectangle around a real compact interval whose boundary avoids the discrete zero set of
`W_(-1)`.  Uniform convergence and Rouche's theorem make the number of zeros of
`g_n W_(n,-1)` in that rectangle eventually equal to the finite number for `W_(-1)`.  The gauges
are zero-free, so these are exactly the Suzuki Clark points.  This proves `(7)`.  Equation `(13)`
is ordinary quotient convergence away from zeros of the limiting denominator.

No claim of ordinary entire convergence to Suzuki's meromorphic Corollary 1.6 target is made.
Condition `(12)` is pair convergence before taking the ratio, so zeros and poles are retained
without the malformed entire-to-meromorphic limit.

## Theorem D: endpoint residual is exactly linear Nevanlinna mass `[PROVED HERE]`

Let

```text
K_z(t)=(tz+1)/(t-z)=z+(z^2+1)/(t-z)                     (14)
```

be the Donoghue probability kernel.  It has the same two projective endpoint values:

```text
lim_(t->+infinity) K_z(t)=z,
lim_(t->-infinity) K_z(t)=z.                             (15)
```

Put

```text
alpha=sigma({-pi/2,pi/2}).                              (16)
```

Weak convergence of the compactified probabilities gives locally uniformly on the upper half
plane

```text
m_n(z)=int K_z(t)dnu_n(t)
 ->m(z)=alpha z+int_R K_z(t)dnu_int(t),                  (17)
```

where `nu_int` is the pullback of the interior part of `sigma`.  Thus `alpha` is exactly the
linear coefficient in the Nevanlinna representation of `m`.  Suzuki symmetry makes `sigma` even,
so the endpoint masses are `alpha/2` each.

The kernel in `(14)`, extended by `(15)`, is continuous on the compact projective interval for
each upper-half-plane `z`; it is uniformly bounded when `z` ranges over a compact subset of that
half-plane.  Weak convergence proves `(17)` and local boundedness upgrades it to locally uniform
convergence.

Combining Theorems B--D gives the exact closure theorem:

```text
common-gauge entire-pair normality
  + zero linear coefficient of the limiting Herglotz function
  => sigma_res=0 and sum_k p_k=1.                        (18)
```

The first hypothesis prevents label condensation on every bounded physical window.  The second
prevents physical escape.  They address disjoint mechanisms and neither can replace the other.

## Complete fixed-lattice rigidity `[PROVED HERE]`

For two finite-aperture Suzuki carriers, equality of

```text
U_1(y_k)=U_2(y_k),
U_1'(y_k)=U_2'(y_k)             for every k in Z         (19)
```

implies equality of the entire carriers, not only their even spectra.  Indeed `(19)` and the
parent holography theorem give identical Donoghue probabilities.  The Donoghue integral gives
`m_1=m_2`; Cayley inversion gives `Theta_1=Theta_2`; normalized phase lifting then gives
`phi_1=phi_2` and `U_1=U_2`.  Consequently the fixed-lattice first jet is a complete invariant of
all self-adjoint-extension divisors.

## What this changes at the RH frontier

Generic compactness, residue bookkeeping, and the meaning of residual mass are now closed.  A
source proof no longer needs to control moving atoms individually.  It must prove exactly:

```text
1. common-gauge entire normality of Suzuki's parity pair,
2. zero linear coefficient of its cofinal Donoghue limit,
3. identification of the limiting meromorphic ratio with the Xi/de Branges carrier. (20)
```

Items 1--2 force the fixed-label probability to survive with total mass one.  Item 3 is then a
single meromorphic-function identity; by complete fixed-lattice rigidity it identifies every
extension divisor at once.

This theorem does not prove `(20)`, does not select the cofinal shift, and does not prove RH.  It
removes the last ambiguity about which topology and which loss mechanisms a source theorem must
control.

## Hostile audit

1. **No false derivative convergence.** Formula `(4)` uses separately extracted masses `p_k`.
2. **No count/mass confusion.** Bounded local zero count is a sufficient structural condition;
   it is not claimed necessary when extra labels have vanishing total mass.
3. **No malformed target convergence.** Entire convergence is imposed on a common-gauge pair;
   its quotient may have poles.
4. **No hidden tightness.** Pair normality kills only interior residual.  Endpoint mass is retained
   explicitly as `alpha z`.
5. **No hidden RH.** All finite carriers are Suzuki's unconditional shifted positive models.
6. **Sharpness.** Free clocks violate local count boundedness and create uniform interior residual;
   the Cayley ground edge has bounded interior count but creates endpoint linear mass.

## Literature and priority audit

Rouche/Hurwitz zero-count stability, Nevanlinna linear mass, and Clark measures are classical and
not claimed as new.  Suzuki does not compactify the inverse phase, define the fixed-label residual,
identify it with escaped-label overcrowding, or state the two-condition closure `(18)`.  Targeted
search of Suzuki's paper, the cited meromorphic-inner literature, and this repository found no
source-specific theorem of this form.  Candidate novelty is the exact synthesis `(4)`--`(20)`;
specialist priority review remains required.

## Lean target

The project already formalizes locally uniform zero transfer and the Donoghue kernel identity.
Add only the new dependency-closed projective endpoint connector:

```text
tendsto_suzukiDonoghueKernel_atTop
tendsto_suzukiDonoghueKernel_atBot
```

Measure-valued weak convergence, Rouche zero counts for the concrete aperture family, and the
common-gauge source pair remain paper-level until that family is represented in Lean.

## Gates

- [x] exact escaped-label tail formula proved
- [x] interior residual/overcrowding alternative proved
- [x] entire-pair normality closure proved
- [x] endpoint residual/linear-mass identity proved
- [x] complete fixed-lattice carrier rigidity proved
- [x] hostile audit closed
- [x] Lean endpoint connector
- [ ] source common-gauge pair normality
- [ ] source zero-linear-mass theorem
- [ ] Xi/de Branges ratio identification
- [ ] RH

## Log

- 2026-07-21 — derived immediately after compactified inverse-phase holography exposed the residual
  as the only cofinal defect; complete paper proof and hostile audit closed.
- 2026-07-21 — both projective Donoghue-kernel endpoint limits formalized unconditionally in
  `SuzukiCompactifiedPhaseProfile.lean`; exact build and axiom audit passed.
