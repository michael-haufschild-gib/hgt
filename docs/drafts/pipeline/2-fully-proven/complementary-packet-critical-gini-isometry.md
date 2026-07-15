# The complementary packet is a cofinal Gini isometry despite local zeta-two expansion

- **ID:** `complementary-packet-critical-gini-isometry`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE-FRAMED FOUR-UNIT ENERGY
- **Scientific status:** `[PROVED HERE] [LITERATURE NOVELTY OPEN] [NOT AN RH PROOF]`
- **Parents:**
  - `complementary-packet-euler-connection-weld.md`
  - `mobius-incidence-clock-gini-fisher-four-unit-law.md`
  - `gamma-sonin-asymptotic-passivity-incidence-curvature.md`
- **Statement:** The boundary complementary packet is not pointwise contractive in its divisor
  clock: at infinitesimal separation its squared metric coefficient is `zeta(2)>1`.  Nevertheless
  its squared distance at separation `a` is `a/(1+omega)^2+O(1)`, uniformly near the critical
  boundary.  Since the squarefree critical clock lives at separation `1/(sigma-1)`, the packet
  covariance has exactly four units of critical relative energy.  Entrywise Gamma completion and
  Sonin projection preserve this upper budget asymptotically.

## Boundary affine packet

Fix `0<omega<=omega_0` and put

```text
c_omega=1/(1+omega),
k_omega(t)=e^(-(1+omega)t)R_omega(e^t).                  (1)
```

At `delta=0`, the complementary packet is the affine path

```text
B_h(t)
 =1_(t>=h)k_omega(t-h)-c_omega 1_(t<h).                 (2)
```

Individual `B_h` are not in `L2(R_+)` because of the constant incoming branch.  Every difference
`B_h-B_k` is in `L2`, so `(2)` defines a genuine path in the affine Hilbert quotient by the common
constant mode.  This is the source-rigged boundary selected by the regularized packets as
`delta->0+`.

For `a>=0`, translation invariance of the affine difference gives

```text
D_omega(a)=||B_(h+a)-B_h||_2^2

 =integral_0^a|k_omega(r)+c_omega|^2dr
  +integral_0^infinity
     |k_omega(r+a)-k_omega(r)|^2dr.                      (3)
```

The right side is independent of `h`.

## Cofinal metric theorem `[PROVED HERE]`

There is a constant `C_(omega_0)` such that for every `0<omega<=omega_0` and every `a>=0`,

```text
|D_omega(a)-c_omega^2 a|<=C_(omega_0).                  (4)
```

### Proof

The elementary power-sum remainder estimate, uniformly for `0<omega<=omega_0`, gives

```text
|k_omega(t)|<=C(e^(-t)+e^(-(1+omega)t)).                 (5)
```

Hence the `L1` and `L2` norms of `k_omega` are uniformly bounded.  Subtracting `c_omega^2a` from
the first term of `(3)` leaves

```text
2c_omega integral_0^a k_omega(r)dr
 +integral_0^a|k_omega(r)|^2dr,                          (6)
```

whose absolute value is uniformly bounded by the `L1` and `L2` norms.  The second term of `(3)` is
at most `4||k_omega||_2^2`.  These bounds prove `(4)`. `QED`

In particular,

```text
D_omega(a)/a->c_omega^2                                 (7)
```

as `a->infinity`, uniformly near `omega=0`.

## Local expansion theorem `[PROVED HERE]`

At the opposite scale,

```text
lim_(a->0+)D_omega(a)/a=zeta(2).                         (8)
```

### Proof

The stitched profile in `(2)` has a unit jump at `0`.  At `log m`, `m>=2`, its jump is `m^(-1)`;
these values are independent of `omega`.  The locally absolutely continuous part has square-
integrable derivative between jumps and contributes `o(a)` to the translation modulus.  Each
jump of size `j` contributes `j^2a+o(a)`.  Since

```text
sum_(m>=1)m^(-2)=zeta(2),                                (9)
```

summation of the square-summable jump contributions proves `(8)`. `QED`

Thus no finite-clock pointwise inequality `D_omega(a)<=a` is available.  The successful metric
law is cofinal `(4)`, not local `(8)`.

## Exact critical four-unit packet energy `[PROVED HERE]`

Let

```text
P_sigma(d)=mu(d)^2d^(-sigma)/Z(sigma),
sigma=1+2omega,
H_sigma=log d under P_sigma,                             (10)
```

and let `H_sigma'` be an independent copy.  Define the source-framed packet curvature kernel

```text
K^B_sigma(d,e)
 =2psi_sigma(d)psi_sigma(e)
   (B_(log e)-B_(log d)).                                (11)
```

Its critical relative energy is

```text
E^B_sigma
 =epsilon sum_(d,e)||K^B_sigma(d,e)||_2^2
 =4epsilon E[D_omega(|H_sigma-H_sigma'|)].               (12)
```

By `(4)`,

```text
E^B_sigma
 =4c_omega^2 epsilon E|H_sigma-H_sigma'|+O(epsilon).     (13)
```

The critical exponential clock theorem gives

```text
epsilon E|H_sigma-H_sigma'|->1,                          (14)
```

and `c_omega->1`.  Therefore

```text
lim_(sigma->1+)E^B_sigma=4.                              (15)
```

Unlike the bare threshold curvature, `(11)` contains the full floor/power-sum packet path whose
connection was proved to synthesize the shifted-Euler source.  The four-unit calibration survives
that source framing without a fitted normalization.

## Gamma/Sonin completion

Apply the critical-line Gamma multiplier `mathcalG_omega` and the exact Sonin projection `Q_tau`
entrywise:

```text
K^(B,Gamma,Sonin)_(sigma,tau)(d,e)
 =Q_tau mathcalG_omega(K^B_sigma(d,e)).                  (16)
```

The Gamma multiplier norm tends to one and `Q_tau` is contractive.  Equations `(15)`--`(16)` give

```text
limsup_(sigma->1+)
 epsilon sum_(d,e)
 ||K^(B,Gamma,Sonin)_(sigma,tau)(d,e)||_2^2<=4.          (17)
```

This proves the source-framed Gamma/Sonin energy gate.  The remaining theorem is not a norm
estimate for `(16)`; it is the direct anti-causal identification and graph convergence of its
canonical relative readout to `ell_E`.

## No-go and positive HT statement

**No-go:** the raw packet is locally expansive by the exact coefficient `zeta(2)`.  Any proof
claiming a pointwise one-Lipschitz packet path is false.

**Positive statement:** the same path is an asymptotic affine isometry with slope
`1/(1+omega)^2`; the bounded local defect disappears against the escaping critical arithmetic
clock.  Critical passivity is therefore a cofinal probabilistic property, not a finite-clock
operator norm.

**General HT insight:** a constrained HT source can be locally expansive at every finite
resolution yet asymptotically passive on its distinguished escaping state.  Uniform operator
contractivity and source-specific critical passivity are inequivalent notions.

## Literature gate

Translation moduli, jump-square asymptotics, Gini mean differences, and power-sum remainder bounds
are established mechanisms.  Targeted searches have not located `(4)`, `(8)`, or the critical
packet energy `(15)` in this shifted-Euler/Suzuki setting.  Project inputs remain admissible;
external specialist audit is required before a novelty claim.

## Gates

- [x] boundary affine packet quotient defined
- [x] exact two-point metric formula proved
- [x] uniform cofinal affine metric proved
- [x] local `zeta(2)` expansion proved
- [x] pointwise contraction falsified positively
- [x] source-framed packet curvature kernel written
- [x] exact critical four-unit packet energy proved
- [x] Gamma/Sonin completion inserted asymptotically passively
- [ ] construct the canonical anti-causal relative readout
- [ ] prove direct pole-to-divisor identity
- [ ] prove graph convergence to `ell_E`
- [ ] independent specialist literature audit
- [ ] RH
