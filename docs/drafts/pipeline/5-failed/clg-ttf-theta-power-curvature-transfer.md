# CLG/TTF: positive mass curvature does not transfer to the cusp current

**Status:** generic transfer disproved on paper. Positive survivor proved in Lean, including
positivity of the literal differentiated power sources on the full real line and exact
recovery of the original source at `v=1`. The `v=1` all-polynomial source sign remains open.
The frontier map is read-only.

## Claim tested

Let `H(x)=exp(x/2) theta(exp(2x))`, `g=log H`, `K=g''`, and
`S=1/4-g'^2`. Positive definiteness of `K`, evenness and positivity of `H`, positive
source `(H''-H/4)/2`, and double-exponential source decay do not by themselves imply
the all-aperture Fourier-current sign. The following counterexample retains these
properties and the same critical strip after rescaling.

## Positive survivor: a global energy floor

Use the actual modular functions `u=6g'`, `A`, and `w` from
`ThetaCuspModularEnergyBounds`. Existing unconditional source identities give

```
0 <= u(x) < 3                            (x >= 0),
Q = Phi/H = u^2/24 + A/16 - 3/8 > 0,
u' = -3 + u^2/3 + 3A/4 = (9-u^2)/6 + 12Q,
A' = -2Aw,                 A > 0,       w >= u,
E = A + 4u^2/3,
E' = -2A(w-u) - (8u/9)(9-u^2).
```

Thus `E` is strictly decreasing on `[0,infinity)`: its derivative is negative at
every positive point, since `u>0` there. We prove `E>=12` without assuming a terminal
asymptotic. If `E(x0)=e<12`, monotonicity and `A>0` force `u(t)^2<3e/4` for all
`t>=x0`. Hence `u'(t)>(9-3e/4)/6>0` uniformly on that ray, contradicting `u(t)<3`
by the mean value theorem. Strict decrease now gives `E(x)>E(x+1)>=12`.

**Unconditional survivor:** `12 < A(x)+4u(x)^2/3 < 96/5` for every `x>=0`, and

```
K - 4S = (E-12)/8 > 0.
```

Consequently `K-vS>0` for every real `v<=4`; positive sources use `0<v<=4`.
This uses the actual complete modular
orbit and the literal positive theta source; no numerical orbit or initial-value
approximation enters. This is stronger than merely observing the failure of the
transfer. It supplies a whole interval of positive source factors. Optimality of
the parameter endpoint `4` is not asserted.

## A positive theta-power source with off-line zeros

Define the mass and its source with fixed asymptotic slopes `+/-1/2` by

```
H_v(x) = H(x/v)^v,
Psi_v(x) = (H_v''(x)-H_v(x)/4)/2
         = H(x/v)^v/(2v) * [K(x/v)-vS(x/v)].
```

For `0<v<=4`, the preceding bound and evenness prove `Psi_v>0` on the full real
line. It is even and smooth. The expansion
`H(y)=exp(y/2)(1+2 exp(-pi exp(2y))+...)` on the positive ray, with termwise
derivative bounds and reflection, proves double-exponential decay of `Psi_v` and
every derivative after any fixed exponential tilt. The leading pure exponential
in `H_v` cancels exactly in the definition of `Psi_v`.

The completed mass curvature is `K_v(x)=K(x/v)/v`. Its Fourier transform is
`Khat(vb)>=0`, using the unconditional spectral formula recorded in
[the source-energy card](../1-in-progress/clg-ttf-all-polynomial-source-energy.md).
The inverse normalized masses are also infinitely divisible, since
`(H_v(0)/H_v(x))^t=(H(0)/H(x/v))^(vt)`.

For the counterexample set `v=4`. Jacobi's four-square Dirichlet series is

```
sum_(n>=1) r_4(n) n^(-s/2)
  = 8 (1-4^(1-s/2)) zeta(s/2) zeta(s/2-1).
```

This factorization is also given in Lagarias–Rains, section 3.4,
[arXiv:math/0104176](https://arxiv.org/pdf/math/0104176), with their normalized
Dirichlet series equal to the displayed series divided by `8`.
For the unscaled mass `H(y)^4`, regularized Mellin transformation and two
integrations by parts give its cusp-source transform as

```
F_4_unscaled(z) = 2 s(s-4) pi^(-s/2) Gamma(s/2)
                     (1-4^(1-s/2)) zeta(s/2) zeta(s/2-1),
s = 2 + iz.
```

The normalization follows from `dy=dt/(2t)` and the source factor `1/2`;
the differential operator contributes `s(s-4)`. This identity is understood by
analytic continuation of the regularized Mellin transform, not by integrating
the growing mass on the Fourier axis. The rescaled source has transform
`F_4(z)=F_4_unscaled(4z)/4`.

The corpus already proves existence of a zeta zero `rho` with `0<Re rho<1`
(`RiemannXiZerosInfinite.exists_riemannZeta_zero_mem_openStrip`). Such a zero is
nonreal by `ZetaRealStrip.riemannZeta_real_strip_ne_zero`. At `s=2rho`, the other
displayed factors are holomorphic and finite: the gamma argument has positive
real part, neither zeta pole is met, and neither polynomial endpoint is met.
Therefore the source transform vanishes at

```
z = Im(rho)/2 + i (1-Re(rho))/2,
0 < Im(z) < 1/2.
```

This is an off-line zero inside the same normalized critical strip. Reality of
the source gives a conjugate zero on the lower half-strip. If the current
`d/da |F_4(b-ia)|^2` were nonnegative throughout `0<a<1/2`, a zero at aperture
`a0` would force this squared modulus to vanish for every `0<a<a0`. The identity
theorem would then force `F_4` to vanish identically, contradicting its positive
value at zero. Thus the all-aperture current sign fails. This is not a
counterexample to RH for the original source `Psi_1=Phi`.

## No-go closure

- **Exact failure:** positivity and infinite divisibility of inverse mass, positive
  mass log curvature, and a positive rapidly decaying cusp source survive the
  theta-power deformation through `v=4`; real-zero confinement does not.
- **Positive survivor:** the actual global energy floor `E>12`, strict energy
  decrease, and the positive normalized source factors for every `0<v<=4`.
- **New constraint on the attempt:** a successful transfer must use a feature
  distinguishing the `v=1` source from the normalized `v=4` source. The established
  positive curvature spectrum alone cannot provide that distinction.
- **Paper dependencies:** corpus modular ODE, source positivity and global drift
  barrier; Lagarias–Rains positive curvature formula and four-square factorization;
  corpus existence and nonreality of a nontrivial zeta zero. No RH assumption.
- **Lean status:** `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspModularEnergyFloor.lean`
  proves `strictAntiOn_thetaCuspModularStrongEnergy`,
  `thetaCuspModularStrongEnergy_gt_twelve`, `thetaCuspModularPowerSourceBracket_pos`,
  `thetaCuspNormalizedPowerSource_eq`, `thetaCuspNormalizedPowerSource_neg`,
  `thetaCuspNormalizedPowerSource_pos`, and `thetaCuspNormalizedPowerSource_one`.
  The last two concern the actual differentiated normalized mass, not an assumed
  source incidence. The full theta-power Mellin incidence and the negative
  transfer statement are paper-only.
- **Validation:** scratch `lake env lean` and final
  `lake --old build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspModularEnergyFloor` passed.
  The leaf compiled in 14 seconds; three required existing modules were refreshed
  sequentially. No umbrella build or numerical computation. All seven new theorem
  axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
  Formal lint passed; module is wired into `RHTower`, and indexes are refreshed.
