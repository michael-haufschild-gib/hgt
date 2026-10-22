# Cofinal CCM endpoint analysis must resum the full radial-prolate jet tower

- **ID:** `ccm-prolate-endpoint-jet-resummation-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE] [NECESSITY THEOREM]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** the prolate Sturm--Liouville endpoint equation and fixed-mode large-bandwidth
  asymptotics
- **Statement:** For every fixed prolate mode, the endpoint logarithmic derivative is asymptotic
  to `-2*pi^2*lambda^3`. At Fourier frequency `y=lambda`, the nominal second endpoint term is
  therefore larger than the first sawtooth term by `pi*lambda^2`. The cofinal CCM tail must be
  treated by a resummed radial-prolate transform, not by any fixed endpoint-jet truncation.

## Prolate endpoint identity

On `[-1,1]`, let `psi_(m,c)` be the fixed-mode normalized prolate eigenfunction satisfying

```text
(1-x^2)psi''-2x psi'+(kappa_m(c)-c^2 x^2)psi=0.                    (1)
```

Regularity at `x=1` gives the exact endpoint relation

```text
2 psi_(m,c)'(1)=(kappa_m(c)-c^2)psi_(m,c)(1).                     (2)
```

In the CCM scaling

```text
c=2*pi*lambda^2,
e_(m,lambda)(x)=lambda^(-1/2)psi_(m,c)(x/lambda),                 (3)
```

equation `(2)` becomes

```text
e_(m,lambda)'(lambda)/e_(m,lambda)(lambda)
 =(kappa_m(c)-c^2)/(2lambda).                                    (4)
```

The endpoint never vanishes for a regular fixed prolate branch, so the quotient is defined.

### Proof

Take `x->1` in `(1)`. The coefficient of `psi''` vanishes, while the regular solution and its first
derivative have finite limits. This gives `(2)`. Equation `(4)` follows by differentiating `(3)`.

## Cofinal logarithmic derivative

The classical fixed-mode prolate expansion gives

```text
kappa_m(c)=(2m+1)c+O_m(1),   c->infinity.                         (5)
```

Only the weaker fact `kappa_m(c)=O_m(c)` is needed below. Equations `(4)`--`(5)` and
`c=2*pi*lambda^2` imply

```text
e_(m,lambda)'(lambda)/e_(m,lambda)(lambda)
 =-2*pi^2*lambda^3+O_m(lambda).                                  (6)
```

## Constrained CCM source

Let

```text
g_lambda=(ell_1 e_(0,lambda)-ell_0 e_(4,lambda))
          /sqrt(ell_0^2+ell_1^2).                                (7)
```

The fixed-mode deficit and endpoint-response laws give

```text
e_(0,lambda)(lambda)/e_(4,lambda)(lambda)=O(lambda^(-4)),
ell_0,ell_1 -> nonzero constants.                                (8)
```

Using `(4)` separately on the two terms in `(7)`, the `m=4` contribution dominates both the value
and derivative at the endpoint. Therefore

```text
g_lambda'(lambda)/g_lambda(lambda)
 =-2*pi^2*lambda^3+O(lambda).                                    (9)
```

## Failure of fixed endpoint order in the critical scaling

For an even `C2` source supported on `[-lambda,lambda]`, two integrations by parts give

```text
hat(f)(y)
 =f(lambda)sin(2*pi*lambda*y)/(pi*y)
  +f'(lambda)cos(2*pi*lambda*y)/(2*pi^2*y^2)
  +R_2(y).                                                       (10)
```

At the first exterior frequency `y=lambda`, the ratio of the coefficient magnitudes of the second
displayed term to the first is

```text
|f'(lambda)/f(lambda)|/(2*pi*lambda).                             (11)
```

For `f=g_lambda`, equation `(9)` gives

```text
|g_lambda'(lambda)/g_lambda(lambda)|/(2*pi*lambda)
 =pi*lambda^2+O(1).                                              (12)
```

Thus the nominal `1/y^2` term is polynomially larger than the nominal `1/y` term in the cofinal
critical scaling. In particular, `(10)` is an asymptotic expansion for fixed `lambda` and
`y->infinity`, but not a cofinal asymptotic expansion at `y=n*lambda` with fixed `n` and
`lambda->infinity`.

The same endpoint equation recursively makes higher jets grow with further powers of the large
prolate parameter. No truncation at a fixed jet order can be promoted to a cofinal dominance
theorem merely by adding more integrations by parts.

## Positive radial-prolate requirement

The correct exterior object is the exact radial prolate function

```text
z |-> hat(e_(m,lambda))(lambda*z),   z>=1,                         (13)
```

with a matched analysis of its endpoint and mass-carrying scales. The exact endpoint-amplitude law

```text
|e_(m,lambda)(lambda)|^2 asymptotic to 2*pi*lambda*d_m(lambda):   (14)
```

combined with `(6)` forces a thin pointwise endpoint scale `y-lambda` of order `lambda^(-3)`, while
the exact leakage identity forces an effective squared-mass scale of order `lambda^(-1)`. These are
different. `ccm-radial-prolate-two-scale-boundary-carrier.md` proves the corresponding normalized
inner derivative and outer `L2` mass laws.

Accordingly, the positive source theorem needed by CCM is

```text
matched two-scale radial-prolate boundary profile with a uniform remainder
  -> arithmetic dilation correlations in the zeta/Weil graph topology
  -> bilinear Rayleigh excess and parity transfer.                (15)
```

The first formal endpoint component remains useful as a calibration: its prime response and
archimedean logarithmic mass have exact constants in
`ccm-constrained-endpoint-euler-response-constant.md` and
`ccm-leading-endpoint-archimedean-log-law.md`. Equations `(12)`--`(15)` prove that those constants
are not yet constants for the full exact tail.

## Literature and novelty verdict

The endpoint identity is immediate from the classical prolate ODE, and `(5)` is standard
fixed-mode spheroidal asymptotics. The comparison with the integration-by-parts hierarchy is a
useful route correction but fails the parent-theory gate. It is classified as a bridge.

## References

- D. Slepian, *Some Asymptotic Expansions for Prolate Spheroidal Wave Functions*, J. Math. Phys. 44
  (1965), 99--140.
- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Lean decision

The formal tree has no prolate Sturm--Liouville operator or fixed-mode asymptotic. Formalizing the
endpoint substitution alone would be a wrapper. No Lean file is added.

## Gates

- [x] exact prolate endpoint derivative identity proved
- [x] cofinal derivative scale proved
- [x] fixed-jet critical-scaling failure quantified
- [x] radial boundary coordinate isolated
- [ ] exact fixed-mode radial-prolate boundary profile in CCM normalization
- [ ] arithmetic correlations of the resummed profile
- [ ] true Weil Rayleigh-excess and parity transfer

## Lean status

`[FORMALIZED]` — supersedes the "No Lean file is added" decision recorded above.  The prolate
Sturm–Liouville theory and the fixed-mode asymptotic `(5)` remain cited parents, but the card's own
computations `(2)`, `(4)`, `(6)`, `(11)`–`(12)` are reachable and are now proved.

Module: `formal/GaloisForLFunctions/RHTower/CCM/CCMProlateEndpointJet.lean`
(5 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired into
`formal/GaloisForLFunctions/RHTower.lean`).

What is proved in Lean:

- `prolate_endpoint_identity` — **equation (2)**: evaluating the prolate equation at `x = 1` kills
  the `(1-x²)` coefficient and leaves the exact first-order endpoint relation
  `2ψ'(1) = (κ − c²)ψ(1)`.
- `hasDerivAt_scaledMode` — the derivative of the CCM-scaled mode `x ↦ N ψ(x/λ)` at the endpoint
  `x = λ` is `N ψ'(1)/λ`.
- `scaled_logDeriv_eq` — **equation (4)**: hence the endpoint logarithmic derivative of the scaled
  mode is exactly `(κ − c²)/(2λ)`, independently of the normalization `N`.
- `critical_scale_logDeriv` — **equation (6)**: in the CCM scaling `c = 2πλ²` this equals exactly
  `−2π²λ³ + κ/(2λ)`.
- `jet_ratio_ge` — **equations (11)–(12)**: with an eigenvalue remainder of size `O(λ)` the ratio of
  the second endpoint term to the first at `y = λ` is at least `πλ² − C/(2π)`, so it grows
  polynomially.  This is the quantitative failure of any fixed endpoint-jet truncation to be
  cofinal.

Deliberately outside the Lean statement (cited parents, not results of this card):

- the prolate Sturm–Liouville operator and the regularity of the fixed-mode branch;
- the fixed-mode eigenvalue asymptotic `(5)` and the deficit/endpoint-response laws `(8)`, `(14)`;
- the integration-by-parts expansion `(10)`;
- the two-scale radial-prolate boundary laws of the companion cards.
