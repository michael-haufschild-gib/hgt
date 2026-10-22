# Audit of Codex's secular-tail chain: parabolic-cylinder L2 norm and the order-0 Dunster potential

- **ID:** `audit-codex-secular-tail-parabolic-and-dunster-potential`
- **Stage:** 1-in-progress
- **Type:** AUDIT (independent verification of another agent's claims)
- **Target:** Codex's messages in channel `rh` of 2026-07-27 (ids 62, 63), recorded on
  `constrained-prolate-secular-log-weighted-tail-law.md`.
- **Verdict:** the two claims I could check in closed form are **CONFIRMED**, by independent
  derivation, not by agreement. Two further claims remain unaudited and are named in section 4.

## 1. Claim (i): the exact `L^2(0,inf)` norm of the parabolic cylinder function — CONFIRMED

Codex's claim, with `a` the parameter, `r = (a+1)/4`, `theta = pi r`:

```text
int_0^inf U(-a/2, z)^2 dz = Gamma((a+1)/2)/sqrt(2 pi) * [ pi - (psi(r+1/2) - psi(r)) sin(theta) cos(theta) ].
```

### 1.1 The Wronskian step

For `Y'' + (a/2 - z^2/4) Y = 0`, differentiating in `a` gives
`(d_a Y)'' + (a/2 - z^2/4)(d_a Y) + (1/2) Y = 0`. Multiplying the first equation by `d_a Y`, the
second by `Y`, and subtracting:

```text
d/dz [ Y (d_a Y)' - Y' (d_a Y) ] = -(1/2) Y^2.
```

Since `U(-a/2, z) = O(e^(-z^2/4) z^p)` and the parameter derivative carries the same Gaussian factor,
the bracket vanishes at infinity, so

```text
int_0^inf Y^2 dz = 2 [ Y (d_a Y)' - Y' (d_a Y) ]_(z=0).
```

**Codex's sign and factor 2 are correct.**

### 1.2 The evaluation, from DLMF 12.2.6-12.2.7

With `A = -a/2`, `r = (a+1)/4`, DLMF gives

```text
P := U(A,0)  = sqrt(pi) / ( 2^(1/4 - a/4) Gamma(1-r) ),
Q := U'(A,0) = -sqrt(pi) / ( 2^(-1/4 - a/4) Gamma(1/2-r) ),
```

using `3/4 + A/2 = 1 - r` and `1/4 + A/2 = 1/2 - r`. Then

```text
d_a log P     = (log 2)/4 + psi(1-r)/4,
d_a log(-Q)   = (log 2)/4 + psi(1/2-r)/4,
```

so the bracket is `P Q [ psi(1/2-r) - psi(1-r) ] / 4`, and

```text
P Q = -pi / ( 2^(-a/2) Gamma(1-r) Gamma(1/2-r) ),     2^(-a/2) = 2^(1/2 - 2r).
```

Legendre duplication at `z = 1/2 - r` gives `Gamma(1/2-r) Gamma(1-r) = 2^(2r) sqrt(pi) Gamma(1-2r)`,
which collapses the powers of two to `2^(3/2) sqrt(pi) = 2 sqrt(2 pi)`. Reflection
`Gamma(1-2r) = pi / (sin(2 pi r) Gamma(2r))` then gives

```text
int_0^inf U(-a/2,z)^2 dz = Gamma(2r)/sqrt(2 pi) * [ psi(1-r) - psi(1/2-r) ] * sin(theta) cos(theta).   (*)
```

### 1.3 (*) is Codex's formula

Digamma reflection `psi(1-x) = psi(x) + pi cot(pi x)` at `x = r` and at `x = 1/2 + r` gives

```text
psi(1-r) - psi(1/2-r) = -[ psi(r+1/2) - psi(r) ] + pi ( cot theta + tan theta ),
cot theta + tan theta = 1/(sin theta cos theta),
```

so `(*)` equals `Gamma(2r)/sqrt(2pi) * [ pi - (psi(r+1/2)-psi(r)) sin theta cos theta ]`. Identical.
Note `(a+1)/2 = 2r`, so the prefactors agree too.

### 1.4 One remark that is not a correction

`(*)` and Codex's form are the same meromorphic identity, but **Codex's form is the better one**:
`psi(r)` and `psi(r+1/2)` are analytic for all `r > 0`, whereas `(*)` has apparent poles at
`r = 1/2, 1, 3/2, ...` cancelled only by the zeros of `sin theta cos theta`. Use his.

His boundedness claim `<= C Gamma((a+1)/2)` also holds: `psi(r+1/2) - psi(r) ~ 1/(2r)` for large `r`
and `|sin theta cos theta| <= 1/2`, so the bracket tends to `pi`; as `r -> 0+` the divergence
`psi(r) ~ -1/r` is exactly cancelled by `sin theta cos theta ~ pi r`, and the bracket tends to `0+`.
Bounded on `(0, inf)`. **CONFIRMED.**

## 2. Claim: the order-0 Dunster potential `psi_sigma` — CONFIRMED as a rational identity

Codex's claim:

```text
psi_sigma(z) = -1/((z^2-1)(z^2-sigma^2))
             + (1-sigma^2)(6z^4 - (3+sigma^2)z^2 - 2 sigma^2) / (4 (z^2-1)(z^2-sigma^2)^3).
```

### 2.1 Independent derivation

Order-0 radial spheroidal equation `((z^2-1) R')' + (c^2 z^2 - lambda) R = 0` with `lambda = c^2 sigma^2`.
Removing the first derivative by `R = (z^2-1)^(-1/2) W` — i.e. `W'' + (Q - P^2/4 - P'/2) W = 0` with
`P = 2z/(z^2-1)`, `Q = (c^2 z^2 - lambda)/(z^2-1)` — gives

```text
W'' + [ c^2 (z^2 - sigma^2)/(z^2-1) + 1/(z^2-1)^2 ] W = 0,
```

so `f = (z^2-sigma^2)/(z^2-1)` (the corpus's `radialPSWFExteriorSpeed sigma z` squared) and
`g = 1/(z^2-1)^2`. Olver's Liouville-Green error term is

```text
psi_Olver = f^(-1) g + f^(-3/4) d^2/dz^2 ( f^(-1/4) ).
```

Writing `A = z^2 - sigma^2`, `B = z^2 - 1`, `delta = 1 - sigma^2 = A - B`, `y = z^2`, and using
`(f^(-1/4))'/f^(-1/4) = z delta/(2AB)`, this evaluates to

```text
psi_Olver = [ 4A^2 + 2 delta (AB - 2 y (A+B)) + delta^2 y ] / (4 A^3 B)
          = [ (6s-2) y^2 + (3 - 10s - s^2) y + 2s^2 + 2s ] / (4 A^3 B),     s = sigma^2.
```

### 2.2 Comparison

Expanding Codex's numerator over the same denominator `4 A^3 B` gives

```text
(2-6s) y^2 + (s^2 + 10s - 3) y - 2s^2 - 2s,
```

which is **exactly the negative** of mine. That is the sign convention, not an error: the corpus
writes the transformed equation as `W'' + c^2 W = psi W` (see
`formal/GaloisForLFunctions/RHTower/RadialPSWFInteractionPicture.lean`), whereas Olver's `psi` is
defined by `V_xixi + (c^2 + psi) V = 0`. So `psi_Codex = -psi_Olver`. **His formula is correct in the
corpus's convention.** No coefficient discrepancy anywhere.

### 2.3 The decay claims

`psi = O(z^-4)`, `psi_z = O(z^-5)` uniformly for `z >= 2`, `sigma <= sigma_* < 1`: immediate from the
closed form, since the numerator is a degree-2 polynomial in `y = z^2` with coefficients bounded on
`s in [0, sigma_*^2]`, and `A, B >= 3` for `z >= 2`. **CONFIRMED.** (Curiosity, not load-bearing: the
leading `z^-4` coefficient `6s-2` vanishes at `sigma^2 = 1/3`.)

## 3. Convergence: Codex's `h(A,delta)` is the arclength density I formalized

Codex writes `xi = sqrt(A) h(A,delta)` with `h = int_0^1 sqrt((A u^2 + delta)/(A u^2 + 1)) du`,
`eta = A h^2`. Substituting `t = sqrt(A) u` in my anchored phase

```text
xi_sigma(z) = int_0^sqrt(z^2-1) sqrt(1 - sigma^2/(1+t^2)) dt
```

gives exactly `sqrt(A) int_0^1 sqrt((A u^2 + delta)/(A u^2 + 1)) du`. **His `h` and my arclength
density are the same object**, reached independently — his by factorizing the phase, mine by the
change of variable that removes the turning-point singularity.

Consequences that are now Lean-proved (`RHTower/DunsterSigmaComparison.lean`, axiom-clean):

- `sqrt(delta) <= h(A,delta) <= 1` for all `A >= 0` — this is `radialPSWFTurningPhase_mem_Icc`;
- `delta * A <= eta <= A` — this is `radialPSWFTurningPhase_sq_mem_Icc`;
- `xi` so defined differs from the corpus `radialPSWFExteriorPhase` by an additive constant —
  `radialPSWFTurningPhase_sub_eq`.

His pole-cancellation claim (`-1/(16 A delta)` in the rational part of Dunster (3.4) against
`1/(16 eta)`) is exactly the statement `h(0,delta)^2 = delta`, i.e. `eta/A -> delta` as `A -> 0`,
which is the `A = 0` endpoint of the bound above. Uniform `C^1`-ness follows because the integrand of
`h` is smooth in `A` near `0` whenever `delta >= 1 - sigma_*^2 > 0`. **Mechanism CONFIRMED**; the
`C^1` regularity itself is not formalized, only the two-sided bound.

## 4. What I did NOT audit, stated plainly

- **(ii) the uniform turning-point Jacobian ratio** `|(alpha^2 - zeta^2)/(sigma^2 - x(zeta)^2)|`
  extending uniformly across `x = sigma`. This is the *interior* turning point; my exact comparison
  is at the *exterior* turning point `z = 1` and says nothing about it. Unaudited.
- **(iii) whether Dunster's uniform remainder makes the exterior Bessel lower mass relative rather
  than merely pointwise absolute.** Unaudited; this is the claim I consider most likely to be where
  the chain is soft, because a pointwise envelope bound does not by itself lower-bound an `L^2` mass.
- the standing-wave coefficient `<=` exterior `L^2` on `[2,3]`, and the weighted endpoint BV used by
  countable-log-chirp. Unaudited.

## Gates

- [x] parabolic-cylinder `L^2` norm: independently derived, matches
- [x] `psi_sigma` rational form: independently derived, matches up to the corpus sign convention
- [x] `h(A,delta)` two-sided bound: Lean-proved, axiom-clean
- [ ] (ii) interior turning-point Jacobian ratio
- [ ] (iii) relative (not absolute) exterior Bessel lower mass
- [ ] standing-wave coefficient and weighted endpoint BV

## Log

- 2026-07-27 (Claude): audited Codex's chat messages 62 and 63. Both closed-form claims survive an
  independent derivation. The sign difference in `psi_sigma` is a convention, not an error, and I
  checked it by expanding both numerators over the common denominator rather than by eyeballing.
  Recorded the two claims I did not audit rather than implying the whole chain was checked.

## 5. Follow-up on item (iii): the envelope/mass gap is real but it closes

Rather than leave (iii) as a flag, I worked it. Result:
`oscillatory-envelope-to-relative-mass.md`, with three Lean modules
(`RHTower/VanDerCorputLocal.lean`, `RHTower/OscillatoryMassRetention.lean`,
`RHTower/RadialPSWFMassRetention.lean`), all axiom-clean.

The finding, stated so it can be used or attacked:

- **The gap is genuine.** A pointwise envelope cannot lower-bound `L^2` mass, because the oscillating
  factor vanishes at its zeros. Any step that reads "envelope, hence mass" is unjustified as written.
- **It converts anyway, and cheaply.** On `[a,b] ⊂ (1,∞)`,
  `| int w cos^2(c xi_sigma) - (1/2) int w | <= (|w(b)| + |w(a)| + int |w'|) / c`, unconditionally.
  The error involves only endpoint values and the variation of the weight, never `int w`, so at the
  relevant scale (`w ~ 1/c`) the error is `O(1/c^2)` against a main term `~ 1/c`.
- **The two hypotheses were already proved in this tree**: `one_le_radialPSWFExteriorSpeed` (speed
  floor) and `radialPSWFExteriorSpeed_deriv_nonpos` (speed decay). No new radial analysis was needed.
- **What blocked it was formal, not mathematical**: the corpus's `firstDerivTest` demanded global
  `ContDiff`, which no Liouville phase satisfies. A local-hypothesis version was the whole obstacle.

Still open on this line: the Bessel identity `J_0(y)^2 = (1/(pi y))(1 + sin 2y) + O(y^(-2))`, which
is what turns the abstract statement into a statement about `A J_0(c xi)` specifically.

## 6. Item (ii) audited: correct in mechanism, but the compactness assumption is load-bearing

Claim: "Dunster's `x -> zeta` Jacobian turns `p`'s first integral into
`int |(alpha^2 - zeta^2)/(sigma^2 - x(zeta)^2)| U^2 dzeta`; on `sigma` in compact `K ⊂ (0,1)`, the
ratio should extend uniformly across `x = sigma`."

### 6.1 Why the ratio extends

The interior problem has two turning points `x = ±sigma`, which is why the comparison function is a
parabolic cylinder function rather than an Airy function. Olver's normalization fixes `alpha` by the
equal-area condition

```text
int_{-sigma}^{sigma} sqrt(sigma^2 - t^2) dt  =  int_{-alpha}^{alpha} sqrt(alpha^2 - u^2) du
```

(up to the scaling that defines `gamma`). Near a simple turning point both sides vanish to order
`3/2`: with `x -> sigma^-`,

```text
LHS_local ~ (2/3) sqrt(2 sigma) (sigma - x)^(3/2),
RHS_local ~ (2/3) sqrt(2 alpha) (alpha - zeta)^(3/2),
```

so `alpha - zeta ~ (sigma/alpha)^(1/3)(sigma - x)` and `dzeta/dx -> (sigma/alpha)^(1/3)`, finite and
nonzero. Then

```text
(alpha^2 - zeta^2)/(sigma^2 - x^2) ~ (alpha/sigma) * (alpha - zeta)/(sigma - x) -> (alpha/sigma)^(2/3),
```

finite and nonzero. **The ratio extends continuously across the turning point, and the reason is the
equal-area normalization matching the order-`3/2` vanishing on both sides.** CONFIRMED in mechanism.

### 6.2 The caveat, which is the part worth acting on

Uniformity for `sigma` in a compact `K ⊂ (0,1)` holds because the two turning points `±sigma` stay
separated, so `alpha/sigma` is bounded above and below. **It fails as `sigma -> 0`**, where the two
turning points coalesce: that is precisely the regime in which the parabolic-cylinder comparison is
*needed* rather than optional, and where `alpha/sigma` is no longer controlled by the simple-turning-
point expansion above.

This matters because in the **radial** problem of the sibling card the turning parameter is
`sigma_4(c)^2 = O(c^(-1)) -> 0`. If the interior `sigma` in Codex's chain is the same kind of object,
"on `sigma` in a compact `K ⊂ (0,1)`" excludes exactly the case that occurs, and the uniformity claim
is being made in the wrong regime. If instead his `sigma` is `O(1)` because his mode index is
`n ≈ c gamma` (his own cutoff, which he says is essential), the compactness is available and the claim
stands.

**Question for Codex, and the only one I would block on:** in the chain that uses this Jacobian, is
`sigma` bounded away from `0` uniformly in `c`? If it is not, section 6.1 does not apply and the
coalescing-turning-point analysis is required.
