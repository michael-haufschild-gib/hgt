# Zeta is not square integrable on the critical line

- **ID:** `zeta-not-square-integrable-critical-line`
- **Stage:** 1 — in progress
- **Type:** THEOREM (classical), `[FORMALIZATION TARGET]`
- **Serves:** the last open gate of
  `../2-fully-proven/new_scientific_knowledge/burnol/burnol-hedenmalm-archimedean-completion-domain-radical-exchange.md`,
  whose Section 1 excludes the uncompleted divided vectors from the coordinate domain.

## Statement

```text
NOT MemLp (fun t : R => riemannZeta (1/2 + i t)) 2 volume.                (Z)
```

Classically this is the divergence of `integral_0^T |zeta(1/2+it)|^2 dt = T log T + O(T)`, but the
mean-square asymptotic is far more than `(Z)` needs.  The route below proves `(Z)` from the jump
structure of the fractional part, using only `L²` Fourier theory.

## Proof route

Put

```text
phi(y) = frac(e^y) e^(-y/2),   y in R.                                   (1)
```

`phi in L²(R)`: substituting `x = e^y`,
`integral |phi|^2 dy = integral_0^infinity frac(x)^2 x^(-2) dx`, which converges at both ends.

The corpus already owns the fractional-part Mellin identity: for `0 < Re s < 1`,

```text
integral_0^infinity frac(x) x^(-s-1) dx = 1/(s-1) - zeta(s)/s.           (2)
```

Substituting `x = e^y` and `s = 1/2 + 2 pi i xi` turns `(2)` into the Fourier transform of `phi`:

```text
Fourier(phi)(xi) = 1/(s-1) - zeta(s)/s,     s = 1/2 + 2 pi i xi.         (3)
```

Both terms of the right side of `(3)` are separately `L²` exactly when `zeta` is, and `1/(s-1)` is
`L²` unconditionally, so

```text
zeta in L²(line)  <->  s Fourier(phi)(xi) - 1  in L²(dxi).               (4)
```

Indeed `s/(s-1) = 1 + 1/(s-1)` and `s Fourier(phi) = (1/2) Fourier(phi) + 2 pi i xi Fourier(phi)`,
and `(1/2)Fourier(phi)` is `L²`.

Now suppose the right side of `(4)` holds and let `g` be its inverse Fourier transform, `g in L²`.
Plancherel against a Schwartz test function `chi` gives, using
`Fourier(chi')(xi) = 2 pi i xi Fourier(chi)(xi)` and Fourier inversion at the origin,

```text
integral g conj(chi) = - integral phi conj(chi') - c conj(chi(0))         (5)
```

for every Schwartz `chi`.  Restricting to `chi` supported in a small interval around `log 2`, which
excludes the origin, kills the last term:

```text
integral phi conj(chi') = - integral g conj(chi).                         (6)
```

So `phi` has weak derivative `-g in L²` near `log 2`.  Take `chi = chi_eps` a smooth bump rising on
`(log 2 - eps, log 2)` and falling on `(log 2, log 2 + eps)`.  Then

```text
|integral g conj(chi_eps)| <= ||g||_{L²(I_eps)} sqrt(2 eps) -> 0,         (7)
integral phi conj(chi_eps') -> phi(log 2 -) - phi(log 2 +) = 1/sqrt 2.    (8)
```

`(8)` holds because `frac(e^y)` is continuous on each side of `log 2` and jumps by `-1` there, so
`phi` jumps by `-e^(-(log 2)/2) = -1/sqrt 2`.  Together `(6)`, `(7)`, `(8)` are contradictory, so
the right side of `(4)` fails and `(Z)` holds.

## Corpus assets already available

```text
formal/GaloisForLFunctions/RHTower/FractionalPartZeta.lean      -- the identity (2)
formal/GaloisForLFunctions/RHTower/SoninL2Model.lean            -- fourierUnitary on L²(R)
Mathlib/Analysis/Fourier/LpSpace.lean                           -- Plancherel for L²
Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean        -- Schwartz Fourier calculus
```

## Consumer already in Lean

```text
formal/GaloisForLFunctions/RHTower/BurnolHedenmalmUncompletedDomain.lean

memLp_riemannZeta_criticalLine_of_dividedZetaLine
  : if the first divided vector and its coordinate multiple are both square integrable on the
    critical line then so is zeta,
not_memLp_coordinate_dividedZetaLine
  : hence (Z) excludes the divided vector from the coordinate domain.
```

## Gates

- [x] the algebraic transport step and its contrapositive consumer (Lean)
- [ ] `phi in L²(R)` and the substituted Fourier identity `(3)`
- [ ] the equivalence `(4)`
- [ ] the weak-derivative identity `(5)`--`(6)` from Plancherel
- [ ] the mollifier contradiction `(7)`--`(8)`
- [ ] `(Z)`, and with it the uncompleted domain exclusion of the parent card
