# Zeta is not square integrable on the critical line

- **ID:** `zeta-not-square-integrable-critical-line`
- **Stage:** 3-formalized
- **Type:** THEOREM (classical statement, new elementary proof), `[FORMALIZED]`
- **Serves:** the last open gate of
  `burnol-hedenmalm-archimedean-completion-domain-radical-exchange.md`,
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

Both `phi in L^1(R)` and `phi in L^2(R)`: substituting `x = e^y`,

```text
integral |phi| dy = integral_0^infinity frac(x) x^(-3/2) dx,
integral |phi|^2 dy = integral_0^infinity frac(x)^2 x^(-2) dx,           (2)
```

and both converge, because `frac(x) = x` near `0` and `frac(x) <= 1` near infinity.  The corpus
owns the substitution as `integral_Ioi_eq_integral_exp_smul` and
`integrableOn_Ioi_iff_integrable_exp_smul`.

The corpus also owns the exact fractional-part Mellin identity: for `0 < Re w < 1`,

```text
integral_0^infinity frac(x) x^(-(w+1)) dx = - zeta(w)/w.                 (3)
```

Substituting `x = e^y` and `w = 1/2 + 2 pi i xi` turns `(3)` into the Fourier transform of `phi`:

```text
Fourier(phi)(xi) = - zeta(w)/w,     w = 1/2 + 2 pi i xi.                 (4)
```

There is no extra pole term: the two halves `(0,1]` and `(1,infinity)` of `(3)` cancel it exactly.

**Step A.**  If `zeta` is square integrable on the critical line then `Fourier(phi)` is
*integrable*, by Cauchy--Schwarz against `1/|w|`:

```text
integral |Fourier(phi)| dxi = integral |zeta(w)|/|w| dxi
  <= (integral |zeta(w)|^2 dxi)^(1/2) (integral |w|^(-2) dxi)^(1/2) < infinity.   (5)
```

**Step B.**  With `phi` and `Fourier(phi)` both integrable, Fourier inversion holds at every
continuity point of `phi`:

```text
FourierInv(Fourier(phi))(y) = phi(y)   whenever phi is continuous at y.   (6)
```

Write `psi = FourierInv(Fourier(phi))`.  Since `Fourier(phi)` is integrable, `psi` is *continuous
everywhere*.

**Step C.**  `phi` is continuous at every `y` with `e^y` not an integer, and there

```text
phi(y) = (e^y - n) e^(-y/2)   for   n < e^y < n+1.                        (7)
```

Take `y_k = log 2 - 1/(k+1)` and `z_k = log 2 + 1/(k+1)`.  For large `k`, `1 < e^(y_k) < 2` and
`2 < e^(z_k) < 3`, so by `(6)`,`(7)`

```text
psi(y_k) = (e^(y_k) - 1) e^(-y_k/2) -> 1/sqrt 2,
psi(z_k) = (e^(z_k) - 2) e^(-z_k/2) -> 0.                                 (8)
```

Both sequences tend to `log 2` and `psi` is continuous, so `psi(log 2)` equals both `1/sqrt 2` and
`0`.  That is absurd, so the hypothesis of Step A fails and `(Z)` holds.

This is much cheaper than the mean-square asymptotic: it needs no Sobolev theory, no Hardy space,
no Phragmen--Lindelof and no approximate functional equation --- only the corpus's fractional-part
identity, the log substitution, `L^1` Fourier inversion, and the single jump of `frac` at `2`.

## Corpus assets already available

```text
formal/GaloisForLFunctions/RHTower/FractionalPartZeta.lean      -- the identity (2)
formal/GaloisForLFunctions/RHTower/SoninL2Model.lean            -- fourierUnitary on L²(R)
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonBerezinFaithful.lean
  integral_Ioi_eq_integral_exp_smul, integrableOn_Ioi_iff_integrable_exp_smul  -- the substitution
Mathlib/Analysis/Fourier/Inversion.lean
  MeasureTheory.Integrable.fourierInv_fourier_eq                 -- inversion at continuity points
Mathlib/Analysis/Fourier/FourierTransform.lean                   -- fourier_eq, 𝓕 and 𝓕⁻
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

- [x] the algebraic transport step and its contrapositive consumer
- [x] `phi in L^1(R)` via the log substitution `(2)`
- [x] the Fourier identity `(4)` from the corpus fractional-part identity `(3)`
- [x] Step A: Cauchy--Schwarz integrability of `Fourier(phi)` `(5)`
- [x] Step B: continuity of `psi` and inversion at continuity points `(6)`
- [x] Step C: the two-sided jump contradiction `(7)`,`(8)`
- [x] `(Z)`, and with it the uncompleted domain exclusion of the parent card

## Formal theorem chain

```text
formal/GaloisForLFunctions/RHTower/ZetaCriticalLineNotSquareIntegrable.lean

fractLogCarrier                                     phi y = frac(e^y) e^(-y/2)          (1)
fractLogCarrier_eq_exp_smul                         the log substitution                (2)
integrable_fractLogCarrier                          phi is integrable                   (2)
criticalAbscissa                                    w = 1/2 + 2 pi i xi
fourier_fractLogCarrier                             Fourier(phi)(xi) = - zeta(w)/w      (4)
memLp_inv_criticalAbscissa                          1/w is square integrable
integrable_fourier_fractLogCarrier                  Step A                              (5)
continuous_fourierInv_of_integrable                 Step B, continuity of psi
fractLogCarrier_eq_left / _eq_right                 the two branches at log 2           (7)
continuousAt_fractLogCarrier_left / _right          continuity off the points log n
not_memLp_riemannZeta_criticalAbscissa              Step C, the contradiction        (8),(Z)

formal/GaloisForLFunctions/RHTower/BurnolHedenmalmUncompletedDomain.lean

not_memLp_riemannZeta_criticalLine                  (Z) in the natural parametrisation
not_memLp_coordinate_dividedZetaLine_unconditional  the parent card's exclusion
```

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/ZetaCriticalLineNotSquareIntegrable.lean  -- clean
lake env lean GaloisForLFunctions/RHTower/BurnolHedenmalmUncompletedDomain.lean     -- clean
lake build GaloisForLFunctions.RHTower.BurnolHedenmalmUncompletedDomain             -- success
#print axioms not_memLp_riemannZeta_criticalAbscissa -> [propext, Classical.choice, Quot.sound]
#print axioms not_memLp_riemannZeta_criticalLine     -> [propext, Classical.choice, Quot.sound]
```

Both modules are wired into `GaloisForLFunctions.RHTower`.
