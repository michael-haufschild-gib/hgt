# Burnol divided-shift physical dissipativity

- **ID:** `burnol-divided-shift-physical-dissipativity`
- **Stage:** 2-fully-proven
- **Type:** `[PAPER-PROVED] [REDISCOVERED BRIDGE]` / Route R reduction
- **Exact claim:** fixed-source projection flatness is equivalent to nonpositivity of one explicit
  physical dilation-autocorrelation port at every right-half Xi divisor point.

## Exact frontier

`BurnolXiDividedShiftSourceFlatness` asks that the projection of the Mellin Cauchy multiplier
applied to the fixed co-Poisson atom vanish.  Existing actual-zero annihilation instead applies to
Burnol's completed-Mellin Riesz evaluator.  No corpus theorem identifies those two vectors.

## Conjecture loop

1. `[FALSIFIED]` Actual-zero evaluator orthogonality directly makes the divided shift
   source-orthogonal.  Killing mechanism: these are different vectors; strict accretivity proves
   the divided shift of any nonzero source vector has nonzero source projection off the line.
2. `[CIRCULAR]` The evaluator and divided shift agree modulo the source orthogonal complement.
   Killing mechanism: this equality immediately gives the existing flatness endpoint and hence RH.
3. `[PAPER-PROVED]` The spectral divided shift is the physical one-sided dilation resolvent, and
   source flatness is equivalent to nonpositivity of its single fixed-source autocorrelation port.
   This does not identify the shift with the evaluator.  It changes the producer's codomain from a
   Hilbert-space vector equality to one real scalar inequality of the form output by an oriented
   Stokes energy law.

## Definitions

Let `H` be the even physical `L²` space, `U : H -> L²(R)` the corpus Mellin unitary, and

```text
V_u f(x) = sqrt(u) f(ux),
A_rho f = integral_[1,infinity] u^(-rho-1/2) V_u f du,
m_rho(t) = 1 / (rho - (1/2 + i t)),
M_rho = U^(-1) M_(m_rho) U.
```

For `Re rho > 1/2`, define the fixed atom

```text
f0 = coPoissonSubWindowEven(c=1/2,d=1)
```

and its physical port

```text
Pi(rho) = integral_[1,infinity]
  u^(-rho-1/2) <f0,V_u f0> du.
```

`BurnolXiDividedShiftPhysicalDissipativity` is

```text
for every Xi divisor rho with Re rho > 1/2, Re Pi(rho) <= 0.
```

## Paper proof

### Lemma 1: physical/spectral divided-shift identity

For every `f in H` and `Re rho > 1/2`, `A_rho f = M_rho f`.

Put `delta = Re rho - 1/2 > 0`.  The physical Bochner integrand has norm

```text
|u^(-rho-1/2)| ||V_u f|| = u^(-Re rho-1/2) ||f||,
```

whose integral over `[1,infinity)` is `||f||/delta`.  Thus `A_rho f` exists.  Since `U` is
bounded linear it commutes with this Bochner integral, and the corpus dilation law gives

```text
U(V_u f)(t) = u^(it) U(f)(t).
```

For arbitrary `G in L²(R)`, Cauchy--Schwarz and the preceding `L¹` bound give absolute
integrability of the weak pairing:

```text
integral_[1,infinity] integral_R
  |u^(-rho-1/2+it) conj(G(t)) U(f)(t)| dt du
 <= (1/delta) ||G||_2 ||U(f)||_2.
```

Fubini is therefore valid.  The scalar Laplace integral is

```text
integral_[1,infinity] u^(-rho-1/2+it) du
  = 1 / (rho-(1/2+it)) = m_rho(t).
```

Hence `<G,U(A_rho f)> = <G,m_rho U(f)>` for every `G`.  Hilbert-space extensionality and
unitarity give `A_rho f=M_rho f`.

### Lemma 2: physical-port identity and strict sign

The existing theorem `inner_burnolShift` and Lemma 1 give

```text
Pi(rho) = <f0,M_rho f0>.
```

The already formalized Cauchy-symbol identity gives

```text
Re Pi(rho) = (Re rho-1/2) ||M_rho f0||².
```

The multiplier symbol is nowhere zero and `f0 != 0`, so `M_rho f0 != 0`.  Therefore

```text
Re Pi(rho) > 0                                             (1)
```

at every point with `Re rho>1/2`, without any zero-location hypothesis.

### Theorem: scalarization of source flatness

Assume `BurnolXiDividedShiftSourceFlatness`.  At a right-half Xi divisor, existing source
non-erasure contradicts the asserted zero projection; hence no such divisor exists, so physical
dissipativity holds vacuously.

Conversely assume physical dissipativity.  At a right-half Xi divisor it contradicts `(1)`; hence
no such divisor exists, so source flatness holds vacuously.  Thus

```text
BurnolXiDividedShiftSourceFlatness
  <-> BurnolXiDividedShiftPhysicalDissipativity.
```

The existing RH consumer then closes RH from physical dissipativity.

## Hostile audit

- The physical/spectral identity is `[LITERATURE]`/`[BRIDGE]`: Mellin diagonalization of dilation
  and Burnol's divided-shift mechanism are classical.  No novelty claim attaches to it.
- Scalarization is not an RH proof.  The sign law remains RH-strength on actual Xi divisors.
- It is not a rename of projection flatness as a source task: the output type is weakened from an
  exact vector equation against the entire closed source space to one real inequality for one
  explicit autocorrelation.  Gamma/Stokes jump forms naturally output such signs.
- `[OPEN CORE]` Derive `Re Pi(rho) <= 0` at actual right-half Xi divisor points from a
  pre-divisor oriented Euler--Gamma Stokes boundary law.

## Literature boundary

- J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, J. Théorie des Nombres de Bordeaux 16 (2004), 65--94.
- J.-F. Burnol, *Entrelacement de co-Poisson*, Ann. Inst. Fourier 57 (2007), 525--602.

These sources provide Sonine/co-Poisson and Mellin-dilation mechanisms.  They do not supply the
new Route R source-side nonpositive Stokes sign.
