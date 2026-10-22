# Route J Hellinger--Gamma residue pure-Hodge coface

- **ID:** J-HGRPHC
- **Stage:** 1-in-progress (local theorem proved/formalized; global tensor survivor open)
- **Type:** THEOREM (paper and unconditional Lean) + OPEN PRODUCER
- **Source:** updated oriented-source-admission producer, Hellinger--Beta Gamma column, and Route-J pure-Hodge modular transgression
- **Open core:** construct an adjacent-grade source coface whose pure-Hodge Green primitives are graph-Cauchy without assuming divisor admission.

## Frontier distinction

The updated oriented-source-admission paper excludes fixed-witness residue scaling.  It asks for an
off-diagonal adjacent-grade Hellinger--Beta coface with telescoping finite boundaries and a
graph-Cauchy labelled chain.  The already proved pure-Hodge modular transgression supplies the
local admitted carrier and unsquared secondary trace, but its ungauged common-depth capacity
diverges for every nonzero modular displacement.

The even Gamma residue inside the reflected Hellinger--Beta column supplies a source-native gauge

```text
g_n = Res_{z=-2n} Gamma(z) = 1 / (2n)!.
```

This is not multiplication by the full nonzero Hellinger residue and therefore is not covered by
the fixed-witness no-go.  It changes grade and suppresses both reciprocal modular directions.

## Theorem J-HGRPHC

Fix distinct primes `p,q`, real modular displacement `a`, and let `Omega_n(a)` be the pure-Hodge
odd transgression on the labelled common-depth pair `((p,n),(q,n))`.  Define

```text
Q_n(a) = g_n Omega_n(a),
E_n(a) = Q_(n+1)(a) - Q_n(a).
```

Then:

1. `Q_n(a)` and `E_n(a)` lie in the actual Gamma-admitted Hodge sector for every auxiliary
   boundary displacement; their coefficient planes remain Hodge anti-fixed.
2. Finite boundaries telescope exactly:

   ```text
   sum_{n < N} E_n(a) = Q_N(a) - Q_0(a).
   ```

3. With `C_a(p,q,n)` the two-sided pure-Hodge graph capacity,

   ```text
   K_a(p,q,n) = g_n^2 C_a(p,q,n) -> 0.
   ```

   In particular `K_a` is uniformly bounded for every fixed `a`, including `a != 0`.
4. The squared Euclidean norm of the two odd coefficient channels is bounded by `K_a(p,q,n)`.
   Hence `Q_n(a)` is graph-null in its coefficient plane, and the partial coface primitives
   converge coefficientwise to `-Q_0(a)`.
5. The secondary Poincare traces telescope with the same signs and retain the unsquared
   reflection-odd boundary at every finite grade.

All statements are unconditional and use only factorial domination of a fixed exponential.

## Proof

The exact Gamma residue formula gives

```text
g_n = (-1)^(2n)/(2n)! = 1/(2n)! != 0.
```

Write `L=log p+log q` and `c=|2aL|`.  The PHMT sewing identity rewrites the two-sided capacity as

```text
C_a(p,q,n)=exp(2aL(n+1))+exp(-2aL(n+1)).
```

Both exponents are at most `c(n+1)`, so

```text
0 <= K_a(p,q,n)
   <= 2 exp(c(n+1))/((2n)!)^2
   <= 2 exp(c) (exp(c))^n/n!.
```

The last sequence tends to zero by factorial domination.  It is also bounded above by the explicit
constant `2 exp(c) exp(exp(c))`, using the exponential-series term bound.  This proves convergence
and uniform capacity for every real `a`; no critical-line condition occurs.

If `x=exp(-aR_n)` and `y=exp(aR_n)`, the squared norm of the two opposite odd channels is
`g_n^2 (y-x)^2/2`.  Since `(y-x)^2/2 <= x^2+y^2`, it is bounded by `K_a(p,q,n)` and therefore
tends to zero.

Every `Q_n(a)` is a scalar multiple of the already proved actual-admitted pure-Hodge
transgression, so every adjacent difference `E_n(a)` is admitted for every auxiliary displacement.
Linearity and the anti-fixed coefficient theorem preserve Hodge parity.  Finally,

```text
sum_{n<N} (Q_(n+1)-Q_n)=Q_N-Q_0
```

is the finite difference identity.  Applying the gradewise Poincare trace after constructing the
vector coface gives

```text
Tr_n(Q_n)=g_n GammaOdd_a((p,n),(q,n)).
```

Because `g_n` is nonzero and the cell half-heights are distinct, this scalar vanishes exactly when
`a=0`.  Thus graph damping preserves the finite unsquared detector rather than replacing it by a
positive square.

## Lean certificate

Production module:

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedHellingerGammaPureHodgeCoface.lean
```

It is wired into `GaloisForLFunctions.RHTower`.  Direct
`lake env lean GaloisForLFunctions/RHTower/CCM/CCMFirstClockPrimitivePromotedHellingerGammaPureHodgeCoface.lean`
passes.  Load-bearing declarations include:

- `hellingerEvenGammaResidueGauge_eq_gammaNegNatResidue`;
- `hellingerGammaGaugedPureHodgeCapacity_tendsto_zero`;
- `hellingerGammaGaugedPureHodgeCapacity_uniform`;
- `hellingerGammaGaugedOddCoefficientCapacity_tendsto_zero`;
- `hellingerGammaPureHodgeAdjacentCoface_mem_actual`;
- `sum_hellingerGammaPureHodgeAdjacentCoface`;
- `hellingerGammaGaugedPureHodgeCoefficients_antiFixed`;
- `hellingerGammaGaugedPureHodgeSecondaryTrace_eq_zero_iff`.

## Falsity attack

- **Not the full missing landing.** The limit above is one depth-zero pure-Hodge carrier, not the
  completed Xi Green primitive.  Claiming Route J/L closure from it is forbidden.
- **Not fixed residue scaling.** `g_n` is the even Gamma-residue factor and changes with grade;
  adjacent differences leave every fixed incidence line.
- **No hidden critical-line premise.** Capacity convergence must be proved for arbitrary real `a`.
- **No scalar shortcut.** Admission and telescoping are vector-valued; the Poincare trace is taken
  only after the coface is constructed.
- **Potential failure point.** A coefficient-faithful tensoring with the completed Xi jet carrier
  may fail to preserve the source differential or may kill the relative admission quotient.

## Exact survivor after J-HGRPHC

Construct the coefficient-faithful tensor/coend of this coface with the completed Xi Green source,
prove its graph limit is the completed Xi Green primitive rather than a fixed pure carrier, and
audit injectivity on the relative admission quotient.  Until that is done the route remains open.

## Novelty audit

Corpus search finds the Gamma residue recurrence, Hellinger half-lattice residues, cofinal
pure-Hodge countertransport, and PHMT capacity classification separately.  No existing theorem
combines the even Gamma-residue gauge with the labelled pure-Hodge modular orbit to obtain an
adjacent-grade graph-Cauchy coface.
