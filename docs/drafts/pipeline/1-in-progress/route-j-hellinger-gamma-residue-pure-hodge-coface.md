# Route J Hellinger--Gamma residue pure-Hodge coface

- **ID:** J-HGRPHC
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (paper proof and Lean certificate pending)
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

## Frozen conjecture J-HGRPHC

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
4. Hence `Q_n(a)` converges to zero in the coefficient graph norm and the partial coface
   primitives converge to `-Q_0(a)`.
5. The secondary Poincare traces telescope with the same signs and retain the unsquared
   reflection-odd boundary at every finite grade.

All statements are unconditional and use only factorial domination of a fixed exponential.

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

