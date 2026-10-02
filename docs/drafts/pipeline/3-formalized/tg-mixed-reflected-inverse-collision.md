# TG full mixed-prime reflected inverse collision

- **ID:** TG-C5-INVERSE
- **Stage:** 3-formalized
- **Parent:** `../1-in-progress/tg-mixed-reflection-collision-counterterm.md`
- **Route:** TG
- **Modules:** `RHTower.PrimeBurnolConfluentMomentGram`,
  `RHTower.PrimeBurnolMixedReflectedCollision`

## Exact result

For every finite injective packet of literal prime-depth labels, let

```
f_i(r)=A_i r exp(-lambda_i r),
M_j(i,l)=A_i A_l (j+2)!/(lambda_i+lambda_l)^(j+3),
G=M_0,
K=M_2-M_1 G^-1 M_1.
```

The moment block `[[G,M_1],[M_1,M_2]]` is the literal L2 Gram of `(f_i,r f_i)`.
Both its determinant and `det K` are nonzero, with no assumed inverse or analytic premise.
Its inverse's lower-right block is exactly `K^-1`.

Let `c(k)` be the literal L2 Gram of all columns at clocks `k` and `-k`, retaining all
cross-prime entries. For `P=[[I,I],[I,-I]]`, its parity form `c_p=(1/2)P c P` satisfies

```
c_p(k)=T(k) J(k) T(k)^*,  T(k)=diag(I,i*k*I),
J(0)=2[[G,M_1],[M_1,M_2]],
lim_(k->0,k!=0) k^2 c_p(k)^-1 = [[0,0],[0,(1/2)K^-1]].
```

The rational entries defining `J` are continuous for every real clock parameter. The inverse
is continuous at zero because the confluent source Gram has nonzero determinant. The limit
is two-sided and punctured; no inverse of the collided raw Gram is asserted.

## Dependency-closed proof

1. Every radial jet `A_i r^(m+1) exp(-lambda_i r)` belongs to L2. Gamma integrability proves
   this for every natural order; exact Laplace integration gives every mixed factorial moment.
2. An L2-zero finite combination of `(f_i,r f_i)` is zero on the positive half-line by
   continuity and positivity of Lebesgue measure on open sets.
3. Evaluation at positive integers gives an exponential-polynomial relation at the distinct
   nonzero nodes `exp(-lambda_i)`. Corpus theorem `HTGeometry.expPolySum_eq_zero` forces each
   polynomial coefficient to vanish. Literal amplitudes are nonzero, giving independence.
4. The Gram criterion gives invertibility. The lower two block equations of its inverse,
   combined with `G G^-1=I`, give `R_22 K=I` and hence `R_22=K^-1`.
5. Exact rational identities establish the factorization of the actual reflected Gram.
   Multiplication of the inverse by `k^2` removes the scaling poles. Continuous inversion of
   `J` at zero then gives the displayed full matrix limit.

The second module also proves, for idempotents p,q and a matrix unit c,

```
Tr(c*C(c^-1 q c,q,p))
 = Tr(c p c^-1 q c (p-q)) + Tr(c (q p q-p q p)).
```

This exact reduction makes the complete cubic pole depend on the single inverse coefficient
above, instead of an uncontrolled three-inverse expansion.

## Frontier contribution and remaining work

TG-C4 supplied only a single prime-depth pole. This result identifies its full mixed-prime
replacement: the inverse of the radial Schur complement, not a sum of diagonal inverses.
It removes assumed invertibility from the collision calculation and retains source provenance.

The actual theta-weighted cubic coefficient `-Tr(G K^-1 (U-I/2) G V)` is now proved in
`PrimeBurnolMixedCubicPrincipal`; see `tg-mixed-reflected-cubic-principal.md`. Gamma/continuum
cancellation, a bound uniform in packet growth, and the source-to-Hardy index identity remain
open. RH is neither proved nor falsified by these finite identities.

## Audit

- Combined scratch module: `lake --old env lean`, exit 0, no warnings.
- Confluent moment production leaf: direct foreground `lake --old env lean -o ...`, exit 0.
- Mixed collision production leaf: direct foreground `lake --old env lean -o ...`, exit 0.
- Both production leaves emit no warnings. Separate import audit checks all 21 public theorems:
  only `propext`, `Classical.choice`, and `Quot.sound`; no new axioms or proof holes.
- Both modules wired into the RHTower umbrella; no umbrella or full build requested.
- Corpus index regenerated. Formal lint exits 1 on ten unrelated unwired RHTower leaves:
  CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
  CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
  CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
  ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving. Neither new module is reported.
- Scoped tracked-file whitespace check passes. Owned temporary proof/search files cleaned.
