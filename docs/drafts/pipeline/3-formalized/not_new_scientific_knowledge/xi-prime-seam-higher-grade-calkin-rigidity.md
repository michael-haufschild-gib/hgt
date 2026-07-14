# Xi prime-seam higher-grade Calkin rigidity

- **ID:** `xi-prime-seam-higher-grade-calkin-rigidity`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[TOP-DOWN CHAIN]`, `[VALUE RELATION]`, `[OPERATOR RIGIDITY]`
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `xi-prime-seam-euler-zero-tangent.md`;
  `SummableEulerCalkinInjectivity.lean`

## Statement

Fix a prime `p`, a real `0 < sigma < 1`, and a Sonin cutoff `a > 0`.  The exact difference between
the actual Euler-unit tangent and its empty-parameter first coefficient is the FE-paired Lambert
tail

```text
T_p^(>1)(sigma)
  = sum_(m>=2) m log(p)
      [p^(-m sigma)-p^(-m(1-sigma))].                    (1)
```

Write its grade-`m=j+2` coefficient as `c_j(p,sigma)`, lift the prime-power scale `p^(j+2)` to the
positive-Euler metric corner, and sum in operator norm.  Lean proves:

```text
sum_j c_j(p,sigma) = T_p^(>1)(sigma),                    (2)
sum_j |c_j(p,sigma)| < infinity,                         (3)
p^(j+2) is strictly increasing,                          (4)
c_0(p,sigma) != 0 iff sigma != 1/2.                      (5)
```

Summable Euler Calkin injectivity then gives the pointwise rigidity law

```text
the higher-grade even Sonin corner is compact
  iff sigma = 1/2,                                       (6)
```

and the identical law after transport to the concrete archimedean Hardy--Titchmarsh source line.
No zero data, RH assumption, limiting measure, or unproved convergence input occurs in `(1)`--`(6)`.

For the actual Xi divisor support, define `XiPrimeEulerFEHigherGradeCompact(a,p)` to say that this
one fixed prime's higher-grade archimedean corner is compact at the horizontal coordinate of every
divisor point.  Then

```text
XiPrimeEulerFEHigherGradeCompact(a,p) iff RH.             (7)
```

## Proof

The already-formalized Lambert expansion supplies `(2)`.  Both reflected geometric-derivative
series converge absolutely throughout the open strip, giving `(3)`.  Prime-power scales satisfy
`p^(j+2)>1` and are strictly increasing.  If the grade-two coefficient vanished, equality of the
norms of `p^(-2 sigma)` and `p^(-2(1-sigma))`, followed by strict monotonicity of real powers with
base `p>1`, would force `sigma=1/2`; this proves `(5)`.

The summable Calkin-injectivity theorem says that every nonzero absolutely summable coefficient
family on strictly increasing positive-Euler scales has a noncompact lower corner.  It applies
directly to `(1)`.  On the critical line every coefficient vanishes termwise, so the operator is
zero and hence compact.  This proves `(6)`.  Applying `(6)` at every Xi divisor point and using the
exact reflection-fixed formulation of RH proves `(7)`.

## Top-down consequence

This closes the ambiguity left by the empty-versus-actual Euler tangent comparison.  The
higher-prime-power Lambert grades do **not** vanish in the Sonin Calkin quotient off the critical
line.  The paper Marcinkiewicz quotient and the operator Calkin quotient therefore cannot be
interchanged at this interface.

The positive constraint is:

```text
successful actual-Euler operator cancellation
  -> nonlinear completed-product, cross-grade, or cross-place coupling
  -> cancellation of the faithful higher-grade Calkin class
  -> critical-line orientation.                          (8)
```

Thus a proof route cannot declare the additive tail in `(1)` compact and retain only the
degree-one seam.  It must exhibit an additional coupled term with exactly the opposite essential
class.  Equation `(6)` makes that remaining target falsifiable and operator-theoretic rather than
an unspecified chart-transfer issue.

## Literature boundary

Finite completed local products may acquire quasi-inner behavior even when their individual local
factors do not.  This is compatible with `(8)`: the formal theorem rules out only the standalone
additive higher-grade remainder.  It does not rule out cancellation inside a nonlinear completed
product or an all-place coupling.  General Hankel/Schatten regularity theory likewise does not
supply the source-specific cross-grade cancellation required by `(8)`.

## Lean

`formal/GaloisForLFunctions/RHTower/XiPrimeSeamHigherGradeCalkinRigidity.lean` proves:

```text
primeHigherPowerScale_one_lt
primeHigherPowerScale_strictMono
primeEulerFEHigherGradeCoefficient_hasSum
summable_norm_primeEulerFEHigherGradeCoefficient
primeEulerFEHigherGradeCoefficient_ne_zero_of_re_ne_half
primeEulerFEHigherGradeEvenCorner_isCompactOperator_iff
primeEulerFEHigherGradeArchimedeanCorner_isCompactOperator_iff
xiPrimeEulerFEHigherGradeCompact_iff_riemannHypothesis
```

## Gates

- [x] exact identification with the FE-paired Lambert tail
- [x] absolute summability on the open strip
- [x] strictly increasing prime-power operator scales
- [x] grade-two faithfulness to horizontal displacement
- [x] even-Sonin Calkin rigidity
- [x] concrete archimedean Hardy--Titchmarsh Calkin rigidity
- [x] fixed-prime Xi-divisor capstone equivalent to RH
- [x] no `sorry`, `admit`, axiom, or RH hypothesis in the pointwise theorem
- [ ] construct the cross-grade, completed-product, or cross-place cancellation demanded by `(8)`
