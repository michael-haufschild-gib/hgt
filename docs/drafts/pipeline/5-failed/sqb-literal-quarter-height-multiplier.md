# SQB literal quarter-height multiplier

Status: this scalar multiplier mechanism is closed negatively. Its sharp
positive survivor is paper-proved and formalized. SQB itself remains live; RH
remains unproved.

## Mechanism and exact obstruction

The entire Casimir transform is unchanged by shifting the scattering exponent
s by one quarter. The literal source candidate is multiplication of the original
completed Eisenstein field by y^(−1/4), shifting its outgoing power accordingly.
For every actual Xi copy rho, this candidate fails scalar modular inversion
invariance. With Q=x²+y² and S(x,y)=(-x/Q,y/Q), its exact law is

`Q^(−1/4)v(S(x,y))=v(x,y)`.

The original field has nonzero horizontal mean on every positive horizontal
line. At a nonzero point of height two, Q>1, so the multiplier cannot be one.
No selected nonzero field value is assumed.

## Strong positive survivor

The complete transformed differential equation retains an explicit forcing:

`[−Delta_H−(rho/2+1/4)(1−rho/2−1/4)]v`
`= (1/2)y^(−1/4)[y partial_y E−(1−rho/2)E]`.

At every actual Xi copy the bracket is precisely the differentiated full Fourier
tail minus its outgoing indicial multiple. The incoming Weyl term cancels through
Lambda(rho)=0. This full remainder, and the displayed second-order residual,
beat every fixed complex height power along each fixed vertical ray.

There is also a sharp density classification. Among all real power weights y^b,
the squared density y^b|v|² is inversion invariant everywhere if and only if
b=1/2. Its unique compensating density is exactly |E|² pointwise. Restoring this
power-weighted density therefore restores the original density rather than an
independent improvement in its size.

The [complete cusp-norm classification](../3-formalized/sqb-full-source-cusp-norm.md)
sharpens this statement in the full two-dimensional cusp measure. With all
Fourier modes retained, `y^b|v|²/y²` is integrable exactly when
`b+1/2<Re rho`. Thus the unweighted quarter field is integrable exactly for
`Re rho>1/2`, while the unique invariant compensation b=1/2 has divergent
norm at every actual Xi copy. The proof subtracts an admitted complete tail
and uses the nonzero original Weyl coefficient; the endpoint is divergent.

These are the exact surviving source equation, remainder, transformation law,
and optimal power compensation. Pointwise rapid forcing does not establish
normalized Hilbert-space occurrence or an estimate for the entire-transform
operator. Other intertwiners, corrections, and carriers are not excluded.

## Proof and Lean status

[Dependency-closed paper proof and audit](../3-formalized/sqb-quarter-shift-source-equation.md).
The two modules `SelbergScatteringHeightConjugation` and
`SelbergScatteringQuarterShiftSource` contain 21 public declarations in namespace
`RHTower.SelbergScatteringHeightConjugation`. Both final module audits, all public
axiom audits, umbrella wiring, index coverage, and formal lint pass. Only
`propext`, `Classical.choice`, and `Quot.sound` occur in the axiom reports.

The additional module `SelbergScatteringCuspNorm` contains ten public declarations
with the same standard axiom set and an isolated successful module build.
Repository-wide formal lint passes; the linked norm audit records its current
certificate alongside the isolated module and axiom checks.
