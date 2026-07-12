# Hedenmalm completeness as a static value constraint

- **ID:** `hedenmalm-static-value-constraint`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]` / constraint reformulation
- **Scientific status:** `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean file:** `formal/GaloisForLFunctions/RHTower/XiHedenmalmValueConstraint.lean`

## Statement

Define the pointwise quotient constraint

\[
\mathcal V_\Theta:
\qquad
U_\alpha(\alpha)\ne0
\quad\text{for every Xi divisor point }\alpha,
\]

where

\[
U_\alpha(z)=i\,\operatorname{dslope}(\Xi_C,\alpha)(z)
\]

is the unique regular Fourier-side solution of the Hedenmalm theta equation.
Then

\[
\mathcal V_\Theta
\iff \text{every Xi zero is simple}.
\]

Consequently,

\[
\begin{aligned}
&\text{continued prime--Gamma upper one-Cauchy value inequality}
\\[-2mm]&\qquad+\ \mathcal V_\Theta
\iff RH+\text{simplicity}.
\end{aligned}
\]

The same pair of value constraints is equivalent to existence of a conservative
divisor-supported Hedenmalm metric.

## Formal declarations

- `XiThetaFirstQuotientValueConstraint`;
- `xiThetaFirstQuotientValueConstraint_iff_simple`;
- `continuedPrimeArchFormula_and_thetaValueConstraint_iff_rh_and_simple`;
- `continuedPrimeArch_and_thetaValueConstraint_iff_exists_conservative_metric`.

## Proof

At a divisor point `alpha`, the removable quotient has the exact value

\[
U_\alpha(\alpha)=i\Xi_C'(\alpha).
\]

It is nonzero exactly when the local analytic multiplicity is one.  The Xi divisor enumerates
every zero with its analytic multiplicity, so imposing the value relation at every support point
is exactly global simplicity.

The prime--Gamma upper one-Cauchy value inequality is already equivalent to RH.  Substituting the
local value characterization of simplicity into the existing source-to-Hilbert capstone proves
both displayed equivalences.

## Constraint, not flow

The former interface was

```text
closure(span of theta eigenfunction evaluations) = the full Xi carrier.
```

That statement suggests an approximation or completion process.  The exact condition is instead

```text
for every divisor point alpha, the unique regular quotient has U_alpha(alpha) != 0.
```

The Hilbert closure is a consequence of these fixed local values: each nonzero value supplies the
corresponding coordinate vector.  No density argument needs to be treated as primitive input.

## Top-down consequence

This discharges two interfaces in the Hedenmalm theorem surface:

- eigenfunction completeness is replaced by a pointwise quotient value relation;
- existence of a conservative metric is replaced by the prime--Gamma sign plus the same local
  value relation.

It does not prove either RH or simplicity.  The RH-bearing source inequality remains unchanged,
and the local quotient values retain exact divisor multiplicity.

## Scientific status

The theorem is a direct consequence of the newly formalized multiplicity chain and the existing
source capstone.  It is a valuable formulation change but not independent new scientific
knowledge.

## Gates

- [x] closure/density interface eliminated from the theorem statement
- [x] exact pointwise value constraint
- [x] unconditional Lean proof
- [x] no placeholders or project axioms
- [x] imported by the RHTower umbrella
