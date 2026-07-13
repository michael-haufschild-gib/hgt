# First-divided-source numerical-sector criterion for RH

- **ID:** `first-divided-source-numerical-sector-rh`
- **Stage:** 3-formalized
- **Type:** TOP-DOWN STATIC SOURCE-VALUE CRITERION
- **Scientific status:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean module:** `formal/GaloisForLFunctions/RHTower/XiFirstDividedSourceNumericalSector.lean`

## Statement

For an Xi divisor support point `rho`, write

\[
\alpha_\rho=(\rho-\tfrac12)(-i),
\qquad
Q_\rho=\operatorname{xiThetaDividedChain}(\alpha_\rho,1).
\]

Let `J` be a complex-linear map from entire source functions into a complex Hilbert space. Lean
proves

\[
\begin{aligned}
J(\Xi_C)=0
&\Longrightarrow
J(M_zQ_\rho)=\alpha_\rho J(Q_\rho),\\
J(Q_\rho)\ne0
&\Longrightarrow
\operatorname{Im}\langle JQ_\rho,J(M_zQ_\rho)\rangle
=\operatorname{Im}(\alpha_\rho)\,\|JQ_\rho\|^2.
\end{aligned}
\]

Consequently,

\[
\left.
\begin{array}{l}
J(\Xi_C)=0,\\
J(Q_\rho)\ne0\quad\text{for every Xi divisor support point }\rho,\\
\operatorname{Im}\langle JQ_\rho,J(M_zQ_\rho)\rangle\ge0
\quad\text{for every }\rho
\end{array}
\right\}
\Longrightarrow RH.
\]

Functional-equation reflection replaces `alpha_rho` by `-alpha_rho`. Applying the same one-sided
constraint on both reflected fibers forces `Im(alpha_rho)=0` because both retained norm squares are
strictly positive.

The formal chain is

```text
Xi source annihilation
  -> exact first-divided-source coordinate eigenrelation

fiberwise first-divided-source faithfulness
  + upper numerical sector on every reflected fiber
  -> Im(centered Xi coordinate) = 0 at every divisor support point
  -> RH.
```

## Strict improvement over the evaluated-mode criterion

The previous Hedenmalm numerical-sector endpoint used the evaluated theta mode. At a multiple Xi
zero that vector vanishes, so the numerical value is zero and a separate local-normality or
simplicity input is required.

The present criterion uses the full first divided source before point evaluation. Its faithfulness
hypothesis is meaningful at every support point, including multiple zeros. The RH implication needs
neither a simplicity hypothesis nor local Jordan normality.

It also removes the global operator symmetry used by the earlier symmetric-source-quotient theorem.
Only one static scalar value per existing divisor fiber is constrained.

## Canonical two-point discharge

The quotient and faithfulness inputs can be removed. For any two distinct regular source points
`u,v`, define

\[
J_{u,v}(F)=\Xi_C(v)F(u)-\Xi_C(u)F(v).
\]

This construction contains no chosen divisor point. Lean proves unconditionally

\[
J_{u,v}(\Xi_C)=0
\]

and, at every divisor support point,

\[
J_{u,v}(Q_\rho)=
\frac{\Xi_C(u)\Xi_C(v)(v-u)}
{(u-\alpha_\rho)(v-\alpha_\rho)}\ne0.
\]

The module fixes `u=-i` and `v=-2i`. Both correspond to points in the absolutely convergent
prime-source half-plane, and their regularity and distinctness are proved. Therefore the fully
discharged chain is

```text
upper numerical sector for the fixed (-i,-2i) two-point quotient
  -> RH.
```

No quotient existence, zero enumeration, fiber choice, simplicity, or operator realization remains.

## Anti-redressing attack

The algebraic recurrence is unconditional and has no sign content. Source annihilation alone simply
makes coordinate multiplication diagonal on the retained first divided fibers; it allows nonreal
eigenvalues.

For the canonical two-point quotient, however, the residual upper-sector premise is still an exact
orientation test on actual divisor fibers. By the proved value formula, it says

\[
\operatorname{Im}(\alpha_\rho)\,
\left|\frac{\Xi_C(-i)\Xi_C(-2i)(-i)}
{(-i-\alpha_\rho)(-2i-\alpha_\rho)}\right|^2\ge0
\]

for every reflected fiber. The rational weight is strictly positive, so this remaining condition
cannot itself be advertised as an independent source theorem: after reflection it is precisely the
zero-orientation content of RH. The gain is interface discharge and a fixed value target, not a
proof of its sign.

## Open core

`[OPEN CORE]` Prove the fixed two-point inequality

\[
\operatorname{Im}\langle J_{-i,-2i}Q_\rho,
  J_{-i,-2i}(M_zQ_\rho)\rangle\ge0
\]

from a stronger source-side finite or cofinal theorem which is formulated before the Xi divisor is
inserted. It must not assume a self-adjoint multiplication operator, zero location, real-rootedness,
or a limiting positive form equivalent to RH.

The nearby explicit two-pole CCM source energy already identifies Cauchy-packet Weil squares with
four continued prime--Gamma divided differences. The research question is whether the fixed
`(-i,-2i)` packet admits a coefficient-level localization theorem strong enough to control each
reflected divisor-fiber orientation, rather than only its globally summed energy. Without such a
localization, the capstone remains a redressing and the route stops here.

## Formal verification

Lean proves:

- `xiFirstDividedSource_coordinate_eq_smul`;
- `xiFirstDividedSourceNumericalValue_im_eq`;
- `xiSpectralPointSupport_im_eq_zero_of_firstDividedSourceUpperSector`;
- `riemannHypothesis_of_firstDividedSourceUpperNumericalSector`;
- `xiTwoPointSourceQuotient_XiC`;
- `xiTwoPointSourceQuotient_firstDivided_eq`;
- `xiTwoPointSourceQuotient_firstDivided_ne_zero`;
- `riemannHypothesis_of_twoPointFirstDividedSourceUpperNumericalSector`;
- `riemannHypothesis_of_canonicalTwoPointFirstDividedSourceUpperNumericalSector`.

The module contains no new axiom or admitted proof.
