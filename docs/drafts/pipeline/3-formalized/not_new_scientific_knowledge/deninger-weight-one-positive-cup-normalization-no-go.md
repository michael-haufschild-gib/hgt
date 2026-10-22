# Deninger weight-one positive cup normalization no-go

- **ID:** `deninger-weight-one-positive-cup-normalization-no-go`
- **Stage:** 3-formalized
- **Type:** STANDARD TWO-DIMENSIONAL CLASSIFICATION; ROUTE-L UNIQUENESS NO-GO
- **Label:** `DAC_WEIGHT_ONE_POSITIVE_CUP_NORMALIZATION_NO_GO`
- **Route:** L
- **Parent:** `deninger-arithmetic-calderon-paugam-hardy-comparison`

## Claim

Weight-one flow covariance, nondegeneracy, and positive odd Hodge do not uniquely determine the
middle cup pairing, even on one complementary two-eigenvalue block.

For (lambda\in\mathbf C), put

\[
 \Theta_\lambda(x_+,x_-)
 =\bigl(\lambda x_+,(1-\lambda)x_-\bigr).                    \tag{1}
\]

For every (c>0), define

\[
 \Psi_c(x,y)=c(x_+y_- - x_-y_+),                             \tag{2}
\]

and the anti-linear odd Hodge operator

\[
 J(x_+,x_-)=(-\overline{x_-},\overline{x_+}).                \tag{3}
\]

Then:

1. (Psi_c) is complex-bilinear, alternating, and nondegenerate;
2. it has exact weight one:
   \[
   \Psi_c(\Theta_\lambda x,y)+\Psi_c(x,\Theta_\lambda y)=\Psi_c(x,y); \tag{4}
   \]
3. (J^2=-1);
4. cup followed by (J) is positive:
   \[
   \Psi_c(x,Jx)=c(|x_+|^2+|x_-|^2)>0\quad(x\ne0);            \tag{5}
   \]
5. if (c\ne d), then (Psi_c\ne\Psi_d), already on
   (((1,0),(0,1))).

Hence the listed formal Hodge/Poincaré axioms leave a positive scale undetermined on every
complementary block. With several blocks, absent extra source locality/trace constraints, scales
can vary blockwise.

## Proof

Alternation follows by swapping the two determinant rows. If (x\ne0), pairing against
((0,1)) detects (x_+), while pairing against ((1,0)) detects (-x_-), so `(2)` is
nondegenerate for (c\ne0). Expanding `(4)`, the coefficient of (x_+y_-) is
(lambda+(1-lambda)=1), and the coefficient of (x_-y_+) is the same. Formula `(3)` squares to
(-1), and direct substitution gives `(5)`. Finally
(Psi_c((1,0),(0,1))=c).

## Route-L consequence

The following data do not prove the Green--Paugam comparison:

- alternating cup;
- Poincaré nondegeneracy;
- weight-one flow derivation law;
- odd (K_{\mathbf R}) operator;
- positive cup--Hodge diagonal.

They characterize a family, not Paugam's specific trace normalization. Route L still needs the
source theorem

\[
 \Psi_{\mathrm{Green}}=\psi_{\mathrm{Paugam}}
\]

on a source-dense nuclear core, with hereditary passage through the actual arithmetic quotient.
Prime-orbit coefficients, Arakelov trace, or an equivalent local Lefschetz normalization must fix
the block scales before spectral decomposition. Naming an arbitrary member of `(2)` “the source
cup” is theatre.

## Positive survivor

The ambiguity is exactly normalization, not existence. A source Green--Stokes computation on one
canonical generator per locally defined block, plus a theorem that those blocks generate the
nuclear cohomology and that the trace is hereditary, would fix all (c)'s. This is the correct
target for clause 6 of `DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`.

## Hostile and novelty audit

- This is elementary symplectic linear algebra and is not claimed as new scientific knowledge.
- No Xi-zero indexing defines `(1)`--`(3)`; (lambda) is arbitrary.
- Positivity is proved for every (c>0), so the counterexample survives adding positivity.
- The result does not deny a source normalization theorem; it proves that formal covariance cannot
  replace one.

## Lean formalization

Module:
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerWeightOnePositiveCupNormalizationNoGo.lean`.

Kernel-checked declarations formalize the complementary plane, flow generator, scaled cup, and
odd Hodge operator, followed by:

- additivity and complex homogeneity in both cup variables;
- `deningerComplementaryCup_self` and
  `deningerComplementaryCup_left_nondegenerate`;
- `deningerComplementaryCup_weight_one`;
- `deningerComplementaryHodge_sq`;
- exact cup--Hodge energy and strict positivity;
- `deningerComplementaryCup_distinct_scale` on the two coordinate generators.

All declarations are unconditional and use no Xi divisor or RH premise.
