# Exact residue: a scalar boundary for the three-channel balance

Status: `[BRIDGE]`, derived algebra; no new source inequality and no RH proof. The experiments reject a universal sign for the first two channels separately. They motivate keeping the exact boundary between adverse mixed transport and available curvature. This is an explicit coordinate change of the existing compensation, not a new universal law.

Write the existing affine homotopy as `M'''=−W'''H−3W''H'−3W'H''`, with `W=14+v(10+8R)`, `R=(exp(q)−1)⁻¹`, `v=t a`. Primes on `W,H` here mean homotopy derivatives. At a point where `q>0`, `v>0`, `A=−dq>0`, `B=−H>0`, put

`b=(exp(q)+1)/(exp(q)−1)`, `r=−dv/(v A)`, `s=H'/(B A)`, `h=H''/(B A²)`.

The exact normalized budget is

`M'''/(v B A³) = (b²−1)[12(r−b/2)(s−b/2)−1] + 3h[(6+4b)r−2(b²−1)]`.

Proof: `R_q=−R(R+1)`, `R_qq=(2R+1)R(R+1)`, and `R_qqq=−(6R²+6R+1)R(R+1)`. Substitute `dq=−A`, `dv=−vAr`, `H=−B`, `H'=BAs`, `H''=BA²h` into the existing third-derivative formula and use `b=2R+1`. The first two channels alone become

`(b²−1)[12(r−b/2)(s−b/2)−1]`.

Thus their exact sign boundary is a hyperbola in the shifted `(r,s)` plane, not the sign of either channel separately. Let `L=(6+4b)r−2(b²−1)`; `W'=−v A L`. When `L>0`, full compensation is nonnegative exactly when

`h ≥ hcrit = (b²−1)[1−12(r−b/2)(s−b/2)]/(3L)`.

This gives a sharp positive survivor: the amount of lower-transport curvature sufficient to pay the complete signed mixed contribution is explicit. It can be negative, in which case any nonnegative curvature suffices. A positive `hcrit` requires a quantitative reserve. The experiment's far-region sign failure is therefore not a failure of the complete budget.

Formalization target: connect the scalar third-derivative formula to `C5LikelihoodAffineData.compensationThree`, prove its exact polynomial normalization and shifted-reserve identity unconditionally. Multiplying by one extra denominator factor makes the identities valid also at the degenerate real-field division-by-zero convention. Positivity interpretations above explicitly concern the nondegenerate physical domain. No measured number occurs in these algebraic proofs.

Missing mathematical producer: prove that the literal theta source stays above this exact boundary throughout the structural chamber and homotopy. The existing strict `H''>0` theorem supplies only `h>0`; it does not by itself prove `h≥hcrit` where `hcrit>0`. The numerical implication observed so far must not be substituted for this inequality. The broader CLG chain still also needs its compact/core and global packet/completion inputs.
