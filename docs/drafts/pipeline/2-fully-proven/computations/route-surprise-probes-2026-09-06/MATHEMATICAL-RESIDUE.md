# Exact residue: a scalar boundary for the three-channel balance

Status: `[BRIDGE]`, derived algebra, formalized in `formal/GaloisForLFunctions/RHTower/ThetaCuspC5BoseHyperbolicReserve.lean`; no new source inequality and no RH proof. The experiments reject a universal sign for the first two channels separately. They motivate keeping the exact boundary between adverse mixed transport and available curvature. This is an explicit coordinate change of the existing compensation, not a new universal law.

Write the existing affine homotopy as `M'''=−W'''H−3W''H'−3W'H''`, with `W=14+v(10+8R)`, `R=(exp(q)−1)⁻¹`, `v=t a`. Primes on `W,H` here mean homotopy derivatives. At a point where `q>0`, `v>0`, `A=−dq>0`, `B=−H>0`, put

`b=(exp(q)+1)/(exp(q)−1)`, `r=−dv/(v A)`, `s=H'/(B A)`, `h=H''/(B A²)`.

The exact normalized budget is

`M'''/(v B A³) = (b²−1)[12(r−b/2)(s−b/2)−1] + 3h[(6+4b)r−2(b²−1)]`.

Proof: `R_q=−R(R+1)`, `R_qq=(2R+1)R(R+1)`, and `R_qqq=−(6R²+6R+1)R(R+1)`. Substitute `dq=−A`, `dv=−vAr`, `H=−B`, `H'=BAs`, `H''=BA²h` into the existing third-derivative formula and use `b=2R+1`. The first two channels alone become

`(b²−1)[12(r−b/2)(s−b/2)−1]`.

Thus their exact sign boundary is a hyperbola in the shifted `(r,s)` plane, not the sign of either channel separately. Let `L=(6+4b)r−2(b²−1)`; `W'=−v A L`. When `L>0`, full compensation is nonnegative exactly when

`h ≥ hcrit = (b²−1)[1−12(r−b/2)(s−b/2)]/(3L)`.

This gives a sharp positive survivor: the amount of lower-transport curvature sufficient to pay the complete signed mixed contribution is explicit. It can be negative, in which case any nonnegative curvature suffices. A positive `hcrit` requires a quantitative reserve. The experiment's far-region sign failure is therefore not a failure of the complete budget.

Formalized exactly: incidence with `C5LikelihoodAffineData.compensationThree`, polynomial normalization, the hyperbolic coordinate identity, and the shifted-reserve identity. All four theorems are unconditional. Multiplying by one extra denominator factor makes the identities valid also at the degenerate real-field division-by-zero convention. Positivity interpretations above explicitly concern the nondegenerate physical domain. No measured number occurs in these algebraic proofs. Scratch and source `lake env lean` checks and the named leaf build pass. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; no added axioms or proof placeholders.

Missing mathematical producer: prove that the literal theta source stays above this exact boundary throughout the structural chamber and homotopy. The existing strict `H''>0` theorem supplies only `h>0`; it does not by itself prove `h≥hcrit` where `hcrit>0`. The numerical implication observed so far must not be substituted for this inequality. The broader CLG chain still also needs its compact/core and global packet/completion inputs.

## Retaining the mixed coordinate

Set `κ=s-r+h/(2r)` and `Q=(6+4b)r²-4(b²-1)r+b(b²-1)`. For `r≠0`, the same budget becomes

`F=(b²-1)[12(r-b/2)(r+κ-b/2)-1]+3h Q/r`.

The coefficient has the exact square decomposition

`(6+4b)Q=[(6+4b)r-2(b²-1)]²+(b²-1)(6b+4)`.

Consequently increasing `h` strictly increases `F` when `b>1,r>0` and `b,r,κ` are fixed. Actual source deformation may change those coordinates; no source monotonicity is asserted. The exact division-free identity retains the residual `2r(s-r-κ)+h` before any substitution, and the cleared specialization stays valid at `r=0`.

Four additional Lean theorems prove the square decomposition, incidence identity, cleared specialization, and unconditional nonnegativity of `Q(1+x²,r)`. The paired boundary experiments and their limitations are in [boundary-followup/REPORT.md](boundary-followup/REPORT.md). They suggest distinct compensation regimes but do not prove that the actual source occupies only favorable regimes.
