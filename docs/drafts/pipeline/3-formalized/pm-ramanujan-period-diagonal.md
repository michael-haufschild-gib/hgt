# Exact complete-period Ramanujan diagonal

- **ID:** pm-ramanujan-period-diagonal
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route PM; `../1-in-progress/pm-paired-cutoff-gram-budget.md`
- **Statement:** Finite multiples inversion diagonalizes the complete-period centered primitive covariance; actual denominator bands retain their signed totient mean.

## Scope

This is an unconditional finite arithmetic identity. It does not bound the
anchored reciprocal energy, establish small-damping admission, or decide RH.

For real coefficients a(q), Q>=1, and a common period P divisible by every
1<=d<=Q, put

`F(N)=sum_(q<=Q) a(q)*Re(P_q(N))-a(1)*N`.

Then

`sum_(N<P) F(N)^2 = P*(M^2+D)`,

`sum_(N<P) (F(N)+M)^2 = P*D`,

where `M=(sum_(q<=Q) a(q)*phi(q)-a(1))/2` and
`D=(sum_(q<=Q) gcdPowKernel(2,q)*a(q)^2-a(1)^2)/12`.

The literal actual band `X<q<=Y`, X>=1, has a(1)=0. Its complete-period
energy is therefore the squared signed totient mean plus the exact
coefficient-square diagonal, times P. Both terms remain in the theorem.

## Dependency-closed paper proof

Define `b(d)=d*sum_(m<=Q/d) mu(m)*a(d*m)`. For positive e<=Q,

`sum_(d<=Q,e|d) b(d)/d = a(e)`.

To prove this, write d=e*r, interchange the finite hyperbola r*m<=Q/e,
and use `sum_(m|n)mu(m)=1_(n=1)`. No infinite exchange occurs.

The corpus floor formula gives `F(N)=-sum_(d<=Q)b(d)*(N mod d)/d`:
the linear term cancels by the e=1 inversion coordinate. The residue
period mean is `(sum b(d)-sum b(d)/d)/2`. Hyperbola interchange and
the totient divisor identity give `sum b(d)=sum a(q)*phi(q)`, hence M.

The exact centered-residue covariance has kernel
`(gcd(d,e)^2-1)/(12*d*e)`. Its gcd-square part factors as

`sum_q gcdPowKernel(2,q)*(sum_(q|d)b(d)/d)^2`.

Multiples inversion makes this the asserted diagonal. The constant part
is `(sum b(d)/d)^2=a(1)^2`. The existing full-period mean/variance identity
then proves both displayed second-moment laws. The actual coefficients
and primitives are real, so their real squares equal complex norm squares.

## Lean certificate

Module: `GaloisForLFunctions.RHTower.PMRamanujanPeriodDiagonal`.

- `pmRamanujanResidueCoeff_multiples`
- `pmRamanujanResidueCoeff_gcd_diagonal`
- `pmRamanujanResidueCoeff_periodCovariance`
- `pmRamanujan_sum_primitive_eq_residue`
- `pmRamanujanResidueCoeff_periodMean`
- `pmRamanujan_complete_period_square`
- `pmRamanujan_complete_period_centered_square`
- `pmRamanujanDenominatorBand_period_square`

Ten public declarations, including the two definitions, passed standard-axiom
audit: propext, Classical.choice, Quot.sound only. Targeted `lake --old build`
passed; only the new leaf built. Umbrella import is present. Final direct-file
audit (`lake env lean GaloisForLFunctions/RHTower/PMRamanujanPeriodDiagonal.lean`)
exited 0 without diagnostics. No umbrella build was run. Global formal lint
reports fourteen unrelated unwired leaves, listed on the active card; no
error names this leaf.

## Remaining hard PM problem

The physical measure gives residue r its infinite progression weight,
not weight 1/P. The desired natural-band upper bound must control the full
signed covariance under those actual weights. Centering by the reciprocal
Mangoldt mean avoids imposing a separate totient-mean bound; it does not
prove the needed variance comparison. The active card records that precise
conjecture and the failed absolute-weight and fixed-cofactor inferences.
