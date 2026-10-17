# Coherent annular Schur coupling of signed prime–polar transport

For a real compact continuous source f, let h(t)=∫f(u)f(u+t)du and R=h(0).
Fix arbitrary a,b in R, set A=exp(a), d=exp(b), and I=[A,A+d]. Let

g(u)=d⁻¹∫_I f(u-y)dy,     H(t)=d⁻¹∫_I h(t+y)dy.

For the actual signed prime–polar packet P_N already constructed, write

D=∫fP_N,  Q=∫P_N²,  C=H(0),
B=d⁻²∫_I∫_I h(z-y)dzdy,  W=chebyshevWork(f,a,b,N).

All sums in P_N retain Λ(n)/√n and all continuum terms retain 2cosh(t/2).
There is no grid-blindness assumption. The zero source is included, with real
division by zero interpreted as zero.

## The joint constraint

The actual source geometry proves

0≤B≤R,  0≤B-C²/R,  0≤Q-D²/R,

**(W-CD/R)² ≤ (B-C²/R)(Q-D²/R).**

The unprojected coherent transport bound is

**(D-W)² ≤ Q(R+B-2C).**

The joint constraint also gives the unconditional energy certificate

**D²/R + (W-CD/R)²/(B-C²/R) ≤ Q.**

When the collar residual energy is zero, its quotient is zero and the first
constraint forces W=CD/R. For positive residual energy, divide the Schur bound
by B-C²/R and add D²/R. Thus Chebyshev work detects packet energy beyond the
single-source lower bound D²/R.

In particular, the entire collar is represented by one vector. Its energy B
retains correlations between every pair of collar shifts; neither an assumed
orthogonality nor independent per-shift energy expenditure is used. The first
inequality constrains the two actual signed scalar quantities D and W jointly,
using their source-parallel components and the residual packet energy.

## Dependency-closed proof

**Source admission.** Choose M>0 containing the support of f in [-M,M]. If
f(u-y) is nonzero for y in I, then -M≤u≤M+A+d. Thus g has compact support.
Its continuity follows by integration of the continuous integrand on compact I.
For arbitrary compact continuous q, the mixed integrand q(u)f(u-y) has compact
support in R²: support bounds on u and u-y bound y. Fubini and division by d give

∫q(u)g(u)du=d⁻¹∫_I∫q(u)f(u-y)dudy.

All integrals here are absolutely integrable by continuity and compact support.
Changing variable u-y in the inner integral gives

∫g(u)f(u+t)du=H(t).

At t=0 this gives ∫gf=C. Applying mixed Fubini with q=g gives
∫g²=d⁻¹∫_I H(-y)dy=B. Since |h(t)|≤R, integrating twice yields B≤R;
B≥0 follows from its actual squared-source representation.

**Arithmetic covariance.** The previously verified actual mixed packet identity
gives ∫gP_N=D_N(H). The exact finite-window Stieltjes theorem identifies this
with W, including H(0), its upper endpoint, and the negative-exponential polar
shadow. Similarly ∫fP_N=D. No differentiability of f is needed.

**Residual geometry.** For any compact continuous p,q,f let R=∫f²,
c_p=∫pf, c_q=∫qf. Set p⊥=p-(c_p/R)f and q⊥=q-(c_q/R)f. Expanding integrals gives

∫p⊥²=∫p²-c_p²/R,
∫q⊥²=∫q²-c_q²/R,
∫p⊥q⊥=∫pq-c_pc_q/R.

For R≠0 these are elementary fraction identities. For R=0 all fractions are
zero and the same equalities hold directly. Applying integral Cauchy–Schwarz to
these actual compact continuous residuals, with p=g and q=P_N, gives the joint
constraint. Their squared energies also prove residual nonnegativity.
Applying Cauchy–Schwarz to f-g and P_N gives the coherent transport bound,
since ∫(f-g)²=R+B-2C. Thus every analytic premise is discharged by actual sources.

**Global transfer.** At N=N₀(f)+K for any natural K, contribution 3 proves
D=D∞(h) and W=W∞ for the admitted literal half-line pairing and work.
Substitution yields both full-half-line inequalities with the same B and C and
the actual finite packet Q_N. This step does not assert that Q_N stabilizes.

## Scope

This is one contribution: a coherent continuum collar source and its joint
signed arithmetic–Chebyshev Schur constraint. Generic projection algebra is
not claimed as new. The corpus has finite-packet Schur precedents; the current
package connects actual mixed prime–polar packets to the full collar Gram
geometry and the admitted global work without extra analytic hypotheses.
No uniform arithmetic cancellation estimate or external novelty claim is made.

`AnnularCorrelationSource.lean` and `SignedPrimePolarCoherentSchur.lean` both pass
direct `lake --old env lean <leaf> -o <leaf.olean>` without diagnostics. The final
scratch audit exits 0: ten endpoint axiom reports use only propext, Classical.choice,
and Quot.sound, and printed main signatures have no extra premises. Both modules
are wired into the field umbrella. Index refresh passes; global lint flags three
unrelated unwired modules, recorded in the companion facts ledger. This is verified
contribution 4 of the requested 100, with all helper results counted together.
