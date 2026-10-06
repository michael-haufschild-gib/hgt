# TT C80 — Complete kinetic Bernstein differences

Status: exact complete source identities formalized; coefficient signs and RH OPEN.
Parent: P1:tt-kinetic-contraction-source.

## Exact mathematical result

Let S(h,v,z) be the entire cleared third slope from C79. It is a polynomial
in z of degree at most19, with ALL coefficients a_j(h,v), 0≤j≤19, retained.
For real h,v,Z set

 f_i = sum_(j=0)^19 a_j(h,v)*Z^j*choose(19-j,i-j),

where a summand is zero if j>i. With the unscaled Bernstein basis
b_i^N(e)=e^i*(1-e)^(N-i), the following holds for every real h,v,Z,e:

 S(h,v,eZ)-S(h,v,Z)
   = (1-e)*sum_(i=0)^18 [f_i-choose(19,i)*f_19]*b_i^18(e).

Here S and a_j mean real parts at real arguments. This identity does not
assume source positivity, coefficient positivity, or any clock/drift range.
The natural degree19 bound suffices; no sharp-degree17 theorem is used.

For b=1/12-7h/72, V=9-s*(1-h²*b*s)*h² and Z0=(1-h*b*s)/3, the ENTIRE
cleared source equals h^4*V times the C79 contraction source. Consequently,

 (1-e)*sum_(i=0)^18 [f_i(h,V,Z0)-choose(19,i)*f_19(h,V,Z0)]*b_i^18(e)
   = h^4*V*(1-e)*C(h,s,e).

This is an unconditional identity, including h=0 and V=0. Those zero
factors must not be cancelled without justification. On the positive-clock,
positive-drift interior the weighted sum has exactly the sign of C.

## Dependency-closed proof

1. Split every literal cleared moment by kinetic exponent. Reconstruct
   every moment exactly and derive all35 coefficient normal forms in Lean.
2. The exact clock derivation of z^j*c has only the three adjacent kinetic
   orders j+1,j,j-1, with all clock, drift and kinetic field terms retained.
3. Assemble the full slope using its five determinant cofactors. This gives
   a concrete univariate polynomial over the complete clock/drift ring.
4. Prove its degree bound19 and all twenty coefficient slots. No leading
   coefficient, asymptotic truncation or boundary restriction replaces S.
5. Zero kinetic partial derivatives of the moment coefficients are proved.
   Commutation of mixed partials propagates this to all source blocks.
   Exact evaluation therefore uses coefficients independent of z.
6. Apply the corpus's monomial-to-Bernstein identity to the complete source.
   Binomial partition of unity gives the nineteen full control differences.
7. C79's exact h^4 slope and drift factors identify this full sum with C.

## Audit and limits

All twenty new production leaves passed direct foreground `lake --old env lean`
audits, warning-free, and are wired exactly once. No umbrella build. Final
imported audit covered all244 theorem or proof-derived normal-form declarations;
only propext, Classical.choice, Quot.sound occur. Capstone types checked.
Logs: /tmp/tt_c80_production_axioms.log and /tmp/tt_c80_*_production*.log.
Manifest: /tmp/tt_c80_production_manifest.json.

Formal lint completed with ten unrelated umbrella omissions (listed in the
working log), no C80 defect. Scoped forbidden-declaration and raised-limit
checks, wiring and whitespace checks pass. Thirty-eight superseded owned
scratch sources/caches/generators removed; final audit, successful drift-row
pilot and active C81 drafts retained. No source sampling, external coefficient
arithmetic or raised limits.

No finite-clock inequality was proved by this construction. Positivity of
all nineteen control differences is a candidate sufficient certificate,
not an established theorem. A negative coefficient would not alone refute
source positivity. The whole cofactor normalization attempt exceeded the
default heartbeat limit; it was cancelled, with no limits raised. Exact
second-variable coefficient splitting is the next proof decomposition.

Full source quadratic, fourth Schur gap, compact/adverse-ray join,
all-rank/integrated closure, and RH remain open.
