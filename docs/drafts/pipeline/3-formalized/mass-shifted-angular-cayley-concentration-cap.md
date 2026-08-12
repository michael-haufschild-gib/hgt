# Mass-shifted angular Cayley concentration cap

- **ID:** `mass-shifted-angular-cayley-concentration-cap`
- **Stage:** 3-formalized
- **Type:** unconditional integral theorem / exact Cayley transfer
- **Lean module:**
  `GaloisForLFunctions.RHTower.AngularPolynomialConcentrationCap`
- **Depends on:** `mass-shifted-projective-outlier-angular-energy`

## Result

For `q(theta)=Q(cos(theta))`, define full angular mass `M`, derivative energy `E`, and symmetric
arc mass `M_delta`. If `B>0` and

```text
E <= B^2 M,
```

then genuine integral Sobolev and AM--GM give

```text
q(theta)^2 <= (1/(2*pi)+2*B) M,
M_delta <= 2*delta*(1/(2*pi)+2*B) M.
```

For the squared physical Cayley half-density packet

```text
rho(a,Q,x) = a^2/(a^2+x^2) * Q(cos(2*arctan(x/a)))^2,
```

Lean proves the exact finite-window Jacobian

```text
integral[-R,R] rho = (a/2) M_(2*arctan(R/a)).
```

Thus an angular bandwidth bound transfers without approximation to a physical-window mass cap.
On `n asymp a`, any constrained-root estimate `E <= C*n*(k+1)*M` with `k=o(n)` makes every fixed
physical-window mass vanish, contradicting completed-source tightness.

## Proof

1. Apply corpus theorem `RHTower.sobolev_pointwise` to the complexification of `q` on one full
   period.
2. Bound the cross integral using `2|q q'| <= B q^2 + B^-1 (q')^2`.
3. Integrate the resulting pointwise cap over `[-delta,delta]`.
4. Differentiate `phi_a(x)=2 arctan(x/a)` exactly.
5. Apply actual interval change of variables; the Cayley half-density factor is exactly
   `(a/2) phi_a'(x)`.

## Conjecture / failure / pivot audit

- Inferring concentration failure from degree alone gives only critical `B=O(a)` and no
  contradiction.
- Root-spread outlier counting supplies `k=o(n)` but not the energy estimate by itself.
- Affinely moving an interior root cluster outside a unit disk changes the arcsine weight; treating
  that transfer as automatic is invalid.
- Surviving target is exactly one original-measure constrained-zero estimate. Once supplied, this
  module completes all Sobolev and physical Cayley transfer work.

## Lean capstones

- `RHTower.angularPolynomialEval_sq_le_of_energy`
- `RHTower.angularPolynomialArcMass_le_of_energy`
- `RHTower.hasDerivAt_cayleyAngularCoordinate`
- `RHTower.integral_cayleyHalfDensityPolynomialSq_eq_arcMass`
- `RHTower.integral_cayleyHalfDensityPolynomialSq_le_of_energy`

## Status

Direct module verification passes. Axiom and targeted-build audit pending final module audit. RH is
not claimed.
