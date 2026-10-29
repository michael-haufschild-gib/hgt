# Primitive arithmetic curvature and its conductor-uniform floor

Status: all three modules are formalized, individually checked, and wired. No integral-symbol or complete-operator identity is claimed.

## Exact finite objects

For `m>1`, let

```
P_m(k) = sum_(zeta primitive of order m) |sum_(0<=j<k) zeta^j|^2,
A_m(t) = sum_(d|m) mu(m/d)*d^2*fract(t/d)*(1-fract(t/d)).
```

Finite root orthogonality and Möbius inversion prove

```
P_m(k) = sum_(d|m) mu(m/d)*(k mod d)*(d-(k mod d)),
A_m(k+u) = (1-u)*P_m(k)+u*P_m(k+1)  (0<=u<1).
```

The constant mode and quadratic cell coefficient cancel for nontrivial conductors. Prefix energy is zero exactly when `m` divides `k`.

## Norm quantum

When `m` does not divide `k`, the geometric prefix is a nonzero cyclotomic integer. Its norm has nonzero integral absolute value at least one. Its embeddings are exactly the primitive roots. The arithmetic–geometric mean of their squared magnitudes gives

```
phi(m) <= P_m(k).
```

Consecutive integers cannot both be conductor multiples. Interpolation therefore gives the simultaneous real bound

```
fract(t)*(1-fract(t)) <= A_m(t)/phi(m)  (m>1, t>=0).
```

## Formalized declarations

- `PrimitiveRootPrefixEnergyIsAMobiusQuadraticRemainder.lean`: `primitiveRootPrefixEnergy_eq_moebius_remainder`, `primitiveRootPrefixEnergy_eq_zero_iff`, `arithmeticOverlapCurvature_eq_interpolation`, and the unnormalized real floor. Needed check53212 and final check7845 passed.
- `CyclotomicNormGivesAConductorUniformCurvatureFloor.lean`: `one_le_prod_primitive_prefix_norm`, `totient_le_primitiveRootPrefixEnergy`, and `fract_quadratic_le_normalized_arithmeticOverlapCurvature`. Final check22113 passed.

All printed capstone dependencies are `propext`, `Classical.choice`, and `Quot.sound` only. Both modules are imported by the programme umbrella. No full or umbrella build was run.

## Exact logarithmic divisor jet

`TheDownwardPrimeRowIsAnExactLogarithmicDivisorJet.lean` proves the literal identity

```
sum_(a|n) Lambda(a)*c_m(n/a)
  = log(n)*c_m(n)-sum_(d|m,d|n) mu(m/d)*d*log(d).
```

At `n=m`, the existing completed prime-row theorem identifies the last sum with `phi(m)*(log(m)+tameDifferent(m))`. Final individual check38873 passed clean; all three capstone dependencies are the same standard axioms listed above. The module is wired into the umbrella. The surrounding corpus already bounds the downward correction uniformly; that boundedness is not a new result.

## Boundary

These are finite arithmetic identities and inequalities. They neither identify the full overlapping Weil operator with a proposed symbol nor prove its positivity or exhaustion. Previously proposed integral representations, symbol matching, Fourier descriptions, and larger-overlap transfers are unproved conjectural extensions; implementation is deferred under [the existing successor backlog](../0-backlog/cact-successor-correction-beyond-touching.md). They are not completed paper proofs awaiting formalization.
