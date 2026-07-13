# Prime-Adams pure-weight local jet to RH

- **ID:** `prime-adams-pure-weight-local-jet-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[LARGE OUTLANDISH DETOUR]`
- **Lean bridge:** `formal/GaloisForLFunctions/RHTower/LocalDivisorJetAdamsDilation.lean`
- **Calibration:** `BoundaryModulus.lean`, `FunctionFieldFE.lean`

## Claim

The actual `n`-th Adams operation on the Euler germ acts on an order-`m` local analytic jet by
dilation.  In its monomial directions its eigenvalues are

```text
lambda_j = n^j,  0 <= j < m.
```

If the completed prime--Gamma source realizes this local Adams module as one pure-weight object,
all `lambda_j` must lie on one weight circle.  The constant and first cotangent directions then give
`1=n`, impossible for `n>=2` unless the first cotangent direction is absent.  Hence `m=1`.

This is the local mixed-weight obstruction: a nonreduced zero produces weights
`0,1,...,m-1`; local purity is equivalent to reducedness for a genuine dilation.

## Two-ended chain

```text
completed marked Euler--Gamma object with Adams operations
  -> localize its source-defined Adams module at a hypothetical Xi divisor point
       [OPEN CORE A: local comparison, without enumerating target multiplicity]
  -> identify the local spectrum with 1,n,...,n^(m-1)
       [PROVED LEAN on the actual prime derivative jets]
  -> prove the localized module is pure of one source weight
       [OPEN CORE B: prime--Gamma polarization / purity]
  -> all eigenvalues have one common norm
  -> m = 1
       [PROVED LEAN: adamsDilation_sameWeight_forces_simple]
  + independently source RHLadder 1
  -> every hypothetical right-half order is both one and even
  -> RH
       [PROVED LEAN CONDITIONAL CAPSTONE:
        riemannHypothesis_of_rhLadder_one_of_rightAdamsDilationPure].
```

## Determinant residue and its limit

The exact diagonal determinant is

```text
det(Psi^n | A_m) = n^(m(m-1)/2),
```

formalized as `adamsDilationDeterminant_eq`.  It is a multiplicity character, but a centered
functional-equation normalization divides the weights symmetrically and makes the determinant one
for every `m`.  Therefore determinant-one after centering is not a simplicity theorem.  Purity must
control every eigenvalue, not merely their product.

## Candidate source providers

1. a prime--Gamma cohomology in which the localized Adams action is polarized and pure, analogous
   to normalized Frobenius on a pure function-field cohomology;
2. a KMS/GNS realization whose modular normalization makes the local Adams action unitary on the
   actual divisor cohomology;
3. a weight-filtration comparison proving that all positive cotangent weights cancel in the
   completed source localization.

The function-field analogy is only a calibration: `FunctionFieldFE.lean` explicitly separates FE
duality from the further purity theorem.  Importing purity by analogy would assume the hard core.

## Firewalls

1. Defining the eigenbasis from the already-known Xi multiplicity is consumer algebra only.
2. FE reciprocity pairs weights but does not put them on one circle; symmetry is not purity.
3. Determinant one after centered normalization is automatic and multiplicity-blind.
4. Satake-side second-moment positivity does not automatically transfer to the zero-side local
   module; that comparison must be proved.
5. A divisor-supported positive metric assembled from the Xi zeros is target-fed.
6. The source theorem must act on the actual local divisor cohomology, not an auxiliary pure module.

## Status

- `[PROVED LEAN]` exact source-correct prime-power coefficient/dilation law;
- `[PROVED LEAN]` determinant `n^(m(m-1)/2)`;
- `[PROVED LEAN]` one common Adams weight forces `m=1`;
- `[PROVED LEAN]` pure local Adams plus `RHLadder 1` implies RH;
- `[PROVED NO-GO]` reversibility and centered determinant one do not see multiplicity;
- `[OPEN CORE]` source-derived local comparison and purity;
- `[OPEN]` independent first ladder rung.
