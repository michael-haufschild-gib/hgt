# Route P primitive Gamma--Julia signed bivariate stability

- **ID:** `route-p-primitive-gamma-julia-signed-bivariate-stability`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM] [P-G105G]`
- **Parent:** `route-p-joint-depth-gamma-julia-log-krein-matrix-completion.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaSignedBivariateStability.lean`

## Goal

Determine whether P-G105F full prime-log Julia--Krein completion admits a finite stable pencil
without erasing negative channel orientation or off-diagonal arithmetic incidence.

## Conjecturing loop

### Conjecture 1 — one scalar spectral variable should retain Route-P stability

**Rejected structurally.** One variable weights child and negative pivot identically, forgetting
which channel carries Krein orientation. The universal `2 × 2` block has one positive and one
negative direction; a scalar collapse cannot encode signed polarization.

### Conjecture 2 — separate channel variables destroy full off-diagonal incidence

**Falsified.** Define

```text
D(z,w)=diag(z,w),
P_H(z,w)=I+((D(z,w)B) tensor H),
H=LGL.
```

This is exactly

```text
I + (D(z,w) tensor I) (B tensor H),
```

so it acts on P-G105F completed matrix and retains every entry of `H` in original basis.

### Conjecture 3 — negative pivot forces a zero in upper-half-plane product chamber

**Falsified; sign is precisely stabilizing.** For every nonnegative eigenvalue `lambda` of `H`,
the factor is

```text
q_lambda(z,w)=1+lambda z/64-lambda w-lambda^2 z w.
```

If `lambda>0` and `q_lambda=0`, then

```text
w=(1+lambda z/64)/(lambda(1+lambda z)).
```

This real Möbius map has orientation determinant `-63 lambda^2/64`, hence sends upper half-plane
strictly to lower half-plane. For `lambda=0`, factor is `1`. Thus every factor and their full
finite product are upper-half-plane stable.

## Paper proof

P-G186 window Gram `G` is positive semidefinite. Prime-log diagonal `L` is Hermitian, so
`H=LGL=LᴴGL` is positive semidefinite. Unitary diagonalization gives eigenvalues
`lambda_i≥0`. Conjugating only for proof turns full pencil into block diagonal form and yields

```text
det P_H(z,w)=product_i q_{lambda_i}(z,w).
```

For positive `lambda`, direct imaginary-part calculation gives

```text
Im ((1+lambda z/64)/(lambda(1+lambda z)))
  = -(63/64) lambda^2 Im(z) / |lambda(1+lambda z)|^2 < 0.
```

Therefore it cannot equal `w` with `Im(w)>0`. Zero eigenvalues contribute unit factors. Every
factor is nonzero, hence product is nonzero. `QED`

## Novelty and anti-theatre audit

Determinantal stability from positive spectra is classical in broad form. Route-specific new
knowledge is exact stable polarization of corpus's literal P-G105F completion: coefficient
`1/64`, Julia defect `63/64`, negative pivot, prime-log congruence, and full P-G186 incidence all
survive in one closed pencil. No injectivity, strict positive definiteness, or finite
nondegeneracy is required.

This changes architecture materially. Negative Krein index is not finite stability obstruction;
after retaining channel polarization it becomes orientation-reversing Möbius mechanism that proves
stability. Prior scalar failures were shadows of erasing channel chirality.

Physical Stokes provenance is not claimed. Variables `z,w` are canonical child/pivot channel
coordinates, but corpus has not yet proved they equal a source-derived Stokes current. No cofinal
limit, Xi divisor identity, signed-permutation coefficient extraction, or RH claim is made.

## Formal status

Lean proves unconditionally:

- exact one-eigenchannel determinant factor;
- strict upper-to-lower Möbius image theorem;
- factor stability for every nonnegative eigenvalue;
- exact left-action identity on full P-G105F completed matrix;
- spectral product formula for arbitrary finite Hermitian `H`;
- positive semidefiniteness of actual prime-log-conjugated P-G186 Gram;
- actual finite determinant factorization and upper-half-plane stability for every packet;
- premise-free family capstone quantifying all upper-half-plane pairs.

Direct Lean and target-only module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Forbidden scan and `git diff --check` pass. Module is wired;
no umbrella build was run.

## Refined open core

Identify signed channel diagonal with literal source-derived Gamma/co-Poisson/Stokes current, then
prove cofinal convergence on the two-variable product chamber while retaining divisor information.
Finite algebra and finite stability are closed; physical orientation and infinite Xi landing are
not.

## Higher universal principle

A one-negative-index completion carries a projective orientation, not merely an indefinite norm.
When positive and negative channels receive independent variables, negative determinant becomes an
anti-Pick transfer: upper half-plane is sent to lower half-plane, forcing multivariate stability.
Scalarization destroys this projective sign and manufactures the apparent obstruction.

## Log

- 2026-08-16 — P-G105G full finite signed bivariate stability paper-proved and formalized.
