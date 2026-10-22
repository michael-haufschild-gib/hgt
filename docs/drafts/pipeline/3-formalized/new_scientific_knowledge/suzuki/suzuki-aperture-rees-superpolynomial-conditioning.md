# Suzuki prime-cutoff aperture forces superpolynomial reflected-sewing conditioning

- **ID:** `suzuki-aperture-rees-superpolynomial-conditioning`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper; unconditional Lean source checked)
- **Parents:** `riemann-source-modular-superselection`,
  `prime-valuation-hellinger-rees-reflection-fracture`,
  `suzuki-one-sided-carleman-exterior-seam`
- **RH used:** no
- **Computation used:** no
- **Claimed novelty:** source-specific quantitative synthesis; external priority unverified

## Exact scope

Suzuki's operator on `[-a,a]` sees arithmetic translations `log n` precisely for
`n <= exp(2a)`.  For integer cutoff `X`, define its matching physical aperture

```text
a_X = (1/2) log(X+1).                                   (1)
```

Fix `0<c<1/2`.  Let

```text
H_c(N) = primeValuationSquaredHellingerBelow(c,N),
b_N    = product_(p<N) (1-p^(-1)).
```

Suppose bounded real-linear maps `R_N : R -> R` sew the actual reflected scalar sectors exactly:

```text
R_N(H_c(N)) = H_(-c)(N)                                 (2)
```

for every `N`.  Then for every fixed `K>=0`,

```text
a_X^K = o(||R_(X+1)||),                                 (3)
```

and in particular

```text
||R_(X+1)|| is not O(a_X^K).                            (4)
```

Thus no polynomially conditioned exact reflected-valuation sewing can act at Suzuki's physical
prime aperture.  Every bounded map at a finite cutoff is allowed; obstruction concerns conditioning
of cofinal family.

This theorem does **not** exclude singular or relation-valued sewing, non-scalar breadth, a
source-selected channel retained before reflection-invariant scalar fusion, or surviving
two-angle meromorphic Livsic/Hermite--Biehler route.

## Paper proof `[PROVED HERE]`

Mathlib's harmonic lower bound and finite Euler-product domination give

```text
log(X+1)
 <= sum_(1<=m<=X) 1/m
 <= product_(p<X+1) (1-p^(-1))^(-1)
  = b_(X+1)^(-1).                                      (5)
```

Since `log(X+1)>=0`, equations `(1)` and `(5)` imply

```text
0 <= a_X <= b_(X+1)^(-1).                              (6)
```

Taking `K`-th powers yields

```text
a_X^K = O(b_(X+1)^(-K)).                               (7)
```

The reflected Hellinger--Rees fracture theorem, applied to `(2)`, states unconditionally that

```text
b_N^(-K) = o(||R_N||)                                  (8)
```

for every `K`.  Compose `(8)` with cofinal shift `N=X+1`, then compose with `(7)`, proving `(3)`.

If `(4)` failed, `(3)` and transitivity would give `a_X^K=o(a_X^K)`.  But `a_X>0` for every
`X>=1`, contradicting irreflexivity of little-oh on an eventually nonzero germ.  This proves
`(4)`.

## Frontier impact

Updated modular-superselection theorem says finite-Rees reflected scalar sewing is impossible but
does not translate its intrinsic Wold scale into Suzuki's physical aperture.  Suzuki's source
formula supplies missing bridge `n<=exp(2a)`.  Result upgrades qualitative "beyond every Rees
order" into operational source constraint:

```text
exact scalar reflected sewing
  => condition number grows faster than every power of aperture.  (9)
```

Consequences for Route G:

1. polynomially stable finite-aperture source reconstruction cannot implement scalar reflected
   sewing;
2. boundedness of each finite-cutoff inverse is irrelevant without superpolynomial condition
   control;
3. any surviving exact construction must use at least one escape named in exact scope above;
4. theorem narrows Route G but does not close it.

## Novelty audit

Classical ingredients are not novel: harmonic lower bound, finite Euler product, Mertens scale,
and little-oh transitivity.  Reflected Hellinger--Rees fracture is prior internal work.

Targeted searches of Suzuki canonical-system/screw-function papers and arXiv for combinations of
Suzuki aperture, reflected Hellinger sewing, Wold/Rees scale, and operator conditioning found no
statement equivalent to `(3)` or `(4)`.  Suzuki 2026 gives exact cutoff `n<=exp(2a)` but no
reflected-valuation sewing cost.  Suzuki 2012 studies innerness/canonical systems but no
prime-aperture conditioning theorem.

Honest status: new dependency-closed synthesis relative to source and corpus; external priority
remains unverified.  No claim that generic Euler-product growth or generic Hellinger singularity
is new.

## Lean

Module:

```text
GaloisForLFunctions.RHTower.Suzuki.SuzukiApertureReesConditioningNoGo
```

Main declarations:

```text
log_natCast_add_one_le_primeWoldBoundaryVolumeBelow_succ_inv
suzukiPrimeCutoffAperture_le_woldScale_succ
suzukiPrimeCutoffAperture_pow_isBigO_woldScale_succ_pow
reflectedHellingerSewingOperatorNorm_beyondEverySuzukiAperturePower
reflectedHellingerSewingOperatorNorm_not_isBigO_suzukiAperturePower
```

Direct unconditional check:

```text
lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiApertureReesConditioningNoGo.lean
```

passed without `sorry`, `admit`, new axiom, `unsafe`, or computation.

Umbrella wiring, targeted build and axiom audit:

```text
GaloisForLFunctions.RHTower imports GaloisForLFunctions.RHTower.Suzuki.SuzukiApertureReesConditioningNoGo
lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiApertureReesConditioningNoGo      green
#print axioms on all five declarations   [propext, Classical.choice, Quot.sound]
```

Repository lint reaches the module; its remaining errors name only unrelated modules added
concurrently elsewhere in the shared tree.

## Gates

- [x] physical cutoff extracted from Suzuki source
- [x] exact paper proof
- [x] stronger no-polynomial-BigO corollary
- [x] unconditional Lean direct check
- [x] scope excludes false class-complete Route G claim
- [ ] external priority audit
- [x] targeted module build, lint, axiom audit, umbrella wiring

## Log

- 2026-08-01 — theorem conjectured from updated modular-superselection scope and Suzuki cutoff.
- 2026-08-01 — paper proof closed; unconditional Lean direct check passed.
