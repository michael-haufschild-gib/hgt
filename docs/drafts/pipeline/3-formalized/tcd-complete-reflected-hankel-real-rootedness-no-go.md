# TCD complete reflected-Hankel real-rootedness no-go

- **ID:** tcd-complete-reflected-hankel-real-rootedness-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · TCD cofinal landing
- **Statement:** Positive real entire source + strict exact rank-three TCD determinant + all reflected polynomial-square Hankel inequalities does not imply real-rootedness.

## Goal

Kill the generic sign-only landing from the finite TCD/S6F gate to RH.

## Gates

- [x] Corpus-derived RH chain and counterexample
- [x] Dependency-closed paper proof
- [x] Lean theorem, targeted build, axioms audit
- [ ] Publication-ready

## Proof

For `F(z)=cosh z+cosh(2z)`, `F(x)>0` on `ℝ` and `F(iπ/3)=0`. At each real center,
`F(x+t)F(x-t)` is a five-atom positive cosh mixture with squared frequencies
`0,1,4,9,16`. Hence every reflected polynomial-square Hankel form is nonnegative; five positive
distinct atoms also make the rank-three Hankel matrix positive definite, so its determinant equals
the exact TCD signed determinant and is strictly positive.

## No-go closure

- **Exact killing theorem:** `completeReflectedHankel_realRootedness_noGo`.
- **Strongest positive survivor:** exact positive five-atom representation and strict rank-three TCD determinant.
- **New insight:** surviving TCD landing must use theta–Xi/source–divisor incidence beyond reflected-Hankel signs.
- **Status:** `RHTower/TCDCompleteReflectedHankelRealRootednessNoGo.lean`; targeted build passes; standard axioms only. Targeted literature audit through 2026-09 found no exact collision.
