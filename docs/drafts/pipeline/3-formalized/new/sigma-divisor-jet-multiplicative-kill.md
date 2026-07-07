# Sigma divisor jet multiplicative kill

- **ID:** sigma-divisor-jet-multiplicative-kill
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), negative route theorem
- **Source:** `docs/drafts/rh-monodromy-weight-mismatch/106-joint-reading-no-go.md` rescue shape; `formal/GaloisForLFunctions/RHTower/SigmaDivisorJet.lean`
- **Statement:** The natural pinned-annulus divisor-tangent object is the local jet algebra `R[X]/(X^m)`. Any `{sigma_p}` source direction locally divisible by the zero factor `X^m`, in particular any multiplicative local direction `(X^m u) h_p`, has zero class in that algebra. Thus a multiplicative sigma lane cannot produce a divisor refinement finer than multiplicity at one pinned annulus.

## Goal

Doc 106 left one non-character, non-positivity escape hatch: build a `{sigma_p}`-graded divisor refinement finer than multiplicity, read at one pinned annulus. The first viable object is the local divisor-tangent class: if the function has local form `X^m u`, a source direction `delta_p` contributes the class of its local direction modulo `X^m`.

This theorem kills the multiplicative-source candidate. A prime lane that acts locally by multiplying the function by a holomorphic factor changes only the unit and contributes no local divisor jet.

## Gates

- [x] 0 -> 1  in-progress: the candidate object is named as the local divisor-jet algebra `R[X]/(X^m)`.
- [x] 1 -> 2  fully-proven: ideal-quotient proof: divisibility by `X^m` implies zero class in `R[X]/(X^m)`.
- [x] 2 -> 3  formalized: Lean module `GaloisForLFunctions.RHTower.SigmaDivisorJet`; narrow check `lake env lean GaloisForLFunctions/RHTower/SigmaDivisorJet.lean` passed.
- [ ] 3 -> 4  publication-ready: integrate into the RHTower narrative around docs 105-106 and the `M+` seam gap.

## Proof

Let `R` be a commutative ring and fix a local zero of multiplicity `m`. Model the pinned-annulus local algebra by the coordinate `X = z-rho` and the quotient

`J_m(R) = R[X] / (X^m)`.

For any local source direction `delta`, its divisor-tangent reading is `[delta] in J_m(R)`. If `X^m` divides `delta`, then `delta in (X^m)`, hence `[delta] = 0`.

A multiplicative sigma source direction has local form

`delta_p = (X^m u) h_p = X^m (u h_p)`,

so `X^m | delta_p` for every `p`. Therefore every sigma-labelled divisor jet is zero. This is independent of character theory and positivity: no group of weights or ordered cone appears in the statement.

## Formal Surface

Lean declarations:

- `jetIdeal`
- `LocalDivisorJet`
- `jetClass`
- `jetClass_eq_zero_of_X_pow_dvd`
- `jetClass_mul_X_pow_eq_zero`
- `HasNontrivialSigmaJet`
- `no_nontrivialSigmaJet_of_X_pow_dvd`
- `no_nontrivialSigmaJet_of_multiplicative`
- `no_nontrivialSigmaJet_of_unit_multiplicative`

## Exhaustion Against Current `M+` Generators

The pinned-annulus escape hatch now has the following disjunction.

| Source of a sigma grade | Disposition |
|---|---|
| external pinned symmetry | killed by `JointReadingNoGo.lean`: the joint `{sigma_p} x partial_s` symmetry has exponent `2`, while the q62 weight mechanism needs unbounded order |
| positivity / Landau shadow | killed by `LandauShadowNoGo.lean`: the real-axis positivity shadow is blind to off-line divisor parity |
| local multiplicative sigma source | killed here: `(X^m u) h_p` maps to `0` in `R[X]/(X^m)` |
| commutator with the archimedean generator | killed by coordinate-scale commutation: finite coordinate scalings commute with the simultaneous scaling generator; no local commutator class is produced |
| cross-prime curvature | prior cross-prime curvature card: the square-zero curvature is a discrete curl/coboundary object and is the A2 variance face, not a local divisor-tangent refinement |

So the existing category data do not supply the desired object. A survivor would have to be added as a new primitive interface, not extracted from the current pinned sigma/archimedean generators.

## Open Residue

The only surviving shape is a non-multiplicative sigma-to-local-divisor source map:

`sigma_p -> delta_p` with some `delta_p mod X^m != 0`,

constructed before reading the zero divisor and without using a flow or positivity. The current `M+` data provide sigma actions as local unit changes at the pinned annulus, so this residue is exactly the missing interface rather than an available construction.

## Log

- 2026-07-07 - Codex: created and formalized the local jet obstruction; narrow Lean check passed.
