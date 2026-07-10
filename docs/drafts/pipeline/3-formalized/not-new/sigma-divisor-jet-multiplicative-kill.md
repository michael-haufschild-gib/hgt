# Sigma divisor jet multiplicative kill

- **ID:** sigma-divisor-jet-multiplicative-kill
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), negative route theorem
- **Source:** `docs/drafts/rh-monodromy-weight-mismatch/106-joint-reading-no-go.md` rescue shape; `formal/GaloisForLFunctions/RHTower/SigmaDivisorJet.lean`; `formal/GaloisForLFunctions/RHTower/PrimeDivisorAtomsNoGo.lean`; `formal/GaloisForLFunctions/RHTower/SigmaDivisorExhaustion.lean`; `formal/GaloisForLFunctions/RHTower/FittingSeamBoundary.lean`; `formal/GaloisForLFunctions/RHTower/MPlusTorsionSeam.lean`
- **Statement:** The natural pinned-annulus divisor-tangent object is the local jet algebra `R[X]/(X^m)`. Any `{sigma_p}` source direction locally divisible by the zero factor `X^m`, in particular any multiplicative local direction `(X^m u) h_p`, has zero class in that algebra. Prime-local atom maps are also zero at strip points because every finite Euler layer is a unit there. The only algebraic survivor is a torsion seam presentation `R^n --A--> R^n` with `det A = X^m` and a sigma defect `Delta_p`; its Fitting boundary is nonzero only if `Delta_p` is not in `A End + (X^m)`. The current definition of `M+` has finite-free regular lanes and no torsion seam presentation layer, so this survivor is not available inside bare `M+`.

## Goal

Doc 106 left one non-character, non-positivity escape hatch: build a `{sigma_p}`-graded divisor refinement finer than multiplicity, read at one pinned annulus. The first viable object is the local divisor-tangent class: if the function has local form `X^m u`, a source direction `delta_p` contributes the class of its local direction modulo `X^m`.

This theorem kills the multiplicative-source candidate. A prime lane that acts locally by multiplying the function by a holomorphic factor changes only the unit and contributes no local divisor jet.

## Gates

- [x] 0 -> 1  in-progress: the candidate object is named as the local divisor-jet algebra `R[X]/(X^m)`.
- [x] 1 -> 2  fully-proven: ideal-quotient proof: divisibility by `X^m` implies zero class in `R[X]/(X^m)`.
- [x] 2 -> 3  formalized: Lean modules `GaloisForLFunctions.RHTower.SigmaDivisorJet`, `GaloisForLFunctions.RHTower.SigmaDivisorExhaustion`, and `GaloisForLFunctions.RHTower.FittingSeamBoundary`; narrow checks `lake env lean GaloisForLFunctions/RHTower/SigmaDivisorJet.lean`, `lake env lean GaloisForLFunctions/RHTower/PrimeDivisorAtomsNoGo.lean`, `lake env lean GaloisForLFunctions/RHTower/SigmaDivisorExhaustion.lean`, and `lake env lean GaloisForLFunctions/RHTower/FittingSeamBoundary.lean` passed. `../scripts/formal_tools.py index && ../scripts/formal_tools.py lint --check-generated` passed after integration.
- [ ] 3 -> 4  publication-ready: integrate into the RHTower narrative around docs 105-106 and the `M+` seam gap.

## Proof

Let `R` be a commutative ring and fix a local zero of multiplicity `m`. Model the pinned-annulus local algebra by the coordinate `X = z-rho` and the quotient

`J_m(R) = R[X] / (X^m)`.

For any local source direction `delta`, its divisor-tangent reading is `[delta] in J_m(R)`. If `X^m` divides `delta`, then `delta in (X^m)`, hence `[delta] = 0`.

A multiplicative sigma source direction has local form

`delta_p = (X^m u) h_p = X^m (u h_p)`,

so `X^m | delta_p` for every `p`. Therefore every sigma-labelled divisor jet is zero. This is independent of character theory and positivity: no group of weights or ordered cone appears in the statement.

## Formal Surface

Lean declarations in `SigmaDivisorJet.lean`:

- `jetIdeal`
- `LocalDivisorJet`
- `jetClass`
- `jetClass_eq_zero_of_X_pow_dvd`
- `jetClass_mul_X_pow_eq_zero`
- `jetClass_eq_zero_iff_coeff_lt_eq_zero`
- `jetClass_ne_zero_iff_exists_coeff_lt_ne_zero`
- `HasNontrivialSigmaJet`
- `no_nontrivialSigmaJet_of_X_pow_dvd`
- `no_nontrivialSigmaJet_of_multiplicative`
- `no_nontrivialSigmaJet_of_unit_multiplicative`

Lean declarations in `PrimeDivisorAtomsNoGo.lean`:

- `eulerInvFactor_orderAt_zero`
- `eulerPartial_orderAt_zero`
- `eulerPartial_zeroSet_eq_empty`
- `xi_divisor_prime_invisible`
- `no_sigma_graded_refinement`
- `SigmaSourceMap`
- `sigma_source_map_trivial`
- `source_atom_mismatch`
- `prime_content_and_divisor_disjoint`

Lean declarations in `SigmaDivisorExhaustion.lean`:

- `pinnedSigmaDivisorSources_killed`
- `pinnedSigmaDivisorSources_mismatch_with_emSplit`

Lean declarations in `FittingSeamBoundary.lean`:

- `fittingBoundaryTrace`
- `fittingBoundaryClass`
- `HasNontrivialFittingBoundary`
- `fittingBoundaryTrace_right_factor`
- `fittingBoundaryTrace_smul`
- `fittingBoundaryClass_eq_zero_iff_coeff_lt_eq_zero`
- `fittingBoundaryClass_ne_zero_iff_exists_coeff_lt_ne_zero`
- `fittingBoundaryClass_eq_zero_of_trace_X_pow_dvd`
- `no_nontrivialFittingBoundary_of_trace_X_pow_dvd`
- `fittingBoundaryClass_eq_zero_of_right_factor`
- `fittingBoundaryClass_eq_zero_of_right_factor_mod_X_pow`
- `nonzero_fittingBoundaryClass_obstructs_right_factor_mod_X_pow`
- `no_nontrivialFittingBoundary_of_right_factor_mod_X_pow`
- `fittingBoundaryTrace_left_factor`
- `fittingBoundaryClass_eq_zero_of_left_factor`
- `fittingBoundaryClass_eq_zero_of_left_factor_mod_X_pow`
- `nonzero_fittingBoundaryClass_obstructs_left_factor_mod_X_pow`
- `no_nontrivialFittingBoundary_of_left_factor_mod_X_pow`
- `fittingBoundaryTrace_eq_sum_det_updateRow`
- `HasSupportedTorsion`
- `no_supportedTorsion_of_noZeroSMulDivisors`
- `supportedTorsion_forces_not_noZeroSMulDivisors`

Lean declarations in `MPlusTorsionSeam.lean`:

- `TorsionSeamPresentation`
- `MPlusTorsionSeamObject`
- `TorsionSeamPresentation.Hom`
- `TorsionSeamPresentation.Hom.id`
- `TorsionSeamPresentation.Hom.comp`
- `TorsionSeamPresentation.BoundaryCoeffWitness`
- `TorsionSeamPresentation.defectNonmember_of_coeffWitness`
- `coeff_obstructs_right_factor_mod_X_pow`

## Exhaustion Against Current `M+` Generators

The pinned-annulus escape hatch now has the following disjunction.

| Source of a sigma grade | Disposition |
|---|---|
| external pinned symmetry | killed by `JointReadingNoGo.lean`: the joint `{sigma_p} x partial_s` symmetry has exponent `2`, while the q62 weight mechanism needs unbounded order |
| positivity / Landau shadow | killed by `LandauShadowNoGo.lean`: the real-axis positivity shadow is blind to off-line divisor parity |
| local multiplicative sigma source | killed here: `(X^m u) h_p` maps to `0` in `R[X]/(X^m)` |
| prime-local divisor atoms | killed by `PrimeDivisorAtomsNoGo.lean`: each finite Euler factor and finite Euler atlas is a unit at strip points, so the source atom map is zero |
| commutator with the archimedean generator | killed by coordinate-scale commutation: finite coordinate scalings commute with the simultaneous scaling generator; no local commutator class is produced |
| cross-prime curvature | prior cross-prime curvature card: the square-zero curvature is a discrete curl/coboundary object and is the A2 variance face, not a local divisor-tangent refinement |
| Fitting boundary from a torsion seam presentation | algebraically viable only after adding a local presentation `A` with `det A = X^m`; fake defects `Delta_p = A H_p mod X^m` vanish, and a nonzero boundary is exactly a proof of `Delta_p ∉ A End + (X^m)` |

So the existing category data do not supply the desired object. A survivor would have to be added as a new primitive interface, not extracted from the current pinned sigma/archimedean generators.

## Open Residue

The only surviving shape is no longer a loose source map. It is a p-labelled torsion seam presentation:

`R^n --A--> R^n -> Q`, `det A = X^m`, with sigma defects `Delta_p`.

The boundary candidate is `tr(adj(A) Delta_p) mod X^m`. Fake defects vanish by formal theorem:

`Delta_p = A H_p + X^m K_p  =>  [tr(adj(A) Delta_p)] = 0 in R[X]/(X^m)`.

So an extended category with this layer would have one exact next theorem:

`Delta_p ∉ A End + (X^m)`.

But the audited `M+` definition is the completed finite-free `(sigma_p, partial_s)` connection category: finite-free `R+`-modules, commuting semilinear `sigma_p` automorphisms, and a compatible `partial_s` connection. It has no object field for `Q = coker A`, no morphism condition preserving `A`, and no supported torsion slot. Therefore the route is killed inside bare `M+`.

The formal extension is now `MPlusTorsionSeam.lean`: it adds the torsion seam presentation as a constraint layer over an abstract regular base, defines seam morphisms, proves identity and composition, and proves that a coefficient witness below `m` in `tr(adj(A) Delta_p)` implies `Delta_p ∉ A End + (X^m)`. The trace has the row-replacement determinant form `sum_i det(A with row i replaced by row_i(Delta_p))`, so the arithmetic witness is a concrete determinant coefficient, not an opaque adjugate class.

The coefficient condition is exact: the Fitting boundary is nonzero iff some coefficient below `m` survives. Hence any determinant-compatible defect with `X^m | tr(adj(A) Delta_p)` is dead; the surviving arithmetic target is precisely determinant transversality modulo `X^m`.

## Log

- 2026-07-07 - Codex: created and formalized the local jet obstruction; narrow Lean checks passed.
- 2026-07-07 - Codex: added `SigmaDivisorExhaustion.lean`, packaging prime-local atom triviality and multiplicative local jet triviality into one pinned-annulus theorem.
- 2026-07-07 - Codex: added `FittingSeamBoundary.lean`, formalizing the only viable torsion-presentation boundary and proving fake right-factor defects vanish. Audited the current `M+` definition: no torsion seam presentation layer is present, so the route is killed unless `M+` is extended at the object/morphism definition level.
- 2026-07-07 - Codex: added `MPlusTorsionSeam.lean`, a formal constraint-layer extension with torsion seam objects, morphisms, identity, composition, coefficient witnesses, and the theorem deriving `Delta_p ∉ A End + (X^m)` from a surviving low coefficient.
- 2026-07-07 - Codex: strengthened `FittingSeamBoundary.lean` with left-factor fake-defect vanishing and the Jacobi row form `fittingBoundaryTrace_eq_sum_det_updateRow`; the next witness can be searched as a low coefficient in a row-replacement determinant sum.
- 2026-07-07 - Codex: upgraded the coefficient witness to an iff in `SigmaDivisorJet.lean` / `FittingSeamBoundary.lean` and added the determinant-compatible no-go `fittingBoundaryClass_eq_zero_of_trace_X_pow_dvd`. A live seam defect must now be determinant-transverse modulo `X^m`.
