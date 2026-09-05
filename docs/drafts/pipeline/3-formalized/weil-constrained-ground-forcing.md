# Exact pole forcing of the constrained Weil ground

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every attained constrained ground belongs to the actual unrestricted Friedrichs operator domain and has unique two-pole forcing. At every aperture a nonzero ground can be chosen with pure parity and one even or odd forcing profile.

## Proof chain and open source problem

Literal constrained Weil ground → exact forced operator equation → source-derived exclusion of its unique possible zero threshold → positive ground at every aperture → weighted pole exclusion → RH. Operator-domain membership, forcing uniqueness, and the parity reduction are proved. Excluding a nonzero constrained zero ground remains open; RH is neither proved nor disproved.

Write `f=Jₐu`, `μ=μ₀(a)`, and `p±(x)=exp(±x/2)` on the aperture. The actual equation is

`Hₐf = μf + c₊p₊ + c₋p₋`.

For a pure-parity ground the coefficients satisfy `c₋=r c₊`, with `r=1` or `r=-1`, so

`Hₐf = μf + c(p₊+r p₋)`.

The scalar `c` may be zero; no vanishing or nonvanishing theorem for it is claimed. A zero-threshold argument must cover both scalar values and both parity possibilities. Pure parity does not select the even branch.

## Dependency-closed paper proof

The shifted actual compact pencil represents `Q-E mass`. At the attained constrained ground `E=μ`, this form is nonnegative on the constrained sector and the ground is null. Hermitian polarization makes its sesquilinear functional vanish on the common kernel of the two pole-coordinate functionals.

The two literal side bumps have strictly positive pole-moment determinant. Cramer inversion supplies form vectors with coordinates `(1,0)` and `(0,1)`. Subtracting the two coordinate components from an arbitrary form vector leaves a constrained vector. Consequently every continuous functional vanishing on the constrained sector is a unique linear combination of the two moment coordinates. With Lean's conjugate-linear first inner-product convention, the physical forcing coefficients are the conjugates of that functional evaluated on the two coordinate-section vectors.

Applying this classification to the shifted ground functional gives a physical representative equal to `μf+c₊p₊+c₋p₋`. The existing converse Friedrichs representation theorem gives actual unrestricted operator-domain membership and that exact operator value. No boundary trace, smoothness, or unrestricted eigenvector assumption is used.

Reflection swaps the two pole coordinates and preserves their common kernel. The corpus's exact energy and physical-mass decompositions split a constrained ground into even and odd parts. Both parts attain the same constrained Rayleigh floor whenever nonzero, and at least one is nonzero. Complex polarization of the diagonal reflection identity proves reflection invariance of the complete sesquilinear form. For `Ru=ru`, the shifted functional and coordinate swap force `r c₋=c₊`; since `r²=1`, this gives `c₋=r c₊`. Applying the operator-domain theorem to a nonzero parity ground proves the single-profile source equation.

## Conjecture refinement and corpus provenance

The attempted ordinary zero-eigenstate conclusion omitted the functionals discarded by the constraints. The proved replacement retains them exactly as unique pole forcing. The second conjecture, suggested by the corpus's unrestricted ground-parity splitting, strengthens this to a single forcing profile in a pure-parity constrained ground. Both positive statements are formalized; no route is retired by this work.

Inputs: `CCMRestrictedWeilPolarConstrainedSmoothCore` (side-bump Cramer identities), `CCMRestrictedWeilPolarStrictDomain` (closed constrained sector and shifted diagonal), `CompactConstrainedRadical` (semidefinite radical), `CCMRestrictedWeilCanonicalGroundHeadEnergy` (exact shifted pencil), `BoundedPerturbedFriedrichsOperator.boundedPerturbedFriedrichsOperator_mem_domain_of_represents`, and `CCMRestrictedWeilGroundParity` (literal reflection and energy/mass splitting). Mathlib `inner_map_polarization'` promotes the real-diagonal source identity to the full complex form.

Whole-index searches for constrained ground/boundary, ground/Lagrange, constraint/annihilator, and Hermitian diagonal identities located these inputs. The existing parity theorem concerned the unrestricted ground; it did not provide the constrained forcing statement. This is a corpus novelty check, not a literature-priority claim.

## Lean statements and validation

| Leaf under `formal/GaloisForLFunctions/RHTower/` | Public theorems | Main endpoints |
|---|---:|---|
| `CCMRestrictedWeilPolarGroundForcing.lean` | 10 | `existsUnique_polarGround_operator_forcing`, `exists_normalized_polarGround_operator_forcing` |
| `CCMRestrictedWeilPolarGroundParityForcing.lean` | 9 | `polarForcing_coefficient_reflection`, `exists_polarGround_singleProfile_forcing` |

Both leaves are wired into `RHTower.lean`. Foreground `lake env lean` scratch checks and both exact named `lake --old --log-level=error build <module>` audits pass. The 19 public theorem axiom audits contain only `[propext, Classical.choice, Quot.sound]`. The actual `riemannZeta` definition of `RiemannHypothesis` was printed during audit. No added axiom, admission, computational oracle, numerical experiment, full build, or umbrella build was used.

`git diff --check` passes. Repository-wide formal lint reports eight unrelated, concurrently created, unwired `HTGeometry.Arxiv2608BellmanShoreline*` modules: `Algebra`, `Applications`, `CanonicalFaces`, `Convex`, `CrossPolytope`, `DelaySystem`, `NComp`, and `TwoHalfCells`. This audit therefore does not claim clean global lint.

Scratch and complete lint output: `/tmp/hgt-polar-forcing.mgyslef7`. `Combined.lean` and `ParityCombined.lean` are the final checked source copies; smaller assembly files are earlier inputs. All owned Lean/build sessions are terminal.
