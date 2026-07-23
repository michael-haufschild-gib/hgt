# Chirotope-blind physical/holomorphic period-incidence fracture universality law

Status: paper proof complete; Lean exact audit passed.

## Lean sources

- `periodIncidenceMultiplier_hasLeftInverse_iff_discrete`
- `rankThreePhysicalOsculation_effectivity_fracture`
- `holomorphic_period_incidence_exclusion`
- `periodChirotope`

## Survivor

A discrete Gaussian-lattice triple and a rationally independent conic source can have the same
labelled rank-two chirotope. The lattice realization has an effective global period-incidence
multiplier. The conic realization simultaneously has exact physical contact orders two and three,
no effective global incidence multiplier, no new first-order bounded-holomorphic completion
class, and no nonzero bounded-holomorphic class surviving every powered incidence range.

Thus local oriented-matroid data does not determine any of global incidence effectivity, physical
osculation, or all-power bounded-holomorphic visibility.

## Proof skeleton

Use the lattice triple `(1, 1+i, 1+2i)` and conic parameter `sqrt(2)+i`. Direct sign analysis gives
the same all-positive labelled chirotope. The lattice triple lies in the Gaussian integer lattice,
so its integer span is discrete and its multiplier has a left inverse. Rational irrationality of
`sqrt(2)` proves independence of `1`, `sqrt(2)+i`, and `(sqrt(2)+i)^2`. Existing rank-three physical
osculation and period-incidence exclusion theorems then give the conic branch's exact contact,
ineffectivity, closure-range equality, and all-power vanishing.

## Novelty audit

Pending post-formalization literature search.
