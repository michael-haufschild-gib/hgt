# Arithmetic order relations and full sign ambiguity

- **ID:** biscale-order-relation-classification-1810
- **Stage:** 1-in-progress
- **Parent:** [field programme](biscale-field-development-1810.md), items 3–4 and 13
- **Status:** exact candidate and symbolic construction; full proof and Lean gates open

## Candidate local criterion

Let positive orders `d₁,…,d_m` divide a cyclic period `P`, and let `L=lcm(d₁,…,d_m)`. There should exist frequencies of exactly these orders summing to zero if and only if, for every prime `ℓ|L`, the number of indices attaining the largest `ℓ`-adic valuation is not one, and for `ℓ=2` this number is even.

The restriction `ℓ|L` matters: an all-odd tuple must not acquire a spurious even-length condition. The empty tuple and `L=1` need separate explicit treatment.

Necessity follows by reducing the frequency sum at its highest `ℓ`-primary level modulo `ℓ`: a unique unit cannot sum to zero; at two, a sum of units is zero only for an even number of summands.

For sufficiency, work separately in `ℤ/ℓ^Hℤ`. Give each lower-order term its required power of `ℓ` times a unit. At two, choose all but one of the maximal-order units arbitrarily equal to one; their number is odd, so the final cancelling term is a unit. At an odd prime, reserve two maximal-order terms. After choosing the others, choose the penultimate unit avoiding zero and the negative accumulated residue modulo `ℓ`; at most two residues are forbidden and `ℓ≥3`. The cancelling final term is then a unit. CRT combines these choices with each term's exact primary orders; multiplication by `P/L` embeds the resulting relation in the actual period.

## Candidate exact observation classification

For a finite nonzero coordinate support `S`, make a binary matrix whose rows are the parity vectors of multiplicities in all tuples of orders from `S` of total length at most `k` satisfying the above explicit local criterion. For `k≥2`, squared magnitudes are already determined. The remaining sign ambiguity should be exactly the binary kernel of this matrix, via the literal moment Fourier formula and its inverse. Zero coordinates are omitted from the active support; products involving them impose no sign relation.

Affine observations add the rows supported on comparable pairs `d|q`. This gives a finite arithmetic description even when several odd factors and several two-adic valuation levels occur.

Through degree six, the existing same-valuation triples pair every two coordinates in a block. The newly formalized mixed quintic orients every lower block when a higher block is active. Odd-order coordinates have cubic orientation. The resulting candidate full ambiguity is:

- `L` odd: identity only;
- `L` even: identity and simultaneous sign reversal of exactly the highest active two-adic block.

The latter sign change should equal actual translation by `L/2`; this converse and the full-data invariance still require a complete proof here. With affine data, the highest-block flip survives exactly when no comparable active pair crosses from that block to a lower block.

## Sharp-order proposal with an explicit finite input

The local criterion constructs row matrices for degrees `2,3,4,5,6` directly from prime valuations of the support, without enumerating the factorial-period frequency space. Their binary ranks should give the exact first separating degree, with the uniform upper bound six supplied by the block proof. A closed finite rank formula must replace a tautological definition as a least separating degree. Handle empty support and the constant-only support separately: their orders can be below two.

For every surviving kernel sign vector, actual weights can be constructed by Möbius inversion: the order-`q` atom has coefficient `d μ(q/d)` at each divisor `d|q` and zero elsewhere. Exact coordinate realization must be proved or reused from the corpus. Such atoms would supply all indistinguishable witnesses required for sharp lower bounds.

## Attack and novelty boundaries

- Do not infer that sixth data alone orient lower blocks: the argument uses **all moments through six**, including odd degrees.
- Do not confuse global sign with the highest-block sign; lower active blocks generally retain their orientation.
- Scalar Fourier coefficients constant on order classes form a much narrower family than arbitrary real cyclic functions.
- Classical cyclic six-deck results and Casper–Orozco's unit-decomposition / phase-gluing method are close prior art. The claimed contribution, if established, must be the exact arithmetic sign classification, effective support formula and its quantitative consequences, not the number six.
- Current highest-block corpus query returned antiperiodicity and within-block results, without this general parity classification among returned statements. Snapshot retrieval does not prove absence.

Completion gates: local criterion in both directions; Fourier inversion; exact coordinate realization; translation realization; affine refinement; explicit degree formula and actual lower-bound witnesses; direct Lean audits and axiom closure. No gate is marked complete yet.
