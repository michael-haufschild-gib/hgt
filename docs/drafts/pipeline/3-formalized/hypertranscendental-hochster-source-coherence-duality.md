# Hypertranscendental source coherence is the topology of the constraint boundary

- **ID:** `hypertranscendental-hochster-source-coherence-duality`
- **Stage:** 3-formalized
- **Source card:**
  `../2-fully-proven/new_scientific_knowledge/other/hypertranscendental-hochster-source-coherence-duality.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/HypertranscendentalHochsterSourceCoherenceDuality.lean`
- **Status:** `[FORMALIZED UNCONDITIONALLY]`

## Exact theorem surface

`HochsterSourceCoherenceExact facets` states, for every multidegree `σ`, every Koszul degree `p`,
and every alternating multidegree-`σ` tensor in the Stanley--Reisner ring, both exact halves of
Hochster correspondence:

- the tensor is a Koszul cycle iff its exhaustive strand cochain is a reduced simplicial cocycle
  on the induced constraint subcomplex;
- the tensor is a Koszul boundary iff that strand cochain is a reduced simplicial coboundary.

`hochsterSourceCoherenceExact` proves this profile for every finite facet complex by the
all-degree exhaustive strand theorem.

`hypertranscendentalHochsterSourceCoherence_orientationProduct` is the cross-category capstone.
For arbitrary finite facet complex, arbitrary finite localized structural family, and arbitrary
`k : ℕ`, it proves simultaneously:

1. finite residue surgery leaves the embedded differential field unchanged;
2. the oriented source is Herglotz exactly when `k = 0`;
3. its negative residue index is exactly `k`;
4. its complete finite-family nonlinear differential matroid is exactly the localized
   Stanley--Reisner linear matroid; and
5. the same facet complex has the exact all-multidegree, all-Koszul-degree Hochster
   source-coherence profile.

Hence arbitrary finite derived constraint topology and arbitrary finite residue orientation
coexist over one universal hypertranscendental field.  Complete unpolarized derived topology does
not select the positive analytic chamber.

## Verification

- Direct check:
  `lake env lean GaloisForLFunctions/HTGeometry/HypertranscendentalHochsterSourceCoherenceDuality.lean`
- Umbrella: `GaloisForLFunctions.HTGeometry`
- Axiom audit for the predicate and both capstones: only `propext`, `Classical.choice`, and
  `Quot.sound`.

Independent localization/grading convention review and novelty review remain publication gates,
not formalization dependencies.
