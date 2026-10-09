# Every ordered critical-value tuple is realized

- **ID:** ORDERED-CRITICAL-VALUE-SURJECTIVITY-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); realization bridge
- **Parent:** `../1-in-progress/finite-planar-polynomial-realization.md`
- **Statement:** For every n and every ordered tuple b∈C^{n+1}, the constructed additive-constant critical-value map B:C^n×C→C^{n+1} has a preimage of b.

## Audit and significance

**BRIDGE.** Properness of the actual map is fully audited; its local inverse at every tuple of distinct critical positions passes production Lean. The exact source corpus theorem `ComplexPolynomialComplementPathConnected.isPathConnected_complexMvPolynomial_nonzeroLocus` supplies path connectedness of a complex polynomial nonzero locus. The lexical configuration query had no hits; subsequent source search found this stronger applicable theorem. No external sources used; external novelty unverified.

This result realizes prescribed critical values, not prescribed covering monodromy. The latter and finite planar completions of actual Xi pieces remain explicit obligations. The target has not changed to an assumed uniformization theorem.

## Complete paper proof [PROVED HERE]

Let m=n+1 and let Cfg_m⊂C^m be the injective tuples. The polynomial Δ(b)=∏_{i<j}(b_i−b_j) is nonzero exactly on Cfg_m. At the tuple b_i=i, every factor is nonzero. The checked complex polynomial complement theorem therefore makes Cfg_m path connected, in particular connected and nonempty. It is open by continuity of the finitely many coordinate differences.

Cfg_m is dense. Fix any tuple b and any neighborhood V of b. The affine perturbation b(t)_i=b_i+t i is continuous in t and equals b at t=0, so its preimage of V is a neighborhood of zero. A collision b(t)_i=b(t)_j with i≠j forces t=(b_j−b_i)/(i−j), since distinct natural indices remain distinct in C. There are only finitely many such forbidden parameters. The inspected theorem that the complement of a countable set in a nontrivial real topological vector space is dense applies to C; hence this neighborhood contains t outside the finite forbidden set. Then b(t)∈Cfg_m∩V. This proves density with no numerical selection.

There is a parameter v with distinct critical positions. Start with the distinct numbers r_j=j for j<m, let μ=(∑r_j)/m, and put c_i=r_{i+1}−μ for i<n, with additive constant zero. The sum identity mμ=∑r_j makes the remaining position a₀=−∑c_i equal r₀−μ. Thus every position equals r_j−μ; translation preserves distinctness. This includes m=1, where the single position is zero.

By the proved local-inverse theorem, an open neighborhood of B(v) lies in the image of B. Density of Cfg_m makes that neighborhood meet Cfg_m. Hence the subset I of configurations that belong to range(B) is nonempty.

The map B is proper, so its image is closed. Thus I is closed in Cfg_m. It is also open there: if b=B(v) is an injective tuple, then the critical positions of v are distinct (coincident positions would give coincident values). The local inverse at v supplies an open target neighborhood of b contained in range(B). Intersecting it with Cfg_m proves relative openness. Connectedness and nonemptiness now give I=Cfg_m. Finally range(B) is closed and contains the dense subset Cfg_m, so range(B)=C^m. This proves surjectivity, including tuples with repeated values. The proof retains the actual map throughout and makes no unproved monodromy assumption.

## Next after surjectivity

Prove the restriction over Cfg_m is a proper covering, then identify its path-lifting action with the prescribed planar monodromy and control collisions to the two marked values. Surjectivity alone does not perform that identification.

## Log

- 2026-10-09 — full argument recorded from the checked proper map, checked local inverse, and inspected corpus topology. Configuration density and connectedness adapters are the next Lean step.

## Lean certificate

`HTGeometry/ComplexConfigurationSpace.lean` (8 explicit declarations) and `HTGeometry/OrderedCriticalValueSurjectivity.lean` (3 declarations) pass their production leaf builds, all 11 public axiom audits, and final actual-source `lake env lean` checks. Both final logs are empty. Every axiom list contains only `propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired into the HTGeometry umbrella.

The decisive unconditional theorem is `GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap.surjective_valuesWithConstant`. The continuation and connected-cover theorem is now fully audited in `ordered-critical-value-covering.md`. Prescribed planar monodromy remains unproved. External novelty is unverified.
