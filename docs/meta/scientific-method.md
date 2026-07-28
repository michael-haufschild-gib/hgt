## Conjecture formation

A conjecture is an informed truth-hunch, not a statement selected because it looks provable:

> Based on everything presently known, statement \(S\) may be true, although no proof route for
> \(S\) is presently visible.

Conjecture formation ends when \(S\) is frozen. Provability begins afterward. Before freezing \(S\):

1. absorb relevant observations, established theory, failed routes, and primary literature;
2. ask what physical statement now seems true;
3. do not ask whether current mathematics, Lean, or corpus machinery can prove it;
4. do not weaken, strengthen, or reshape it to expose a proof;
5. record the hunch, its physical meaning, and why it is believed, without a candidate realization.

If a proof route is already visible and materially determines the statement, classify it as a
`[BRIDGE]` or derived theorem candidate, not as the primary conjecture. After freezing, proof search,
hostile falsification, novelty audit, prediction extraction, and unconditional Lean formalization
begin. Inability to find a proof does not count against the conjecture.

## Conjecture attack

When stuck on a frozen conjecture:

1. **Split it into subclaims.** Prove or test each part separately.
2. **Attack it as false.** Search for counterexamples and edge cases.
3. **Reverse it.** Ask whether the converse, contrapositive, or inverse is easier.
4. **Change the viewpoint.** Rotate it, reflect it, rephrase it, or look at it from another angle.
5. **Make it visual.** Turn it into a shape, machine, path, game, or physical object.
6. **Ask what action is happening.** Are you moving, preserving, compressing, cutting, joining, sorting, counting, or transforming something?
7. **Strip it to essentials.** Keep only the properties truly needed. Remove decoration.
8. **Look for similar objects.** Ask what else has the same key properties.
9. **Test small cases.** Work out the first few examples by hand.
10. **Test extreme cases.** Check zero, one, maximum, infinite, symmetric, degenerate, or pathological cases.
11. **Run experiments.** Generate examples, compute data, draw diagrams, and look for patterns.
12. **Find an invariant.** Ask what stays unchanged while the object changes.
13. **Find a monotone quantity.** Look for something that only increases, decreases, or cannot cross a boundary.
14. **Prove a weaker bridge.** Keep the frozen conjecture unchanged; label any easier statement
    `[BRIDGE]` rather than silently replacing the hunch.
15. **Form a new stronger hunch only independently.** If failure suggests a different statement,
    freeze it as a new conjecture before attacking it; do not add structure merely to rescue the old
    conjecture.
16. **Use a minimal counterexample.** Assume the smallest counterexample exists, then try to make it smaller.
17. **Change representation.** Rewrite it as algebra, geometry, graph theory, matrices, probability, order, or optimization.
18. **Look for the right theorem.** Ask what known technique the problem resembles.
19. **Write the fake proof.** Draft the proof you wish worked, then identify the exact gap.
20. **Name the missing lemma.** Turn repeated obstacles into smaller claims.
21. **Build a dependency chain.** Ask: “What would be enough to prove this?” until you reach something manageable.
22. **Compare nearby false statements.** Change assumptions until it breaks; the breaking point reveals the structure.
23. **Classify boundary cases.** Study when equality, failure, or sharpness occurs.
24. **Extract the positive residue.** After every no-go, seek the strongest positive theorem exposed
    by the obstruction, state the new insight exactly, and formalize it in Lean once its paper proof
    is dependency-closed. If none survives, record the serious attempts explicitly.
