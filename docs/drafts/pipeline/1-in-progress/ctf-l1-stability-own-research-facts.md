# CTF `L¹`-stability facts

- `RHTower.boseTransform_le_kernelBound_mul_tailL1` proves that, at every point in the Bose domain, the response difference of two integrable profiles is bounded by a compact kernel constant times their tail `L¹` distance.
- `RHTower.tendsto_boseTransform_of_tailL1` proves bounded measurable tail profiles converging in that tail `L¹` metric have pointwise-convergent Bose responses.
- `RHTower.no_l1_stable_tail_repair` is an unconditional no-go: no uniformly bounded moving tail family can both converge in tail `L¹` to a bounded profile and converge on `[1,2]` to a critical profile's Bose response.
- Therefore a CTF repair in this tail model cannot admit an `L¹`-convergent reindexing. A viable CTF mechanism must leave fixed bounded-tail `L¹` compactness or establish the alternative all-grade source orientation law. This does **not** exclude arbitrary noncompact moving arrays.
- Lean status: `ChronologicalTailL1StabilityNoGo.lean` leaf-checks; audited the three theorems with only `propext`, `Classical.choice`, and `Quot.sound`.
