# Library ticket — 2026-07-08: weld-charge-faithfulness-dichotomy → 3-formalized (C2/Q2-E settled)

**For:** librarian (door/00-index.md, door/00-status.md — the weld / seam-transcendence rows; buckets touching
the deck charge, the weld class table, and the prime rate lattice).

**New card:** `docs/drafts/pipeline/3-formalized/weld-charge-faithfulness-dichotomy.md` (3-formalized,
THEOREM (Lean), axiom-clean). Settles question **C2/Q2-E**: *does the deck charge preserve or collapse the
prime-lattice independence of the weld classes?*

**Verdict (BRIDGE).** Faithfulness of a weld charge `H²(WeldGroup;ℝ) →+ M` on the rank-∞ prime lattice is a
**target-torsion trichotomy** whose dividing line is *bounded exponent*, not torsion:
(i) any **finite / bounded-exponent** target ⟹ total collapse to 0 (ℝ divisible, no bounded-exponent character);
(ii) the **torsion-free** `H²(·;ℝ)` ⟹ total faithfulness (unique factorization);
(iii) the **compact divisible torsion circle** `ℝ/ℤ` ⟹ faithfulness RETURNS but is gated by the **transcendence
of e** (`{log p}∪{1}` ℤ-independent because a relation gives `e^k=∏p^{z_p}∈ℚ`, impossible for k≠0). The order
channel stays faithful on ℤ via the profinite `ℤ↪ℤ₂`.

**Mathlib gap filled.** `e^n` / `e^k` irrationality (mathlib has only π) built from scratch by the Hermite
integral — `exp_nat_irrational`, `exp_int_irrational`, axiom-clean. This is the concrete point where the
**arithmetic** weld (prime multiplicative independence) meets the **transcendental** frontier (e); the two are
independent inputs to circle-faithfulness, neither reducible to the other.

**Door relevance.** A precise *location* theorem for the seam: it separates the divisible/flow-like flux channel
(where the collapse lives) from the discrete/constraint-like order channel (faithful), and shows the compact-target
faithfulness is exactly a transcendence statement. "Constraint, not flow" clean — every result is a rigidity
(hom forced zero) or an independence; no carrier constructed. Distinct mechanism from `DeciderBarrier`
(modular quotient) and `deck-charge-invariant` (divisor blindness): this is a coefficient-ring divisibility law.

**Lean.** `formal/GaloisForLFunctions/RHTower/{WeldChargeFaithfulness, ExpNatIrrational, WeldCircleFaithfulness}.lean`,
all imported in the `RHTower` umbrella; lint pass, axiom-clean (`propext, Classical.choice, Quot.sound`).

**Open continuations externalized (not claimed):** which period lattices `Λ⊂ℝ` are faithful (rank-2 `⟨1,τ⟩`
needs `{log p,1,τ}` independence, open for generic τ); the simultaneous circle charge `p↦(log p mod 1)` as a
Kronecker/infinite-torus equidistribution object; adjoining e as a non-arithmetic weld rate (needs transcendence
of e, a further mathlib gap).
