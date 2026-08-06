# Cycle 18: the capstone as an EXACT identity (2026-08-06)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-18).
Lean: appended to `formal/GaloisForLFunctions/RHTower/GibbsPotentialBound.lean`
(`log_cancellation_eq`, `norm_one_sub_pos_of_root`), built, no sorry, axioms clean.

## THE EXACT CONDENSATION LAW
For any finite S, any x, provided gibbsDiagC S x (−1) ≠ 0:
  log‖Z_S(x)‖ − log‖J_S(x)‖ = ∑_ζ ( log‖1−ζ‖ − log‖1+ζ‖ ).
The e^{−xm} prefactor cancels between the two product formulas of cycle 13. NO estimate, NO
hypothesis on zero locations, every coupling.
The cycle-17 Coulomb-potential bound and the cycles-10/13 sufficient direction are both
readings of this one identity (bounding its summands from either side).

With cycle 15 (anchor) + cycle 16 (bridge):
  RH ⟺ ∑_ζ log(‖1−ζ‖/‖1+ζ‖) ≥ (1/2 − ε)·log(1/x)   (up to the explicit geometric tail).
Each summand is positive exactly when that zero is in the OPEN LEFT half-plane — which is
why stability mattered, and why its failure (cycle 11) matters: some summands can be
negative and the identity accounts for them exactly.

## Lean trap (cost me two iterations)
Keep multiset maps in PLAIN LAMBDA form. After `multiset_log_prod`, normalize with
`simp only [Multiset.map_map, Function.comp_def]` — NOT `Multiset.map_map` alone, else
`Real.log ∘ f` and `fun ζ => Real.log (f ζ)` are distinct atoms and linarith/ring fail.
For sum-splitting lemmas, prove a `∀ s : Multiset ℂ` version by `Multiset.induction_on`
inside the proof rather than reusing a comp-shaped helper.
