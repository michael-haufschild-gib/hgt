# Polar-constrained right continuity of the restricted Weil floor — Lean certificate

- **ID:** `WEIL-ENTRY-001-L1`
- **Stage:** 3-formalized
- **Parent card:** `1-in-progress/weil-positivity-soft-prime-entry.md` (Theorem D, the direction
  needed for propagation past a prime threshold)
- **Module:** `GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarConstrainedRightContinuity`
  (imports `SuzukiGroundEnergyContinuity`; wired after it in `RHTower.lean`)
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on every theorem; lint clean; no
  hypotheses beyond the floor being propagated.

## Statements

Let `J_a = ccmArchimedeanFormToAperture a` embed the exact CCM form domain into the aperture
Hilbert space and `Q_a = ccmRestrictedWeilSourceQuadratic a` be the literal source form
(archimedean weight, indefinite polar rank-two term, finite von Mangoldt translation block).

- `IsPolarConstrained a u`: `⟨p_a(½), J_a u⟩ = 0 ∧ ⟨p_a(−½), J_a u⟩ = 0`.
- `isPolarConstrained_iff_of_val_eq`: the constraints are invariant under aperture extension
  (`inner_ccmPolarApertureVector_eq_of_val_eq`).
- `IsPolarConstrained.smul`: invariant under scaling (through `Submodule.coe_inner`,
  `Submodule.coe_smul`, `inner_smul_right`; the direct rewrite on the subtype fails).
- `polarConstrained_floor_of_le`: a constrained floor `m‖J_b v‖² ≤ Q_b v` at `b` gives the same
  floor at every `a ≤ b`.
- `exists_polarConstrained_floor_suzukiRightAperture`: if `m‖J_a u‖² ≤ Q_a u` for all constrained
  `u` at `a`, then for every `ε > 0` some canonical right aperture `a + 1/(k+1)` carries the
  constrained floor `m − ε`.
- `exists_polarConstrained_floor_right`: the same on the whole interval `c ≤ a + δ`.
- `exists_polarConstrained_pos_floor_right`: a strictly positive constrained floor `m` at `a`
  gives the floor `m/2` on `[a, a + δ]`.

## Proof (as formalized)

Suppose every right aperture carries a constrained counterexample `v_k` with
`Q(v_k) < (m − ε)‖J v_k‖²`. Then `J v_k ≠ 0` (else `Q(v_k) = 0`, via `Q(0 • u) = 0`). Normalize,
`‖J w_k‖ = 1`, `Q(w_k) < m − ε`, still constrained. Extend to the fixed aperture `b = a + 1`
(`exists_ccmArchimedeanFormDomain_extension`); the source, the norm and the constraints are
unchanged (`_eq_of_val_eq` lemmas). The form-domain norms are bounded by
`ccmArchimedeanFormNorm_sq_le_source_add_remainder_norm_mass`, so compactness of the form embedding
(`isCompactOperator_ccmArchimedeanFormToAperture`) gives a subsequence converging to `fstar`;
`indicatorCutoff_limit_suzukiRightAperture` places `fstar` in the aperture `a`; the norm is `1`;
the closed sublevel set `isClosed_ccmRestrictedWeilSource_sublevel` gives `w'` with
`J_b w' = fstar` and `Q_b(w') ≤ m − ε`; continuity of the two pole coefficients keeps `fstar`
constrained; `exists_ccmArchimedeanFormDomain_of_limit_support` transfers `w'` to a constrained
`u` at `a` with `‖J_a u‖ = 1` and `Q_a(u) ≤ m − ε`, contradicting the floor `m` at `a`.

## What this closes on the parent card

Theorem D's continuity input in the direction that matters: strict positivity of the constrained
form at a threshold aperture propagates to larger apertures, the term of the entering prime
included. What remains external is the strict positivity at `√2` itself (Theorem C, which uses
Connes–Consani's Sonin inequality); the corpus's `SoninStrictPositivityTransfer` holds the
abstract mechanism for it.
