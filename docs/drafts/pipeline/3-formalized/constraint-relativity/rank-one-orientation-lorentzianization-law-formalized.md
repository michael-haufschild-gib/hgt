# Rank-one orientation and Lorentzianization law — formalized

- **ID:** `rank-one-orientation-lorentzianization-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `rank-one-orientation-lorentzianization-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.RankOneOrientation` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/RankOneOrientation.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

§2, the absolute source quotient:

1. `IsAbsoluteSplitting` — **card `(2.2)`**: `D H + j T = 1`, `T D = 0`, `T j = 1`, over an
   arbitrary commutative ring, with no finiteness or dimension hypothesis.
2. `IsAbsoluteSplitting.isCompl` — **card `(2.3)`, first box**: `A₂ = im D ⊕ j(O)`.
3. `IsAbsoluteSplitting.range_le_ker`, `IsAbsoluteSplitting.quotEquiv`,
   `IsAbsoluteSplitting.quotEquiv_mk` — **card `(2.3)`, second box**: `A₂ / im D ≅ O`, with the
   inverse induced by the section `j`.
4. `IsAbsoluteSplitting.observer_decomp` — **card `(2.4)`**: `F = (F j) T + (F D) H`.
5. `IsAbsoluteSplitting.observer_factors` — a boundary-blind observer (`F D = 0`) factors through
   the absolute coordinate `T`; `IsAbsoluteSplitting.factor_unique` — that factorization is unique,
   because `T j = 1` makes `T` surjective.

5b. `isAbsoluteSplitting_prod`, `isAbsoluteSplitting_prod_observer_ne_bot` — **the splitting
    datum exists**: for arbitrary `A₁` and `O` the product `A₁ × O` carries a canonical absolute
    splitting (inclusion, projection, retraction, section), with nonzero absolute part whenever `O`
    is nonzero.  Items 1–5 are therefore statements about an inhabited class, not vacuous ones.

§3, coframe before metric:

6. `portVector`, `inner_portVector`, `portVector_ne_zero` — Riesz representation of the port `M`.
7. `portScale`, `portScale_pos` — **card `(3.2)`**: `c = M(r) = ⟪r,r⟫ > 0`.
8. `portAxis`, `map_portAxis` — **card `(3.2)`**: `M(u) = 1` for `u = r/c`.
9. `inner_portAxis_right`, `inner_portAxis_left`, `inner_portAxis_self`, `map_transverse`,
   `inner_transverse_portAxis` — **card `(3.2)`**: `V = ker M ⊕ ℝu`, `P`-orthogonally.
10. `portForm`, `portOmega`, `portForm_eq` — **card `(3.3)`**: `Q(x) = P(z,z) + Ω t²` with
    `Ω = c⁻¹ + Γ`.
11. `portForm_pos_of_map_eq_zero` — the transverse form is positive definite.
12. `finrank_le_one_of_portForm_nonpos` — **card `(3.5)`**: every subspace on which `Q ≤ 0` has
    dimension at most one, i.e. `ind₋(Q) + dim Rad(Q) ≤ 1`.  This is proved uniformly for all three
    phases and needs no finite-dimensionality of `V`.
13. The trichotomy **card `(3.4)`**: `portForm_pos_of_omega_pos` (`Ω > 0`, positive definite),
    `portForm_eq_zero_iff_of_omega_zero` (`Ω = 0`, radical is exactly `ℝu`),
    `portForm_portAxis` (`Q(u) = Ω`, so `Ω < 0` gives one timelike direction) together with item 11
    (positive on `ker M`), which is the signature `(dim V − 1, 1)`.
14. `map_ne_zero_of_portForm_neg` — **card `(4.1)`**: the timelike set misses `ker M`, so it is
    separated by the sign of `M`.

§4, time reversal and orientation erasure:

15. `portReflect` — **card `(4.2)`**: `Θ(z + t u) = z − t u`.
16. `portReflect_of_map_eq_zero`, `portReflect_portAxis`, `map_portReflect`,
    `portReflect_involutive` — `Θ` fixes `ker M` pointwise, negates the axis and the port, and is an
    involution.
17. `inner_portReflect` — `Θ` is `P`-orthogonal; `portForm_portReflect` — `Θ` preserves `Q`.
18. `eq_portReflect` — **Proposition 4.1**: `Θ` is the *unique* orthogonal map fixing `ker M`
    pointwise and negating `M`.
19. `sq_map_portReflect` — every reader built from `P(z,z)`, `M(x)²` or `Q(x)` is `Θ`-invariant and
    so cannot recover the sign of `M(x)`.
20. `exp_map_portReflect_ne` — positivity alone does not erase orientation: `exp ∘ M` is positive
    and separates `x` from `Θx`.

§5, the reciprocal-flow no-go:

21. `binQuad`, `binQuad_diag_eq_zero` — **card `(5.1)`**: invariance under `(a,b) ↦ (e^{sμ}a,
    e^{−sμ}b)` for all `s` forces `A = D = 0`.
22. `binQuad_eq_zero_of_nonneg` — **Theorem 5.1**: an invariant positive semidefinite quadratic
    form is identically zero.

§7, the component countermodel:

23. `two_port_negative_definite`, `two_port_nonpos` — **card §7**: with two independent ports
    `P − 2M₁² − 2M₂² = −(x² + y²)` is nonpositive on a two-dimensional space, so the rank-one
    bound of item 12 is genuinely a one-port statement.

## Scope

§6 (corpus instantiation) and §8 (predictions) are explicitly conjectural in the card — the card
itself says that without the identification `(6.3)` the one-port conjunction is a synthesis, not a
theorem.  Nothing there is formalized, and §9 lists exactly what the card does not imply.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/RankOneOrientation.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.RankOneOrientation          # green
```
