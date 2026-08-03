# Claim trace: Stokes--Cartan one-defect law

Audit date: 2026-08-03

This ledger separates new claims, prior geometric inputs, and formally checked algebra. Existing
contact-tomography work is input; it is not relabelled as new.

| ID | Paper claim | Status | Dependency | Lean witness |
|---|---|---|---|---|
| G0 | Every relevant core has one simultaneous rooted contact realization, and a generic class has all Stokes circles at infinity | Prior geometric input, reproved at paper level from contact coarea and cited | Douçot 2021 diagram invariance; Douçot 2026, Thms. 1.4--1.6; explicit loop/edge formulae in Douçot 2025 | `StokesDecoratedCore.RootedRealization`; prior modules `StokesContactTomography`, `StokesRootedCutConstruction` |
| N1 | `C = I + sum_e ell_e u_e u_e^T - (H-1) r r^T` | **New central law** | G0 plus exact definition of complementary contact | `CertifiedFissionDatum.cartanEntry_eq_oneDefect`, `cartanMatrix_eq_positiveMatrix_sub_outer` in `StokesCartanLorentzCapacity.lean` |
| N2 | Exact quadratic form: positive terminal squares + positive cut-conormal squares - one total-rank square | **New** | N1 | `cartanQuadratic_eq_oneDefect`, `positiveQuadratic_eq_squares` |
| N3 | Cartan form is positive on `ker(r^T)` and has negative index at most one | **New** | N2 | `cartanQuadratic_pos_of_totalRamification_eq_zero`, `cartanForm_sigNeg_le_one` |
| N4 | Capacity normal form and finite/affine/Lorentz trichotomy controlled by `Omega=c^{-1}-lambda` | **New** | N1 and positive definiteness of `P` | `cartanQuadratic_eq_centered_capacity`, `cartanQuadratic_pos_of_capacityGap_pos`, `cartanQuadratic_nonneg_of_capacityGap_eq_zero`, `cartanForm_sigNeg_eq_one_of_capacityGap_neg` |
| N5 | Affine kernel is exactly the capacity line; negative and zero modes cannot coexist | **New** | N4 | `cartanQuadratic_eq_zero_of_capacityGap_eq_zero_iff_capacityLine`, `capacityVector_ne_zero` |
| N6 | `det C = det(P)c Omega` | **New Stokes consequence**; determinant lemma is classical | N1 | `cartanMatrix_det_eq_capacity` |
| N7 | Root extension updates capacity by `c/(1+tc)` and leaves `Omega` and `det(P)c` invariant | **New intrinsic/gauge law**; Sherman--Morrison is classical | N1/N6 | `capacity_update`, `capacityGap_update_invariant`, `determinant_capacity_prefactor_invariant` in `StokesCartanCoronaCapacity.lean` |
| N8 | Reciprocal capacity is effective tree resistance; exact corona pruning uses parallel/series reduction | **New geometric interpretation and recursion**; electrical identities are classical | N4 plus current change `m_i=r_i x_i` | `parallel_completion`, `parallel_completion_effectiveResistance`, `series_extension_gap_invariant` |
| N9 | Arbitrary finite type-A legs add positive fluctuation squares and cannot create a second defect | **New full-diagram law** | N2 plus exact path completion | `TypeALeg.path_completion`, `family_completion`, `fullCartanQuadratic_eq_completed`, `fullCartanQuadratic_pos_of_totalRamification_eq_zero` in `StokesCartanTypeALegs.lean` |
| N10 | Wild dimension is one total-rank square gain minus explicit positive leg, terminal, and cut-conormal defects | **New identity** built on prior dimension formula | Douçot 2021 dimension formula plus N9 | `wildDimension_eq_conservation` |
| N11 | Principal positive Hessian is `D + sum ell_e dnu_e tensor dnu_e`; multi-Rees nonnegative specializations remain one-defect | **New finite microlocal formulation** | N2/N9 | Gram and hyperplane pieces formalized by `positiveQuadratic_eq_squares`, `fullPositiveQuadratic_eq_completed`; paper proof handles symbolic Rees weights |
| N12 | Every type-A genus-zero diagram is finite, affine, or Lorentzian | **New global theorem** | G0 and N9; only diagram equality is transported | Core and leg algebra formalized; global geometric transport is cited/paper-level |
| N13 | For graph adjacency `B`, `lambda_2(B) <= 2`, with simple affine eigenvalue and exactly one eigenvalue above 2 in Lorentz phase | **New spectral/Kac--Moody exclusion** | N12 and spectral mapping `Spec(2I-B)=2-Spec(B)` | N3--N5 formalize inertia premise; finite spectral translation is paper-level |

## Formal trust audit

- New modules contain no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations.
- Principal capstones report only `propext`, `Classical.choice`, and `Quot.sound` under
  `#print axioms`.
- Formal lint passed before manuscript audit.
- Final direct module builds and targeted `lake build` audit are recorded in `HOSTILE_REVIEW.md`.

## Deliberately unclaimed

- No new irregular Riemann--Hilbert equivalence.
- No analytic isomorphism theorem for all weak representations.
- No identification of `ell_e` with characteristic-cycle or vanishing-cycle multiplicities.
- No converse claiming every one-defect matrix is geometrically realizable.
- No statement outside type-A genus zero.
