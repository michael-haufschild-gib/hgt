# Pointed Krein relation and linear-anchor boundary (2026-08-18)

Formal module: `formal/GaloisForLFunctions/RHTower/SourceHorizontalSecondCartierPointedKreinBoundaryRelation.lean`.

Producer already formalized:
- pointed jet (K=ℂ⊕ℂ²), Hermitian nondegenerate indefinite form;
- boundary relation with vertical fibre exactly (ℂU), provably not graph;
- actual Xi/Gamma-Wold coefficient, prime character, orientation swap, and support multiplicity;
- nonzero ghost (G) is null but nonradical;
- prime transfer is Krein-isometric for every nonzero character;
- any antisymmetric additive order rejects simultaneous (0≤G) and (0≤-G).

New sharp boundary:
- `sourceHorizontalSecondCartierPointedKrein_anchor_covariance_norm_eq_one`: any complex-linear anchor (A:ℂ²→ₗℂ), nonzero on source ghost and intertwining reciprocal-star source transfer with unit-anchor λ action, forces ‖λ‖=1.
- `sourceHorizontalSecondCartierPointedKrein_strictRight_no_linear_transverse_anchor`: such anchor cannot exist on any strict-right Xi fibre.

Interpretation: relation is genuine survivor and avoids scalar/multiplicative/Hardy firewalls, but admits all nonzero λ and is not itself RH. Exact open core is source-derived Xi-selected nonlinear boundary condition/polarization or genuinely relational transversality coupling reciprocal-star ghost leg to unit leg without reducing to a complex-linear section.

Verification:
- direct `lake env lean` passed;
- exact leaf `lake build GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierPointedKreinBoundaryRelation` passed;
- #print axioms on producer and new boundary theorems: only propext, Classical.choice, Quot.sound;
- umbrella import present; no umbrella build;
- formal lint reports only pre-existing unrelated unreachable modules.
- frontier map and Stage-3 card updated.