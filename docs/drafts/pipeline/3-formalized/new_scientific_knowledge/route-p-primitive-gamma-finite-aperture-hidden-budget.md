# Route P primitive Gamma finite-aperture hidden budget

- **ID:** `route-p-primitive-gamma-finite-aperture-hidden-budget`
- **Stage:** 3-formalized
- **Label:** `P-G193`
- **Source:** P-G188 finite-aperture defect mass, P-G189 first flux, P-G192 retained Wold channel
- **Statement:** Replacing infinitesimal flux by finite-aperture Burnol defect mass produces a
  canonical antidiagonal current whose full ordered-pair hidden energy is exactly twice the square
  of total defect mass. This energy tends to zero at the balanced wall and therefore lies strictly
  inside P-G184's fixed positive source budget at some positive aperture.

## Conjecture loop

`C193-A` asked whether P-G192's infinitesimal hidden trace could be bounded directly by P-G184's
budget. That route would require a sharp global numerical estimate for the double-Green prime sum
and would compare an infinitesimal current with a finite conserved budget.

The pivot keeps aperture finite. Let

```text
m_c(i) = P-G188 Burnol aperture defect mass,
D(c)   = sum_i m_c(i),
A_c(i,j) = sqrt(m_c(i)m_c(j)),
W_c(i,j) = (A_c(i,j),-A_c(i,j)).
```

For `c>0`, every `m_c(i)` and `D(c)` is strictly positive. P-G189 gives
`D(c)/c -> sum_i J(i)` from the right, hence Lean proves `D(c)->0` without numerical estimates.

## Exact complete-energy law

The physical cooriented Gamma reporter kills every `W_c(i,j)`, while its retained resolved energy
is

```text
energy(W_c(i,j)) = 2 m_c(i)m_c(j).
```

Absolute summability and the product-tsum theorem give the complete ordered-pair identity

```text
sum_(i,j) energy(W_c(i,j)) = 2 D(c)^2.                 (1)
```

Consequently the left side of `(1)` tends to zero as `c->0+`. Since P-G184's cubic source trace
budget is strictly positive, sufficiently small positive apertures satisfy

```text
sum_(i,j) energy(W_c(i,j)) < P-G184 source budget.     (2)
```

This is a finite-time feasibility theorem, not the missing colligation. It does not yet prove that
visible transported energy plus `(1)` obeys one common conservation identity, nor does it map the
packet coefficient-faithfully to completed-Xi conormal residues.

## Higher universal principle

P-G190's nonzero first flux and P-G193's vanishing finite mass are compatible because the Wold
channel is born linearly in aperture while complete pair energy is quadratic. The obstruction was
an order mismatch: comparing a derivative current directly with a finite budget hides the small
parameter that makes lossless dilation possible.

Thus the correct object for the matrix-complete colligation is finite-aperture defect amplitude;
the double-Green flux is its tangent vector, not its finite energy.

## Hostile novelty audit

The corpus already had P-G188's scalar conservation law and P-G189's normalized first derivative.
It did not contain their matrix-complete antidiagonal lift, exact factorization `(1)`, the right-wall
vanishing of total pair energy, or positive-aperture budget feasibility `(2)`. The result does not
claim the still-missing visible/hidden coefficient transport.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaFiniteApertureHiddenBudget.lean
```

Capstones:

- `tendsto_routePPrimitiveBurnolApertureTotalDefectMass_zero`;
- `tsum_routePPrimitiveGammaFiniteApertureHiddenPairEnergy`;
- `tendsto_tsum_routePPrimitiveGammaFiniteApertureHiddenPairEnergy_zero`;
- `exists_positive_tsum_routePPrimitiveGammaFiniteApertureHiddenPairEnergy_lt_budget`.

Verification:

- `/tmp/pg193.lean`: `lake env lean /tmp/pg193.lean` passed cleanly;
- exact leaf build passed; no umbrella build run;
- `/tmp/pg193_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- targeted forbidden-declaration scan clean;
- umbrella import wired without building umbrella.

## Gates

- [x] infinitesimal-budget conjecture audited and pivoted
- [x] finite-aperture amplitude constructed
- [x] complete ordered-pair energy and summability proved
- [x] right-wall vanishing proved
- [x] positive-aperture strict budget feasibility proved
- [x] scratch verification
- [x] exact leaf build only
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [ ] couple visible and hidden packets in one source conservation identity
- [ ] land coefficient-faithfully on completed-Xi conormal matrix
- [ ] prove W-H184 unconditionally
- [ ] unconditional RH
