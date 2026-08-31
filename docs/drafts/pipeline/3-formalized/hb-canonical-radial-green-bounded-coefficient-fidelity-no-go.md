# HB canonical radial Green bounded-fidelity no-go

- **ID:** HB-RG-BF-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · HB bounded-noncompact/full-causal survivor
- **Statement:** No bounded complex-linear operator on the Xi-copy Hilbert packet has every canonical diagonal matrix element equal to the BM radial Green-jump coefficient.

## Goal

Kill bounded-noncompact, coefficient-faithful realization of HB's full causal Green discontinuity:

`full canonical radial fidelity → coefficients with Im = -Im ρ → unbounded diagonal data → no bounded operator`.

The survivor is exact: coefficient-faithful HB must use a genuinely unbounded operator/domain, or change coefficient fidelity/topology before projection.

## Gates

- [x] 0 → 1: exact corpus chain and attack identified
- [x] 1 → 2: dependency-closed paper proof and hostile scope audit
- [x] 2 → 3: closed Lean capstone, direct Lean pass, targeted build, axiom audit, umbrella wiring
- [ ] 3 → 4: publication-ready

## Corpus and literature audits

Corpus search found the separate ingredients but no synthesis: `hbXiPeierlsRadialWeight_im`, `tendsto_xiOrderedPositiveOrdinate_atTop`, Xi-copy enumeration, and the generic operator-norm diagonal bound. Existing HB no-gos cover compact, Hilbert--Schmidt, finite-rank, or nonselective arbitrary bounded cancellation, not bounded realization of all canonical radial Green coefficients.

Primary-source searches through 2026-08-31 found radial QNM Green-residue constructions and spectral/RH operator proposals, but no BM/Xi coefficient-fidelity boundedness theorem. Closest physical comparison: Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935; closest 2026 Schwarzschild radial Green comparison: Kehagias--Riotto, arXiv:2606.24812.

## Paper proof `[PROVED HERE]`

Fix overtone `n` and bounded `K`. Positive Xi copies `q_k` satisfy `Im(q_k)=γ_k→∞`. The canonical coefficient has imaginary part `-γ_k`, hence norm at least `γ_k`. For the coordinate unit vector `e_k`, Cauchy--Schwarz and boundedness give `|⟪e_k,K e_k⟫|≤‖K‖`. Coefficient fidelity identifies this matrix element with the canonical coefficient, contradicting `γ_k>‖K‖`. No diagonality assumption is used.

## No-go closure

- **Exact killing mechanism:** Xi height occurs unchanged in imaginary part of canonical radial Green coefficient.
- **Strongest positive survivor:** arbitrary cross-fibre mixing cannot hide unbounded prescribed diagonal data; exact coefficient-faithful realization is necessarily unbounded.
- **New insight:** bounded-noncompact HB cannot retain full canonical radial coefficient fidelity; remaining full-causal operator route must specify an unbounded domain/topology.
- **Status:** theorem `d4HBCanonicalRadialGreenBoundedCoefficientFidelityRouteKilled` in `ThetaCuspHawkingHBCanonicalRadialGreenBoundedCoefficientFidelityNoGo.lean`. `lake env lean` and target-only `lake build` pass. Axioms: `propext`, `Classical.choice`, `Quot.sound`. Global lint reaches the new module but is blocked by 17 unrelated pre-existing unwired modules.
