# HB canonical radial Green bounded-fidelity no-go

- **ID:** HB-RG-BF-NOGO
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` · HB bounded-noncompact/full-causal survivor
- **Statement:** No bounded complex-linear operator on the Xi-copy Hilbert packet has every canonical diagonal matrix element equal to the BM radial Green-jump coefficient.

## Goal

Kill bounded-noncompact, coefficient-faithful realization of HB's full causal Green discontinuity. Proof chain: full causal radial incidence fixes `hbXiPeierlsRadialWeight`; its imaginary part is `-Im ρ`; ordered positive Xi ordinates tend to infinity; bounded operators have uniformly bounded unit-vector diagonal matrix elements. Survivor: coefficient-faithful HB must use a genuinely unbounded operator/domain, or abandon the canonical full Green jump before projection.

## Gates

- [x] 0 → 1: exact corpus declarations and proof chain identified
- [ ] 1 → 2: complete paper proof and novelty audit
- [ ] 2 → 3: closed Lean capstone, targeted build, axiom/lint audit, umbrella wiring
- [ ] 3 → 4: publication-ready

## Approach

Enumerate positive Xi copies by increasing multiplicity-aware ordinate. Test a putative bounded operator on the associated coordinate unit vectors. Cauchy--Schwarz and the operator norm uniformly bound its diagonal matrix elements, while `|Im(hbXiPeierlsRadialWeight)|` tends to infinity.

## No-go closure

- **Exact killing mechanism:** unbounded Xi height is already present in the imaginary part of every canonical radial Green coefficient.
- **Strongest positive survivor:** arbitrary cross-fibre mixing cannot hide unbounded prescribed diagonal data; every exact coefficient-faithful realization is unbounded.
- **New insight:** the bounded-noncompact HB branch survives only by changing coefficient fidelity/topology; full canonical radial fidelity forces an unbounded Green operator.
- **Status:** corpus novelty audit in progress; paper proof dependency-closed modulo routine norm inequalities.
