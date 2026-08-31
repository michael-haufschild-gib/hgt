# Arbitrary Hilbert--Schmidt Hermitian completion fidelity no-go

- **ID:** HB-HS-HERMITIAN-COMPLETION-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `ThetaCuspHawkingReducedSecondOrderChiralTeukolskyGradeIncidence.lean`, `ThetaCuspHawkingHBReducedTeukolskyHermitianDilationFidelityNoGo.lean`, `HermitianDilationSecondJetObstruction.lean`
- **Statement:** No self-adjoint Hilbert--Schmidt completion containing a faithful nonzero off-diagonal source entry can have the same Hilbert--Carleman determinant as the rank-one holomorphic source kernel, irrespective of all other finite- or infinite-rank counterterms.

## Result

**[PROVED HERE]** Let `L : kappa × kappa -> C` be Hilbert--Schmidt and self-adjoint. Let `i != j` and `L(i,j)=c`. Let `K_c=c e_00` be the rank-one source kernel. If

`det_2(1-zL) = det_2(1-zK_c)` for every complex `z`,

then `c=0`.

Consequently, for nonzero Einstein seed and every tilted Xi copy, the exact reduced doubled-grade Einstein--Teukolsky source coefficient cannot be embedded faithfully as an off-diagonal entry of any self-adjoint Hilbert--Schmidt angular completion preserving its source determinant.

## Proof

Equality of entire Hilbert--Carleman determinants gives equality of Taylor coefficient two. The corpus second-jet identity gives

`[z^2] det_2(1-zT) = -tr(T^2)/2`.

Self-adjointness of `L` converts its holomorphic square trace into total Hilbert--Schmidt energy:

`tr(L^2)=<L,L>_HS=||L||_HS^2`.

For `K_c`, rank-one composition gives `tr(K_c^2)=c^2`. Hence determinant fidelity forces

`||L||_HS^2 = c^2`.

Taking complex norms yields `||L||_HS^2=|c|^2`. But self-adjointness and source fidelity give `L(j,i)=conj(c)`. Since `i != j`, these are two distinct entries of the Hilbert--Schmidt sum, so

`||L||_HS^2 >= |L(i,j)|^2+|L(j,i)|^2 = 2|c|^2`.

Thus `2|c|^2 <= |c|^2`, forcing `c=0`.

For the exact source coefficient

`c(q)=d4ThetaReducedSecondOrderChiralTeukolskyGradeSource amplitude mixed anti q (2s(q))`,

the corpus proves `c(q) != 0` exactly when `Re(q) != 1/2` for nonzero seed. Therefore determinant-faithful self-adjoint Hilbert--Schmidt completion is impossible on every tilted Xi fibre.

## Exact RH chain and route consequence

The coefficient is the actual mixed-horizon HB optical source projection. Existing exact complex transmutations map it through nowhere-zero factors to FZZ-P information force, every PW-B recoil imbalance, and RBH multiplicity-leading imbalance. Universal source extinction is the shared four-route Ward endpoint and is RH-equivalent.

This theorem kills a proposed producer rather than assuming that endpoint: finite or infinite self-adjoint Hilbert--Schmidt angular completion cannot convert forced tilted leakage into a determinant-faithful conservative carrier. Extra diagonal blocks, extra sectors, nonlocal couplings, and arbitrary Hilbert--Schmidt counterterms do not help.

## No-go closure

- **Exact killing mechanism:** quadratic determinant fidelity demands one copy of source square mass; Hermitian source fidelity necessarily stores two conjugate copies.
- **Strongest positive survivor:** sharp representation boundary `source-faithful + self-adjoint + Hilbert--Schmidt + determinant-faithful => source=0`. A surviving construction must abandon at least one of self-adjointness, Hilbert--Schmidt/Fredholm regularity, coefficient fidelity, or determinant fidelity.
- **New insight:** failure is not locality, dimension, canonical block choice, or missing counterterm. It is an invariant factor-of-two energy obstruction already visible in one faithful off-diagonal pair.
- **Novelty status:** internal corpus search found only standard/canonical chiral dilation rigidity, not arbitrary self-adjoint Hilbert--Schmidt completions. August 2026 primary-source audit found no theta/Birmingham--Mokhtari use of this arbitrary-completion obstruction. General trace identities are standard; source-specific route-class theorem and four-route consequence are the new result.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingHBArbitraryHilbertSchmidtHermitianCompletionFidelityNoGo`
- Generic rigidity: `selfAdjoint_sourceBlock_entireDet2_ne_diagKernel`
- Exact tilted-source theorem: `d4HBReducedTeukolskyArbitraryHermitianCompletion_tilted`
- Closed capstone: `d4HBReducedTeukolskyArbitraryHermitianCompletionFidelityRouteKilled`
- `lake env lean` PASS
- Targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingHBArbitraryHilbertSchmidtHermitianCompletionFidelityNoGo` PASS
- `#print axioms`: only Lean/mathlib standard `propext`, `Classical.choice`, `Quot.sound`; no added axiom
- Scoped forbidden-declaration scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- Global lint currently fails only on unrelated concurrently added modules missing umbrella imports; this module is umbrella-reachable and absent from every lint error

## Gates

- [x] 0 → 1  conjecture frozen with falsifiers and exact route chain
- [x] 1 → 2  dependency-closed paper proof
- [x] 2 → 3  Lean module, umbrella, targeted build, scoped lint/axiom audit
- [ ] 3 → 4  publication-ready standalone note

## Log

- 2026-08-31 — paper proof closed after arbitrary-index scratch Lean validation
- 2026-08-31 — Lean formalization closed; module wired into `RHTower.lean`; targeted build passed
