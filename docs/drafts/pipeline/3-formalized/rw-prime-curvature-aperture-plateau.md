# Literal prime-curvature aperture plateau through invisible cutoff entries

- **ID:** RW-PRIME-CURVATURE-PLATEAU
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and audited Lean)
- **Source:** RW; exact multiplicative-cutoff API in `CCMPrimePoleJumpRates`.
- **Statement:** For every `2 < A < 5/2`, aperture `a=log A`, and real observable `f`, the actual prime Γ₂ at `log 2` equals its value at the established aperture `log(21/10)`. Hence the exact one-direction classification and sharp compact-source compensation hold throughout this whole aperture band.

## Dependency-closed paper proof

The literal signed index set contains all integers `2≤n≤floor(A²)`, in both orientations. Since `4<A²<25/4<7`, it contains 2, 3, 4 and may contain 5 or 6. No larger index occurs.

The four rows used by Γ₂ at `log 2` have multiplicative positions `q∈{2,1,2/3,1/2}`. Every base point is inside `[A⁻¹,A]`, since `A⁻¹<1/2≤q≤2<A`. The exact corpus rate formula is zero outside the target cutoff; inside it is

`Λ(n)(qn+1)/(n(q+1))` in the forward orientation, and

`Λ(n)(q+n)/(n(q+1))` in the backward orientation.

All targets for indices 2, 3, 4 are listed below; each cell is ordered by index.

| Base q | Backward targets | Forward targets |
|---|---|---|
| 2 | 1, 2/3, 1/2 | 4, 6, 8 |
| 1 | 1/2, 1/3, 1/4 | 2, 3, 4 |
| 2/3 | 1/3, 2/9, 1/6 | 4/3, 2, 8/3 |
| 1/2 | 1/4, 1/6, 1/8 | 1, 3/2, 2 |

The accepted targets lie in `[1/2,2]` and remain accepted throughout the band. Every rejected target is at most `1/3` or at least `8/3`, hence remains rejected because `A⁻¹>2/5>1/3` and `A<5/2<8/3`. Thus the existing four literal row identities hold with identical rates.

Every extra index/orientation is checked explicitly:

| Base q | n=5 backward | n=5 forward | n=6 backward | n=6 forward |
|---|---|---|---|---|
| 2 | 2/5 | 10 | 1/3 | 12 |
| 1 | 1/5 | 5 | 1/6 | 6 |
| 2/3 | 2/15 | 10/3 | 1/9 | 4 |
| 1/2 | 1/10 | 5/2 | 1/12 | 3 |

All backward targets are at most `2/5<A⁻¹`; all forward targets are at least `5/2>A`. These rates vanish regardless of their Mangoldt coefficient. This uses literal endpoint geometry, not an assumption that index 6 has zero weight.

Stronger visibility survivor, audited on paper before Lean: the same conclusion holds for every integer `n≥5`, independently of cutoff membership. Indeed `1/2≤q≤2` gives `q/n≤2/5<A⁻¹` and `qn≥5/2>A`. The Lean row proof can eliminate the entire higher-index tail symbolically rather than enumerating just 5 and 6. No additional analytic premise is introduced.

Expand `Γ₂=LΓ/2−Γ(f,Lf)` using the four rows. The rows and their targets are identical to those at `log(21/10)`, so the complete iterated energy agrees for every observable. The one-direction coefficients depend only on `log 2` and `log 3`, and are consequently unchanged.

All six sample positions `{1/2,2/3,1,4/3,3/2,2}` are strictly inside the aperture. Exact finite interpolation therefore transports every sharp normalized sample stencil to compact smooth exact-pole sources of arbitrarily small form norm and `|Q|` at each aperture in the band. The two-zero curvature repair similarly remains dense and preserves its own actual ground infimum `μ₀(a)`.

## New insight and limits

Cutoff membership and local curvature visibility have different thresholds: indices 5 and 6 may enter while this actual Γ₂ reader remains exactly unchanged. The completed constrained ground energy is strictly antitone in aperture by the corpus, so this fixed local prime-curvature reader does not track its changing floor. No statement about the full curvature field, integrated compensation, or the sign of `μ₀(a)` follows.

At `A=5/2`, the index-5 jump from q=2 to q=2/5 and its companion from q=1/2 to q=5/2 reach the closed endpoints. The old row argument therefore stops there. No assertion about the sign beyond this threshold is retained.

## Audit and continuation

- Corpus search before new code: `log cutoff` in `CCMPrimePoleJumpRates`; exact lexical `gammaTwo aperture` in `CCM`; exhaustive text search of the actual operator names supplements retrieval.
- Lean leaf: `formal/GaloisForLFunctions/RHTower/CCMPrimePoleCurvatureAperturePlateau.lean`, wired in `RHTower.lean`. Every row, index and orientation is covered; no case sampling, numerical experiments, new axioms, heartbeat overrides or full builds.
- Six public theorems: `higher_rate_zero`, `rowFor_eq_old`, `gammaTwo_eq_fixed`, `exists_constrained_rankOne_extremizer`, `constrained_rankOne_compensation_iff`, `exists_nonnegative_curvature_near_ground`.
- Named `lake --old --log-level=error build +GaloisForLFunctions.RHTower.CCMPrimePoleCurvatureAperturePlateau` passed. Required final direct `lake env lean GaloisForLFunctions/RHTower/CCMPrimePoleCurvatureAperturePlateau.lean` passed with no warnings. All six `#print axioms` checks in `/tmp/hgt-rw-plateau-axiom-audit.lean` passed; output `/tmp/hgt-rw-plateau-axiom-audit.txt` lists only `propext`, `Classical.choice`, `Quot.sound`.
- Public searches for prime Bochner aperture laws, Weil cutoff curvature and von-Mangoldt Γ₂ found no exact matching result. This remains a bounded novelty audit, with no claim of universal literature or training-data absence.
- Next candidate: boundary aperture `a=log 2`, where compact interior sources force both endpoint samples to vanish and may remove the negative direction completely. Exact determinant proof and formal audit remain open.
