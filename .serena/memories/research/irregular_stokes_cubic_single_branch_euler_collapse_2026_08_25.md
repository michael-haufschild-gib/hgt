# Cubic single-branch Euler collapse (2026-08-25)

Formalized concrete irregular microlocal RH obstruction in `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicSingleBranchEulerCollapse.lean`.

For local data with exactly one coefficient-generated Puiseux branch and one Stokes orbit at every marked point, unit Rees fusion satisfies
`globalReesWittForm genus d 1 x = 2 * (1 - genus) * commonRankLinear d x ^ 2`.
Local proof: terminal energy and rank-square each equal `x₀²`; canonical self-contact is zero, so local Witt form is `2r²`. Summing over `q=p+1` points and adding fusion `2(1-g-q)r²` cancels all slope/cover/puncture dependence.

Public consequences exclude completed-Xi cubic unit landing fibres in genus 0 and genus 1. Since a cubic landing has negative value and nonzero common rank, genus 0 gives positive `2r²`, while genus 1 gives zero. Thus any viable low-genus completed-Xi incidence requires genuine multibranch geometry somewhere.

Public declarations:
- `RHTower.routePPrimitiveGammaJuliaStokesSingleOrbitBranchUnitReesWittForm_eulerCollapse`
- `RHTower.not_nonempty_routePPrimitiveGammaJuliaStokesCubicSphereUnitLandingFiber_singleOrbitBranch`
- `RHTower.not_nonempty_routePPrimitiveGammaJuliaStokesCubicTorusUnitLandingFiber_singleOrbitBranch`

Targeted module elaboration passed. `#print axioms` for exactly these declarations returned `[propext, Classical.choice, Quot.sound]`. No umbrella/full build or global lint. Temporary scratch and build `.olean` files removed. Card promoted to `docs/drafts/pipeline/3-formalized/route-p-cubic-single-branch-euler-collapse.md`. Frontier map remained read-only.