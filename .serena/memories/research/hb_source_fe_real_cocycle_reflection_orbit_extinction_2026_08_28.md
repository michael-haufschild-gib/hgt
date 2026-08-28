# HC53: HB source-FE real cocycle and reflection-orbit extinction (2026-08-28)

Formal module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceFERealCocycleReflectionOrbitExtinction.lean`

Card: `docs/drafts/pipeline/3-formalized/hb-source-fe-real-cocycle-reflection-orbit-extinction.md`

New closed results:
- Exact literal carrier factorization `C(1-s) C(s) = (s(1-s))^2 (s(1-s)+6)/64`.
- In open strip at nonzero height, reality of this product forces `Re(s)=1/2` by a positive-cofactor factorization of its imaginary part.
- Literal BM unit-source FE cocycle is real iff its actual Xi copy lies on critical line.
- For a reflection-real Ward kernel, nonzero reflected-pair entry `K(q,Rq)` forces criticality.
- On every tilted reflection orbit, all four entries of the full `2x2` kernel block vanish.
- Reflection-real kernel nonzero on every reflected pair has full packet covariance iff RH.

Interpretation: HC52 diagonal extinction did not exclude mixed-copy/reflection-pair forms. HC53 closes that loophole. Any off-RH fixed Ward kernel must couple distinct functional-equation orbits.

Verification:
- Direct `lake env lean` passed.
- Target-only `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFERealCocycleReflectionOrbitExtinction` passed (`11921/11921`).
- All six public theorem axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella wired.
- Formal lint has no HC53 failure; remaining errors are unrelated pre-existing umbrella reachability gaps.
- No forbidden declarations; `git diff --check` passed; scratch and Lean processes cleaned.

Bounded novelty audit found no Xi-source cocycle reality or reflection-orbit kernel rigidity theorem in corpus or targeted primary literature (arXiv:2210.15935, arXiv:2604.13182).