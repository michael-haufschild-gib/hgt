# HC54: HB source-FE line-conjugate permutation-kernel no-go (2026-08-28)

Formal module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceFELineConjPermutationKernelNoGo.lean`

Card: `docs/drafts/pipeline/3-formalized/hb-source-fe-line-conjugate-permutation-kernel-no-go.md`

Corpus-led conjecture and new closed results:
- Let R(q)=1-q, S(q)=conj(q), J(q)=1-conj(q) on multiplicity-exact Xi copies.
- R and S commute; J is involutive.
- Literal BM helicity factor, unit Einstein carrier, and complete unit source obey Schwarz conjugation.
- Source FE cocycle obeys `kappa(Sq)=conj(kappa(q))` and `kappa(Jq)*kappa(q)=1`, including critical-wall source extinction.
- Canonical kernel `K_J(q,r)=1` iff `r=Jq`, else zero, is symmetric, reflection-real, and an HC52 Ward kernel.
- Associated arbitrary-kernel packet form is unconditionally source-FE covariant.
- Testing either slot against basis vector at Jq reads coefficient at q; both radicals are zero on all finite packets.
- On every tilted q, Jq is neither q nor Rq. HC53's full within-orbit 2x2 block vanishes while this global form remains algebraically nondegenerate.

Interpretation: HC53's distinct-orbit survivor is real and canonical. Symmetry, reflection reality, and global algebraic nondegeneracy of an arbitrary fixed Peierls kernel cannot select RH. Remaining HB/FZZ-P/PW-B/RBH producer must select the literal local/diagonal physical pairing rather than the nonlocal FE-Schwarz permutation pairing.

Verification:
- Direct `lake env lean` passed.
- Target-only build passed `11922/11922`.
- All 21 public theorem axiom audits report only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella wired.
- No forbidden declarations; diff check passed.
- Formal lint has no HC54 failure; unrelated pre-existing umbrella reachability errors remain.
- HC54 scratch cleaned; no HC54 Lean/build process remained. Other users' unrelated Lean processes were preserved.

Bounded novelty audit found reflection-based conserved QNM bilinear forms (arXiv:2210.15935) and nonlinear QNM coupling work, but no Xi source-cocycle line-conjugate permutation-kernel classification.