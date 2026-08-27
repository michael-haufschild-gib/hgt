# BM second-harmonic Hermitian-source orientation no-go

- **ID:** HB-BM-HSONG
- **Stage:** 3-formalized
- **Type:** NO-GO + EXACT RECEIVER
- **Parent:** HB
- **Statement:** `[LEAN-PROVED] [NEW] [NO-GO]` Literal Hermitian angular--Einstein source weights satisfy forced reflected complex cancellation law exactly on critical wall, where both weights vanish. Off wall, actual norm-square source cannot supply missing Peierls orientation.

## Goal

Test actual corpus second-harmonic source coefficient, rather than arbitrary positive weights,
against unique complex orientation forced by reflected BM current cancellation.

## Gates

- [x] 0 → 1 in-progress: literal Hermitian-weight compatibility conjecture frozen after corpus search
- [x] 1 → 2 fully-proven: coefficient compatibility and reflected-current zero locus
- [x] 2 → 3 formalized: direct Lean, targeted build, umbrella, axiom audit
- [ ] 3 → 4 publication-ready: external priority review

## Exact frozen claims

Let `A(q)` be literal angular--Einstein polarized source amplitude and
`w(q)=normSq(A(q))`. Let `r_n(q)=-λ_n(q)/λ_n(Jq)` be unique reflected complex cancellation ratio.
Then

`w(Jq) = w(q) r_n(q)  ↔  Re(q)=1/2`.

Equivalently, reflected current `w(q)J_n(q)+w(Jq)J_n(Jq)` vanishes exactly on critical wall.
Universal vanishing over Xi support is equivalent to RH.

## Complete paper proof

Both `w(q)` and `w(Jq)` are real. Off wall, angular mixing is nonzero; nonlinear Einstein carrier
at seed one is nonzero; hence `w(q)≠0`. Taking imaginary parts of proposed coefficient law gives
`w(q) Im(r_n(q))=0`, contradicting nonzero weight and previously proved `Im(r_n(q))≠0`. On wall,
angular mixing and its reflected copy vanish, so both weights are zero and compatibility holds.
Exact reflected-current classifier converts coefficient compatibility into current zero locus.

## Hostile review and novelty verdict

- This theorem uses literal source amplitude already present in corpus; it does not assume an
  arbitrary positive cone.
- It rules out Hermitian norm-square realization, not every possible augmented Peierls pairing.
- Sourced Teukolsky and conserved-current literature located in narrow primary-source searches does
  not state this coefficient incompatibility or its Xi critical-wall classification.

Verdict: imaginary-part obstruction `[REDISCOVERED]`; coefficient-faithful BM/Xi Hermitian-source
no-go `[NEW] [NO-GO]`, external priority provisional.

Primary audit: Birmingham--Mokhtari, arXiv:hep-th/0609028; Green et al., arXiv:2210.15935;
Spiers--Pound--Moxon, arXiv:2305.19332; Spiers, arXiv:2402.00604.

## No-go closure

- **Exact killing mechanism:** squaring source amplitude destroys phase required by nonreal ratio.
- **Strongest positive survivor:** literal Hermitian reflected current is exact critical-wall receiver,
  and universal cancellation is exactly RH.
- **New insight:** remaining producer must transport unsquared complex phase with reflection law
  `r(Jq)=r(q)⁻¹`; no Hermitian source normalization can do it off wall.
- **Status:** dependency-closed paper proof and Lean formalization complete.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSecondHarmonicHermitianSourceOrientationNoGo.lean`
- Literal source weight:
  `d4BMXiSecondHarmonicHermitianSourceWeight`
- Compatibility classifier:
  `d4BMXiSecondHarmonicHermitianSourceOrientationCompatible_iff`
- Reflected-current classifier:
  `d4BMXiSecondHarmonicHermitianSourceReflectionCurrent_eq_zero_iff`
- Global endpoint:
  `forall_d4BMXiSecondHarmonicHermitianSourceReflectionCurrent_eq_zero_iff_rh`
- Direct `lake env lean` passed.
- Targeted module build passed.
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.

## Log

- 2026-08-27 — conjectured from literal source norm-square factorization and nonreal forced ratio.
- 2026-08-27 — exact compatibility no-go and Lean proof completed.
