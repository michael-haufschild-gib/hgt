# HB source-FE modular Bogoliubov dilation no-go

- **ID:** HC79
- **Stage:** 3-formalized
- **Type:** THEOREM / EXACT NONLINEAR SCATTERING CLASSIFICATION / NO-GO
- **Source:** read-only `rh-current-frontier-map.md` · shared HB/FZZ-P/PW-B/RBH source-Ward core

## Goal

Test the strongest remaining conservative-scattering loophole against the literal nonlinear
Birmingham--Mokhtari source functional-equation cocycle. Canonically orient every reflection orbit
toward the branch on which cocycle squared gain is at least one, then construct the minimal
two-mode bosonic `SU(1,1)` dilation of that exact gain.

Frozen claim: every Xi reflection orbit, including every tilted orbit, admits this exact
source-faithful CCR dilation unconditionally. Its partner occupation is zero exactly on the
critical wall and strictly positive off it. Consequently bosonic CCR, signed-Hermitian
conservation, and conservative KMS-style two-mode completion cannot force the missing Ward law.
The positive survivor is a canonical reflection-invariant source partner-production number whose
universal extinction is exactly RH and whose pointwise extinction is exactly HB optical darkness,
FZZ-P equilibrium, PW-B balance, and canonical RBH balance.

This is not a numerical estimate. It classifies the full reflected nonlinear source orbit inside
the physical `SU(1,1)` scattering geometry.

## Gates

- [x] 0 → 1 in-progress: corpus audit; exact statement frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof and bounded primary-literature audit
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready: independent mathematical review and broader novelty search

## Corpus audit

- `[CORPUS]` `ThetaCuspHawkingBMSourceFECocycleHyperbolicModulusOrientation.lean` proves the literal
  source cocycle expands precisely left of the wall, contracts precisely right of it, has unit
  gain precisely on the wall, and has reciprocal reflected gain.
- `[CORPUS]` `ThetaCuspHawkingBogoliubovCCRCompletionEndpoint.lean` defines
  `IsTwoModeBosonicCCR` and proves a generic pointwise squeeze completion for the theta Born
  amplitude. It does not construct a reflection-orbit completion of the literal BM source-FE
  cocycle or identify its partner number with the four-route Ward locus.
- `[CORPUS]` `ThetaCuspHawkingSuzukiWallKMSCommutatorEndpoint.lean` proves exact Hawking KMS
  `SU(1,1)` scattering and signed-Hermitian conservation, but not the source-cocycle orbit law.
- `[CORPUS]` `ThetaCuspHawkingBMCrossPairResponseCompensator.lean` already shows that even a
  division-free reflected source-dependent correction can cancel tilted fibres. Thus a useful
  successor must classify the full conservative two-mode dilation, not merely exclude singular
  scalar corrections.
- `[CORPUS NEGATIVE]` exact searches for source-FE cocycle Bogoliubov/CCR dilation, expanding orbit
  representative, and source-cocycle partner occupation returned no matching theorem.

## Bounded primary-literature audit

- Lin--Chen--Good--Nambu, arXiv:2608.11957 (2026), reformulates moving-mirror Hawking radiation in
  Rindler/Milne modes and derives squeezed partner modes and their correlations. It does not use a
  Riemann-Xi source-FE cocycle or canonically orient reflected divisor orbits by cocycle gain.
- Hotta--Schützhold--Unruh, arXiv:1503.06109 (2015), defines partner modes for moving-mirror and
  black-hole radiation and shows that partners can be vacuum fluctuations without corresponding
  local energy transport. It does not identify partner occupation with an exact arithmetic Ward
  cocycle or the four route balances here.
- Shaterzadeh-Yazdi--Turner--Sanders, arXiv:0710.3205 (2007), develops `SU(1,1)` symmetry for
  multimode squeezing networks. It supplies general physical context, not the coefficient-faithful
  BM source-cocycle reflection classification.
- Osawa--Lin--Nambu--Hotta--Chen, arXiv:2404.09446 (2024), separates moving-mirror partner modes
  from a final energetic burst and emphasizes nonlinear multimode partner structure. It does not
  contain the present source-FE gain or RH wall law.

This bounded audit found no published statement matching HC79 as of 2026-08-28. It is not an
exhaustive claim over all literature.

## Conjecture HC79-A: canonical expanding reflection representative

For `q : XiZeroCopy`, choose `q` when `Re(q) ≤ 1/2` and its FE reflection otherwise. The chosen
representative has cocycle squared gain at least one. This choice is reflection-orbit invariant:
choosing from `reflect(q)` gives the same underlying representative up to the equality case.

Define

`G(q) = normSq(kappa(expand(q)))`,

`N(q) = G(q) - 1`,

`a(q) = sqrt(G(q))`, and `b(q) = sqrt(N(q))` viewed as a complex pair amplitude.

Then `G(q) ≥ 1`, `N(q) ≥ 0`, and

`a(q)^2 - norm(b(q))^2 = 1`.

Hence `(a(q),b(q))` is an exact two-mode bosonic CCR fibre on every Xi reflection orbit.

## Conjecture HC79-B: positive partner-production survivor

The canonical partner number is reflection invariant and has the sharp wall law

`N(q) = 0 iff Re(q)=1/2`,

`0 < N(q) iff Re(q)≠1/2`.

The off-wall statement is strict: the orbit always has one genuinely expanding branch, so the
minimal conservative dilation necessarily contains a nonzero partner channel. No passivity,
pseudo-unitarity, or KMS/CCR conservation contradiction arises from the source-FE gain.

## Conjecture HC79-C: four-route extinction transmutation

Pointwise `N(q)=0` is equivalent to each established shared receiver:

- HB canonical Peierls--Darboux optical power zero;
- Deninger reflect-gauge Ward charge zero;
- FZZ-P reflected information force zero;
- PW-B partner imbalance zero at every grade;
- on the canonical divisor copy, RBH multiplicity-leading imbalance zero.

Universal partner-vacuum scattering, `∀ q, N(q)=0`, is equivalent to RH. The theorem is a no-go
for deriving RH from two-mode CCR alone, not an assertion of RH: exact bosonic completion exists
unconditionally even when `N(q)>0`.

## Paper proof mechanism

HC78 gives the gain trichotomy and reflected reciprocity. On the left half-strip choose `q`; on the
right choose `reflect(q)`, whose real part is left of the wall. On the wall either choice has gain
one. Therefore `G≥1`. Real square-root identities give `a²=G` and `|b|²=N`, hence the exact CCR
balance. Reflection exchanges the two cases, so `N` is invariant. The HC78 strict trichotomy gives
the sharp zero/positive classification. Existing exact zero-locus transmutations then transport
partner-vacuum extinction to HB, FZZ-P, PW-B, and RBH, and the universal theorem to RH.

## Hostile checks

- Do not identify the raw contracting gain with a bosonic positive-sheet coefficient; first choose
  the expanding reflection representative.
- Do not infer the result from generic CCR completion alone. The new content is coefficient-faithful
  source-cocycle specialization, reflection-orbit canonicity, and the exact four-route survivor.
- Prove nonnegativity before every `Real.sqrt` square rewrite.
- Prove strict nonzero partner production off wall, not merely its wall vanishing.
- Do not assume RH, KMS equilibrium, fixed-pairing covariance, or source-FE unitarity.

## Expected route impact

If proved, conservative two-mode scattering is removed as an HB/FZZ-P/PW-B producer: the literal
off-wall source defect has a fully physical bosonic dilation and is read as partner production,
not inconsistency. The exact positive survivor upgrades the frontier boundary: any producer must
forbid this source-specific partner channel using additional pre-divisor dynamics, source locality,
or singular infinite-frequency coupling. CCR, signed-Hermitian conservation, and fibrewise KMS
completion alone are terminal.

## Closure

Status: `[NEW] [PAPER-PROVED] [LEAN-PROVED] [NO-GO-CLOSED-WITH-POSITIVE-SURVIVOR]`
`[NOVELTY-AUDIT-PASSED-BOUNDED]`.

Formal module:
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFEModularBogoliubovDilationNoGo`.
It is imported by `GaloisForLFunctions.RHTower`.

`hbXiPeierlsUnitSourceFEOrbitExpandingGain_ge_one` places the literal source orbit on the positive
bosonic sheet. `hbXiPeierlsUnitSourceFEOrbit_isTwoModeBosonicCCR` constructs its exact scalar CCR
fibre, while `hbXiPeierlsUnitSourceFEOrbitBogoliubov_preserves_signedHermitian` proves the complete
Nambu transformation preserves the signed Hermitian form for arbitrary two-mode input.

The positive survivor is `hbXiPeierlsUnitSourceFEOrbitPartnerNumber`. It is nonnegative,
reflection invariant, zero exactly on the wall, and strictly positive on every tilted orbit. Its
universal extinction is RH. Exact pointwise theorems identify its zero locus with HB optical
darkness, Deninger Ward cancellation, FZZ-P information equilibrium, every-grade PW-B balance,
and canonical-copy RBH multiplicity-leading balance.

No-go scope: this closes bosonic CCR, pseudo-unitarity, signed-Hermitian conservation, and
fibrewise conservative KMS completion as independent producers. It does not close HB/FZZ-P/PW-B
globally. Remaining hard producer must derive partner-vacuum extinction from source-global
pre-divisor dynamics, locality, or singular infinite-frequency coupling; assuming extinction is
already RH.

Verification on 2026-08-28:

- `lake env lean` on module: pass.
- Target-only `lake build` on module: pass, 12,018/12,018 jobs.
- `#print axioms` on CCR, full signed-Hermitian preservation, strict partner production, universal
  RH equivalence, FZZ-P receiver, and RBH receiver: only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Formal lint: no HC79 finding; repository-wide gate remains red only for unrelated pre-existing
  unreachable modules in RHTower and HTGeometry.
