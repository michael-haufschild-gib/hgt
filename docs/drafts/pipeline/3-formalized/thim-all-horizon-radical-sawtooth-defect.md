# All-horizon radical sawtooth invariance and defect dissipation

- **ID:** thim-radical-sawtooth-defect
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Squarefree-supported weights have radical-invariant active sawtooth endpoints; equal sieve responses give exact negative Dirichlet-energy defect increments. Möbius and nonnegatively power-damped weights have nonpositive defects at all powers of bases in `[2, 2N]`.

## Scope and plan

1. Audit existing radical invariance, sawtooth endpoint signs, and first-octave estimates.
2. Give dependency-closed paper arguments, including the damped first-octave envelope.
3. Formalize in `AllHorizonRadicalSawtoothAndDefectReduction.lean`, wire its umbrella, audit every new theorem's axioms, and run formal lint.
4. Record crisp facts and boundaries in `logs/thim-radical-sawtooth-knowledge.md`.

`update_plan` is unavailable in this session; this card tracks the plan.

## Audit facts

- Corpus hybrid search found existing sieve power invariance and rough checkpoint estimates; search was partial at 60 seconds (vector statement stage unfinished). Exact source searches check local duplication.
- Actual predecessor identity has coefficient `-1/2`, whereas self endpoint has `+1/2`; the brief's predecessor sign is incorrect but does not affect invariance.
- Pillar VII's rough comparison requires a rough integer `r >= 2` preceding the endpoint; such a checkpoint need not exist below a small base. Use its underlying polarization identity for unconditional nonpositivity, and retain a rough-comparison corollary where applicable.
- Nonnegative damping `ε >= 0` is the parameter domain for the requested sign theorem, consistent with existing power-damped bounds.

## Gates

- [x] Scope and corpus dependencies located.
- [x] Complete paper argument.
- [x] All requested Lean statements audited (nonnegative damping domain).
- [x] Umbrella and all 13 axiom closures verified; knowledge ledger written.
- [x] Formal lint executed; global gate failed outside the new leaf, as detailed below.
- [x] All 13 declarations, exact axiom closures, source fingerprint, fresh compiled artifact,
  umbrella reachability, and complete API entries passed the final artifact audit.
- [x] Owned scratch files removed; all owned build/search/index jobs terminated normally.

## Dependency-closed paper proof [PROVED HERE]

Write `s(j)=sieveSeq N c j` and `D(M)=sieveRenormalizedPrefixDefect N M c`.
Harmonic division preserves squarefree support because `0/s=0`. Applying Pillar IX to both
`c` and `s ↦ c(s)/s` in the actual predecessor formula `A(k)=-(s_c(k)-s_{c/d}(k))/2`
proves divisor-multiplication and positive-power invariance, at every horizon.

For `2 <= k <= l` and `s(l)=s(k)`, subtract the two universal polarization identities and
split `[1,l-1]` at `k`. Endpoint squares cancel, leaving
`2(D(l-1)-D(k-1)) = -Σ_{j=k}^{l-1}(s(j+1)-s(j))²`.
Thus the defect decreases along ordered equal-response endpoints. Pillar IX supplies
these endpoints for divisor multiplication and powers; no horizon bound is used.

For `ε >= 0`, `k >= 2`, choose a prime `p | k`. Existing divisor-ordering antitonicity
and the prime Euler factor imply `0 <= τ_ε(k) <= 1-p^(-ε)`.
Also `|c_ε(k)| <= k^(-ε) <= p^(-ε)`, by the Möbius absolute bound and nonpositive-power
antitonicity. Hence `τ_ε(k)+|c_ε(k)| <= 1`, and `|τ_ε(k)-c_ε(k)| <= 1`.
If `k <= N`, the sieve response is `τ_ε(k)` and lies in `[0,1]`; if `N<k<=2N`,
first-octave reciprocity gives `τ_ε(k)-c_ε(k)`. Therefore `|s(k)|<=1` for all bases
`2<=k<=2N`. Such a base forces `N>=1`, so `s(1)=1`.
At every positive power `k^m`, squarefree support gives `s(k^m)=s(k)`; the universal
polarization formula now gives `D(k^m-1) <= 0`. Specializing `ε=0` gives Möbius weights.
If a rough checkpoint `r>=2` precedes `k^m`, the same square bound feeds Pillar VII
and gives the stronger comparison `D(k^m-1)<=D(r-1)<=0`.

This is one connected contribution: radical endpoint invariance becomes an additive
energy dissipation law, with an infinite family of certified trans-horizon checkpoints.

## Lean certificate and requirement audit

Module: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/AllHorizonRadicalSawtoothAndDefectReduction.lean`.

| Requirement | Verified declaration |
|---|---|
| Harmonic division preserves squarefree support | `squarefree_support_harmonic` |
| Divisor multiplication, every horizon | `activeCenteredSawtoothSum_mul_of_dvd_of_squarefree_support` (both predecessor and self endpoints) |
| Positive powers, every horizon | `activeCenteredSawtoothSum_pow_of_squarefree_support` (both endpoints) |
| Damped checkpoint nonpositivity, `ε>=0`, `2<=k<=2N`, `m>=1` | `sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_pow_nonpos` |
| Möbius checkpoint nonpositivity, same base/exponent domain | `sieveRenormalizedPrefixDefect_moebiusReal_pow_nonpos` |
| Pillar VII comparison at any preceding rough checkpoint | `sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_pow_le_rough_checkpoint` |
| Stronger exact dissipation and exponent monotonicity | `two_mul_sieveRenormalizedPrefixDefect_pow_sub`, `sieveRenormalizedPrefixDefect_pow_antitone` |

The requested union `k<=N` or `N+1<=k<=2N` is exactly `k<=2N` for natural `k,N`.
No bound is imposed on `k^m` relative to `N`. No unproved analytic/arithmetic premise
is added; support, positivity, and domain conditions are explicit mathematical parameters.

Original-source audit: `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/TransHorizonIncidenceMechanics/AllHorizonRadicalSawtoothAndDefectReduction.olean GaloisForLFunctions/TransHorizonIncidenceMechanics/AllHorizonRadicalSawtoothAndDefectReduction.lean` exited 0 without warnings.
Source SHA-256: `dbb5fa4e280f9a75be158c42d8ab660cc36ec4dc53be524973fe30c4b3eaba46`.

Every one of the 13 public theorems was checked using `#print axioms` in a scratch file,
with exactly `[propext, Classical.choice, Quot.sound]`. No added axiom, proof debt,
computational decision oracle, or heartbeat increase. Both required local dependencies
were compiled individually, sequentially. No full or umbrella build was run.

The leaf is imported by `TransHorizonIncidenceMechanics.lean`, itself imported by
`MainTheorems.lean`; concurrent umbrella upkeep already supplied the leaf import.
All 13 declarations occur in the regenerated API.

Evidence: `logs/thim-radical-sawtooth-lean.txt`, `logs/thim-radical-sawtooth-axioms.txt`,
`logs/thim-radical-sawtooth-index.txt`, `logs/thim-radical-sawtooth-lint.txt`, and
`logs/thim-radical-sawtooth-audit.json`. Index generation was repeated after the concurrent
staleness finding (`logs/thim-radical-sawtooth-index-final.txt`, exit 0); this is not a claim
that concurrent global changes have ceased or that global lint passes.

Global `scripts/formal_tools.py lint --check-generated` exited 1: 11 unreachable modules
in other areas, the pre-existing unregistered `TransHorizonIncidenceMechanics.lean` umbrella,
and API/overview staleness from concurrent source changes after index generation.
No diagnostic cites the new leaf. This certifies the leaf, not a clean global project gate.
README was not edited by this contribution.

