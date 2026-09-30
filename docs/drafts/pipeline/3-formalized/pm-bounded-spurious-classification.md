# Complete arithmetic classification of bounded Fermi witnesses

- **ID:** pm-bounded-spurious-classification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route PM; literal alternating fractional-part generators
- **Statement:** Bounded Fermi witnesses are exactly continuous dyadically self-similar functions with zero fundamental logarithmic mean.
- **Novelty:** Exact literal generator identity and complete source class were not found in scoped corpus/public searches; global novelty remains unverified. Generic periodicity and compactness are not claimed new.

## Goal

Identify the entire bounded spurious source class, including arbitrary continuous log-periodic
profiles. This distinguishes the explicitly source-classified neutral kernel from the unbounded
zero-multiplicity obstruction. It does not prove every witness bounded.

## Gates

- [x] 0 → 1: literal source and logarithmic mean specified
- [x] 1 → 2: dependency-closed arithmetic proof below, [PROVED HERE]
- [x] 2 → 3: actual-leaf Lean audit and axiom audit
- [ ] 3 → 4: standalone publication and completed novelty review

## Exact source identity

Put `L(w)=integral_(1/2)^1 w(t)/t dt`. Every continuous function on `(0,1]` satisfying
`w(t/2)=w(t)` has a uniform bound, by compactness of `[1/2,1]` and dyadic reduction.
For every `a≥1`, the literal source pairing satisfies

`integral_0^1 phi_a(t) w(t) dt = -(1/a) L(w)`.

No zeta divisor, functional equation, spectral premise or RH enters this identity.

## Dependency-closed paper proof

1. Write `N_a(t)={1/(at)}` and `A_a=integral_0^1 N_a(t) w(t) dt`.
   Both fractional parts and `w` are bounded and measurable on the finite interval, so all
   integrals below exist.
2. The exact change of variable `t=2u`, using self-similarity, gives

   `A_a = 2 integral_0^(1/2) N_(2a)(u) w(u) du`.

3. Split `A_(2a)` at `1/2`. Therefore

   `A_a-2 A_(2a) = -2 integral_(1/2)^1 N_(2a)(t) w(t) dt`.

4. On `1/2<t≤1`, `a≥1` implies `0<1/(2at)<1`, so the fractional part equals `1/(2at)`.
   The last expression is exactly `-(1/a)L(w)`, proving the source identity.
5. Every bounded actual Fermi witness is self-similar by the existing exponent-zero rigidity.
   Apply the identity at `a=1` to its conjugate. Source orthogonality forces `L(conj w)=0`,
   hence `L(w)=0`.
6. Conversely continuity and self-similarity give boundedness and square-integrability.
   Zero logarithmic mean also holds for the conjugate; the exact identity proves orthogonality
   to every actual generator with `a≥1`. Thus the function belongs to the literal witness class.

Consequently the two intrinsically defined function sets are equal, with no hypothesis parameters
in the set-equality capstone. The arithmetic proof classifies a source kernel; it is not universal
source positivity.

## Prior-art audit

Corpus search `Fermi dyadic periodic zero mean generator pairing --any --module FermiNyman`
reported `partial: true`, with existing individual spurious modes, half-dilation invariance and
bounded-witness rigidity. No exact all-profile logarithmic-mean classification surfaced.
Scoped public searches for Nyman/Beurling with periodic/log-mean/dyadic/fractional-part terms
found no matching literal source identity. No claim of exhaustive public or training-data absence.

## Log

- 2026-09-29 — closed arithmetic paper proof; Lean implementation queued after rank/kernel audits.

## Complete Lean certificate

`formal/GaloisForLFunctions/RHTower/FermiNymanBoundedSpuriousClassification.lean`
proves every paper clause. `integrableOn_nymanGen_mul_of_bounded` justifies the literal
integrals; `nymanGen_half` and `integral_fermiNymanGen_mul_of_dyadicSelfSimilar` prove the exact
all-scale arithmetic identity. The hypothesis-free set equality
`RHTower.boundedFermiWitnessSet_eq_dyadicLogMeanZeroSet` proves both directions of the complete
classification. `RHTower.fermiMultiplicityJetKernelSet_eq_dyadicLogMeanZeroSet` also gives the
source description of the full correlation-jet kernel. Original continuity and self-similarity
domains are retained inside the intrinsic sets; no analytic input is assumed.

Targeted `lake --old build +GaloisForLFunctions.RHTower.FermiNymanBoundedSpuriousClassification:olean`
passed as part of the two-leaf PM build. Final `lake env lean` on this exact source passed exit 0.
One shared audit of all 52 declarations in the five PM coordinate/classification leaves found
only `propext`, `Classical.choice`, and `Quot.sound`. The leaf is imported by `RHTower.lean`.
Authoritative `scripts/formal_tools.py lint` reported only ten unrelated concurrent unreachable
leaves; none concerns this certificate. Global lint remains a separately recorded workspace gate.

- 2026-09-29 — exact source, direct compiler, axiom and reachability audits completed; moved to Stage 3.
