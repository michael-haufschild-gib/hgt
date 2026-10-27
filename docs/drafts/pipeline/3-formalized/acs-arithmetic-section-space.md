# Arithmetic section spaces on the scaling surface

- **ID:** acs-arithmetic-section-space
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); restricted source construction
- **Route:** ACS: arithmetic sections → Riemann–Roch and ampleness → Hodge index → RH.
- **Statement:** Independently varying smooth sections on short neighbourhoods of the integer logarithms admit a positive source floor, uniformly in the number of arithmetic points.

## Goal

Construct an additive space of actual arithmetic sections on the original scaling surface, and prove Riemann–Roch and ampleness for its source cone. The full objective remains unconditional closure of ACS. A restricted carrier does not close the route; extension to all compact tests remains required.

The current corpus proves a spacing-scale floor for tests `Σ x_n g(u−log n)` with one common profile `g`. Positivity on each such family does not by itself prove positivity on their linear span. The candidate extends the floor to `Σ g_n(u−log n)` with independently varying `C²` profiles supported in `[0,w]`. This is a source-defined linear space rather than a collection of individually positive tests or a zero-blind ideal.

## Exact candidate

There exists an explicit `c > 0`, independent of `N`, such that, for every `N ≥ 1`, `0 < w ≤ c log(1+1/N)`, and all real `C²` profiles `g_n` supported in `[0,w]`,

`M(Σ_{1≤n≤N} g_n(·−log n)) ≥ ∫ (Σ_{1≤n≤N} g_n(·−log n))²`.

On the kernel of the sinh pole moment this gives a positive Weil floor and hence the source `L²` cone has Riemann–Roch and ampleness. All prime, Gamma and polar terms must be retained. No positivity premise is admissible.

## Approach and attack

1. The integer-log separation kills every non-ratio prime lag. The prime charge becomes the integral of the finite prime form on the profile vector `(g_n(u))_n`.
2. Apply the existing tilted prime Schur bound pointwise, then integrate.
3. For each distinct pair, mixed autocorrelation is bounded by half the sum of the two profile masses. Pair-window localization and symmetric row summation give the archimedean cross bound with independent masses.
4. Match the tilted prime saving to the cross row. Choose the width constant with a unit coercivity margin.
5. Construct the linear section carrier and prove its source-cone properties on the original scaling surface.

**[OPEN CORE: full ACS]** There is no proved extension from this sparse support carrier to arbitrary sources. That extension, including the mixed pairing with omitted directions, remains required. The restricted statement below has a complete paper proof and Lean certification.

## Paper proof of the restricted statement

Put `G_n = ∫ g_n²`, `δ = log(1+1/N)`, and `f(u)=Σ g_n(u−log n)`. All sums indexed by `1≤n≤N` are finite. Every profile, product and translate is continuous and compactly supported, so all source integrals and finite interchanges exist. The Lévy integrability follows from the existing theorem for compact `C²` functions.

Assume `0<w≤spacingRatio·δ`. The existing constant satisfies `spacingRatio<1/2`, so distinct translated supports are disjoint and `∫f²=ΣG_n`.

For each integer `k≥1`, a product of the profiles at `m,n` in the lag `−log k` vanishes unless `m=nk`: otherwise the two distinct positive integer logarithms are separated by at least `δ`, since one of their indices is at most `N`. At equality the translated product integrates to `∫g_m g_n`. The positive lag is identical with `n=mk`. Orders `k>N` vanish. Summing the exact Hecke weights gives

`primeSum(f)=Σ_m Σ_n P(m,n)∫g_m g_n=∫P_N((g_n(u))_n)du`.

The tilted Schur theorem applies to this real profile vector at each `u`. Integrating yields

`primeSum(f)≤Σ_m G_m[log N+2(log4+4)−(m/(4N))log m]`.

For the archimedean term restrict the nonnegative Lévy integral to `w<y≤1`. Its inner square integral is `2ΣG_n−2∫f(u)f(u+y)du`. Expanding the mixed correlation, its diagonal terms vanish for `y>w`; an off-diagonal term occurs only in `|y−(log n−log m)|≤w`. By the integrated inequality `2|ab|≤a²+b²` and translation invariance of Lebesgue measure its absolute value is at most `(G_m+G_n)/2`.

The existing pair-window estimate bounds its weighted `y` integral by `B_mn=crossBound(w,log n−log m)`. This bound is nonnegative and symmetric. Consequently the complete cross contribution is at most `Σ_m G_m Σ_{n≠m}B_mn`. The existing row bound gives `Σ_{n≠m}B_mn≤4exp(5/2)wm(1+log(N+1))`. The diagonal density integral is at least `log(1/w)`. Thus

`levyEnergy(f)≥Σ_m G_m[log(1/w)−8exp(5/2)wm(1+log(N+1))]`.

The proved row comparison `crossRow_le_saving` bounds the subtracted cross row by `(m/(4N))log m+3/4`. After subtracting the prime bound and adding the exact constant Gamma term, one obtains

`M(f)≥[2 gammaHardyPhaseRate(0)+log(1/w)−log N−spacingConstant]∫f²`.

Take `c=spacingRatio·exp(−(spacingConstant+2|gammaHardyPhaseRate(0)|+1))`. Since `δ≤1/N` and `spacingRatio≤1`, the assumed width gives `log(1/w)≥log N+spacingConstant+2|gammaHardyPhaseRate(0)|+1`; the bracket is at least one.

The section sums form a real linear space: add profiles pointwise and multiply them by scalars. On its linear kernel `S(f)=∫f(u)sinh(u/2)du=0`, the exact full-form identity is `Re W(f,f)=M(f)+2C(f)²≥∫f²`. The existing source-cone theorem with reserve `∫f²` gives Riemann–Roch and ampleness on this scaling subsurface. No new analytic sign assumption enters.

The carrier is nonzero for every `N≥1,w>0`. Choose smooth bumps `b₁,b₂` supported respectively in `(0,w/2)` and `(w/2,w)`, with values one at `w/4` and `3w/4`. Each is a section supported at the arithmetic point `n=1`. If `S(b₁)=0`, use `b₁`; otherwise `S(b₂)b₁−S(b₁)b₂` has zero sinh moment and value `−S(b₁)≠0` at `3w/4`.

## Gates

- [x] Exact candidate and source-only definitions.
- [x] Complete dependency-closed paper proof for the restricted section space.
- [x] Lean leaf check with `lake --old env lean`; exit 0.
- [x] Transitive axiom audit; umbrella wiring.
- [x] Scope assessed: independent-profile source floor and restricted RR/ampleness; full ACS remains open.

## Evidence and constraints

Read the ACS README, ACS/HF frontier entries, relevant killed mechanisms, and the route-obstacle discussion. Corpus searches locate `SourceRiemannRochAwayFromTheLowFrequencyDivisor`, `ExactArithmeticSourceEffectivity`, and `SpacingScaleHarmonicAnalysis.TheStabilityLawAtTheSpacingScale`.

The report's spacing-scale gap is superseded by existing source. Its common-profile theorem is not a new contribution here. The SSHA README's advertised `TheCriticalWidthLaw.lean` is absent; no claim from that advertised theorem is used.

External search and novelty checks are excluded by the user. No claim of literature novelty is made. Existing unrelated worktree edits are preserved.

## Scope assessment

The positive result controls cross terms between independently chosen profiles; it strengthens the existing common-profile family to a linear source carrier. It is not a construction of unrestricted arithmetic `h⁰`, a subquadratic height, or full-source ampleness. Those remain the ACS closing obligations. The original route goal is therefore still active.

The existing constant-one self-energy, tilted prime rows, and source-cone calculus are reused rather than presented as new discoveries. No numerical experiment, external search, or novelty check was used. The source-only support and pole-moment restrictions are explicit, and no RH input is added.

## Verification state

Final exact-file check completed with exit 0:

```text
cd formal
lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticSectionSpace.lean
```

All three principal declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. No unresolved Lean process remains. No extra axioms, placeholders, trusted-computation shortcut, or heartbeat increase was used.

Final declaration names:

- `integral_sq_le_markovEnergy_arithmeticSection`
- `sinhNeutralArithmeticSections_effectivity`
- `exists_nonzero_sinhNeutralArithmeticSection`

Umbrella import and ACS README integration are present. The umbrella must not be compiled.

## Remaining route work

Full ACS closure is unproved. The construction restricts support to short arithmetic neighbourhoods and removes one explicit pole moment. It gives no unrestricted arithmetic section-count law, bounded-error Rosati height, or source estimate controlling the omitted directions and their mixed pairings. Further work must attack those obligations; improving this width constant or repackaging the restricted cone would not meet the requested goal.
