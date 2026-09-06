# Actual Weil pole comparison between genuine prime powers

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `CCMRestrictedWeilPoleCutoffAtoms`, `CCMRestrictedWeilOddPrimePowerGap`, `CCMRestrictedWeilOddPrimePowerCriterion`, `CCMRestrictedWeilPoleEntrySlopes`; 19 public theorems and four definitions, all wired into `RHTower`.
- **Closed result:** all zero-Mangoldt integer checkpoints can be removed from the odd tail. Above any starting radius at least two, actual odd nonnegativity is exactly its starting inequality and all later genuine prime-power entry inequalities.
- **RH chain:** all-aperture prime–Gamma pole positivity → integrated Chebyshev square-root bound → bounded critical resolvent → mathlib RH. The source signs remain unproved.

## Corpus-driven conjecturing loop

1. **Conjecture:** the frozen moving pole matrix admits a literal finite-atom presentation. **Proved:** reciprocal Mangoldt and Chebyshev combine into the diagonal atoms; the affine prime tent combines into the cross atoms. Adjacent integer cutoffs differ by exactly one atom.
2. **Conjecture:** zero-Mangoldt integers can be crossed without changing the full frozen functions. **Proved:** every new atom is identically zero unless its index is a genuine prime power. At a prime-power right endpoint the new atoms also vanish, now by the exact entry identity.
3. **Conjecture:** the previous minimum principle extends across a whole prime-power gap. **Proved:** the frozen functions agree at every interior radius, so their derivatives agree; the existing actual-source inequality `E''-E<0` applies throughout that interior. The endpoint energy identities include both boundaries.
4. **Conjecture:** only genuine prime-power checkpoints are needed on the tail. **Proved:** bracket any radius by the largest prime power below its cutoff and the least prime power above it. If the lower bracket precedes the chosen starting radius, replace it by that start. Apply the closed gap comparison.
5. **Conjecture:** the two parities have different entry responses. **Proved:** the odd entry correction has positive slope and the even entry correction negative slope at every genuine prime power, with exact squared exponential factors. **Limit:** an entry slope gives no permanent sign for that atom; the earlier actual sign-reversal theorem still applies. The surviving task is aggregate control of the genuine prime-power checkpoint values.

The finite-sum mechanism is informed by `SuzukiScrewDistributionalKernel.exists_affine_screwPrimeSum_Ioo`; that theorem assumes avoidance of integer log locations. Here the exact Mangoldt support removes zero-weight locations, and the moving exponential matrix is retained. The fixed-state first-failure theorem is not used as a substitute for this moving-source argument.

## Exact finite arithmetic atoms

For integer `n`, variable radius `s`, and `lambda=Lambda(n)`, define

`d_n(s)=2lambda(exp(s)/n-exp(-s))`,

`c_n(s)=lambda(1+1/n)(2s-log(n))`.

Let `A_sm,C_sm` be the exact Gamma–polar parts, with both admitted boundary primitives. For reference cutoff `N=floor(exp(2a))`,

`A_ch,a(s)=A_sm(s)-sum_{2≤n≤N}d_n(s)`,

`C_ch,a(s)=C_sm(s)-sum_{2≤n≤N}c_n(s)`.

For consecutive cutoffs, the matrix changes by `(-d_(N+1),-c_(N+1))` at every variable radius. Both atoms vanish identically when `n` is not a prime power. At `b=log(n)/2` they vanish regardless of its Mangoldt weight, since `exp(b)/n=exp(-b)` and `2b=log(n)`.

## Full-source comparison across a prime-power gap

Suppose `a≤b` and no genuine prime power has entry `log(n)/2` strictly between them. For every `a≤c<b`, every integer newly visible at `c` has zero Mangoldt weight. Finite-sum restriction therefore makes both entire frozen functions at `a` and `c` equal. At `c=b`, any remaining new nonzero atom is exactly at entry and has zero value. Consequently the actual odd energy throughout `[a,b]` equals the single frozen function from `a`.

If `a≥2`, the existing shifted differential inequality holds at every interior radius. Continuity and the local second-derivative test give

`[E(c)≥0 for every c∈[a,b]] iff [E(a)≥0 and E(b)≥0]`,

with `E(c)>0` for every strict interior point when the endpoint signs hold.

No bound on gap length, number of skipped integers, or prime distribution is assumed. Every genuine prime power, including higher powers, remains an active boundary.

## Genuine prime-power tail criterion

For any starting radius `a≥2`,

`[E(c)≥0 for all c≥a] iff [E(a)≥0 and E(log(n)/2)≥0 for all prime powers n with log(n)/2≥a]`.

For a given `c`, put `N=floor(exp(2c))≥2`. The finite maximum `p` of prime powers at most `N` exists because two is a prime power. The least prime power `q>N` exists by Euclid's theorem for primes. Their entries bracket `c`; the maximal/minimal properties exclude every other prime-power entry inside the gap. Apply the endpoint comparison, replacing the lower entry by `a` when necessary. This proves the forward-producing direction; the reverse direction is restriction.

Negating the equivalence localizes every negative tail witness to a negative starting value or negative prime-power entry. This does **not** assert that the first zero or first sign change occurs at such an entry.

Combining with the actual two-pole RH equivalence yields

`RH iff [all even-pole energies ≥0] and [all odd energies at 0<a≤2 are ≥0] and [all odd prime-power entry energies above two are ≥0]`.

The theorem is `riemannHypothesis_iff_even_and_odd_primePower_entries`. None of the remaining signs is supplied by this equivalence.

## Exact parity entry slopes

At `b=log(n)/2`, the new odd correction is `2(-d_n+c_n)` and the new even correction is `2(-d_n-c_n)`. Their derivatives are

`odd: 4Lambda(n)(1-exp(-b))²`,

`even: -4Lambda(n)(1+exp(-b))²`.

Since `b>0`, the first is strictly positive exactly when `n` is a prime power; the second is strictly negative exactly in that case. Both adjacent frozen-energy differences have the corresponding derivative at entry. The formulas retain the actual arithmetic weight and exact exponential normalization. They do not impose a differentiability claim on the global energy at a nonzero slope jump.

## Verification

- Foreground `lake env lean` passed for `/tmp/hgt-pole-prime-gaps.vZ58TE/Atoms.lean`, `Gap.lean`, `PrimeCriterion.lean`, and `Slopes.lean`.
- All four named leaf builds passed with `lake --old --log-level=error build GaloisForLFunctions.RHTower.<leaf>`. No full or umbrella build.
- `lake env lean /tmp/hgt-pole-prime-gaps.vZ58TE/Axioms.lean` audited all 23 public declarations: exactly `[propext, Classical.choice, Quot.sound]`, without an added axiom or computation oracle.
- `python3 scripts/formal_tools.py lint` passed with existing large-file warnings; `git diff --check` passed. Research index refreshed and the new gap declarations retrieved. Process inspection found no Lean or Lake process.
- No numerical experiments, external computations, background builds, subagents, or commits.

## Current frontier

Boundary handoff, arbitrary prime-power-gap comparison, exact support reduction, negative-witness localization and parity entry slopes are closed. The [entry/loss and shape package](weil-pole-entry-age-balance.md) identifies the common positive post-entry loss and proves eventual ordinary odd concavity, even convexity, and one unique actual even minimum per closed prime-power gap. Actual odd checkpoint signs, even minimum signs, and bounded-radius ranges remain open. The [full prime–Gamma source problem](../1-in-progress/weil-two-pole-compression-prime-error.md) and RH remain unresolved.
