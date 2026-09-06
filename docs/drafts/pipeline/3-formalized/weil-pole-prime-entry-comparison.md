# Actual odd-pole comparison through integer entries

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `CCMRestrictedWeilPolePrimeEntry`, `CCMRestrictedWeilOddPrimeEntryComparison`, `CCMRestrictedWeilOddIntegerEntryCriterion`; 14 public theorems and one definition, all wired into `RHTower`.
- **Result:** the next integer-entry boundary is included in the exact odd-pole interval comparison. Above any starting radius at least two, actual odd nonnegativity is exactly its starting inequality and all subsequent integer-entry inequalities.
- **RH chain:** prime–Gamma pole sign → square-root integrated Chebyshev bound → bounded critical resolvent → mathlib RH. The source signs remain open.

## Conjecture → proof → next conjecture

1. **Candidate:** propagate positivity using only the unchanged-cutoff comparison. **Gap:** it omits the next boundary, where both arithmetic cumulatives change. The moving exponential tests prevent direct use of the corpus's fixed-state first-failure theorem.
2. **Conjecture:** the incoming chamber still gives the actual value at that boundary. **Proved:** the entering diagonal atom and cross tent both vanish exactly. The prime cumulatives jump, but their complete matrix contribution cancels there.
3. **Conjecture:** the interval minimum principle therefore includes the next boundary. **Proved:** all interior radii retain the original cutoff; the chamber expression is continuous at both positive endpoints; the actual right endpoint equals its chamber value.
4. **Conjecture:** all odd inequalities on the tail reduce to entry values. **Proved:** every radius lies between consecutive `log(n)/2` entries. If the left entry precedes the chosen starting radius, that starting radius replaces it and has the same cutoff. The endpoint theorem applies in either case.
5. **Surviving problem:** prove the actual endpoint signs. Existing corpus theorems for one-sided dyadic Chebyshev increments do not directly apply to these integrated-error/pole values; a source identity or comparison connecting them is still required.

These are exact statements about the original full Weil form. No approximation, numerical experiment, or additional positivity premise is used to prove the equivalences.

## Exact entry cancellation

Let `N=floor(exp(2a))` and let `exp(2b)=N+1`. Since `a>0`, `N+1≥2`. Put `n=N+1`, `lambda=Lambda(n)`, and `W(a)=sum_{2≤m≤N}Lambda(m)(1+1/m)`.

The literal cumulative jumps are

`M(exp(2b))=M(exp(2a))+lambda/n`,

`psi(exp(2b))=psi(exp(2a))+lambda`.

The new diagonal prime term is `2lambda(exp(b)/n-exp(-b))=0`, since `n=exp(2b)`. The new cross tent is `lambda(1+1/n)(2b-log(n))=0`. Hence

`A(b)=A_ch,a(b)`, `C(b)=C_ch,a(b)`, `E(b)=E_ch,a(b)`.

The complete tent at the boundary is exactly `T(a)+2(b-a)W(a)`. All existing prime powers, Gamma boundary masses, and polar terms are retained.

## Closed interval comparison

For `2≤a≤b` and `exp(2b)≤floor(exp(2a))+1`, every `a<s<b` has the same cutoff as `a`. The existing source theorem gives

`E_ch,a''(s)-E_ch,a(s)<0`.

The positive-radius chamber expression is continuous on `[a,b]`. At the right endpoint it agrees with the actual source by either the unchanged-cutoff identity or the exact entry cancellation. A nonpositive interior minimum contradicts the second derivative test and the strict shifted differential inequality. Consequently

`[E(c)≥0 for every c∈[a,b]] iff [E(a)≥0 and E(b)≥0]`,

and the endpoint signs imply `E(c)>0` for every `a<c<b`.

These are `ccmWeilOddPole_nonneg_until_next_entry_iff_endpoints` and `ccmWeilOddPole_pos_before_next_entry`.

## Discrete tail and RH criteria

Define the actual positive aperture `a_n=log(n)/2` for every integer `n≥2`. Lean proves `exp(2a_n)=n` and its exact integer cutoff.

For any `a≥2`,

`[E(c)≥0 for every c≥a] iff [E(a)≥0 and E(a_n)≥0 for every a_n≥a]`.

**Proof.** Given `c≥a`, put `N=floor(exp(2c))`, `l=a_N`, and `r=a_(N+1)`. Then `N≥2`, `l≤c<r`, and `exp(2r)=N+1`. If `a≤l`, apply the closed interval criterion to `[l,r]`. Otherwise apply it to `[a,r]`; monotonicity and the floor characterization give `floor(exp(2a))=N`. The converse is immediate restriction. Negating this equivalence localizes any negative tail witness to the starting radius or an integer-entry radius.

Combining this result with the proved two-pole RH criterion gives the exact equivalence

`RH iff [all even-pole energies ≥0] and [all odd-pole energies at 0<a≤2 are ≥0] and [E(a_n)≥0 whenever a_n≥2]`.

This is `riemannHypothesis_iff_even_and_odd_integer_entries`. It does not prove the endpoint inequalities, remove the even condition, or replace all integer entries with prime-power entries.

## Verification

- Foreground `lake env lean` passed for `/tmp/hgt-pole-entry.5i0d6Q/Entry.lean`, `Comparison.lean`, `Endpoints.lean`, and `Witness.lean`.
- All three named leaf builds passed with `lake --old --log-level=error build GaloisForLFunctions.RHTower.<leaf>`. The final criterion build includes the negative-witness corollary. No full or umbrella build.
- `lake env lean /tmp/hgt-pole-entry.5i0d6Q/Axioms.lean` audited all 15 public declarations: exactly `[propext, Classical.choice, Quot.sound]`. No added axiom or computation oracle.
- `python3 scripts/formal_tools.py lint` passed with existing large-file warnings. `git diff --check` passed. Research index refreshed and new declarations retrieved. Process inspection found no Lean or Lake process.
- No numerical experiment, external computation, background build, subagent, or commit.

## Current frontier

The changed-cutoff handoff and continuum-to-integer-entry reduction in this package are closed. The [prime-power gap package](weil-pole-prime-power-gaps.md) further removes every zero-Mangoldt integer checkpoint and proves the exact opposite parity entry slopes. The remaining odd tail obligation is genuine prime-power checkpoint positivity. The compact initial odd range and all even signs remain separate obligations. The broader [prime–Gamma source-sign problem](../1-in-progress/weil-two-pole-compression-prime-error.md) and RH remain open.
