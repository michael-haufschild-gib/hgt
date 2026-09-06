# Exact prime sign cutoff and budgets for the odd exponential pole

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `CCMRestrictedWeilOddPrimeCutoff`, `CCMRestrictedWeilOddPrimeTransport`, `CCMRestrictedWeilOddPrimeBudget`; 20 public theorems and six definitions, wired into `RHTower`.
- **RH chain:** full prime–Gamma pole inequality → square-root integrated Chebyshev error → bounded actual unit-Riesz resolvent → mathlib RH. This package supplies exact arithmetic structure for the first inequality; it does not prove its sign.

## Conjecture → failure → positive replacement

The actual pole matrix in `CCMRestrictedWeilPrimePoleMatrix` gives the prime self and cross entries. The corpus's `CCMGuinandWeilPrimeEntryIncidence` and `CCMGuinandWeilPrimeEntryRankOneTangent` distinguish entry behavior from a complete aperture path in a different source family. They motivate checking the full literal-pole contribution before trying to propagate its initial sign.

The permanent-positive odd-prime shortcut fails for every genuine prime power. Its positive replacement is a unique sign cutoff, a classification of every visible term, and an exact decomposition of the full odd Weil energy into two nonnegative prime budgets and the complete Gamma–pole balance.

The hyperbolic calculus mechanism is standard and already occurs in `HTGeometry.HyperbolicBounds`; no claim of a new general calculus theorem is made. The identified kernel, signs, and budget identity concern the actual source and its original prime normalization.

## Exact atom and sign cutoff

Write `p_±=1_[-a,a] exp(±x/2)`, `h=log(n)/2`, and `u=a-h`. For `n≥2` and `h≤a`, reflection and self-adjointness give

`<T_n(p_++r p_-),p_++r p_->=2[2(exp(a)/n-exp(-a))+r(2a-log n)(1+1/n)]`, `r=±1`.

In odd parity this is

`<T_n(p_+-p_-),p_+-p_->=8 exp(-h)[sinh(a-h)-(a-h)cosh(h)]`.

For each positive aperture there is exactly one `H(a)∈(a/3,a/2)` solving

`sinh(a-H)=(a-H)cosh(H)`.

For `0<h<a`, the kernel is positive iff `h<H(a)`, negative iff `H(a)<h`, and zero iff `h=H(a)`. It also vanishes at entry `h=a`. In the prime-power variable, the cutoff lies strictly between `exp(2a/3)` and `exp(a)`.

**Dependency-closed proof.** The derivative of `u cosh(u)-sinh(u)` is `u sinh(u)>0` for `u>0`, so `sinh(u)<u cosh(u)`. Hence `sinh(u)/u` is strictly increasing on positive arguments. The function `sinh(a-h)/(a-h)-cosh(h)` is strictly decreasing for `0<h<a`. At `h=a/2` it is negative. At `h=a/3`, the identity `sinh(2h)=2sinh(h)cosh(h)` and `sinh(h)>h` make it positive. Continuity and the intermediate value theorem give the root; strict monotonicity gives uniqueness and the complete sign classification. Multiplication by the positive factor `a-h` restores the undivided kernel.

For a fixed genuine prime power, the full Weil contribution is `-Lambda(n)` times the displayed operator energy. It is positive at `a=log(n)` and negative at the larger aperture `b=3log(n)/2`. This is proved directly for every prime power in `ccmOddPole_primePower_contribution_changes_sign`, without numerical examples or a sign premise.

## Exact nonnegative budgets and full source

For every visible integer, put

`w_n=8 Lambda(n) exp(-h_n)[sinh(a-h_n)-(a-h_n)cosh(h_n)]`, `h_n=log(n)/2`.

With the original finite range `2≤n≤floor(exp(2a))`, define

`O(a)=sum_{h_n≤H(a)} w_n`,

`R(a)=sum_{H(a)<h_n} (-w_n)`.

Both budgets are nonnegative, by the exact kernel signs and nonnegativity of Mangoldt weights. The boundary terms at the cutoff and entry vanish. Their difference is exactly the negative of the actual finite prime-operator energy:

`R-O=-<P_a(p_+-p_-),p_+-p_->`.

No prime power, endpoint normalization, or sign is dropped. With `N=2sinh(a)`, `M=2a`, `kappa=-EulerGamma-log(2pi)` and the admitted Gamma boundary masses `B_0,B_1`, define

`G_odd=2[kappa(N-M)-exp(a)+(2a+1)exp(-a)+2a²+B_1-B_0-(N-M)²]`.

The actual full source then satisfies

`Q(p_+-p_-)=G_odd+R-O`.

The negative odd pole square is essential and remains in this formula. Consequently

`Q(p_+-p_-)≥0  iff  O≤G_odd+R`.

This is an exact aggregate comparison, not a consequence of the two separate budget signs. The even energy sign remains an independent half of the current two-pole RH criterion.

## Verification

- Foreground scratch checks passed with `lake env lean /tmp/hgt-odd-prime-cutoff.SCuUYh/Cutoff.lean`, then `Transport.lean`, then `Budget.lean`.
- Named final audits passed with `lake --old --log-level=error build GaloisForLFunctions.RHTower.<leaf>` for all three leaves. No full or umbrella build.
- `lake env lean /tmp/hgt-odd-prime-cutoff.SCuUYh/Axioms.lean` audited all 26 public declarations: exactly `[propext, Classical.choice, Quot.sound]`, no additional axiom or oracle.
- `python3 scripts/formal_tools.py lint` passed with existing large-file warnings; `git diff --check` passed. Process inspection found no remaining Lean or Lake process. The research index includes the new declarations.
- No numerical experiments or external computation were used. The three imports are wired into `RHTower`.

## Current mathematical frontier

Prove `O≤G_odd+R` for all apertures and the corresponding even sign, or obtain the equivalent full prime–Gamma pole comparison by another argument. [Current source-sign card](../1-in-progress/weil-two-pole-compression-prime-error.md). The constrained-ground and other RH routes remain open. [Closed shortcut and positive survivor](../5-failed/weil-odd-prime-permanent-entry-sign.md).
