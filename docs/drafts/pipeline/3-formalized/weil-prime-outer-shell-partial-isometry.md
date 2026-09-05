# Exact outer-shell prime transport

- **ID:** WEIL-PRIME-OUTER-SHELL
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `AutocorrelationChainDamping`, `CCMRestrictedWeilBoundedRemainder`, `CCMRestrictedWeilGroundFrequencyLocalization`, `CCMRestrictedWeilFormTranslation`.
- **Module:** `GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimeOuterShell` (wired into `RHTower.lean`).
- **Statement:** Above the half-diameter, the square of the actual compressed symmetric translation is the endpoint-overlap projection. Its norm is exactly one while overlap is nonempty, with both eigenvalue signs present under both pole constraints. The literal finite-prime norm is at most `21(exp(a)+exp(a/2))`.

## Proof chain and scope
Literal prime–Gamma source → quantitative source estimate on constrained ground → exclude zero-ground forced equations → positive ground at every aperture → weighted pole exclusion → RH. The actual prime norm estimate is proved. The all-aperture sign and zero-ground exclusion remain open.

## Conjecture loop and positive survivor
1. **Conjecture:** scalar chain-two damping transfers to the completed literal aperture operator. **Proved:** `ccmApertureSymmetricTranslation_sq_val`, `norm_ccmApertureSymmetricTranslation_le_one`, and the source norm bounds below.
2. **Conjecture:** the two pole constraints permit a strictly smaller atomwise contraction constant. **Falsified:** nonzero constrained vectors attain both `+1` and `-1` for every `a<h<2a`.
3. **Pivot:** classify the exact surviving constant and retain signed extremizers. **Proved:** `polarConstrained_outerShell_bound_iff` says the uniform constrained bound with real constant `C` holds exactly when `1≤C`.

## Dependency-closed paper proof [PROVED HERE]
Let `P_a` be cutoff to `[-a,a]`, let `T_h f(x)=f(x+h)`, and put `S_h=P_a(T_h+T_{-h})P_a`, restricted to the aperture Hilbert space.

For `h>a`, the shifts by `±2h` fall outside the original support. At any surviving point at most one of `x+h` and `x-h` lies in the aperture. Therefore

`S_h² f = 1_{[-a,a-h] ∪ [-a+h,a]} f`.

The right side is an orthogonal projection. Since `S_h` is self-adjoint, the Hilbert operator norm identity gives `||S_h||²=||S_h²||≤1`. If `h≥2a`, the endpoint intervals are empty or singletons, hence the cutoff is zero almost everywhere. Self-adjointness then gives `S_h=0`.

For `a<h<2a`, choose `b=(2a-h)/4>0` and a nonzero pole-constrained form vector at radius `b`, supplied by the explicit smooth-core construction. Translate it by `±h/2`. Both translates fit strictly inside radius `a`. Translation multiplies each exponential moment by a nonzero scalar, so both translates remain constrained. Applying `S_h` interchanges them: the unwanted translates by `±3h/2` lie outside the aperture. Their inner product is zero because `h>2b`. Their sum and difference are thus nonzero constrained form vectors with eigenvalues `+1` and `-1`. This proves the exact norm and the optimality classification, retaining both signs.

The actual prime operator is `T(n)=S_{log n}/sqrt(n)`. Its norm is `1/sqrt(n)` for `a<log(n)<2a`, zero for `log(n)≥2a`, and bounded by the existing `2/sqrt(n)` otherwise. Summing with nonnegative von Mangoldt weights proves

`||P_a|| ≤ Σ_{2≤n≤exp(2a)} (1 if a<log(n), else 2) Λ(n)/sqrt(n)`

`≤ primeMassHalf(exp(2a)) + primeMassHalf(exp(a))`

`≤ 21(exp(a)+exp(a/2))`.

The last inequality uses the already proved elementary mass bound `primeMassHalf(X)≤21sqrt(X)`. No asymptotic, numerical quadrature, or computed certificate enters the proof. The half-diameter boundary `h=a` is conservatively charged by the inner-shell estimate; the full-diameter endpoint is handled exactly.

## No-go closure
- **Exact obstruction:** `exists_polarConstrained_outerShell_eigenvectors` and `polarConstrained_outerShell_bound_iff` rule out a smaller uniform atomwise bound from the two pole constraints alone.
- **Strongest positive survivor:** exact endpoint projection, both constrained eigenvalue signs, exact prime-atom norm, and the improved literal two-scale finite-prime envelope.
- **Consequence:** another independent-prime absolute-value estimate cannot improve this sharp outer-shell constant. Joint arithmetic correlations, the Gamma energy of extremizers, or other coupled source information may still improve the complete form. No route is retired by this result.
- **Novelty audit:** the corpus already had scalar chain-two/three inequalities and their paper interpretation. The new Lean statements act on the actual completed aperture operator and establish sharpness within the pole-constrained form domain. This is corpus integration and a precise survivor classification, not a claim of external novelty for path-shift numerical radii.

## Verification
- `lake env lean /tmp/hgt-prime-shell.7o42tom1/Combined.lean`: all 16 public theorems pass without warnings.
- Named final audit `lake --old --log-level=error build GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimeOuterShell`: PASS.
- `lake env lean /tmp/hgt-prime-shell.7o42tom1/Audit.lean`: all 16 public declarations use exactly `[propext, Classical.choice, Quot.sound]`; the actual mathlib `RiemannHypothesis` definition is printed.
- `python3 scripts/formal_tools.py lint`: PASS (repository large-file warnings only); `git diff --check`: PASS.
- All owned Lean and build processes terminated normally.
- No umbrella build, no numerical experiment, no oracle, and no added axiom.
