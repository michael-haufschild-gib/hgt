# EDQ Möbius current escape and the unit endpoint defect

Stage: 3-formalized. Dependency-closed paper proof and new-declaration Lean audit complete.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH.
Objective: construct a literal growing-channel family and determine its full current behavior, rather than assuming finite-channel positivity survives an interchange of limits. RH remains open.

## Paper proof

Use all channel indices p<N (actual moduli p+1), with coefficients
`c_p=mu(p+1)/(p+1)`. The modulus-one path is identically zero and causes no
additional source term. Let H_N be the actual harmonic Möbius partial sum.
The corpus proves H_N→0 by a proved Mertens saving, ordinary Abel convergence,
and the reciprocal-zeta pole normalization. No numerical values are used.

At source integer n≥1 with n≤N, the full coefficient is exactly

`sum_(d≤N) mu(d)/d * (1-d*[d divides n]) = H_N - [n=1]`.

This uses the complete finite divisor identity, not absolute rearrangement of
the conditional harmonic Möbius series. Consequently, for every fixed positive
prefix length K and every complex s, once K≤N the weighted prefix is

`P_N(s,K)=H_N*sum_(n=1..K)n^(-s)-1`.

Thus P_N(s,K)→-1 as the channel cutoff N increases. In contrast, at any actual
nontrivial zeta zero, each fixed finite-channel combination has ordinary
endpoint limit zero as K increases, by the existing explicit combined tail
bound. These are different iterated limits, with an exact nonzero unit defect.
The source is not allowed to exchange these limits.

For every fixed K, the finite mixed-current Gram head converges as N increases
to the telescoping sum of reflection weight increments:

`sum_(n<K) delta w_n * norm(P_N(s,n+1))^2 -> (K+1)^(2*Re(s)-1)-1`.

At an actual right-half zero, the complete current is at least every such
finite Gram head. The displayed limit grows without bound as K increases.
Given any fixed real bound, first choose K so its limiting head exceeds that
bound, then use convergence in N. Hence the actual Möbius quadratic current
tends to positive infinity at every right-half zero. Reflection reverses the
entire current for this same coefficient family, so its absolute value tends
to infinity at every off-line zero. At critical-line points the source current
is identically zero for every channel cutoff.

The exact classification is therefore: at an actual zero, boundedness of this
literal growing-channel current is equivalent to critical-line location. RH
is equivalent to such boundedness at every actual nontrivial zero. More sharply,
a bounded cofinal subsequence suffices: escape to infinity excludes even
arbitrarily late returns below a fixed bound. The subsequence and bound may
depend on the zero. This changes
the remaining producer from an asserted zero value to a concrete arithmetic
boundedness target; the boundedness itself is not assumed or proved here.

## Corpus basis and positive content

EulerDeletionMixedCurrentGram supplies the full signed current, finite-prefix
bounds, and actual endpoint tail estimates. DeningerMobiusHarmonicZero and
DeningerHarmonicPartial supply the unconditional ordinary harmonic Möbius limit.
EulerDeletionRemainderMobiusInversion supplies the finite divisor-inversion
pattern. BaezDuarteMobiusPrefixApproximation identifies a related unweighted
modular prefix; it does not supply the new weighted chronological-current limit.
EulerDeletionMeanInterferenceDescent concerns another coefficient-mean quotient
and is not substituted for this source.

The positive result is an exact arithmetic unit boundary, its finite Gram
transport, and forced cofinal current escape at any off-line zero. No route is
retired; no off-line zero is asserted to exist. The independent arithmetic
bound required to close RH remains open.

## Formal certificate

Leaf: `formal/GaloisForLFunctions/RHTower/EulerDeletionMobiusCurrentEscape.lean`
(250 lines; 14 public theorems, five definitions, five private helpers).
Namespace: `RHTower.DeletionMobiusCurrent`.

- `coefficient`, `sourcePath`, `sourcePrefix`, `sourceCurrent`, `energyHead`: the actual reciprocal-modulus Möbius weights, finite deletion path, ordinary prefix, full mixed current, and its finite Gram head.
- `source_coefficient_initial`, `sourcePath_initial`, `sourcePrefix_initial`: exact finite divisor collapse and the complete harmonic term minus the unit impulse on the expanding source window.
- `sourcePrefix_tendsto`, `sourcePrefix_zero_endpoint`, `endpoint_limit_defect`: fixed positive prefixes tend to -1 as channels grow, while every fixed finite-channel path has endpoint zero at every actual zero. The two limits are kept separate.
- `energyHead_tendsto`: the fixed Gram head converges to `(K+1)^(2*Re(s)-1)-1`, at every complex source parameter.
- `sourceCurrent_partner`: full complex reflection reversal for the same literal coefficient family.
- `sourceCurrent_tendsto_atTop`, `abs_sourceCurrent_tendsto_atTop`: positive-infinite current at every right-half zero and absolute real-current escape at every off-line zero.
- `sourceCurrent_bounded_iff`, `sourceCurrent_cofinally_bounded_iff`: at any actual zero, boundedness or merely arbitrarily late bounded returns are each equivalent to critical-line location.
- `riemannHypothesis_iff_mobius_current_bounded`, `riemannHypothesis_iff_mobius_current_cofinally_bounded`: exact equivalences with Mathlib's original RH. Bounds and cofinal subsequences may depend on the zero; no uniform bound across all zeros is demanded.

Final scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_mobius.lean`, exit 0,
no diagnostics. Final leaf audit:
`LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionMobiusCurrentEscape`,
exit 0; only the new leaf rebuilt (7.2 seconds). Dependencies cached/replayed.
One umbrella import added; no full or umbrella build.

New-only axiom audit: `lake env lean /tmp/edq_mobius_axioms.lean`, exit 0.
All 19 public declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`; their dependency closure covers all five private helpers.
No added axioms, admissions, numerical premises, or external computation certificates.

These equivalences do not prove bounded returns. The arithmetic producer remains
open, and RH is neither proved nor falsified. No route is retired.

## Repository checks and cleanup

Repository lint passed once, with existing file-size warnings. The search
index was refreshed once; exact indexed search retrieves the cofinal RH
criterion. Scoped whitespace, local links, exact single umbrella wiring,
equality with the checked scratch source, and forbidden-declaration checks
passed. No owned Lean or Lake process remained. All three owned scratch Lean
sources were removed. Logs remain under `/tmp/edq_mobius` with `.api.log`,
`.check.log`, `.build.log`, `.axioms.log`, `.lint.log`, and `.index.log` suffixes.
