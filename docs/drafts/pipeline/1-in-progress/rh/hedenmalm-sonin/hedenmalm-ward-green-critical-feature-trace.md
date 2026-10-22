# Hedenmalm Ward--Green critical-feature trace

- **ID:** `P-G150`
- **Stage:** `1-in-progress`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [CORPUS-NEW SYNTHESIS] [NOT RH]`
- **Parent:** `P-G149`
- **Module:** `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmWardGreenCriticalFeatureTrace.lean`

## Conjecture loop

1. `[CONJECTURE]` P-G149's unbounded Ward--Green graph may fail to be trace-legal because its
   inverse-square weight is singular at the infinitely populated critical line.
2. `[PROVED]` Each exponential reflection-pair defect has exact divided-difference form

   ```text
   exp(2ka)+exp(-2ka)-2 = 4 sinh(ka)^2.
   ```

   On `|a|<=1/2`, `k<=5`, the mean-value bound
   `|sinh(ka)|<=|ka| cosh(5/2)` cancels `a^(-2)` before summation.
3. `[PROVED]` Dropping the two negative five-shift legs yields one explicit finite constant
   `C_W` with

   ```text
   fiveShiftRenormalizedKreinDefect(1,q) <= C_W
   ```

   for every Xi multiplicity copy, including the totalized diagonal.
4. `[PROVED]` Ward--Green critical-feature current factors exactly as

   ```text
   renormalizedKreinDefect(1,q) * |ell_q(k_t)|^2.
   ```

   The first factor is nonnegative and bounded by `C_W`; the second is square-summable because
   the critical feature is a sum of two legal Cauchy tests. Hence every fixed real center `t`
   gives an absolutely summable nonnegative global trace.
5. `[PROVED]` Critical-feature evaluation never vanishes. The scalar defect vanishes exactly on
   the critical line. Therefore, for every fixed `t`,

   ```text
   WardGreenTrace(t)=0  <->  RH.
   ```

## New knowledge

Singular transverse normalization and trace-classness are compatible. The cancellation must be
performed at amplitude level (`sinh(a)/a`) before the divisor sum; bounding the inverse-square
coefficient separately would be false. P-G149's unbounded inverse graph has a canonical legal
trace on every critical-feature channel, with an explicit height-independent scalar majorant.

Remaining obstruction is no longer domain, kernel, reporter, height escape, or absolute
summability. It is arithmetic evaluation of a concrete Hermitian Ward--Green trace. Existing
prime--Gamma formulas evaluate holomorphic Weil polarization, while this trace uses same-copy
Hermitian energy. Next loop must construct the missing source real/anti-holomorphic trace or prove
a source inequality comparing it to the four-term prime--Gamma formula.

## Gates

- [x] divided-difference hyperbolic bound
- [x] uniform normalized five-shift ceiling
- [x] exact Ward--Green/current factorization
- [x] fixed-feature absolute summability
- [x] nonnegative trace and exact RH zero criterion
- [x] direct Lean check
- [x] exact module build
- [x] axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)
- [ ] umbrella build
- [ ] arithmetic Hermitian source evaluation
- [ ] unconditional RH
