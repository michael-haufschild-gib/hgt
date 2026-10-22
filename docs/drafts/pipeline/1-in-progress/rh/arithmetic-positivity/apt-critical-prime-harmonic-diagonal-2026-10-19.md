# Critical prime limit: exact harmonic divisor diagonal

- **ID:** APT-CRITICAL-PRIME-HARMONIC-DIAGONAL
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** apt-critical-single-source-prime-limit-2026-10-19.md
- **Statement:** Regroup the verified complete native prime limit by harmonic, then classify every signed arithmetic coefficient.

## Scope and gates

The input is the actual-source limit already formalized in
`FactorialCriticalPrimeLimit.lean`. A finite prime or harmonic truncation does not satisfy
this task. General divisor convolution and rearrangement are classical baseline machinery;
no significant-result credit is assigned to those alone. Accepted count remains **0/100**.
README is read-only. No numerical experiments, new axioms, heartbeat increases, full
builds, commits, or pushes. One owned foreground Lean invocation at a time.

- [x] Specify the exact native endpoint and dependency-closed paper proof.
- [x] Search prior corpus work before starting Lean; inspect available candidates.
- [x] Verify reusable APIs in this toolchain and formalize the full rearrangement.
- [x] Formalize the sharp coefficient sign classification.
- [x] Pass targeted build, actual-file, axiom and index checks.
- [x] Run global lint and record its unrelated failures without claiming a pass.
- [ ] Audit novelty and native significance; do not count a classical restatement.

## Exact endpoint and paper proof

Use the verified notation `w_k=χ(k)/k²` and
`J_k=∫_(v>1) v⁻²(1-cos(2πkv/12))dv`. Zero-index terms are defined as zero.
For positive integers `m`, put

`S(m)=Σ_(d|m) d Λ(d)`,

`A(m)=χ(m) Σ_(d|m) d Λ(d) χ(m/d)`.

The proposed exact native identity is

`factorialCriticalPrimeLimit=(4/π⁴) Σ_(m≥1) A(m) J_m / m⁴`.

1. Start from the already verified full series
   `(4/π⁴) Σ_(r≥2) Σ_(l≥1) [Λ(r)/r] w_(rl) w_l J_(rl)`.
   Since `|χ|≤1` and `0≤J≤2`, the absolute summand is at most
   `2 Λ(r)/(r³ l⁴)`. This is summable: compare the prime factor with the existing
   summable `Λ(r)/r²` majorant and use the convergent fourth-power series.
   Thus regrouping by `m=rl` is valid for the complete series.
2. For a fixed `m=rl`, the summand equals
   `r Λ(r) χ(m) χ(m/r) J_m/m⁴`. Summing over the divisors `r|m` gives `A(m)`.
   The missing divisor `r=1` contributes zero because `Λ(1)=0`. All zero-index
   terms vanish. The regrouped series is absolutely convergent.
3. If `m` is odd, every divisor and quotient is odd, hence `A(m)=S(m)`.
   If `4|m`, then `χ(m)=0`, hence `A(m)=0`.
   If `m=2n` with `n` odd, split the divisors into odd `d|n` and even `2d`.
   The odd terms contribute `S(n)`: both outer and quotient signs are negative.
   Among even divisors, only `2` can have nonzero von Mangoldt value. Indeed,
   an even prime power dividing `2n` must be `2`, because `n` is odd. Its term
   is `-2 log 2`. Consequently `A(2n)=S(n)-2 log 2`.
4. `A(1)=0`, and `A(2)=-2 log 2<0`. If odd `n>1`, choose a prime divisor
   `p|n`. It satisfies `p≥3`, and nonnegativity of every summand gives
   `S(n)≥p log p>2 log 2`. Therefore

   - `A(m)<0` exactly when `m=2`;
   - `A(m)=0` exactly when `m=1` or `4|m`;
   - `A(m)>0` exactly when `2<m` and `4` does not divide `m`.

This is one negative **harmonic channel**, not a rank-one operator claim. The scalar
prime limit still contains both signs; this identity alone does not determine its total
sign or the complete Weil sign. The positive survivor is the exact coefficient
classification and the absolutely convergent decomposition of the actual-source limit.

## Prior work and reuse audit

- The parent card records 241 paginated APT lexical hits, with stable total and no
  missing pages. Existing `GeneralDivisorBernoulliFilterClassification.lean` already
  classifies the dyadic stencil and its Fourier multiplier; do not recount those.
- The deep query for dyadic prime/divisor/harmonic regrouping completed; all twenty
  candidate lemmas and twenty source arguments were screened. It mostly recovered
  generic or unrelated divisor work. Semantic coverage was unmeasured, so this search
  does not establish absence or priority. JSON:
  `/tmp/apt-critical-dyadic-divisor-reindex-deep.json`.
- `WeilPhiDoobDivisorEnergy.lean` already provides a complete prime/divisor regrouping
  for a different theta-ground-state source. Reuse its summation mechanism when applicable.
- All seven `vonMangoldt divisors` hits were screened. The relevant existing
  `constrainedProlate_sum_vonMangoldt_divisors_ge_two` uses mathlib's
  `ArithmeticFunction.vonMangoldt_sum` to collapse an unweighted divisor sum to `log m`;
  the present coefficient instead contains `d Λ(d)` and the dyadic quotient sign.
- API-oriented searches are recorded in
  `/tmp/apt-critical-diagonal-tsum-search.json` and
  `/tmp/apt-critical-diagonal-von-mangoldt-search.json`; their concrete candidates
  must still be checked against source and Lean before use.
- The `tsum divisorsAntidiagonal` query recovered
  `RHTower/ConstrainedProlatePrimeShiftDoubleSum.lean`. Its public
  `tsum_prodMul_fiber_decomposition` already proves general regrouping by a product
  fiber. Mathlib also supplies `HasSum.tsum_fiberwise`; use that primitive directly
  where it avoids an unnecessary prolate-source dependency. No new regrouping
  principle is claimed.
- A module-filtered lexical query returned no mathlib von Mangoldt declarations;
  the default hybrid query `vonMangoldt_apply_prime` recovered the exact installed
  mathlib theorem and related APIs. This confirms that lexical absence is not a
  dependency-corpus absence. Source and scratch Lean checks remain authoritative.
- The hybrid query `natural number not power of two has an odd prime divisor`
  recovered both `Nat.eq_two_pow_or_exists_odd_prime_and_dvd` and the exact stronger
  `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt`. The latter supplies the
  positive coefficient witness directly. `isPrimePow_iff_unique_prime_dvd` rules
  out any other even negative von Mangoldt charge. Their installed source statements
  and scratch API checks were verified; no replacement factorization proof is needed.

## Continuation state

`/tmp/apt_critical_diagonal.lean` passed the complete native double-series regrouping,
absolute convergence, the exact coefficient at two, and the sharp three-way sign
classification. Initial Lean failures were limited to fiber-sum coercions, equality
orientation, and a modular-case tactic that continued after closing its goal; those
were corrected. The full scratch check exited 0 with an empty diagnostic log. Installed
`formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeHarmonicDiagonal.lean`
with five public declarations and an APT umbrella import. Its targeted build, direct
actual-file audit, actual-import four-theorem axiom audit, and index refresh all passed.
The actual-file log is empty. Every axiom list contains only `propext`, `Classical.choice`,
and `Quot.sound`. All five public declarations appear in the generated API index.
`/tmp/apt_critical_diagonal_api.lean` passed all initial API probes. The existing
prime-limit package remains unchanged and retains its completed actual-file audits.

## Verification evidence

- `/tmp/apt_critical_diagonal_build.log`: targeted leaf build, exit 0.
- `/tmp/apt_critical_diagonal_actual.log`: direct actual-file audit, exit 0, empty log.
- `/tmp/apt_critical_diagonal_actual_axioms.log`: four public theorems, exit 0;
  standard axioms only.
- `/tmp/apt_critical_diagonal_index.log`: exit 0; all five exports verified.
- `/tmp/apt_critical_diagonal_lint.log`: exit 1. Concurrent modules
  `BezoutValuationIncidence.CoprimeMobiusSignAndEvenDilationMeans`,
  `TransHorizonIncidenceMechanics.FermiHomogeneousEnergyAndPronicComparison`, and
  `TransHorizonIncidenceMechanics.FermiPrimeExponentGramBounds` are not reachable
  from their area umbrellas. `formal/LEAN_API.md` and `formal/LEAN_OVERVIEW.md`
  became stale during concurrent source changes. No own-leaf lint error was reported.
- Completed scratch Lean sources were removed after validation; logs and search JSON
  are retained. No placeholder proof, new axiom, unsafe declaration, or heartbeat change.

The result isolates one negative harmonic channel in the actual complete prime limit,
but it does not prove the total prime-form sign. Generic convolution and regrouping are
classical. Keep the significant-result count at **0/100** until a native consequence and
priority audit justify credit. The next candidate is tracked in
`apt-critical-translated-prime-form-2026-10-19.md`; it seeks a coefficient-`ℓ²` bound
independent of the number of offsets, using the exact diagonal on a translated family.

## Further candidate, not yet a theorem

For a fixed finite real coefficient pattern `b_j`, translate the source indices to
`N+j` and let `N→∞`. Let `P_b(t)=Σ_j b_j exp(2πijt)`. A prospective full-profile
limit replaces `J_m` above with

`J_m(b)=∫_(v>1) v⁻²(1-cos(2πmv/12)) |P_b(mv)|² dv`.

The resonance calculation gives this expression on paper: the surviving pair has
`k=rl`, and the offset difference contributes `cos(2πk(i-j)v)`; summing in `i,j`
gives `|P_b(kv)|²`. Uniform prime admission for a fixed translated pattern must be
proved before passing through every prime power. This extension, any periodized
kernel sign, and any full Weil consequence remain open and receive no credit.

## Log

- 2026-10-19 — Native diagonal and sharp coefficient classification derived on paper;
  corpus audit recorded before Lean. No contribution credited.
