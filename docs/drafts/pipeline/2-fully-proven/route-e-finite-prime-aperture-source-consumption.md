# Route E finite-prime aperture source-consumption law

- **ID:** `route-e-finite-prime-aperture-source-consumption`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / TERMINAL ROUTE-E SOURCE-CLASSIFICATION
- **Route:** E — additive Möbius / Gamma--Hankel covariance
- **Opened:** 2026-08-01
- **Computation policy:** no numerical computation; symbolic proof only
- **Statement:** Every finite prime aperture containing all primes through additive resolution
  `N` reproduces the exact Mertens self-convolution at `N`; hence the canonical cofinal-aperture
  `N^(2+o(1))` upper law is definitionally equivalent to Route E's open second-Cesàro source and
  implies RH.

## Goal

Decide whether increasing finite Euler apertures can independently produce Route E's missing
upper-signed cancellation. Exact target is not another sufficient criterion. Exact target is a
classification of what finite Euler truncation knows at its matching additive resolution.

## Frozen definitions and claim

For finite prime aperture `S`, define

```text
mu_S(n) = mu(n), if primeFactors(n) is contained in S;
          0,     otherwise.

M_S(k) = sum_(n<=k) mu_S(n),
U_S(N) = sum_(a+b=N) M_S(a) M_S(b).
```

Let `P_N={p prime : p<=N}`. Freeze:

```text
P_N subset S  ->  U_S(N)=U(N),                         (E-SC1)
U_{P_N}(N)=mobiusAdditiveTriangleSecondCesaro(N).       (E-SC2)
```

Consequently the proposition

```text
forall epsilon>0, exists C>=0, forall N,
  Re U_{P_N}(N) <= C (N+1)^(2+epsilon)                 (E-SC3)
```

is equivalent, without analytic hypotheses, to
`MobiusAdditiveTriangleSecondCesaroSubpowerUpperBound`; therefore `(E-SC3) -> RH` by the existing
unconditional double-Abel/Mellin consumer.

Falsifier: one `N`, one `S` containing `P_N`, and one antidiagonal coefficient on which the finite
Euler expansion differs from the actual Mertens coefficient.

## Internal prior-research audit

Checked Route E ledger, additive-triangle papers, half-polylog source card, one/two-prime removal,
ternary insertion, Lambert lift, LCM cubical parity, Gowers wall, Pluecker diagonal lift, all
formalized Gamma--Hankel consumers, `RHProofLab/EulerProductArithmetic.lean`, and corpus-wide exact
phrase/symbol searches. Existing work proves finite squarefree Euler expansions, one-prime windows,
two-prime sign failure, and cofinal reciprocal products on `Re s>1`. No theorem identifies the
matching finite-prime aperture with the exact Mertens self-convolution at additive resolution `N`.

`docs/support-extraction-log.md`, named by root instructions, is absent in this checkout; repository
search found no replacement carrying this exact claim.

## External state of art at 2026-08-01

Primary sources checked:

1. Liflandsky, arXiv:2607.09797: critical Möbius--Laplace decay implies RH; converse uses extra zero
   hypotheses. No source estimate.
2. Verjovsky, arXiv:2607.25002: local Fourier moments recover `M(N)` and are RH-equivalent. This is
   another source-consuming critical criterion.
3. Cantarini--Gambini--Zaccagnini, arXiv:2603.10241: weighted explicit formulas for additive
   Liouville/Möbius convolutions, not an unconditional binary critical upper source.
4. Banks--Shparlinski, arXiv:2506.08787: multiple/ternary Möbius sums; binary versions explicitly
   remain out of reach.
5. Tao--Teräväinen, JEMS 27 (2025), and Matomäki--Radziwill--Shao--Tao--Teräväinen, Inventiones 244
   (2026): logarithmic fixed-order uniformity or almost-all short-interval information, not the
   cutoff-pointwise binary law.
6. Mangerel, arXiv:2404.12117: qualitative strict inequality for a Liouville binary correlation,
   with no power saving of Route E strength.

No checked source states `(E-SC1)`--`(E-SC3)`. Novelty remains provisional: finite coefficient
stabilization is elementary; Route E source-classification application may be new.

## Heavy-conjecture ladder and hostile attacks

### C0 — diagonal positivity after Gamma sewing

Killed. Diagonal is already bounded; signed off-diagonal upper control is the only source.

### C1 — one-prime removal makes transfer positive

Killed. Existing exact two-prime kernel has a negative lobe already at `(2,3)`.

### C2 — average over increasingly many finite prime apertures

Hostile question: does cofinal averaging introduce cancellation unavailable at one aperture?

Attack: at matching resolution `N`, any aperture containing `P_N` has already stabilized every
Möbius coefficient needed by every `a+b=N` term. No residual aperture variable remains to average.
The cofinal head is the target, not an approximation to it.

### C3 — choose sparse cofinal apertures adapted to favorable returns

Attack: if aperture misses a prime `p<=N`, it changes source coefficients rather than estimates the
actual Route E source. Once it covers `P_N`, `(E-SC1)` removes selection freedom. A target-adapted
choice before coverage is a different arithmetic function; a choice after coverage is inert.

### C4 — use finite Euler Hilbert positivity before taking cofinal limit

Killed inside this source class. Positivity must either discard Möbius parity, contradicting exact
coefficient recovery, or retain parity and arrive at `U(N)` unchanged. Existing negative-lobe and
LCM-cubic walls describe the two failures.

### C5 — genuinely nonlocal all-prime cancellation law

Survives. It must act before finite-aperture coefficient stabilization and prove cancellation among
actual signed Möbius coefficients. Such a law is not supplied by finite Euler algebra; through the
existing consumer it proves RH.

## Anti-theatre audit

- **New delta if proved:** exact all-aperture stabilization and equivalence of canonical finite
  Euler upper law with the open Mertens second-Cesàro source.
- **Not new:** finite Euler subset expansion itself; the already-formalized source-to-RH consumer.
- **Does not prove:** `(E-SC3)`, bounded Gamma--Hankel returns, or RH.
- **Closes:** finite/cofinal Euler aperture as an independent Route E producer.
- **Positive survivor:** a nonlocal all-prime signed cancellation theorem not obtained by
  truncating, averaging, taking norms of, or selecting finite Euler heads.
- **Source-consumption test:** no target estimate is assumed. The conclusion explicitly shows
  where the target is consumed.

## Paper-proof obligations

- [x] Prove prime-factor coverage: `n<=N`, `n>0` implies `primeFactors(n) subset P_N`.
- [x] Prove `mu_S(n)=mu(n)` for `n<=N` when `P_N subset S`, including `n=0,1`.
- [x] Prove `M_S(k)=M(k)` for every `k<=N`.
- [x] Prove both antidiagonal coordinates are at most `N`, yielding `(E-SC1)`.
- [x] Compose with exact second-Cesàro identity for `(E-SC2)`.
- [x] Prove proposition equivalence `(E-SC3)` and unconditional implication to RH.
- [x] Attack prime powers, non-prime aperture entries, duplicate primes, sparse apertures, and
      cutoff-dependent apertures.

## Dependency-closed paper proof

Put `P_N={p in Nat : p<=N and p is prime}`. Let `n<=N`.

If `n=0`, then `mu(n)=0`, so any aperture mask has the same coefficient. If `n>0` and
`p in primeFactors(n)`, then `p` is prime and `p|n`. Divisibility with `n>0` gives `p<=n<=N`, so
`p in P_N`. Thus `primeFactors(n) subset P_N`; if `P_N subset S`, then
`primeFactors(n) subset S` and `mu_S(n)=mu(n)`. This includes `n=1`, whose prime-factor set is
empty.

For every `k<=N`, every index in `M_S(k)=sum_(n<=k)mu_S(n)` is at most `N`; coefficientwise
equality therefore gives

```text
M_S(k)=M(k).                                             (1)
```

If `(a,b)` belongs to the natural antidiagonal at `N`, then `a+b=N`, hence `a<=N` and `b<=N`.
Applying `(1)` twice in every finite summand yields

```text
U_S(N)=sum_(a+b=N) M_S(a)M_S(b)
      =sum_(a+b=N) M(a)M(b)
      =U(N).                                             (2)
```

This proves `(E-SC1)`. Taking `S=P_N` and using the already-proved exact finite identity

```text
mobiusAdditiveTriangleSecondCesaro(N)=U(N)
```

proves `(E-SC2)`. Substitute this pointwise equality into both sides of `(E-SC3)`. Quantifiers,
constant sign, exponent, and one-sided real-part inequality are unchanged, so `(E-SC3)` is iff
`MobiusAdditiveTriangleSecondCesaroSubpowerUpperBound`. Existing unconditional theorem
`mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_implies_riemannHypothesis` gives the claimed
RH consequence. No Littlewood converse is used.

### Edge cases

1. **Prime powers:** aperture mask admits them when their prime lies in `S`, but their Möbius
   coefficient is zero unless squarefree; equality remains exact.
2. **Non-prime aperture entries:** never occur in a prime-factor set and are inert.
3. **Duplicate primes:** apertures are finite sets, so duplication is impossible.
4. **`N=0` and `N=1`:** only zero/empty-factor-set coefficients occur; argument above applies.
5. **Sparse apertures:** if `P_N` is not covered, resulting polynomial is a different source and no
   equality is asserted.
6. **Cutoff-dependent apertures:** dependence on `N` is arbitrary. Coverage alone triggers `(2)`;
   after coverage, selection has no effect.
7. **Larger cofinal heads:** primes above `N` cannot divide a positive integer at most `N`, so they
   are invisible at resolution `N`.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure statement, falsifier, novelty audit, hostile ladder
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [ ] 2 -> 3 formalized: unconditional Lean theorem, umbrella wiring, lint and axiom audit
- [ ] 3 -> 4 publication-ready

## Log

- 2026-08-01 — exact finite-aperture source-consumption claim frozen after internal and external
  audits; Lean work blocked pending paper closure.
- 2026-08-01 — dependency-closed proof completed; all finite and cutoff edge cases discharged.
