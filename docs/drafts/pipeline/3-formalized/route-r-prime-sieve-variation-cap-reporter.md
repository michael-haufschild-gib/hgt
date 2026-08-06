# Route R prime-sieve variation cap reporter

- **ID:** route-r-prime-sieve-variation-cap-reporter
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** [PROVED HERE] [LEAN-FORMALIZED] [ROUTE-R BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]
- **Statement:** Nested prime-sieve loss weights define a positive mass-one, coefficient-faithful all-prime reporter whose value on Route R's explicit essential-cap sequence is a strictly positive real calibration times the Hodge-mate rate and the nonzero Xi Cartier coefficient.

## Goal

Construct the bounded all-prime reporter missing from the earlier singular-Stokes audit. Coefficients
must use pre-divisor source data only, survive infinite-rank prime-log transport, and assume neither
fixed-ideal preservation, critical-line placement, cap nullity, nor RH.

This theorem does **not** assert reporter vanishing. It reduces the remaining producer to one exact
source statement: prove the independently constructed reporter is Stokes-flat.

## Exact theorem

Fix an enumeration \(e:\mathbb N\simeq\mathbb P\) of ordinary primes. Put

\[
P_n=\{e(0),\ldots,e(n-1)\},\quad
a_n=\prod_{p\in P_n}(1-p^{-1}),\quad
w_n=\frac{a_n}{e(n)},\quad
q(p)=(1-p^{-1})(2-p^{-1}).
\]

Let the formalized fixed-orientation essential-cap port be

\[
E_p(\rho)=\bigl(A_\rho q(p)\bigr)c_\rho,
\qquad A_\rho=2\Re\rho-1,
\]

where \(c_\rho\ne0\) is the multiplicity-leading Xi Cartier coefficient. Define

\[
C_e=\sum_{n\ge0}w_nq(e(n)),\qquad
\mathscr R_e(\rho)=\sum_{n\ge0}w_nE_{e(n)}(\rho).
\]

Then:

1. \(w_n>0\) for every \(n\), and \(\sum_nw_n=1\).
2. \(0<q(e(n))<2\), so \(C_e\) exists and \(0<C_e<2\).
3. The reporter series converges absolutely and
   \[
   \boxed{\mathscr R_e(\rho)=\bigl(A_\rho C_e\bigr)c_\rho.}
   \]
4. Hence \(\mathscr R_e(\rho)=0\iff A_\rho=0\iff\Re\rho=\tfrac12\).
5. Consequently \((\forall\rho,\ \mathscr R_e(\rho)=0)\iff\mathrm{RH}\).

Weights depend only on finite Euler sieve and next prime, not on \(\rho\), Xi zeros, or a fitted
physical metric. The theorem holds for every prime enumeration. Numeric calibration may depend on
enumeration, but positivity and zero detection do not.

## Complete proof

Existing prime-sieve telescope gives

\[
a_n-a_{n+1}=\frac{a_n}{e(n)}=w_n,
\qquad a_0=1,
\qquad a_n\longrightarrow0.
\]

Thus \(w_n>0\), and the nonnegative series telescopes to \(\sum_nw_n=1\).

Every ordinary prime exceeds one. Therefore \(0<e(n)^{-1}<1\), whence

\[
0<1-e(n)^{-1}<1,\qquad
1<2-e(n)^{-1}<2,\qquad
0<q(e(n))<2.
\]

Comparison \(0<w_nq(e(n))<2w_n\) proves absolute summability and
\(0<C_e<2\sum_nw_n=2\).

The formalized prime-log essential-cap identity is

\[
E_{e(n)}(\rho)=\bigl(A_\rho q(e(n))\bigr)c_\rho.
\]

Absolute convergence permits multiplication by fixed scalars to pass through the series, so

\[
\mathscr R_e(\rho)
=\sum_nw_n\bigl(A_\rho q(e(n))\bigr)c_\rho
=\left(A_\rho\sum_nw_nq(e(n))\right)c_\rho
=\bigl(A_\rho C_e\bigr)c_\rho.
\]

Now \(C_e>0\), hence \(C_e\ne0\), and \(c_\rho\ne0\). Factorization yields
\(\mathscr R_e(\rho)=0\iff A_\rho=0\). Existing centered-rate theorem gives
\(A_\rho=0\iff\Re\rho=\tfrac12\); universal quantification over Xi divisor support and the existing
support formulation of RH give final equivalence. Every dependency is unconditional. QED.

## Conjecture/falsification log

### C1 — raw independent-prime reporter [FALSIFIED]

Coefficients \(1/p\) fail: Euler's prime-harmonic series diverges. Existing Lean theorem
not_summable_naiveSingularDefect already kills this.

### C2 — coarse surviving-density reporter [FALSIFIED]

Using cofinal density \(a_n\) suppresses the conormal channel because \(a_n\to0\). This is erasure,
not descent.

### C3 — source-normal blow-up [FALSIFIED AS BOUNDED REPORTER]

Renormalizing by \(a_n^{-1}\) retains the coefficient but diverges at the cofinal boundary.

### C4 — nested loss increments [SURVIVES]

Actual variation increments \(w_n=a_n/e(n)=a_n-a_{n+1}\) are positive, total exactly one, require no
zero-dependent choices, and yield strictly positive calibration \(C_e\).

## Hostile audit

- Generic regular weighted means are literature; that parent fact is not claimed as new. Exact
  sieve-variation/Route-R-cap identification is the project-specific bridge; priority is unverified.
- Enumeration dependence does not fit the answer: every enumeration gives mass-one positive weights
  and \(C_e>0\); no \(\rho\)-dependent choice occurs.
- This does not prove RH by renaming it. Reporter vanishing remains RH-strength. Constructive gain is
  existence, convergence, source purity, positivity, and coefficient faithfulness.
- Infinite prime-log modes remain present; bounded ℓ¹ pairing is assembled only after transport, so
  finite-rank obstruction is not evaded by erasure.
- Exact factorization holds at every Xi divisor point without assuming cap nullity.

## Collision audit

Internal search covered formal corpus, all pipeline stages, failed routes, and Route R memories.
Prime-sieve telescope and essential-cap identity existed separately; no theorem combined them. Earlier
Route R records explicitly left bounded reporter construction open.

Primary-literature audit found generic weighted summability/Silverman--Toeplitz theory, regularized
determinant identities, Bost--Connes finite-prime limits, and twisted cyclic/KMS frameworks. None of
the inspected sources contained exact nested sieve-loss/Route-R-cap factorization. Negative search is
not proof of priority; status remains [NOVELTY UNVERIFIED].

## Frontier delta

Before this theorem, Route R had a coefficient-faithful cap at each prime and its cofinal essential
limit, but no positive bounded all-prime source reporter. Reporter assembly is now closed. Open core
is strictly narrower:

\[
\boxed{\text{derive }\mathscr R_e(\rho)=0\text{ from an independent pre-divisor Stokes law}.}
\]

Because \(C_e>0\) and \(c_\rho\ne0\), cancellation, corona erasure, enumeration choice, and
variable-grade averaging cannot hide a nonzero Hodge-mate rate inside this reporter.

## Gates

- [x] 0 → 1: well-posed, source-pure coefficients, hostile alternatives audited
- [x] 1 → 2: complete dependency-closed proof above, [PROVED HERE]
- [x] 2 → 3: Lean theorem and targeted build
- [ ] 3 → 4: publication-ready treatment

## Formalization certificate

Module: `GaloisForLFunctions.RHTower.RouteRPrimeSieveVariationCapReporter`.

Key unconditional theorems:

- `hasSum_routeRPrimeSieveVariationWeight`
- `routeRPrimeSieveCapCalibration_pos`
- `routeRPrimeSieveCapCalibration_lt_two`
- `summable_ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter`
- `ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter_eq`
- `ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter_eq_zero_iff`
- `ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter_eq_zero_iff_flat`
- `forall_ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter_eq_zero_iff_RH`

Verification:

- `lake env lean GaloisForLFunctions/RHTower/RouteRPrimeSieveVariationCapReporter.lean` — PASS
- `scripts/formal_tools.py lint` — PASS
- `lake --quiet build +GaloisForLFunctions.RHTower.RouteRPrimeSieveVariationCapReporter:olean` — PASS
- `#print axioms` on calibration positivity, exact factorization, zero equivalence, and RH equivalence — `[propext, Classical.choice, Quot.sound]`
- Umbrella import added to `GaloisForLFunctions/RHTower.lean`.

## Log

- 2026-08-06 — Conjectures C1--C4 attacked; only nested sieve-loss reporter survived.
- 2026-08-06 — Complete paper proof recorded; promoted directly to Stage 2.
- 2026-08-06 — Lean formalization, umbrella wiring, lint, target build, and axiom audit passed.
