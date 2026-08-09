# Burnol all-prime completion and singular-potential entrance wall

- **ID:** `burnol-all-prime-completion-singular-potential-entrance-wall`
- **Stage:** 3-formalized
- **Formalized companion:** `burnol-all-prime-completion-singular-potential-entrance-wall-formalized.md`
- **Type:** THEOREM / PRE-DIVISOR SOURCE CONSTRUCTION / EXACT DOMAIN WALL
- **Scientific status:** `[PAPER-PROVED] [SOURCE-PURE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** R
- **Parents:** `burnol-xi-prime-two-completion-landing`,
  `burnol-gamma-bockstein-first-wall-extraction-law`,
  `route-r-reciprocal-log-fisher-half-density-entrance-wall`, and
  `xi-physical-prime-log-aperture-fusion-cross-kernel`
- **Lean:** `RHTower/BurnolAllPrimeCompletionWall.lean` (with `RHTower/BurnolPrimeLogSummability.lean`).

## Result

The reciprocal-log entrance vector is not an invented detector.  It is the boundary of one
explicit singular potential applied to the already constructed unit--double valuation shuttle.
For every ordinary prime this boundary admits a coefficient-faithful Burnol-to-Xi completion.
Across all primes, inverse completion of its Xi conormal has a sharp Hilbert-domain wall:

\[
 \left(\frac{c_\rho}{p\log p\,C_p(\rho)}\right)_{p\in\mathbb P}
 \in \ell^2(\mathbb P)
 \quad\Longleftrightarrow\quad
 \Re\rho\le \frac12,                                      \tag{AW0}
\]

where `c_rho` is any nonzero leading Xi Cartier coefficient and

\[
 C_p(w)=\frac{w^2(w-1)}{2(p^w-1)}.                         \tag{AW1}
\]

The completed Xi conormal itself is always square-summable.  The physical prime-endpoint
presentation differs from the strict source-boundary presentation by a sequence whose inverse
completion is square-summable throughout the whole critical strip.  Thus the wall in `(AW0)` is
neither a choice of reader nor a diagonal remainder: it is exactly the failure of the singular
pre-divisor boundary to survive inverse completion on a right-half Xi fibre.

This does not prove that the inverse-completed boundary lands in the fixed physical conormal.
It constructs the boundary, the potential, and both coefficient-faithful presentations, and
reduces the remaining producer to closed source admission of this one boundary-at-infinity.

## 1. General prime-window completion

For an ordinary prime `p`, use the Burnol sub-window `[p^(-1),1]`.  Its completed Mellin source is

\[
 F_p(w)=\Gamma_{\mathbb R}(w)\,(p^w-1)\frac{\zeta(w)}w .    \tag{AW2}
\]

The formula follows directly from the general sub-window identity

\[
 (d^{-w}-c^{-w})\left(-\frac{\zeta(w)}w\right)
\]

at `c=p^(-1), d=1`.  If `0<Re w<1`, then

\[
 |p^w|=p^{\Re w}>1,
\]

so `p^w-1` and `C_p(w)` are nonzero.  With the standard completion

\[
 \xi(w)=\frac12w(w-1)\Gamma_{\mathbb R}(w)\zeta(w),
\]

one obtains the exact pre-divisor identity

\[
 \boxed{C_p(w)F_p(w)=\xi(w).}                             \tag{AW3}
\]

Let `rho` be a Xi divisor point of multiplicity `m`, and write

\[
 \xi(w)=(w-\rho)^m(c_\rho+O(w-\rho)),\qquad c_\rho\ne0.
\]

Since `C_p(rho) != 0`, `(AW3)` gives

\[
 F_p(w)=(w-\rho)^m
       \left(\frac{c_\rho}{C_p(\rho)}+O(w-\rho)\right).    \tag{AW4}
\]

Equivalently, for the first divided vector, including the confluent value at `s=rho`,

\[
 C_p(s)[F_p]_{\rho,s}=[\xi]_{\rho,s}.                     \tag{AW5}
\]

No simplicity hypothesis occurs.  Equation `(AW5)` is the all-prime functorial extension of the
existing prime-two landing.

## 2. Singular potential of the strict valuation boundary

The constructed unit--double valuation shuttle and physical endpoint coefficients are

\[
 R_p=-\frac{\log p}{p+1},\qquad
 W_p=\frac{\log p}{p},\qquad
 E_p=\frac{\log p}{p(p+1)},                              \tag{AW6}
\]

and the pre-divisor response-renormalization identity is

\[
 W_p+R_p=E_p.                                             \tag{AW7}
\]

Introduce the fixed prime-log Green potential

\[
 Q_p=-\frac{p+1}{p(\log p)^2}.                            \tag{AW8}
\]

It is singular as an all-prime potential, but its unit--double boundary is the square-summable
coefficient

\[
 \boxed{A_p:=Q_pR_p=\frac1{p\log p}.}                    \tag{AW9}
\]

At every finite prime aperture this is a literal strict boundary, because the valuation shuttle
is prime-diagonal and linear, so multiplication by `Q_p` commutes with its two-aperture
difference.  The cofinal boundary converges in `ell^2(P)` since

\[
 \sum_p |A_p|^2\le\sum_{n\ge2}\frac1{n^2(\log n)^2}<\infty.\tag{AW10}
\]

The potentials themselves escape; finite exactness therefore does not assert closed-range
exactness of the cofinal Hilbert complex.  The resulting class is an explicit boundary at
infinity, not a formally declared zero class.

Multiplying `(AW7)` by `Q_p` yields the second presentation

\[
 Q_pW_p+A_p=Q_pE_p=-\frac1{p^2\log p}.                    \tag{AW11}
\]

Thus strict source-boundary and physical endpoint coefficients differ by an explicit
inverse-square correction before any Xi specialization.

## 3. Exact inverse-completion wall

Weight the leading completed Xi conormal in prime `p` by `A_p`.  Its completed and uncompleted
coefficients are respectively

\[
 V_{\rho,p}=\frac{c_\rho}{p\log p},\qquad
 U_{\rho,p}=\frac{c_\rho}{p\log p\,C_p(\rho)}.            \tag{AW12}
\]

The completed vector `V_rho` is always in `ell^2(P)`.  Put `sigma=Re rho`.  From `(AW1)`,

\[
 U_{\rho,p}
 =K_\rho\frac{p^\rho-1}{p\log p},\qquad
 K_\rho=\frac{2c_\rho}{\rho^2(\rho-1)}\ne0.              \tag{AW13}
\]

### Theorem 1 — sharp domain classification

For every `rho` in the open critical strip and every nonzero `c_rho`, `(AW0)` holds.

### Proof

Suppose first that `sigma<=1/2`.  For every prime,

\[
 |p^\rho-1|\le p^\sigma+1\le \sqrt p+1\le2\sqrt p.
\]

Therefore

\[
 |U_{\rho,p}|^2
 \le \frac{4|K_\rho|^2}{p(\log p)^2}.
\]

The majorant is summable even over all integers `n>=2`, by the integral test for
`1/(x(log x)^2)`.  Hence `U_rho` is square-summable.

Now suppose `sigma=1/2+delta` with `delta>0`.  Reverse triangle inequality gives

\[
 |p^\rho-1|\ge p^\sigma-1\ge\frac12p^\sigma
\]

for all sufficiently large primes.  Since every positive power dominates `log^2 p`, one also has

\[
 \frac{p^{2\delta}}{(\log p)^2}\ge1
\]

eventually.  Consequently

\[
 |U_{\rho,p}|^2
 \ge \frac{|K_\rho|^2}{4}
      \frac{p^{2\delta}}{p(\log p)^2}
 \ge \frac{|K_\rho|^2}{4p}
\]

for all sufficiently large primes.  Euler's divergence of `sum_p 1/p` proves that `U_rho` is not
square-summable.  This proves `(AW0)`. `QED`

The proof uses no prime number theorem and no zero-density estimate.  The critical exponent is
forced jointly by the `p^(-1)` boundary coefficient and the `p^(Re rho)` inverse-completion gain.

## 4. Physical correction is harmless on the whole strip

Let

\[
 B_{\rho,p}:=
 \frac{c_\rho}{p^2\log p\,C_p(\rho)}
 =K_\rho\frac{p^\rho-1}{p^2\log p}.                     \tag{AW14}
\]

For `0<sigma<1`,

\[
 |B_{\rho,p}|^2
 \ll_\rho \frac{p^{2\sigma}}{p^4(\log p)^2}
 \ll_\rho \frac1{p^2},                                  \tag{AW15}
\]

so `B_rho` belongs to `ell^2(P)` throughout the critical strip.  Inverse-completing `(AW11)` gives

\[
 \frac{Q_pW_pc_\rho}{C_p(\rho)}=-U_{\rho,p}-B_{\rho,p}.  \tag{AW16}
\]

Hence

\[
 \left(\frac{Q_pW_pc_\rho}{C_p(\rho)}\right)_p\in\ell^2
 \quad\Longleftrightarrow\quad
 U_\rho\in\ell^2
 \quad\Longleftrightarrow\quad
 \Re\rho\le\frac12.                                     \tag{AW17}
\]

Thus the source-boundary and fixed physical endpoint presentations have the same entrance wall.
The trace-class response correction cannot create or erase it.

## 5. Consequence for Route R

Let `rho` be a hypothetical right-half Xi divisor.  Lean already proves the explicit Burnol
current `J_rho` is strictly positive there.  The theorem above supplies an independent route to
the required contradiction:

1. `A=(1/(p log p))_p` is the cofinal limit of explicit finite strict unit--double source
   boundaries;
2. its completed Xi conormal `V_rho` is in `ell^2(P)`;
3. its coefficient-faithful inverse completion is the explicit `U_rho`;
4. `U_rho` is not in `ell^2(P)` when `Re rho>1/2`;
5. physical endpoint replacement changes `U_rho` only by the always-square-summable `B_rho`.

Therefore a source-derived closed landing of this one boundary at every Xi fibre excludes every
right-half divisor before the local `J_rho` contradiction is invoked.  Equivalently, it proves the
needed nonpositive-`J_rho` statement vacuously by independently ruling out its domain of
quantification.

The remaining theorem is concrete:

> **SINGULAR BOUNDARY CLOSED LANDING.**  The cofinal finite boundaries `(A_p)` obtained from the
> prime-log Green potential `(Q_p)` remain a boundary after coefficient-faithful inverse
> Burnol--Xi completion on the fixed same-fibre physical conormal.

This is strictly weaker than a full GNS comparison, source-dagger isometry, or all-vector
completion theorem.  It concerns one written potential, one strict valuation boundary, and one
explicit graph-domain assertion.  It is not proved here.

**2026-08-08 correction.** Interpreted as ordinary `ell^2` valuation-range exactness, this target
is false: unique potential `Q` is not square-summable and the range is nonclosed. Valid replacement
is the uniform finite multiplicity-jet estimate / closed inverse-completion domain admission in
`burnol-all-prime-window-hilbert-cartier-jet-wall.md`. That successor also constructs the honest
all-prime Burnol source vector and an unconditional reciprocal-Stokes sewn landing.

## 6. Conjecture / proof-or-fail loop

1. **Prime-two diagonal completion signs `J_rho`.** `[FAILED]`  Its negative normal slope is added
   to the bare current; diagonal completion does not orient the bare Bockstein line.
2. **An arbitrary reciprocal-log sequence can be declared the source producer.** `[FAILED]`
   Without provenance this only repackages the entrance criterion.
3. **The unit--double valuation shuttle has the required singular potential.** `[PROVED]`
   Equations `(AW8)`--`(AW10)` identify it exactly and make every finite stage a strict boundary.
4. **Prime-two completion is exceptional.** `[FAILED]`  Equations `(AW2)`--`(AW5)` construct the
   coefficient-faithful completion functorially for every ordinary prime and every Xi
   multiplicity jet.
5. **The all-prime wall needs prime asymptotics.** `[FAILED]`  The upper side is an integer-series
   comparison; the lower side uses only power-over-log growth and Euler divergence.
6. **The physical endpoint correction may absorb the divergence.** `[FAILED]`  Its inverse
   completion is square-summable on the entire strip by `(AW14)`--`(AW17)`.
7. **Finite exactness already proves cofinal exactness.** `[FAILED]`  The singular potentials
   escape, so closed range is real content.  This is precisely the surviving source theorem.
8. **Strongest survivor.** `[PAPER-PROVED]`  One explicit strict pre-divisor boundary has a
   functorial all-prime Xi completion and a sharp inverse-completion domain wall, with a robust
   physical endpoint presentation modulo an everywhere-admissible correction.

## 7. Anti-theatre audit

- The theorem does not assume `Re rho=1/2`, `J_rho<=0`, RH, source-dagger conservation, or fixed
  physical lift equality.
- New source object is forced by existing valuation response coefficient; the weight
  `1/(p log p)` is derived as `Q_pR_p`, not selected after inspecting the desired wall.
- General prime completion is an exact analytic identity, including multiplicity-leading Cartier
  coefficients.
- Divergent and convergent sides are both proved; no numerical experiment or asymptotic heuristic
  is used.
- Claimed progress is not RH: closed landing of the singular boundary remains open and is stated
  explicitly.

## Lean formalization (2026-08-09)

Module: `RHTower/BurnolAllPrimeCompletionWall` (with `RHTower/BurnolPrimeLogSummability`).

| Paper item | Lean declaration |
|---|---|
| `(AW1)` | `burnolAllPrimeCompletionMultiplier`, `nat_cpow_sub_one_ne_zero`, `burnolAllPrimeCompletionMultiplier_ne_zero` |
| `(AW2)` | `burnolAllPrimeCompletedMellin`, `soninMellinEvaluation_primeWindow_eq` |
| `(AW3)` | `burnolAllPrimeCompletionMultiplier_mul_completedMellin` |
| `(AW6)`, `(AW7)` | `burnolValuationShuttle`, `burnolPhysicalEndpointWeight`, `burnolEndpointResponse`, `burnolPhysicalEndpointWeight_add_valuationShuttle` |
| `(AW8)`, `(AW9)` | `burnolPrimeLogGreenPotential`, `burnolSourceBoundary`, `burnolPrimeLogGreenPotential_mul_valuationShuttle` |
| `(AW10)` | `burnolSummable_sourceBoundary_sq` |
| `(AW11)` | `burnolPrimeLogGreenPotential_mul_endpointResponse`, `burnolPrimeLogGreenPotential_physical_presentation` |
| `(AW12)`, `(AW13)` | `burnolAllPrimeInverseCompletionCoefficient`, `burnolAllPrimeInverseCompletionConstant`, `burnolAllPrimeInverseCompletionCoefficient_eq` |
| `(AW0)` / Theorem 1 | `summable_burnolAllPrimeInverseCompletionCoefficient_sq_iff` (both sides: `..._of_re_le_half`, `not_..._of_half_lt_re`) |
| `(AW14)`, `(AW15)` | `burnolAllPrimePhysicalCorrection`, `burnolAllPrimePhysicalCorrection_eq`, `burnolSummable_allPrimePhysicalCorrection_sq` |
| `(AW16)` | `burnolAllPrimePhysical_inverse_completion` |
| `(AW17)` | `summable_burnolAllPrimePhysicalPresentation_sq_iff` |
| `(AW4)` | `tendsto_burnolAllPrimeMultiplicityJet` |
| `(AW5)` | `burnolAllPrimeCompletionMultiplier_mul_dslope_completedMellin`, `burnolAllPrimeCompletedMellin_eq_zero_of_xi_eq_zero` |

Supporting infrastructure built for the wall: `burnolSummable_prime_one_div_mul_log_sq` (telescoping
comparison), `burnolNotSummable_prime_one_div`, `burnolEventually_log_pow_le_rpow`,
`burnolPrimeWallThreshold`.

## Gates

- [x] strict finite-stage source boundary
- [x] singular potential written explicitly
- [x] functorial all-prime Burnol--Xi completion
- [x] multiplicity-faithful leading-coefficient transport
- [x] exact `ell^2` entrance-wall classification
- [x] physical endpoint correction proved harmless across the strip
- [ ] specialist novelty audit
- [ ] singular boundary closed landing
- [x] Lean formalization: all numbered statements `(AW0)`--`(AW17)` unconditional in Lean
- [ ] RH

## Log

- 2026-08-08 — derived the prime-log Green potential of the unit--double response, generalized
  prime-two completion to every prime, proved the sharp all-prime inverse-completion wall, and
  identified the physical endpoint correction as strip-uniformly admissible.
- 2026-08-09 — first unconditional Lean layer built and umbrella-wired; see the Lean
  formalization table above for the exact declaration-to-equation map.
