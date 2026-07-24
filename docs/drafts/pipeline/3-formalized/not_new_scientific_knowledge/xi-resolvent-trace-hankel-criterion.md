# RH from the resolvent trace, on Euler-ray (prime) data

- **ID:** `xi-resolvent-trace-hankel-criterion`
- **Stage:** 3 — formalized in Lean 4
- **Lean module:** `GaloisForLFunctions.RHTower.XiResolventTraceHankelCriterion`
- **Status:** unconditional; a *sufficient* condition for RH stated on prime--Gamma data

## What this closes

The Gaussian ladder (`gaussian-heat-trace-rh-criterion.md`) tests the squared divisor with
`exp (-t w)`.  Those weights are analytically ideal but the corpus has no Lean explicit formula for
Gaussian tests, so the ladder could not be attacked from the prime side inside Lean.

Replacing the Gaussian weight by the **resolvent weight** `(w + X)^(-1)` keeps the whole
moment-positivity structure and lands exactly on data the corpus already computes from primes:

```text
sum_q (w q + x^2)^(-1) = logDeriv xi (1/2 + x) / x ,
```

which for `x > 1/2` is the absolutely convergent prime--Gamma expression
`1/s + 1/(s-1) + logDeriv Gamma_R s - L(Lambda, s)` at `s = 1/2 + x`.

## Formalized

```lean
def xiResolventPoint (X : ℝ) (q : XiZeroCopy) : ℂ := (xiSpectralPoint q ^ 2 + (X : ℂ))⁻¹

def xiResolventTrace (X : ℝ) (p : Polynomial ℝ) : ℂ :=
  ∑' q, xiResolventPoint X q * evalRealPolynomial p (xiResolventPoint X q) ^ 2

theorem riemannHypothesis_of_forall_xiResolventTrace_re_nonneg {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ p : Polynomial ℝ, 0 ≤ (xiResolventTrace X p).re) : RiemannHypothesis

def xiResolventMoment (n : ℕ) (X : ℝ) : ℂ := ∑' q, xiResolventPoint X q ^ (n + 1)

theorem xiResolventMoment_zero_eq_logDeriv {x : ℝ} (hx : 0 < x) :
    xiResolventMoment 0 (x ^ 2) = logDeriv xi ((1 / 2 : ℂ) + (x : ℂ)) / (x : ℂ)
```

Supporting: `xiSpectralSq_add_ofReal_re_pos`, `xiSpectralSq_add_ofReal_ne_zero`,
`xiResolventPoint_ne_zero`, `norm_xiResolventPoint_le` (the resolvent coordinate is dominated by
`2 / ‖alpha‖^2`, from `normSq alpha < 2 Re (alpha^2)`), `summable_norm_xiResolventPoint`,
`summable_xiResolventPoint`, `finite_setOf_le_norm_xiResolventPoint` (the resolvent coordinates
accumulate only at the origin — a shell statement, via `finite_xiHeatShell`), and
`xiReciprocalSquareResolventTerm_eq_xiResolventPoint` (identification with the corpus's
reciprocal-square resolvent term at the imaginary base point `-x i`).

## Proof mechanism — corpus reuse, not reconstruction

The reality conclusion is **not** re-derived.  It is the corpus's abstract converse

```text
traceHankel_nonnegative_on_principalIdeal_implies_real   (TraceHankelConverse.lean)
```

instantiated with `lam q = xiResolventPoint X q` and the trivial separator `a = 1`.  That theorem's
hypothesis shape — nonzero atoms, summable, finite outside every disk around the origin — is
exactly what the resolvent coordinates satisfy, and the three facts above supply them.  A real
resolvent value forces a real squared spectral point (`Complex.inv_im`), and the height gap
`2 < g^2` then forces a real spectral point, which is RH via
`exists_spectralSq_im_pos_of_not_riemannHypothesis`.

## Why this is the useful basis

- **No contour, no exhaustion.**  The corpus's other prime-side Hankel criterion
  (`riemannHypothesis_of_countableSymmetricPrimeArchTraceHankelNonnegative`) proceeds through
  symmetric rectangles and a cofinality argument.  This one is a single absolutely convergent sum
  over the whole divisor at once.
- **Entries are already prime-computable in Lean.**  `xiResolventMoment 0` is the Euler-ray
  response; its higher `n` are the derivatives of the same function, i.e. the derivatives of
  `logDeriv xi` at `1/2 + x`, whose prime side is `sum_n Lambda(n) (log n)^m n^(-s)`.
- **It composes with the existing Euler-ray results.**  `xiSquaredEulerFullKernel_twoPoint_det_pos`
  (2 nodes, unconditional) and `xiSquaredEulerOrbitKernel_threePointDet_neg` (one off-line orbit,
  3 nodes) live on exactly these moments.

## Audit

`lake build +GaloisForLFunctions.RHTower.XiResolventTraceHankelCriterion` passes 8968/8968;
`scripts/formal_tools.py lint` passes; all theorems depend only on `propext`, `Classical.choice`,
`Quot.sound`; no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`.

## Novelty

`[REDISCOVERED]` mathematically — moment positivity of a resolvent-weighted spectral measure is the
Hamburger/Stieltjes picture, and the Euler-ray identity is already in the corpus.
`[NEW TO CORPUS]` as a composition: the corpus had the abstract converse and the Euler-ray identity
separately; this is the first module in which nonnegativity of an explicitly prime-computable
family is proved to **imply RH** without any contour truncation.

`[NOT AN RH PROOF]` — the hypothesis `∀ p, 0 ≤ Re (xiResolventTrace X p)` is unproved.

## Open core

Prove, for one `X > 1/4`, that every real polynomial gives `0 ≤ Re (xiResolventTrace X p)`.
Expanding `p` in monomials, this is positive semidefiniteness of the Hankel matrix
`(xiResolventMoment (j+k) X)`, i.e. of the derivative array of `logDeriv xi (1/2 + x)/x` at
`x = sqrt X`.  The classification from the Gaussian lane transfers verbatim: the order-one rung is
blind, and the first content is the order-two (Turán) minor, which is the Loewner determinant of
the Euler-ray response — precisely the object whose two-node case is already unconditional
(`xiSquaredEulerFullKernel_twoPoint_det_pos`) and whose three-node case is open.

---

## [LEAN-PROVED] The resolvent ladder

Module `GaloisForLFunctions.RHTower.XiResolventHankelLadder`.  The whole structure of the Gaussian
lane now sits on prime-computable data.

```lean
def xiResolventHankelForm (N : ℕ) (a : ℕ → ℝ) (X : ℝ) : ℂ :=
  ∑ j ∈ range N, ∑ k ∈ range N, (a j * a k : ℂ) * xiResolventMoment (j + k) X

xiResolventTrace_rangeSum :
  xiResolventTrace X (∑ j ∈ range N, C (a j) * X ^ j) = xiResolventHankelForm N a X

riemannHypothesis_of_forall_xiResolventHankelForm_re_nonneg {X : ℝ} (hX : 0 ≤ X) :
  (∀ N a, 0 ≤ (xiResolventHankelForm N a X).re) → RiemannHypothesis
```

So **RH follows from positive semidefiniteness of one explicit array**, the moments
`xiResolventMoment n X = sum_q (w q + X)^(-(n+1))`, whose order zero is
`logDeriv xi (1/2 + x) / x` at `X = x^2`.

Supporting structure:

- `norm_xiResolventPoint_le_one` — the height gap `2 < g^2` bounds every resolvent coordinate by
  `1`, so `summable_norm_xiResolventPoint_pow` gives absolute summability of every moment;
- `two_mul_xiResolventTuranMinor_eq_tsum_pair` — the variance expansion
  `2 (R0 R2 - R1^2) = sum_(q,q') u q u q' (u q - u q')^2`;
- `xiResolventPoint_lineConj` — critical-line reflection conjugates the resolvent coordinate;
- `xiResolventPairTerm_lineConj` — the exact negative core
  `-4 ‖u q‖^2 (Im (u q))^2`, and `..._re_neg_of_im_ne_zero` its strict negativity off the line.

Audit: `lake build +GaloisForLFunctions.RHTower.XiResolventHankelLadder` passes 8969/8969; lint
passes; axioms `propext`, `Classical.choice`, `Quot.sound`.

## Where the two lanes meet

The resolvent basis reproduces the Gaussian classification exactly, but with a different
concentration mechanism, and this is the useful part:

| | Gaussian basis | Resolvent basis |
|---|---|---|
| weight | `exp (-t w)` | `(w + X)^(-1)` |
| concentration onto the bottom of the spectrum | large `t` | large Hankel **order** `n` |
| order-1 rung | provably blind | the Euler-ray response, positive unconditionally — blind |
| order-2 rung | forces the two lowest strata real | the Loewner determinant of the Euler-ray response |
| Lean access to prime data | none (no Gaussian explicit formula) | **direct**, via `xiResolventMoment_zero_eq_logDeriv` |

The corpus's unconditional `xiSquaredEulerFullKernel_twoPoint_det_pos` is now explained
structurally: it is an order-two statement in a basis where order two does not yet concentrate, so
it carries no information about off-critical zeros.  Concentration in the resolvent basis needs
order `n` with `(n+1) |arg (w + X)| > pi/2`, i.e. `n` of size `(g^2 + X) / (g |2 Re rho - 1|)`.
That is the exact price of detection, and it is why no fixed low-order minor can close RH here.

## Open core, restated on prime data

Prove, for one `X > 1/4`, that the array `(xiResolventMoment (j+k) X)` is positive semidefinite —
equivalently, that the derivative array of `logDeriv xi (1/2 + x) / x` at `x = sqrt X` is a
Hamburger moment array.  Order one is vacuous; order two is the Loewner determinant whose two-node
case the corpus already has unconditionally and whose three-node case is open.

---

## [LEAN-PROVED] Quantitative vacuity of the low rungs

Last section claimed, on paper, that detection in the resolvent basis needs order `n` with
`(n+1) |arg (w + X)| > pi/2`.  That is now a theorem, in the form that matters: **the low rungs
hold unconditionally, so they cannot detect anything.**

Modules: `GaloisForLFunctions.HTGeometry.SectorPowerPositivity` (source-independent) and
`GaloisForLFunctions.RHTower.XiResolventLowRungVacuity`.

### The sector law, without trigonometry

```lean
re_mul_pos_and_abs_im_le :
  0 < z.re → |z.im| ≤ c * z.re → 0 < w.re → |w.im| ≤ d * w.re →
  0 ≤ c → 0 ≤ d → c * d < 1 → (c + d) / (1 - c * d) ≤ e →
  0 < (z * w).re ∧ |(z * w).im| ≤ e * (z * w).re

re_pow_pos_of_abs_im_le_fifth :
  0 < z.re → |z.im| ≤ z.re / 5 → 1 ≤ m → m ≤ 7 → 0 < (z ^ m).re
```

Angles add under multiplication; in tangent coordinates that is `(c + d) / (1 - c d)`.  The whole
proof is `Re (z w) = Re z Re w - Im z Im w`, `Im (z w) = Re z Im w + Im z Re w` and the triangle
inequality — no `arctan`, no `pi`.  Starting from `c = 1/5` the rounded budgets are
`1/5, 1/2, 4/5, 5/4, 2, 4, 21`, and the seventh power is the last the budget covers.

### The unconditional sector bound for the Xi divisor

```lean
abs_im_xiSpectralSq_add_le_fifth {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
  |(xiSpectralPoint q ^ 2 + X).im| ≤ (xiSpectralPoint q ^ 2 + X).re / 5
```

Inputs, both already in the corpus and both computation-free: the strip bound
`|Im alpha| < 1/2` (`abs_im_xiSpectralPoint_lt_half`) and the height floor
`32 < (Re alpha)^2` (`xiSpectral_re_sq_gt_thirtytwo`).  Then
`|Im (w + X)| = 2 |Re alpha| |Im alpha| < |Re alpha|` while
`Re (w + X) ≥ (Re alpha)^2 - 1/4 ≥ 5 |Re alpha|`.

### The vacuity theorem

```lean
re_xiResolventMoment_nonneg {X : ℝ} (hX : 0 ≤ X) {n : ℕ} (hn : n ≤ 6) :
  0 ≤ (xiResolventMoment n X).re
```

**The first seven rungs of the resolvent ladder are true whether or not RH holds.**  They are not
weak evidence for RH; they are no evidence at all.  The criterion of the previous sections can
therefore only begin to detect an off-critical zero at order eight, and the threshold rises exactly
as the height floor improves: with `(Re alpha)^2 > H` the sector constant is
`|Re alpha| / ((Re alpha)^2 - 1/4) ~ 1/sqrt H`, so the first informative order grows like
`sqrt H`.

Audit: `lake build +GaloisForLFunctions.RHTower.XiResolventLowRungVacuity` passes 9076/9076; lint
passes; axioms `propext`, `Classical.choice`, `Quot.sound`.

### Research consequence

This closes the question "which rung should be attacked first" with a proof rather than a guess.
Attacking rungs one through seven is provably wasted effort; the corpus's unconditional two-node
Euler-ray determinant sits inside that vacuous range, which explains its unconditionality.  The
first candidate with content is order eight — and the same computation shows the honest way to make
detection cheap is not a cleverer minor but **a better computation-free height floor**, since the
first informative order scales like the square root of the floor.

---

## Correction to the previous section, and the general chain

**The direction I stated last was backwards.** A *better* computation-free height floor does not make
detection cheaper — it makes it harder.  The sector constant is `c ~ 1/sqrt H` for a floor
`(Re alpha)^2 > H`, and the first informative order is `~ (pi/2) sqrt H`.  So raising the floor
enlarges the provably vacuous initial segment of the ladder.  Recorded so the lever is not chased in
the wrong direction.

The correct reading is stronger and is a genuine structural no-go for finite truncation: since the
horizontal displacement `|2 Re rho - 1|` has no positive lower bound available a priori, the angle
`|arg (w + X)|` of an off-critical copy can be arbitrarily small, so **no fixed finite rung can
decide RH**.  Only the full ladder does.  The vacuity theorem is the quantitative beginning of that
statement for the actual Xi divisor.

To make the accounting reusable at any floor, the sector law is now available in chain form:

```lean
re_pow_pos_and_abs_im_le_of_chain {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 ≤ c)
    (him : |z.im| ≤ c * z.re) (d : ℕ → ℝ) (hd1 : c ≤ d 1) (hdnn : ∀ k, 0 ≤ d k)
    (hstep : ∀ k, 1 ≤ k → c * d k < 1 ∧ (c + d k) / (1 - c * d k) ≤ d (k + 1)) :
    ∀ m, 1 ≤ m → 0 < (z ^ m).re ∧ |(z ^ m).im| ≤ d m * (z ^ m).re
```

Any improved floor now yields its vacuous range by exhibiting a budget sequence `d`; the `1/5`
chain (seven powers) is the instance currently used.  The corpus's off-line floor
`xiWard_offlinePair_height_sq_gt_sixtyfive` gives `c = 1/8` and twelve powers, once transferred from
`XiRightUpperZeroCopy` to the general off-critical copy.

## Corpus check: the arithmetic matrix positivity already exists

The 3-4-1 no-go on `weil-positivity-ladder-outside-strip.md` concluded that a *fixed* trigonometric
identity only buys positivity on a fixed configuration, and that the sign must come from a
mechanism adapting to the configuration.  That mechanism is already formalized in the corpus, and
this lane should consume it rather than rebuild it:

```text
GaloisForLFunctions.HTGeometry.PrimeDirichletPositiveDefinite
  PositiveDefiniteOnReal
  positiveDefinite_atomicFourierSeries_of_nonnegative
  signedPrimeVerticalTrace_eq_LSeries
  signedPrimeVerticalTrace_positiveDefinite_iff_allPositive
```

On every convergence line `sigma > 1` the prime vertical trace is a positive-definite function of
the height, and 3-4-1 is its `(1,2,1)` instance.  So the arithmetic side already supplies matrix
positivity for **every** finite configuration of heights and weights.

**Why it does not yet compose with this lane, exactly.**  Positive-definiteness is a statement about
values of the prime series along a *vertical* line `sigma + i t`.  The resolvent moments
`xiResolventMoment n X` are derivatives of the same series at a single *real* point `1/2 + x`.  The
two data sets are Fourier-dual, not equal, so no direct substitution exists.  Bridging them is a
Poisson/Herglotz representation problem — recovering the real-axis derivative array from the
vertical-line positive-definite data — and that is the next well-posed target for this lane.

---

## Correction: the archimedean array is NOT known to be positive semidefinite

The previous section asserted that "the archimedean array is positive semidefinite by the
elementary pole/digamma structure of `logDeriv xi (1/2 + x)/x`".  **That was asserted, not proved,
and it is not obvious.**  Retracted.

What is actually true, and what the retraction exposes, is sharper and better:

Write `A = Q + P` on `X > 1/4` (valid because the prime series converges there), with `Q` the
Euler-ray response of the Xi divisor and `P` the prime part.  Then:

- `P` is completely monotone on `(1/4, infinity)`: it is `sum_n Lambda(n) n^(-1/2) e^(-L sqrt X)/sqrt X`
  with `L = log n`, and both `e^(-L sqrt X)` and `1/sqrt X` are completely monotone.  Hence its
  moment array is PSD — this is the formalized `vonMangoldtLogMoment_hankel_nonneg`.
- Under RH, `Q(X) = sum 2/(X + gamma^2)` is completely monotone, so `A = Q + P` is too.
- Unconditionally, `A` is an **explicit elementary function containing no zeros and no primes**.
  So "is `A` completely monotone on `(1/4, infinity)`?" has a definite answer independent of RH.

This isolates a genuinely new checkpoint:

> **[OPEN, elementary]**  Is `A(X) = [1/s + 1/(s-1) + logDeriv Gamma_R s] / x`, `s = 1/2 + x`,
> `x = sqrt X`, completely monotone on `X > 1/4`?

It is **necessary for RH** (RH makes it so), it is prime-free and zero-free, and a *negative*
answer would disprove RH outright.  Its inverse Laplace density is computable in closed form —
`1/(X - 1/4)` gives `e^(t/4)`, `1/sqrt X` gives `1/sqrt(pi t)`, and each Gamma pole contributes
`- e^(b^2 t) erfc(b sqrt t)` with `b = 2k + 1/2` — so the question is the sign of one explicit
regularized sum of error functions.  That is an ordinary analysis problem with no arithmetic in it,
and it is the first sub-problem this lane has produced that is entirely free of both zeros and
primes.

## [LEAN-PROVED] The split at order zero

Module `GaloisForLFunctions.RHTower.XiResolventArchPrimeSplit`.

```lean
lseries_vonMangoldt_ofReal {σ : ℝ} (hσ : 1 < σ) :
  LSeries (fun n => (vonMangoldt n : ℂ)) σ = ((vonMangoldtLogMoment 0 σ : ℝ) : ℂ)

xiResolventMoment_zero_eq_arch_sub_prime {x : ℝ} (hx : 1 / 2 < x) :
  xiResolventMoment 0 (x ^ 2)
    = ((1/2 + x)⁻¹ + (1/2 + x - 1)⁻¹ + logDeriv Gammaℝ (1/2 + x)) / x
      - (vonMangoldtLogMoment 0 (1/2 + x)) / x
```

The ladder's order-zero entry is now exhibited in Lean as *archimedean minus prime*, with the prime
term identified as the order-zero entry of the moment array proved PSD in
`VonMangoldtLogMomentHankel`.  So the two halves of the domination question are now separate,
named, formalized objects.

Audit: `lake build +GaloisForLFunctions.RHTower.XiResolventArchPrimeSplit` passes 9086/9086; lint
passes; axioms `propext`, `Classical.choice`, `Quot.sound`.

---

## [LEAN-PROVED] Strict quantitative domination at order zero

```lean
log_two_rpow_le_vonMangoldtLogMoment_zero {σ : ℝ} (hσ : 1 < σ) :
  Real.log 2 * (2 : ℝ) ^ (-σ) ≤ vonMangoldtLogMoment 0 σ

re_xiResolventMoment_zero_add_primeTwo_le_arch {x : ℝ} (hx : 1 / 2 < x) :
  (xiResolventMoment 0 (x ^ 2)).re + Real.log 2 * (2 : ℝ) ^ (-(1/2 + x)) / x
    ≤ (arch (1/2 + x) / x).re
```

The archimedean quantity exceeds the Euler-ray response of the Xi divisor by at least the single
prime `2`'s contribution — unconditional, with an explicit gap.  Audit: build 9086/9086, lint
passes, axioms `propext`, `Classical.choice`, `Quot.sound`.

## [PAPER] The elementary target, made exact

The open question "is `A` completely monotone on `X > 1/4`?" is equivalent to nonnegativity of its
inverse Laplace density, and that density is computable in closed form from the Gaussian explicit
formula.  Writing `nu(t) = sum_rho exp((rho - 1/2)^2 t)` for the Gaussian zero trace and
`nu_P(t) = (1/sqrt(pi t)) sum_n Lambda(n) n^(-1/2) exp(-(log n)^2/(4t)) >= 0` for the prime density,
the explicit formula gives `nu = nu_A - nu_P` with

```text
nu_A(t) = 2 exp(t/4) + (1/2pi) integral_R exp(-t r^2) [Re psi(1/4 + i r/2) - log pi] dr.
```

**So the elementary target is exactly:  is that expression nonnegative for every `t > 0`?**  It
contains no zeros and no primes.

Two halves of the analysis, recorded so the work is not redone:

- **Large `t` is easy.**  `Re psi(1/4 + i r/2) >= psi(1/4)` for every real `r`, because
  `Re (1/(k + 1/4 + i r/2)) = (k+1/4)/((k+1/4)^2 + r^2/4) <= 1/(k+1/4)`; the digamma real part is
  minimized on the real axis.  Hence
  `nu_A(t) >= 2 exp(t/4) - (log pi - psi(1/4)) / (2 sqrt(pi t))`, which is positive once
  `t` is bounded below.
- **Small `t` is also fine, for a different reason.**  There the Gaussian is wide and the
  logarithmic growth `Re psi(1/4 + i r/2) ~ log|r/2|` dominates: the integral behaves like
  `(1/(4 sqrt(pi t))) log(1/t) -> +infinity`.

What is genuinely open is the intermediate range, where the margin is finite (numerically of order
one near `t ~ 1`, but that is not admissible as evidence).  Closing it needs an explicit two-sided
bound on `integral exp(-t r^2) Re psi(1/4 + i r/2) dr`.  That is ordinary analysis with no
arithmetic, but it is an estimate, and mathlib currently has no digamma development, so the Lean
cost is dominated by building that rather than by the mathematics.

**Status of this target:** `[OPEN]`, elementary, necessary for RH, sufficient for nothing.  Its
value is that it is the only sub-problem this lane produced that touches neither the zeros nor the
primes — and its failure would refute RH outright.

---

## Correction: mathlib and the corpus DO have digamma

Last section said "mathlib currently has no digamma development, so the Lean cost is dominated by
building that".  **Wrong, and retracted.**  `Complex.digamma` exists in mathlib, and the corpus
carries a substantial development around it: `RHTower.DigammaGaussSeries`
(`digamma_eq_neg_euler_add_tsum_gauss`, `gaussDigammaSeriesTerm`),
`HTGeometry.ExplicitDigammaHerglotzPalette` (summability, Herglotz source, imaginary-part
positivity), `HTGeometry.CanonicalDigammaSourceSelection`, `HTGeometry.DigammaSectorBounds`,
`RHTower.DigammaAsymptotic`, `DigammaBounds`, `DigammaLine`, `DigammaSeries`, `DigammaUniform`.

The elementary target is therefore considerably more accessible than I claimed.  Cost assessments
must be checked against the corpus, not asserted.

## [LEAN-PROVED] The archimedean primitive: digamma's real part is minimised on the real axis

Module `GaloisForLFunctions.RHTower.DigammaVerticalMinimum`.

```lean
re_gaussDigammaSeriesTerm_real_le {a : ℝ} (ha : 0 < a) (y : ℝ) (n : ℕ) :
  (gaussDigammaSeriesTerm a n).re ≤ (gaussDigammaSeriesTerm (a + y * I) n).re

digamma_real_le_re_digamma_add_mul_I {a : ℝ} (ha : 0 < a) (y : ℝ) :
  (Complex.digamma a).re ≤ (Complex.digamma (a + y * I)).re
```

Mechanism: in the Gauss series `psi(s) = -gamma + sum_n [1/(n+1) - 1/(s+n)]` the subtracted term
contributes `Re (1/(a+n+iy)) = (a+n)/((a+n)^2 + y^2) <= 1/(a+n)`, so every summand is smallest on
the real axis.  Termwise comparison then transfers to the sums.

Audit: `lake build +GaloisForLFunctions.RHTower.DigammaVerticalMinimum` passes 8653/8653; lint
passes; axioms `propext`, `Classical.choice`, `Quot.sound`.

**What it buys.**  This is exactly the large-time half of the elementary complete-monotonicity
target.  Applied at `a = 1/4` it gives, uniformly in the height `r`,

```text
Re psi(1/4 + i r/2) >= psi(1/4),
```

so the Gaussian archimedean integral obeys

```text
(1/2pi) integral exp(-t r^2) [Re psi(1/4 + i r/2) - log pi] dr
    >= -(log pi - psi(1/4)) / (2 sqrt(pi t)),
```

and hence `nu_A(t) >= 2 exp(t/4) - (log pi - psi(1/4)) / (2 sqrt(pi t))`, which is positive for all
`t` bounded below.  The remaining open piece is the small-`t` range, where the logarithmic growth of
`Re psi` must be used instead — the corpus's `DigammaAsymptotic` and `DigammaSectorBounds` are the
natural inputs there.

## [LEAN-PROVED] The archimedean factor's log-derivative is minimised on the real axis

```lean
re_logDeriv_Gammaℝ_real_le {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
  (logDeriv Complex.Gammaℝ σ).re ≤ (logDeriv Complex.Gammaℝ (σ + y * I)).re
```

Immediate from `digamma_real_le_re_digamma_add_mul_I` through the corpus's
`logDeriv_Gammaℝ_eq : logDeriv Gamma_R s = -(log pi)/2 + digamma (s/2) / 2`.

This is a reusable archimedean primitive, not tied to this lane: in any completed-explicit-formula
argument the archimedean contribution at height `y` never dips below its real-axis value, so it can
be replaced by the real-axis value in a lower bound, uniformly in the height.  It is the completed
analogue of the classical fact used in de la Vallee Poussin arguments, and it is the exact input
needed for the large-time half of the complete-monotonicity target.

Audit: build 8939/8939, lint passes, axioms `propext`, `Classical.choice`, `Quot.sound`.

## [LEAN-PROVED] Digamma's real part increases with the height

```lean
re_one_div_vertical (a y : ℝ) (n : ℕ) :
  (1 / (a + y * I + n)).re = (a + n) / ((a + n)^2 + y^2)

re_gaussDigammaSeriesTerm_mono {a : ℝ} (ha : 0 < a) {y z : ℝ} (hyz : |y| ≤ |z|) (n : ℕ) :
  (gaussDigammaSeriesTerm (a + y * I) n).re ≤ (gaussDigammaSeriesTerm (a + z * I) n).re

re_digamma_mono_of_abs_le {a : ℝ} (ha : 0 < a) {y z : ℝ} (hyz : |y| ≤ |z|) :
  (Complex.digamma (a + y * I)).re ≤ (Complex.digamma (a + z * I)).re
```

`Re psi(a + i y)` is nondecreasing in `|y|` on every vertical line of the right half-plane — the
subtracted resolvent atom `(a+n)/((a+n)^2 + y^2)` decreases in `|y|`, so every Gauss summand
increases.  The real-axis minimum proved earlier is the special case `y = 0`.

Audit: build 8939/8939, lint passes, axioms `propext`, `Classical.choice`, `Quot.sound`.

**Why the monotone form and not just the minimum.**  The small-`t` half of the
complete-monotonicity target cannot use the constant lower bound `psi(1/4)`: there the Gaussian is
wide and one needs the *growth* of `Re psi` away from the axis.  Monotonicity supplies exactly that
in usable form — for `|r| >= R`, `Re psi(1/4 + i r/2) >= Re psi(1/4 + i R/2)` — so the integral
splits as

```text
(1/2pi) integral exp(-t r^2)[Re psi(1/4 + i r/2) - log pi] dr
   >= -(2R/2pi)(log pi - psi(1/4)) + (Re psi(1/4 + iR/2) - log pi) * (sqrt(pi/t) - 2R)/(2pi),
```

which tends to `+infinity` as `t -> 0` once `R` is chosen with `Re psi(1/4 + iR/2) > log pi`.  What
remains is purely numerical: exhibit such an `R`, and bound `log pi - psi(1/4)`.  Both are explicit
constants; neither involves zeros or primes.
