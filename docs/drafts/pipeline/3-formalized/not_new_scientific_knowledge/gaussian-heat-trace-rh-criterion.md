# Gaussian heat trace: from RH-disproof endpoint to exact RH criterion

- **ID:** `gaussian-heat-trace-rh-criterion`
- **Stage:** 1-in-progress (paper proof closed; Lean in progress)
- **Lean module (existing, one-way only):** `GaloisForLFunctions.RHTower.XiGaussianHeatTraceDisproof`
- **Lean module (new):** `GaloisForLFunctions.RHTower.XiGaussianHeatTraceCriterion`

## The gap this card closes

`XiGaussianHeatTraceDisproof.lean` builds the multiplicity-exact polynomial-square Gaussian trace

```text
T(P,t) = sum_q  P(w_q)^2 * exp(-t*w_q),      w_q := xiSpectralPoint q ^ 2,
```

proves it absolutely summable for every `t>0`, proves it **real unconditionally** (critical-line
reflection), and proves the single implication

```text
RH  ->  0 <= T(P,t)                    (xiPolynomialGaussianHeatTraceReal_nonneg_of_riemannHypothesis)
T(P,t) < 0  ->  not RH                 (contrapositive; the "disproof endpoint")
```

**The converse is absent.** Without it the object is a falsification device, not a criterion: it can
only ever refute RH, never certify it. This card supplies the converse and therefore the
equivalence.

## Why the squared coordinate is the right carrier

`xiSpectralPoint q = (rho_q - 1/2)(-I)`, so with `rho = 1/2 + b + i*g` one has `Re alpha = g`,
`Im alpha = -b`, hence

```text
w = alpha^2,   Re w = g^2 - b^2,   Im w = -2*g*b.
```

The corpus already proves `normSq alpha < 2*Re(alpha^2)` (`xiSpectralPoint_normSq_lt_two_mul_sq_re`)
and `2 < g^2` (`xiZeroCopy_two_lt_im_sq`). So `Re w > 0` always and `g != 0` always, giving the exact
dictionary

```text
w_q real   <->  b = 0   <->  that copy lies on the critical line.
```

RH is therefore exactly *reality of the whole `w`-divisor*, and `Re w` is a genuine **shell
coordinate** (bounded shells are finite, see below). This is what makes the Gaussian filter local.

## [PAPER-PROVED] The converse

**Theorem.** If some copy `q0` has `Im w_{q0} != 0`, then there exist a real polynomial `P` and a
time `t>0` with `T(P,t) < 0`.

*Proof.* Write `w0 := w_{q0}`, `A0 := Re w0 > 0`, `B0 := Im w0 != 0`, and set `R := A0 + 1`.

1. **Shells are finite.** `normSq alpha_q < 2*Re w_q`, so on `S := {q : Re w_q <= R}` one has
   `1/‖alpha_q‖^2 > 1/(2R) > 0`. A summable nonnegative family exceeds a fixed positive level only
   finitely often, and `xiSpectralPoint_inv_sq_summable` is exactly that summability. Hence `S` is
   finite, and `q0 in S`.

2. **The filter.** Put `S1 := {q in S : w_q = w0 or w_q = conj w0}` and `F := S \ S1`, and

   ```text
   P := prod_{q in F} ( (X - Re w_q)^2 + (Im w_q)^2 ).
   ```

   Each factor is a real polynomial whose complex evaluation is `(z - w_q)(z - conj w_q)`. Hence
   `P(w_q) = 0` for every `q in F`, while `c := P(w0)^2 != 0` because for `q in F` neither `w_q` nor
   `conj w_q` equals `w0`. The filter needs no knowledge of the divisor beyond its finiteness in the
   shell; only existence is asserted.

3. **The surviving class is a single rotating vector.** For `q in S1` the summand is either
   `c*exp(-t*w0)` or its complex conjugate (real `P`, real `t`), so **every** `q in S1` contributes
   the same real part

   ```text
   Re( c*exp(-t*w0) ) = |c| * exp(-t*A0) * cos( arg c - t*B0 ).
   ```

   No multiplicity bookkeeping between the two conjugate classes is needed. Let `n := |S1| >= 1`.

4. **The tail is exponentially subordinate.** For `q not in S` one has `Re w_q > R`, so for `t >= 1`

   ```text
   | P(w_q)^2 exp(-t*w_q) |  <=  |P(w_q)|^2 exp(-Re w_q) * exp(-(t-1)*R),
   ```

   whence `|tail(t)| <= C * exp(R) * exp(-t*R)` with `C := sum_q ‖P(w_q)^2 exp(-w_q)‖ < infinity`.

5. **Phase selection.** `B0 != 0`, so `t_n := (arg c - pi - 2*pi*n)/B0`, `n in Z`, is an unbounded
   arithmetic progression on which `cos(arg c - t*B0) = -1` exactly. Choose `n` with
   `t := t_n > max(1, log( C*exp(R) / (n*|c|) ))`. Then

   ```text
   T(P,t) <= -n*|c|*exp(-t*A0) + C*exp(R)*exp(-t*R) < 0,
   ```

   because `R - A0 = 1` makes the second term beat the first exactly when `t` exceeds that log. QED

**Corollary (exact criterion).**

```text
RH  <->  for every real polynomial P and every t>0,  0 <= T(P,t).
```

## Where the mathematical content sits

Two structural readings, both proved by the argument above and both new *to this corpus*:

- **Shell localization.** The polynomial `P` is a *spectral filter*: it annihilates every copy in the
  shell `Re w <= R` except one conjugate class. After filtering, `exp(t*A0)*T(P,t)` equals
  `n*|c|*cos(arg c - t*B0)` up to `O(exp(-t))`. So the large-time oscillation **frequency** of the
  filtered trace is exactly `Im w0 = -2*g*b`, the off-line charge of the isolated zero. RH is
  precisely the statement that every filtered trace is eventually of one sign.

- **[NO-GO] The unfiltered trace is blind above the bottom shell.** With `P = 1` the criterion
  degenerates: `T(1,t) = sum_q exp(-t*w_q)` is governed as `t -> infinity` only by the copies of
  minimal `Re w`, and within that bottom shell an on-line copy of large multiplicity dominates any
  off-line partner (`3 + cos t >= 2 > 0`). Concretely, an admissible strip-confined symmetric
  multiset with `w = -196` of multiplicity `3` and an off-line quadruple at `g = 100, b = 1/10` has
  `T(1,t) > 0` for every `t > 0`. **Hence complete monotonicity of the scalar Euler-ray response is
  strictly weaker than RH**; only the *matrix/filtered* version is equivalent. This is the exact
  reason every scalar positivity criterion in the corpus stalls, and it is a design constraint for
  future rungs: a scalar functional of the divisor can only read the bottom of the spectrum.

## Audit

- **[REDISCOVERED] as mathematics.** This is Weil positivity restricted to the Hermite/Gaussian test
  family, which is dense; the classical statement is Weil (1952) and its Hermite dictionary appears
  in Groskin, arXiv:2607.02828 (see `rh-sota-literature-lean-wall-2026.md`). No novelty is claimed
  for the equivalence itself.
- **[NEW TO CORPUS] as an exact theorem.** The corpus carries the implication and its
  contrapositive only. The converse, the explicit filter construction, the shell-finiteness lemma,
  and the blindness no-go are not present.
- **Not circular.** The converse consumes `not RH` to produce a witness; that is the correct
  direction for an equivalence, and no step assumes positivity of anything.
- **Not an RH proof.** It relocates RH to an infinite family of explicit inequalities whose data are
  Gaussian-damped, hence absolutely convergent for *every* parameter — unlike
  `riemannHypothesis_iff_outsideStrip_nonneg`, whose entries need `|Im z| > 1/2` for the prime
  series to converge.

## Gates

- [x] paper proof closed, dependency-free
- [x] hostile audit: FALSE / CIRCULAR / REDISCOVERED / BRIDGE / INSIGNIFICANT considered
- [ ] Lean: shell finiteness, filter polynomial, converse, equivalence
- [ ] `#print axioms` + lint + index

## Next generative move after this lands

The filter `P` is a *hard* (polynomial) spectral cutoff. Replace it by an adaptive one: the same
argument with `P` chosen from the reproducing kernel of the shell turns the criterion into a
statement about the **Christoffel function** of the Gaussian-damped zero measure, whose asymptotics
are governed by the archimedean density. That is the first place where the archimedean side can
dominate a filtered prime sum without a fixed trigonometric identity — the mechanism the 3-4-1
no-go (`weil-positivity-ladder-outside-strip.md`) demanded.

---

## [LEAN-PROVED] Stage 3 certificate

Module `formal/GaloisForLFunctions/RHTower/XiGaussianHeatTraceCriterion.lean`, wired into the
`GaloisForLFunctions.RHTower` umbrella.

Capstone:

```lean
theorem riemannHypothesis_iff_forall_xiPolynomialGaussianHeatTraceReal_nonneg :
    RiemannHypothesis ↔
      ∀ (P : Polynomial ℝ) (t : ℝ), 0 < t → 0 ≤ xiPolynomialGaussianHeatTraceReal P t
```

Supporting theorems, in dependency order:

- `xiSpectralSq_re_pos` — every squared copy has strictly positive real part;
- `xiSpectralPoint_re_eq` — the real part of the centered coordinate is the height;
- `xiSpectralSq_im_ne_zero_of_im_ne_zero` — squaring preserves off-criticality, because the height
  never vanishes;
- `finite_xiHeatShell` — **every shell `Re (w q) <= R` of the squared divisor is finite**, from
  `normSq alpha < 2 Re (alpha^2)` plus reciprocal-square summability along the cofinite filter;
- `re_mul_exp_neg_mul`, `re_heatSummand_conj` — polar form of a summand and equality of the two
  conjugate contributions;
- `norm_xiPolynomialGaussianHeatTerm`, `summable_norm_xiPolynomialGaussianHeatTerm`;
- `exists_neg_xiPolynomialGaussianHeatTraceReal_of_spectralSq_im_pos` — the converse;
- `exists_spectralSq_im_pos_of_not_riemannHypothesis` — normalisation of the witness by the
  line-conjugation involution.

Reused rather than rebuilt: `realOrbitSeparator`, `evalRealOrbitSeparator_eq_zero`,
`evalRealOrbitSeparator_ne_zero`, `evalRealPolynomial_conj` (all from `TraceHankelConverse.lean`),
and the whole summability/reality package of `XiGaussianHeatTraceDisproof.lean`.

Audit: `lake build +GaloisForLFunctions.RHTower.XiGaussianHeatTraceCriterion` passes 8960/8960;
`scripts/formal_tools.py lint` passes; the capstone and every supporting theorem depend only on
`propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.

## [PAPER-PROVED] The blindness no-go, with its explicit witness

Take an admissible abstract divisor — strip-confined, stable under both `alpha -> conj alpha` and
`alpha -> -alpha`, reciprocal-square summable — consisting of

```text
four on-line copies at  g = 14, b = 0        (w = -196, real),
one off-line quadruple  g = 100, b = 1/10    (w = 9999.99 -+ 20 i).
```

Its unfiltered Gaussian trace is

```text
T(1,t) = 4 exp(-196 t) + 4 exp(-9999.99 t) cos (20 t)
       >= 4 (exp(-196 t) - exp(-9999.99 t)) > 0    for every t > 0.
```

So `T(1,·) >= 0` holds while the divisor is not real. **The unfiltered trace — equivalently complete
monotonicity of the scalar Euler-ray response — is strictly weaker than RH.** The filter polynomial
is not a convenience: it is the entire content, because a scalar functional of the divisor reads
only the copies of minimal `Re w`, and there an on-line copy of larger multiplicity dominates any
off-line partner.

This is the exact reason the corpus's scalar positivity criteria stall, and it is now a design
constraint: any future rung must be a *matrix* (filtered) statement, or it is provably blind.

---

## [LEAN-PROVED] The positive successor to the blindness no-go: the Turán minor

The no-go said a *scalar* functional of the divisor is blind. The successor is the first `2 x 2`
Hankel minor of the same Gaussian data, and it is provably **not** blind.

Modules: `GaloisForLFunctions.HTGeometry.CommonRealPartTuranDeterminant` (source-independent) and
`GaloisForLFunctions.RHTower.XiGaussianHeatTuranDefect`.

### The vertical-line law (abstract, unconditional)

For a finite weighted complex configuration, `configTuranDeterminant_eq_pair_sum` is the variance
identity

```text
2 (f0 f2 - f1^2) = sum_(i,j) m_i m_j (w_i - w_j)^2,     f_n = sum_i m_i w_i^n.
```

If all points share one real part every difference is purely imaginary, so every squared difference
is `-(Im w_i - Im w_j)^2` and

```text
configTuranDeterminant_re_nonpos_of_common_re :  Re (f0 f2 - f1^2) <= 0,
configTuranDeterminant_re_neg_of_common_re   :  < 0  as soon as two positively weighted
                                                 points sit at different heights.
```

A positive measure on the real line has **nonnegative** Turán determinant. So a configuration on a
vertical line betrays its nonreality already at the second Hankel minor — the exact feature the
total mass lacks.

### The Xi instance

`xiGaussianHeatMoment n t = sum_q (w q)^n exp(-t w q)` with `w q = xiSpectralPoint q ^ 2`; it is
**real unconditionally** (`star_xiGaussianHeatMoment`, by critical-line reflection). Put

```text
xiHeatTuranDefect t = M0(t) M2(t) - M1(t)^2.
```

- `xiHeatTuranDefect_nonneg_of_riemannHypothesis` — under RH the `w q` are positive reals, so the
  moments are those of a positive measure and the minor is Cauchy--Schwarz (proved through finite
  partial sums and `Summable.tsum_le_of_sum_le`, no measure theory).
- `not_riemannHypothesis_of_xiHeatTuranDefect_neg` — **one strictly negative value of a single
  explicit scalar function of `t` refutes RH.**
- `xiHeatShell_turanDeterminant_re_neg_of_im_ne_zero` — `Re w` is constant on each shell
  (`xiHeatShell`, finite by `finite_xiHeatShell`), so a shell is a vertical-line configuration; an
  off-critical copy and its line conjugate are two shell points at opposite heights, hence the
  shell's Turán determinant is **strictly negative**. This is the non-blindness, on the actual
  divisor.

Audit: `lake build +GaloisForLFunctions.RHTower.XiGaussianHeatTuranDefect` passes 8962/8962;
`formal_tools.py lint` passes; all listed theorems depend only on `propext`, `Classical.choice`,
`Quot.sound`.

## [PAPER-PROVED, Lean pending] The asymptotic converse

Let `A = min_q Re (w q)` (attained: shells are finite) and let the bottom shell carry weights
`m_l` at heights `B_l`, closed under `B -> -B`. Then

```text
exp(2 t A) * xiHeatTuranDefect t  ->  -(1/2) sum_(l,l') m_l m_l' (B_l - B_l')^2 exp(-i t (B_l+B_l'))
```

as `t -> infinity`. The right side is an almost-periodic function of `t` whose **mean value** is
`-(1/2) sum over pairs with B_l + B_l' = 0`, which by the conjugation symmetry equals
`-2 sum_l m_l^2 B_l^2 < 0` whenever some `B_l <> 0`. Hence

> **If the bottom shell of the Xi divisor contains an off-critical copy, then
> `xiHeatTuranDefect t < 0` for arbitrarily large `t`.**

Contrapositive, and the target this opens:

> **`xiHeatTuranDefect t >= 0` for all large `t`  ==>  the lowest zeros of `xi` lie on the critical
> line** — with `xiHeatTuranDefect` an *explicit* combination of Gaussian-damped von Mangoldt sums
> and archimedean terms via the Weil explicit formula with Hermite test functions
> `u^(2n) exp(-t u^2)`.

That is a genuine source inequality, strictly weaker than RH, non-blind, and computation-free.
Remaining Lean work: attainment of `A`, the dominated limit of `exp(t A) M_n(t)`, and the
mean-value step. Nothing conjectural.

---

## [LEAN-PROVED] The ladder: RH as one explicit Hankel matrix

Module `GaloisForLFunctions.RHTower.XiGaussianHeatHankelLadder`.

Expanding a real polynomial in the monomial basis identifies the polynomial criterion with the
quadratic form of the Hankel matrix of the Gaussian-damped moments:

```lean
xiPolynomialGaussianHeatTraceReal_rangeSum :
  xiPolynomialGaussianHeatTraceReal (∑ j ∈ range N, C (a j) * X ^ j) t = xiHeatHankelForm N a t

riemannHypothesis_iff_forall_xiHeatHankelForm_nonneg :
  RiemannHypothesis ↔ ∀ N a t, 0 < t → 0 ≤ xiHeatHankelForm N a t
```

with `xiHeatHankelForm N a t = ∑_(j,k<N) a j * a k * M (j+k) t` and
`M n t = Re ∑_q (w q)^n exp(-t * w q)` unconditionally real.

So **RH is positive semidefiniteness of one explicit real symmetric matrix** whose entries are, via
the Weil explicit formula with the Hermite test functions `u^(2n) exp(-t u^2)`, Gaussian-damped von
Mangoldt sums plus archimedean terms — absolutely convergent for every `t > 0`, no half-plane
restriction anywhere.

The leading minors are a ladder of source inequalities, each strictly weaker than RH:

| rung | statement | status |
|---|---|---|
| 1 | `M 0 t >= 0` (the plain heat trace) | **provably blind** — explicit witness above |
| 2 | `M0 M2 - M1^2 >= 0` (`xiHeatTuranDefect`) | **not blind**; forces the bottom shell real |
| k | `k x k` leading minor `>= 0` | peels the bottom `k-1` shells |
| all | Hankel PSD | RH |

`xiHeatTuranDefect_nonneg_of_forall_xiHeatHankelForm` places the Turán minor inside the ladder as
rung 2 (via the test vector `(-M1, M0)`, with the degenerate case `M0 = 0` handled by forcing
`M1 = 0`), so the two modules are one object.

## Where this leaves the programme

The corpus's diagnosis — *criteria are saturated, what is missing is a source inequality* — is now
met with a specific graded list of source inequalities rather than one monolithic wall. Rung 1 is
settled negatively (blind). Rung 2 is the first with content, and it is exactly

> **`M0(t) M2(t) >= M1(t)^2` for large `t`**, i.e. **log-convexity of the Gaussian heat trace**,
> since `M1 = -M0'` and `M2 = M0''`.

Under RH this is Cauchy--Schwarz for a positive measure; unconditionally it is open, and by the
asymptotic converse it is equivalent to reality of the bottom shell of the divisor — currently
known only by interval arithmetic. That is the exact next scientific target.

### Remaining Lean steps for the asymptotic converse (mechanical, not conjectural)

1. `D t = (1/2) ∑∑ (w q - w q')^2 exp(-t (w q + w q'))` (double-tsum form of `ν ν'' - ν'^2`).
2. Attainment of `A = min Re w` (shells are finite and the divisor is nonempty).
3. Domination of the cross-shell pairs by `exp(-t(2A + δ))`.
4. Single-conjugate-pair bottom stratum: the bottom sum is exactly `-4 m^2 B0^2 exp(-2 t A)`, with
   **no oscillation**, so no Diophantine step is needed in that case. The general stratum needs the
   almost-periodic mean-value argument recorded above.

---

## [LEAN-PROVED] Rung 2 opened up: the pair expansion and its exact negative core

Module `GaloisForLFunctions.RHTower.XiGaussianHeatTuranPairSum`.

The Turán minor is now available as a **variance sum over ordered pairs of divisor copies**, and
the off-critical signal inside it is a closed-form term rather than an estimate.

```lean
two_mul_xiHeatTuranMinor_eq_tsum_pair :
  2 * (M 0 t * M 2 t - M 1 t ^ 2) = ∑' z : XiZeroCopy × XiZeroCopy, xiHeatPairTerm t z
two_mul_xiHeatTuranDefect_eq_re_tsum_pair :
  2 * xiHeatTuranDefect t = (∑' z, xiHeatPairTerm t z).re
```

with `xiHeatPairTerm t (q,q') = (w q - w q')^2 * exp(-t w q) * exp(-t w q')`.  Proof route: absolute
summability of the three monomial heat families, `tsum_mul_tsum_of_summable_norm` for each of the
products `M2*M0`, `M1*M1`, `M0*M2`, then the pointwise expansion of `(w - w')^2`.  No estimate and
no measure theory.

**The negative core, exactly.** Pairing a copy with its own critical-line conjugate gives

```lean
xiHeatPairTerm_lineConj :
  xiHeatPairTerm t (q, xiZeroCopyLineConjEquiv q)
    = ((-4 * (Im (w q))^2 * Real.exp (-(2 * t * Re (w q)))) : ℝ)
xiHeatPairTerm_lineConj_neg_of_im_ne_zero :
  (Im (w q) ≠ 0) → (xiHeatPairTerm t (q, xiZeroCopyLineConjEquiv q)).re < 0
```

So each off-critical copy deposits into the Turán minor an explicit negative amount
`-4 (Im w)^2 exp(-2 t Re w)`, strictly negative exactly off the critical line and graded by the
shell coordinate `Re w`.  This is the *signal*; proving `xiHeatTuranDefect >= 0` unconditionally is
exactly the statement that no such deposit survives, and the pair expansion makes the competing
positive terms — pairs of copies at different real parts — the only thing left to control.

Audit: `lake build +GaloisForLFunctions.RHTower.XiGaussianHeatTuranPairSum` passes 8964/8964; lint
passes; axioms are `propext`, `Classical.choice`, `Quot.sound`.

### Bookkeeping of the pair expansion (paper)

Grouping the pairs by shell:

- **same shell, both real** — the copies coincide in `w`, so `(w - w')^2 = 0`: no contribution;
- **same shell, conjugate pair** — the negative core above;
- **different shells** — `(w - w')^2 exp(-t(w + w'))` with `Re(w + w') >= A_1 + A_2`, so
  exponentially subordinate to the bottom-shell terms as `t -> infinity`.

Hence the large-`t` sign of `xiHeatTuranDefect` is decided by the **two lowest strata** only, and
it is positive precisely when both are real.  Sharper than the earlier "bottom shell" reading, and
the reason rung 2 is a *local* statement about the lowest zeros.

---

## [LEAN-PROVED] The bottom shell exists

Module `GaloisForLFunctions.RHTower.XiHeatShellMinimum`.

```lean
nonempty_xiZeroCopy : Nonempty XiZeroCopy
exists_min_xiSpectralSq_re :
  ∃ q₀ : XiZeroCopy, ∀ q, (xiSpectralPoint q₀ ^ 2).re ≤ (xiSpectralPoint q ^ 2).re
```

Nonemptiness from `xiDivisorSupport_infinite` plus positivity of the analytic multiplicity;
attainment of the minimum from `finite_xiHeatShell` applied at the shell coordinate of any single
copy, so the search is confined to a finite set.

This is step (2) of the three remaining steps for the asymptotic converse of the Turán rung:
`A = min Re w` is attained.  Steps (1) — the double-tsum form of `nu nu'' - nu'^2`, already proved
as `two_mul_xiHeatTuranMinor_eq_tsum_pair` — and (3), cross-shell domination by
`exp(-t(2A + delta))`, are what remain before the single-conjugate-pair case closes with no
Diophantine input.

Audit: build 9077/9077, lint passes, axioms `propext`, `Classical.choice`, `Quot.sound`.

## Correction to the index card's open core (4)

The index card listed as an open core "the corpus's `PrimeDirichletPositiveDefinite` gives matrix
positivity along **vertical** lines; the ladder needs the derivative array at a **real** point;
bridging them is a Poisson/Herglotz representation problem".  **That framing was wrong.**  Both
statements are parallel consequences of positivity of the *same* measure
`nu_x = sum_n Lambda(n) n^(-1/2-x) delta_(log n)`: the vertical-line statement is its Fourier
transform being positive definite, the ladder statement is its power moments being a positive
Hankel array (`vonMangoldtLogMoment_hankel_nonneg`).  Neither needs to be derived from the other,
and no bridge is missing.  Open core (4) is withdrawn.

What that leaves is sharper: the arithmetic side is fully supplied, and **every remaining
obstruction in this lane is archimedean** — the complete monotonicity of `A`, and the size of the
margin by which the archimedean array must exceed the prime array.

## [LEAN-PROVED] Tail primitives for the pair sum

Added to `XiGaussianHeatTuranPairSum`:

```lean
norm_xiHeatPairTerm (t : ℝ) (z : XiZeroCopy × XiZeroCopy) :
  ‖xiHeatPairTerm t z‖
    = ‖w z.1 - w z.2‖ ^ 2 * Real.exp (-(t * ((w z.1).re + (w z.2).re)))

norm_xiHeatPairTerm_le_of_le {t₁ t m : ℝ} (ht : t₁ ≤ t)
    (hm : m ≤ (w z.1).re + (w z.2).re) :
  ‖xiHeatPairTerm t z‖ ≤ ‖xiHeatPairTerm t₁ z‖ * Real.exp (-((t - t₁) * m))
```

The first exhibits a pair term as *squared separation of the two shell points* times the Gaussian
damping at their **combined** shell coordinate; the second converts a lower bound on that combined
coordinate into a uniform exponential factor beyond any reference time.

Together with `exists_min_xiSpectralSq_re` these are the two inputs step (3) needs: pairs not both
in the bottom shell have combined coordinate at least `2A + delta`, so their total is bounded by
`exp(-(t-1)(2A+delta))` times a fixed constant, while the bottom-block terms carry `exp(-2tA)`.
Since the bottom block of a single conjugate pair evaluates to `-4 m^2 B0^2 exp(-2tA)` with no
oscillation (`xiHeatPairTerm_lineConj`), the comparison closes without any Diophantine input.

What is still missing for step (3) is only the bookkeeping: a `delta > 0` separating the bottom
shell from the rest — which needs the *second* shell value to be attained, the same finiteness
argument as `exists_min_xiSpectralSq_re` applied to the divisor minus the bottom block.

Audit: build 8964/8964, lint passes, axioms `propext`, `Classical.choice`, `Quot.sound`.

## [LEAN-PROVED] The bottom shell is isolated

```lean
exists_bottom_shell_gap :
  ∃ (A δ : ℝ), 0 < δ ∧ (∃ q₀, (w q₀).re = A) ∧ (∀ q, A ≤ (w q).re) ∧
    ∀ q, (w q).re = A ∨ A + δ ≤ (w q).re
```

Every copy either sits exactly in the bottom shell or is at least `delta` above it.  Proof: the
sublevel set `Re w ≤ A + 1` is finite (`finite_xiHeatShell`), so the competing values in it form a
finite set whose minimum above `A` is attained; copies outside that sublevel set are more than `1`
above `A`, so `delta = min (attained gap) 1` works, and `delta = 1` in the degenerate case where no
copy sits strictly between `A` and `A + 1`.

Audit: build 9077/9077, lint passes, axioms `propext`, `Classical.choice`, `Quot.sound`.

### Step (3) is now assembled from certified parts

With `exists_bottom_shell_gap`, `norm_xiHeatPairTerm` and `norm_xiHeatPairTerm_le_of_le`, the
cross-shell estimate is a finite composition: any ordered pair not lying entirely in the bottom
shell has combined coordinate at least `2A + delta`, hence total norm at most
`C * exp(-(t-1)(2A + delta))` with `C = sum ‖pairTerm 1 z‖`, while the bottom block carries
`exp(-2 t A)`.  The remaining Lean work is the split of the double sum over
`(bottom block) x (bottom block)` and its complement — the same `Summable.sum_add_tsum_compl`
pattern already used in `XiGaussianHeatTraceCriterion` — plus summability of the pair-term norms,
which follows from `summable_xiHeatPairTerm` by `summable_norm_iff`.

No new mathematics remains in step (3); what is left is assembly.

## [LEAN-PROVED] The Turán rung detects an off-critical bottom shell

Module `GaloisForLFunctions.RHTower.XiHeatTuranBottomDetection`.  Step (3) is assembled; the
converse half of rung 2 is now a theorem.

```lean
xiHeatPairTerm_of_conj (t : ℝ) (h : w z.2 = conj (w z.1)) :
  xiHeatPairTerm t z = ((-4 * (Im (w z.1))^2 * Real.exp (-(2 t Re (w z.1)))) : ℝ)

exists_neg_xiHeatTuranDefect_of_bottom_conjugate_pair
    (hmin : ∀ q, (w q₀).re ≤ (w q).re)
    (him : (w q₀).im ≠ 0)
    (hbottom : ∀ q, (w q).re = (w q₀).re → w q = w q₀ ∨ w q = conj (w q₀)) :
  ∃ T, ∀ t, T < t → xiHeatTuranDefect t < 0
```

**If the copies of least shell coordinate form a single conjugate pair off the critical line, the
Turán minor is strictly negative for all large heat times.**

Assembly, all parts previously certified: the variance expansion
(`two_mul_xiHeatTuranDefect_eq_re_tsum_pair`); the bottom block `B ×ˢ B` with `B = xiHeatShell A`,
on which every pair term is either zero (equal points) or the explicit nonpositive real
`-4 (Im w0)^2 exp(-2 t A)` (conjugate points — the phases cancel because the two heights are
opposite, which is why **no Diophantine or almost-periodicity input is needed**); the isolation gap
`exists_bottom_shell_gap` giving `2A + delta` as a lower bound on the combined shell coordinate of
every other pair; and the damping transfer `norm_xiHeatPairTerm_le_of_le` turning that into
`C exp(2A+delta) exp(-t(2A+delta))`.  The threshold is explicit:
`T = max 1 (K/delta)` with `K = C exp(2A+delta) / (4 (Im w0)^2)`.

Audit: build 9078/9078, lint passes, axioms `propext`, `Classical.choice`, `Quot.sound`.

### Where rung 2 now stands

- **(⟸)** `xiHeatTuranDefect_nonneg_of_riemannHypothesis` — RH forces the rung.
- **(⟹, detection)** the theorem above — an off-critical bottom shell of the simplest shape is
  *seen* by the rung, with an explicit time threshold.
- **Open** — the positivity of `xiHeatTuranDefect` itself, which is where the arithmetic lives; and
  the general bottom stratum (several conjugate pairs, or a mixed real/complex stratum), which does
  need the almost-periodic mean-value argument recorded earlier on this card.

### The payoff form

```lean
xiSpectralSq_bottom_im_eq_zero_of_forall_xiHeatTuranDefect_nonneg
    (hmin) (hbottom) (hpos : ∀ t, 0 < t → 0 ≤ xiHeatTuranDefect t) :
  (xiSpectralPoint q₀ ^ 2).im = 0

xiSpectralPoint_bottom_im_eq_zero_of_forall_xiHeatTuranDefect_nonneg
    (hmin) (hbottom) (hpos) :
  (xiSpectralPoint q₀).im = 0
```

**Turán positivity of the Gaussian heat trace forces the lowest zero onto the critical line.**  The
second statement is about the zero itself, obtained from the first through
`xiSpectralSq_im_ne_zero_of_im_ne_zero` — squaring detects the critical line because the height
never vanishes.

This is the first statement in this lane of the shape "an unconditional-looking positivity
hypothesis on prime-and-archimedean data yields a *location* theorem about an actual zero", rather
than another restatement of RH.  The hypothesis `hpos` is exactly the rung-2 source inequality, and
`hbottom` says the bottom stratum is a single conjugate class — the generic situation, and the case
where the phases cancel identically so no Diophantine input is needed.

Audit: build 9078/9078, lint passes, axioms `propext`, `Classical.choice`, `Quot.sound`.

### Remaining in this sub-lane

- the general bottom stratum: several conjugate classes at one shell level.  A single extra
  conjugate class plus real points is reachable with a *periodic* choice `t = 2 pi k / B0` (one
  frequency, no Diophantine input); two or more distinct non-real classes need the Cesàro average
  `(1/T) integral_0^T ... dt`, whose cosine averages vanish elementarily — no Kronecker theorem is
  required in either case, only integration.
- the arithmetic core: `0 ≤ xiHeatTuranDefect t`, unproved.
