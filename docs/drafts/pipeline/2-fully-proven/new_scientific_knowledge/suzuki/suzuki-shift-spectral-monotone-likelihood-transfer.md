# Suzuki shift-spectral monotone-likelihood transfer

- **ID:** `suzuki-shift-spectral-monotone-likelihood-transfer`
- **Stage:** 2-fully-proven
- **Type:** SOURCE-SPECTRAL THEOREM / NEGATIVE-STIELTJES PRODUCER
- **Scientific status:** `[PAPER-PROVED] [LEAN CROSS-WRONSKIAN CORE] [CANDIDATE NOVEL APPLICATION] [NOT RH]`
- **Parent:**
  `../../1-in-progress/suzuki-negative-stieltjes-central-flux-colligation.md`
- **RH used:** no
- **Computation used:** no

## Problem closed

The source card conjectures normalized Euler--Gamma shift jet is negative Stieltjes.  Direct
formula is quotient of cross-resolvent matrix elements, not ordinary Donoghue function:

```text
q(lambda)=N(lambda)/D(lambda).
```

Checking `q'<=0`, then every alternating derivative, is not viable source principle.  The theorem
below replaces whole hierarchy by one spectral monotone-likelihood law.

## Theorem A: finite monotone spectral ratios are anti-Pick

Let real nodes satisfy `t_1<...<t_n`, let `w_j>0`, and let responses `r_j` be nondecreasing in
nodes.  Put

```text
D(z)=sum_j w_j/(t_j-z),
N(z)=sum_j w_j*r_j/(t_j-z),
q(z)=N(z)/D(z).
```

`D` has positive imaginary part in upper half-plane, hence never vanishes there.  Direct
symmetrization gives exact diagonal Pick identity

```text
Im q(z)/Im z
 =-[1/(2*|D(z)|^2)]
   sum_(j,k) w_j*w_k*(r_j-r_k)*(t_j-t_k)
   /(|t_j-z|^2*|t_k-z|^2).                            (1)
```

Every summand after minus sign is nonnegative before that sign.  Therefore

```text
Im q(z)<=0,  Im z>0.                                  (2)
```

Thus `q` is anti-Herglotz in shift variable.  Since `D` has one real zero between consecutive
nodes and no nonreal zeros, rational Herglotz partial-fraction theorem yields

```text
q(z)=ell-sum_k nu_k/(sigma_k-z),
nu_k>=0,                                               (3)
```

where `sigma_k` are uncancelled zeros of `D` and
`ell=(sum_j w_j*r_j)/(sum_j w_j)`.  Equation `(3)` is exactly negative-Stieltjes law conjectured
in parent card.  Constant responses produce zero measure, as required.

## Theorem B: measure and real-axis cross-Wronskian form

For positive base measure `mu`, spectral node `t`, and response `r` monovarying with `t`, define

```text
D(lambda)=integral (t-lambda)^(-1) dmu,
N(lambda)=integral r(t)(t-lambda)^(-1) dmu.
```

For `lambda` below support, quotient rule numerator is

```text
N'(lambda)D(lambda)-N(lambda)D'(lambda).               (4)
```

Squared resolvent reweights toward lower nodes.  Exact two-sample identity is

```text
(t_x-lambda)^(-2)(t_y-lambda)^(-1)
 -(t_y-lambda)^(-2)(t_x-lambda)^(-1)
 =(t_y-t_x)/[(t_x-lambda)^2(t_y-lambda)^2].            (5)
```

Multiplying `(5)` by `r(t_y)-r(t_x)` and integrating product measure proves `(4)<=0`.  Same
symmetrization as `(1)` gives anti-Pick property under standard integrability.  If quotient has
finite constant plus `O(1/z)` at infinity and is analytic off `[lambda_a,infinity)`, Herglotz
representation gives negative-Stieltjes measure supported there.

## Exact Suzuki instantiation

At aperture `a`, source card derived

```text
R_lambda=(A_a-lambda)^(-1),
e=e^x,
d=2(1+x),
h=h_a,

D_a(lambda)=<R_lambda e,d>,
N_a(lambda)=<R_lambda e,h>,
q_norm,lambda^EG=N_a(lambda)/D_a(lambda).              (6)
```

For real eigenbasis `A_a phi_j=t_j phi_j`, put

```text
w_j=<e,phi_j><d,phi_j>,
r_j=<h,phi_j>/<d,phi_j>.                               (7)
```

Whenever denominators in `(7)` are nonzero, `(6)` has form of Theorem A exactly.  Therefore
negative-Stieltjes conjecture is discharged by two source-pure spectral statements:

```text
w_j>=0,
(r_j-r_k)*(t_j-t_k)>=0.                                (8)
```

This is stronger and more falsifiable than derivative sign `(S36.9)`.  One violating eigenpair
kills transfer.  If `(8)` holds through compact-resolvent limit with required tightness, resulting
Stieltjes atoms are zeros of `D_a`, with nonnegative residues forced by `(1)`.

## RH frontier after theorem

Theorem closes abstract implication

```text
positive common cross-spectral measure + monotone source response
 -> negative-Stieltjes shift jet.
```

It does not establish actual Suzuki hypotheses `(8)`.  Remaining source work is exact:

1. prove `(8)` from prime--Gamma restricted-Weil operator, or exhibit first violating mode and
   retire Stieltjes route;
2. prove resulting Stieltjes chord mass reaches `ell_a-c_Xi` for one intrinsic nonescaping pair;
3. upgrade central scalar inequality to full normalized jump Pick kernel in spectral variable;
4. invoke existing Xi-pole theorem to conclude RH.

## Hostile tests

- Ground eigenfunction positivity alone does not imply `(8)` for excited modes.
- Positivity-preserving resolvent cannot be assumed; corpus has a breakdown theorem at large
  aperture.
- Ordinary Donoghue measure is in spectral variable `z`, not shift variable `lambda`.
- Near-ground Cayley and far-negative free limits remain forbidden schedules.
- Orbit-inserted FE--Schwarz countermodels must fail `(8)`, mass gap, or full jump kernel before Xi
  divisor identification.

## Formalization

`formal/GaloisForLFunctions/RHTower/SuzukiShiftSpectralMonotoneRatio.lean` proves `(5)`, integrated
cross-Wronskian inequality, and exact quotient-rule nonpositivity from monotone-likelihood kernel.
**The setup fact** — that `D` has positive imaginary part above the real axis and hence never
vanishes there — is formal in the same module.  It is what makes `q = N / D` well posed at all:

- `im_cauchyTerm`: a single Cauchy term's imaginary part is `w * Im z / |t - z|^2`.
- `im_cauchySum_pos`, `cauchySum_ne_zero`: a positive combination of Cauchy kernels is Herglotz
  above the real axis, hence nonvanishing there.
- `im_cauchySum_neg`, `cauchySum_ne_zero_of_im_ne_zero`: **`D` has no nonreal zeros** — off the real
  axis the imaginary part carries the sign of `Im z`, in both half-planes.  This is the half of the
  zero-structure claim behind `(3)` that needs no node ordering.
- `hasDerivAt_cauchySumReal`, `deriv_cauchySumReal_pos`, `injOn_cauchySumReal`: **the uniqueness
  half of the interlacing** — off the nodes the derivative is `sum w_j/(t_j - x)^2 > 0`, so `D` is
  strictly increasing on every node-free interval and takes each value at most once.  That is the
  "one" of "one real zero between consecutive nodes".
- `continuousOn_cauchySumReal`, `exists_zero_of_sign_change`,
  `existsUnique_zero_of_sign_change`: **`(3)`'s interlacing** — on a node-free interval whose
  endpoints carry opposite signs there is *exactly one* zero, existence by the intermediate value
  theorem and uniqueness by the strict monotonicity above.  The remaining analytic input is the sign
  change itself, which comes from the one-sided blow-up of the two bounding node terms — and that is
  formal too:
- `tendsto_cauchyTerm_atBot`, `tendsto_cauchyTerm_atTop`: a Cauchy term runs to `-infinity`
  approaching its node from the right and to `+infinity` from the left.  Since every other term stays
  continuous there, the combination inherits the blow-up, which is exactly the sign change the
  interlacing consumes.

**The constant term of `(3)`** — same module.  `ell = (sum w_j r_j)/(sum w_j)` is singled out by one
property: subtracting it makes the numerator a Cauchy transform of *zero total weight*, so `q - ell`
decays one order faster and no further constant survives.

- `suzukiShiftEll`, `sum_weight_sub_ell_eq_zero`: `ell` is exactly the value that zeroes the total
  weight of `w_j (r_j - ell)`.
- `numerator_sub_ell_mul`, `ratio_sub_ell_eq`: hence above the real axis `q - ell` is that
  zero-total-weight transform divided by `D`.

**Complex anti-Pick identity `(1)`** is now formal, in
`formal/GaloisForLFunctions/RHTower/SuzukiAntiPickIdentity.lean`.  The identity is algebra, not
analysis, and splits into two ingredients:

- `im_cauchy_mul_conj`: the imaginary part of a Cauchy factor against the conjugate of another
  carries the antisymmetric node difference `t_k - t_j`.
- `sum_sum_add_swap`: symmetrization of a double sum over one finite index set.
- `im_antiPick_sum`: **`(1)`** — symmetrized, every summand carries `(r_j - r_k)(t_j - t_k)` behind
  a leading minus sign, which is exactly what makes `(2)` read off from monotonicity.

The identity needs no nonvanishing hypothesis: it holds as stated with the junk values of division
by zero agreeing on both sides, so it applies verbatim at any spectral parameter.

**`(2)`, the anti-Herglotz sign**, follows in the same module:

- `antiPick_sum_nonneg`: monotone likelihood is exactly nonnegativity of every product
  `(r_j - r_k)(t_j - t_k)`, so with nonnegative weights the symmetrized sum is nonnegative.
- `im_antiPick_nonpos`: **`(2)` in summed form** — the leading minus sign of `(1)` and `Im z > 0`
  turn that nonnegativity into nonpositivity.
- `im_div_eq_im_mul_conj`, `im_ratio_nonpos_of_im_mul_conj_nonpos`: and a ratio whose numerator
  against the conjugate denominator has nonpositive imaginary part is anti-Herglotz.  This last
  needs no nonvanishing hypothesis either.

**The residue sign of `(3)`** is formal in the same module.  The partial-fraction form carries one
piece of content beyond its algebra — that the coefficients are nonnegative — and that sign is
forced pointwise:

- `im_poleTerm`: the imaginary part of a pole term directly above its own pole is `-nu/y`.
- `poleCoeff_nonneg_iff_im_nonpos`: **`nu_k >= 0`** — a pole term is anti-Herglotz on that line
  exactly when its coefficient is nonnegative.  No global partial-fraction theory is needed to see
  the sign; evaluating one term on one vertical line suffices, in both directions.

What remains of `(3)` is the algebraic decomposition itself — that `q` *has* this form with poles at
the uncancelled zeros of `D` — which needs the zero structure of `D` between consecutive nodes.
Concrete eigenvector instantiation `(7)--(8)` also remains paper-level; note that `(8)` is exactly
the monotone-likelihood hypothesis consumed by `antiPick_sum_nonneg`, so the abstract side of it is
already discharged.

## Novelty audit

Monotone-likelihood ordering and ratios of Cauchy transforms are classical.  Candidate novelty is
their exact use on Suzuki Euler--Gamma cross-resolvent quotient, identification of coefficient
laws `(8)` as complete negative-Stieltjes producer, and connection to chord-mass RH threshold.
External priority remains unverified.

## Gates

- [x] finite anti-Pick identity proved
- [x] negative-Stieltjes partial-fraction consequence proved
- [x] measure cross-Wronskian transfer proved
- [x] exact Suzuki eigen-coefficient conditions isolated
- [x] real-axis algebraic core formalized in Lean
- [ ] prove or falsify actual source coefficient laws `(8)`
- [ ] prove chord-mass gap for one source-selected pair
- [ ] prove full normalized jump Pick kernel
- [ ] RH

## Log

- 2026-08-01 — the complex anti-Pick identity `(1)` formalized (`im_antiPick_sum`), one of the three
  items this card listed as paper-level.  It is finite-sum algebra: the imaginary part of each mixed
  Cauchy term carries `t_k - t_j` (`im_cauchy_mul_conj`), and symmetrizing the double sum
  (`sum_sum_add_swap`) turns that into the factor `(r_j - r_k)(t_j - t_k)` behind a minus sign, from
  which `(2)` reads off directly.  No nonvanishing hypothesis is needed — division-by-zero junk
  values agree on both sides — so the identity holds at every spectral parameter.  Targeted build
  green, axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(2)` derived from `(1)` (`im_antiPick_nonpos`,
  `im_ratio_nonpos_of_im_mul_conj_nonpos`).  Monotone likelihood enters exactly as nonnegativity of
  each `(r_j - r_k)(t_j - t_k)`, which the symmetrization of `(1)` isolates; the leading minus sign
  and `Im z > 0` then give the anti-Herglotz sign.  The ratio step also needs no nonvanishing
  hypothesis, since `Complex.div_im` already handles a zero denominator consistently.  Targeted
  build green, axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the residue sign of `(3)` formalized (`poleCoeff_nonneg_iff_im_nonpos`).  The
  nonnegativity `nu_k >= 0` needs no partial-fraction theory: evaluating a single pole term on the
  vertical line above its own pole gives `-nu/y`, so anti-Herglotz and nonnegativity are equivalent
  there, in both directions.  What remains of `(3)` is the decomposition itself, which needs the
  zero structure of `D`.  Recorded also that `(8)` is precisely the monotone-likelihood hypothesis
  `antiPick_sum_nonneg` consumes, so its abstract side is discharged and only the concrete
  eigenvector data is outstanding.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the setup fact formalized (`im_cauchySum_pos`, `cauchySum_ne_zero`): a positive
  combination of Cauchy kernels is Herglotz above the real axis and therefore nonvanishing, which is
  what makes the ratio `q = N/D` well posed.  The card states this in passing while setting up, and
  it had no declaration although everything downstream depends on it.  Targeted build green, axiom
  audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — "`D` has no nonreal zeros" formalized (`cauchySum_ne_zero_of_im_ne_zero`), the half
  of `(3)`'s zero-structure claim that needs no node ordering: off the real axis the imaginary part
  of a positive Cauchy combination carries the sign of `Im z`, in both half-planes.  What remains of
  the zero structure is the interlacing — one real zero between consecutive nodes — which is an
  intermediate-value argument requiring the nodes ordered and the one-sided limits at them.
  Targeted build green, axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the uniqueness half of `(3)`'s interlacing formalized (`deriv_cauchySumReal_pos`,
  `injOn_cauchySumReal`): off the nodes `D' = sum w_j/(t_j-x)^2 > 0`, so `D` is strictly increasing
  on every node-free interval and has at most one zero there.  "One real zero between consecutive
  nodes" is thus two claims with different proofs — uniqueness from the derivative sign, needing no
  ordering, and existence from the sign change at the endpoints, needing the nodes ordered and their
  one-sided limits.  Only the latter remains.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(3)`'s interlacing assembled (`existsUnique_zero_of_sign_change`): on a node-free
  interval with a sign change there is exactly one zero, existence by the intermediate value theorem
  and uniqueness by the derivative sign.  What is left of the zero structure is only the sign change
  itself — the one-sided blow-up of the two bounding node terms — which is where the node ordering
  and the limits actually enter.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the one-sided blow-up formalized (`tendsto_cauchyTerm_atBot`,
  `tendsto_cauchyTerm_atTop`): a Cauchy term runs to `-infinity` approaching its node from the right
  and `+infinity` from the left.  With the interlacing lemmas this makes the whole zero-structure
  claim behind `(3)` formal — no nonreal zeros, exactly one real zero per node-free interval with a
  sign change, and the blow-up that produces the sign change.  What remains of `(3)` is only the
  assembly into the partial-fraction form.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the constant term of `(3)` formalized (`suzukiShiftEll`,
  `sum_weight_sub_ell_eq_zero`, `ratio_sub_ell_eq`).  The card names `ell` as the weighted mean
  without saying what singles it out; the answer is that subtracting it zeroes the numerator's total
  weight, so `q - ell` is a zero-total-weight Cauchy transform over `D` and decays one order faster.
  With this and the zero structure, what remains of `(3)` is the residue extraction assembling the
  pieces into the displayed form.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
