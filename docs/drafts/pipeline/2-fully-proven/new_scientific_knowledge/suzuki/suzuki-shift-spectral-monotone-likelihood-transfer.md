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
- `tendsto_residue_of_simple_zero`: **the residue extraction** — at a simple zero of `D` the residue
  of `N/D` is `N(sigma)/D'(sigma)`, obtained as the limit of `(z - sigma) q(z)`.  No contour is
  needed: dividing by `z - sigma` turns the denominator into its own difference quotient at `sigma`,
  which converges to `D'(sigma)` precisely because `D(sigma) = 0`.  This names the coefficient
  `nu_k` of each pole.
- `residue_poleTerm`, `poleCoeff_eq_residue`: **the coefficients are forced.**  If the ratio
  decomposes as a pole term at `sigma` plus something continuous there, that pole's coefficient
  *must* be `N(sigma)/D'(sigma)`.  So a decomposition of the displayed shape is unique, with exactly
  the coefficients the extraction names — and by `poleCoeff_nonneg_iff_im_nonpos` they are
  nonnegative, which is `nu_k >= 0`.

**The existence step needs no Liouville argument** — mathlib already carries partial fractions, in
`Mathlib/Algebra/Polynomial/PartialFractions.lean`.  Its specialization to distinct linear factors
is in `formal/GaloisForLFunctions/HTGeometry/LinearPartialFractions.lean`:

- `eq_C_of_degree_lt_one`: a polynomial of degree below one is a constant.
- `div_linear_prod_eq_add_sum_const`: hence over a product of distinct monic linear factors the
  remainders are constants, so the decomposition is `q + sum nu_i/(X - sigma_i)` with **scalar**
  coefficients — exactly the shape `(3)` displays.

Every ingredient of `(3)` is therefore formal: the constant term, the zero structure, the residue
formula, the uniqueness of the coefficients, their sign, and the general decomposition over linear
factors.

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

## Theorem A itself, and the instantiation (formal)

Two named theorems sat on either side of an *unstated* identity: `im_antiPick_nonpos` gave the
symmetrized double sum its sign, and `im_ratio_nonpos_of_im_mul_conj_nonpos` consumed
`Im(N conj D) <= 0`, but nothing said the double sum **is** `Im(N conj D)`.  Theorem A was therefore
not proved as a statement about `q = N/D`, though every piece of it was.  The join is in
`SuzukiAntiPickIdentity.lean`:

- `im_numerator_mul_conj_denominator`: expanding the product of the two Cauchy sums and taking
  imaginary parts termwise gives exactly the symmetrized double sum of `(1)`.
- `im_shiftRatio_nonpos`: **Theorem A** — with nonnegative weights and monotone responses the ratio
  of Cauchy transforms is anti-Herglotz above the real axis.
- `shiftRatio_eq_const_of_response_const`: **constant responses give the constant ratio**, so the
  Stieltjes measure vanishes — the card's "as required".

The instantiation `(6)--(7)` is formal too, in
`formal/GaloisForLFunctions/RHTower/SuzukiCrossResolventInstantiation.lean`.  A finite orthonormal
eigenbasis makes the resolvent explicit, and its matrix elements are then Cauchy combinations:

- `spectralOperator`, `spectralResolvent`, `spectralOperator_basis`,
  `spectralOperator_spectralResolvent`: the construction is genuinely the resolvent — off the
  spectrum it inverts `A - lambda`.
- `inner_spectralResolvent`: **the matrix element is a Cauchy combination**, its weight at each node
  the product of the two vectors' spectral coefficients.
- `crossWeight`, `crossResponse`, `inner_spectralResolvent_denominator`,
  `inner_spectralResolvent_numerator`: **`(6)` has the form of Theorem A exactly**, with
  `w_j = <e,phi_j><d,phi_j>` and `r_j = <h,phi_j>/<d,phi_j>` — this is `(7)`.
- `crossWeight_self_nonneg`: a diagonal cross weight is a square, so the weight half of `(8)` is
  automatic when `e = d`.
- `im_crossResolventRatio_nonpos`: **the card's "Therefore"** — given the two source-pure spectral
  statements `(8)`, the cross-resolvent quotient is anti-Herglotz.  Nothing else about the operator
  is used.

So `(8)` really is the whole remaining source debt: the abstract implication it feeds is now formal
end to end, and the concrete eigenvector data is all that is outstanding.

## Theorem B's derivative identification (formal)

The same joint appeared in Theorem B.  `suzukiShiftSpectralMonotoneRatio_derivativeNumerator_nonpos`
signs an expression built from four integrals, and its docstring asserted that this expression "is
exactly `(N' D - N D') / D^2`" — but nothing proved it, so the sign was not yet monotonicity of
anything.  Closed in `SuzukiShiftSpectralMonotoneRatio.lean`:

- `hasDerivAt_suzukiShiftResolventKernel`: **the kernel's shift derivative is its own square**.  This
  is why squared resolvents appear at all — they are not a reweighting chosen for convenience but
  what differentiation produces.
- `hasDerivAt_integral_weighted_suzukiShiftResolventKernel`: under the standard domination
  hypotheses, differentiating under the integral turns each matrix element into its squared-kernel
  counterpart.
- `hasDerivAt_suzukiShiftRatio`: **`(4)` is the derivative** — the quotient rule assembles the four
  integrals into exactly the displayed expression.
- `deriv_suzukiShiftRatio_nonpos`: **Theorem B** — hence the source quotient is nonincreasing in the
  shift variable.

## The measure-level anti-Pick property (formal)

Theorem B's second claim — "same symmetrization as `(1)` gives anti-Pick property under standard
integrability" — is formal in `formal/GaloisForLFunctions/RHTower/SuzukiMeasureAntiPick.lean`, and it
needs no complex integration theory.  Splitting the kernel as `1/(t - z) = u + i v` with
`u = (t - Re z)/|t - z|^2` and `v = Im z/|t - z|^2` reduces the whole statement to the corpus's own
integrated monotone-likelihood theorem:

- `cauchyKernel_cross_eq`: **the two-sample kernel collapses.**  In `v(x) u(y) - v(y) u(x)` the real
  part of the spectral parameter cancels, leaving `Im z (t y - t x)` over the two squared
  denominators — exactly the antisymmetric node increment of `(1)`.
- `monotoneLikelihood_cauchyKernel`: so above the real axis, monotone likelihood *is* the sign
  hypothesis `integral_mul_integral_le_of_monotoneLikelihoodKernel` consumes.
- `integral_cauchyKernel_crossWronskian_le`: hence the cross-multiplied expectation order.
- `im_measureNumerator_mul_conj_denominator`: the imaginary part of the numerator against the
  conjugate denominator is those same four real integrals.
- `im_measureShiftRatio_nonpos`: **Theorem B's anti-Pick property** — the ratio of the two Cauchy
  transforms is anti-Herglotz above the real axis.

That `Re z` cancels in the two-sample kernel is why the finite and measure symmetrizations are the
same computation: the anti-Pick sign never depended on the real part of the spectral parameter.

## Toward the Herglotz representation

Theorem B's last sentence cites the Herglotz representation as a classical input.  **mathlib has no
Herglotz representation theorem**, but it does carry the Poisson integral formula for harmonic
functions on discs (`InnerProductSpace.HarmonicContOnCl.circleAverage_poissonKernel_smul`) and the
mean value property.  The layer that turns those into representation input is in
`formal/GaloisForLFunctions/HTGeometry/PoissonBoundaryPositivity.lean`:

- `poissonKernel_pos`: the Poisson kernel is strictly positive at every interior point.
- `nonneg_of_nonneg_on_sphere`: hence **positivity propagates inward** — a harmonic function
  nonnegative on the bounding circle is nonnegative on the whole disc.
- `poissonBoundaryData`: on every disc a nonnegative harmonic function has boundary data that
  (i) reproduces it against the Poisson kernel, (ii) is nonnegative, and (iii) has total mass exactly
  the centre value.  These three are precisely what a Herglotz representation consumes: a family of
  positive boundary measures with mass pinned independently of the radius, hence uniformly bounded.
- `harmonicAt_neg_im`, `nonneg_neg_im_on_sphere`,
  `nonneg_neg_im_of_antiHerglotz_on_sphere`: an anti-Herglotz function supplies exactly that data,
  and the sign propagates inward from a circle in the upper half-plane without assuming the disc
  lies there.

The boundary data is packaged as an actual measure in the same module, which is the object a weak-*
limit acts on:

- `poissonBoundaryMeasure`: the boundary values as a density in the angle.
- `integral_poissonBoundaryMeasure`: integrating against it is the angular average weighted by the
  boundary values.
- `integral_one_poissonBoundaryMeasure`: **its total mass is the centre value, for every radius** —
  the bound is uniform because it does not depend on the radius at all.
- `integral_poissonKernel_poissonBoundaryMeasure`: testing it with the Poisson kernel returns the
  value of the function.

What remains for the representation is the weak-* limit of that bounded family as the discs exhaust
the domain, and the transfer to the half-plane with support on the ray.

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
- 2026-08-01 — the residue extraction of `(3)` formalized (`tendsto_residue_of_simple_zero`): at a
  simple zero of `D` the residue of `N/D` is `N(sigma)/D'(sigma)`, as the limit of
  `(z - sigma) q(z)`.  The proof needs no contour integration — dividing by `z - sigma` turns `D`
  into its own difference quotient at `sigma`, which converges to `D'(sigma)` because `D(sigma) = 0`.
  Every structural ingredient of `(3)` is now formal: the constant term, the zero structure, the
  residue formula naming each `nu_k`, and the sign forcing `nu_k >= 0`.  Targeted build green, axiom
  audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the coefficient identification of `(3)` formalized (`poleCoeff_eq_residue`): a pole
  term's coefficient in any such decomposition must equal the residue, so the decomposition is
  unique with exactly the coefficients already named, and their nonnegativity is the residue-sign
  lemma.  What is left of `(3)` is only *existence* of the decomposition — the Liouville-type step
  that `q` has this shape — everything about its constant, poles, coefficients and signs being
  proved.  Targeted build green, axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the existence step of `(3)` does not need a Liouville argument: mathlib carries
  partial fractions (`div_prod_eq_quo_add_sum_rem_div`).  Specialized to distinct linear factors
  (`div_linear_prod_eq_add_sum_const`), the remainders have degree below one and are therefore
  constants, giving exactly the scalar-coefficient shape `(3)` displays.  What remains of `(3)` is
  the bridge for this denominator — clearing the Cauchy sum to a polynomial whose roots are exactly
  the `sigma_k`, simple, and counted by its degree.  Checking mathlib before planning the step
  replaced a projected complex-analysis build with one lemma application.  Targeted build green,
  axiom audit `[propext, Classical.choice, Quot.sound]`.

## The factorization bridge (formal)

Clearing the denominators turns the shift ratio into a ratio of polynomial values, and a degree
count turns the analytic zero structure into an actual factorization.

In `formal/GaloisForLFunctions/RHTower/SuzukiAntiPickIdentity.lean`:

- `prod_mul_cauchySum`: the node product times a Cauchy combination is the sum of the weights
  against the complementary products — each term loses its own factor and keeps the rest.
- `prod_node_ne_zero`, `cauchyRatio_eq_polyRatio`: hence `q = N/D` is a ratio of two polynomial
  values, both of degree at most one below the node count.
- `cauchyClearedPoly`, `aeval_cauchyClearedPoly`, `natDegree_cauchyClearedPoly_le`,
  `prod_mul_cauchySum_eq_aeval`: the cleared combination is the value of an honest polynomial of
  degree at most `n - 1`.

In `formal/GaloisForLFunctions/HTGeometry/LinearPartialFractions.lean`:

- `prod_X_sub_C_dvd_of_isRoot`: distinct roots contribute a product of linear factors as a divisor
  (pairwise coprimality plus `Finset.prod_dvd_of_coprime`).
- `eq_C_mul_prod_X_sub_C`: **the factorization bridge** — a polynomial of degree at most `card s`
  vanishing at `card s` distinct points is a constant times the product of the linear factors, the
  degrees leaving only a constant cofactor.
- `div_eq_add_sum_const_of_isRoot`: **partial fractions from a root list** — a rational function
  whose denominator has degree at most `card s` and vanishes at `card s` distinct points decomposes
  as a polynomial part plus one simple pole at each point, with scalar residues.

This closes the gap between the analytic zero structure and the algebraic decomposition: the
zero-counting theorems produce a root list, and `div_eq_add_sum_const_of_isRoot` consumes a root
list.

## The root list and `(3)`'s existence (formal)

The indexing step is formal too, so `(3)` holds unconditionally in the ordered-node setting.  In
`SuzukiAntiPickIdentity.lean`:

- `tendsto_cauchySumReal_atBot` / `_atTop`: the whole combination inherits the one-sided blow-up at
  a node — its own term diverges and every other term stays continuous there.
- `exists_mem_Ioo_cauchySumReal_neg` / `_pos`: hence it is negative just right of a node and
  positive just left of one, which is the sign change.
- `existsUnique_zero_in_gap`: exactly one zero between consecutive nodes — sign change for
  existence, `strictMonoOn_cauchySumReal` for uniqueness.
- `eval_cauchyClearedPoly`, `prod_mul_cauchySumReal_eq_eval`, `isRoot_cauchyClearedPoly`: a zero of
  the combination is a root of the cleared polynomial, the node product not vanishing there.
- `cauchyClearedPoly_ne_zero`: below every node all terms are positive, so the polynomial is nonzero.
- `exists_injective_gapRoots`: with the nodes strictly increasing, the `n` gap zeros are distinct —
  they lie in disjoint intervals — and each is a root.
- `exists_factorization_cauchyClearedPoly`: `n` distinct roots of a polynomial of degree at most `n`,
  so the factorization bridge gives `c * prod (X - sigma_i)` with `sigma_i` in the `i`-th gap.
- `exists_partialFractions_shiftRatio`: **`(3)`, existence** — the cleared shift ratio is a
  polynomial part plus one simple pole per node gap, with scalar residues.

The interlacing is not an extra hypothesis: it is where the roots come from, and its disjointness is
what makes them distinct.  Degree `n` and `n` roots then leave no freedom.

- 2026-08-01 — the bridge from the analytic zero structure to the algebraic factorization is formal.
  The clearing identity (`prod_mul_cauchySum`) makes the denominator a polynomial of degree at most
  `n - 1`; the factorization bridge (`eq_C_mul_prod_X_sub_C`) turns `n - 1` distinct roots plus that
  degree bound into `c * prod (X - sigma_k)`; and `div_eq_add_sum_const_of_isRoot` chains it with the
  linear-factor partial fractions to give the decomposition shape `(3)` displays, directly from a
  root list.  The general form needs no ordering — only the final indexing of the interlacing zeros
  does.  All ten new declarations built green with axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(3)`'s existence is closed unconditionally.  The chain runs: blow-up at each node
  gives a sign change; sign change plus strict monotonicity gives exactly one zero per gap
  (`existsUnique_zero_in_gap`); the clearing identity makes each zero a root of a polynomial of
  degree at most `n`; disjointness of the gaps makes the `n` roots distinct; and the factorization
  bridge then forces `c * prod (X - sigma_i)`, so the partial-fraction decomposition follows with one
  simple pole per gap (`exists_partialFractions_shiftRatio`).  The interlacing is not an added
  assumption — it is the source of the roots, and the count is exactly tight.  Thirteen new
  declarations, targeted build green, axioms `[propext, Classical.choice, Quot.sound]` throughout.
- 2026-08-01 — **Theorem A itself was not proved**, though every named piece of it was.
  `im_antiPick_nonpos` signed the symmetrized double sum and `im_ratio_nonpos_of_im_mul_conj_nonpos`
  consumed `Im(N conj D) <= 0`, but no declaration said the two were the same quantity.  The missing
  link is `im_numerator_mul_conj_denominator` — expand the product of the Cauchy sums, take imaginary
  parts termwise, and `(1)`'s double sum appears — after which `im_shiftRatio_nonpos` is Theorem A
  for the ratio `q = N/D`.  Also formal: constant responses give a constant ratio and hence zero
  measure (`shiftRatio_eq_const_of_response_const`), the card's "as required".
- 2026-08-01 — the instantiation `(6)--(7)` formalized in `SuzukiCrossResolventInstantiation.lean`.
  A finite orthonormal eigenbasis makes the resolvent explicit and verifiable
  (`spectralOperator_spectralResolvent` shows it inverts `A - lambda`), and its matrix elements are
  Cauchy combinations with weights `<e,phi_j><d,phi_j>` — which is `(7)` verbatim.  Hence
  `im_crossResolventRatio_nonpos`: the two source-pure statements `(8)` give the anti-Herglotz sign
  with nothing else about the operator used.  The card's "Therefore ... is discharged by two
  source-pure spectral statements" is now a theorem rather than a connective, and `(8)`'s concrete
  eigenvector data is the entire remaining source debt.  Eleven new declarations, targeted builds
  green, axioms `[propext, Classical.choice, Quot.sound]` throughout.
- 2026-08-01 — Theorem B had the same joint gap as Theorem A: the cross-Wronskian law signed an
  expression whose docstring *claimed* it was `(N' D - N D')/D^2`, with nothing proving it.  Closed by
  `hasDerivAt_suzukiShiftResolventKernel` (the kernel's shift derivative is its own square — which is
  why squared resolvents appear at all, they are what differentiation produces rather than a chosen
  reweighting), `hasDerivAt_integral_weighted_suzukiShiftResolventKernel` (differentiation under the
  integral, standard domination), `hasDerivAt_suzukiShiftRatio` (the quotient rule assembling the
  four integrals into the displayed expression), and `deriv_suzukiShiftRatio_nonpos` (**Theorem B**:
  the quotient is nonincreasing in the shift variable).  A docstring asserting an identity is the
  same failure mode as a card sentence asserting one.  Targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — Theorem B's measure-level anti-Pick property formalized
  (`SuzukiMeasureAntiPick.lean`), and it needs no complex integration theory.  Splitting the kernel
  into `u + i v` reduces the claim to the corpus's own `integral_mul_integral_le_of_monotoneLikelihoodKernel`:
  the two-sample kernel `v(x) u(y) - v(y) u(x)` collapses to `Im z (t y - t x)` over the two squared
  denominators (`cauchyKernel_cross_eq`), because **`Re z` cancels**.  That cancellation is why the
  finite and measure symmetrizations are the same computation — the anti-Pick sign never depended on
  the real part of the spectral parameter.  Chain: kernel sign → cross-multiplied expectation order →
  `Im(N conj D)` in four real integrals → `im_measureShiftRatio_nonpos`.  Eight new declarations,
  targeted build green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — first installment on Theorem B's Herglotz representation step.  **mathlib has no
  Herglotz representation theorem**, but it does have the Poisson integral formula for harmonic
  functions on discs and the mean value property, so the missing layer is the positivity/mass
  packaging: `poissonKernel_pos` (strict interior positivity), `nonneg_of_nonneg_on_sphere`
  (positivity propagates inward), and `poissonBoundaryData` — on every disc the boundary data
  reproduces the function, is nonnegative, and has total mass exactly the centre value.  That third
  component is the uniform bound the weak-* limit needs, and it comes free from the mean value
  property rather than from any estimate.  An anti-Herglotz function supplies this data on every
  circle in the upper half-plane (`nonneg_neg_im_of_antiHerglotz_on_sphere`), and the sign then
  propagates inward without assuming the disc lies in the half-plane.  Remaining: the weak-* limit as
  the discs exhaust the domain, and the half-plane transfer with support on the ray.  Six new
  declarations, targeted build green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the boundary data packaged as a measure (`poissonBoundaryMeasure`), with the three
  properties stated as integrals against it: the angular-average formula
  (`integral_poissonBoundaryMeasure`), the representation
  (`integral_poissonKernel_poissonBoundaryMeasure`), and the total mass
  (`integral_one_poissonBoundaryMeasure`).  The mass identity is the point: it equals the centre
  value for **every** radius, so the family is uniformly bounded with no estimate involved — the
  mean value property supplies the compactness input directly.  Four new declarations, targeted build
  green, axioms `[propext, Classical.choice, Quot.sound]`.
