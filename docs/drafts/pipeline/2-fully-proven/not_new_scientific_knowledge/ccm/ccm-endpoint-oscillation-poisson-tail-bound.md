# CCM endpoint-oscillation Poisson-tail bound

- **ID:** `ccm-endpoint-oscillation-poisson-tail-bound`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** classical Poisson summation, Fourier series of the sawtooth, and fixed-mode
  prolate concentration asymptotics
- **Statement:** On an even compactly supported smooth source, the CCM arithmetic sum of the
  exterior Fourier tail is controlled by endpoint jets. Its leading `1/y` tail produces the
  uniformly bounded sine series, so the generic coherent-growth obstruction is absent on this
  source class.

## Theorem

Let `f` be even and `C2` on `[-lambda,lambda]`, extend it by zero, and suppose

```text
integral_R f(x)dx=0.                                   (1)
```

Use the Fourier convention

```text
Ff(y)=integral_R f(x)exp(2*pi*i*x*y)dx.
```

For almost every `v>=lambda`, Poisson summation and endpoint Fourier expansion give

```text
E(f)(1/v)
 =sqrt(v) sum_(n>=1) Ff(nv)-f(0)/(2sqrt(v)),           (2)
```

and

```text
|E(f)(1/v)|
 <= (|f(lambda)|+|f(0)|)/(2sqrt(v))
    +( |f'(lambda)|+||f''||_L1(0,lambda) )/(12v^(3/2)). (3)
```

Consequently,

```text
||1_(0,lambda^(-1)) E(f)||_(L2(d*u))
 <= (|f(lambda)|+|f(0)|)/(2sqrt(lambda))
    +( |f'(lambda)|+||f''||_1 )/(12sqrt(3)lambda^(3/2)). (4)
```

The formula is unchanged as an `L2` statement if the exceptional values at which a lattice point
hits an endpoint are assigned either one-sided value.

## Proof

For values of `v` at which the periodization is continuous at the sampling point, Poisson summation
gives

```text
sum_(m in Z) f(m/v)=v sum_(n in Z) Ff(nv).             (5)
```

Both functions are even, and `(1)` says `Ff(0)=0`. Separating the zero terms in `(5)` and dividing
by `2sqrt(v)` proves `(2)`. The usual midpoint convention proves the same identity at the remaining
values, which form a null set for the norm estimate.

Twice integrating by parts on `[0,lambda]`, using `f'(0)=0`, gives for `y!=0`

```text
Ff(y)
 = f(lambda)sin(2*pi*lambda*y)/(pi*y)
   +f'(lambda)cos(2*pi*lambda*y)/(2*pi^2*y^2)
   -1/(2*pi^2*y^2)
      integral_0^lambda f''(x)cos(2*pi*x*y)dx.         (6)
```

Substitute `y=nv` and sum. The leading endpoint jump is not estimated term by term: the exact
sawtooth Fourier series gives

```text
|sum_(n>=1) sin(n*theta)/n|<=pi/2.                    (7)
```

The remaining terms are absolutely summable, and

```text
sum_(n>=1) 1/n^2=pi^2/6.                              (8)
```

Multiplication by `sqrt(v)` in `(2)` now gives `(3)`. Under `u=1/v`, the measure `d*u` is invariant.
Minkowski's inequality and

```text
integral_lambda^infinity v^(-1) d*v=1/lambda,
integral_lambda^infinity v^(-3) d*v=1/(3lambda^3)
```

give `(4)`.

## Deficit-scale central correction for the CCM seed

Let `e_0=h_(0,lambda)`, `e_1=h_(4,lambda)`, with compressed-Fourier eigenvalues `chi_0>chi_1`, and
put

```text
ell_j=integral_R e_j=chi_j e_j(0),
d_j=1-chi_j^2.
```

The normalized zero-integral CCM two-mode source is

```text
g_lambda=(ell_1 e_0-ell_0 e_1)/sqrt(ell_0^2+ell_1^2). (9)
```

Direct evaluation at zero gives the exact identity

```text
g_lambda(0)
 =ell_0 ell_1(chi_1-chi_0)
   /(chi_0 chi_1 sqrt(ell_0^2+ell_1^2)).               (10)
```

The fixed-mode asymptotics proved in `constrained-prolate-two-mode-ground-state.md` imply

```text
d_0/d_1->0,
ell_0->2^(1/4),
ell_1->sqrt(3)/2^(5/4),
chi_0-chi_1~d_1/2.
```

Therefore, for the orientation in `(9)`,

```text
g_lambda(0)/d_1
 ->-2^(-3/4)sqrt(3/11).                               (11)
```

Thus the Poisson zero-mode correction in `(2)` is of concentration-deficit order `d_1`, not
square-root-leakage order `sqrt(d_1)`. This is the exact first-order cancellation created by the
zero-integral combination.

## Route consequence

`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-poisson-tail-l2-unboundedness.md`
proves that the arithmetic tail map is unbounded on the
ambient leakage space because coherent slowly varying logarithmic packets make the Dirichlet sum
grow. Equations `(3)`--`(7)` show that this mechanism is absent for a fixed smooth compact source:
its leading Fourier leakage oscillates as an endpoint sine series and is uniformly summable.

This does not yet prove the CCM comparison. Equation `(4)` replaces the generic operator norm by
the exact source quantities that must now be estimated:

```text
g_lambda(lambda),
g_lambda'(lambda),
||g_lambda''||_1,
```

or higher endpoint jets after further integrations by parts. The central term is already at the
correct deficit scale by `(11)`. What remains is to show that the endpoint-jet remainder enters the
closed Weil residual quadratically, or otherwise below the constrained gap, and then to obtain the
projective rate required for locally uniform determinant convergence.

## Novelty and significance verdict

The bound is assembled from classical Poisson summation, two integrations by parts, and the
sawtooth Fourier series. Identity `(11)` is an algebraic consequence of the fixed-mode theorem and
Fuchs asymptotics. The combination materially sharpens the CCM open core by proving that its
special leakage does not realize the generic coherent-growth obstruction, but the mathematical
ingredients do not clear the dual novelty/significance gate. It is classified as a bridge.

## References

- A. Connes, C. Consani, *Spectral triples and zeta-cycles*, arXiv:2106.01715.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- W. H. J. Fuchs, *On the eigenvalues of an integral equation arising in the theory of band-limited
  signals*, J. Math. Anal. Appl. 9 (1964), 317--330.

## Lean status

**Partially superseded, 2026-08-04.**  The Fourier input `(7)` is formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/SawtoothFourierSeries.lean`, together with the sawtooth series
identity it rests on.  The previous decision said formalizing "only the sawtooth estimate" would be a
wrapper.  It is the opposite of a wrapper: `(7)` is the one step of the proof that is **not** available
in mathlib, because the series `∑ sin(nθ)/n` is only conditionally convergent and therefore cannot be
stated as a `HasSum` at all.  Mathlib's Bernoulli Fourier expansions
(`hasSum_one_div_nat_pow_mul_sin`) start at exponent three for exactly this reason.

- `expCoeff`, **`norm_sum_exp_le`**, **`exists_tendsto_sum_expCoeff`** — the harmonic exponential
  coefficients `e^{inθ}/n`, the geometric bound on the exponential partial sums off the lattice, and
  convergence by Dirichlet's test.  The bound reuses the corpus's own `RHTower.norm_geom_sum_le`.
- **`tsum_expCoeff_mul_pow`** — inside the disc the generating function is `-log(1 - x e^{iθ})`, from
  mathlib's `hasSum_taylorSeries_neg_log`.  The `n = 0` term is `0` on both sides because division by
  zero is zero, so no index surgery is needed.
- `one_sub_exp_mul_I_eq`, **`arg_one_sub_exp_mul_I`**, **`im_neg_log_one_sub_exp`** — the boundary
  chord in polar form, `1 - e^{iθ} = 2 sin(θ/2) e^{i(θ-π)/2}`, and hence
  `Im(-log(1 - e^{iθ})) = (π - θ)/2`.
- **`tendsto_sum_expCoeff`**, **`tendsto_sum_sawtoothSine`** — Abel's limit theorem glues the two:
  on `(0, 2π)` the sine series converges to `sawWave θ = (π - θ)/2`.  This is the same route the corpus
  already used for its odd-harmonic (square-wave) series, so the two Fourier series now share one
  method.
- **`exists_sum_sawtoothSine_abs_le`**, `exists_mem_Ioo_sub_int_mul_two_pi`,
  `sawtoothSine_periodic`, **`exists_sum_sawtoothSine_abs_le_of_ne`** — equation `(7)` itself:
  the series converges and its sum is at most `π/2` in absolute value, for **every** angle off the
  lattice `2πZ`, which is the form the card's substitution `y = nv` needs.

Equation `(8)` is mathlib's `hasSum_zeta_two` and needs no corpus work.

Equation `(6)` is formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCMEndpointFourierJet.lean`:

- `hasDerivAt_linScaled`, `hasDerivAt_sinScaled`, `hasDerivAt_negCosScaled` — the two antiderivatives
  of `cos(2πxy)` and `sin(2πxy)`.
- **`integral_mul_cos_ibp`**, **`integral_mul_sin_ibp`** — the two integrations by parts, each stated
  with the constant `1/(2πy)` already extracted so that the composition is pure algebra.
- **`integral_mul_cos_twice_ibp`** — equation `(6)` on the half-interval, with the `f'(0)` boundary term
  kept explicit rather than assumed away, so the hypothesis `f'(0) = 0` is used exactly once.
- `integral_symm_eq_two_mul_of_even`, `integral_symm_eq_zero_of_odd`,
  **`integral_symm_mul_cos_eq`**, **`integral_symm_mul_sin_eq_zero`** — the even/odd reduction to the
  endpoint half-interval.  The vanishing of the sine transform is the statement that the Fourier
  transform of the even extension is real, which the card uses implicitly.
- **`integral_symm_mul_cos_endpoint_jet`** — `(6)` for the full symmetric interval: the endpoint jet at
  `λ` carries the whole transform up to a second-derivative remainder of order `y^{-2}`.

Equation `(3)` is formalized in the same module, on the Fourier side of `(2)`:

- `endpointLeadTerm`, `endpointRemTerm`, **`endpointLeadTerm_eq`** — the `1/y` and `1/y²` parts of `(6)`
  sampled at `y = n v`.  The leading term is exactly `(A/(π v))` times the `n`-th sawtooth sine term, so
  the whole leading series *is* the sawtooth series at angle `2π λ v`.
- **`exists_tendsto_sum_endpointLeadTerm`** — the leading series converges off the lattice `λ v ∉ Z`,
  with sum at most `|A|/(2v)`.  This is the step the card flags: the leading endpoint jump is *not*
  estimated term by term — term by term it would only give a divergent harmonic sum — but through
  `(7)`, whose value `π/2` produces the constant `1/2`.
- `summable_one_div_sq`, `abs_endpointRemTerm_le`, **`summable_endpointRemTerm`**,
  **`abs_tsum_endpointRemTerm_le`** — the remainder series converges absolutely with sum at most
  `(|B| + C)/(12 v²)`, where `C` bounds the second-derivative integral.  The constant `1/12` is
  `(1/(2π²))·(π²/6)`, so `(8)` enters exactly once.
- **`abs_fourierTail_le`** — equation `(3)` assembled:

  ```text
  | sqrt(v) sum_(n>=1) Ff(nv) - f(0)/(2 sqrt(v)) |
    <= (|f(lambda)| + |f(0)|)/(2 sqrt(v))
       + (|f'(lambda)| + ||f''||_1)/(12 v^(3/2)),
  ```

  with every constant matching the card.  Note what this does *not* need: `(2)` is used only to identify
  the left-hand side with `E(f)(1/v)`; the estimate itself is unconditional on the Fourier side.

Equation `(4)` is formalized in the same module:

- `inv_pow_eq_rpow`, `integrableOn_Ioi_inv_pow`, `integral_Ioi_inv_pow`, **`integral_Ioi_inv_sq`**,
  **`integral_Ioi_inv_cube`**, **`integral_Ioi_inv_four`** — the three improper moments
  `∫_λ^∞ v^{-2} = 1/λ`, `∫_λ^∞ v^{-3} = 1/(2λ²)`, `∫_λ^∞ v^{-4} = 1/(3λ³)`.  The card lists only the
  first and third; the middle one is the cross term.
- `integrableOn_endpointDominant`, **`integral_endpointDominant`** — the squared dominating profile of
  `(3)` against `d*v`, integrating to `a²/λ + ab/λ² + b²/(3λ³)`.
- **`integral_sq_div_le_of_endpoint_bound`** — equation `(4)`:

  ```text
  int_lambda^infinity |G(v)|^2 d*v
    <= ( a sqrt(1/lambda) + b sqrt(1/(3 lambda^3)) )^2,
  ```

  which is the card's bound with `a = (|f(λ)| + |f(0)|)/2` and `b = (|f'(λ)| + ‖f''‖₁)/12`, since
  `√(1/λ) = 1/√λ` and `√(1/(3λ³)) = 1/(√3 λ^{3/2})`.

  **Minkowski's inequality is not needed.**  The card invokes it, but for these two weights the cross
  term is explicit: `∫_λ^∞ v^{-1/2} v^{-3/2} d*v = 1/(2λ²)`, and the whole content of Minkowski here is
  the single comparison `1/(2λ²) ≤ √(1/λ)·√(1/(3λ³))`, i.e. `√3 ≤ 2`.  So `(4)` follows from three
  explicit moments and one numerical inequality, with no `L^p` machinery at all.

Equations `(2)` and `(5)` are formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/PoissonSummationPiecewise.lean`.

The earlier note called this "a genuine obstacle": by `(6)` the leading term of `Ff` is
`f(lambda) sin(2 pi lambda y)/(pi y)`, so `Ff(y) = O(1/y)` and no better whenever `f(lambda) != 0`,
while mathlib's Poisson summation theorems require decay strictly faster than `1/y` on **both** sides.
That much is correct, and it is why no `HasSum` statement of `(5)` can exist.  What was wrong was the
conclusion that Dirichlet--Jordan is therefore needed.  The identity holds with the *conditional* part
reduced to two explicit numbers.  The route:

- **`sawPrimitive`**, `sawPrimitive_intCast`, `sawPrimitive_add_intCast`, `abs_sawPrimitive_le`,
  `measurable_sawPrimitive`, **`sawPrimitive_eq_neg_bernoulliHalf`** — the `1`-periodic primitive
  `({x} - {x}^2)/2` of the sawtooth.  It is continuous, unlike the sawtooth, and on each cell it is the
  local `B2` half already built for the Euler--Maclaurin step.
- **`hasSum_cos_div_sq`** — its cosine series
  `sum_(n>=1) cos(2 pi n x)/n^2 = 2 pi^2 (1/12 - sawPrimitive x)`, for **every** real `x`.  This is the
  `k = 1` case of mathlib's Bernoulli Fourier expansion, extended off `[0,1]` by periodicity.  Note the
  contrast with the sine series: the exponent `2` case of the *cosine* family is available precisely
  because it converges absolutely, whereas the sine family starts at exponent `3`.
- `intervalIntegrable_bdd_mul`, `intervalIntegrable_sawUnit_mul`, `intervalIntegrable_sawPrimitive_mul`
  — the two bounded kernels against an integrable factor.
- `sawUnit_eq_of_cell`, `em1_cell`, `em1_aux`, **`em1`** — **Euler--Maclaurin at arbitrary real
  endpoints**:

  ```text
  sum_(alpha < m <= beta) g(m)
    = g(beta) saw(beta) - g(alpha) saw(alpha) + int_alpha^beta g - int_alpha^beta saw(x) g'(x) dx.
  ```

  The two endpoint terms are what the truncated source needs: they are the jump contributions, and at
  integer endpoints they collapse to the trapezoid weights of the earlier integer-endpoint formula.
  The proof is one cell computation plus induction on `floor(beta) - floor(alpha)`.
- `em2_cell`, `em2_aux`, **`em2`** — the second integration by parts, trading the sawtooth remainder
  for `sawPrimitive`.  Because that kernel is continuous and periodic there is **no** interior boundary
  contribution, so the cell induction has nothing to cancel.
- **`tendsto_sum_sawtoothSine_of_ne`**, `sawWave_add_int_mul_two_pi` — the *value* of the sawtooth sine
  series at every angle off the lattice.  The corpus already had convergence and the bound `(7)`; the
  substitution `theta = 2 pi b/u` needs the value.
- **`integral_mul_cos_twice_ibp_gen`** — `(6)` with both endpoints free and the hypotheses localised to
  `[a,b]`, which is what a two-sided source requires.
- **`hasSum_integral_cos_div_sq`** — the remainder interchange.  Absolutely convergent, dominated by
  `||w||/n^2`, so it is an unconditional `HasSum`.
- **`em_dilated`** — the arithmetic side assembled: the lattice sum of `h` over `u Z` inside `[a,b]`
  equals `u^(-1) int f`, the two endpoint sawtooth terms, and a remainder against `sawPrimitive`.
- **`tendsto_sum_endpointSine`** (conditional half), **`hasSum_endpointCos`** (absolute half),
  **`cosTransform_term`** (the term identity) — the three pieces of the Fourier side.  The term
  identity is the observation that makes the whole thing work: the `n`-th transform sample, expanded by
  `(6)` and multiplied by `2/u`, splits **exactly** into one sawtooth-sine term and one `1/n^2` term.
- **`tendsto_sum_cosTransform`** — equation `(5)`:

  ```text
  sum_(m in Z) f(mu) - u^(-1) int f
    = lim_(N -> oo) sum_(n=1)^N (2/u) int_a^b h(t) cos(2 pi t n/u) dt.
  ```

  The hypotheses `a/u not in Z`, `b/u not in Z` are exactly the card's "for almost every `v`": no
  lattice point sits on an endpoint, which is where the periodisation jumps.
- `sum_Ioc_symm`, **`tendsto_poissonHalfSum`** — equation `(2)` itself, for an even source of total
  integral zero:

  ```text
  sqrt(u) sum_(m>=1) f(mu) = (1/sqrt u) sum_(n>=1) Ff(n/u) - sqrt(u) f(0)/2,
  ```

  which with `u = 1/v` is the card's `E(f)(1/v) = sqrt(v) sum_(n>=1) Ff(nv) - f(0)/(2 sqrt v)`.  The
  zero mode drops out through `(1)` and the `f(0)/2` is the folding of the two-sided lattice window
  onto its positive half.

Two by-products of this route are worth recording.  First, the sawtooth-subtraction decomposition
sketched earlier — periodise, subtract sawtooth translates, apply `hasSum_fourier_of_periodic_two` —
turned out to be unnecessary: doing Euler--Maclaurin *first* leaves the jump as two explicit numbers
rather than as a function that must be corrected.  `PeriodicFourierDecay.lean` stands on its own as the
absolutely convergent Fourier-series theorem mathlib lacks, but `(2)` does not use it.  Second, the
first-order and second-order Euler--Maclaurin formulas are both needed, and for different reasons: the
first order produces the endpoint jump terms, the second order makes the remainder absolutely
convergent.  A proof using only one of them cannot close `(5)`.

Equations `(9)`, `(10)`, `(11)` are formalized in
`formal/GaloisForLFunctions/RHTower/CCMTwoModeDeficitScale.lean`:

- `twoModeSource`, **`twoModeSource_eq_of_eigen`** — equation `(10)`, as an exact identity with no
  asymptotics: under the eigen-relation `l_j = c_j e_j(0)` the value at the origin of the normalised
  combination `(9)` is `l0 l1 (c1 - c0)/(c0 c1 sqrt(l0^2 + l1^2))`.  What matters is that the
  **difference** of the two eigenvalues appears, and that is exactly the first-order cancellation the
  zero-integral normalisation creates.
- **`tendsto_one_of_tendsto_deficit`** — a vanishing concentration deficit `d = 1 - c^2` forces
  `c -> 1`; this is the step that turns the card's deficit hypotheses into eigenvalue limits.
- **`deficitScale_const`** — the closed evaluation of the limiting constant.  Writing
  `s = 2^(1/4)` so that `s^4 = 2`, the two limits give `l0 l1 -> sqrt 3/2` and
  `l0^2 + l1^2 -> 11/(4 s^2)`, hence `sqrt(l0^2+l1^2) -> sqrt 11/(2 s)`, and the product with the gap
  factor `-1/2` is `-s sqrt 3/(2 sqrt 11) = -2^{-3/4} sqrt(3/11)`.
- **`tendsto_twoModeSource_div_deficit`** — equation `(11)`.  The fixed-mode asymptotics enter as
  explicit `Tendsto` hypotheses, exactly as the card imports them; the conclusion is unconditional
  given them.  The content of the statement is the *scale*: the ratio to `d1` has a finite nonzero
  limit, so the zero-mode Poisson correction of `(2)` is of concentration-deficit order and not of
  square-root-leakage order.

The asymptotics themselves belong to `constrained-prolate-two-mode-ground-state.md` and are not
reproved here.

## Gates

- [x] exact positive-half Poisson correction proved
- [x] endpoint-oscillation arithmetic-tail bound proved
- [x] CCM central correction shown to be deficit-scale
- [x] Lean: sawtooth sine series identity proved (absent from mathlib: conditional convergence)
- [x] Lean: uniform bound `(7)` unconditional, for every angle off the lattice
- [x] Lean: absolutely convergent Fourier series for periodic `C²` functions (absent from mathlib)
- [x] Lean: pointwise Fourier inversion for periodic `C²` functions
- [x] Lean: general-integrand Euler--Maclaurin sawtooth cell step (corpus had only the zeta case)
- [x] Lean: Euler--Maclaurin at arbitrary real endpoints, both orders (absent from mathlib)
- [x] Lean: cosine series of the periodic `B2` primitive at every real argument
- [x] Lean: Poisson summation at `Ff(y) = O(1/y)` regularity `(5)`, unconditional
- [x] Lean: the positive-half `E(f)` form `(2)` for an even zero-integral source
- [x] Lean: twice-integrated endpoint Fourier formula `(6)` unconditional
- [x] Lean: even/odd reduction of the Fourier transform to the endpoint half-interval
- [x] Lean: Fourier-side endpoint tail convergence and the bound `(3)` unconditional
- [x] Lean: `L²(d*v)` bound `(4)` unconditional, without Minkowski
- [x] Lean: exact central-value identity `(10)` for the zero-integral two-mode source
- [x] Lean: deficit-scale limit `(11)` from the imported fixed-mode asymptotics
- [ ] fixed-mode endpoint-jet asymptotics at the required cofinal strength
- [ ] closed-Weil residual estimate relative to the constrained gap
- [ ] projective determinant transfer to `Xi`
