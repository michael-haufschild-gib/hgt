# Route E Beurling local-axiom firewall

- **ID:** `ROUTE-E-BEURLING-FIREWALL-001`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / SOURCE-CLASSIFICATION FIREWALL
- **Scientific status:** `[LITERATURE] [PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **RH used:** no
- **Computation used:** no
- **Lean status:** FULLY FORMALIZED.  Items 3, 4, 6 and 7 are formalized unconditionally, together
  with the sign transition `(BF7)` and the transition asymptotic `(BF8)` of item 5, the scalar
  renewal barrier `(BF9)` in both its power and its Mertens form, the Mellin identity `(BF16)`, the
  aperture failure `(BF14)` and the local-prefix nonrobustness law `(BF22)`.  See "Lean progress".

## Lean progress

`formal/GaloisForLFunctions/RHTower/BeurlingSystemGibbsGauge.lean` introduces the abstract layer
and closes two of the seven items:

- `structure BeurlingSystem` carries the prime labels and their norms with the single axiom
  `1 < labelNorm p`; the generalized integers are `Multiset Label`, the free commutative monoid,
  with `intNorm` multiplicative (`intNorm_add`), at least one (`one_le_intNorm`) and
  `intNorm_replicate` on prime powers.  `moebius` is the generalized Möbius function, with
  `moebius_cons_of_notMem` the sign flip used by the one-large-prime sector of `(BF4)`.
- **Item 3.**  `gibbsWeight_mul_le` is log-submodularity of `(BF2)` and `gibbsWeight_mul_lt` its
  strict form in transverse directions, which is the conditional two-prime Rayleigh law.  The proof
  is the card's: `(r-1)(s-1) ≥ 0` for the two transverse norm products.
- **Item 6.**  `log_labelNorm_div_log_intNorm_replicate` is `(BF10)`, `gammaGauge` is `(BF11)`, and
  `gammaGauge_mem_Icc_of_truncate` proves the gauge lies in `[1,2]` after deleting the labels of
  norm below two (`truncate`).

`formal/GaloisForLFunctions/RHTower/BeurlingSystemCounting.lean` supplies the analytic foundation:
`IsDiscrete`, the counting function `countBall`, the linear-growth predicate `HasLinearCounting`
extracted from `(BF1)`, and `summable_expNegNorm` — every exponential Gibbs sum over the
generalized integers converges absolutely, by grouping the integers into unit norm layers and
comparing with a geometric series.  This is the convergence input the card uses for `(BF4)`.

`#print axioms` on all of these: `propext`, `Classical.choice`, `Quot.sound` only.

`formal/GaloisForLFunctions/RHTower/BeurlingSystemDecomposition.lean` closes the decomposition half
of item 4:

- `largeCount` counts the labels above the cutoff, `gibbsTerm` is the Möbius-weighted exponential
  term, and `phi`, `apertureSum`, `oneLargeSum`, `higherLargeSum` are `Φ_P`, `A_{P,z}` and the two
  remaining sectors of `(BF3)`–`(BF4)`;
- `phi_eq_apertureSum_add` is the exact three-sector split;
- `oneLargeSum_eq_neg_tsum` is the substantive step: the one-large-label sector is reindexed by
  `g = p·m` — injectivity of `(p,m) ↦ p ::ₘ m`, surjectivity onto the sector via
  `exists_cons_of_largeCount_eq_one`, the Möbius sign flip, and Fubini — giving
  `-∑_{|p|>z} A_{P,z}(|p|x)`;
- `phi_eq_apertureSum_sub_tsum_add` is `(BF4)` itself.

`formal/GaloisForLFunctions/RHTower/BeurlingSystemTailBound.lean` proves the window estimate and
the structural half of the remainder bound:

- `HasCountingError κ C θ` is the two-sided `(BF1)`; `layerIndex` indexes the windows of width
  `1/x` above the threshold, and `layerIndex_bounds` is the window containment;
- `card_layer_le` bounds the population of one window by the counting increment, through the
  set-difference of two balls;
- `tsum_tail_le` is `(BF15)`: `∑_{|g| > T} e^{-x|g|} ≤ e^{-xT}((κ/x + 2CT^θ)·E + (2C/x)·E')` with
  the two explicit geometric constants `expGeomSum`, `expGeomLinSum`.  The card's subadditivity
  step is replaced by `rpow_add_le_of_one_le`, `(T+s)^θ ≤ T^θ + s`, which is what the endpoint
  needs;
- `sq_lt_intNorm_of_two_le_largeCount` is the structural fact behind `(BF6)`: two labels above the
  cutoff already force `|g| > z²`; `abs_higherLargeSum_le_tsum` turns the remainder into a tail
  sum, and `abs_higherLargeSum_le` combines the two into the bound at threshold `z²`.

The endpoint of `(BF6)` is in the same module: `mul_exp_neg_antitone` is the elementary
monotonicity `(y+1)e^{-y} ≤ (Y+1)e^{-Y}` (proved from `1 + t ≤ e^t`, with no derivatives),
`rpow_le_add_one` replaces `y^θ` by `y + 1`, `abs_higherLargeSum_le_explicit` gives the explicit
two-term bound under `(BF5)`, and `eventually_abs_higherLargeSum_le` is `(BF6)` itself:
`|R_{P,≥2,z}(x)| ≤ K x^{-1/2}` for all small `x`, with `K = κE + 2CE' + 1`.  Item 4 of the card is
therefore closed.

`formal/GaloisForLFunctions/RHTower/BeurlingSystemTransitionKernel.lean` closes `(BF7)`:

- `largeTail` is the prime sum of `(BF7)` and `transitionKernel` the kernel itself;
  `summable_largeTailTerm` gets convergence for every positive `t` by pushing the primes into the
  generalized integers along `p ↦ {p}`;
- `largeTail_strictAnti` is strict decrease, `continuousOn_largeTail` continuity on every
  `[a, ∞)` with `a > 0`, `tendsto_largeTail_atTop` the vanishing at infinity and
  `tendsto_largeTail_atZero` the blow-up at the origin when infinitely many primes lie above the
  cutoff;
- `exists_unique_transition` is the single transition itself — a unique `τ > 0` with
  `∑_{|p|>z} e^{-(|p|-1)τ} = 1` — and `transitionKernel_sign` is the sign pattern: negative below
  `τ`, positive above.

`formal/GaloisForLFunctions/RHTower/BeurlingSystemPrefixFirewall.lean` closes the local-prefix
nonrobustness theorem and supplies the algebraic input to `(BF16)`:

- `AgreesBelow`, `HasMoebiusDecay`, `IsSoundCertificate` and `IsPrefixNeighborhood` are the four
  notions of the theorem's statement, and
  `not_isPrefixNeighborhood_of_isSoundCertificate` is `(BF22)`: given that below every prescribed
  cutoff there is an agreeing system violating some strict-half decay exponent, no sound
  certificate class is a finite-prefix neighbourhood of the reference system.  The external
  existence input enters exactly as the card states it, as a hypothesis on the class;
  `hasMoebiusDecay_of_isPrefixNeighborhood` is the contrapositive reading.
- `sum_moebius_divisors` is the generalized Möbius identity `∑_{d ∣ g} μ_P(d) = [g = 1]` over the
  free label monoid, proved by matching the squarefree divisors with the subsets of the support and
  using the alternating powerset sum.  This is the algebraic input to the Dirichlet inversion
  `∑_g μ_P(g)|g|^{-s} = ζ_P(s)^{-1}` needed by `(BF16)`.

`formal/GaloisForLFunctions/RHTower/BeurlingSystemZetaSeries.lean` starts the Dirichlet layer of
item 7:

- `dyadicIndex` blocks the generalized integers by `2^k ≤ |g| < 2^{k+1}`, and
  `summable_intNorm_rpow` proves `∑_g |g|^{-s} < ∞` for every real `s > 1`.  The dyadic block
  carries at most `N(2^{k+1}) ≤ C·2^{k+1}` integers of weight at most `2^{-ks}`, so the series is
  geometric with ratio `2^{1-s}`; no Abel summation is needed, only the cumulative counting bound;
- `zetaSeries`, `moebiusSeries`, `summable_moebiusTerm` and `zetaSeries_pos` set up the two
  Dirichlet series and their basic properties;
- `divisorPairEquiv` identifies the ordered factorizations `d + e = n` with the divisors of `n`,
  and `moebiusSeries_mul_zetaSeries` is the Dirichlet inversion
  `(∑_g μ_P(g)|g|^{-s}) · (∑_g |g|^{-s}) = 1` for every real `s > 1`: expand the product over
  pairs, regroup by `n = d + e` through the sigma-fibre equivalence, and evaluate each fibre with
  `sum_moebius_divisors`.  This is the algebraic half of `(BF16)`.

`formal/GaloisForLFunctions/RHTower/BeurlingSystemMellin.lean` proves `(BF16)`:

- `countable_of_isDiscrete` — a discrete system has countably many generalized integers, since the
  balls exhaust it;
- `mellin_phi` — for `Re s > 1`,
  `mellin (fun x => Φ_P(x)) s = Γ(s) · ∑_g μ_P(g)|g|^{-s}`.  The termwise interchange is the
  mathlib lemma `hasSum_mellin`, whose four hypotheses are supplied by the positivity of the
  norms, the exponential-sum `HasSum` of `Φ_P` and the absolute convergence of the Möbius series.
- `zetaSeriesC`, `moebiusSeriesC`, `summable_intNorm_cpow`, `summable_moebius_cpow` carry the two
  Dirichlet series to complex exponents, `moebiusSeriesC_mul_zetaSeriesC` is the complex Dirichlet
  inversion, `zetaSeriesC_ne_zero` its immediate consequence, and `mellin_phi_eq_gamma_div` is
  `(BF16)` in the displayed form `mellin Φ_P s = Γ(s)/ζ_P(s)` for `Re s > 1`;
- `continuousOn_phi_Ioi` and `abs_phi_le` are the two analytic inputs about `Φ_P`: continuity on
  the open half-line, and the exponential bound `|Φ_P(x)| ≤ e^{-x/2} ∑_g e^{-|g|/2}` for `x ≥ 1`;
- `not_isBigO_rpow_of_continuation_eq_zero` is item 7, the strict-half failure `(BF13)`.  Given a
  continuation `Z` of the zeta series, holomorphic right of `a` and vanishing at some `ρ` with
  `Re ρ > a`, the assumed `O(x^{-a})` decay would make `mellin Φ_P` holomorphic on that half-plane;
  `mellin Φ_P · Z` then agrees with `Γ` on the Euler chamber, so by the identity theorem on the
  (convex, hence preconnected) half-plane they agree at `ρ`, forcing `Γ(ρ) = 0` — impossible.  The
  continuation and its zero enter exactly as the card has them, from the external construction;
- `not_aperture_decay_of_continuation_eq_zero` is `(BF14)`: on any schedule satisfying `(BF5)`, a
  strict-half decay bound for the zero/one-large-prime difference would, through `(BF4)` and
  `(BF6)`, force one for `Φ_P` itself, which the previous theorem forbids.  The comparison
  `x^{-1/2} ≤ x^{-a}` for `x ≤ 1` is where `a > 1/2` is used, exactly as on the card.

`formal/GaloisForLFunctions/RHTower/BeurlingSystemPartialSummation.lean` builds the Abel bridge
that the PNT-consuming statements need:

- `primeCount` and `primeCountLt` are the two prime counting functions, `HasPrimePNT` is the
  generalized prime number theorem `π_P(X) log X / X → 1`, and `finite_primeBall` is finiteness:
  the labels inject into the generalized integers by `p ↦ {p}`, so discreteness of the integers
  transfers to the primes;
- `sum_labelNorm_weight` is partial summation over an arbitrary finite family of labels:
  `f(|p|) - f(Y)` is the integral of `f'` against the indicator of `{t ≤ |p|}` (mathlib's
  `intervalIntegral.integral_indicator`), and exchanging the finite sum with the integral turns the
  weight into the counting function of the family from above;
- `countGe_primeWindow` identifies that weight with `π_P(X) - π_P^<(t)` by splitting the ball at
  an interior height, `integral_mul_primeCountLt_eq` replaces the strict counting function by the
  non-strict one (they differ only on the finite set of prime norms below `X`, which is null), and
  `sum_primeWindow_eq_sub_sub_integral` is the Abel identity

  ```text
  ∑_{Y < |p| ≤ X} f(|p|) = π_P(X) f(X) - π_P(Y) f(Y) - ∫_Y^X f'(t) π_P(t) dt.
  ```

`formal/GaloisForLFunctions/HTGeometry/LogWeightedRpowIntegral.lean` gains
`tendsto_logKernelRemainder`: a vanishing weight integrated against any kernel dominated by
`C·t^(a-1)/log t` contributes `o(x^a/log x)`.  Splitting at a height where `|g| ≤ δ` bounds the
tail by `Cδ` times the logarithmic power integral, whose normalization tends to one.

`formal/GaloisForLFunctions/RHTower/BeurlingSystemPrimeSumAsymptotic.lean` and
`.../BeurlingSystemMertensWindow.lean` close `(BF9)` in both of its forms:

- `pntError` is the relative PNT error `E`, `primeCount_eq_mul` is the exact factorization
  `π_P(t) = (t/log t)(1 + E(t))`, `tendsto_pntError` is `E → 0`, and `integrableOn_pntError` is
  local integrability, from monotone measurability and the crude bound `π_P(t) log t / t ≤
  π_P(x) log x / 2` on `[2,x]`;
- `primeRpowSum_eq` is Abel summation for the weight `t^(a-1)`, splitting the sum into a boundary
  term, `(a-1)` times the logarithmic power integral, and an `E`-weighted remainder, and
  `tendsto_primeRpowSum` is the power form of `(BF9)`: for every `a > 0`

  ```text
  ∑_{2 < |p| ≤ X} |p|^(a-1) ∼ X^a/(a log X);
  ```

  the boundary term contributes `a`, the logarithmic power integral `a-1`, and the remainder
  vanishes by `tendsto_logKernelRemainder` with the kernel taken to be the bound itself;
- `primeInvWindowSum_eq` is Abel summation for the reciprocal weight, `integral_invDivLog` is the
  iterated-logarithm primitive, `log_log_rpow_sub` evaluates it on the window, and
  `tendsto_primeInvWindowSum` is the Mertens form of `(BF9)`: for every `u > 1`

  ```text
  ∑_{X^{1/u} < |p| ≤ X} |p|^{-1} → log u.
  ```

  Both boundary terms vanish because `π_P(t)/t → 0` (`tendsto_primeCount_div`), the main term is
  the exact constant `log log X - log log X^{1/u} = log u`, and the remainder is bounded by the
  same iterated logarithm times a vanishing factor.

`#print axioms` on all of these: `propext`, `Classical.choice`, `Quot.sound` only.

`formal/GaloisForLFunctions/RHTower/BeurlingSystemTransitionAsymptotic.lean` closes `(BF8)`:

- `eventually_primeCount_le`, `eventually_le_primeCount` and `eventually_primeCount_le_two_mul` are
  the two-sided counting bounds the prime number theorem provides;
- `integral_linear_exp` evaluates the exponential moment of the linear weight through the explicit
  primitive `-(u/t + 1/t²)e^{-(u-1)t}`, and `sum_primeWindow_exp_le` runs Abel summation on a
  window: bounding `π_P` by `2u` gives

  ```text
  ∑_{z < |p| ≤ X} e^{-(|p|-1)t} ≤ 2(z + 1/t)e^{-(z-1)t} + π_P(X)e^{-(X-1)t};
  ```

- `largeTail_le` passes to the whole tail.  Every finite subfamily sits inside some window, and the
  boundary term `π_P(X)e^{-(X-1)t}` vanishes as `X → ∞`, so the window bound survives the limit
  and bounds every partial sum; `Real.tsum_le_of_sum_le` then bounds the tsum itself;
- `le_largeTail` is the matching lower bound from a single window: every label of `(z, Y]`
  contributes at least `e^{-(Y-1)t}`, so the tail is at least `(π_P(Y) - π_P(z))e^{-(Y-1)t}`;
- `tendsto_largeTailBound` evaluates the upper bound at `t = c log z / z` as
  `2 z^{1-c}(1 + 1/(c log z))e^{c log z/z}`, which vanishes for `c > 1`, and
  `tendsto_primeCountWindow` is the window count `(π_P(Kz) - π_P(z)) log z / z → K - 1`, proved by
  factoring `π_P(Kz) log z / z` as `(π_P(Kz) log(Kz)/(Kz)) · K · (log z / log(Kz))`.  With `K`
  chosen between `1` and `1/c` the lower bound is `((K-1)/2) z^{1-cK}/log z`, which diverges;
- `eventually_largeTail_lt_one` and `eventually_one_lt_largeTail` are the two regimes, and
  `nonempty_largeLabel` derives from the prime number theorem that arbitrarily large generalized
  primes exist — a bounded prime set would force `π_P(y) log y / y → 0`;
- `tendsto_transition_ratio` is `(BF8)`.  For every `τ` with `τ_z > 0` and `L(z, τ_z) = 1`, strict
  antitonicity of the tail turns the two regimes into `(1-ε) log z / z < τ_z < (1+ε) log z / z`,
  which is `z τ_z / log z → 1`.

`#print axioms` on all of these: `propext`, `Classical.choice`, `Quot.sound` only.

All seven items of the card are now formalized.

(The card's `(BF22)` is closed; see above.)

The Diamond–Montgomery–Vorhauer and Zhang existence constructions are external inputs; formalizing
them is a separate long project, and the items above are all stated for an arbitrary system
satisfying the card's axioms, so they are unconditional theorems in Lean.

## Exact claim

There is a discrete Beurling prime system \(\mathcal P\), with free commutative generalized-integer
monoid \(\mathcal G_{\mathcal P}\), multiplicative norm \(|\cdot|\), generalized Möbius function
\(\mu_{\mathcal P}\), and zeta function \(\zeta_{\mathcal P}\), for which all of the following hold.

1. For some \(1/2<\theta<1\) and \(\kappa>0\),

   \[
   N_{\mathcal P}(X)=\#\{g\in\mathcal G_{\mathcal P}:|g|\le X\}
   =\kappa X+O(X^\theta),
   \tag{BF1}
   \]

   and the generalized primes obey a PNT with a de la Vallée Poussin-scale remainder.

2. \(\zeta_{\mathcal P}\) has infinitely many zeros \(\rho\) with
   \(\Re\rho>1/2\).

3. Every finite squarefree exponential-Gibbs table

   \[
   w_x(S)=\exp\!\left(-x\prod_{p\in S}|p|\right)
   \tag{BF2}
   \]

   is strictly log-submodular in every genuinely transverse pair of set directions.  In
   particular every conditional two-prime table is strictly Rayleigh.

4. With

   \[
   \Phi_{\mathcal P}(x)
    =\sum_{g\in\mathcal G_{\mathcal P}}\mu_{\mathcal P}(g)e^{-x|g|},
   \qquad
   A_{\mathcal P,z}(x)
    =\sum_{\substack{g\in\mathcal G_{\mathcal P}\\p\mid g\Rightarrow |p|\le z}}
       \mu_{\mathcal P}(g)e^{-x|g|},
   \tag{BF3}
   \]

   unique factorization gives the exact zero/one-large-prime decomposition

   \[
   \Phi_{\mathcal P}(x)
   =A_{\mathcal P,z}(x)
    -\sum_{|p|>z}A_{\mathcal P,z}(|p|x)
    +R_{\mathcal P,\ge2,z}(x).
   \tag{BF4}
   \]

   If \(0<x\le x_0\) and

   \[
   xz^2\ge \tfrac12\log(1/x),
   \tag{BF5}
   \]

   then

   \[
   |R_{\mathcal P,\ge2,z}(x)|=O(x^{-1/2}).
   \tag{BF6}
   \]

5. The one-large-prime kernel

   \[
   K_{\mathcal P,z}(t)
   =e^{-t}\left(1-\sum_{|p|>z}e^{-(|p|-1)t}\right)
   \tag{BF7}
   \]

   has exactly one sign transition \(\tau_{\mathcal P,z}\), and

   \[
   \frac{z\tau_{\mathcal P,z}}{\log z}\longrightarrow1.
   \tag{BF8}
   \]

   For fixed \(1<u<2\), \(Y=X^{1/u}\), its positive scalar renewal norm has the same barrier

   \[
   \sum_{Y<|p|\le X}|p|^{-\alpha}
   \sim\frac{X^{1-\alpha}}{(1-\alpha)\log X}\quad(0\le\alpha<1),
   \qquad
   \sum_{Y<|p|\le X}|p|^{-1}=\log u+o(1).
   \tag{BF9}
   \]

6. The divided-log prime-power completion is still exact:

   \[
   \frac{\Lambda_{\mathcal P}(p^k)}{\log|p^k|}=\frac1k,
   \tag{BF10}
   \]

   and its critical depth-zero Gamma gauge is

   \[
   \frac1{1-|p|^{-1}}.
   \tag{BF11}
   \]

   After deleting finitely many initial generalized primes, without changing any zero or
   asymptotic assertion, this gauge lies in \([1,2]\).

7. Nevertheless, for every zero \(\rho\) from item 2 and every
   \(a\) with

   \[
   \max(\theta,\tfrac12)<a<\Re\rho,
   \tag{BF12}
   \]

   neither

   \[
   \Phi_{\mathcal P}(x)=O(x^{-a})
   \tag{BF13}
   \]

   nor

   \[
   A_{\mathcal P,z(x)}(x)
   -\sum_{|p|>z(x)}A_{\mathcal P,z(x)}(|p|x)=O(x^{-a})
   \tag{BF14}
   \]

   can hold as \(x\downarrow0\) on any schedule satisfying `(BF5)`.

Consequently strict Rayleigh/log-submodular finite Gibbs geometry, generalized unique
factorization, PNT-quality prime distribution, the critical zero/one seam, the scalar-renewal
barrier, the divided-log Gamma/co-Poisson completion, and bounded depth-zero Gamma recovery do
**not** imply the Route E source estimate.  Any universal proof from only those inputs is false.

## External existence input

Diamond--Montgomery--Vorhauer prove that, for every \(1/2<\theta<1\) and suitable \(a>0\), there
is a **discrete** Beurling prime system satisfying `(BF1)`, with \(\zeta_{\mathcal P}\) analytic
on \(\Re s\ge\theta\) apart from its simple pole at \(1\), and with infinitely many zeros on

\[
\Re s=1-\frac{a}{\log|\Im s|}.
\]

They also prove

\[
\psi_{\mathcal P}(X)
=X+O\!\left(Xe^{-2\sqrt{a\log X}}\right).
\]

Thus the system supplies items 1--2, with strict-right zeros arbitrarily close to \(1\).

Primary source:

- H. G. Diamond, H. L. Montgomery, and U. M. A. Vorhauer,
  *Beurling primes with large oscillation*, Math. Ann. **334** (2006), 1--36,
  Theorem 1, DOI `10.1007/s00208-005-0638-2`.

The source explicitly notes that additive structure of the ordinary integers is what permits
zero-free information beyond the Beurling axioms used in its construction.

## Critical-normalization sharpening

`[PAPER-PROVED BRIDGE; NOVELTY UNVERIFIED]` The preceding firewall can be made strictly sharper
at the generalized-integer counting boundary.  For every prescribed integer cutoff \(R\), there
is a discrete Beurling system \(\mathcal P_R\) such that

\[
\mathcal P_R\cap[1,R]
=\{p\le R:p\text{ is an ordinary rational prime}\},
\tag{BF17}
\]

\[
N_{\mathcal P_R}(X)
=X+O\!\left(
 X^{1/2}\exp\{c(\log X)^{2/3}\}
\right),
\tag{BF18}
\]

and \(\zeta_{\mathcal P_R}\) is analytic on \(\Re s>1/2\), apart from its simple pole at \(1\),
but has infinitely many zeros on

\[
\Re s=1-\frac1{\log|\Im s|}.
\tag{BF19}
\]

Moreover every generalized prime belongs to the dyadic rational mesh

\[
\left\{n+\frac{\ell}{2^n}:n\ge0,\ 0\le\ell<2^n\right\}.
\tag{BF20}
\]

These are Wen-Bin Zhang's Theorem 2.  Theorem 2 states that its system has properties
(i)--(iii) of Theorem 1 and then replaces the RH conclusion by `(BF19)` and the sharp
de la Vallée Poussin oscillation law.  In particular `(BF17)` is available with \(R\) chosen
arbitrarily large before the system is constructed.

Primary source:

- W.-B. Zhang, *Normalization of Beurling generalized primes with Riemann hypothesis*,
  Ann. Univ. Sci. Budapest. Sect. Comput. **39** (2013), 459--469, Theorem 2,
  DOI `10.71352/ac.39.459`.

This system satisfies every conclusion `(BF2)`--`(BF11)`.  Indeed, for each fixed
\(\delta>0\),

\[
\exp\{c(\log X)^{2/3}\}=O_\delta(X^\delta),
\]

so `(BF18)` implies `(BF1)` with \(\kappa=1\) and any
\(\theta=1/2+\delta<1\).  The already-proved higher-large-prime estimate therefore applies
unchanged.  Zhang's prime error gives the PNT inputs used in `(BF8)`--`(BF9)`, while the free
prime-label monoid gives the finite Gibbs, zero/one-sector, and divided-log identities.

The strict-half failure is now stronger than item 7.  If \(\rho\) is a zero in `(BF19)`, then
for **every**

\[
\frac12<a<\Re\rho,
\tag{BF21}
\]

neither `(BF13)` nor `(BF14)` can hold.  The proof of `(BF13)` from `(BF16)` uses only the
assumed \(O(x^{-a})\) behavior at zero and exponential decay at infinity; it does not require
\(a>\theta\).  The deduction from `(BF14)` uses `(BF6)` and \(a>1/2\).  Thus `(BF21)` follows.

Consequently Route E cannot be obtained from the earlier local package even after adjoining all
three of the following:

```text
near-critical generalized-integer rigidity
  N_P(X)=X+X^(1/2+o(1));
analytic continuation of zeta_P through the full strict right half-plane;
agreement with ordinary rational primes below an arbitrarily prescribed finite aperture.
```

This is a genuine strengthening of the source classification.  A successful ordinary-integer
source must be discontinuously sensitive to the exact infinite additive lattice (or an equivalent
all-scale self-duality); no finite prime prefix, \(X^{1/2+o(1)}\) counting error, or strict-half
analytic continuation can supply the missing Wold-breadth orientation.

## Paper proof

### Finite Gibbs geometry

Let \(A,B\) be finite prime-label sets.  Write

\[
c=\prod_{p\in A\cap B}|p|,\qquad
r=\prod_{p\in A\setminus B}|p|,\qquad
s=\prod_{p\in B\setminus A}|p|.
\]

Every generalized prime norm is \(>1\), so

\[
rs+1-r-s=(r-1)(s-1)\ge0.
\]

Therefore

\[
w_x(A\cup B)w_x(A\cap B)
=e^{-xc(rs+1)}
\le e^{-xc(r+s)}
=w_x(A)w_x(B).
\]

The inequality is strict when both set differences are nonempty.  Taking each difference to be
one prime gives the conditional two-prime Rayleigh law.  No discreteness, additive structure, or
zero-free input occurs.

### Exact zero/one decomposition

The Beurling generalized integers are the free commutative monoid on the generalized-prime
labels.  Every squarefree \(g\) therefore contains exactly zero, one, or at least two labels with
norm \(>z\).  The zero sector is \(A_{\mathcal P,z}(x)\).  In the one sector write uniquely
\(g=pm\), where \(|p|>z\) and every prime label of \(m\) has norm at most \(z\).  Then
\(\mu_{\mathcal P}(pm)=-\mu_{\mathcal P}(m)\), giving the second term of `(BF4)`.  The remaining
sector is \(R_{\mathcal P,\ge2,z}\).  Absolute convergence follows from `(BF1)`.

### Critical higher-large-prime remainder

Every generalized integer in the remainder has norm \(>z^2\).  Put

\[
S_{\mathcal P}(T,x)=\sum_{|g|>T}e^{-x|g|}.
\]

Partition \((T,\infty)\) into intervals of length \(1/x\).  From `(BF1)`, for a constant \(C\),

\[
\begin{aligned}
N_{\mathcal P}(T+(j+1)/x)-N_{\mathcal P}(T+j/x)
\le{}&\kappa/x\\
&+C\bigl((T+(j+1)/x)^\theta+(T+j/x)^\theta\bigr).
\end{aligned}
\]

Multiplying by \(e^{-xT-j}\), summing over \(j\ge0\), and using
\((r+s)^\theta\le r^\theta+s^\theta\) for \(0<\theta<1\), gives

\[
S_{\mathcal P}(T,x)
\ll e^{-xT}\bigl(x^{-1}+T^\theta+x^{-\theta}\bigr).
\tag{BF15}
\]

Take \(T=z^2\).  Under `(BF5)`, \(e^{-xT}\le x^{1/2}\).  The first term in `(BF15)` is
\(x^{-1/2}\).  Put \(y=xT\).  Once \(x\) is small, `(BF5)` gives
\(y\ge\frac12\log(1/x)>\theta\), and \(y^\theta e^{-y}\) is decreasing there.  Hence, since
\(\theta<1\),

\[
e^{-xT}T^\theta
=x^{-\theta}e^{-y}y^\theta
\ll x^{1/2-\theta}\log(1/x)^\theta
=O(x^{-1/2}),
\qquad
e^{-xT}x^{-\theta}\le x^{1/2-\theta}=O(x^{-1/2}).
\]

This proves `(BF6)`.

### Transition and scalar-renewal laws

For fixed \(z\), the prime sum in `(BF7)` converges for every \(t>0\), strictly decreases from
\(+\infty\) to \(0\), and hence crosses \(1\) exactly once.  PNT partial summation gives, uniformly
for fixed \(c>0\),

\[
\sum_{|p|>z}e^{-(|p|-1)c\log z/z}
=z^{1-c+o(1)}.
\]

For every \(c<1\) this tends to \(+\infty\); for every \(c>1\) it tends to \(0\).  Monotonicity
then proves `(BF8)`.  The same PNT and ordinary partial summation give `(BF9)`.

### Gamma completion

The generalized von Mangoldt function has value \(\log|p|\) on \(p^k\), while
\(\log|p^k|=k\log|p|\).  This proves `(BF10)`.  Formula `(BF11)` is the same depth-zero
half-density/Gamma quotient as for rational primes.  Removing finitely many labels only
multiplies the zeta function by a finite nonvanishing Euler factor on \(\Re s>0\), so it preserves
all strict-right zeros and asymptotic conclusions; after doing so every remaining norm is at least
\(2\), and `(BF11)` lies in \([1,2]\).

### Strict-half failure

For \(\Re s>1\), absolute convergence and termwise Mellin transformation give

\[
\int_0^\infty\Phi_{\mathcal P}(x)x^{s-1}\,dx
=\Gamma(s)\sum_g\frac{\mu_{\mathcal P}(g)}{|g|^s}
=\frac{\Gamma(s)}{\zeta_{\mathcal P}(s)}.
\tag{BF16}
\]

Fix a zero \(\rho\) and \(a\) as in `(BF12)`.  If `(BF13)` held, the left side of `(BF16)` would
define a holomorphic function on \(\Re s>a\): the assumed bound handles \(x\downarrow0\), while
`(BF1)` gives exponential decay at \(+\infty\).  On \(\Re s>1\) it equals
\(\Gamma/\zeta_{\mathcal P}\), so analytic continuation would make that quotient holomorphic at
\(\rho\).  This is impossible because Gamma has no zeros and \(\zeta_{\mathcal P}(\rho)=0\).
Thus `(BF13)` fails.

By `(BF4)` and `(BF6)`, `(BF14)` would imply `(BF13)`, because \(a>1/2\).  Therefore `(BF14)`
also fails.

This closes all seven items.

## Hostile audit

1. **Not an RH proof.**  The theorem constructs a countermodel to a source axiom set.
2. **Not a new Beurling construction.**  Discrete system and its zeros are exactly
   Diamond--Montgomery--Vorhauer's theorem.
3. **Not merely “Beurling systems differ.”**  Items 3--6 verify, one by one, that the exact local,
   critical-aperture, renewal, and Gamma mechanisms currently retained by Route E survive in the
   countermodel.
4. **No functional-equation claim.**  The countermodel is not asserted to carry the Riemann
   functional equation.  That absence is the point: functional-equation/archimedean data remain a
   possible ordinary-integer-specific source.
5. **No additive-lattice claim.**  Generalized norms are real and need not form the ordinary
   additive lattice.  Therefore additive Fourier structure also remains a possible discriminator.
6. **No overclaim of novelty.**  The local-axiom firewall appears absent from the searched
   literature, but it is an elementary synthesis over a known Beurling construction.  It remains
   `[BRIDGE] [NOVELTY UNVERIFIED]`, not candidate new scientific knowledge.

## Exact representation lesson

The surviving depth-zero source cannot be a theorem of:

```text
free prime-factor monoid
+ PNT-quality prime counting
+ finite Gibbs log-submodularity/Rayleigh geometry
+ zero/one critical aperture
+ scalar prime renewal
+ divided-log Gamma prime-power completion
+ bounded depth-zero Gamma gauge.
```

That package has a strict-right-zero model.  A successful Route E source must use at least one
structure not preserved by this firewall.  Current exact candidates are:

1. ordinary additive lattice and its distinguished character \(n\mapsto e^{int}\);
2. archimedean functional equation/co-Poisson reflection tied to that lattice;
3. an equivalent global invariant that rules out the Diamond--Montgomery--Vorhauer system before
   the desired Möbius estimate is invoked.

Merely naming “integer-specific arithmetic” is not a source theorem.  Next conjecture must exhibit
one exact discriminator and derive a quantitative orientation from it.

## Local-prefix nonrobustness theorem

`[PAPER-PROVED BRIDGE; NOVELTY UNVERIFIED]`  The Zhang sharpening has a topology-free
formulation which removes a remaining ambiguity in “cofinal continuity.”  Let \(\mathscr B\) be
any class of discrete Beurling systems containing the ordinary primes \(\mathcal P_0\) and all
systems supplied by `(BF17)`--`(BF20)`.  Give \(\mathscr B\) the finite-prefix topology: a basic
neighborhood of \(\mathcal P_0\) prescribes agreement with the rational primes below one finite
cutoff.

Let \(\mathcal C\subseteq\mathscr B\) be any certificate class with the soundness property

\[
\mathcal P\in\mathcal C
\quad\Longrightarrow\quad
\Phi_{\mathcal P}(x)=O_{\mathcal P,\varepsilon}
  (x^{-1/2-\varepsilon})
\quad\text{for every }\varepsilon>0.
\tag{BF22}
\]

Then \(\mathcal C\) cannot both contain \(\mathcal P_0\) and be a neighborhood of
\(\mathcal P_0\).  Equivalently, no sound Route E certificate which is stable under sufficiently
long finite-prime-prefix agreement can certify the ordinary primes.

The proof is one line but the quantifiers matter.  If \(\mathcal C\) contained a basic
neighborhood of \(\mathcal P_0\), choose its cutoff \(R\).  Zhang's system
\(\mathcal P_R\) lies in that neighborhood by `(BF17)`, hence in \(\mathcal C\).  Soundness
would give `(BF13)` for every \(a=1/2+\varepsilon\), contradicting `(BF21)` at any zero
\(\rho\) with \(1/2<a<\Re\rho\).

This does **not** say that pointwise finite-aperture formulas are useless, nor does it assume RH
for \(\mathcal P_0\).  It says that a successful certificate at \(\mathcal P_0\) cannot have an
open, uniform margin in finite-prefix topology.  Its admission step must be tail-singular:
exact all-scale additive lattice structure, exact co-Poisson self-duality, or another
non-open invariant must enter before the strict-half estimate.  Pointwise convergence at each
fixed physical scale is insufficient; required nonuniformity is in the joint
prime-aperture/critical-scale limit.

Hostile novelty audit found literature on Beurling zero distributions and on Zhang's
normalization theorem, but no statement of `(BF22)` as a source-certificate nonrobustness law.
The construction is external and the deduction elementary, so status remains
`[BRIDGE] [NOVELTY UNVERIFIED]`, not independent new construction.
