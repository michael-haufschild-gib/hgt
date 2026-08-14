# Every strictly positive informative binary-tree channel has an HT homogeneous BP clock

- **ID:** `asymmetric-binary-tree-channel-rg-clock-hypertranscendence`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / TRANSFER-CHANNEL UNIVERSALITY
- **Scientific status:** `[PROVED HERE] [PARENT-DERIVED CLASSIFICATION]`
  `[ASYMMETRIC BINARY CHANNEL] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[FORMULA-LEVEL NOVELTY SEARCH PASSED PROVISIONALLY] [SPECIALIST AUDIT OPEN]`
  `[NOT A QUANTUM OR CONTINUUM-QFT THEOREM]`
- **Scope:** general hypertranscendence in exact tree inference and scale generation; no RH or
  distinguished-special-function input
- **Statement:** Let a strictly positive, positively informative binary channel be copied on every
  edge of a regular `p`-ary tree, `p>=2`.  On the exact homogeneous likelihood-message submanifold,
  its belief-propagation recursion has a hypertranscendental exact message-to-depth beta and clock
  in every locally invertible DA message scheme.  This holds for every channel asymmetry and every
  nonzero information strength.  The proof uses strict channel positivity to produce the
  non-superattracting real basin that excludes every Ritt-integrable rational map.

## Channel and exact homogeneous recursion

Write the row-stochastic binary channel as

```text
P(+|+)=alpha,       P(-|+)=1-alpha,
P(+|-)=gamma,       P(-|-)=1-gamma,                            (1)
```

and assume

```text
0 < gamma < alpha < 1.                                          (2)
```

Thus all four transition probabilities are positive and the child is positively informative about
the parent.  Put

```text
u=2 alpha-1,             v=2 gamma-1,
-1 < v < u < 1.                                                   (3)
```

Parameterize an incoming child likelihood message by `y in [-1,1]`:

```text
mu_y(t)=(1+t y)/2,             t in {+1,-1}.                    (4)
```

One branch contributes parent likelihoods

```text
w_+(y)=sum_t P(t|+) mu_y(t)=(1+u y)/2,
w_-(y)=sum_t P(t|-) mu_y(t)=(1+v y)/2.                          (5)
```

For `p` conditionally independent identical descendant branches, the common factor `2^(-p)`
cancels from the projective likelihood.  Exact homogeneous belief propagation is therefore

```text
                         (1+uy)^p-(1+vy)^p
R_(p;u,v)(y) = -----------------------------------------.        (6)
                         (1+uy)^p+(1+vy)^p
```

The symmetric BSC/zero-field Ising family is the slice `v=-u`.  Equation `(6)` is genuinely larger:
it contains every strictly positive positively correlated asymmetric binary channel.

## Rational degree, noncancellation, and monotonicity

Put `A(y)=1+uy` and `B(y)=1+vy`.  On `[-1,1]`, assumptions `(3)` give

```text
A(y)>0,                    B(y)>0.                              (7)
```

The primitive numerator and denominator of `(6)` have no common complex zero.  A common zero would
give `A^p=B^p=0`, hence `A=B=0`; subtracting the two affine equations gives `(u-v)y=0`, and then
`1=0`.  At least one of the leading coefficients `u^p-v^p` and `u^p+v^p` is nonzero, since their
simultaneous vanishing would force `u=v=0`.  Therefore

```text
deg R_(p;u,v)=p >= 2.                                            (8)
```

Direct differentiation gives

```text
R_(p;u,v)'(y)
  = 2p(u-v) A(y)^(p-1) B(y)^(p-1)
      / (A(y)^p+B(y)^p)^2
  > 0                         for -1 <= y <= 1.                  (9)
```

Moreover `|R(y)|<1` on the closed interval because `A^p,B^p>0`.  Thus strict stochastic
positivity becomes a global complex-dynamical discriminator: the physical real interval is mapped
strictly into its interior and the map is orientation-preserving there.

## Three multiplier regimes

The uninformative message `y=0` is a fixed point with exact multiplier

```text
lambda=R_(p;u,v)'(0)=p(u-v)/2=p(alpha-gamma)>0.                  (10)
```

### I. Contractive information: `0<lambda<1`

Zero is attracting but not superattracting.  The normalized local Schröder function `Phi` satisfies

```text
R(Phi(z))=Phi(lambda z),       Phi(0)=0,       Phi'(0)=1.        (11)
```

The Becker--Bergweiler classification permits a DA Schröder function only at a repelling fixed
point of a rational map of degree at least two.  Hence `Phi` is HT.

### II. Critical information: `lambda=1`

Zero is rationally indifferent.  The map cannot be the identity because its degree is `p>=2`.
Leau--Fatou petals therefore exist, and every sectorial Abel coordinate

```text
A_0(R(y))=A_0(y)+1                                               (12)
```

is HT by Becker--Bergweiler.  The sectorial beta `1/A_0'` is HT by the same antiderivative
argument as in the Bethe theorem.

### III. Expansive information: `lambda>1`

Let `H(y)=R(y)-y`.  Then `H(0)=0` and `H'(0)=lambda-1>0`, so `H(y)>0` for all sufficiently small
positive `y`.  Strict interval mapping gives `H(1)=R(1)-1<0`.  Let `c` be the first positive zero
after that initial positive interval.  Then

```text
0<c<1,             R(c)=c,             0<R'(c)<=1.              (13)
```

The upper bound follows from the left derivative at the first crossing; strict positivity follows
from `(9)`.  Thus `c` is either attracting but not superattracting or parabolic.

At zero, the normalized Poincare function again satisfies `(11)`, now with `lambda>1`.  If it were
DA, Ritt--Becker--Bergweiler would make `R` Möbius-conjugate to power/inverse-power, signed
Chebyshev, or elliptic/Weierstrass type.  Power and signed-Chebyshev maps have only
superattracting or repelling fixed cycles; elliptic/Weierstrass maps have no Fatou basin and all
periodic points are repelling.  None admits the non-super nonrepelling fixed point `(13)`.
Therefore the Poincare function at zero is HT.

## Exact beta, clock, and message-scheme theorem

When `lambda!=1`, let `kappa=Phi^(-1)`.  The exact homogeneous continuous iterate, beta, and
punctured depth clock are

```text
F_s(y)=Phi(lambda^s kappa(y)),
beta_y(y)=(log lambda) kappa(y)/kappa'(y),
tau_y(y)=log(kappa(y))/log lambda,
tau_y(R(y))=tau_y(y)+1.                                         (14)
```

The beta/clock equivalence proves that both are HT in regimes I and III.  At `lambda=1`, equation
`(12)` supplies the sectorial clock and beta.

If `x=h(y)` is any locally invertible DA likelihood-message chart, then local inversion,
composition, differentiation, and division transport DA in both directions.  Therefore the HT
verdict is invariant across every DA chart, including likelihood ratio, log-likelihood ratio,
odds, cavity field, and magnetization.

## Physical theorem and boundary

The theorem identifies a class-wide mechanism:

```text
strictly positive informative binary transfer
  + exact multiplicative aggregation on a regular tree
  -> an interior non-superattracting physical fixed point or an attracting zero
  -> exclusion of every finite-ADE exact message-depth generator.             (15)
```

The deterministic identity-channel boundary `alpha=1, gamma=0` is the symmetric noiseless power
map and is DA.  The uninformative boundary `alpha=gamma` collapses `(6)` to zero.  Other partially
degenerate boundary channels are not classified here.

This result concerns the deterministic homogeneous likelihood ray inside exact tree BP.  It does
not classify the full distributional BP operator, root reconstruction, mutual information,
channel capacity, loopy BP, or finite-depth decoding error.  For asymmetric channels the
Kesten--Stigum bound need not be the sharp reconstruction threshold; the present multiplier
classification must not be substituted for that stochastic theory.

## Quantum/QFT boundary and next theorem

Every positive two-state classical transfer tensor satisfying `(2)` is covered, so the theorem
applies to the diagonal binary sector of a tree tensor network whenever that sector is invariant
under contraction.  It does **not** prove the claim for a genuinely noncommutative quantum channel:
operator-valued messages need not remain on a projective line, and partial trace need not reduce to
two affine weights.

The next inheritance target is exact and falsifiable:

`[CONJECTURE]` Let a primitive completely positive transfer channel on a regular tree preserve a
faithful two-projection commutative subalgebra and let branch contraction multiply its two positive
likelihood components.  If the induced classical channel is strictly positive and informative,
then the expectation-value radial clock of that invariant sector is HT; if no such invariant sector
exists, an operator-valued replacement for the Ritt discriminator is required.

The first clause should become a theorem by proving the invariant-sector reduction, not by calling
the classical result quantum.  The second clause is the genuine noncommutative open core.

## Formula-level novelty audit

The external comparison separated three bodies of work:

1. broadcasting and reconstruction on trees, including asymmetric binary channels, studies root
   information, moment recursions, and reconstruction thresholds;
2. belief-propagation literature supplies exact sum-product recursion on trees and analyzes fixed
   points, contraction, and stability;
3. Becker--Bergweiler/Fernandes classify DA Schröder and Abel functions without applying the
   theorem to positive asymmetric channel recursions.

Searches combining asymmetric binary channels, tree BP, the affine-power formula `(6)`, rational
dynamics, Schröder/Abel functions, differential algebra, and hypertranscendence found the parent
literatures separately and no statement of `(8)`--`(15)`.  This is a provisional formula-level
novelty pass, not a priority proof.  Citation-graph and specialist audits remain required.

## Anti-theatre and dual gate

Exact BP, positive binary channels, and the functional-equation classification are parent theory.
The candidate new delta is the class theorem turning strict stochastic positivity into the global
non-Ritt fixed-point certificate `(13)`, and hence into scheme-invariant HT exact depth generation
for **every** channel in the open asymmetric parameter region `(2)`.

This is not merely the symmetric Ising theorem with renamed variables: `v` is independent of `u`,
and the proof replaces spin-flip symmetry by positivity and monotone first-crossing geometry.  The
novelty gate is provisionally positive.  The significance gate is positive as a universal theorem
for exact tree inference, but it is not Fields- or Nobel-level alone; the latter requires a
noncommutative quantum transfer theorem or an inherited continuum QFT/holographic observable.

## Lean boundary

The two affine branch likelihoods, exact rational family, symmetric Bethe specialization, fixed
anchor and multiplier, projective factor identities, noncancellation algebra, and exact derivative
cross-numerator factorization are now formalized unconditionally in
`formal/GaloisForLFunctions/HTGeometry/AsymmetricBinaryTreeRG.lean`.  The real interval
first-crossing theorem and external HT classification are not represented by assumptions.

## Primary sources

- E. Mossel, *Reconstruction on trees: beating the second eigenvalue*,
  *Annals of Applied Probability* 11 (2001), <https://doi.org/10.1214/aoap/998926994>.
- W. Liu and N. Ning, *Reconstruction for the Asymmetric Ising Model on Regular Trees*,
  <https://arxiv.org/abs/1712.00395>.
- W. Liu and N. Ning, *Large Degree Asymptotics and the Reconstruction Threshold of the
  Asymmetric Binary Channels*, <https://arxiv.org/abs/1812.06039>.
- Q. Yu and Y. Polyanskiy, *Ising Model on Locally Tree-like Graphs: Uniqueness of Solutions to
  Cavity Equations*, <https://arxiv.org/abs/2211.15242>.
- G. Fernandes, *A survey on the hypertranscendence of the solutions of Schroeder's, Boettcher's
  and Abel's equations*, <https://arxiv.org/abs/2102.12168>.
- L. Di Vizio and G. Fernandes, *A Galoisian proof of Ritt theorem on the differential
  transcendence of Poincare functions*, <https://arxiv.org/abs/2102.08268>.

## Gates

- [x] Exact asymmetric-channel homogeneous BP map derived.
- [x] Degree `p` and primitive noncancellation proved.
- [x] Strict interval mapping and global monotonicity proved.
- [x] Attracting, parabolic, and repelling multiplier regimes classified.
- [x] Non-super nonrepelling fixed point proved in the repelling regime.
- [x] Every Ritt-integrable class excluded.
- [x] Exact beta/clock HT proved throughout the open channel region.
- [x] DA message-scheme invariance proved.
- [x] Reconstruction and QFT boundaries stated.
- [x] Formula-level novelty search completed provisionally.
- [ ] Citation-graph and specialist priority audit completed.
- [x] Unconditional asymmetric rational-family algebra formalized in HTGeometry.
- [ ] Invariant commutative sector of a primitive quantum transfer channel proved.
- [ ] Genuinely operator-valued quantum-channel discriminator proved.

## Log — the real interval first-crossing theorem `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/RealTreeBPFirstCrossing.lean` (wired into
`GaloisForLFunctions.HTGeometry`, axiom-clean: `propext`, `Classical.choice`, `Quot.sound`).

Two reusable real-analysis lemmas that mathlib does not have:

- **`exists_first_zero_of_pos_of_neg`** — a continuous function positive at the left endpoint and
  negative at the right endpoint has a zero before which it stays positive.  The first zero is
  `sInf (Icc a b ∩ H⁻¹' Iic 0)`, which lies in the (closed) set, so `H c ≤ 0`; nothing below it lies
  in the set, so `H > 0` on `[a, c)`; and the left limit gives `H c ≥ 0`.
- **`deriv_nonpos_of_first_zero`** — the derivative at such a first zero is nonpositive, because the
  slope `(H y − H c)/(y − c)` is negative on the whole left approach and
  `hasDerivAt_iff_tendsto_slope` transfers the sign to the limit.

The belief-propagation layer:

- `treeBP p u v y = ((1+uy)^p − (1+vy)^p)/((1+uy)^p + (1+vy)^p)` — equation `(6)` over `ℝ`;
- `branch_pos` — both affine branch weights are positive on `[-1,1]` when `-1 < v < u < 1`;
- `treeBP_zero`, `treeBP_lt_one` — the uninformative fixed point and strict interval mapping;
- **`hasDerivAt_treeBP`** — the exact derivative `(9)`,
  `R' = 2p(u−v)A^{p−1}B^{p−1}/(A^p+B^p)^2`, and `treeBP_deriv_pos` its strict positivity;
- `hasDerivAt_treeBP_zero` — the multiplier `(10)`, `λ = p(u−v)/2`;
- **`exists_treeBP_interior_fixedPoint`** — equation `(13)`: for `λ > 1` there is `c ∈ (0,1)` with
  `R(c) = c` and `0 < R'(c) ≤ 1`, i.e. an interior fixed point that is attracting but not
  superattracting, or parabolic;
- `exists_channelTreeBP_interior_fixedPoint` (channel coordinates `0 < γ < α < 1`, multiplier
  `p(α−γ)`) and `exists_symmetricTreeBP_interior_fixedPoint` (the symmetric BSC / zero-field Ising
  slice `v = −u`).

This closes the card's real interval first-crossing gate.  The remaining Lean obligation is the
external Ritt / Becker--Bergweiler classification of rational maps admitting a differentially
algebraic Schröder/Poincaré function; the interior fixed point `(13)` is exactly the datum that
excludes every map on that special list.

## Log — the special-map multiplier layer `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SpecialMapFixedPointMultiplier.lean` (wired into
`GaloisForLFunctions.HTGeometry`, axiom-clean: `propext`, `Classical.choice`, `Quot.sound`).

The Ritt / Becker--Bergweiler step is used here in the contrapositive form "none of the special maps
admits a fixed point that is attracting but not superattracting, or parabolic".  That half is now
unconditional in Lean for both polynomial families on the list.

- **`multiplier_eq_of_conj`** — the multiplier of a fixed point is invariant under any locally
  invertible conjugacy (chain rule on `φ ∘ R = S ∘ φ`, cancelling `φ'(c) ≠ 0`).
- `powerMap`, **`powerMap_multiplier`** — every finite fixed point of `z ↦ z^n` has multiplier `0`
  (at the origin) or exactly `n`; `powerMap_no_nonsuper_nonrepelling` and
  **`not_conj_powerMap_of_nonsuper_nonrepelling`** turn that into the exclusion.
- `dicksonMap`, `exists_joukowski` (every complex number is `w + w⁻¹` for some `w ≠ 0`, via a square
  root of `c² − 4`), `dicksonMap_joukowski` (`D_n(w + w⁻¹) = wⁿ + w^{−n}`, mathlib's
  `dickson_one_one_eval_add_inv`), and **`dicksonMap_deriv_joukowski`** (the differentiated
  semiconjugacy, by uniqueness of the derivative on the open set `w ≠ 0`).
- **`two_le_norm_dicksonMap_multiplier`** — every finite fixed point of the normalized Chebyshev
  map has multiplier of modulus at least the degree.  A fixed point forces `wⁿ = w` or `wⁿ = w⁻¹`
  (the factorisation `(a − w)(aw − 1) = 0`), giving multiplier `n` or `−n` away from `w² = 1`; at
  `w = ±1` the doubled-variable identity `(C_n ∘ 2X) = 2 T_n` together with
  `T_derivative_eq_U`, `U_eval_one` and `U_eval_neg_one` gives modulus `n²`.
- **`not_conj_dicksonMap_of_nonrepelling`** — the corresponding exclusion.

Together with the interior fixed point `(13)` of `RealTreeBPFirstCrossing.lean`, this rules out the
power and Chebyshev branches of the Ritt list unconditionally.  What remains for this card is the
Lattès branch and the classification theorem itself (Becker--Bergweiler), whose proof needs
Nevanlinna value-distribution theory — absent from mathlib and the corpus, and therefore the next
substrate to build.

### Log addendum — inverse-power branch and the general linearizing mechanism `[PROVED]`

- `invPowerMap`, **`invPowerMap_multiplier`** — every finite nonzero fixed point of `z ↦ z^{-n}`
  satisfies `c^{n+1} = 1` and has multiplier exactly `−n`; `not_conj_invPowerMap_of_nonrepelling`
  is the exclusion.
- **`norm_multiplier_of_linearizingSemiconj`** — the mechanism common to all three branches of the
  Ritt list: if `R ∘ π = π ∘ (a·)` with `1 < ‖a‖`, then at a fixed point coming from a regular point
  of `π` whose orbit point has the same `‖π′‖`, the multiplier has modulus exactly `‖a‖`.  For the
  elliptic branch `π` is the Weierstrass `℘` and the equal-norm hypothesis is
  `℘′(a z₀) = ±℘′(z₀)`, which holds because a fixed point forces `a z₀ ≡ ±z₀` modulo the lattice.

Power, inverse-power and Chebyshev branches are therefore closed unconditionally; the elliptic
branch needs `℘` and its lattice symmetry, and the classification theorem itself remains.

### Log addendum — the elliptic (Lattès) branch is closed `[PROVED]`

mathlib carries the Weierstrass function (`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`:
`weierstrassP`, `derivWeierstrassP`, `deriv_weierstrassP`, `differentiableOn_weierstrassP`, and the
differential equation `derivWeierstrassP_sq`), so the last branch of the Ritt list is now
unconditional too:

- `hasDerivAt_weierstrassP` — `℘` is differentiable off the lattice with derivative `℘′`;
- **`norm_derivWeierstrassP_eq_of_weierstrassP_eq`** — equal `℘`-values force equal `|℘′|`,
  immediately from `℘′² = 4℘³ − g₂℘ − g₃` (no need for the two-to-one structure of `℘`);
- **`norm_multiplier_lattes`** — for `R ∘ ℘ = ℘ ∘ (a·)`, every regular fixed point has multiplier of
  modulus exactly `‖a‖`;
- **`not_lattes_of_nonrepelling`** — hence a Lattès map with `1 < ‖a‖` has no attracting-but-not-
  superattracting or parabolic regular fixed point.

All four families on the Ritt list — power, inverse power, Chebyshev, Lattès — are therefore
excluded unconditionally by the interior fixed point `(13)`.  The single remaining input for this
card is the classification theorem itself (Ritt / Becker--Bergweiler): that a rational map admitting
a differentially algebraic Schröder/Poincaré function must be one of those four.

### Log addendum — the Koenigs germ estimates `[PROVED]`

Starting the remaining classification input.  The corpus already carries a full Koenigs
linearization for the quadratic family (`Bottcher/KoenigsLinearization.lean`); the general germ
version needed for an arbitrary rational RG map is begun in
`formal/GaloisForLFunctions/HTGeometry/KoenigsLinearizationGerm.lean` (wired, axiom-clean).

- **`exists_quadratic_bound`** — the second-order Taylor bound for a holomorphic germ vanishing at
  the origin: `‖g z − μ z‖ ≤ K‖z‖²` near `0`, obtained from mathlib's
  `HasFPowerSeriesAt.isBigO_sub_partialSum_pow` after checking that both low-order coefficients of
  `g z − μ z` vanish.
- **`exists_contraction_ball`** — for any rate `c` strictly above `‖μ‖`, a ball on which the germ
  both contracts by `c` and satisfies its quadratic bound.
- **`orbit_norm_le`** — geometric decay `‖g^[n] z‖ ≤ cⁿ‖z‖` of the whole orbit.
- `koenigsApproxGerm g μ n z = g^[n] z / μⁿ` and **`koenigsApproxGerm_dist_succ`** — the telescope
  estimate `‖κ_{n+1} − κ_n‖ ≤ (K‖z‖²/‖μ‖)·(c²/‖μ‖)ⁿ`, geometric as soon as `c < √‖μ‖`, which is
  attainable because `‖μ‖ < √‖μ‖ < 1` for an attracting multiplier.

These are the convergence inputs for the linearizer; the limit, its normalization `κ′(0) = 1` and
the functional equation `κ ∘ g = μ·κ` come next, and after them the Poincaré function of the
repelling fixed point that the Ritt / Becker--Bergweiler classification is about.

### Log addendum — the Koenigs linearizer exists and satisfies its functional equation `[PROVED]`

- **`koenigsApproxGerm_cauchySeq`** — the approximants `g^[n] z / μⁿ` are Cauchy on the contraction
  ball, by `cauchySeq_of_le_geometric` applied to the telescope estimate with ratio `c²/‖μ‖ < 1`;
- `koenigsGerm`, `koenigsApproxGerm_tendsto` — the linearizer as the pointwise limit;
- **`koenigsGerm_semiconj`** — the Koenigs functional equation `κ(g z) = μ · κ(z)`, from
  `κ_n(g z) = μ · κ_{n+1}(z)` in the limit;
- `koenigsApproxGerm_at_zero`, `koenigsGerm_zero` — the normalization at the fixed point.

Remaining for the linearizer: analyticity of the limit (locally uniform convergence of the
approximants, each analytic on the contraction ball) and `κ′(0) = 1`; then the inverse gives the
Poincaré function of the repelling fixed point, which is the object the Ritt / Becker--Bergweiler
classification is stated about.

### Log addendum — Koenigs linearization is complete `[PROVED]`

`KoenigsLinearizationGerm.lean` now carries the whole theorem, unconditionally and axiom-clean:

- `koenigsDiff`, `koenigsApproxGerm_eq_add_sum` — the telescope decomposition
  `κ_n = id + ∑_{k<n} (κ_{k+1} − κ_k)`;
- **`koenigsApproxGerm_tendstoUniformlyOn`** — uniform convergence on the whole contraction ball,
  by `tendstoUniformlyOn_tsum_nat` against the summable majorant `(K r²/‖μ‖)·(c²/‖μ‖)^k`;
- `mapsTo_ball_of_contraction`, `mapsTo_ball_iterate`, `iterate_differentiableOn_ball`,
  `koenigsApproxGerm_differentiableOn` — the ball is forward invariant and every approximant is
  holomorphic on it;
- **`koenigsGerm_differentiableOn`** — the linearizer is holomorphic
  (`TendstoLocallyUniformlyOn.differentiableOn`);
- `hasDerivAt_iterate_zero` (`(g^[n])′(0) = μⁿ`), `deriv_koenigsApproxGerm_zero`, and
  **`deriv_koenigsGerm_zero`** — the normalization `κ′(0) = 1`
  (`TendstoLocallyUniformlyOn.deriv` plus uniqueness of limits).

Together with `koenigsGerm_zero` and `koenigsGerm_semiconj` this is **Koenigs' theorem** for a
general holomorphic germ with attracting nonzero multiplier: a holomorphic `κ` with `κ(0) = 0`,
`κ′(0) = 1` and `κ ∘ g = μ · κ` on a ball.  mathlib has no such theorem, and the corpus previously
had it only for `z² + c`.

Next: invert `κ` to obtain the Poincaré function of the repelling fixed point, then the Ritt /
Becker--Bergweiler classification on top of the corpus Nevanlinna stack.

### Log addendum — the Poincaré function `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/PoincareFunctionGerm.lean` (wired, axiom-clean):

- **`exists_poincare_of_linearizer`** — inverting a normalized linearizer turns `κ ∘ g = μ·κ` into
  the Poincaré equation.  From `HasStrictDerivAt κ 1 0` mathlib's inverse function theorem
  (`HasStrictDerivAt.localInverse`, `eventually_left_inverse`, `eventually_right_inverse`,
  `to_localInverse`) supplies `Φ` with `Φ 0 = 0`, `Φ′ 0 = 1`, `κ ∘ Φ = id` near `0`, and the five
  eventual facts combine to `Φ(μ w) = g(Φ w)` — injectivity of `κ` near the fixed point being what
  turns `κ(g(Φ w)) = κ(Φ(μ w))` into the equation itself.
- **`exists_poincare_koenigs`** — the same for the Koenigs linearizer built in
  `KoenigsLinearizationGerm.lean`: the linearizer is holomorphic, so analytic, so
  `AnalyticAt.hasStrictDerivAt` plus `deriv_koenigsGerm_zero` gives the strict derivative `1`, and
  the semiconjugacy holds on the whole contraction ball.

Equation `(11)` of the card — the normalized Schröder/Poincaré function at a fixed point with
`Φ(0)=0`, `Φ′(0)=1`, `R(Φ z) = Φ(λ z)` — is therefore constructed unconditionally for an arbitrary
holomorphic germ, not only for `z² + c`.  The single remaining input is the classification
direction: that a rational map whose Poincaré function is differentially algebraic must be power,
inverse-power, Chebyshev or Lattès — all four of which the card's interior fixed point `(13)`
already excludes.

### Log addendum — the entire Poincaré extension `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/EntirePoincareExtension.lean` (wired, axiom-clean):

- `poincareApprox f Φ₀ λ n w = f^[n](Φ₀(w/λⁿ))` — the rescaled iterates;
- `poincareApprox_succ_of_admissible`, **`poincareApprox_eq_of_le`** — at each point the sequence is
  constant from any admissible exponent onwards, because the germ equation pushes one iterate
  through the rescaling;
- `exists_admissible_exponent` — `‖w‖ < ρ‖λ‖ⁿ` for large `n`, since `‖λ‖ > 1`;
- `differentiable_iterate_self`;
- **`exists_entire_poincare`** — a Poincaré germ at a repelling fixed point of an *entire* map
  extends to an entire `Φ` on the whole plane with `Φ(λ w) = f(Φ w)` everywhere and `Φ = Φ₀` near
  the fixed point.  Each approximant is holomorphic on the disc where the rescaled argument is
  admissible, and the eventual constancy glues them.

With `PoincareFunctionGerm.lean` this gives the global object of the classification theorem: the
entire Poincaré function of a repelling fixed point, normalized by `Φ(0)=0`, `Φ′(0)=1`.  What is
still missing is the classification direction itself, and — for the rational RG maps of this card —
the meromorphic rather than entire form of the extension.

### Log addendum — uniqueness of the linearizer `[PROVED]`

**`eq_koenigsGerm_of_linearizer`** — any analytic `κ` with `κ(0) = 0`, `κ′(0) = 1` and
`κ ∘ g = μ · κ` on the contraction ball coincides with the constructed `koenigsGerm` near the fixed
point.  The proof needs no power-series comparison: iterating the linearizing equation gives
`κ(g^[n] z) = μⁿ κ(z)`, so the approximant defect is `(g^[n]z − κ(g^[n]z))/μⁿ`, which the quadratic
bound for `κ` at the fixed point makes `O((c²/‖μ‖)ⁿ)`; the approximants therefore converge to `κ` as
well as to `koenigsGerm`, and limits are unique.

Koenigs' theorem is thus complete in both directions — existence and uniqueness — so the normalized
Schröder/Poincaré function `(11)` of this card is a well-defined object of the corpus rather than a
choice.

### Log — the map is conjugate to no special map `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/TreeBPComplexMultiplier.lean` (wired, axiom-clean) closes
the whole exclusion half of the card's step `(13)`–`(15)`.

- `treeBPC` — the belief-propagation map `(6)` as a rational map of the complex plane, with
  `treeBPC_ofReal` identifying its restriction to `ℝ` with the real map of the first-crossing
  theorem;
- **`hasDerivAt_treeBPC`** — the exact complex derivative `(9)`;
- **`exists_treeBPC_nonsuper_nonrepelling_fixedPoint`** — the interior fixed point of `(13)` seen in
  `ℂ`: a fixed point whose multiplier is nonzero of modulus at most one, obtained by casting the
  real fixed point and its positive multiplier through `Complex.ofReal`;
- **`treeBPC_not_conj_special`** — the packaged conclusion: that fixed point makes the map conjugate
  to **none** of the four Ritt families.  All four exclusions are discharged simultaneously —
  `powerMap`, `invPowerMap`, `dicksonMap` (Chebyshev) and the Lattès semiconjugacy `R ∘ ℘ = ℘ ∘ (a·)`
  with `1 < ‖a‖`.

So the card's own dynamical argument — "strict channel positivity produces a non-superattracting
real basin that excludes every Ritt-integrable rational map" — is now a Lean theorem.  The one
remaining input is the converse classification (Ritt / Becker--Bergweiler): that a differentially
algebraic Poincaré function *forces* membership in that list.  The Poincaré function itself is now
constructed and characterized in the corpus (`KoenigsLinearizationGerm`, `PoincareFunctionGerm`,
`EntirePoincareExtension`).
