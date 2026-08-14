# Diamond-Ising exact beta has no finite algebraic-differential scheme

- **ID:** `diamond-ising-da-scheme-rg-generation-hypertranscendence`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / EXACT PHYSICAL RG BRIDGE
- **Scientific status:** `[PROVED HERE] [PARENT-DERIVED MATHEMATICS]`
  `[PHYSICAL HIERARCHICAL ISING MODEL] [NOVELTY NEEDS AUDIT] [NOT YET QFT]`
- **Scope:** general hypertranscendence in an interacting physical renormalization problem; no
  Riemann-hypothesis or distinguished-special-function input
- **Statement:** At the nontrivial thermal fixed point of the zero-field Ising model on the
  two-branch, two-bond diamond hierarchical lattice, the exact local Callan--Symanzik beta field
  is hypertranscendental in the physical transmissivity and in every locally invertible
  differentially algebraic coupling scheme.  Linearization is possible, but every linearizing
  coupling coordinate is itself hypertranscendental.

## The exact physical map

Put a zero-field Ising spin `s_v in {+1,-1}` at every vertex and give each bond the weight

```text
exp(K s_v s_w),              t = tanh K.                         (1)
```

One diamond replacement puts two equal bonds in series on each of two parallel branches.
Summing the internal spin on one branch gives an effective series coupling `K_s` with

```text
tanh K_s = t^2.                                                   (2)
```

The two branches are in parallel, so their couplings add.  The tangent addition law therefore
gives the exact one-step renormalization map

```text
R(t) = tanh(2 K_s) = 2 t^2 / (1+t^4).                            (3)
```

This is an exact decimation identity, not a perturbative beta-function approximation.
Hierarchical-lattice RG as a rational map on finite-dimensional projective coupling space is
parent theory; equation `(3)` is also obtained directly from that construction in the Ising
invariant line.

In projective Boltzmann weights, if `z_s=A(1+t)` and `z_d=A(1-t)`, the exact two-branch map is

```text
Z_s=(z_s^2+z_d^2)^2,                 Z_d=(2z_s z_d)^2,
t'=(Z_s-Z_d)/(Z_s+Z_d)=2t^2/(1+t^4).                             (3a)
```

Consequently the four poles `t^4=-1` used below are zeros of the one-block normalization
`Z_s+Z_d`.  Their backward tree is the block-normalization/Fisher divisor tower of the exact
hierarchical recursion, not an auxiliary complex-dynamics decoration.

## The thermodynamic critical fixed point

Let

```text
g(t) = t^3+t^2+t-1.                                               (4)
```

Since `g'(t)=3t^2+2t+1>0` on the real line, while

```text
g(1/2)=-1/8,              g(2/3)=11/27,                           (5)
```

there is a unique `c in (1/2,2/3)` with `g(c)=0`.  The factorization

```text
t^4-2t+1 = (t-1)(t^3+t^2+t-1)                                   (6)
```

shows that `R(c)=c`.  Moreover

```text
R'(t) = 4t(1-t^4)/(1+t^4)^2,
lambda := R'(c) = 2(1-c)/c > 1.                                  (7)
```

Thus `c` is the repelling RG fixed point separating the high- and low-temperature basins on the
physical interval.  Here “critical” is thermodynamic terminology; `c` is not a critical point of
the rational map.

## Exact flow and beta constraint

Let `Phi` be the normalized Poincare function at `c` and let `kappa` be its local inverse:

```text
Phi(0)=c,        Phi'(0)=1,        R(Phi(z))=Phi(lambda z),
kappa(c)=0,      kappa'(c)=1,      kappa(R(t))=lambda kappa(t).    (8)
```

For real flow time `s` near zero, define

```text
F_s(t) = Phi(lambda^s kappa(t)).                                  (9)
```

This is a local one-parameter RG flow with `F_1=R`.  Its canonical beta field is

```text
beta(t) = (d/ds)|_(s=0) F_s(t)
        = (log lambda) kappa(t)/kappa'(t).                         (10)
```

Differentiating the Schroeder constraint in `(8)` gives the static Julia constraint

```text
beta(R(t)) = R'(t) beta(t).                                       (11)
```

Equations `(9)`--`(11)` are established parent RG functional-conjugation theory.  The new work
below is the exact differential-algebraic obstruction for this physical `R` and its scheme-level
interpretation.

## The Poincare function is hypertranscendental

Translate the fixed point to zero:

```text
S(y)=R(y+c)-c,                sigma(z)=Phi(z)-c.                   (12)
```

Then `S(0)=0`, `S'(0)=lambda`, and `S(sigma(z))=sigma(lambda z)`.  Suppose for contradiction
that `sigma` is differentially algebraic over `C(z)`.  The Di Vizio--Fernandes form of Ritt's
theorem then supplies integers `r != 0`, `j`, and a nonzero rational function `A` such that

```text
(sigma'(z))^r = z^j A(sigma(z)).                                  (13)
```

Differentiate the Poincare equation and use `(13)` at `z` and `lambda z`.  Cancellation on a
nonempty germ gives the rational identity

```text
lambda^(r+j) A(S(y)) = S'(y)^r A(y).                              (14)
```

With `B(t)=A(t-c)`, this is

```text
lambda^(r+j) B(R(t)) = R'(t)^r B(t).                              (15)
```

For a point `a` of the Riemann sphere, write `b_a=ord_a(B)`.  The local behavior of `(3)` and
`(7)` now forces an infinite divisor.

1. At the superattracting fixed point `0`, `R` has local degree two and `ord_0(R')=1`.
   Taking orders in `(15)` gives `2b_0=r+b_0`, hence

   ```text
   b_0=r.                                                         (16)
   ```

2. At infinity, `R(t)` tends to `0` with local degree two and `R'(t)` has order three.
   Therefore `2b_0=3r+b_infinity`, so

   ```text
   b_infinity=-r.                                                 (17)
   ```

3. Let `p` be any root of `p^4=-1`.  It is a simple pole of `R`, and `R'` has a double pole
   there.  Equation `(15)` gives

   ```text
   b_infinity=-2r+b_p,             hence b_p=r.                   (18)
   ```

The critical points of `R` are `0`, infinity, and the four roots of `t^4=1`; their critical
values are exactly `0,1,-1`.  The backward orbit of `p` cannot meet this set, because the forward
orbits of `0,1,-1` stay in `{0,1}` whereas `p` is a root of `-1` and is neither `0` nor `+/-1`.
Consequently every point in the backward orbit of `p` has four distinct noncritical preimages.
At every such preimage, taking orders in `(15)` preserves the value `r`.  Thus `B` has order
`r != 0` at infinitely many points, impossible for a rational function.

The contradiction proves

```text
Phi is hypertranscendental over C(z).                             (19)
```

This direct divisor proof also verifies, without relying on a portrait label, that the physical
map lies outside every differentially algebraic case in Ritt's classification.

## The beta field is hypertranscendental

Locally invertible differentially algebraic germs are closed under compositional inversion.
Hence `Phi` is DA if and only if `kappa` is DA.  Equation `(10)` gives one direction immediately:

```text
kappa DA  =>  beta DA.                                           (20)
```

Conversely, if `beta` were DA, then

```text
kappa' = ((log lambda)/beta) kappa                               (21)
```

would make `kappa` DA over the differential field generated by `beta`; transitivity of
differential algebraicity would make `kappa` DA over `C(t)`.  This contradicts `(19)`.  Therefore

```text
beta is hypertranscendental over C(t).                            (22)
```

Notice what has and has not been proved.  The analytic flow `(9)` exists.  Hypertranscendence
does not mean “there is no flow”; it means that the exact flow generator has no finite
algebraic-differential description in the physical coupling.

## Scheme theorem: the complexity cannot be removed by a finite-AD chart

Let `u=h(t)` be a locally invertible DA coupling change near `c`, and write

```text
R_h = h o R o h^(-1).                                             (23)
```

The transported beta field satisfies

```text
beta_h(h(t)) = h'(t) beta(t).                                     (24)
```

DA germs are closed under composition, differentiation, division, and local inversion.  Thus
`beta_h` is DA if and only if `beta` is DA.  Combining this with `(22)` proves:

```text
Every locally invertible DA renormalization scheme has an HT beta field.     (25)
```

The restriction to DA schemes is load-bearing.  The analytic change `u=kappa(t)` makes the flow
linear and gives `du/ds=(log lambda)u`; but `(19)` says that this trivializing coordinate is HT.
Therefore arbitrary analytic reparametrization can move the HT out of the beta field, but it can
do so only by putting the same non-finite differential complexity into the coupling chart.

This suggests the source-categorical physical invariant:

```text
RG-generation HT = no finite algebraic-differential coupling atlas
                   contains a finite algebraic-differential exact beta field.             (26)
```

## Discriminator and route selection

Four reporters were tested against the same requirement: source-natural, non-Gaussian or
interacting, exact, and stable under a stated admissible coordinate class.

| Reporter | Exact parent input | Result of the attack |
|---|---|---|
| p-adic fourth-cumulant boundary cocycle | rigorous non-Gaussian field and shell sum | still open: the shell seed is analytic but not proved DA |
| Poincare/Koenigs scaling coordinate | exact rational RG map | HT, but it is a coordinate rather than a local physical generator |
| canonical beta field | exact rational RG map plus flow normalization | survives; HT in every DA coupling chart |
| hierarchical free-energy cocycle | additive RG cohomology | deferred: local-counterterm quotient and relative base are not yet intrinsic |

There is also an exact negative control.  Pure parallel doubling has

```text
P(t)=2t/(1+t^2),      kappa_P(t)=arctanh(t),
beta_P(t)=(log 2)(1-t^2)arctanh(t),                              (27)
```

so its beta field is DA.  The diamond decimation inserts the series operation `t -> t^2` before
parallel doubling.  The discrete step remains rational, but its critical/pole orbit forces the
continuous generator from DA to HT.  Thus “nonlinearity” alone is not the mechanism; the
discriminator is the global divisor dynamics created by genuine internal-spin decimation.

The divisor has a direct statistical-field meaning.  The valuation contradiction `(16)`--`(18)`
says that a finite algebraic-differential invariant would have to carry the same nonzero order on
every pullback of a complex block-normalization zero.  The proliferating Fisher divisor makes that
impossible.  Complex zeros by themselves are not sufficient--power, Chebyshev, trigonometric, and
elliptic DA cases have highly structured infinite divisors--so the load-bearing fact is the
nonexceptional branching portrait of this divisor tower.

The family theorem
`diamond-ising-family-rg-generation-hypertranscendence.md` now extends this result from `b=2` to
every `b`-branch, two-bond diamond lattice with `b>=2`.

## Physical meaning and present boundary

The result is exact and interacting: it comes from summing physical Ising spins in a hierarchical
lattice, not from inserting a known HT special function into an observable.  It provides the
first clean example in this program where

```text
finite rational discrete RG rule
+ exact analytic continuous interpolation
+ no finite algebraic-differential beta description in any DA scheme.        (28)
```

It is not yet a continuum QFT theorem.  The diamond Ising model is a classical hierarchical
statistical field system.  The next QFT-level obligation is to reproduce the same Ritt-divisor
obstruction on a finite-dimensional invariant coupling slice of a rigorous non-Gaussian field RG,
or to prove that the infinite-dimensional p-adic fixed-point RG induces such a slice on a compact
source sector.

## Anti-theatre and dual gate

The component facts are parent theory:

- the diamond hierarchical Ising decimation and rational RG representation;
- Poincare/Koenigs linearization and exact beta functional equations;
- Ritt's classification and the Di Vizio--Fernandes Galoisian criterion.

The proved contribution is their exact assembly in a physical interacting RG map, the explicit
infinite-divisor obstruction `(16)`--`(18)`, and the DA-scheme invariant formulation `(25)`--`(26)`.
Targeted searches for “hierarchical Ising differential transcendence,” “diamond Ising Poincare
Ritt,” “diamond hierarchical Schroeder beta,” and the exact map together with “beta function” did
not locate this conjunction.  That is negative evidence only; the novelty gate remains open until
formula-level review of the complex-dynamics and hierarchical-RG literature.

The significance gate is partially cleared: `(26)` is a mathematically sharp candidate for a new
physical HT invariant and `(28)` is an exact nontrivial model.  A Fields- or Nobel-level claim is
not warranted without a continuum QFT realization, observable consequences, and a universality
theorem across an intrinsic class of admissible physical schemes.

## Lean boundary

The external Ritt theorem and analytic Poincare existence are not presently in the Lean corpus.
Formalization should therefore target only unconditional exact algebra that carries the physical
map: the rational-function identity `(3)`, its derivative identity `(7)`, and the fixed-point
factorization `(6)`.  A theorem assuming the missing Ritt or analytic inputs would be wrapper
theatre.

That exact core is now formalized in
`../../3-formalized/diamond-ising-exact-rg-algebra.md`, through module
`GaloisForLFunctions.HTGeometry.DiamondIsingRG`.  The full beta-field HT statement remains
paper-level until the external analytic and Ritt theory can be proved unconditionally in Lean.

## Primary sources

- J. De Simoi and S. Marmi, *Potts models on hierarchical lattices and Renormalization Group
  dynamics*, <https://arxiv.org/abs/0708.0616>.
- J. De Simoi, *Potts models on hierarchical lattices and Renormalization Group dynamics II:
  examples and numerical results*, <https://arxiv.org/abs/0711.4610>.
- T. L. Curtright and C. K. Zachos, *Renormalization Group Functional Equations*,
  <https://arxiv.org/abs/1010.5174>.
- L. Di Vizio and G. Fernandes, *A Galoisian proof of Ritt theorem on the differential
  transcendence of Poincare functions*, <https://arxiv.org/abs/2102.08268>.
- M. Aschenbrenner and W. Bergweiler, *Julia's equation and differential transcendence*,
  <https://arxiv.org/abs/1307.6381>.
- F. Pakovich, *On algebraic dependencies between Poincare functions*,
  <https://arxiv.org/abs/2106.05770>.

## Gates

- [x] 0 -> 1 in-progress: exact physical map, source-pure reporter, and hard failure modes stated.
- [x] 1 -> 2 fully-proven: exact paper proof of RG map, repelling fixed point, Ritt obstruction,
  beta HT, and DA-scheme invariance.
- [ ] Novelty audit: formula-level search of hierarchical Ising complex dynamics, invariant
  differentials, and exact-RG beta literature.
- [x] Unconditional rational-function core formalized in HTGeometry, with targeted build and axiom
  audit; the analytic beta-field HT theorem remains external.
- [ ] 3 -> 4 publication-ready: continuum-QFT realization and scheme-universality theorem.

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
