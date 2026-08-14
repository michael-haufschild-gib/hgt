# Every branching diamond-Ising exact beta is hypertranscendental

- **ID:** `diamond-ising-family-rg-generation-hypertranscendence`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / EXACT PHYSICAL RG FAMILY
- **Scientific status:** `[PROVED HERE] [PARENT-DERIVED CLASSIFICATION]`
  `[INFINITE PHYSICAL MODEL FAMILY] [NOVELTY NEEDS AUDIT] [NOT YET CONTINUUM QFT]`
- **Scope:** general hypertranscendence in interacting exact renormalization; no
  Riemann-hypothesis or distinguished-special-function input
- **Statement:** For every integer `b >= 2`, the zero-field Ising model on the `b`-branch,
  two-bond diamond hierarchical lattice has a unique nontrivial thermal fixed point.  Its exact
  local beta field is hypertranscendental in physical transmissivity and in every locally
  invertible DA coupling scheme.

## Exact family of physical RG maps

Let `z_s` and `z_d` be the Boltzmann weights for equal and unequal endpoint spins, and use the
projective high-temperature coordinate

```text
t=(z_s-z_d)/(z_s+z_d)=tanh K.                                    (1)
```

One branch contains two bonds in series, and there are `b` identical branches in parallel.  Exact
summation of the internal spins gives the renormalized projective weights

```text
Z_s=(z_s^2+z_d^2)^b,                 Z_d=(2 z_s z_d)^b.           (2)
```

Writing `z_s=A(1+t)` and `z_d=A(1-t)` in `(2)` and taking
`(Z_s-Z_d)/(Z_s+Z_d)` gives

```text
             (1+t^2)^b-(1-t^2)^b
R_b(t) = --------------------------------.                        (3)
             (1+t^2)^b+(1-t^2)^b
```

For `b=2`, equation `(3)` is `2t^2/(1+t^4)`.  Thus the previously proved two-branch theorem is the
first member of an exact physical family, not a specially inserted rational map.

The denominator in `(3)` is, up to the nonzero projective factor, the one-block normalization
`Z_s+Z_d`.  Its complex zeros are the primitive block-normalization/Fisher divisor.  Pulling this
divisor back under repeated exact RG produces the corresponding higher-generation divisor tower.

## Unique nontrivial fixed point and its multiplier

On the physical interval put

```text
u=log((1+t)/(1-t))=2 arctanh(t),              t=tanh(u/2).        (4)
```

The identity

```text
(1+t^2)/(1-t^2)=cosh u                                         (5)
```

turns `(3)` into the analytically conjugate map

```text
G_b(u)=b log(cosh u).                                            (6)
```

Let `H_b(u)=G_b(u)-u` for `u>=0`.  Then

```text
H_b(0)=0,
H_b'(u)=b tanh u-1,
H_b''(u)=b sech^2 u>0,                                          (7)
```

and

```text
H_b(u)=(b-1)u-b log 2+o(1)             as u -> +infinity.       (8)
```

Therefore `H_b` first decreases, has one strict negative minimum at
`u_0=arctanh(1/b)`, and then increases to infinity.  It has exactly one positive zero `u_b`, and
`u_b>u_0`.  Hence

```text
c_b=tanh(u_b/2) in (0,1)                                       (9)
```

is the unique nontrivial physical fixed point.  Analytic conjugacy preserves its multiplier, so

```text
lambda_b=R_b'(c_b)=G_b'(u_b)=b tanh u_b>1.                      (10)
```

Thus `c_b` is the repelling thermal fixed point separating the high- and low-temperature basins.

## The critical portrait is never Ritt-integrable

The numerator and denominator in `(3)` are coprime: a common zero would force both
`(1+t^2)^b` and `(1-t^2)^b` to vanish.  Exactly one of their leading terms of degree `2b`
survives, according to the parity of `b`.  Hence

```text
deg R_b=2b.                                                       (11)
```

At the high-temperature fixed point,

```text
R_b(t)=b t^2+O(t^6),                                            (12)
```

so `0` is superattracting with local degree two.  At the low-temperature fixed point, write
`x=1-t^2`; then

```text
1-R_b(t)=2x^b/((2-x)^b+x^b).                                    (13)
```

Thus `1` is superattracting with local degree `b`.  In particular `R_b` has two distinct
superattracting fixed points, with local degrees `2` and `b`, both strictly below its global degree
`2b`.

Suppose the normalized Poincare function at `c_b` were differentially algebraic.  The
Ritt--Becker--Bergweiler classification leaves only three dynamical types.

1. **Power type.** A degree-`2b` power map has two superattracting fixed points, both totally
   ramified with local degree `2b`; an inverse power map has its totally ramified points in a
   two-cycle.  Neither portrait matches `(12)`--`(13)`.
2. **Signed Chebyshev type.** A signed Chebyshev polynomial has only its point at infinity as a
   superattracting fixed point; its finite critical points map to noncritical endpoints.  It cannot
   have the two superattracting fixed points in `(12)`--`(13)`.
3. **Elliptic/Weierstrass type.** The associated rational maps have empty Fatou set.  The
   superattracting basin of `0` already gives `R_b` a nonempty Fatou set.

Möbius conjugacy preserves global degree, local degrees, periodic critical portraits, and emptiness
of the Fatou set.  All DA cases are therefore impossible.  If `Phi_b` is the normalized Poincare
function at `c_b`, then

```text
Phi_b is hypertranscendental over C(z) for every b>=2.           (14)
```

## Exact beta and scheme theorem

Let `kappa_b=Phi_b^(-1)` locally and define

```text
beta_b(t)=(log lambda_b) kappa_b(t)/kappa_b'(t).                  (15)
```

DA germs are closed under local compositional inversion, so `Phi_b` is DA exactly when `kappa_b`
is DA.  If `beta_b` were DA, the first-order equation

```text
beta_b kappa_b'-(log lambda_b)kappa_b=0                          (16)
```

and transitivity of differential algebraicity would make `kappa_b`, hence `Phi_b`, DA.  This
contradicts `(14)`.  Therefore

```text
beta_b is hypertranscendental over C(t) for every b>=2.          (17)
```

For a locally invertible DA coupling scheme `v=h(t)` with DA inverse,

```text
beta_(b,h)(h(t))=h'(t) beta_b(t).                                (18)
```

DA closure applied in both directions makes `(17)` invariant under every such scheme.  An
arbitrary analytic chart can linearize the flow, but every such linearizing chart is itself HT.

## Physical interpretation: a Fisher-divisor obstruction to finite scale generation

This family identifies a source-level mechanism:

```text
internal-spin decimation
  -> complex block-normalization divisor
  -> nonexceptional branched RG portrait
  -> differential incoherence of the RG tower
  -> HT exact scale generator.                                  (19)
```

The appearance of partition-function zeros as boundaries or singular loci of complex RG flows is
parent science.  The new claim requiring audit is the last two arrows: their exact assembly into a
scheme-invariant HT generator theorem for the whole branching family.

The presence of complex zeros alone is not sufficient.  DA functions such as trigonometric and
elliptic functions also have infinite structured divisors, and the Ritt-integrable power and
Chebyshev maps are the exact counterexamples.  What matters is that the block divisor generates a
critical portrait outside every parabolic-orbifold/Ritt family.

## Anti-theatre and dual gate

The exact projective RG, the relation between hierarchical RG and Fisher zeros, analytic
linearization, and the Ritt--Becker--Bergweiler classification are parent results.  The work here is
the uniform fixed-point proof `(4)`--`(10)`, the family-wide critical-portrait exclusion, and the
physical HT interpretation `(19)`.

The significance gate improves on the isolated `b=2` result: RG-generation HT now holds for an
infinite family of interacting exact models with varying branching geometry.  The novelty gate is
still open pending formula-level review of hierarchical Ising/Potts complex dynamics and the
differential-transcendence literature.  This is not yet a continuum-QFT theorem.

## Lean boundary

The family formula `(3)`, its Boltzmann-weight derivation `(2)`, the fixed values `R_b(0)=0` and
`R_b(1)=1`, and the local algebra behind `(12)`--`(13)` are unconditional finite algebra.  They are
now formalized in
`../../3-formalized/diamond-ising-family-exact-rg-algebra.md`, through module
`GaloisForLFunctions.HTGeometry.DiamondIsingFamilyRG`.  The analytic fixed-point theorem and the external
Ritt--Becker--Bergweiler classification are not yet in the Lean corpus and must not be replaced by
hypotheses or axioms.

The formal module is substantive rather than a `b=2` wrapper: it derives both physical block
weights for arbitrary `b`, proves the exact normalization factors, proves quadratic contact at the
high-temperature anchor, and proves primitive numerator/denominator noncancellation over `C`.

## Primary sources

- J. De Simoi, *Potts models on hierarchical lattices and Renormalization Group dynamics II:
  examples and numerical results*, <https://arxiv.org/abs/0711.4610>.
- J. De Simoi and S. Marmi, *Potts models on hierarchical lattices and Renormalization Group
  dynamics*, <https://arxiv.org/abs/0708.0616>.
- G. Fernandes, *A survey on the hypertranscendence of the solutions of Schroeder's, Boettcher's
  and Abel's equations*, <https://arxiv.org/abs/2102.12168>.
- L. Di Vizio and G. Fernandes, *A Galoisian proof of Ritt theorem on the differential
  transcendence of Poincare functions*, <https://arxiv.org/abs/2102.08268>.
- A. Denbleyker, D. Du, Y. Liu, Y. Meurice, and H. Zou,
  *Fisher's zeros as boundary of renormalization group flows in complex coupling spaces*,
  <https://arxiv.org/abs/1005.1993>.

## Gates

- [x] Exact `b`-branch physical map derived in projective transmissivity.
- [x] Unique nontrivial repelling physical fixed point proved for every `b>=2`.
- [x] Global and local degrees proved.
- [x] Every Ritt-integrable dynamical portrait excluded.
- [x] Exact beta HT and DA-scheme invariance proved for the whole family.
- [x] Fisher-divisor mechanism isolated without claiming that zeros alone imply HT.
- [ ] Formula-level novelty audit across hierarchical RG and complex dynamics completed.
- [x] Substantive unconditional family algebra formalized in HTGeometry with targeted verification
  and axiom audit.
- [ ] Continuum-QFT realization proved.

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
