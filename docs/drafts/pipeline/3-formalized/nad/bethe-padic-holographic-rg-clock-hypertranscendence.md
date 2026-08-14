# Every finite-temperature Bethe/p-adic holographic Ising RG clock is hypertranscendental

- **ID:** `bethe-padic-holographic-rg-clock-hypertranscendence`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / EXACT HOLOGRAPHIC RG BRIDGE
- **Scientific status:** `[PROVED HERE] [PARENT-DERIVED CLASSIFICATION]`
  `[BETHE-TREE HOLOGRAPHIC MODEL] [P-ADIC TREE WHEN p IS PRIME]`
  `[FORMULA-LEVEL NOVELTY SEARCH PASSED PROVISIONALLY]`
  `[SPECIALIST PRIORITY AUDIT OPEN] [NOT A CONTINUUM QFT THEOREM]`
- **Scope:** general hypertranscendence in exact physical scale generation; no
  Riemann-hypothesis or distinguished-special-function input
- **Statement:** For every branching number `p>=2` and every strictly finite positive temperature
  of the ferromagnetic Bethe-lattice Ising model, the exact boundary-field-to-radial-scale
  generator is hypertranscendental.  Below and above the Bethe transition this is an analytic local
  Schröder/Poincare beta and clock; at the transition it is a sectorial Abel beta and clock.  The
  zero-temperature endpoint is exceptionally differentially algebraic.  The conclusion is invariant
  under every locally invertible differentially algebraic physical field scheme.  When `p` is prime,
  the same theorem lives on the Bruhat--Tits tree used in the parent model's p-adic AdS/CFT
  interpretation.

## Exact parent RG and rational physical chart

Let the Bethe lattice have coordination `q>2` and put

```text
p=q-1 >= 2,                    a=tanh K in [0,1].                (1)
```

Here `K` is the ferromagnetic inverse-temperature edge coupling.  Okunishi--Takayanagi's exact
inward recursion for the effective boundary magnetic field is

```text
h_(n-1)=f_(p,a)(h_n),
f_(p,a)(h)=p arctanh(a tanh h).                                  (2)
```

Its multiplier at zero is

```text
f_(p,a)'(0)=pa,                                                   (3)
```

so the Bethe transition is `pa=1`.  The physical DA change

```text
y=tanh h,                         h=arctanh y                     (4)
```

turns `(2)` into the degree-`p` rational map

```text
                   (1+ay)^p-(1-ay)^p
F_(p,a)(y) = ----------------------------------.                  (5)
                   (1+ay)^p+(1-ay)^p
```

For `a!=0`, its numerator and denominator are coprime: a common zero would force both `1+ay` and
`1-ay` to vanish.  Exactly one parity component carries the degree-`p` leading term, hence

```text
deg F_(p,a)=p >= 2.                                               (6)
```

This is the projective boundary-magnetization RG map.  Its denominator is the exact block
normalization obtained by summing the descendant branches.

## The all-temperature theorem

The temperature axis changes the relevant functional equation, but not the HT verdict:

```text
0<a<1/p       attracting zero        local Schroeder clock       HT
a=1/p         parabolic zero         sectorial Abel clock        HT
1/p<a<1       repelling zero plus     Poincare clock              HT
              ordered attracting basin
a=1           pure branching         power-map clock             DA
a=0           collapsed recursion    no nontrivial scale germ     --          (7)
```

Thus the thermodynamic phase transition is not an onset of hypertranscendence.  It is a transition
between two analytic realizations of the same finite-temperature absence of a finite
algebraic-differential scale law.

### I. High-temperature phase: `0<a<1/p`

Let `lambda=pa`, so `0<lambda<1`.  There is a unique normalized convergent Schröder function
`Phi` near zero:

```text
Phi(0)=0,              Phi'(0)=1,
F_(p,a)(Phi(z))=Phi(lambda z).                                   (8)
```

The Becker--Bergweiler classification states that a DA Schröder function of a rational map of
degree at least two can occur only when the underlying fixed point is repelling.  Here zero is
attracting.  Consequently

```text
Phi is hypertranscendental over C(z).                             (9)
```

This deduction requires no global critical-portrait analysis: finite-temperature attenuation has
placed the physical fixed point in a regime forbidden to every DA Schröder function.

### II. Bethe transition: `a=1/p`

At criticality, zero is a nontrivial parabolic fixed point.  Indeed,

```text
F_(p,1/p)(y)
  = y - ((p^2-1)/(3p^2)) y^3 + O(y^5),                           (10)
```

and the cubic coefficient is nonzero for `p>=2`.  The Leau--Fatou theorem supplies attracting and
repelling petals.  On each petal there is an analytic Abel coordinate `A` satisfying

```text
A(F_(p,1/p)(y))=A(y)+1.                                         (11)
```

Becker--Bergweiler prove that every Abel function of a rational map of degree at least two is
hypertranscendental.  Hence every petal clock `A` is HT.

The exact sectorial continuous iterate and beta are

```text
F_s(y)=A^(-1)(A(y)+s),
beta_crit(y)=1/A'(y).                                            (12)
```

If `beta_crit` were DA, then `A'=1/beta_crit` would be DA; the differential equation for `A'`
would also be an algebraic differential equation for an antiderivative `A`, contradicting the Abel
classification.  Therefore both the exact critical beta and clock are HT on every Leau--Fatou
petal.  This is a **sectorial** theorem; there is no analytic Abel germ through the parabolic fixed
point itself.

### III. Ordered phase: `1/p<a<1`

Define, for `x>=0`,

```text
H(x)=p arctanh(a tanh x)-x.                                      (13)
```

Then `H(0)=0`, `H'(0)=pa-1>0`, and `H(x)->-infinity` as `x->+infinity`.  Moreover

```text
d/dx [p arctanh(a tanh x)]
  = pa (1-tanh^2 x)/(1-a^2 tanh^2 x).                            (14)
```

For `0<a<1`, the right side of `(14)` is strictly decreasing from `pa` to zero: after putting
`u=tanh x`, its derivative with respect to `u>0` has the sign of `-(1-a^2)u`.  Hence `H'` crosses
zero exactly once.  The function `H` first increases and then strictly decreases to minus infinity,
so it has exactly one positive zero `x_*`.  At that zero,

```text
0 < f_(p,a)'(x_*) < 1.                                           (15)
```

Thus `x_*` and `-x_*` are attracting but not superattracting ordered fixed points.  In the rational
coordinate, `y_*=tanh x_*` is a non-superattracting attracting fixed point of `F_(p,a)`.

Zero is now repelling, and its normalized Poincare function again satisfies `(8)`, this time with
`lambda=pa>1`.  If `Phi` were DA, the Ritt--Becker--Bergweiler classification would leave only:

1. power or inverse-power type;
2. signed Chebyshev type;
3. elliptic/Weierstrass type.

The power and inverse-power cases have only superattracting or repelling finite fixed cycles; the
signed Chebyshev cases have no finite attracting fixed point.  This contradicts `(15)`.  The
elliptic/Weierstrass maps have empty Fatou set, again contradicting the attracting ordered basin.
Therefore

```text
Phi is hypertranscendental over C(z).                            (16)
```

### IV. Exact zero-temperature boundary: `a=1`

At zero temperature the edge transfer is noiseless and the map becomes Ritt-integrable.  With

```text
M(w)=(w-1)/(w+1),
```

one has

```text
F_(p,1)=M o (w -> w^p) o M^(-1),
Phi(z)=tanh z,
kappa(y)=arctanh y.                                              (17)
```

The normalized Poincare function, exact beta, and punctured scale clock are explicitly DA:

```text
beta_0T(y)=(log p)(1-y^2) arctanh y,
tau_0T(y)=log(arctanh y)/log p.                                  (18)
```

Thus the sharp HT/DA boundary is not the Bethe critical temperature.  It is the singular
zero-temperature limit where genuine edge attenuation disappears.  At `a=0` (infinite
temperature), the rational map collapses to the constant zero map and carries no nontrivial
invertible scale germ.

## Exact beta, clock, and DA-scheme invariance away from criticality

For `a in (0,1)\{1/p}`, let `Phi` be the local function in `(8)`, `kappa=Phi^(-1)`, and
`lambda=pa`.  The exact beta and exact inward scale clock are

```text
beta_y(y)=(log lambda) kappa(y)/kappa'(y),
tau_y(y)=log(kappa(y))/log(lambda),
tau_y(F_(p,a)(y))=tau_y(y)+1.                                   (19)
```

The general clock-beta equivalence
`../not_new_scientific_knowledge/exact-rg-clock-hypertranscendence-equivalence.md`, together with
`(9)` and `(16)`, proves that both functions in `(19)` are HT.  They are understood on a punctured
local domain for the logarithmic clock.

Because `tanh` and `arctanh` are locally invertible DA germs, this conclusion transports back to
the physical effective field `h` and to every other locally invertible DA boundary-field scheme.
At criticality the same composition argument applies petal by petal to `(11)`--`(12)`.  Therefore
no DA physical reparametrization can erase the all-finite-temperature obstruction.

## Holographic and p-adic meaning

The parent model identifies the generation coordinate with a radial coordinate on an effective
Poincare disk and derives boundary power-law correlations.  When `p` is prime, the branching tree
is the Bruhat--Tits tree and its boundary distance is the p-adic norm used in p-adic AdS/CFT.  The
new conclusion is therefore:

```text
every nonzero finite-temperature edge transfer on the p-adic holographic tree
  forces an HT exact boundary-source-to-radial-scale generator;                 (20)

the thermal transition changes Schroeder geometry into Abel geometry and back,
  but only noiseless zero-temperature branching restores a finite ADE.          (21)
```

This is an exact theorem about the Bethe Ising holographic RG model.  It is **not** a theorem about
a quantum bulk, a continuum boundary CFT, dynamical gravity, cosmological time, or an experimental
material.  The parent paper itself presents the construction as a prototype/toy AdS2/CFT1 and
p-adic AdS/CFT bridge.

## Physical residue and forward conjecture

The theorem isolates a candidate physical mechanism rather than merely attaching HT to a named
model:

```text
exact branching + finite-temperature transfer attenuation
  -> non-Ritt iteration geometry
  -> no finite algebraic-differential exact scale generator.                   (22)
```

The phase transition itself controls which local iteration geometry realizes the obstruction.  The
absence of attenuation at zero temperature removes it exactly.

`[CONJECTURE]` In exact tree tensor networks and holographic RGs whose source recursion is a
degree-at-least-two rational map, a nontrivial noisy transfer channel generically forces an HT radial
scale generator; DA generators occur only on exceptional power/Chebyshev/elliptic loci.  This is
not proved by the Ising family alone.  The next significant theorem must formulate and prove the
transfer-channel hypotheses that exclude all exceptional loci beyond one model.

## Formula-level novelty audit

The audit separated four literatures:

1. Okunishi--Takayanagi derive `(2)`, the Bethe transition, boundary correlations, the effective
   Poincare geometry, and the p-adic-tree interpretation, but do not ask for an exact continuous
   beta/clock or its differential-algebraic status.
2. Becker--Bergweiler/Fernandes classify DA Schröder, Böttcher, and Abel functions, but do not
   apply the classification to this physical recursion or to holographic scale generation.
3. Cayley/Bethe recursion literature studies Gibbs phases, periodic points, Lyapunov exponents,
   modulated phases, and chaos.  The 2022 survey by Akın contains no HT, Abel-clock, or
   differential-algebraic classification of `(5)`.
4. Banerjee--Delporte--Sen--Toriumi (2026) study scalar field theories on the Bethe lattice with
   nonperturbative functional RG and find candidate nontrivial critical behavior.  That is a
   neighboring continuum-field-theory direction, not the exact boundary-field recursion `(2)` and
   not an HT scale-generator theorem.

Formula and conjunction searches included the exact `p arctanh(a tanh h)` recursion, the rational
sum/difference form `(5)`, Bethe/Cayley rational dynamics, `Schroeder`, `Abel`, `beta`,
`hypertranscendence`, and `differential algebra`.  They returned the parent holographic paper and
the separate neighboring literatures, but no prior occurrence of `(7)`--`(21)`.

This is meaningful negative evidence, not a proof of priority.  The formula-level novelty gate is
therefore provisionally passed; a citation-graph and specialist audit remains open before promotion
to publication-ready status.

## Live-corpus overlap audit

The current project corpus was rechecked after the proof because concurrent research added nearby
cards.  `exact-rational-rg-generation-dichotomy.md` already supplies the beta/Poincare equivalence,
rational-cocycle test, and DA-scheme theorem at a **repelling** fixed point.  It therefore supports
the ordered-phase step above but does not contain the attracting high-temperature theorem, the
critical Abel theorem, or the all-temperature/zero-temperature boundary.

The new ultrametric thermal, one-loop resolvent, and de Sitter detector cards obtain HT physical
reporters from Mahler or contractive q-difference constraints.  They concern source spectra and
effective-action/detector observables rather than exact rational RG generation.  They neither
subsume the present theorem nor provide its missing interacting continuum inheritance.

This comparison is a project-overlap check, not part of the external novelty gate.  It confirms
that the present card should reuse the rational-RG dichotomy rather than claim that parent layer as
new, while retaining the high-temperature, critical, and physical boundary assembly as its
candidate delta.

## Anti-theatre and dual gate

The exact recursion, temperature transition, boundary correlations, Poincare-disk coordinate, and
p-adic-tree interpretation are parent physics.  The functional-equation classification is parent
mathematics.  The candidate new theorem is the complete finite-temperature assembly: the
high-temperature attracting-Schröder obstruction, critical sectorial Abel obstruction, ordered
Ritt exclusion, DA-scheme invariant beta/clock conclusion, and exact DA zero-temperature boundary.

The novelty gate is provisionally positive after formula-level search, but not closed.  The
significance gate is positive for an exact theorem inside an established holographic RG model: it
turns temperature into a rigorous discriminator for the differential-algebraic complexity of exact
radial scale.  It is not Fields- or Nobel-level on its own because the model is classical and
tree-based.  That bar requires either the conjectural transfer-channel universality theorem or a
continuum QFT/holographic observable inheritance theorem.

## Lean boundary

The rational family `(5)`, coprimality, all-temperature multiplier, critical nonidentity and cubic
anchor `(10)`, and endpoint anchors are now formalized unconditionally in
`formal/GaloisForLFunctions/HTGeometry/BetheHolographicIsingRG.lean`.  The ordered fixed-point proof
needs real calculus, and the HT conclusions need the external Becker--Bergweiler classification.
No conditional Lean theorem packages those external inputs.  The explicit endpoint Möbius
conjugacy `(17)` remains a formal target.

## Primary sources

- K. Okunishi and T. Takayanagi, *Statistical Mechanics Approach to the Holographic
  Renormalization Group: Bethe Lattice Ising Model and p-adic AdS/CFT*,
  <https://arxiv.org/abs/2310.12601>.
- G. Fernandes, *A survey on the hypertranscendence of the solutions of Schroeder's, Boettcher's
  and Abel's equations*, <https://arxiv.org/abs/2102.12168>.
- L. Di Vizio and G. Fernandes, *A Galoisian proof of Ritt theorem on the differential
  transcendence of Poincare functions*, <https://arxiv.org/abs/2102.08268>.
- H. Akın, *Phase diagrams of lattice models on Cayley tree and chandelier network: a review*,
  <https://arxiv.org/abs/2210.00480>.
- R. Banerjee, N. Delporte, S. Sen, and R. Toriumi, *Critical Phenomena on the Bethe Lattice*,
  <https://arxiv.org/abs/2601.01961>.

## Gates

- [x] Exact parent holographic RG map extracted.
- [x] Global rational physical-field chart derived.
- [x] High-temperature attracting-Schröder HT proved.
- [x] Critical parabolic coefficient and sectorial Abel HT proved.
- [x] Unique non-superattracting ordered fixed point proved.
- [x] Every ordered-phase Ritt-integrable case excluded.
- [x] Exact beta and scale-clock HT proved at every finite positive temperature.
- [x] DA-scheme invariance proved, including petalwise critical invariance.
- [x] Integrable zero-temperature endpoint identified explicitly.
- [x] p-adic-tree scope and non-QFT boundary stated.
- [x] Formula-level novelty search completed with neighboring literatures separated.
- [ ] Citation-graph and specialist priority audit completed.
- [x] Unconditional rational-family algebra and critical cubic anchor formalized in HTGeometry.
- [x] Zero-temperature Möbius conjugacy formalized in HTGeometry (`BetheZeroTemperatureMobiusConjugacy.lean`).
- [ ] Transfer-channel universality theorem proved.
- [ ] Continuum QFT/holographic observable inheritance proved.

## Lean progress

- 2026-07-24 — **Zero-temperature Möbius conjugacy (17) formalized** (gate `Zero-temperature Möbius
  conjugacy formalized in HTGeometry`), in `HTGeometry/BetheZeroTemperatureMobiusConjugacy.lean`
  (unconditional, axioms `[propext, Classical.choice, Quot.sound]`):
  * `betheMobiusM`, `betheMobiusMinv` — the Cayley chart `M(w)=(w-1)/(w+1)` and its inverse
    `M⁻¹(w)=(1+w)/(1-w)`, with `betheMobiusM_betheMobiusMinv : M(M⁻¹ y) = y` (`y ≠ 1`).
  * `betheMobius_conjugacy` — **equation (17)**: `M((M⁻¹ y)^p) = ((1+y)^p - (1-y)^p)/((1+y)^p + (1-y)^p)`,
    i.e. the `p`-th power map conjugated by `M` is exactly the zero-temperature Bethe RG rational map.
  * `betheHolographicIsingRG_one_eq_mobius_conjugacy` — connects it to the corpus RG map at `a=1`:
    `F_{p,1}(y) = betheHolographicIsingNumerator p 1).eval y / (betheHolographicIsingDenominator p 1).eval y
    = M((M⁻¹ y)^p)`.
  This realizes the Ritt-integrable zero-temperature endpoint `F_{p,1} = M ∘ (·^p) ∘ M⁻¹`.  Remaining
  gates (transfer-channel universality, continuum QFT inheritance, citation audit) are non-Lean/paper.

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
