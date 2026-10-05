# Poisson-dust formation compactification, cumulant separation, and equivariant neutrality law

- **ID:** ULF-FCM-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** cofinal attack on ULF-OFCM-2 finite formation polynomial; global formation/properness gate
- **Statement:** Uniformly mass-bounded finite formation packets compactify by adjoining a convolution-exponential dust generator; dust is exactly the linear-only formation cumulant, and every source automorphism transports the compactification information-neutrally.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [GLOBAL FORMATION COMPACTIFICATION] [EXACT PROPERNESS REPAIR] [FUNCTIONAL-EQUATION NEUTRAL] [BRIDGE] [NOVELTY UNVERIFIED] [LEAN-PROVED]

## 1. Why the finite theorem is not globally closed

ULF-OFCM-2 reconstructs a fixed finite source packet from its formation polynomial. Cofinal source
formation has a new limit phenomenon. In any commutative unital Banach algebra,

\[
 \left(1+\frac zN a\right)^N\longrightarrow e^{za}.
 \tag{PDF.1}
\]

Every individual factor tends to the unit, so the factor configuration can converge vaguely to the
empty packet, while the formed law converges to a nontrivial zero-free exponential. A global theory
that adds only countably many ordinary packet factors is therefore not closed and cannot be proper.

The required boundary datum is an infinitesimal **formation dust generator**. This card proves the
complete bounded-mass compactification law and identifies exactly which response degrees can see
the dust.

## 2. Formation algebra

Let `K` be a compact metrizable commutative topological monoid with unit `1`. Let
`M(K)` be the complex finite Borel measures on `K`, with total-variation norm and convolution
`star` induced by the monoid product. Its unit is `delta_1`.

A finite positive packet is a finite list

\[
 A=(\alpha_1,\ldots,\alpha_m),
 \qquad \alpha_j\in\mathcal M_+(K).
\]

Its formation class is the measure-valued polynomial

\[
 \Lambda_A(z)=\mathop{\star}_{j=1}^m(\delta_1+z\alpha_j).
 \tag{PDF.2}
\]

The packet mass is

\[
 |A|_1=\sum_j\|\alpha_j\|=\sum_j\alpha_j(K).
 \tag{PDF.3}
\]

For a positive measure `gamma`, define its convolution exponential

\[
 \operatorname{Exp}_\star(z\gamma)
 =\sum_{r=0}^\infty\frac{z^r}{r!}\gamma^{\star r}.
 \tag{PDF.4}
\]

The series converges in total variation for every complex `z`.

We use the compact-open weak topology on measure-valued entire functions: `F_n -> F` when, for
every `f in C(K)` and every `R>0`,

\[
 \sup_{|z|\le R}\left|\int f\,d(F_n(z)-F(z))\right|\longrightarrow0.
 \tag{PDF.5}
\]

## 3. Infinitesimal packet lemma

### Lemma 3.1 -- triangular-array exponential limit

Let `B` be a commutative unital Banach algebra. For each `N`, let
`a_{N,1},...,a_{N,m_N}` commute and satisfy

\[
 \sum_j\|a_{N,j}\|\le C,
 \qquad
 \max_j\|a_{N,j}\|\longrightarrow0,
 \qquad
 \sum_j a_{N,j}\longrightarrow a
 \tag{PDF.6}
\]

in norm. Then, uniformly for `z` in compact subsets of `C`,

\[
 \boxed{
 \prod_j(1+z a_{N,j})\longrightarrow e^{za}.}
 \tag{PDF.7}
\]

#### Proof

Fix `R`. For large `N`, `R max_j ||a_{N,j}|| <= 1/2`, so the norm-convergent logarithm gives

\[
 \log(1+za_{N,j})=za_{N,j}+r_{N,j}(z),
 \qquad
 \|r_{N,j}(z)\|\le 2R^2\|a_{N,j}\|^2.
 \tag{PDF.8}
\]

Therefore

\[
 \sup_{|z|\le R}\left\|
 \sum_j\log(1+za_{N,j})-z\sum_j a_{N,j}
 \right\|
 \le 2R^2 C\max_j\|a_{N,j}\|\longrightarrow0.
 \tag{PDF.9}
\]

Commutativity identifies the product with the exponential of the sum of logarithms. Continuity of
the Banach-algebra exponential, uniformly on bounded sets, proves `(PDF.7)`. QED.

The special case `a_{N,j}=a/N`, `1 <= j <= N`, proves `(PDF.1)`.

## 4. Global compactification theorem

### Theorem 4.1 -- Poisson-dust subsequential compactification

Fix `C<infinity`. Let `A_N=(alpha_{N,1},...,alpha_{N,m_N})` be any sequence of finite positive
packets on `K` such that

\[
 |A_N|_1\le C.
 \tag{PDF.10}
\]

Then a subsequence admits:

- a countable packet `(alpha_1,alpha_2,...)` of positive measures with
  `sum_j ||alpha_j|| <= C`;
- a positive dust measure `gamma`;
- the mass conservation law

\[
 \boxed{
 \|\gamma\|+\sum_{j=1}^\infty\|\alpha_j\|\le C;}
 \tag{PDF.11}
\]

such that

\[
 \boxed{
 \Lambda_{A_N}(z)\longrightarrow
 \operatorname{Exp}_\star(z\gamma)star
 \mathop{\star}_{j=1}^\infty(\delta_1+z\alpha_j)}
 \tag{PDF.12}
\]

in the compact-open weak topology.

The infinite product in `(PDF.12)` converges in total variation uniformly on compact `z`-sets.

#### Proof

Order each packet by decreasing mass and pad it with zero measures. For each fixed `j`, compactness
of the positive-measure ball on compact `K` gives a diagonal subsequence

\[
 \alpha_{N,j}\Longrightarrow\alpha_j
 \tag{PDF.13}
\]

weakly. Testing against `1` shows convergence of masses. Fatou's inequality on finite partial sums
gives `sum_j ||alpha_j|| <= C`.

The total first-formation measures

\[
 \Gamma_N=\sum_j\alpha_{N,j}
\]

also lie in the weakly compact positive-measure ball of mass `C`. Pass to a further subsequence with
`Gamma_N => Gamma`. For every `J`, positivity gives

\[
 \sum_{j\le J}\alpha_j\le\Gamma.
\]

Hence the total-variation sum `sum_j alpha_j` exists and

\[
 \gamma=\Gamma-\sum_{j=1}^\infty\alpha_j
 \tag{PDF.14}
\]

is positive. Equation `(PDF.11)` follows by evaluating at `K`.

For fixed `J`, split the formation into its first `J` factors and its tail. Since the masses are
ordered,

\[
 \max_{j>J}\|\alpha_{N,j}\|\le\frac{C}{J+1}.
 \tag{PDF.15}
\]

For `J` large compared with a fixed `R`, the logarithm estimate from Lemma 3.1, applied uniformly
in `N`, gives

\[
 \sup_{|z|\le R}\left\|
 \mathop{\star}_{j>J}(\delta_1+z\alpha_{N,j})
 -\operatorname{Exp}_\star\left(z\sum_{j>J}\alpha_{N,j}\right)
 \right\|
 \le \varepsilon_J(R),
 \tag{PDF.16}
\]

where `epsilon_J(R) -> 0`. One may take a constant multiple of
`R^2 C^2 (J+1)^{-1} exp(RC)`.

For fixed `J`, weak convergence on compact `K` is preserved by finite convolution. It is also
preserved by the convolution exponential under the uniform mass bound, because every convolution
power converges weakly and the exponential series has the common total-variation majorant
`exp(RC)`. Thus the `N`-limit of the approximant in `(PDF.16)` is

\[
 \mathop{\star}_{j\le J}(\delta_1+z\alpha_j)star
 \operatorname{Exp}_\star\left(
 z\left(\gamma+\sum_{j>J}\alpha_j\right)\right).
 \tag{PDF.17}
\]

Finally `sum_j ||alpha_j||<infinity` makes the infinite product in `(PDF.12)` normally convergent.
Applying the same tail estimate to the limiting tail shows that `(PDF.17)` converges to `(PDF.12)`
as `J -> infinity`, uniformly after testing against any `f in C(K)` and uniformly for
`|z|<=R`. QED.

## 5. Converse realization and closure classification

### Theorem 5.1 -- every dust boundary is a packet limit

Let `gamma,alpha_1,alpha_2,...` be positive measures satisfying `(PDF.11)`. Then the decorated
formation in `(PDF.12)` is a compact-open weak limit of finite packets of mass at most `C`.

#### Proof

For integers `J,M`, take the packet

\[
 A_{J,M}=left(
 \alpha_1,\ldots,\alpha_J,
 \underbrace{\gamma/M,\ldots,\gamma/M}_{M\text{ copies}}
 \right).
 \tag{PDF.18}
\]

Its mass is at most `C`. For fixed `J`, Lemma 3.1 gives

\[
 \Lambda_{A_{J,M}}(z)\longrightarrow
 \left(\mathop{\star}_{j\le J}(\delta_1+z\alpha_j)\right)star
 \operatorname{Exp}_\star(z\gamma)
\]

as `M -> infinity`. Then let `J -> infinity` and choose a diagonal sequence. QED.

### Corollary 5.2 -- exact properness repair

For every `C`, the closure of finite packet formations with mass at most `C` is exactly the class
of decorated formations `(PDF.12)` satisfying `(PDF.11)`. This closure is compact in the
compact-open weak topology.

The uncompleted finite-packet moduli is not closed, hence cannot provide the required global
properness. Adjoining dust gives the exact bounded-mass compactification.

#### Proof

Theorems 4.1 and 5.1 identify the sequential closure. On compact metrizable `K`, bounded
measure balls are metrizable in the weak topology. On the uniformly bounded formation family

\[
 \sup_{|z|\le R}\|\Lambda_A(z)\|\le e^{RC},
\]

the compact-open weak topology is metrized by countable dense families of test functions, radii,
and complex parameters. Sequential compactness is therefore compactness. QED.

## 6. Formation cumulants: exact dust separation

Near `z=0`, use the formal or norm-convergent convolution logarithm. For the decorated formation
`F`,

\[
 \log_\star F(z)
 =z\gamma+
 \sum_{j=1}^\infty\log_\star(\delta_1+z\alpha_j).
 \tag{PDF.19}
\]

Thus

\[
 \boxed{
 \log_\star F(z)
 =z\left(\gamma+\sum_j\alpha_j\right)
 +\sum_{r=2}^\infty
 \frac{(-1)^{r+1}z^r}{r}
 \left(\sum_j\alpha_j^{\star r}\right).}
 \tag{PDF.20}
\]

All coefficient sums converge in total variation. Therefore:

- the first cumulant is the conserved total infinitesimal formation

\[
 C_1=\gamma+\sum_j\alpha_j;
 \tag{PDF.21}
\]

- for every `r>=2`,

\[
 \boxed{
 C_r=\frac{(-1)^{r+1}}r\sum_j\alpha_j^{\star r},}
 \tag{PDF.22}
\]

and dust contributes nothing.

This is the exact new conservation law: cofinal rank can transmute into a linear-only formation
generator while every nonlinear collision response remains atomic. A theory based only on zeros,
determinants, pair collisions, or higher cumulants can therefore miss nonzero cofinal history.

## 7. Anchor-separated global reconstruction

The compactification need not be uniquely decorated without a separation law. On the literal
multiplicative source monoid `K=[0,1]`, one sufficient source-normal condition is exact and testable.

For a positive measure `alpha`, define its Mellin character

\[
 \chi_t(\alpha)=\int_0^1x^t\,d\alpha(x),
 \qquad t>0.
 \tag{PDF.23}
\]

### Theorem 7.1 -- anchor-separated decorated reconstruction

Suppose two decorated formations on `[0,1]` satisfy `(PDF.11)`, every atomic factor is nonzero and
has no atom at `0`, and for some `t_0>0` the values

\[
 \{\chi_{t_0}(\alpha_j)\}_j
\]

are pairwise distinct within each formation. If their measure-valued entire formation functions
are equal, then their atomic factor multisets are equal and their dust measures are equal.

#### Proof

Apply `chi_t`, a continuous convolution character, to the formation:

\[
 \chi_t(F(z))
 =\exp(z\chi_t(\gamma))
  \prod_j\left(1+z\chi_t(\alpha_j)\right).
 \tag{PDF.24}
\]

At `t=t_0`, absolute summability makes this a genus-zero scalar product. Its nonzero factors give
all zeros, namely

\[
 z_j=-\chi_{t_0}(\alpha_j)^{-1}.
\]

They are simple by anchor separation and locally finite because the character values are summable
and tend to zero. Equality of the scalar entire functions therefore matches the atomic factors by
their `t_0` anchors.

Fix one matched zero and a small disk containing no other zero. For real `t` near `t_0`, continuity,
the tail mass bound, and the simple-zero implicit-function theorem give a unique zero in that disk.
Equality of `(PDF.24)` forces

\[
 \chi_t(\alpha_j)=\chi_t(\beta_j)
\]

near `t_0`. Both sides extend holomorphically to `Re t>0`. The identity theorem and Laplace
uniqueness after `x=exp(-u)` give `alpha_j=beta_j`. This holds for every matched factor.

Finally the first cumulant `(PDF.21)` is determined by `F`. Subtracting the now-equal sum of atomic
factors gives `gamma`. QED.

The zero-atom exclusion is load-bearing because positive Mellin characters annihilate an atom at
the absorbing zero. It is exactly the positive-part condition produced by the finite reconstruction
theorem before zero-mass restoration. Anchor separation is sufficient, not claimed necessary. Its
role is to prevent characterwise root matchings from permuting as the test parameter moves.

## 8. Functional-equation action is information-neutral

Let `A:K->K` be a continuous monoid automorphism fixing the unit. Pushforward is an isometric
convolution-algebra automorphism:

\[
 A_*(\mu\star\nu)=A_*\mu\star A_*\nu,
 \qquad
 \|A_*\mu\|=\|\mu\|.
 \tag{PDF.25}
\]

### Theorem 8.1 -- equivariant lift through the compactification

The action on finite packets has the unique coefficientwise extension

\[
 \boxed{
 (\gamma,\{\alpha_j\})
 \longmapsto
 (A_*\gamma,\{A_*\alpha_j\}),}
 \tag{PDF.26}
\]

and

\[
 A_*F(z)
 =\operatorname{Exp}_\star(zA_*\gamma)\star
  \mathop{\star}_j(\delta_1+zA_*\alpha_j).
 \tag{PDF.27}
\]

It preserves the mass filtration, the atomic/dust layer, every cumulant degree, total variation,
and all `f`-divergences between normalized positive formations for which the divergence is defined.
If `A^2=id`, the lifted action is involutive.

#### Proof

Pushforward commutes with finite convolution, norm-convergent series, infinite normally convergent
products, and weak limits. Equation `(PDF.27)` follows. Bijectivity of `A` makes pushforward a
total-variation isometry and preserves Radon--Nikodym density ratios under change of variables, hence
all defined `f`-divergences. Equations `(PDF.21)--(PDF.22)` transport coefficientwise. QED.

Thus a functional equation can move or exchange a completed formation but cannot erase its dust,
create nonlinear information from it, or select dust `=0`. The existing common-recovery kernel lift
is information-neutral for the same structural reason: an invertible source action transports the
complete generated law. Selection needs an independent properness/current law, not reflection
alone.

## 9. Two-sided positive-dust selection

The compactification supplies an exact selection mechanism once source formation makes the physical
parameter additive at the dust layer.

### Theorem 9.1 -- positive two-sided formation groups are trivial

Let `V` be a real vector space with a pointed cone `V_+`, and let

\[
 \gamma:(\mathbb R,+)\longrightarrow(V,+)
 \tag{PDF.28}
\]

be a group homomorphism. If `gamma_u in V_+` for every physically admitted `u`, and admission is
closed under `u |-> -u`, then

\[
 \boxed{\gamma_u=0}
 \tag{PDF.29}
\]

for every admitted `u`.

In particular this applies to the cone of positive finite measures. If an order-preserving
functional-equation involution satisfies

\[
 A_*\gamma_u=\gamma_{-u},
 \tag{PDF.30}
\]

then the functional equation transports the two positive legs information-neutrally, while
additive dust fusion forces their common value to vanish. If a source reporter calibrates the dust
faithfully, for example

\[
 \ell(\gamma_u)=c u,
 \qquad c\ne0,
 \tag{PDF.31}
\]

then the only admitted displacement is `u=0`.

#### Proof

Additivity gives `gamma_0=0` and

\[
 \gamma_{-u}=-\gamma_u.
\]

Both sides are admitted and therefore lie in `V_+`. Hence
`gamma_u in V_+ cap (-V_+)={0}` by pointedness. Equation `(PDF.31)` then gives `u=0`.
Equation `(PDF.30)` types the functional-equation transport but is not needed to manufacture the
sign: the sign is forced by the group law. QED.

### Why this is not a positivity tautology

Positive one-sided convolution semigroups are abundant. Positive two-sided **groups** are what the
pointed cone forbids. The three independent laws are:

1. cofinal packet formation produces an additive dust generator;
2. functional equation/reversibility admits both `u` and `-u` without information loss;
3. source formation places both legs in the positive cone.

Delete any one and the conclusion fails. A one-sided semigroup can carry nonzero dust; an
unconstrained signed group can carry nonzero odd dust; a noninvertible observer can erase one leg.

This is an exact abstract selection theorem, not yet an RH proof. The remaining arithmetic theorem
must construct, before zero specialization, a coefficient-faithful map from physical displacement
to the cofinal dust layer, prove additive fusion, and provide a nonzero calibration such as
`(PDF.31)`.

## 10. Hostile countermodels and sharp scope

1. **Finite packets are not closed.** `(PDF.1)` is the explicit counterexample.
2. **Zeros do not see dust.** Every scalar character sends the dust factor to a zero-free
   exponential. Root reconstruction alone loses `gamma`.
3. **Higher collisions do not see dust.** Equation `(PDF.22)` makes the loss exact in every degree
   `r>=2`.
4. **First response does not separate dust from atoms.** Only their sum appears in `(PDF.21)`.
   Full formation data or an anchor law is required.
5. **Positivity is load-bearing for compactness.** Signed factors can have unbounded cancellation
   while total first response stays bounded.
6. **Uniform mass is load-bearing.** Without `(PDF.10)`, neither normal-family bounds nor a compact
   formation closure follows.
7. **Anchor separation is load-bearing only for Theorem 7.1.** Compactification and cumulant laws
   need no separation.
8. **Zero-free atomic support is load-bearing only for Theorem 7.1.** Mellin characters cannot
   reconstruct how much of one atomic factor sits at the absorbing zero. The global compactification
   itself retains that boundary mass.
9. **An automorphism is information-neutral, not selective by itself.** A noninvertible observer can erase
   data, but that is a different law and must be typed separately.
10. **Two-sided positivity needs additive dust fusion.** An arbitrary positive family
    `u |-> gamma_u` need not be linear or additive and need not vanish.
11. **No RH theorem is asserted.** A source realization must identify the arithmetic cofinal packet,
   prove a uniform formation-mass/action bound, and derive a law excluding or calibrating the dust
   generator before specialization at zeros.

## 11. Cross-organ prediction

Any cofinal route whose finite apertures admit the same formation-polynomial grammar must exhibit
exactly one of three behaviors:

1. **mass escape:** no bounded formation compactification;
2. **atomic persistence:** a countable normally convergent packet remains visible in nonlinear
   cumulants;
3. **dust transmutation:** vanishing factors survive only in the linear formation current.

Therefore a purported cofinal theorem based solely on determinant zeros, pairwise curvature,
Hankel minors, or higher collision tensors is incomplete until it also controls the linear dust
current. This prediction is route-independent and falsifiable.

## 12. Parent and significance audit

Classical parents include Banach-algebra infinite products, Weierstrass factorization,
Poisson/compound-Poisson generating functions, triangular-array laws of small numbers,
Lévy--Khintchine separation, and weak compactness of finite measures. For direct adjacent results,
Chigansky--Klebaner prove
[compound-Poisson convergence for triangular arrays](https://arxiv.org/abs/1110.5381), while
Barbour--Johnson--Kontoyiannis--Madiman study
[compound-Poisson approximation through information functionals](https://arxiv.org/abs/1004.3692).
Those ingredients are occupied.

The field-level delta is their exact coupling to generated formation packets:

- bounded packet mass has a classified compactification;
- cofinal loss is a positive linear-only dust generator, not an unnamed topology defect;
- nonlinear response degrees exactly separate persistent atoms from dust;
- source automorphisms, including functional-equation involutions, preserve the decomposition and
  are therefore selection-neutral.

Current literature search found no exact theorem stated in this measure-valued formation language.
This is not a priority proof. Keep `[BRIDGE] [NOVELTY UNVERIFIED]`.

## 13. Use for the RH programme

The theorem changes the final gate. It is no longer enough to show that every finite prime packet is
reconstructed or that every nonlinear defect vanishes. A cofinal proof must establish all three:

1. a source-generated bound giving `(PDF.10)` or its renormalized replacement;
2. identification of the arithmetic limit's atomic factors and dust current;
3. a source proof that physical displacement forms the positive two-sided additive dust family of
   Theorem 9.1, with a faithful nonzero calibration.

This isolates a concrete missing mechanism: **linear-dust exclusion under global formation
properness**. It is stronger than another source-native nullhomology request and is not tied to one
existing RH route.

## Gates

- [x] 0 -> 1: explicit cofinal counterexample and survivor mechanism
- [x] 1 -> 2: compactification, converse, cumulant, reconstruction, equivariance, positive two-sided selection, and scope proofs closed
- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.CompactMonoidMeasureAlgebra`, `GaloisForLFunctions.HTGeometry.BanachTriangularExponential`, `GaloisForLFunctions.HTGeometry.WeakStarFormationContinuity`, `GaloisForLFunctions.HTGeometry.PoissonDustCompactification`, `GaloisForLFunctions.HTGeometry.FormationCompactOpenTopology`, `GaloisForLFunctions.HTGeometry.BanachLogSeries`, `GaloisForLFunctions.HTGeometry.FormationCumulants`, `GaloisForLFunctions.HTGeometry.MellinAnchorReconstruction`, `GaloisForLFunctions.HTGeometry.FormationEquivariance`, `GaloisForLFunctions.HTGeometry.PositiveTwoSidedDustSelection`, `GaloisForLFunctions.HTGeometry.FormationScopeCountermodels`, `GaloisForLFunctions.HTGeometry.HalfLineLaplaceTomography`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only
- [ ] 3 -> 4: literal arithmetic realization and independent priority audit


## Lean certificate

Modules `GaloisForLFunctions.HTGeometry.CompactMonoidMeasureAlgebra` (the measure algebra),
`GaloisForLFunctions.HTGeometry.BanachTriangularExponential` (Lemma 3.1),
`GaloisForLFunctions.HTGeometry.WeakStarFormationContinuity` (positive balls, diagonal extraction,
weak-* continuity of products and exponentials), `GaloisForLFunctions.HTGeometry.PoissonDustCompactification`
(Theorems 4.1, 5.1, sequential Corollary 5.2), `GaloisForLFunctions.HTGeometry.FormationCompactOpenTopology`
(the compact-open weak topology, Corollary 5.2), `GaloisForLFunctions.HTGeometry.BanachLogSeries` and
`GaloisForLFunctions.HTGeometry.FormationCumulants` (§6), `GaloisForLFunctions.HTGeometry.MellinAnchorReconstruction`
(§7), `GaloisForLFunctions.HTGeometry.FormationEquivariance` (§8),
`GaloisForLFunctions.HTGeometry.PositiveTwoSidedDustSelection` (§9) and
`GaloisForLFunctions.HTGeometry.FormationScopeCountermodels` (§10).  Corpus input:
`GaloisForLFunctions.HTGeometry.HalfLineLaplaceTomography` (Laplace determinacy).  All names below are in
`GaloisForLFunctions.HTGeometry`.  `K` is a compact Hausdorff second-countable (= compact metrizable)
commutative monoid with continuous multiplication and its Borel σ-algebra; `M(K) = MeasureAlgebra K`
(complex Radon measures as `C(K, ℂ)*`, total variation = dual norm, convolution
`(Φ ⋆ Ψ)(f) = Φ(x ↦ Ψ(y ↦ f(xy)))`, `δ_1 = 1`); `M_+(K)` is `MeasureAlgebra.IsPositive`, identified with
finite positive Borel measures by `MeasureAlgebra.IsPositive.exists_ofMeasure_eq` (Riesz–Markov–Kakutani);
`Exp_⋆ = NormedSpace.exp`; the packet `A` is `A : Fin m → MeasureAlgebra K`, the countable packet
`α : ℕ → MeasureAlgebra K`.  Banach algebras are unital with `‖1‖ = 1`.  For `K = [0, 1]` (§7) the
monoid is `unitInterval` with multiplication.

| Claim | Lean declaration |
|-|-|
| §2 `M(K)` is a commutative unital Banach algebra under convolution | `MeasureAlgebra`, `MeasureAlgebra.mul_apply`, `MeasureAlgebra.one_apply`, `MeasureAlgebra.norm_mul_le'`, `MeasureAlgebra.mul_comm'`, `MeasureAlgebra.ofMeasure_measureConv`, `MeasureAlgebra.norm_ofMeasure` |
| (PDF.1) `(1 + z a/N)^N → e^{za}` uniformly on compact sets | `FormationDust.tendstoUniformlyOn_one_add_div_pow` |
| (PDF.2)–(PDF.3) formation `Λ_A(z) = ⋆_j (δ_1 + z α_j)`, mass `|A|_1 = Σ_j ‖α_j‖ = Σ_j α_j(K)` | `FormationDust.formation`, `FormationDust.packetMass`, `FormationDust.IsPositive.norm_eq` |
| (PDF.4) `Exp_⋆(zγ) = Σ_r z^r γ^{⋆r}/r!` converges in total variation for every `z` | `NormedSpace.exp_series_hasSum_exp'`, `FormationDust.norm_exp_le` |
| (PDF.5) the compact-open weak topology | `FormationDust.FormSpace`, `FormationDust.testMap`, `FormationDust.FormConv`, `FormationDust.WeakUnifOn`, `FormationDust.tendsto_formSpace_iff_formConv` |
| Lemma 3.1, (PDF.6)–(PDF.7) triangular-array exponential limit, uniformly on `|z| ≤ R` | `FormationDust.tendstoUniformlyOn_prod_one_add`, `FormationDust.norm_prod_one_add_sub_exp_le`, `FormationDust.norm_exp_sub_exp_le` |
| Theorem 4.1, (PDF.10)–(PDF.12) Poisson-dust subsequential compactification with `‖γ‖ + Σ_j ‖α_j‖ ≤ C` | `FormationDust.poissonDust_compactification`, `FormationDust.decorated` |
| the infinite product in (PDF.12) converges in total variation uniformly on compact `z`-sets | `FormationDust.multipliable_formation`, `FormationDust.norm_tprod_sub_prod_range_le` |
| (PDF.13) weak compactness of the positive ball and the diagonal subsequence | `FormationDust.isSeqCompact_positiveBall`, `FormationDust.exists_diagonal_positive`, `FormationDust.exists_diagonal_subseq` |
| masses converge, positivity passes to limits, (PDF.14) `γ = Γ - Σ_j α_j ≥ 0` | `FormationDust.tendsto_norm_of_isPositive`, `FormationDust.isPositive_of_tendsto`, `FormationDust.IsPositive.norm_add`, `FormationDust.norm_sum_of_isPositive` |
| (PDF.15) ordered packets: `‖α_{N,j}‖ ≤ C/(j+1)` | `FormationDust.padded`, `FormationDust.norm_padded_le`, `FormationDust.padded_antitone`, `FormationDust.prod_range_padded` |
| (PDF.16) the tail estimate `e^{3RC} R² C²/(J+1)` uniformly in `N` | `FormationDust.norm_prod_range_sub_le`, `FormationDust.norm_formation_sub_le`, `FormationDust.norm_decorated_sub_le` |
| (PDF.17) finite convolution and the exponential preserve weak convergence under the mass bound | `FormationDust.WeakUnifOn.mul`, `FormationDust.weakUnifOn_prod_range`, `FormationDust.weakUnifOn_exp`, `FormationDust.WeakUnifOn.uniform_compact`, `FormationDust.IsPositive.mul` |
| Theorem 5.1, (PDF.18) every decorated formation is a norm limit, uniformly on compact sets, of positive packets `(α_1, …, α_J, γ/M, …, γ/M)` of mass `≤ C` | `FormationDust.decorated_isLimit`, `FormationDust.realizingPacket`, `FormationDust.norm_formation_realizingPacket_sub_le`, `FormationDust.tendstoUniformlyOn_formation_realizingPacket`, `FormationDust.formConv_of_tendstoUniformlyOn` |
| Corollary 5.2, the closure of the finite formations of mass `≤ C` is exactly the class of decorated formations obeying (PDF.11) | `FormationDust.closure_packetFormationSet`, `FormationDust.mem_decoratedSet_iff`, `FormationDust.mem_decoratedSet_of_formConv`, `FormationDust.packetFormationSet_subset_decoratedSet`, `FormationDust.formation_eq_decorated` |
| Corollary 5.2, this closure is compact; `sup_{|z|≤R} ‖Λ(z)‖ ≤ e^{RC}`; the topology is metrized on it by countably many test functions and radii | `FormationDust.isCompact_decoratedSet`, `FormationDust.decoratedSet_seqCompact`, `FormationDust.norm_decorated_le`, `FormationDust.uniformity_decoratedSpace_eq` |
| Corollary 5.2, the uncompleted finite-packet moduli is not closed | `FormationDust.not_isClosed_packetFormationSet`, `FormationDust.formation_ne_exp` |
| (PDF.19) the convolution logarithm `log_⋆ F(z) = zγ + Σ_j log_⋆(δ_1 + zα_j)`, norm-convergent near `0`, with `Exp_⋆(log_⋆ F(z)) = F(z)` | `FormationDust.formationLog`, `FormationDust.exp_formationLog`, `FormationDust.logSeries`, `FormationDust.exp_logSeries`, `FormationDust.summable_logSeries_smul` |
| (PDF.20) `log_⋆ F(z) = z(γ + Σ_j α_j) + Σ_{r≥2} (-1)^{r+1} z^r/r Σ_j α_j^{⋆r}`, all coefficient sums converging in total variation | `FormationDust.hasSum_cumulant`, `FormationDust.summable_norm_pow`, `FormationDust.norm_formationLog_le` |
| (PDF.21)–(PDF.22) `C_1 = γ + Σ_j α_j`, `C_r = (-1)^{r+1}/r Σ_j α_j^{⋆r}` for `r ≥ 2`; dust contributes nothing for `r ≥ 2` | `FormationDust.cumulant`, `FormationDust.cumulant_one`, `FormationDust.cumulant_of_two_le`, `FormationDust.cumulant_dust_invariant`, `FormationDust.logCoeff` |
| the cumulants are determined by the formation (the conservation law) | `FormationDust.cumulant_eq_of_decorated_eq`, `FormationDust.total_and_powerSums_eq_of_decorated_eq`, `FormationDust.eq_zero_of_exp_eq_one`, `FormationDust.eq_of_hasSum_pow_smul` |
| (PDF.23) Mellin characters `χ_t(α) = ∫ x^t dα`, continuous convolution characters of `M([0, 1])` | `FormationDust.powFun`, `FormationDust.mellinChar`, `FormationDust.mellin`, `FormationDust.continuous_mellinChar`, `FormationDust.rightTransform_powFun`, `FormationDust.mellin_ofMeasure_real` |
| Theorem 7.1, anchor-separated decorated reconstruction: equal formations with zero-free atoms and `χ_{t₀}`-distinct nonzero atoms have the same atoms (bijectively) and the same dust | `FormationDust.anchor_reconstruction` |
| (PDF.24) `χ_t(F(z)) = exp(z χ_t(γ)) Π_j (1 + z χ_t(α_j))`; its zeros are `-χ_t(α_j)^{-1}` | `FormationDust.mellinChar_decorated`, `FormationDust.mellinChar_decorated_eq_zero_iff`, `FormationDust.tprod_one_add_eq_zero_iff`, `FormationDust.exists_mellinChar_eq` |
| positive anchors of zero-free atoms; local matching of a zero near `t₀` with a unique atom | `FormationDust.mellin_pos`, `FormationDust.mellin_ofMeasure_pos`, `FormationDust.exists_eventually_mellin_eq`, `FormationDust.continuousAt_mellin_real`, `FormationDust.injOn_of_anchor` |
| holomorphy on `Re t > 0`, identity theorem, Laplace uniqueness after `x = e^{-u}` | `FormationDust.differentiableOn_mellin_ofMeasure`, `FormationDust.mellin_eqOn_of_eventually_eq`, `FormationDust.frequently_eq_of_eventually_real`, `FormationDust.measure_eq_of_moments_succ`, `FormationDust.eq_of_mellin_eventually_eq`, `FormationDust.range_compactify`, `LaplaceTomography.measure_eq_of_laplace_eq_succ` |
| the first cumulant then gives `γ` | `FormationDust.anchor_reconstruction`, `FormationDust.total_and_powerSums_eq_of_decorated_eq` |
| (PDF.25) pushforward along a continuous monoid automorphism is an isometric convolution-algebra automorphism | `FormationDust.push`, `FormationDust.pushAlgHom`, `FormationDust.norm_push_aut`, `FormationDust.push_symm_push`, `FormationDust.push_push_symm`, `FormationDust.continuous_pushAlgHom` |
| Theorem 8.1, (PDF.26)–(PDF.27) the coefficientwise lift `A_* F(z) = Exp_⋆(z A_*γ) ⋆ Π_j (δ_1 + z A_*α_j)` | `FormationDust.pushAlgHom_decorated`, `FormationDust.pushAlgHom_formation`, `FormationDust.pushAlgHom_exp` |
| Theorem 8.1, the lift is the unique continuous extension of the packet action | `FormationDust.eqOn_pushForm_of_continuous`, `FormationDust.pushForm`, `FormationDust.uniformContinuous_pushForm`, `FormationDust.testMap_pushForm` |
| Theorem 8.1, it preserves the mass filtration, positivity, the atomic/dust layers, every cumulant degree and total variation | `FormationDust.push_mem_decoratedSet`, `FormationDust.mass_push_aut`, `FormationDust.isPositive_push`, `FormationDust.pushAlgHom_cumulant`, `FormationDust.norm_push_aut` |
| Theorem 8.1, all `f`-divergences between (normalized) positive formations are preserved | `FormationDust.fDivergence`, `FormationDust.fDivergence_map`, `FormationDust.fDivergence_push`, `FormationDust.toFiniteMeasure_push`, `FormationDust.push_ofMeasure`, `FormationDust.push_normalize`, `FormationDust.isPositive_decorated` |
| Theorem 8.1, `A² = id` lifts to an involution | `FormationDust.push_involutive` |
| Theorem 9.1, (PDF.28)–(PDF.29) positive two-sided additive dust families vanish on a pointed cone | `FormationDust.eq_zero_of_pointedCone`, `FormationDust.PointedCone.eq_zero_of_mem_neg_mem` |
| Theorem 9.1 for the cone of positive measures | `FormationDust.eq_zero_of_isPositive_of_isPositive_neg`, `FormationDust.dust_eq_zero` |
| (PDF.30) an order-preserving involution exchanging the legs: both vanish | `FormationDust.dust_legs_eq_zero` |
| (PDF.31) a faithful calibration admits only `u = 0` | `FormationDust.eq_zero_of_calibration`, `FormationDust.dust_calibration` |
| §9 independence: one-sided semigroups and signed groups carry dust | `FormationDust.oneSided_dust_ne_zero`, `FormationDust.signed_dust_not_positive`, `FormationDust.linearDust` |
| §10 (1) finite packets are not closed | `FormationDust.not_isClosed_packetFormationSet`, `FormationDust.tendstoUniformlyOn_one_add_div_pow` |
| §10 (2) zeros do not see dust | `FormationDust.character_decorated_eq_zero_iff`, `FormationDust.character_exp`, `FormationDust.massHom` |
| §10 (3) higher collisions do not see dust | `FormationDust.cumulant_dust_invariant` |
| §10 (4) the first response does not separate dust from atoms | `FormationDust.firstCumulant_does_not_separate` |
| §10 (5) positivity is load-bearing (signed packets, bounded first response, no convergent subsequence) | `FormationDust.signedPacket_counterexample`, `FormationDust.not_formConv_of_unbounded` |
| §10 (6) uniform mass is load-bearing | `FormationDust.massPacket_counterexample` |
| §10 (8) zero-free atomic support is load-bearing for Theorem 7.1 | `FormationDust.zeroAtom_counterexample`, `FormationDust.mellinChar_dirac_zero` |
| §10 (9) a noninvertible observer erases data | `FormationDust.constant_observer_erases`, `FormationDust.push_one` |
| §10 (10) a non-additive positive family need not vanish | `FormationDust.constant_dust_ne_zero` |

Lemma 3.1 is proved by the product–exponential comparison
`‖Π(1 + x_i) - exp Σ x_i‖ ≤ e^{2Σ‖x_i‖} Σ ‖x_i‖²` in place of logarithms.  Theorem 7.1 is proved without
positivity of the dust and allows zero atoms in the packets (only the nonzero atoms need distinct anchors and no
mass at `0`).  §10 (7) (separation enters only Theorem 7.1) is witnessed by the hypotheses of
`FormationDust.poissonDust_compactification`, `FormationDust.decorated_isLimit` and `FormationDust.hasSum_cumulant`;
§10 (11), §§11–13 and the scope remarks state what is not claimed.

## Log

- 2026-08-14 -- discovered by attacking cofinal extension of ULF-OFCM-2 rather than postulating a global determinant.
- 2026-08-14 -- compactification, converse realization, cumulant separation, anchor reconstruction, and functional-equation neutrality proved on paper.
- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
