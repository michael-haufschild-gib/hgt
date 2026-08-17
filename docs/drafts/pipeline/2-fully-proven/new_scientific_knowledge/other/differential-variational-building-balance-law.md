# Differential variational-building balance and boundary law

- **ID:** `differential-variational-building-balance-law`
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL DIFFERENTIAL-FIELD THEOREM / FOUNDING HT CONSTRAINT LAW
- **Scientific status:** `[PROVED HERE] [LEAN CORE FORMALIZED] [EXTERNAL NOVELTY PROVISIONAL]`
- **Linear witness:** `../../3-formalized/hypertranscendental-clock-shear-rank-threshold.md`
- **Open successor:** `../../1-in-progress/nonlinear-hypertranscendental-clock-building-completeness.md`
- **Statement:** Every reversible automorphism of a finitely generated differential field acts
  canonically on an affine building attached to its variational Ore module.  The action is
  determinant-balanced.  Consequently reversible differential-order growth has no intermediate
  phase: it is either bounded, or has a positive linear rate and a canonical attracting/repelling
  weighted boundary flag.  Rank one permits only the bounded phase.

## 1. Intrinsic object

Let `C` be a characteristic-zero differential field of constants and let `K/C` be a finitely
differentially generated differential field.  Write `delta` for the derivation and

```text
R_K = K[partial;delta],               partial a = a partial + delta(a)       (1)
```

for the Ore ring of differential operators.  The relative Kähler module `Omega=Omega_(K/C)` has
the canonical connection

```text
nabla(a db)=delta(a) db+a d(delta(b)).                                  (2)
```

Thus `Omega` is a left `R_K`-module.  It is finitely generated because any finite differential
generating tuple for `K/C` supplies `R_K`-generators for `Omega`.

Let `Tor_R(Omega)` be its Ore-torsion submodule and put

```text
M_K = Omega/Tor_R(Omega),
Q_K = Frac(R_K),
V_K = Q_K tensor_(R_K) M_K.                                             (3)
```

Since `R_K` is a left and right Euclidean Ore domain, `M_K` is free of finite rank.  The standard
differential-basis criterion for Kähler differentials gives

```text
rank_(R_K) M_K = dim_(Q_K) V_K = differential-trdeg_C K =: r.            (4)
```

Complete `Q_K` for the discrete valuation `v=-ord_partial`.  The completion is the skew field of
formal pseudodifferential operators

```text
Qhat_K = K((partial^(-1))).                                              (5)
```

The homothety classes of valuation lattices in `Qhat_K^r` form the complete affine building

```text
B_delta(K/C)                                                             (6)
```

of type `A_(r-1)`.  This is the **differential variational building**.  It is made from
observables of the cotangent connection, not from an evolution parameter.

## 2. Variational-building theorem

Let `sigma` be a differential `C`-automorphism of `K`.  It acts on one-forms by

```text
d a |-> d sigma(a).                                                      (7)
```

Because `sigma delta=delta sigma`, equation `(7)` intertwines `(2)`.  It preserves Ore torsion and
therefore induces a valuation-preserving semilinear automorphism

```text
T_sigma : V_K -> V_K.                                                    (8)
```

### Theorem A: canonical balanced action

The assignment

```text
sigma |-> T_sigma                                                        (9)
```

is a functorial action of `Aut_delta(K/C)` by isometries of `B_delta(K/C)`.  It is independent of
all differential generators.

Choose an `R_K`-basis of `M_K`.  In that basis `(8)` has the form

```text
T_sigma(v)=A_sigma sigma(v),             A_sigma in GL_r(R_K).           (10)
```

For the dominant relative-position vector

```text
mu_n=(mu_1(n)>=...>=mu_r(n)) in Z^r                                     (11)
```

between a base valuation lattice and its image under `T_sigma^n`, one has the exact balance law

```text
sum_i mu_i(n)=0                  for every n.                             (12)
```

A new `R_K`-basis replaces `(10)` by twisted conjugacy

```text
A_sigma |-> B^(-1) A_sigma sigma(B),                                    (13)
```

so it conjugates the building isometry and cannot change its translation data.

### Proof

Formula `(7)` is semilinear over `sigma` and commutes with `partial` by `(2)`, hence descends
through `(3)` and extends through `(5)`.  Its inverse is induced by `sigma^(-1)`, proving `(8)` and
`(9)`.  In an `R_K`-basis, both the matrix of `(8)` and the twisted matrix of its inverse have
entries in `R_K`; applying `sigma` to the inverse relation shows that `A_sigma` has a two-sided
inverse in `Mat_r(R_K)`.  This proves `(10)`.

The coefficient action of `sigma` preserves `v` and the valuation ring of `(5)`, so `(10)` acts
isometrically on `(6)`.  The degree of the Dieudonné determinant of every matrix in `GL_r(R_K)` is
zero.  Relative invariant factors add to that degree, proving `(12)`.  The ordinary change-of-basis
calculation gives `(13)`.

## 3. Complete asymptotic phase law

### Theorem B: translation vector and thin boundary

For every `sigma` the limit

```text
lambda_delta(sigma)=lim_(n->infinity) mu_n/n                             (14)
```

exists in the dominant real coweight cone, is independent of the base lattice and of the chosen
differential generators, and obeys

```text
sum_i lambda_i=0.                                                        (15)
```

Exactly one of the following holds.

1. **Bounded phase.** `lambda_delta(sigma)=0`; the isometry `T_sigma` fixes a point of the
   building, and every orbit in `(6)` is bounded.
2. **Boundary phase.** `lambda_delta(sigma) != 0`; the isometry translates a geodesic and has
   canonical attracting and repelling points

   ```text
   xi_+(sigma), xi_-(sigma) in boundary_infinity B_delta(K/C).           (16)
   ```

   These are opposite weighted differential flags.  Positive components of `(14)` are exactly
   balanced by negative components through `(15)`.

There is no parabolic third phase and no unbounded sublinear variational drift.

### Proof

The building in `(6)` is complete and has thick spherical building at infinity.  Semisimplicity of
isometries of complete affine buildings gives the fixed-point/translated-geodesic dichotomy.  In
the fixed-point case, the orbit of any base lattice is bounded, so `(11)/n` tends to zero.  In the
translated-geodesic case, every orbit remains a bounded distance from an axis after projection to
the minimum set.  Vector-valued distance from the orbit to the corresponding axial translation is
therefore `O(1)`; division by `n` gives `(14)`.  All axes of one hyperbolic isometry are parallel,
so their two endpoints give the intrinsic pair `(16)`.  Equation `(15)` follows from `(12)`.

This uses established affine-building geometry; the new mathematical content claimed here is its
source-canonical differential-field realization and the consequences below.

## 4. Exact free-field reconstruction theorem

Now let

```text
K=C<x_1,...,x_r>                                                        (17)
```

be the free differential rational field and define `ord_x(sigma)` as the least `m` such that every
`sigma(x_i)` is rational in the jets `partial^j x_k`, `0<=j<=m`.  The matrix in `(10)` is the
Fréchet Jacobian

```text
J_sigma(i,j)=sum_k partial(sigma(x_i))/partial(x_j^(k)) partial^k.       (18)
```

The differential substitution chain rule is exactly the cocycle law for `(18)`.  Characteristic
zero implies that the highest jet on which a rational function depends has nonzero formal partial
derivative.  Consequently

```text
ord_x(sigma^n)=deg_partial J_(sigma^n)=mu_1(n).                          (19)
```

### Theorem C: intrinsic clock speed

The limit

```text
ell_delta(sigma)=lim_(n->infinity) ord_x(sigma^n)/n                     (20)
```

exists, is unchanged by every differential-birational change of free generators, and equals the
largest component of `(14)`.  Moreover

```text
ell_delta(sigma)=0   iff   the sequence ord_x(sigma^n) is bounded,       (21)
ell_delta(sigma)>0   iff   sigma has the boundary pair (16).             (22)
```

Thus differential-order growth of a reversible finite-rank clock is either bounded or genuinely
linear.  Fekete's lemma alone gives existence of `(20)`; the building theorem supplies the strict
gap `(21)` by excluding unbounded sublinear growth.

For a coordinate change `h`, subadditivity gives the explicit finite overhead

```text
|ord_x(h sigma^n h^(-1))-ord_x(sigma^n)|
  <= ord_x(h)+ord_x(h^(-1)),                                            (23)
```

which proves coordinate invariance of `(20)` directly.

## 5. Sharp rank threshold

`[NO-GO]` If `r=1`, the building has type `A_0`, and `(12)` forces `mu_1(n)=0` for every `n`.
By `(19)`, every scalar differential automorphism and every iterate has order zero.  No scalar HT
field can carry reversible clock displacement, even though its jet tower has infinite algebraic
capacity.

`[POSITIVE THEOREM]` If `r>=2`, balanced displacement is possible.  The proved clock shear

```text
(x,y) |-> (y,x+partial y)                                                (24)
```

has

```text
mu_n=(n,-n),  lambda_delta=(1,-1),  ell_delta=1.                         (25)
```

Hence rank two is the exact first boundary phase.  Reversibility does not erase information: it
moves one observable direction beyond every fixed finite jet window while an opposite direction
pays the determinant balance.

## 6. Interpretation of the founding conjecture

The precise replacement for

```text
hypertranscendence is infinite algebraic clock capacity concentrated on a thin boundary
```

is now:

```text
HT capacity       = unbounded freedom of finite jet packets,
reversible constraint = the semilinear action (9),
clock spectrum    = the balanced vector (14),
thin boundary     = the opposite weighted flags (16).                   (26)
```

The clock is not time.  It is the filtered family of differential observables.  A scale factor, a
zeta observable, or any other proposed physical observable can represent `(26)` only after its
cotangent Ore module and comparison map to `(3)` are constructed source-first.

## 7. External novelty gate

The novelty gate is only against external literature.

Established parent theories include:

- Kähler differential modules over differential fields and the equality between their
  `K[partial]`-rank and differential transcendence degree;
- Fréchet derivatives and coordinate-change formulae for Miura/differential substitutions;
- rational pseudodifferential operators and Dieudonné determinants;
- valuations of matrices over discrete-valuation skew fields;
- affine buildings, Cartan projections, and semisimplicity of their isometries;
- degree growth and algebraic entropy of ordinary birational maps.

Representative primary sources are:

- Lorenzoni--Shadrin--Vitolo, *Miura-reciprocal transformations and localizable Poisson pencils*,
  https://arxiv.org/abs/2301.04475;
- Carpentier--De Sole--Kac, *Some algebraic properties of differential operators*,
  https://arxiv.org/abs/1201.1992;
- Oki, *Computing Valuations of the Dieudonné Determinants*,
  https://arxiv.org/abs/1907.04512;
- Parreau, *Affine buildings: construction by norms and study of isometries*,
  https://doi.org/10.2140/iig.2023.20.471.

Those sources establish the ingredients but, in the targeted exact-statement search performed for
this card, no source was located that constructs `(6)` functorially from a differential field and
then proves the combined laws `(12)`, `(14)`, `(16)`, and `(19)--(22)`.  Searches for differential
Cremona/Miura actions on affine buildings, Kähler--Ore variational buildings, and differential
birational order translation lengths returned no matching theorem.

Novelty is therefore **provisional but live**, not a priority claim.  MathSciNet, zbMATH, and
specialist review in differential algebra, integrable systems, and affine buildings are required
before publication.

## 8. Significance and anti-theatre gate

- `[PASS]` The theorem applies to every finitely differentially generated field, not one named
  special function.
- `[PASS]` It creates a source-canonical invariant of differential automorphism groups and proves a
  sharp bounded/linear phase gap.
- `[PASS]` The scalar no-go has a strict positive successor: balanced rank-two boundary dynamics.
- `[PASS]` The new boundary object is forced by the intrinsic cotangent connection; it is not a
  chosen topology or carrier.
- `[PASS]` The clock-shear model realizes every law with exact reconstruction order.
- `[FAIL if redressed]` Kähler differentials, Fréchet linearization, pseudodifferential operators,
  Dieudonné determinants, and affine buildings separately are parent theory.
- `[PAPER VERDICT]` Conditional only on specialist novelty confirmation, Theorems A--C warrant a
  standalone research paper: they define a new invariant and prove a universal phase theorem.
- `[MEDAL VERDICT]` This is a plausible founding theorem of the proposed field, not yet the
  medal-scale classification.  The medal-scale successor is to extend `(26)` from reversible
  finitely generated cores to arbitrary stable tails and prove algebraic descent/completeness of
  their boundary flags.

## 9. Lean formalization

The existing file
`GaloisForLFunctions.HTGeometry.HypertranscendentalKaehlerClockSymbol` already formalizes the
canonical connection `(2)`, including

```text
kaehlerConnectionDifferential
kaehlerConnectionDifferential_D
kaehlerConnectionDifferential_smul
kaehlerConnectionDifferential_map
```

The cached file
`GaloisForLFunctions.HTGeometry.DifferentialIndependentObservableNet` now formalizes the complete
Fekete/conjugacy kernel of `(20)` and `(23)`:

```text
SubadditiveClockGauge
SubadditiveClockGauge.orbitCost_subadditive
SubadditiveClockGauge.tendsto_normalizedOrbitCost
SubadditiveClockGauge.orbitCost_conjugate_le
SubadditiveClockGauge.orbitCost_le_conjugate
SubadditiveClockGauge.translationLength_conjugate
```

The same module formalizes the exact witness `(24)--(25)` through
`clockShearBackwardFirst_mem_iff`.  The touched file passed direct Lean checking.  No Lake build
was run because its `.olean` cache existed.

Full formalization of `(3)--(16)` requires new mathlib-scale infrastructure for Ore localization,
matrix pseudodifferential valuation, and affine buildings.  The card remains at stage 2 until that
infrastructure and the differential-order instantiation of the abstract gauge are machine-checked.

## 10. RH pressure test only

`[CONJECTURE; NOT AN RH RESULT]` Any claim that spectral incompleteness, continuation failure,
positivity failure, monodromy, and noncanonical boundary conditions are representations of one HT
object must now construct comparison maps from those defects to the single source-defined pair
`(B_delta,lambda_delta)` and preserve `(15)` and `(16)`.  Scalar zeta data alone cannot do this;
at least two transverse variational observables are required.

Critical zeros could be a self-dual degeneracy spectrum only where the attracting and repelling
flags lose transversality in an independently constructed self-dual realization.  Nothing here
proves that realization or RH.

## Gates

- [x] 0 -> 1: intrinsic object, theorem, falsifiers, and exact rank-two witness
- [x] 1 -> 2: complete algebraic/building proof and explicit parent-theory boundary
- [ ] 2 -> 3: Ore localization, balanced Cartan law, and building dichotomy fully formalized
- [ ] 3 -> 4: specialist novelty confirmation and standalone preprint

## Log

- 2026-07-15 -- proved the variational-building action, determinant balance, bounded/linear phase
  gap, canonical boundary pair, and exact free-field order identity.

## Lean progress — the balance law `(12)`, and the state of the lattice model

§9 above is out of date.  The tree now owns the whole lattice model that replaces the affine
building in the proofs of `(11)`--`(15)`:

| Module | Contents |
|---|---|
| `DifferentialOperatorOreField` | the Ore condition for `K[∂;δ]`, the `OreSet` instance, and the skew field `PseudoDiffOp K` of rational pseudodifferential operators as a `DivisionRing` |
| `OperatorLattice` | the integral lattice `R^ι ⊆ Q^ι`, the row lattice of a matrix, its saturation, commensurability of the two, and finite generation of the saturation |
| `OperatorConductorLength` | `satLattice_eq_integralLattice` for square matrices with left independent rows, and `exists_degree_sum_eq_quotDim_conductor`: the conductor length is the sum of the degrees of the elementary divisors |
| `OperatorCartanComparison` | the intrinsic/ambient Cartan prefix comparison and `tendsto_normalized_ambient_cartan`: the normalized Cartan vector converges |
| `DifferentialIndependentObservableNet` | the Fekete/conjugacy kernel `SubadditiveClockGauge` of `(20)`, `(23)` |

`GaloisForLFunctions.HTGeometry.OperatorBalanceLaw` adds `(12)` itself, unconditionally and
axiom-clean:

```text
rowIndep_of_vecMul_inverse                     a two-sided row inverse gives left independent rows
rowSpace_eq_top_of_vecMul_inverse
rowLattice_eq_integralLattice_of_vecMul_inverse
    an operator matrix invertible over K[∂;δ] carries the integral lattice onto itself
quotDim_conductor_eq_zero_of_vecMul_inverse    its conductor is trivial
exists_degree_sum_eq_zero_of_vecMul_inverse
    every elementary divisor has degree zero, so ∑_i μ_i = 0
```

This is `(12)` obtained from the lattice description rather than from Dieudonné determinant theory:
invertibility over the operator ring, not merely over the skew field, is exactly what makes the two
lattices equal, and the conductor length is the total elementary-divisor degree.

What `(12)`, `(14)` and `(15)` still need to reach the card's statement: the differential-automorphism
input — the semilinear action `(7)`–`(10)` on `M_K = Ω/Tor`, i.e. that `T_σ` is given by a matrix in
`GL_r(R_K)` — and the identification of `μ_n` with the Cartan prefix invariants of the corpus's
`OperatorCartanComparison`.  With those two links the existing `tendsto_normalized_ambient_cartan`
supplies `(14)` and the balance law supplies `(15)`.
