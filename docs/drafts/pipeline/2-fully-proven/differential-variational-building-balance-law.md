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

## Lean progress — `(2)`: the canonical connection, and `Ω` as an `R_K`-module

`GaloisForLFunctions.HTGeometry.KaehlerConnection` (wired, built, axiom-clean) constructs the
connection `(2)` and the module structure it defines, with no presentation and no choice of
differential generators.

```text
KaehlerJet                            the twisted first jet module `Ω × Ω` with
                                      `a • (ω, ω') = (a ω, a ω' + δ(a) ω)`; `AddCommGroup`,
                                      `Module K`, `Module C`, `IsScalarTower C K`
kaehlerJetFun, kaehlerJetDerivation   **`b ↦ (d b, d (δ b))` is a `C`-derivation into it** — the
                                      Leibniz rule for the second component is exactly the two
                                      cross terms of `δ`
kaehlerLift, kaehlerLift_D            its factorisation through `Ω[K⁄C]`, by the universal property
base_kaehlerLift                      the lift is a section: its first component is the identity
kaehlerConnection                     `∇ := (second component of the lift)`, an additive map
kaehlerConnection_D                   `∇ (d b) = d (δ b)`
kaehlerConnection_smul                **`∇ (a • ω) = a • ∇ ω + δ(a) • ω`** — the law `(2)`
diffOpAux, diffOpSMul, diffOpSMul_mono
                                      the action `∑ aₙ ∂ⁿ ↦ ∑ aₙ ∇ⁿ`
diffOpSMul_smul, diffOpSMul_dpartial, diffOpSMul_dpartial_iterate
                                      `(∂ · p) • ω = ∇ (p • ω)`, and its iterate
diffOpSMul_mul, diffOpSMul_one, diffOpSMul_add, diffOpSMul_zero
kaehlerDiffOpModule                   **`Ω[K⁄C]` is a module over the Ore ring `DiffOp K`**
```

The only hypothesis is that the base is differentially constant, `δ (algebraMap c) = 0`, which is
what "`C` a field of constants" means in `§1`.  This is `(2)` of the card, and it is the input the
lattice model (`OperatorLattice`, `OperatorConductorLength`, `OperatorCartanComparison`,
`OperatorBalanceLaw`) has been waiting for.

What `(3)`--`(4)` still need on top of it: the Ore-torsion quotient `M_K = Ω/Tor` and its freeness
over the left-and-right Euclidean domain `R_K`, the rank identification
`rank M_K = differential-trdeg_C K`, and then the semilinear action of a differential automorphism.

Every declaration reports `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## Lean progress — `(7)`--`(10)`: the semilinear action, before the choice of basis

`GaloisForLFunctions.HTGeometry.KaehlerSemilinearAction` (wired, built, axiom-clean) constructs the
differential-automorphism input of `(7)`--`(10)` in its basis-free form.

```text
TwistedKaehler                        `Ω[K⁄C]` with scalars twisted by `σ`, with its
                                      `AddCommGroup`, `Module K`, `Module C` and tower instances
twistedKaehlerDerivation              **`b ↦ d (σ b)` is a `C`-derivation into it**, for any ring
                                      automorphism `σ` of `K` fixing the base
twistedKaehlerLift                    its factorisation through `Ω[K⁄C]`
kaehlerSemilinear                     `σ_*`, an additive endomorphism of `Ω[K⁄C]`
kaehlerSemilinear_D                   `σ_* (d b) = d (σ b)`
kaehlerSemilinear_smul                **`σ_* (a • ω) = σ(a) • σ_* ω`** — semilinearity
symm_fixes, kaehlerSemilinear_symm_kaehlerSemilinear
                                      **`(σ⁻¹)_* ∘ σ_* = id`**: `σ_*` is an automorphism
kaehlerSemilinear_kaehlerConnection
                                      **`σ_* ∘ ∇ = ∇ ∘ σ_*`** when `σ` commutes with `δ`
```

The commutation is proved by span induction over `Submodule.span K (range d) = ⊤`: the generators
`d b` give `σ(δ b) = δ(σ b)`, and the scalar step is exactly the two Leibniz corrections cancelling,
`σ_*(∇(a • ω)) = σ(a) • ∇(σ_* ω) + δ(σ a) • σ_* ω = ∇(σ_*(a • ω))`.

So `σ_*` is a `σ`-semilinear automorphism of `Ω[K⁄C]` as a `K[∂; δ]`-module.  Passing to
`M_K = Ω/Tor` and reading off a matrix in `GL_r(R_K)` now needs only the freeness statement `(4)`.

## Lean progress — the freeness half of `(4)`: submodules over `K[∂;δ]` are free

`GaloisForLFunctions.HTGeometry.DifferentialOperatorSubmoduleFree` (wired, built, axiom-clean)

```text
exists_basis_card_le        **every submodule of `K[∂;δ]^ι` supported on a finite coordinate set is
                            free of rank at most its size** — the induction over the coordinate set
exists_basis_of_submodule   the same for a finite index type
free_submodule              the same, as `Module.Free`
```

Mechanism: `DifferentialOperatorSubmoduleSplitting.exists_coord_generator` supplies, for a chosen
coordinate `i₀`, an element `x` of the submodule whose `i₀`-coordinate generates the image of the
coordinate projection.  The previous stage lives in the kernel of that projection, so in a relation
`g₀ x + ∑ gᵢ vᵢ = 0` the `i₀`-coordinate reads `g₀ · (x i₀) = 0`; the operator ring is a domain, so
`g₀ = 0` and the rest is a relation among the previous basis.  When `x i₀ = 0` the whole submodule
lies in the kernel and the previous basis already works.

`KaehlerConnection` also gained `kaehlerConnection_unique`: an additive endomorphism sending `d b`
to `d (δ b)` and satisfying the Leibniz law *is* the connection.  This identifies the construction
here with the corpus's other one,
`HypertranscendentalKaehlerClockSymbol.kaehlerConnectionDifferential`, which builds the same map
from the `kerTotal` presentation.

What `(4)` still needs: that `M_K = Ω/Tor` embeds into a finite free module — clearing denominators
in `Q_K ⊗ M_K`, for which `OperatorLattice` already has the lattice layer — and the rank identity
`rank M_K = differential-trdeg_C K`.

## Lean progress — `(4)`: the structure theorem for `K[∂;δ]`-modules

`GaloisForLFunctions.HTGeometry.DifferentialOperatorTorsionFreeQuotient` (wired, built,
axiom-clean) proves the statement `M_K = Ω/Tor` needs:

```text
rowSpanR                                   the left row span of a matrix, as a module over the
                                           operator ring
rowSpanR_rowAdd                            row operations do not move it
colAddVecLinR, colAddVecEquivR, rowSpanR_colAdd
                                           a column operation moves it by an automorphism of the
                                           ambient module
exists_equiv_of_rowColEquiv                **hence any two row-column-equivalent matrices have row
                                           spans related by an automorphism**
coordIdeal, exists_mul_of_mem_rowSpanR_diagonalized
                                           on a diagonal matrix every element of the row span has
                                           its `j`-coordinate in the left ideal of the entry in
                                           that column
row_eq_smul_single                         a row of a diagonal matrix is a multiple of a coordinate
                                           vector
isUnit_of_torsionFree_quotient             **a torsion-free quotient forces every diagonal entry to
                                           be a unit**: otherwise `e_j` is outside the row span
                                           while `d · e_j` is inside, and its class is killed by `d`
hitCols, rowSpanR_eq_coordSupport          with unit entries the row span *is* the span of its
                                           coordinate lines
free_quotient_coordSupport                 the quotient by a coordinate span is the free module on
                                           the remaining coordinates
free_of_torsionFree_quotient               **the structure theorem**: a torsion-free quotient of
                                           `K[∂;δ]^κ` (`κ` finite) is free
```

Together with `DifferentialOperatorSubmoduleFree` (submodules are free) this is the module theory of
`(3)`--`(4)`: for a finitely differentially generated `K/C`, `Ω[K⁄C]` is a quotient of a finite free
`R_K`-module through `kaehlerDiffOpModule`, and `M_K = Ω/Tor` is torsion-free by construction, hence
free.  The remaining input for `(4)` in the card's exact form is the rank identity
`rank M_K = differential-trdeg_C K`; the *balance law* `(12)`/`(15)` needs only that some finite
rank exists, together with `σ_*` becoming a matrix through a basis.

## Lean progress — `(7)`--`(10)`: the differential automorphism acts, and is a matrix

`GaloisForLFunctions.HTGeometry.DifferentialOperatorSemilinearMatrix` (wired, built, axiom-clean)

```text
map_zero', map_one'
map_dpartial, map_dpartial_iterate   a derivation-commuting homomorphism intertwines left
                                     multiplication by `∂`
map_mul'                             **hence it is multiplicative on operators**
mapRingHom, symm_deriv_comm, mapRingEquiv
                                     **a differential automorphism of the coefficient field acts on
                                     `K[∂;δ]` as a ring automorphism**
exists_matrix_of_apply               the matrix of a map in a basis
apply_sum_smul_of_semilinear         a semilinear map carries a basis combination to the twisted
                                     combination of the images
sum_mul_matrix_of_semilinear_comp    the composition identity for the two matrices
isUnit_matrix_of_semilinear_equiv    **a `σ`-semilinear automorphism of a free module of finite rank
                                     has a matrix `A` with `A · σ(A') = 1 = σ(A') · A`**
```

Assembling with the previous two passes: `Ω[K⁄C]` is a `K[∂;δ]`-module (`kaehlerDiffOpModule`),
`M_K = Ω/Tor` is free (`free_of_torsionFree_quotient`), `σ_*` is a `σ`-semilinear automorphism of it
(`kaehlerSemilinear`, `kaehlerSemilinear_symm_kaehlerSemilinear`), `σ` acts on the operator ring
(`mapRingEquiv`), and in a basis `σ_*` is an invertible matrix over `R_K`
(`isUnit_matrix_of_semilinear_equiv`).  That is `(7)`--`(10)`.

What remains on this card: the rank identity `rank M_K = differential-trdeg_C K` of `(4)`, and the
building dichotomy of Theorem B.

## Lean progress — `(3)`: the Kähler module is finitely generated over `R_K`

`GaloisForLFunctions.HTGeometry.KaehlerDifferentialGeneration` (wired, built, axiom-clean)

```text
kaehlerMembershipField            the elements whose differential lies in a given `K`-submodule form
                                  an intermediate field — Leibniz for a product and
                                  `d(x⁻¹) = −x⁻² d x` for an inverse
eq_top_of_connection_stable       **a `K`-submodule stable under the connection and containing the
                                  differentials of a differential generating set is everything**,
                                  by minimality of differential adjunction: the membership field is
                                  derivation closed because `d(δ x) = ∇ (d x)`
connectionOrbit, mem_connectionOrbit_iterate
span_connectionOrbit_eq_top       **`Ω[K⁄C]` is spanned over `K` by the connection orbit of the
                                  generators** — that is, generated over `K[∂;δ]` by their
                                  differentials
```

This is exactly the sentence of `§1`: "It is finitely generated because any finite differential
generating tuple for `K/C` supplies `R_K`-generators for `Ω`."  With it, `Ω[K⁄C]` is a quotient of a
finite free `R_K`-module, so `M_K = Ω/Tor` is free by
`DifferentialOperatorTorsionFreeQuotient.free_of_torsionFree_quotient`, and `σ_*` becomes an
invertible matrix by `DifferentialOperatorSemilinearMatrix.isUnit_matrix_of_semilinear_equiv`.

Card status: `(2)`, `(3)`, `(7)`--`(10)` and the freeness half of `(4)` are Lean.  What remains is
the rank identity `rank M_K = differential-trdeg_C K` and the building dichotomy of Theorem B.

## Lean progress — `(3)`--`(4)` assembled: `M_K` is a free `R_K`-module

`GaloisForLFunctions.HTGeometry.KaehlerModuleFree` (wired, built, axiom-clean), on top of the
`IsConstantBase` class and the module/tower instances now in `KaehlerConnection`:

```text
IsConstantBase, kaehlerDiffOpModuleInstance, diffOp_smul_def
IsScalarTower K (DiffOp K) Ω[K⁄C]            the operator action extends the field action
partial_smul_eq_connection                   `∂ • ω = ∇ ω`
span_diffOp_D_eq_top                         **the differentials of a differential generating set
                                             generate `Ω[K⁄C]` over `K[∂;δ]`**
free_quotient_kaehler_of_torsionFree         **a torsion-free quotient of `Ω[K⁄C]` for a finitely
                                             differentially generated `K/C` is a free
                                             `K[∂;δ]`-module** — this is `M_K = Ω/Tor`
```

together with `DifferentialOperatorTorsionFreeQuotient.free_of_torsionFree_of_fg`
("a finitely generated torsion-free module over the operator ring is free").

So `(2)`, `(3)`, the freeness statement of `(4)`, and `(7)`--`(10)` are all Lean, unconditionally.

**What is left on this card.**

1. The rank identity `rank_{R_K} M_K = differential-trdeg_C K` of `(4)`.  Only the *number* `r` is
   at stake; the balance law itself needs only that some finite rank exists.
2. The building dichotomy of Theorem B.  This is the deep item.  In the lattice model it says that
   `μ_n` is bounded whenever `μ_n/n → 0`, i.e. that the isometry `T_σ` is semisimple.  Over a
   *commutative* complete discretely valued field this follows from the nonarchimedean Jordan
   estimate — the binomial coefficients have absolute value at most one, so `‖A^n‖ ≍ ρ^n` exactly —
   but `Q̂_K = K((∂^{-1}))` is a skew field, infinite dimensional over its centre, so there is no
   eigenvalue or reduced-norm theory to run that argument.  The route that remains is the geometric
   one: the displacement function of an isometry of the *discrete* affine building takes values in a
   discrete set, so its infimum is attained, and a semisimple isometry either fixes a point
   (bounded orbit, `λ = 0`) or translates an axis (`d(L, A^n L) = n·ℓ + O(1)`, `λ ≠ 0`).  That
   requires the CAT(0) geometry of the building, which is the missing layer.

## Lean progress — the rank lower bound of `(4)`

`GaloisForLFunctions.HTGeometry.KaehlerDifferentialIndependence` (wired, built, axiom-clean)

```text
kaehlerConnection_iterate_D                  `∇ⁿ (d y) = d (δⁿ y)`
linearIndependent_diffOp_D_of_differentialIndependent
    **differentially independent elements have `K[∂;δ]`-independent differentials**: an operator
    relation `∑ Lᵢ · d yᵢ = 0` expands, through the connection, into a field-linear relation among
    the `d (δⁿ yᵢ)`, and over a characteristic-zero base algebraic independence of the jets is
    exactly linear independence of their universal differentials
    (`KaehlerAlgebraicIndependence.algebraicIndependent_iff_kaehlerD_linearIndependent`)
linearIndependent_mkQ_of_torsion
    independence survives the quotient by a submodule of torsion elements — the operator ring is a
    domain, so multiplying the relation by the annihilator keeps it nontrivial
```

`KaehlerConnection` gained `diffOpSMul_eq_sum`, the expansion `p • ω = ∑_{n ∈ T} (coeff p n) ∇ⁿ ω`
over any finite set carrying the support.

With `span_diffOp_D_eq_top` (rank at most the number of differential generators) this is both halves
of the rank identity `(4)`: `rank_{R_K} M_K = differential-trdeg_C K`.  The only item left on this
card is the building dichotomy of Theorem B.

### The dichotomy, reduced to a statement about twisted products over `K[∂;δ]`

Reading `(11)` precisely — the base lattice is a *valuation* lattice `O^r`, `O = K[[∂^{-1}]]`, not
`R_K^r` — the dichotomy is a statement about the twisted iterates

```text
A_n = A_sigma · sigma(A_sigma) · … · sigma^(n-1)(A_sigma)  in  GL_r(R_K) ⊂ GL_r(Qhat_K),
```

measured against `O^r`.  Three exact facts follow, all elementary:

* `mu_n = 0` **iff** `A_n ∈ GL_r(K)`.  Indeed `GL_r(R_K) ∩ GL_r(O) = GL_r(R_K ∩ O) = GL_r(K)`,
  because the operators of degree at most zero are the coefficients.
* `∑_i mu_i(n) = 0` for every `n` — this is `(12)`, already Lean.
* `n ↦ d(O^r, A_n O^r)` is subadditive, because `sigma` preserves the degree, so `(14)` follows from
  Fekete; the corpus proves it directly
  (`OperatorCartanComparison.tendsto_normalized_ambient_cartan`), independently of the building.

So the dichotomy is exactly: *a subadditive, integer-valued displacement sequence coming from a
twisted matrix product over `K[∂;δ]` is bounded whenever it is sublinear.*  Two routes are open,
and neither is a degree count:

1. **Geometric.**  Displacements in the building are integral, so the infimum of the displacement
   function is attained; a semisimple isometry of a CAT(0) space either fixes a point (`λ = 0`,
   bounded) or translates an axis (`d(L, T^n L) = nℓ + O(1)`, `λ ≠ 0`).  The missing layer is that
   the lattice-class complex of `Qhat_K^r` is CAT(0).  For `r = 2` it is a tree and Serre's
   elementary elliptic/hyperbolic dichotomy suffices.
2. **Slope-theoretic.**  A formal classification of difference modules over `Qhat_K` with the
   residue automorphism `sigma` — the analogue of Dieudonné–Manin, and of the formal classification
   of difference equations over `C((z^{-1}))` — gives a slope decomposition, and with it
   `mu(A_n) = n·λ + O(1)` directly.

The associated graded of the valuation filtration on `Qhat_K` is the *commutative* ring
`K[ξ, ξ^{-1}]` (the symbol of `∂ a` is `a ξ`), which is what makes route 2 plausible: the obstruction
is entirely the degree cancellation in the twisted product, not noncommutativity of the symbols.

### Lean progress — the first structural step of the dichotomy

Two exact identifications make the dichotomy a statement about *degrees*:

* `mu_1(n) = deg(A_n)` and `-mu_r(n) = deg(A_n^{-1})`, where `deg` is the largest entry degree.
  Indeed `A_n O^r ⊆ ∂^m O^r` exactly when every entry of `A_n` has degree at most `m`, so the
  largest elementary divisor is the largest entry degree.
* So the dichotomy reads: *if `deg(A_n)/n → 0` then `deg(A_n)` is bounded*, for the twisted product
  `A_n = A σ(A) ⋯ σ^(n-1)(A)` of a matrix invertible over `K[∂;δ]`.

`GaloisForLFunctions.HTGeometry.DifferentialOperatorTopCoefficientMatrix` (wired, built,
axiom-clean) proves the structural constraint this produces:

```text
coeff_dpartial_iterate_at, coeff_mul_of_degree_le
    the top coefficient of a product, with degree bounds: `coeff (p q) (d+e) = coeff p d · coeff q e`
    whenever `deg p ≤ d`, `deg q ≤ e` — commuting `∂^d` past a coefficient changes only lower terms
topCoeffMatrix, topCoeffMatrix_mul
    hence the **leading matrix is multiplicative**: `(A B)_{d+e} = A_d · B_e`
not_isUnit_topCoeffMatrix
    **a matrix of operators invertible over `K[∂;δ]` with an entry of positive degree has a
    singular leading matrix** — apply multiplicativity to `A B = 1` with `d + e > 0`
```

So the degree of the twisted product can drop only along the kernel of the leading matrix, and the
leading matrix of every `A_n` with `deg A_n > 0` is singular.  This is the entry point of the slope
theory that route 2 above needs: a Newton-polygon filtration built from the kernels of the leading
matrices, along which the degrees are eventually exactly linear.

`GaloisForLFunctions.HTGeometry.DifferentialOperatorConstantMatrix` (wired, built, axiom-clean)
adds the two consequences the induction needs:

```text
CRingHom, CRingHom_injective          the coefficients as a ring homomorphism into `K[∂;δ]`
isUnit_det_of_map_C_mul_eq_one        **a constant matrix invertible over the operator ring is
                                      invertible over the field** — a left kernel vector over `K`
                                      stays one over `K[∂;δ]`, and an invertible matrix has none.
                                      So `deg A = 0` forces `A ∈ GL_r(K)`, hence `A_n ∈ GL_r(K)`
                                      and `mu_n = 0` for every `n`: the degree-zero case of the
                                      dichotomy is closed
exists_degree_eq_of_topCoeffMatrix_mul_ne_zero
                                      **the degree of a product is exactly additive when the
                                      leading matrices do not annihilate each other**
```

Combining: the degree of the twisted product is exactly additive except along the kernel of the
leading matrix, the leading matrix of every `A_n` of positive degree is singular, and `deg A = 0`
already gives the bounded phase.  What is left is the induction on the kernel filtration — the slope
theory proper.

`GaloisForLFunctions.HTGeometry.DifferentialOperatorChainDegree` (wired, built, axiom-clean) turns
that into the generic branch of the dichotomy, for an ordered product of arbitrary factors — which
is what the twisted product `A σ(A) ⋯ σ^(n-1)(A)` is:

```text
chainProd, chainProdK                 the ordered products of operator and of coefficient matrices
degree_matrix_mul_le                  the entrywise degree bound for a matrix product
topCoeffMatrix_chainProd              **the leading matrix of an ordered product is the ordered
                                      product of the leading matrices**, together with the degree
                                      bound `∑ e_k`
exists_degree_chainProd_eq            **the bound is attained exactly when that product of leading
                                      matrices is nonzero**
```

So the whole dichotomy is now reduced to the behaviour of one sequence of matrices *over the
coefficient field*: `C_n = C_0 σ(C_1) ⋯` — the accumulated leading matrices.  While it stays
nonzero the degree is exactly `∑ e_k`, hence linear for a twisted power, and `λ ≠ 0` unless every
`e_k = 0` (the case already closed by `isUnit_det_of_map_C_mul_eq_one`).  A degree drop happens
exactly when the accumulated leading matrix is annihilated, and the remaining work is the induction
on that kernel filtration.

### Both branches of the dichotomy are now arithmetic

`GaloisForLFunctions.HTGeometry.SubadditiveDegreeDichotomy` (wired, built, axiom-clean)

```text
le_mul_of_subadditive              `d m ≤ m · d 1`
eq_zero_of_mul_of_eq_zero          `d N = 0` forces `d (k N) = 0`
le_sup_of_subadditive_of_eq_zero   **the bounded branch**: a subadditive sequence vanishing at a
                                   positive index is bounded by its values below that index
mul_le_of_subadditive_of_exact     **the linear branch**: if the sequence is exactly additive along
                                   the multiples of `N`, then `n · d N ≤ N · (d n + N · d 1)`, i.e.
                                   `d n / n ≥ d N / N − N·d 1 / n`, so the normalized limit is
                                   `d N / N`
```

Combining with the operator-matrix layer, the dichotomy of Theorem B follows from a *single*
remaining input:

> there is an `N ≥ 1` for which the accumulated leading matrices of the `N`-step chain never
> annihilate — equivalently, `deg` is exactly additive along the multiples of `N`.

Given such an `N`: if `deg A_N = 0` then `A_N ∈ GL_r(K)`
(`isUnit_det_of_map_C_mul_eq_one`), so every `A_{kN} ∈ GL_r(K)`, and
`le_sup_of_subadditive_of_eq_zero` bounds the orbit — the *bounded phase*, `λ = 0`.  If
`deg A_N > 0` then `mul_le_of_subadditive_of_exact` gives `λ = deg A_N / N > 0` — the *boundary
phase*.  What is left is the existence of such an `N`, i.e. the termination of the kernel
filtration, which is where the rank bound `r` enters.

`matDeg_chainProd_eq` closes the generic branch in the exact form the card needs: for a chain of
factors of degree at most `e` whose accumulated leading matrices never vanish, the matrix degree of
the `n`-fold product is **exactly** `n · e`.  Together with the two arithmetic branches this gives,
unconditionally:

> if the accumulated leading matrices of the twisted product never vanish, then either `deg A = 0`
> and the whole orbit is bounded (`λ = 0`), or `deg A > 0` and `λ = deg A > 0`.

Also worth recording, from `P_{n+1} = C₀ · σ(P_n)`: the ranks `rank P_n` are non-increasing, so the
accumulated leading matrices either never vanish or vanish from some index on.  The only remaining
gap is the *recursion* across a vanishing: restarting with the generator `A_N` of the first
vanishing index reproduces the same situation with `σ^N` in place of `σ` and a strictly smaller
degree ratio, and what is missing is the bound on the number of such restarts — the rank bound `r`,
which in the classical theory comes from splitting off a proper sub-object at each drop.

The structural dichotomy of the leading chain is Lean as well:

```text
chainProdK_eq_zero_of_le    once the accumulated leading matrix vanishes it stays zero
rank_chainProdK_antitone    its ranks are non-increasing
chainProdK_dichotomy        **either it never vanishes, or it vanishes from some index on**
```

So exactly one of the two regimes occurs, and in the first the dichotomy of Theorem B is already
proved.  The card's last open point is therefore a single, sharply stated statement:

> after a vanishing at the first index `N`, the restarted chain — generator `A_N`, automorphism
> `σ^N` — reaches the non-vanishing regime after finitely many restarts.

Classically this is the rank bound: each vanishing splits off a proper sub-object, so there are at
most `r` restarts.

### Lean progress — the restart recursion is now an identity

`GaloisForLFunctions.HTGeometry.TwistedMatrixChain` (wired, built, axiom-clean)

```text
iterHom, iterHom_add, iterHom_iterHom      the iterates of a ring endomorphism, as endomorphisms;
                                           `(σ^N)^j = σ^{jN}`
twistedFamily, twistedChain                `σ^n(C)` and the ordered product `C σ(C) ⋯ σ^{n-1}(C)`
twistedChain_left                          **the chain also recurses from the left**:
                                           `P_{n+1} = C · σ(P_n)`
twistedChain_add                           **the chain splits**: `P_{m+n} = P_m · σ^m(P_n)`
twistedChain_restart                       **restarting at step `N` produces the twisted chain of
                                           the `N`-step block, with `σ^N` as the twist**
twistedChain_eq_zero_restart_iff
DiffOp.twistedChain_eq_chainProdK          agreement with the coefficient ordered product
DiffOp.twistedChain_eq_chainProd           agreement with the operator ordered product
```

Everything is stated for an arbitrary ring `R` and endomorphism `σ`, then specialized to both
`K` and `K[∂;δ]`, so the same identities serve the leading-matrix chain and the operator chain.

What this settles.  The card's last open point was phrased as a *claim about restarts*:
"restarting with the generator `A_N` reproduces the same situation with `σ^N` in place of `σ`".
That is no longer a claim — `twistedChain_restart` is it:

`A_{kN} = ` the `k`-th term of the twisted chain of `A_N` with respect to `σ^N`.

So the restart map `(σ, A) ↦ (σ^N, A_N)` sends twisted chains to twisted chains, and any invariant
of a twisted chain — the degree sequence `d`, its normalized limit, the accumulated leading-matrix
chain — recurses along restarts without further hypotheses.  In particular `d'(k) = d(kN)`, so
`λ' = N λ`, exactly as the card asserts.

What remains.  The termination of that recursion.  The restart strictly lowers the degree ratio
(`deg A_N < N · deg A` at a vanishing), but strictly decreasing positive rationals need not
terminate, so an extra invariant is required.  The classical one is the *slope filtration*: at each
drop a proper `σ`-stable sub-object splits off, and its rank bounds the number of drops by `r`.
Note that the corresponding statement for the accumulated leading matrices alone is *not* the right
object — at a restart that chain is generated by `P_N = 0` — because the restarted leading matrix
lives at the new, lower degree `deg A_N`, not at `N · deg A`.  The remaining input is therefore the
lattice-level filtration, i.e. exactly one of the two routes recorded above (CAT(0) semisimplicity
of the affine building, or a Dieudonné–Manin slope decomposition for `σ`-modules over `Qhat_K`);
the restart algebra those routes are applied to is now formal.

### Lean progress — the accumulated leading matrices have a stable rank

`GaloisForLFunctions.HTGeometry.ChainRankStabilization` (wired, built, axiom-clean)

```text
rank_chainProdK_antitone_le      the ranks of an ordered product are non-increasing, iterated
exists_rank_chainProdK_stabilize **the rank stabilises**: it attains its minimum at some index and
                                 stays there
```

`chainProdK_dichotomy` already separated the two regimes — the accumulated leading matrix chain
either never vanishes or vanishes from some index on.  The stable rank refines that: there is an
index `N` beyond which the rank is constant, and the dichotomy is the case distinction on whether
that constant is positive.

This is the entry point of the slope filtration in the exact form the remaining open point needs.
In the positive-rank regime `matDeg_chainProd_eq` already gives `deg A_n = n·e` exactly, so the
dichotomy of Theorem B is settled there; in the zero-rank regime `twistedChain_restart` reproduces a
twisted chain with generator `A_N` and twist `σ^N`, and what is missing is still the bound on the
number of restarts — for which the stable rank is the natural candidate invariant, since a restart
that lowers it can happen at most `r` times.

### Lean progress — the stable image

`GaloisForLFunctions.HTGeometry.ChainStableImage` (wired, built, axiom-clean)

```text
range_chainProdK_antitone, range_chainProdK_antitone_le
    **the images of an ordered product decrease** — each further factor is applied first
exists_range_chainProdK_stabilize
    **the image stabilises**: beyond the index where the rank is minimal it no longer changes
```

Together with `twistedChain_left` — `P_{n+1} = C · σ(P_n)` — this identifies the stable image as the
subspace the accumulated leading matrices carry onto itself: `im P_{n+1} = C · σ(im P_n)`, so on the
stable image the twisted operator is a bijection.  That is the sub-object of the slope filtration in
the non-vanishing regime, and it is nonzero exactly there.

The open point of the card is unchanged in statement but is now equipped: the two regimes are
separated by `chainProdK_dichotomy`, indexed by the stable rank
(`exists_rank_chainProdK_stabilize`), and carry a stable subspace
(`exists_range_chainProdK_stabilize`); the restart is an identity (`twistedChain_restart`); and what
is still missing is the bound on the number of restarts.

### Lean progress — the stable rank decides the dichotomy

`ChainRankStabilization` gained (wired, built, axiom-clean):

```text
rank_eq_zero_iff                  **a matrix has rank zero exactly when it vanishes** — a mathlib
                                  gap, proved by evaluating the linear map at the standard basis
chainProdK_ne_zero_iff_rank_pos   **the accumulated chain never vanishes exactly when its stable
                                  rank is positive**
```

So `chainProdK_dichotomy` is now a genuine numerical criterion rather than a case split: compute the
stable rank of the accumulated leading matrices; if it is positive, `matDeg_chainProd_eq` gives
`deg A_n = n·e` exactly and Theorem B's dichotomy is settled; if it is zero, the chain vanishes from
some index on and `twistedChain_restart` reproduces a twisted chain with generator `A_N` and twist
`σ^N`.

The one open point of the card is unchanged: the bound on the number of restarts.

### Lean progress — the shear invariant, and the bounded branch in its strongest elementary form

`GaloisForLFunctions.HTGeometry.ShiftedMatrixDegree` (wired, built, axiom-clean).

Conjugating an operator matrix by `diag(∂^{k_1},…,∂^{k_r})` changes the degree of the entry `(i,j)`
by `k_j − k_i`.  The conjugate does not lie in `K[∂;δ]`, but the *bound* on its degrees never needs
the conjugate to be formed — it is a purely arithmetic predicate on the entry degrees:

```text
ShiftDegLE k P c  :  deg P_{ij} + k_j − k_i ≤ c   for every nonzero entry
```

```text
ShiftDegLE.mono, shiftDegLE_one
shearSpread, le_shearSpread, shearSpread_nonneg
ShiftDegLE.matDeg_le             the plain degree is within `spread(k)` of the shifted one
ShiftDegLE.mul                   **submultiplicativity**
ShiftDegLE.map                   invariance under a degree-preserving map of the entries
shiftDegLE_twistedChain          **the chain's shifted degree is at most `n·c`**
matDeg_twistedChain_le_of_shiftDegLE
    **every shear bounds the growth rate**: `matDeg A_n ≤ n·c + spread(k)`
matDeg_twistedChain_le_of_shiftDegLE_zero
    **the bounded branch**: a shear with `c = 0` forces `matDeg A_n ≤ spread(k)` for *every* `n`
```

Why this matters for the open point.  The card's bounded phase was previously available only in the
degree-zero case `deg A = 0` (`isUnit_det_of_map_C_mul_eq_one`), which is the shear `k = 0`.  The
shear predicate covers every diagonal change of lattice at once, with a uniform explicit bound, and
it is stated without leaving the operator ring — no completion, no Ore field, no inverse of `∂`.

Two facts fix the exact remaining gap, and both are now visible.

* **Diagonal shears alone do not decide the phase.**  For `A = [[0,1],[∂,0]]` the true rate is `1/2`
  while `min_k ShiftDegLE`-value is `1`: an integer shear cannot see a slope with denominator `2`.
  Passing to `A_2 = ∂·I` repairs it, which is exactly why the restart of `twistedChain_restart` is
  needed and why the bound on the number of restarts is the crux.
* **Constant base changes are also needed.**  For `A = I + ∂M` with `M` a nonzero nilpotent constant
  matrix, `A_n = I + n∂M`, so `matDeg A_n = 1` is bounded, yet every diagonal shear has shifted
  degree at least `1`.  A constant change of basis putting `M` in Jordan form turns it into
  `[[1,∂],[0,1]]`, for which the shear `k = (0,−1)` gives `c = 0`.

So the right invariant is `min over (N, S ∈ GL_r(Frac R)) of matDeg(S⁻¹ A_N S)/N`, and the two
examples show that neither the `N` nor the general `S` can be dropped.  That min is the translation
length of the card's building isometry; the elementary layer above supplies the direction
`min ≤ ⇒ bounded`, and what is still missing is the reverse — that the min is attained, i.e. the
semisimplicity of the isometry.

### Lean progress — the shifted leading matrix, and exact linear growth against a shear

`GaloisForLFunctions.HTGeometry.ShiftedTopMatrix` (wired, built, axiom-clean) completes the shear
layer with its leading-matrix half.

Against a shear the top degree of the entry `(i,j)` is `c + k_i − k_j`, an *integer* which may be
negative — in which case the entry must vanish, since operator degrees are nonnegative.  Reading the
coefficient at an integer index handles both cases uniformly:

```text
coeffZ p n = if 0 ≤ n then coeff p n.toNat else 0
coeffZ_add, coeffZ_sum
coeffZ_mul                     **the leading coefficient of a product, at integer indices**
shiftTopMatrix k P c           the leading matrix against the shear
shiftTopMatrix_mul             **multiplicativity**: `(PQ)^top_{c+d} = P^top_c · Q^top_d`
degree_eq_of_shiftTopMatrix_ne_zero
le_matDeg_of_shiftTopMatrix_ne_zero
shiftDegLE_chainProd, shiftTopMatrix_chainProd
    the ordered product's shifted leading matrix is the ordered product of theirs
matDeg_chainProd_sub_le        **exact linear growth**: `|matDeg (B₀⋯B_{n−1}) − ∑ c_m| ≤ spread(k)`
                               whenever the accumulated shifted leading matrices never vanish
shiftTopMatrix_twistedFamily, matDeg_twistedChain_sub_le
    the same for a twisted chain: `|matDeg A_n − n·c| ≤ spread(k)`, uniformly in `n`
```

What this settles.  Relative to **any** shear `k` with `ShiftDegLE k A c` and `0 ≤ c`, the phase is
completely decided as soon as the accumulated shifted leading matrices never vanish:

* `c = 0` — the degree stays inside a band of width `spread(k)`: the **bounded phase**, `λ = 0`;
* `c ≥ 1` — `matDeg A_n = n·c + O(1)` with an explicit uniform constant: the **boundary phase**,
  `λ = c` exactly, not merely asymptotically.

This is the shear-relative form of `matDeg_chainProd_eq`, which was the unsheared case `k = 0`, and
it is what makes the shear a genuine change of lattice rather than a bookkeeping device: the whole
Cartan invariant `μ₁` is computed to `O(1)` from the shifted leading matrix alone.

What is still missing is unchanged and is exactly one statement: that some pair `(N, S)` attains the
minimum of `matDeg(S⁻¹ A_N S)/N`, i.e. that the building isometry is semisimple.  Everything
downstream of such a pair — the exact rate, the `O(1)` band, the two phases — is now proved.

### Lean progress — constant changes of basis, and the bounded phase from a lattice

`GaloisForLFunctions.HTGeometry.ConstantConjugationDegree` (wired, built, axiom-clean)

```text
matDeg_mul_le, matDeg_mul_le_of_deg_zero
    multiplying by matrices of degree zero cannot raise the matrix degree
twistedChain_conj
    **the twisted chain of a constant conjugate is the constant conjugate of the twisted chain**:
    `(S⁻¹ A σ(S))_n = S⁻¹ · A_n · σⁿ(S)`
matDeg_map_eq_zero, matDeg_twistedChain_le_conj
matDeg_twistedChain_le_of_conj_shiftDegLE_zero
    **the bounded phase from a constant basis and a shear**: if some constant change of basis makes
    the shifted degree vanish for some shear, then `matDeg A_n ≤ spread(k)` for every `n`
```

This removes the second of the two obstructions recorded earlier.  The example `A = I + ∂M` with `M`
a nonzero nilpotent constant matrix has bounded chain degree but shifted degree at least one for
*every* shear; a constant change of basis putting `M` in Jordan form turns it into `[[1,∂],[0,1]]`,
for which the shear `k = (0,−1)` gives `c = 0`.  The criterion above covers exactly that.

Note that a constant conjugation is legitimate inside `K[∂;δ]`: `S⁻¹ A σ(S)` has entries in the
operator ring, unlike a shear, which is why the two are treated differently — the shear only ever
appears as the arithmetic predicate `ShiftDegLE`, never as an actual conjugate.

What the pair `(S, k)` still does not cover.  Every lattice of `K((∂⁻¹))^r` is `U·diag(∂^{k})·O^r`
with `U ∈ GL_r(O)`, and constant `S ∈ GL_r(K)` is a proper subgroup of `GL_r(O)`.  So the criterion
is sufficient for the bounded phase but not yet known to be necessary; making it necessary is the
completion step, and is where the degree valuation on the Ore field `Frac(K[∂;δ])` — not yet in the
tree — becomes unavoidable.

### Lean progress — the degree valuation on the Ore field

`GaloisForLFunctions.HTGeometry.PseudoDiffOpDegree` (wired, built, axiom-clean) supplies the
foundation the previous entry named as missing.

```text
ordQ                     the degree of a rational pseudodifferential operator, `p/q ↦ deg p − deg q`
ordQ_oreDiv, ordQ_zero, ordQ_one, ordQ_numeratorRingHom
ordQ_mul                 **additivity** on nonzero elements
ordQ_inv                 `ordQ x⁻¹ = −ordQ x`
```

Well-definedness is the Ore-expansion condition: multiplying numerator and denominator by the same
nonzero operator shifts both degrees equally, which is `degree_mul`.  Additivity is read off the Ore
product formula together with `ore_eq`: from `oreDenom·r₁ = oreNum·s₂` the degrees give
`deg oreNum − deg oreDenom = deg r₁ − deg s₂`, and the rest is bookkeeping.

**Both factors must be nonzero.**  The operator degree uses the convention `deg 0 = 0`, so
`ordQ 0 = 0` and the multiplicative law fails at zero — `ordQ (0·y) = 0` while
`ordQ 0 + ordQ y = ordQ y`.  This is a convention artefact, not a defect of the theory, but it has
to be carried in the statement.

This is the `r = 1` case of the Cartan invariant `μ₁` and the valuation whose completion carries the
lattice theory of a twisted matrix chain.  Note also, from the same computation, a fact worth
recording about the remaining gap: the standard slope-`1/2` example `[[0,1],[∂,0]]` is **not** in
`GL₂(K[∂;δ])` — inverting it forces `∂·B₁₂ = 1`, impossible by degree.  So the denominator-two
obstruction that defeats integer shears is not available inside the operator ring itself, and
whether a matrix invertible *over `K[∂;δ]`* can have non-integral slopes is now a sharp, isolated
question.

### Lean progress — the restart is unavoidable: an invertible matrix whose leading chain dies

The previous entry left one sharp question: can a matrix invertible over `K[∂;δ]` have non-integral
slopes?  If not, integer shears would suffice and the restart bound would follow.  **The answer is
no — non-integral slopes do occur, already at rank three.**

`GaloisForLFunctions.HTGeometry.InvertibleLeadingChainVanishes` (wired, built, axiom-clean) exhibits
the witness: the companion matrix of `t³ + ∂·t + 1`,

```text
companionMatrix  = !![0, 0, -1; 1, 0, -∂; 0, 1, 0]
companionInverse = !![-∂, 1, 0; 0, 0, 1; -1, 0, 0]
companionMatrix_mul_inverse, companionInverse_mul_matrix   **it is invertible over `K[∂;δ]`**
matDeg_companionMatrix                                     its matrix degree is one
topCoeffMatrix_companionMatrix                             the leading matrix is `E₂₃`, one entry
topCoeffMatrix_companionMatrix_sq                          **its square is zero**
chainProdK_companion_eq_zero                               so the accumulated leading chain dies
                                                           at the second step
```

The mechanism is that the only degree-one entry sits in the last column, so the leading matrix is a
single matrix unit `E₂₃` and `E₂₃² = 0`.  The reason this is possible while the matrix stays
invertible is that the constant term of the companion polynomial is a unit: the determinant is `±1`,
and the inverse is written out above.

Newton polygon of `t³ + 0·t² + ∂·t + 1`, with `v = −deg`: the points are `(0,0)`, `(1,−1)`, `(3,0)`,
so the lower hull has slopes `−1` and `+1/2`, and the root valuations are `1` once and `−1/2` twice
— sum zero, as the balance law requires.  A slope with denominator two is invisible to every integer
shear, so **no `(S, k)` with `S` constant and `k` integral can put this matrix in the exact-degree
branch**; passing to `A₂` is genuinely necessary.

This settles the shape of what is left.  The restart of `twistedChain_restart` is not an artefact of
the presentation but a real feature, and the missing statement is exactly the bound on the number of
restarts — equivalently, that the slopes have denominator at most `r`, which is the Newton-polygon
statement for the twisted product and the one thing the elementary layer cannot reach.

### Lean progress — the growth rate exists, unconditionally

`GaloisForLFunctions.HTGeometry.TwistedChainDegreeRate` (wired, built, axiom-clean) proves the
existence half of `(14)`/`(20)` for the matrix degree, with no hypotheses at all:

```text
matDeg_map_le                    a degree-preserving twist does not raise the matrix degree
matDeg_twistedChain_add_le       **subadditivity**: `matDeg A_{m+n} ≤ matDeg A_m + matDeg A_n`
subadditive_matDeg_twistedChain
twistedChainRate                 the asymptotic clock speed
tendsto_matDeg_twistedChain      **Fekete: an actual limit, not a limsup**
```

Subadditivity is the chain-splitting identity `A_{m+n} = A_m · σ^m(A_n)` of `twistedChain_add`,
together with `matDeg_mul_le` and the fact that twisting by a degree-preserving endomorphism leaves
a matrix degree alone.  What is notable is what it does *not* need: no invertibility over the
operator ring, no hypothesis on the leading matrices, no shear, no completion.

Effect on the open point.  The card's `λ` is now a *theorem*, not a conditional object, so the
remaining question is sharpened from "does the limit exist" to "is it attained".  Concretely, with
`InvertibleLeadingChainVanishes` in hand: for the companion matrix of `t³ + ∂t + 1` the rate exists
and equals `1/2`, no integer shear witnesses it, and the missing statement is exactly that some
pair `(N, S)` realises the infimum — the semisimplicity of the building isometry, equivalently the
bound on the number of restarts.

### Lean progress — the rate is identified, not merely approximated

`GaloisForLFunctions.HTGeometry.TwistedChainRateIdentification` (wired, built, axiom-clean)

```text
twistedChainRate_nonneg                 `0 ≤ λ`
twistedChainRate_le_matDeg              `λ ≤ matDeg C`
twistedChainRate_eq_zero_of_shiftDegLE  a shear with `c = 0` forces `λ = 0` — the bounded phase
twistedChainRate_eq                     **`λ = c` exactly**, whenever a shear puts the generator at
                                        shifted degree `c` and the accumulated shifted leading
                                        matrices never vanish
```

The last is the band estimate `|matDeg A_n − n·c| ≤ spread(k)` divided by `n`: the error is
`spread(k)/n → 0`, so an order squeeze pins the Fekete limit and uniqueness of limits identifies it
with `c`.  This is `(14)` of the card in the non-degenerate regime — the asymptotic invariant is
*computed*, not merely shown to exist.

Status of the card's asymptotic law.  Existence of `λ` is unconditional
(`tendsto_matDeg_twistedChain`); its value is `c` whenever the leading chain survives, and `0`
whenever some shear reaches `c = 0`.  What remains is exactly the attainment question: whether every
`A` admits a pair `(N, S)` reaching one of those two regimes.  `InvertibleLeadingChainVanishes`
shows the naive answer is no — for the companion matrix of `t³ + ∂t + 1` the rate is `1/2` and no
integer shear sees it — so the missing statement is the bound on the number of restarts.

### Lean progress — the companion witness has exact rate `1/2`

`GaloisForLFunctions.HTGeometry.CompanionHalfRate` (wired, targeted leaf build, axiom-clean) now
proves the quantitative assertion about the rank-three restart witness rather than reading its rate
only from the paper Newton polygon:

```text
companionSquare, companionSquare_eq
    the two-step block `A²` is explicit
matDeg_companionSquare, topCoeffMatrix_companionSquare
    `deg A² = 1` and its leading matrix is `diag(0,-1,-1)`
matDeg_companionSquare_pow
    **`deg((A²)^n) = n` for every n**
matDeg_companionMatrix_even_pow
    **`deg(A^(2n)) = n` for every n**
twistedChainRate_companionMatrix
    **the full Fekete rate of the identity-twisted companion chain is exactly `1/2`**
```

The restart block's `(1,1)` leading entry is `(-1)^n`, so its accumulated leading matrix never
vanishes and the existing exact chain-degree theorem applies.  The normalized even powers form a
cofinal subsequence constantly equal to `1/2`; uniqueness of the already-proved full-chain limit
identifies the rate.  All seven new public declarations audit to
`[propext, Classical.choice, Quot.sound]`; the module is imported by the `HTGeometry` umbrella,
which was not built.

This closes the explicit nonintegral witness and proves quantitatively that one restart can reveal a
rate invisible to the original leading matrix.  It does not bound the number of restarts for an
arbitrary invertible rank-`r` chain, so the card remains at Stage 2.

`CompanionHalfRate.lean` now also closes the complementary odd iterates:

```text
matDeg_companionMatrix_odd_pow : deg(A^(2n+1)) = n+1
matDeg_companionMatrix_pow     : deg(A^k) = (k+1)/2
```

The proof multiplies the exact two-step block by the original companion matrix and tracks the
nonzero `(1,2)` top coefficient.  The parity assembly formalizes that every power has exact degree
`ceil(k/2)`, not only a cofinal subsequence.  Direct check, targeted leaf build, and new-theorem
axiom audit pass with only `[propext, Classical.choice, Quot.sound]`.  General restart attainment
remains the card's unresolved formal core, so no promotion is made.

### Lean progress — completed pseudodifferential skew field and functorial valuation action (2026-09-02)

Three new leaves close the completion gap named above:

- `PseudoDiffOpValuation` proves the nonarchimedean inequality for rational pseudodifferential
  order, constructs the exact additive valuation `-ord_∂`, and proves every finite integer value is
  realized.
- `PseudoDiffOpCompletion` generalizes mathlib's commutative completion argument to completable
  topological division rings.  It proves that the uniform completion is a division ring with
  continuous inversion, extends the valuation to that completion, and defines its valuation ring.
- `PseudoDiffOpAutomorphism` extends every derivation-preserving coefficient automorphism through
  the Ore localization and completion, proves identity and composition laws, preserves the extended
  valuation, and restricts functorially to the completed valuation ring.

All declarations pass direct checking, targeted leaf builds, and axiom audit with only `propext`,
`Classical.choice`, and `Quot.sound`.  The remaining card theorem is now the actual affine-building
layer: valuation lattices and relative-position vectors over this completed skew field, general
semisimplicity/attainment, the bounded-or-axis dichotomy with no parabolic phase, and canonical
opposite boundary flags.  Those interfaces are absent from the corpus, so Theorems A–C are not yet
fully formalized and the card remains at Stage 2.

### Lean progress — exact valuation-lattice and homothety carrier (2026-09-02)

Two further leaves now construct the actual lattice carrier over the completed noncommutative skew
field, without replacing it by a commutative or finite-dimensional surrogate:

- `CompletedPseudoDiffOpLattice` defines a lattice as a finitely generated left module over the
  completed valuation ring whose completed-skew-field span is the whole coordinate space.  It
  constructs the standard lattice, proves finite generation and full span, transports every lattice
  under the completed coefficient action, proves identity and composition, and proves the standard
  lattice is fixed.
- `DifferentialVariationalBuildingCarrier` proves that right multiplication by a nonzero completed
  skew scalar preserves lattices, that resulting homothety relation is reflexive, symmetric, and
  transitive, and forms the exact quotient of full valuation lattices by homothety.  Coefficient
  automorphisms preserve homothety and descend to this quotient with unconditional identity and
  composition laws.

Both leaves pass direct checking and targeted leaf builds.  Every new declaration audits with only
`propext`, `Classical.choice`, and `Quot.sound`.  Top carrier leaf is wired into `HTGeometry`; umbrella
was not built.

This closes vertex carrier and functorial coefficient-action portions of `(6)` and `(9)`.  Card still
cannot move: missing exact interfaces are apartment/metric structure and relative-position vectors
for these noncommutative valuation lattices, the integral matrix part of `T_σ`, determinant balance
`(12)`, semisimplicity/axis attainment and no-parabolic dichotomy, canonical opposite weighted
boundary flags, and free-field reconstruction `(18)--(22)` on that building action.

### Lean progress — exact standard apartment over the completed skew field (2026-09-02)

`DifferentialVariationalStandardApartment` constructs the canonical completed uniformizer from
`∂⁻¹` and proves its extended additive valuation is exactly `1`.  It defines coordinatewise right
scaling by completed-skew-field units, proves preservation and composition of full finitely
generated valuation lattices, and specializes this action to integral coweights via uniformizer
powers.

The leaf proves the exact diagonal classification: two standard coweight lattices are homothetic if
and only if their coweights differ by one common integer.  Hence integral coweights modulo constant
translation embed injectively into the building carrier.  It also proves the rank-one standard
apartment is a singleton, constructs the balanced rank-two coweight `![1, -1]` as a non-base
apartment and building point, and proves every derivation-preserving coefficient automorphism fixes
the standard apartment pointwise.

Direct checking and the targeted leaf build pass.  Every new declaration's axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound` (several purely relational declarations need fewer or
none).  The leaf is wired into `HTGeometry`; the umbrella was not built.

This closes the canonical-uniformizer, diagonal-lattice, and standard-apartment embedding layer.
The card remains at Stage 2: arbitrary full lattices still require a noncommutative Cartan
decomposition/apartment-coverage theorem and relative-position metric; the full semilinear matrix
action and integral Fréchet Jacobian must be constructed; determinant balance, semisimplicity and
axis attainment, the no-parabolic dichotomy, opposite weighted boundary flags, and free-field
reconstruction `(18)--(22)` remain open.

### Lean progress — canonical Ore quotient, corrected projective action, and matrix balance (2026-09-02)

Five new leaves close the algebraic action chain without adding a geometric premise:

- `DifferentialOperatorOreTorsion` defines the literal submodule of elements killed by a nonzero
  operator.  Closure uses the proved Ore common-left-multiple theorem, and the quotient by this
  whole submodule is torsion-free.
- `DifferentialVariationalProjectiveBuildingCarrier` corrects the homothety orientation forced by
  noncommutativity.  Left valuation lattices must be quotiented by **left** homothety for arbitrary
  left-linear maps to descend.  It constructs the action of every completed-skew linear
  equivalence, coefficient automorphism, invertible matrix, and their exact semidirect product.
- `DifferentialVariationalProjectiveStandardApartment` proves that integral coweights modulo common
  translation embed injectively in this corrected carrier.  The proof uses invariance of the
  valuation ring under inner conjugation; it is not a commutative rewrite.  The rank-two balanced
  point remains non-base and coefficient automorphisms fix the apartment pointwise.
- `DifferentialVariationalSemilinearMatrixAction` embeds `K[∂;δ]` into the completed
  pseudodifferential skew field and sends every invertible operator matrix to a genuine completed
  matrix unit.
- `DifferentialVariationalOreModule` assembles the exact object and action:

  ```text
  VariationalOreModule                         M_K = Ω[K⁄C]/Tor_R
  variationalOreModule_free                    finite differential generation makes M_K free
  kaehlerSemilinear_diffOp_smul                σ₊(P·ω) = σ(P)·σ₊(ω)
  kaehlerSemilinear_mem_oreTorsion             σ₊ preserves the canonical torsion submodule
  variationalOreModuleEquiv                    the induced invertible action on M_K
  variationalOreModuleEquiv_refl/trans         identity and functorial composition
  exists_variationalOre_completedPseudoDiffOpMatrixUnit
      every finite basis produces the genuine completed matrix unit acting on the projective carrier
  exists_variationalOre_operatorMatrix_degree_balance
      the action matrix has trivial operator-row-lattice conductor and degree-zero operator divisors
  ```

The last theorem connects the actual differential-automorphism action to the existing operator
balance certificate, closing `(3)` and `(7)`--`(10)` in one checked chain.  It does **not** yet call
those operator-row-lattice divisors the completed-building Cartan vector `μ`: that identification
is one of the remaining comparison theorems needed for `(12)`.  Direct checks and targeted builds
of the two top leaves pass.  Every declaration introduced
in these five leaves audits to exactly `[propext, Classical.choice, Quot.sound]`.  All leaves are
wired into `HTGeometry`; no umbrella build was run.

This also corrects the preceding status paragraph: full semilinear matrix action and its exact
operator-row-lattice balance certificate are no longer open.  What remains is the genuinely
affine-building content:
apartment coverage/Cartan decomposition for every full lattice, relative-position vector and
metric, identification of the balanced operator invariants with that vector, completeness and
CAT(0) semisimplicity, axis attainment/no parabolic phase, intrinsic opposite weighted boundary
flags, and free-field Fréchet/order reconstruction `(18)--(22)`.  The card therefore remains at
Stage 2 and is not promoted.

### Lean progress — finite rank, canonical matrix unit, and basis covariance (2026-09-02)

`DifferentialVariationalOreModule` and `DifferentialOperatorSemilinearMatrix` now remove the last
externally supplied finite-basis input from the algebraic action:

```text
variationalOreModule_finite
    finite differential generation makes M_K finitely generated over K[∂;δ]
exists_fin_basis_variationalOreModule
    freeness plus finite generation produces an actual Fin r operator basis; neither r nor a basis
    is assumed
basisTransitionMatrixUnit
    the row-coordinate transition between arbitrary finite bases is a genuine matrix unit over an
    arbitrary, possibly noncommutative, ring
matrix_changeBasis_semilinear
basisMapMatrix_changeBasis_semilinear
    exact twisted covariance A_new B = σ(B) A_old, equivalently
    A_new = σ(B) A_old B⁻¹ in the row-coordinate convention
basisMapMatrixUnitOfSemilinearEquiv
variationalOreOperatorMatrixUnit
variationalOreCompletedMatrixUnit
    canonical operator and completed matrix units in every fixed finite basis
variationalOreProjectiveBuildingAction
    the literal semilinear action v ↦ σ(v)A on the corrected projective completed-lattice carrier
DifferentialFieldAut
DifferentialFieldAut.projectiveBuildingEquiv
DifferentialFieldAut.projectiveBuildingEquiv_one/mul
    the intrinsic group of base-fixing derivation-preserving field automorphisms acts functorially
    by genuine carrier equivalences, with inverse induced by the inverse field automorphism
variationalOre_basisMapMatrix_trans
variationalOreOperatorMatrixUnit_trans
variationalOreCompletedMatrixUnit_trans
    exact operator and completed semilinear cocycle laws
variationalOreProjectiveBuildingAction_changeBasis
    actions in two finite bases are conjugate by the genuine completed transition-matrix unit
exists_variationalOre_finiteBasis_completedPseudoDiffOpMatrixUnit
exists_variationalOre_finiteBasis_operatorMatrix_degree_balance
    finite differential generation alone supplies both the completed action matrix and the exact
    operator-row-lattice degree-balance certificate
```

This closes the finite-rank existence needed by `(10)`, the functorial carrier-action part of `(9)`,
the basis-change law `(13)`, and construction of the actual projective carrier equivalence in every
finite basis.  The isometry claim is not inferred: it still requires the missing metric/Cartan
layer.  Direct checks and targeted builds of the changed leaves pass.  Every new declaration audits
to exactly `[propext, Classical.choice, Quot.sound]`.

No completed-building Cartan vector is inferred from the operator-row-lattice certificate.  The
remaining gap is still the affine-building geometry and comparison layer listed above; in
particular, apartment coverage/Cartan decomposition, relative position and metric, comparison of
that relative position with operator invariants, CAT(0) completeness/semisimplicity, boundary
flags, and free-field reconstruction remain absent.  Card stays at Stage 2.

### Lean progress — lattice sandwich, commensurability, and the full rank-one carrier (2026-09-02)

`DifferentialVariationalLatticeCommensurability` proves the first arbitrary-lattice structure
theorems over the actual completed noncommutative skew field:

```text
exists_int_le_completedPseudoDiffOpAddValue
exists_uniformizer_right_unscale_mem_integer
exists_uniformizer_left_scale_mem_integer
    every completed operator has a finite valuation floor, and one left uniformizer power clears
    its denominator
exists_le_standardCompletedPseudoDiffOpLatticeAtConstantCoweight
exists_standardCompletedPseudoDiffOpLatticeAtConstantCoweight_le
    every full finitely generated lattice L has an exact sandwich
        π^a O^r ⊆ L ⊆ π^b O^r
standardCompletedPseudoDiffOpLatticeAtCoweight_antitone
leftScaleCompletedPseudoDiffOpLattice_carrier_mono
completedPseudoDiffOpLattice_leftCommensurable
    every pair of full lattices is commensurable by correctly oriented left uniformizer
    homotheties
```

The lower inclusion uses `L.full` literally: each standard basis vector is a finite
completed-skew linear combination of lattice vectors, and one left uniformizer exponent clears
all coefficients in all finitely many supports.  No commutation of the uniformizer through a
coefficient is used.

`DifferentialVariationalRankOneBuilding` then proves that every full rank-one lattice is principal.
A nonzero finite generator of least additive valuation divides every other generator on the left;
inner-conjugation invariance of the valuation ring converts its resulting right-principal form to
the correct left-homothety form.  Consequently

```text
exists_generator_rankOne_completedPseudoDiffOpLattice
standardCompletedPseudoDiffOpLattice_leftHomothetic_rankOne
differentialVariationalProjectiveBuildingCarrierFinOne_subsingleton
```

classify the **entire** corrected projective rank-one carrier, not only its standard apartment, as
one point.  `DifferentialVariationalRankOneAction` therefore proves

```text
DifferentialFieldAut.projectiveBuildingAction_rankOne
DifferentialFieldAut.projectiveBuildingEquiv_rankOne
```

so every canonical differential automorphism acts identically in rank one.  This closes the
geometric type-`A₀` no-displacement half of §5.

All three leaves pass direct `lake env lean` checks, targeted leaf builds, and batched audits of
only their new public declarations with exactly `[propext, Classical.choice, Quot.sound]`; they are
wired into `HTGeometry`, whose umbrella was not built.

The sandwich proves boundedness/commensurability, not diagonalization.  For rank at least two the
remaining exact obligations are still simultaneous noncommutative Cartan decomposition of a pair
of lattices, its dominant relative-position vector and metric, comparison with the balanced
operator invariants, CAT(0) completeness/semisimplicity and axes, boundary flags, and the free-field
Fréchet/order reconstruction.  Card remains at Stage 2.

### Lean progress — full-lattice interleaving metric and action isometries (2026-09-02)

`DifferentialVariationalLatticeInterleaving` upgrades arbitrary-lattice commensurability to an
exact integral metric on the full space of actual valuation lattices.  It defines

```text
L.InterleavedAt n M  ⇔  πⁿL ⊆ M and πⁿM ⊆ L
completedPseudoDiffOpLatticeInterleavingDistance L M
    = the least such n
```

and proves unconditionally:

```text
leftScale_uniformizer_zpow_carrier_le_self
leftScale_uniformizer_zpow_carrier_antitone
exists_completedPseudoDiffOpLattice_interleavedAt
exists_least_completedPseudoDiffOpLattice_interleavedAt
completedPseudoDiffOpLattice_interleavedAt_zero_iff
completedPseudoDiffOpLatticeInterleavingDistance_self
completedPseudoDiffOpLatticeInterleavingDistance_comm
completedPseudoDiffOpLatticeInterleavingDistance_eq_zero_iff
completedPseudoDiffOpLatticeInterleavingDistance_triangle
```

Thus the least radius is finite for every pair, separates literal lattices, and satisfies symmetry
and the triangle inequality.  The same leaf proves exact preservation of every radius, hence of
the metric, under completed-skew linear equivalences and differential coefficient automorphisms.
Their composite `differentialVariationalLatticeSemilinearAction`, the literal representative-level
action `v ↦ σ(v)A`, is therefore an isometry.

Direct checking and the targeted leaf build pass.  A single batched audit of all 24 declarations
introduced by the leaf reports exactly `[propext, Classical.choice, Quot.sound]`.  The leaf is wired
into `HTGeometry`; the umbrella was not built.

This closes a genuine full-lattice bounded metric and the representative-level action-isometry
layer.  It does not identify this uniformizer interleaving metric with the paper's Euclidean
Cartan metric and does not descend it to homothety classes: that requires simultaneous
noncommutative Cartan decomposition and homothety-normalized relative position in rank at least
two.  Those comparison results, CAT(0) semisimplicity/axes, boundary flags, and free-field
Fréchet/order reconstruction remain open.  Card stays at Stage 2.

### Lean progress — projective metric descent and canonical action isometry (2026-09-02)

Three further leaves close quotient descent for the unconditional interleaving metric.
`DifferentialVariationalProjectiveInterleaving` proves the noncommutative conjugation step:

```text
leftScaleCompletedPseudoDiffOpLattice_eq_self_of_unitAddValue_eq_zero
leftScale_inner_uniformizer_zpow_eq
leftScale_uniformizer_zpow_leftScale
completedPseudoDiffOpLatticeInterleavingDistance_leftScale
```

A valuation-zero completed-skew unit fixes every lattice.  Hence conjugating `πⁿ` by an
arbitrary unit changes no lattice, and simultaneous arbitrary left homothety preserves literal
interleaving distance.  No false commutation of `π` through a coefficient is used.

`DifferentialVariationalProjectiveInterleavingMetric` minimizes the literal distance over the
second left-homothety orbit.  Natural-number well-ordering gives an attained minimum.  The leaf
proves representative independence in both arguments and then descends the result to
`DifferentialVariationalProjectiveBuildingCarrier`, with exact laws

```text
d(x,x) = 0
d(x,y) = d(y,x)
d(x,y) = 0 ⇔ x = y
d(x,z) ≤ d(x,y) + d(y,z).
```

`DifferentialVariationalProjectiveInterleavingAction` proves that completed-skew linear transport,
differential coefficient transport, every literal semilinear action `v ↦ σ(v)A`, and finally
the actual canonical Ore-module action preserve this projective distance exactly:

```text
DifferentialFieldAut.projectiveBuildingAction_interleavingDistance
```

All three leaves pass direct checks, targeted leaf builds, and batched audits of only their 40 new
declarations with exactly `[propext, Classical.choice, Quot.sound]`; they are wired into
`HTGeometry`, whose umbrella was not built.

This closes an unconditional separating projective metric and the canonical action-isometry claim
for that metric.  It still does not identify this integral orbit-interleaving metric with the
paper's Euclidean Cartan metric or supply a dominant Cartan vector.  Full rank-at-least-two Cartan
decomposition/comparison, CAT(0) geometry and axis semisimplicity, boundary flags, and free-field
Fréchet/order reconstruction remain open.  Card remains at Stage 2.

### Lean progress — exact standard-apartment formula for the projective metric (2026-09-02)

`DifferentialVariationalProjectiveInterleavingStandardApartment` computes the new metric on the
entire standard apartment.  First it proves two exact structural statements:

```text
leftScaleCompletedPseudoDiffOpLattice_eq_uniformizer_zpow_unitAddValue
    aL = π^{v(a)}L for every completed-skew unit a and every valuation lattice L
standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff
    L_m ⊆ L_n ⇔ ∀i, n_i ≤ m_i
```

It follows that literal interleaving is the coordinatewise centered-box condition and that the
descended projective distance has the exact upper-bound formula

```text
d([L_m],[L_n]) ≤ r
  ⇔ ∃ c : ℤ, ∀ i,
      n_i + c ≤ m_i + r  and  m_i ≤ n_i + c + r.
```

Thus common coweight translation is handled intrinsically and the projective metric is explicitly
computable on every diagonal apartment point.  Direct checking, targeted leaf build, and a batched
audit of all five declarations pass with exactly `[propext, Classical.choice, Quot.sound]`; the
leaf is wired into `HTGeometry` without building the umbrella.

This formula is the integral Chebyshev/recentering metric, not the Euclidean norm of the dominant
Cartan vector.  It therefore supplies exact comparison infrastructure but does not close the
higher-rank Cartan decomposition or the paper's Euclidean building geometry.  Card stays at
Stage 2.

### Lean progress — free-coordinate Ore basis and literal Fréchet reconstruction (2026-09-02)

`FreeDifferentialAutomorphismOrder` now defines the paper's literal Fréchet matrix `(18)` and its
jet order, proves the exact rational minimal-order characterization `(19)`, the differential
substitution cocycle and both twisted inverse identities, Fekete convergence `(20)`, the explicit
conjugacy overhead `(23)`, and invariance of the limiting speed.

`FreeDifferentialVariationalOreBasis` supplies the previously missing identification with the
intrinsic variational construction:

```text
freeVariationalOreBasis
    the classes of dx_i form an actual K[∂;δ]-basis of Ω/Tor
kaehlerD_eq_sum_frechet_smul
    du = Σ_j J(u)_j · dx_j for every free differential rational function u
variationalOreModuleEquiv_freeVariationalOreBasis_apply
variationalOre_basisMapMatrix_free_eq_freeFrechetMatrix
    the canonical action on Ω/Tor has matrix exactly J_σ in that basis
variationalOreOperatorMatrixUnit_free_val
isUnit_freeFrechetMatrix
variationalOreCompletedMatrixUnit_free_val
    J_σ is a unit already over K[∂;δ], and completion preserves that literal matrix
freeDifferentialOrder_eq_variationalOreActionMatrix_matDeg
    ord_x(σ) is degree of the actual canonical variational action matrix
freeDifferentialOrder_finOne_eq_zero
freeDifferentialOrder_pow_finOne_eq_zero
    every rank-one free differential automorphism and every iterate has order zero
```

Both leaves pass direct checks and targeted leaf builds.  Batched audits of only their new public
declarations report exactly `[propext, Classical.choice, Quot.sound]`.  Both are wired into
`HTGeometry`; no umbrella build was run.

This closes literal `(18)`, the minimal-order/matrix-degree part of `(19)`, `(20)`, `(23)`, and the
free rank-one order no-go.  It does not identify matrix degree with the largest Euclidean Cartan
component `μ₁(n)`, nor prove the boundedness equivalence `(21)` or boundary equivalence `(22)`.
Those statements still require higher-rank noncommutative Cartan decomposition, the paper's
Euclidean building metric, CAT(0) semisimplicity/axes, and boundary flags.  Card remains at Stage 2.

### Lean progress — literal rank-two clock shear and exact unit cost (2026-09-02)

`FreeDifferentialClockShear` constructs the paper's rank-two witness as an actual differential
automorphism of the free jet field.  Its mutually inverse polynomial substitutions are

```text
x_n ↦ y_n                 x_n ↦ -x_{n+1} + y_n
y_n ↦ x_n + y_{n+1}       y_n ↦ x_n,
```

and the construction proves both polynomial composition identities before lifting the equivalence
to the fraction field and proving that it commutes with the jet derivation.  Hence this is a
bundled `FreeAut`, not a matrix-only surrogate.

In the canonical free-coordinate Ore basis, its literal Fréchet matrix is

```text
J = !![0, 1; 1, ∂].
```

The leaf proves the persistent leading-coefficient chain for every matrix power, compatibility of
coefficient transport with `J` and all its powers, and therefore the exact identities

```text
freeFrechetMatrix (freeClockShear ^ (n + 1)) = J ^ (n + 1)
DiffOp.matDeg (J ^ n) = n
freeDifferentialOrder (freeClockShear ^ n) = n
freeOrderGauge.translationLength freeClockShear = 1.
```

Direct checking and the targeted leaf build pass.  A batched audit of all 27 new public
declarations reports exactly `[propext, Classical.choice, Quot.sound]`.  The leaf is wired into
`HTGeometry`; no umbrella build was run.

This closes the exact free-field rank-two clock witness and unit asymptotic cost claimed in `(24)`.
It does not manufacture the paper's dominant Cartan vector `(n,-n)`: that literal statement still
depends on a higher-rank Cartan decomposition for the completed noncommutative valuation ring.
The Euclidean Cartan metric, CAT(0) semisimplicity/axes, and boundary flags remain open, so the card
remains at Stage 2.

### Lean progress — exact projective orbit distance of the clock shear (2026-09-02)

`DifferentialVariationalOperatorMatrixInterleaving` converts projective lattice interleaving for
an arbitrary invertible Ore matrix into an exact entrywise degree criterion.  It first proves that
the completed valuation of every embedded nonzero differential operator is the negative of its
Ore degree.  It then characterizes both standard-lattice containments for a left-scaled matrix
orbit, including the inverse-matrix containment and the noncommutative inner-conjugation needed
for arbitrary left scalars.  The resulting equivalence is

```text
standard.LeftOrbitInterleavedAt n (U · standard)
  ⇔ ∃ z : ℤ,
      (∀ i j, (U⁻¹)ᵢⱼ = 0 ∨ degree (U⁻¹)ᵢⱼ ≤ n - z) ∧
      (∀ i j, Uᵢⱼ = 0 ∨ degree Uᵢⱼ ≤ n + z).
```

No commutativity of the completed skew field is assumed: every arbitrary homothety is reduced to
its exact uniformizer power using its additive value, while the remaining value-zero unit acts by
an integral inner automorphism.

`FreeDifferentialClockShearOrbit` constructs the literal inverse Ore matrix

```text
J⁻¹ = !![-∂, 1; 1, 0]
```

and proves both two-sided inverse identities.  Its persistent inverse leading chain gives
`matDeg ((J⁻¹)^n) = n`; together with the existing forward identity
`matDeg (J^n) = n`, this supplies degree-`n` entries on both sides.  Consequently every
projective recentering integer `z` at radius `d` obeys simultaneously
`n ≤ d + z` and `n ≤ d - z`.  The exact orbit law follows:

```text
completedPseudoDiffOpLatticeOrbitInterleavingDistance
  standard (freeClockShearCompletedOrbitLattice n) = n.
```

Finally, the same leaf identifies this matrix orbit with the actual canonical variational action
in the proved free Ore basis.  Coefficient transport fixes the standard lattice, and the canonical
completed action matrix of `freeClockShear^n` is exactly the completed embedding of `J^n`.
Therefore the action-level statement is literal:

```text
projectiveInterleavingDistance
  freeClockShearProjectiveBasePoint
  ((freeClockShear^n).projectiveBuildingAction
    freeVariationalOreBasis freeClockShearProjectiveBasePoint) = n.
```

Both leaves pass direct checks and targeted leaf builds.  One batched audit of their 30 new public
declarations reports exactly `[propext, Classical.choice, Quot.sound]`.  Both are wired into
`HTGeometry`; no umbrella build was run.

This closes an exact rank-two geometric unit-cost law for the unconditional projective
interleaving metric, with minimization over every left homothety rather than a fixed
representative.  It does not identify that metric with the paper's Euclidean Cartan metric or
construct the dominant Cartan vector `(n,-n)`.  Higher-rank noncommutative Cartan decomposition,
Euclidean comparison, CAT(0) axes, and boundary flags remain open.  Card remains at Stage 2.

### Lean progress — bi-infinite canonical clock axis (2026-09-02)

`FreeDifferentialClockShearAxis` extends the actual projective clock orbit from natural iterates
to every integer iterate:

```text
freeClockShearProjectiveOrbitPoint z
  = (freeClockShear^z).projectiveBuildingAction
      freeVariationalOreBasis freeClockShearProjectiveBasePoint.
```

Action functoriality and projective-metric isometry transport the positive-power calculation across
inverse powers and arbitrary orbit origins.  The exact pairwise formula is

```text
projectiveInterleavingDistance
  (freeClockShearProjectiveOrbitPoint m)
  (freeClockShearProjectiveOrbitPoint n)
  = Int.natAbs (n - m).
```

Thus the literal canonical variational action has a bi-infinite unit-speed metric axis, rather than
only an asymptotic order calculation or a one-sided orbit estimate.
`DifferentialVariationalProjectiveInterleavingMetricSpace` also promotes the natural-number
distance to a genuine separated real-valued `MetricSpace`, preserving its exact integral values.
In this metric the orbit map itself satisfies mathlib's `Isometry` predicate:

```text
Isometry (freeClockShearProjectiveOrbitPoint : ℤ → B).
```

Direct checks and targeted leaf builds pass.  A batched audit of all seven public declarations
introduced by the metric-space and axis leaves reports exactly
`[propext, Classical.choice, Quot.sound]`.  Both leaves are wired into `HTGeometry`, and the
umbrella was not built.

This is an exact axis for the unconditional projective interleaving metric.  Identifying it with a
Euclidean geodesic in the paper's affine building, constructing its visual-boundary endpoints, and
recovering the dominant Cartan vector `(n,-n)` still require the missing noncommutative Cartan and
CAT(0) layers.  Card remains at Stage 2.

### Lean progress — canonical action bundled by metric isometries (2026-09-02)

`DifferentialVariationalProjectiveInterleavingIsometry` upgrades every canonical variational
action from an equality-of-distance theorem to a mathlib `IsometryEquiv`:

```text
projectiveBuildingInterleavingIsometryEquiv σ b : B ≃ᵢ B.
```

The bundled isometries obey chronological multiplication and the identity law exactly, using the
already-proved canonical projective action rather than a parallel action definition.  Direct
checking, targeted leaf build, and a batched audit of all four new declarations pass with exactly
`[propext, Classical.choice, Quot.sound]`.  The leaf is umbrella-wired without an umbrella build.

This closes the functorial “action by isometries” assertion for the unconditional projective
interleaving metric.  It does not identify that metric with the paper's Euclidean Cartan metric;
the balance, asymptotic Cartan vector, and visual-boundary claims remain open.  Card remains at
Stage 2.

### Lean progress — completeness of the projective interleaving metric (2026-09-02)

`DifferentialVariationalProjectiveInterleavingComplete` proves a genuine `CompleteSpace`
instance for every finite-rank projective lattice carrier equipped with the interleaving metric.
The proof uses the exact integral distance: a Cauchy filter has a member of diameter strictly below
one, hence that member is a singleton, so the filter converges.  No local compactness, residue-field
finiteness, or external building theorem is assumed.

Direct checking, targeted leaf build, and the new-instance axiom audit pass with exactly
`[propext, Classical.choice, Quot.sound]`.  The leaf is wired into `HTGeometry`; no umbrella
build was run.

This closes completeness for the unconditional projective interleaving metric.  Completeness alone
does not supply CAT(0), geodesic interpolation, noncommutative Cartan decomposition, or visual
boundary flags, so the paper's Euclidean phase theorem remains open and the card stays at Stage 2.

### Lean progress — faithful Euclidean realization of the standard apartment (2026-09-03)

`DifferentialVariationalEuclideanStandardApartment` constructs the literal real type-`A`
coweight hyperplane and embeds every integral standard-apartment vertex into it.  For an integral
coweight `m`, its canonical representative is

```text
m_i - (sum_j m_j) / r.
```

The leaf proves this representative has sum zero, is invariant under every common integral
translation, and separates the quotient classes.  Consequently

```text
standardApartmentEuclideanEmbedding
```

is injective into the actual Euclidean space `{x : R^r | sum_i x_i = 0}`.  It also proves that every
integral coweight admits a decreasing (dominant) permutation preserving its total sum.  Thus the
continuous Euclidean apartment, determinant-balance hyperplane, integral vertices, and dominant
Weyl chamber now coexist without replacing Euclidean geometry by the interleaving metric.

The zero-sum apartment is a closed subspace of finite-dimensional Euclidean space, so the leaf also
installs its genuine `CompleteSpace` instance.  It constructs the literal straight segment between
any two apartment points, proves its two endpoint laws, and proves the exact constant-speed formula
`d(gamma(s),gamma(t))=|s-t|d(x,y)`; zero-sum balance is preserved at every real parameter.

Direct checking, the targeted leaf build, and a batched audit of all eighteen new declarations pass
with exactly `[propext, Classical.choice, Quot.sound]`; the leaf is umbrella-wired and no umbrella
build was run.

This is exact apartment infrastructure, not the still-missing global theorem.  Remaining work is
the noncommutative Cartan decomposition identifying arbitrary lattice pairs with these apartment
coordinates, gluing apartments into the Euclidean affine building and proving its CAT(0)
semisimplicity, and identifying axial endpoints with weighted residue flags.  The card remains at
Stage 2.

### Lean progress — arbitrary-lattice noncommutative Cartan decomposition (2026-09-03)

The previously named Cartan-decomposition gap is now closed unconditionally for the actual
completed pseudodifferential skew field and its actual valuation lattices.

`CompletedPseudoDiffOpIntegerPrincipal`, `CompletedPseudoDiffOpLatticeSplitting`, and
`CompletedPseudoDiffOpLatticeBasis` prove two-sided valuation divisibility, principality of every
finitely generated fractional left ideal, coordinate splitting, and an integral basis of exactly
the ambient rank for every full lattice.  The basis remains a basis after scalar extension to the
completed skew field.

`CompletedPseudoDiffOpValuationDiagonal` proves a genuinely noncommutative Smith-style reduction:
a globally least-valuation matrix entry divides every entry on both sides, integral left row
shears and right column shears isolate it, and recursion on the complementary block diagonalizes
every finite completed-skew matrix.  `CompletedPseudoDiffOpValuationShear` realizes every column
shear by an actual completed-skew linear equivalence preserving the standard lattice and proves
that row shears preserve the integral row span.

`CompletedPseudoDiffOpLatticeCartan` assembles these facts into the exact capstones

```text
exists_completedPseudoDiffOpLattice_cartan_standard
exists_completedPseudoDiffOpLattice_pair_cartan
```

For arbitrary full lattices `L,M`, one completed-skew linear frame sends `L` to the standard
lattice and `M` to a literal uniformizer-coweight lattice.  No commutativity, chosen matrix
presentation, lattice-basis premise, or diagonalizability premise is assumed.  The seven new leaves
pass direct checks and targeted leaf builds; batched audits of their new capstones report exactly
`[propext, Classical.choice, Quot.sound]`.  They are wired into `HTGeometry`; no umbrella build was
run.

This supplies existence of arbitrary-pair Cartan coordinates, but not yet their uniqueness as a
dominant Weyl-chamber vector.  Remaining global obligations are uniqueness/invariance of the
dominant relative position, gluing continuous apartments into the Euclidean affine building,
CAT(0) semisimplicity and axes, and identification of visual endpoints with weighted residue
flags.  The card remains at Stage 2.

### Lean progress — canonical dominant relative position (2026-09-03)

`CompletedPseudoDiffOpResidue` constructs the strict completed-valuation ideal, proves it is a
two-sided maximal ideal, and proves that its quotient is a division ring.  Thus a
standard-lattice stabilizer has an honest invertible reduction over the residue skew field.

`CompletedPseudoDiffOpCartanUniqueness` uses that reduction to prove a division-ring Hall rank
inequality for every matrix support cut.  A nonzero reduced matrix entry can carry a source
coweight only to a target coweight no larger than it.  Hall inequalities for all integral
sublevels, applied also to the inverse stabilizer, recover every exact coweight multiplicity.
Consequently two Cartan reductions of the same ordered pair differ only by a Weyl permutation.

The leaf realizes the sorting permutation by an actual completed-skew coordinate linear
equivalence preserving the standard lattice.  It therefore proves existence and exact uniqueness
of a decreasing Cartan vector and exposes the canonical invariant

```text
completedPseudoDiffOpDominantRelativePosition L M : Fin r → ℤ.
```

Every dominant simultaneous reduction computes this same vector.  Both new leaves pass direct
checks and targeted leaf builds.  A batched audit of all their new public declarations reports
exactly `[propext, Classical.choice, Quot.sound]`.  Both are wired into `HTGeometry`; no umbrella
build was run.

This closes uniqueness/invariance of dominant relative position.  Remaining global obligations
are gluing continuous apartments into the Euclidean affine building, CAT(0) semisimplicity and
axes, identification of visual endpoints with weighted residue flags, and the full Theorem B/free-
field endpoint equivalences.  Card remains at Stage 2.

### Lean progress — projective Euclidean relative-position vector (2026-09-03)

`CompletedPseudoDiffOpProjectiveRelativePosition` proves the exact transformation law for the
canonical dominant Cartan vector under independent changes of both lattice representatives.
Scaling the second lattice adds the scalar valuation to every coordinate; scaling the first
subtracts it.  Centering therefore removes both common translations.

The leaf packages the centered vector as a literal point of the zero-sum Euclidean apartment and
descends it through both quotient arguments to the actual projective lattice carrier:

```text
differentialVariationalProjectiveEuclideanRelativePosition
```

It also proves the representative formula and both lattice-scale invariance laws.  Direct checking
and the targeted leaf build pass.  The batched audit of all new declarations, together with the two
new canonical-frame computation laws, reports exactly
`[propext, Classical.choice, Quot.sound]`.  The leaf is wired into `HTGeometry`; no umbrella build
was run.

This closes descent of the vector-valued Cartan invariant to projective vertices, but does not
construct the continuous global affine building or establish CAT(0), semisimplicity, axes, visual
boundary flags, the differential rank identity, or the full Theorem B/free-field endpoint
equivalences.  Card remains at Stage 2.

### Lean progress — exact vector-valued isometry of the canonical action (2026-09-03)

`CompletedPseudoDiffOpProjectiveEuclideanAction` proves that every finite completed-skew linear
equivalence is represented by an invertible row-action matrix and uses this representation to
transport arbitrary Cartan frames through differential coefficient automorphisms.  It follows
that coefficient transport preserves the complete canonical dominant Cartan vector, not merely
its interleaving radius.

Consequently completed-skew linear transport, coefficient transport, and their semilinear
composition all preserve the centered projective Euclidean relative-position point exactly.  The
canonical variational Ore action therefore satisfies

```text
DifferentialFieldAut.projectiveBuildingAction_euclideanRelativePosition
```

in every finite operator basis.  This is the vector-valued isometry assertion of Theorem A on the
actual projective completed-lattice carrier.  Direct checking and the targeted leaf build pass;
all thirteen new declarations audit to exactly `[propext, Classical.choice, Quot.sound]`.  The leaf
is wired into `HTGeometry`; no umbrella build was run.

Remaining work is the continuous global affine-building realization and CAT(0) semisimplicity,
axes, visual boundary flags, asymptotic phase dichotomy, and full free-field endpoint identities.
Card remains at Stage 2.

### Lean progress — literal rank-two Cartan vector `(n,-n)` (2026-09-03)

`FreeDifferentialClockShearCartan` upgrades the earlier scalar interleaving-distance computation to
the complete dominant Cartan vector.  Two general inclusion equivalences identify sharp uniformizer
rescalings of a matrix-image lattice with lower and upper coordinate bounds on its canonical
relative-position vector.  The clock matrix and its inverse both have exact maximum operator degree
`n`; applying the two sharp inclusion tests to each side gives, for every `n`,

```text
completedPseudoDiffOpDominantRelativePosition_freeClockShear n
  = ![(n : ℤ), -(n : ℤ)].
```

Thus the full finite-iterate assertion `μ_n=(n,-n)` in `(25)` is now Lean, without assuming a
determinant-balance theorem.  Direct checking, the targeted leaf build, and the axiom audit of all
three new declarations pass; each declaration reports exactly
`[propext, Classical.choice, Quot.sound]`.  The leaf is wired into `HTGeometry`; no umbrella build
was run.

The general balance law for every variational operator matrix and the global CAT(0)/boundary phase
theorem remain open.  Card remains at Stage 2.

### Lean progress — arbitrary operator-matrix Cartan extrema (2026-09-03)

`DifferentialOperatorCartanExtrema` proves the two sharp endpoint identities for every invertible
positive-rank matrix over the differential Ore ring.  For the canonical dominant relative-position
vector from the standard completed lattice to its matrix image, the last coordinate is minus the
maximum operator degree of the matrix, while the zeroth coordinate is the maximum operator degree
of its inverse:

```text
completedPseudoDiffOpDominantRelativePosition_last_eq_neg_matDeg
completedPseudoDiffOpDominantRelativePosition_zero_eq_inv_matDeg
```

The proof first shows that a matrix unit has a nonzero entry attaining its matrix degree, including
degree zero, and then combines this witness with the two exact completed-lattice inclusion tests.
Direct checking and the targeted leaf build pass.  All three new declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`.  The leaf is wired into `HTGeometry`; no umbrella build
was run.

This closes arbitrary finite-rank Cartan endpoint control.  The general coordinate-sum balance law,
global CAT(0) realization, boundary phase theorem, and remaining free-field equivalences remain
open.  Card remains at Stage 2.

### Lean progress — exact free differential order/Cartan identity `(19)` (2026-09-03)

`DifferentialOperatorCartanExtrema` now also proves the reversed-pair endpoint formula: for a
matrix-image lattice paired back to the standard lattice, its top canonical dominant Cartan
coordinate is the operator degree of the original matrix.  `FreeDifferentialOrderCartan` applies
this formula to the canonical variational Ore matrix and its literal Fréchet-matrix identification,
giving

```text
freeDifferentialOrder_eq_topCartan
```

in every positive finite free differential rank.  This is the exact Lean form of `(19)` for one
automorphism; applying it to each iterate gives the stated finite-iterate identity without any new
premise.  Direct checks and targeted builds pass.  Both new declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`.  Both leaves are wired into `HTGeometry`; no umbrella
build was run.

Remaining work is the general coordinate-sum balance law, continuous global CAT(0) building,
semisimplicity/axes and visual boundary flags, asymptotic phase dichotomy, and the remaining
free-field endpoint consequences.  Card remains at Stage 2.

### Lean progress — exact uniformizer-power quotient lengths (2026-09-03)

`CompletedPseudoDiffOpUniformizerResidue` packages the canonical inverse derivative inside the
completed valuation ring, proves that it generates the strict maximal ideal, and identifies the
residue quotient as one simple composition factor.  `CompletedPseudoDiffOpUniformizerPowerLength`
then identifies every principal uniformizer-power lattice with the integer ring, proves every
adjacent layer has module length one, constructs the exact consecutive quotient sequence, and
deduces the unconditional formula

```text
completedPseudoDiffOpUniformizerPowerQuotient_length n :
  length(O / O·∂⁻ⁿ) = n.
```

Direct checks and targeted leaf builds pass.  The batched audit of all twenty new declarations in
the two leaves reports exactly `[propext, Classical.choice, Quot.sound]`.  Both leaves are wired
into `HTGeometry`; no umbrella build was run.

This supplies the exact local length unit needed to define and compute additive relative indices
of completed lattices.  Identification of the Cartan coordinate sum with the variational Ore
balance, continuous global CAT(0) realization, semisimplicity/axes, boundary flags, and the
asymptotic phase theorem remain open.  Card remains at Stage 2.

### Lean progress — unconditional finite-rank Cartan balance `(12)` (2026-09-03)

The completed-lattice length chain now includes arbitrary coweight intervals, arbitrary relative
lattice quotients, exact length additivity for nested lattices, and the additive integral Cartan
index.  `DifferentialOperatorCompletedCartanBalance` proves that this index vanishes for every
matrix unit over the differential Ore ring.  Its proof uses only actual Ore row-column reduction:
elementary operator transvections have zero index, every reduced diagonal matrix unit and its
inverse have order-zero entries, and hence the reduced matrix fixes the standard completed
valuation lattice.

Consequently the literal dominant relative-position vector satisfies

```text
differentialOperatorMatrixCartanBalance
variationalOreCartanBalance
```

for every invertible finite operator matrix and every canonical finite-basis variational Ore
action, respectively.  The same leaf states the balance for every finite iterate and packages a
finite-basis all-iterate form directly from finite differential generation.  This closes equation
`(12)` without a determinant premise, a chosen diagonal form, or any extra proposition hypothesis.
`FreeDifferentialOrderCartan` likewise now states `(19)` explicitly for every iterate.  Direct
checking and the targeted leaf builds pass.  All thirty-eight declarations in the new balance
leaf, and the new free-iterate declaration, audit to exactly
`[propext, Classical.choice, Quot.sound]`.  The leaf is wired into `HTGeometry`; no umbrella build
was run.

Remaining work is the continuous global affine-building realization, CAT(0) semisimplicity and
axes, visual weighted boundary flags, the asymptotic phase dichotomy, and the remaining free-field
endpoint equivalences.  Card remains at Stage 2.

### Lean progress — exact operator rank/differential-transcendence identity `(4)` (2026-09-03)

`DifferentialVariationalRank` closes the basis-free operator-rank identity in `(4)`.  It first
turns every differential-algebraicity relation into an explicit nonzero operator annihilating the
corresponding universal differential modulo Ore torsion.  For every finite index type it then
proves the exact equivalences

```text
DifferentialIndependent C y
  ↔ LinearIndependent (DiffOp K) [d y_i]
  ↔ LinearIndependent (PseudoDiffOp K) localized-coordinate-row(y_i).
```

For an arbitrary finite differential generating tuple, a differential-matroid basis of its range
is consequently a skew-field basis of the localized coordinate space attached to every finite
operator basis.  Cardinal comparison gives the unconditional theorem

```text
variationalOreModule_rank_eq_differentialTranscendenceDegree :
  Module.rank (DiffOp K) (VariationalOreModule C K) =
    constantBaseDifferentialTranscendenceDegree C K.
```

The right side is the corpus's `differentialTranscendenceDegree` with the base equipped internally
with its canonical zero derivation and the induced `DifferentialAlgebra C K` structure.  No new
premise is exposed.  The leaf also proves that differential generators span the quotient and its
localized coordinate space.  Direct checking and the targeted leaf build pass.  All twelve new
public declarations audit to only `[propext, Classical.choice, Quot.sound]`.  The leaf is wired
into `HTGeometry`; no umbrella build was run.

This closes `rank_(R_K) M_K = differential-trdeg_C K` and the finite skew-field coordinate
dimension comparison.  The literal noncommutative balanced tensor-product carrier
`Q_K tensor_(R_K) M_K` is not yet packaged in the corpus, so its displayed middle equality in
`(4)` is not claimed as a separate Lean theorem.  Continuous affine-building gluing, CAT(0)
semisimplicity/axes, visual boundary flags, the global phase dichotomy, and the remaining
free-field endpoint equivalences also remain.  Card remains at Stage 2.

### Lean progress — exact reversal of Euclidean Cartan position (2026-09-03)

`CompletedPseudoDiffOpRelativePositionSymmetry` proves the ordered-pair reversal law for arbitrary
actual completed valuation lattices.  If `mu(L,M)` is the canonical decreasing Cartan vector, then

```text
mu(M,L)_i = -mu(L,M)_(rev i).
```

The proof constructs the reverse Cartan frame explicitly: it applies the inverse diagonal
coweight to exchange the standard and displaced lattices, then reverses the finite coordinate
frame to return to the dominant chamber.  It also proves self-position is zero, centering commutes
with this reversal, and therefore the Euclidean norm of the centered projective position is
symmetric.  The leaf exposes

```text
differentialVariationalProjectiveEuclideanVertexDistance
```

as the literal Euclidean norm of the centered Cartan vector and proves nonnegativity, diagonal
vanishing, and symmetry.  Direct checking, the targeted leaf build, and the batched audit of all
eighteen new declarations pass; every declaration uses at most
`[propext, Classical.choice, Quot.sound]`.  The leaf is wired into `HTGeometry`; no umbrella build
was run.

This is the exact symmetry layer needed for the Euclidean vertex metric.  Its triangle inequality
still requires Cartan-product majorization, and the continuous affine-building gluing, CAT(0)
semisimplicity/axes, visual boundary flags, global phase dichotomy, literal balanced tensor
carrier, and remaining free-field endpoint equivalences remain open.  Card remains at Stage 2.

### Lean progress — Euclidean vertex isometries and rank-two displacement (2026-09-03)

`CompletedPseudoDiffOpProjectiveEuclideanAction` now proves that completed-skew linear transport,
differential coefficient transport, their semilinear composition, and every canonical variational
Ore action preserve `differentialVariationalProjectiveEuclideanVertexDistance` exactly.

`FreeDifferentialClockShearEuclidean` evaluates that distance on the literal canonical rank-two
orbit.  Combining the already-proved Cartan vector `(n,-n)` with the genuine type-`A_1` Euclidean
norm gives

```text
freeClockShear_euclideanVertexDistance n = sqrt(2) * n.
```

Both direct checks and targeted builds pass.  A batched audit of the five new declarations reports
exactly `[propext, Classical.choice, Quot.sound]`.  The new leaf is wired into `HTGeometry`; no
umbrella build was run.

This closes the vector-norm displacement and action-invariance pieces on actual vertices.  The
Euclidean vertex triangle inequality still requires Cartan-product majorization; continuous
apartment gluing, CAT(0), semisimplicity/axes, visual flags, the global phase dichotomy, literal
balanced tensor carrier, and remaining free-field endpoint equivalences remain open.  Card remains
at Stage 2.

### Lean progress — literal noncommutative rational tensor carrier (2026-09-03)

`DifferentialOreLocalizationTensor` constructs the scalar extension displayed in `(3)` as a
literal noncommutative balanced quotient.  For every left `K[∂;δ]`-module `M`, the free left
`Q_K`-module on `M` is divided by additivity and the Ore balance relation

```text
1 ⊗ (a • m) = a ⊗ m.
```

Thus no commutative tensor-product surrogate is used.  Every finite operator basis induces and is
proved to invert a `Q_K`-linear equivalence between this quotient and `Q_K^r`.  Specializing to the
torsion-free variational Kähler module gives the unconditional equality

```text
rank_(Q_K) (Q_K tensor_(K[∂;δ]) M_K)
  = rank_(K[∂;δ]) M_K
  = differential-trdeg_C K.
```

This closes all three literal terms in `(4)`.  Direct checking and the targeted leaf build pass.
The batched audit of all twenty-one new declarations reports exactly
`[propext, Classical.choice, Quot.sound]`; the leaf is wired into `HTGeometry`, and no umbrella
build was run.

Remaining work is Cartan-product majorization and the Euclidean vertex triangle inequality,
continuous affine-building gluing, CAT(0) semisimplicity/axes, visual boundary flags, the global
phase dichotomy, and remaining free-field endpoint equivalences.  Card remains at Stage 2.

### Lean progress — exact Euclidean vertex separation (2026-09-03)

`CompletedPseudoDiffOpEuclideanSeparation` proves that a centered dominant Cartan vector vanishes
exactly when the uncentered coweight is constant.  Pulling the resulting standard-lattice
homothety back through the actual Cartan frame gives

```text
completedPseudoDiffOpEuclideanRelativePosition L M = 0
  iff L.LeftHomothetic M.
```

Passing to the projective quotient proves exact point separation and its strict-positivity form:

```text
differentialVariationalProjectiveEuclideanVertexDistance x y = 0 iff x = y,
0 < differentialVariationalProjectiveEuclideanVertexDistance x y iff x != y.
```

The proof includes the rank-zero carrier rather than imposing positive rank.  Direct checking and
the targeted leaf build pass.  All five new declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`; the leaf is wired into `HTGeometry`, and no umbrella
build was run.

Together with nonnegativity and symmetry, only Cartan-product majorization and its Euclidean
triangle consequence remain before this vertex function is a metric.  Continuous affine-building
gluing, CAT(0) semisimplicity/axes, visual boundary flags, the global phase dichotomy, and remaining
free-field endpoint equivalences also remain.  Card stays at Stage 2.

### Lean progress — exact Cartan majorization and Euclidean vertex triangle (2026-09-03)

`CompletedPseudoDiffOpEuclideanTriangle` constructs the literal meet of any two full completed
valuation lattices and proves its carrier is their submodule intersection.  An injective map from
the triple-intersection quotient layer into the second pair quotient gives the unconditional
asymmetric finite-length triangle.  In simultaneous Cartan coordinates this length is exactly the
hinge sum

```text
sum_i max(0, mu_i - t).
```

Uniformizer shifts therefore turn the length triangle into every hinge inequality for a Cartan
product.  The integral threshold identity for decreasing coweights converts these inequalities
into every top-`k` majorization inequality.  The already-proved Cartan-index cocycle centers that
majorization without loss, and the finite-dimensional Karamata/Minkowski compiler yields the exact
projective vertex triangle

```text
differentialVariationalProjectiveEuclideanVertexDistance x z
  <= differentialVariationalProjectiveEuclideanVertexDistance x y
     + differentialVariationalProjectiveEuclideanVertexDistance y z.
```

No abstract metric or building premise is used, and rank zero is included.  Direct checking and
the targeted leaf build pass.  All thirty-two new declarations audit to at most
`[propext, Classical.choice, Quot.sound]`; the leaf is wired into `HTGeometry`, and no umbrella
build was run.

This closes Cartan-product top-sum majorization and the exact Euclidean vertex triangle.  The
remaining exact obligations are continuous affine-building gluing, CAT(0) geometry,
semisimplicity/axes, visual boundary flags, the global asymptotic phase dichotomy, and remaining
free-field reconstruction endpoint equivalences.  Card stays at Stage 2.

`CompletedPseudoDiffOpEuclideanMetricSpace` packages this function as literal `PseudoMetricSpace`
and `MetricSpace` structures.  They are named values, not competing global instances, so the
Euclidean metric coexists coherently with the earlier integral interleaving metric on the same
carrier.  Its direct check and targeted build pass; all three declarations audit to at most
`[propext, Classical.choice, Quot.sound]` and the leaf is wired into `HTGeometry`.

`CompletedPseudoDiffOpEuclideanComplete` proves the Euclidean vertex metric itself is complete.
Centered integral coweights give a rank-independent separation radius: distance below `1/2`
forces equality, including ranks zero and one.  Hence every Euclidean Cauchy filter is eventually
a singleton.  Direct checking and the targeted build pass; all three declarations audit to at
most `[propext, Classical.choice, Quot.sound]`, and the leaf is umbrella-wired.  This is
completeness of the literal vertex carrier; continuous apartment gluing and CAT(0) geometry of the
full geometric realization remain separate obligations.

`CompletedPseudoDiffOpProjectiveEuclideanIsometry` upgrades exact distance invariance to literal
`Isometry` values for every completed-skew semilinear projective action.  For each bundled
differential-field automorphism, the existing inverse-automorphism carrier equivalence and this
distance theorem assemble into a genuine `IsometryEquiv` of the named Euclidean metric space.
Its multiplication and identity laws prove the action is functorial at the literal isometry level.
Direct checking and the targeted leaf build pass; all six new declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, and the leaf is wired into `HTGeometry`.  No umbrella
build was run.  This closes metric-level action packaging but does not supply the still-missing
continuous affine-building realization, CAT(0) geometry, axes, or boundary theory; card stays at
Stage 2.

`CompletedPseudoDiffOpProjectiveEuclideanBasisIsometry` packages every invertible completed-skew
matrix action, and in particular every completed operator-basis transition, as a literal Euclidean
`IsometryEquiv`.  The denominator-free twisted change-of-basis identity now yields exact conjugacy
of canonical differential-field actions in any two finite operator bases.  Direct checking and the
targeted leaf build pass; all four new declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, and the leaf is wired into `HTGeometry` without an
umbrella build.  This closes Theorem A's functoriality and basis-independence at the complete
Euclidean vertex-metric level.  Continuous affine realization and Theorem B's CAT(0)/axis/boundary
claims remain, so the card stays at Stage 2.

`DifferentialOperatorCompletedCartanBalanceEveryLattice` removes the standard-base restriction
from equation (12).  Simultaneous semilinear transport preserves Cartan index, and the additive
Cartan cocycle proves that displacement from an arbitrary lattice equals the matrix Cartan
character.  Since every invertible differential-operator matrix has character zero, every
canonical variational action and every finite iterate is exactly balanced from every completed
valuation lattice.  Direct checking and the targeted leaf build pass; all six new declarations
audit to exactly `[propext, Classical.choice, Quot.sound]`, and the leaf is wired into `HTGeometry`
without an umbrella build.  Equation (12) is now fully base-point independent.  Theorem B's
continuous affine realization and axis/boundary phase law remain, so the card stays at Stage 2.

`DifferentialVariationalEuclideanTranslationLength` constructs the Euclidean orbit-displacement
gauge on the full differential-automorphism group and proves its exact subadditivity.  Fekete's
lemma gives unconditional convergence of normalized scalar Euclidean orbit distance.  A uniform
two-base-point bound proves lattice-base independence; exact transition-matrix conjugacy proves
finite operator-basis independence.  Direct checking and the targeted leaf build pass; all nine
new declarations audit to exactly `[propext, Classical.choice, Quot.sound]`, and the leaf is wired
into `HTGeometry` without an umbrella build.  This closes existence and intrinsicness of the
scalar Euclidean translation speed.  Vector-valued coweight convergence, zero-speed rigidity,
axes, continuous CAT(0) realization, and weighted boundary flags remain, so the card stays at
Stage 2.

`DifferentialVariationalCartanTranslationVector` closes the vector-valued limit in `(14)` without
assuming CAT(0) geometry.  Every top-`k` Cartan sum is proved nonnegative and subadditive on an
orbit by the already-established Cartan majorization triangle.  Fekete convergence for all
fundamental-weight coordinates reconstructs the full coordinatewise limit

```text
differentialVariationalCartanTranslationVector
tendsto_differentialVariationalCartanTranslationVector.
```

The limit is proved dominant and exactly balanced, and uniform two-base-point prefix bounds plus
exact basis-transition conjugacy make it independent of every lattice base point and finite
operator basis.  Direct checking and the targeted leaf build pass; all twenty new declarations
audit to exactly `[propext, Classical.choice, Quot.sound]`, and the leaf is wired into `HTGeometry`
without an umbrella build.

Thus `(14)` and `(15)` now hold intrinsically at the complete projective vertex level.  Remaining
obligations are zero-vector rigidity (bounded orbit/fixed point), continuous affine-building
realization, semisimple axes, visual attracting/repelling weighted flags, and corresponding
free-field phase endpoint equivalences.  Card stays at Stage 2.

`DifferentialVariationalCartanTranslationNorm` identifies the independently constructed scalar
Fekete speed with the literal Euclidean norm of the full intrinsic Cartan translation vector:

```text
differentialVariationalEuclideanTranslationLength
  = differentialVariationalCartanTranslationVectorEuclideanNorm.
```

It also proves, without a rank or positivity premise, that scalar speed vanishes exactly when the
complete Cartan vector vanishes.  Direct checking and the targeted leaf build pass; all five new
declarations audit to exactly `[propext, Classical.choice, Quot.sound]`, and the leaf is wired into
`HTGeometry` without an umbrella build.  This closes the scalar/vector norm comparison in `(14)`
and the zero-speed/zero-vector equivalence.  Bounded-orbit/fixed-point rigidity, continuous affine
realization, semisimple axes, visual weighted flags, and free-field phase endpoints remain, so the
card stays at Stage 2.

`FreeDifferentialCartanTranslationSpeed` closes the exact free-field reconstruction endpoint from
finite iterate to asymptotic speed.  It first identifies the canonical free action on the literal
standard projective completed-lattice point.  Respecting the matrix-degree orientation, it proves
that `freeDifferentialOrder sigma` is the top centered Cartan coordinate from the orbit point back
to the base point.  Reversing the already-constructed intrinsic vector then gives a dominant,
balanced order-oriented translation vector and the exact equality

```text
freeOrderGauge.translationLength sigma
  = freeDifferentialReverseCartanTranslationVector sigma 0
  = -differentialVariationalCartanTranslationVector ... sigma (Fin.last r).
```

Thus `(19)` and `(20)`, including identification with the largest component of `(14)` in the
paper's orbit-to-base convention, are now unconditional on the actual projective vertex carrier.
Direct checking and the targeted leaf build pass.  All ten new declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`; the leaf is wired into `HTGeometry`, and no umbrella
build was run.  The strict zero-speed/bounded-order equivalence `(21)`, boundary equivalence `(22)`,
continuous affine realization, axes, and weighted visual flags remain, so the card stays at Stage
2.

`FreeDifferentialBoundedOrbit` closes the finite-displacement comparison inside `(21)`.  For every
iterate, the free differential order is bounded above by the literal Euclidean displacement of the
standard projective lattice vertex.  Conversely, dominance and exact Cartan balance bound every
coordinate, hence the Euclidean displacement, by the square of the rank times that order.  Thus

```text
FreeDifferentialEuclideanOrbitBounded sigma
  iff FreeDifferentialOrderPowersBounded sigma.
```

No properness, CAT(0), or phase assumption enters this equivalence.  Direct checking and the
targeted leaf build pass; all seven new public declarations audit to at most
`[propext, Classical.choice, Quot.sound]`.  The leaf is wired into `HTGeometry`; no umbrella build
was run.  The remaining strict part of `(21)` is now exactly zero-speed versus bounded orbit/fixed
point.  Continuous affine realization, semisimple axes, `(22)`, and weighted visual flags also
remain, so the card stays at Stage 2.

`DifferentialVariationalRankOnePhase` upgrades the earlier free-field and carrier-subsingleton
results to the complete intrinsic type-`A₀` phase statement.  Every rank-one canonical action fixes
every projective completed-lattice vertex; every finite orbit displacement is exactly zero; the
full Cartan translation vector and scalar Euclidean speed vanish; and the orbit is bounded with
bound zero.  Direct checking and the targeted leaf build pass.  All six new theorems audit to
exactly `[propext, Classical.choice, Quot.sound]`; the leaf is umbrella-wired without an umbrella
build.  This closes the sharp rank-one no-displacement theorem on the full current carrier.  The
higher-rank continuous affine realization, zero-speed semisimplicity, axes, and weighted visual
flags remain, so the card stays at Stage 2.

`DifferentialVariationalPhaseNecessary` proves every unconditional implication that does not use
semisimplicity.  Boundedness is independent of lattice base point; a fixed vertex forces a bounded
orbit; a bounded orbit forces zero scalar speed and zero Cartan vector; and strict positive speed
is equivalent to a nonzero Cartan vector and excludes both bounded orbits and fixed vertices.  The
abstract subadditive translation length is also proved nonnegative.  Direct checking and the
targeted leaf build pass.  All ten new theorems audit to exactly
`[propext, Classical.choice, Quot.sound]`; the leaf is umbrella-wired without an umbrella build.
The only missing direction in the phase partition is now the semisimple rigidity
`zero vector/speed -> fixed point -> bounded orbit`, together with continuous axes and their
weighted visual endpoints.  Card remains at Stage 2.

### Lean progress — bounded orbit exactly fixes a projective lattice vertex (2026-09-03)

`CompletedPseudoDiffOpIntegerNoetherian` proves every left ideal of the completed
pseudodifferential valuation ring is principal, by choosing a nonzero member of least natural
valuation and using exact left divisibility.  Consequently the valuation ring and all its finite
coordinate powers are left Noetherian.

`DifferentialVariationalBoundedOrbitFixedVertex` uses this finiteness algebraically.  Exact Cartan
balance turns a projective Euclidean bound into a literal uniformizer-interleaving bound for every
chosen lattice representative.  Isometry identifies forward and inverse displacement, so one
bound controls all integer iterates.  Their carrier supremum lies in one fixed enlarged lattice;
Noetherianity makes it finitely generated, while the zeroth iterate makes its completed-skew span
full.  Shifting the integer index proves this new lattice is literally invariant under the
canonical semilinear action.  Thus, without a geometric fixed-point premise,

```text
DifferentialVariationalEuclideanOrbitBounded b x sigma
  -> DifferentialVariationalHasFixedVertex b sigma.
```

`DifferentialVariationalFixedVertexPhase` combines this result with the already-proved reverse
implication, giving exact bounded-orbit/fixed-vertex equivalence for every finite rank and every
base vertex.  In the free differential field it also identifies bounded reconstruction-order
powers exactly with the fixed-projective-lattice phase.

Both new leaves pass direct checking and targeted builds.  All new declarations audit to at most
`[propext, Classical.choice, Quot.sound]`; both leaves are wired into `HTGeometry`, and no umbrella
build was run.  Remaining exact phase obligation is now strictly `zero Cartan vector/scalar speed
-> bounded orbit`; continuous affine-building realization, semisimple axes, and opposite weighted
visual flags also remain.  Card stays at Stage 2.

### Lean progress — zero speed forces a bounded orbit; the phase partition closes (2026-09-11)

`DifferentialVariationalZeroSpeedBoundedOrbit` proves the last missing implication of `(21)`,

```text
differentialVariationalEuclideanTranslationLength_eq_zero_implies_orbitBounded
differentialVariationalCartanTranslationVector_eq_zero_implies_orbitBounded
```

and it does so **algebraically**: no continuous affine realization, CAT(0) comparison, geodesic, or
affine-building semisimplicity theorem is used anywhere in the proof.  The mechanism is a monotone
layer count on the forward orbit hull.

Write `M_n = L + σL + ⋯ + σⁿL`, built by the recursion `M_{n+1} = L + σ M_n`, and
`d_n = length(M_{n+1}/M_n)`.

1. **Layer monotonicity** (`orbitHullDefect_succ_le`).  Since `M_{n+2} = L + σ M_{n+1}` and
   `M_{n+1} = L + σ M_n`, the layer `M_{n+2}/M_{n+1}` is a quotient of `σ M_{n+1} / σ M_n` — the
   general submodule fact `length((A ⊔ B)/(A ⊔ B')) ≤ length(B/B')`, isolated as the reusable
   `length_sup_quotient_le`.  The canonical semilinear action preserves the dominant Cartan vector
   exactly (`DifferentialFieldAut.latticeBuildingAction_dominantRelativePosition`), hence preserves
   quotient length, so `d_{n+1} ≤ d_n`.  The layer sequence is an antitone sequence of naturals.
2. **A vanishing layer is a fixed vertex** (`orbitHullLattice_fixed_of_defect_eq_zero`).  If
   `d_n = 0` then `M_{n+1} = M_n`, so the hull absorbs its own image, `σ M_n ⊆ M_n`.  Exact Cartan
   balance (`variationalOreCartanBalance_everyLattice`) upgrades that one-sided inclusion to an
   equality, through the new
   `DiffOp.completedPseudoDiffOpLattice_eq_of_carrier_le_of_balanced`: in a common Cartan frame the
   inclusion forces every coweight coordinate to be `≤ 0` while the character forces their sum to
   be `0`.  So `M_n` is a literally fixed projective lattice vertex, and the already-proved
   fixed-vertex implication bounds the orbit.
3. **A persistent layer forces linear growth.**  Otherwise `d_n ≥ 1` for every `n`, so
   `length(M_n / L) = ∑_{k<n} d_k ≥ n` (`natLength_orbitHullLattice`).  On the other hand a
   sublinear Euclidean displacement confines the hull: from `‖μ(σ^k)‖ ≤ N` the balanced-interleaving
   theorem puts `σ^k L` inside `π^{-N} L`, so with `m = ⌈B + εn⌉` the whole hull lies inside
   `π^{-m} L`, whose length above `L` is exactly `rank · m` (`natLength_leftScale_uniformizer`).
   Hence `n ≤ rank·(B + εn + 1)` for every `n`; choosing `ε = 1/(2(rank+1))` makes this false for
   large `n`.

The capstone records the complete unconditional partition,

```text
differentialVariationalPhase_iff
    bounded orbit ↔ fixed projective vertex ↔ zero scalar speed ↔ zero Cartan vector
differentialVariationalEuclideanTranslationLength_pos_iff_orbitUnbounded
differentialVariationalEuclideanTranslationLength_pos_iff_noFixedVertex
```

the last two being the card's **"there is no parabolic third phase and no unbounded sublinear
variational drift"** in its exact form: strictly positive stable speed is the precise complement of
the bounded phase, so displacement is either bounded or genuinely linear.  Combined with
`FreeDifferentialBoundedOrbit` this closes `(21)` in the free field as well: `ell_delta(sigma) = 0`
if and only if `ord_x(sigma^n)` is bounded.

Direct check with `lake env lean`, targeted leaf build, and the axiom audit all pass.  All 27 new
declarations audit to exactly `[propext, Classical.choice, Quot.sound]`; the leaf is wired into
`HTGeometry` and no umbrella build was run.

Remaining for Stage 3: `(16)` and `(22)` — the canonical attracting/repelling pair
`xi_±(sigma)` as opposite weighted differential flags, and the identification of positive speed with
that boundary pair.  The bounded/unbounded dichotomy itself no longer needs the visual boundary.

### Lean progress — the canonical attracting core, and the boundary phase (2026-09-11)

`DifferentialVariationalAttractingFlag` builds the canonical object `(16)` asks for, algebraically,
and proves the equivalence `(22)` against it.  No visual boundary, geodesic, or CAT(0) structure is
used anywhere.

The construction is a growth filtration of the completed coordinate space.  For a rate `1/c`,

```text
variationalSlowSet σ b L c
    = { v : ∀ᶠ n, σⁿ v ∈ π^(-⌊n/c⌋) L }
```

collects the vectors whose variational orbit leaves the base lattice at rate at most `1/c`; each is
a submodule over the completed valuation ring (`variationalSlowSubmodule`).  The **attracting core**

```text
variationalAttractingCore σ b L = ⋂ c, variationalSlowSet σ b L (c+1)
variationalAttractingSubmodule σ b L
```

is their intersection, the vectors of non-positive growth rate.  It is canonical: it is defined from
`σ` and the vertex alone, and by commensurability of lattices it does not see which representative
of the projective vertex is used.

The two halves:

```text
variationalAttractingCore_eq_univ_of_orbitBounded
translationLength_eq_zero_of_variationalAttractingCore_eq_univ
variationalAttractingCore_eq_univ_iff
```

The first adjoins the single vector `v` to the base lattice — still a full finite lattice
(`DiffOp.adjoinVectorLattice`) — uses base-vertex independence of boundedness, and turns the
Euclidean bound into a uniform uniformizer confinement through exact Cartan balance.  The second
runs the opposite way: a finite generating family of `L` carries the whole lattice
(`DifferentialFieldAut.latticeBuildingAction_carrier_le_of_span`), so rate-`1/c` confinement of the
generators confines `σⁿ L` itself, and the new one-sided inclusion test

```text
DiffOp.carrier_le_leftScale_uniformizer_iff_relativePosition
    M ⊆ π^z L  ↔  ∀ i, z ≤ μ_i(L,M)
DiffOp.euclideanVertexDistance_le_of_carrier_le_scale
    balance + one-sided inclusion ⇒ ‖μ‖ ≤ (rank+1)³ N
```

converts that into `dist(L, σⁿL) ≤ (rank+1)³ ⌊n/c⌋`.  Dividing by `n` and letting `c → ∞` kills the
speed.  The inclusion test is the general-pair form of the corpus's
`CompletedPseudoDiffOpCartanInclusion` lemmas, and the distance bound is the exact converse of
`completedPseudoDiffOpLattice_interleavedAt_of_balanced_euclidean_le`: balance means one-sided
containment already controls both sides.

The capstone is `(22)`'s content:

```text
variationalAttractingCore_ne_univ_iff_translationLength_pos
variationalAttractingCore_ne_univ_iff_cartanVector_ne_zero
variationalAttractingSubmodule_ne_top_iff_translationLength_pos
```

**`σ` is in the boundary phase exactly when its canonical attracting core is proper** — that is,
exactly when some coordinate direction escapes the base lattice at a strictly positive exponential
rate.  Combined with the previous entry, the phase law now reads: bounded orbit ⟺ fixed vertex ⟺
zero speed ⟺ zero Cartan vector ⟺ full attracting core, and the negation of all five is the
boundary phase.

Direct check with `lake env lean`, targeted leaf build, and the axiom audit pass.  All 25 new
declarations audit to exactly `[propext, Classical.choice, Quot.sound]`; the leaf is wired into
`HTGeometry` and no umbrella build was run.

Still open for Stage 3: the attracting core is so far a valuation-ring submodule.  Upgrading it to a
`CompletedPseudoDiffOp`-subspace (the uniformizer is fixed by every coefficient automorphism, so
only the denominator-clearing step is missing), proving it `σ`-stable (which needs the vector-level
composition law for the semilinear action), and pairing it with the repelling core of `σ⁻¹` into the
opposite weighted flags of `(16)` are the remaining bricks.

### Lean progress — the attracting core is an invariant subspace, and the boundary pair (2026-09-11)

Two further leaves upgrade the attracting core from a growth filtration to the canonical boundary
datum `(16)` asks for.

`DifferentialVariationalAttractingSubspace` proves the vector-level cocycle law

```text
DifferentialFieldAut.vecBuildingAction_mul
    (σ·τ) v = τ (σ v)
DifferentialFieldAut.vecBuildingAction_pow_succ
```

from the matrix cocycle `U_{στ} = τ(U_σ)·U_τ`, transport of a row product, and associativity of
`vecMul`; no new algebra is introduced.  With it:

```text
variationalAttractingCore_vecBuildingAction_mem     the core is σ-invariant
variationalAttractingCore_uniformizer_zpow_smul     closed under π^z
variationalAttractingCore_smul_mem                  closed under every completed skew scalar
variationalAttractingSubspace                       the canonical invariant subspace
variationalAttractingSubspace_ne_top_iff_translationLength_pos
```

The invariance step reads the rate-`1/(2c+2)` condition one index along the orbit and uses
`⌊(n+1)/(2c+2)⌋ ≤ ⌊n/(c+1)⌋`, valid for every `n`.  The scalar closure uses that the canonical
uniformizer is *fixed* by every differential coefficient automorphism
(`mapCompletedPseudoDiffOpUnit_uniformizer`), so `π^z`-scaling only shifts the confinement exponent
by the constant `z`, which one rate halving absorbs; an arbitrary nonzero skew scalar then factors
as `π^{-t}` times a valuation-ring element.  **The attracting core is therefore a genuine subspace
over the completed pseudodifferential skew field, invariant under the action** — a weighted
differential flag datum, not merely a lattice-level object.

`DifferentialVariationalBoundaryPair` supplies the companion and the pair:

```text
differentialVariationalEuclideanTranslationLength_inv    speed is inversion-invariant
variationalRepellingSubspace, variationalRepellingSubspace_invariant
variationalBoundaryPair_iff
    (attracting proper ∧ repelling proper) ↔ 0 < ell_delta(sigma)
variationalBoundaryPair_eq_top_iff
    (attracting = ⊤ ∧ repelling = ⊤) ↔ ell_delta(sigma) = 0
```

Speed is inversion-invariant because the canonical action is an isometry, so
`d(x, σ^{-n}x) = d(x, σ^n x)`; the repelling objects are the attracting objects of `σ⁻¹`.  This is
`(22)` with its boundary datum made explicit: **the boundary phase is exactly the phase in which `σ`
carries a canonical proper attracting subspace together with a canonical proper repelling subspace,
and the bounded phase is exactly the phase in which both degenerate to the whole space.**

Direct checks, targeted leaf builds, and axiom audits pass for both leaves.  All 16 declarations of
the subspace leaf and all 6 of the boundary-pair leaf audit to exactly
`[propext, Classical.choice, Quot.sound]`; both are wired into `HTGeometry` and no umbrella build
was run.

What remains of `(16)` is exactly the word *opposite*: transversality of the two canonical
subspaces, i.e. `F + G = ⊤` with `F ∩ G` the zero-rate part.  That is the slope/Lyapunov splitting
for a cyclic semilinear group over a complete discretely valued skew field, and it is the only
remaining mathematical input of Theorem B; the dichotomy itself, both canonical subspaces, their
invariance, and the exclusion of a parabolic phase are now unconditional in Lean.  The continuous
affine realization is no longer needed for any of the statements above.

### Lean progress — Theorem C's gap `(21)` and boundary equivalence `(22)`, in the free field (2026-09-11)

`FreeDifferentialClockPhase` restates the phase law in the card's own free-field coordinates, the
differential order `ord_x(sigma^n)`:

```text
freeDifferentialOrderTranslationLength_eq_zero_iff
    ell_delta(sigma) = 0  ↔  ord_x(sigma^n) is bounded
freeDifferentialOrderTranslationLength_pos_iff
    ell_delta(sigma) > 0  ↔  ord_x(sigma^n) is unbounded
freeDifferential_boundaryPair_iff
    (attracting subspace proper ∧ repelling subspace proper)  ↔  ell_delta(sigma) > 0
```

The first is the exact statement of `(21)`: the order-oriented Cartan vector is antitone with zero
sum, so a vanishing top coordinate — which is exactly `ell_delta(sigma)` by
`freeDifferentialOrderTranslationLength_eq_reverseCartan_zero` — forces the whole vector to vanish;
the zero-speed theorem then supplies a bounded Euclidean orbit, and the corpus comparison
`freeDifferentialEuclideanOrbitBounded_iff_orderPowersBounded` converts that back into bounded
differential order.  The second is the card's sentence **"differential-order growth of a reversible
finite-rank clock is either bounded or genuinely linear"**, now a theorem rather than a consequence
of the building dichotomy: `Fekete's lemma alone gives existence of (20)` and this gives the strict
gap, with the affine-building input replaced by the orbit-hull argument.  The third is `(22)`.

Direct check, targeted leaf build and axiom audit pass; all 5 declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, and the leaf is wired into `HTGeometry` without an
umbrella build.

**State of Theorem B and Theorem C.**  `(14)`, `(15)`, `(19)`, `(20)`, `(21)`, `(23)` and the whole
bounded/boundary dichotomy including the exclusion of a parabolic phase are unconditional in Lean;
`(16)`'s canonical pair exists and `(22)` holds for it.  The one remaining mathematical input is
transversality of the pair — that the attracting and repelling subspaces span, which is the
slope/Lyapunov splitting for a cyclic semilinear group over a complete discretely valued skew field.
That splitting is proved classically by successive approximation across the slope gap; it needs a
degree/slope layer for sigma-stable subspaces, which the corpus does not yet have.

### Lean progress — the growth filtration stabilizes, and escape is uniform (2026-09-11)

`DifferentialVariationalGrowthStabilization` proves that the attracting core is reached at a finite
rate index, which is the separation the transversality of `(16)` needs.

A slow set `S c = { v : ∀ᶠ n, σⁿ v ∈ π^{-⌊n/c⌋} L }` is only a valuation-ring submodule.  Its
**saturation**

```text
variationalSlowSaturation σ b L c = { v : ∃ z, π^z • v ∈ variationalSlowSet σ b L c }
```

is a subspace over the completed skew field.  The two facts that make it one are new and reusable:

```text
DiffOp.uniformizer_conj_mem_integer      π^z o π^{-z} ∈ O for o ∈ O
DiffOp.uniformizer_shift_factorization   π^m a = (π^d · π^z a' π^{-z}) · π^z
```

the first because the valuation is multiplicative, so conjugation preserves it; the second the exact
regrouping that turns an arbitrary scalar `a = π^{-t} o` into an integral factor acting on the
already-dilated vector.  Two sandwiching inclusions,

```text
variationalSlowSet_subset_saturation        S c ⊆ Sat c
variationalSlowSaturation_subset_slowSet    Sat c ⊆ S (c-1)
```

hold because dilating by `π^{-z}` costs only the constant `z`, which one rate step absorbs
(`uniformizer_smul_mem_variationalSlowSet`).  The saturations form a descending chain of subspaces
of a finite-rank space over a division ring, hence stabilize; sandwiching again transfers the
stabilization to the slow sets themselves:

```text
exists_variationalSlowSet_eq_attractingCore
    ∃ c₀ ≥ 1, ∀ m ≥ c₀, variationalSlowSet σ b L m = variationalAttractingCore σ b L
exists_uniform_escape_rate
    ∃ c₀ ≥ 1, every vector outside the core escapes π^{-⌊n/c₀⌋} L infinitely often
```

So the attracting core is not merely an intersection of rates: **it is a single slow set, and every
direction outside it escapes at a rate bounded below by one positive constant.**  That uniform gap
is exactly the hypothesis under which the classical slope splitting is proved by successive
approximation — the remaining step is the contraction estimate for the twisted Sylvester iteration
`X ↦ C^{-1}(φ(X)A + B)` in a basis adapted to the core, whose convergence needs the uniform
expansion of the quotient (now available) together with the subexponential growth on the core.

Direct check, targeted leaf build, and axiom audit pass; all 13 new declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, and the leaf is wired into `HTGeometry` without an
umbrella build.

### Lean progress — relative growth modulo an invariant subspace, and the tower fixed point (2026-09-11)

`DifferentialVariationalRelativeGrowth` runs the whole growth filtration *relative* to a fixed
subspace, without transporting the semilinear action to a quotient.  The target of the growth
condition is enlarged from `π^{-m} L` to

```text
variationalRelativeTarget L W m = (π^{-m} L).carrier ⊔ W
```

and because `W` is a subspace over the completed skew field it is stable under every dilation, so
every absolute argument ports verbatim: relative slow sets are valuation-ring submodules, their
uniformizer saturations are subspaces, the sandwich inclusions hold, and the descending chain of
saturations stabilizes.

```text
exists_variationalRelativeSlowSet_eq_attractingCore
variationalRelativeAttractingSubspace, variationalRelativeAttractingSubspace_carrier
variationalRelativeAttractingSubspace_invariant
le_variationalRelativeAttractingSubspace
exists_variationalRelativeAttractingSubspace_fixedPoint
```

The capstone is the tower: for a `σ`-invariant `W₀` the relative attracting subspace is again
`σ`-invariant and contains `W₀`, so iterating gives an ascending chain, which stabilizes because the
coordinate space is Noetherian over the completed skew field.  The limit `W` satisfies

```text
variationalRelativeAttractingSubspace σ b L W = W
```

— **its own relative attracting core is itself**: read through the quotient, the induced action on
`V/W` has trivial attracting core, so no direction outside `W` is asymptotically absorbed into it.

Direct check, targeted leaf build and axiom audit pass; all 21 declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, and the leaf is wired into `HTGeometry` without an
umbrella build.

**Where the remaining obstruction now sits, precisely.**  The two available separations are
`liminf`-type: a vector outside the core has `liminf_n val(σⁿ v)/n ≤ -1/c₀`, uniformly in the vector.
The Sylvester contraction `X ↦ C^{-1}(φ(X)A + B)` that produces the invariant complement needs a
`limsup`-type bound instead — every direction of `V/W` expanding by at least `δk` for *all* large
`k`, not merely infinitely often.  Upgrading `liminf` to `limsup` is exactly attainment of the
Lyapunov exponents, i.e. the Harder--Narasimhan/slope filtration.  The next brick is therefore the
degree of a `σ`-stable subspace, computable inside the ambient space as the signed length
`length(M/(M ∩ σM)) - length(σM/(M ∩ σM))` for `M = L ∩ W`, since these are finite-length modules
over the completed valuation ring; from it the slope, the maximal destabilizing subobject, and the
attained exponents follow.

### Lean progress — integral lattices inside an invariant subspace (2026-09-11)

`DifferentialVariationalSubspaceLattice` builds the first layer of the degree theory the
transversality step needs, and does it inside the ambient coordinate space rather than by
transporting the action.

```text
DiffOp.exists_uniformizer_smul_mem_lattice        ∃ k, π^k • v ∈ L
subspaceTraceLattice L W = L.carrier ⊓ W          finitely generated, spans W
subspaceTraceLattice_fg, span_subspaceTraceLattice
DiffOp.exists_uniformizer_smul_mem_of_mem_span    v ∈ span_D M ⇒ ∃ k, π^k • v ∈ M
DiffOp.exists_uniformizer_smul_le                 commensurability, one common power
```

The trace of the base lattice on a subspace is finitely generated because it is a submodule of a
finitely generated module over the left Noetherian valuation ring, and it spans the subspace because
every vector is pushed into the base lattice by a uniformizer power.  The span lemma is a span
induction whose scalar step reuses the regrouping `π^m a = (π^d · π^z a' π^{-z}) · π^z` and the
invariance of the valuation ring under conjugation by uniformizer powers; the commensurability
statement then takes the supremum of the finitely many powers that clear the generators, so **a
single uniformizer power carries one integral submodule into any other with the same skew-field
span**.

Direct check, targeted leaf build and axiom audit pass; all 8 declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, and the leaf is wired into `HTGeometry` without an
umbrella build.

Next bricks for the degree: finiteness of the layer `length(M / π^k M)` for a finitely generated
integral submodule — via the surjection `(O/π^k O)^j ↠ M/π^k M` and `length(O/πO) = 1`, which holds
because every left ideal of the completed valuation ring is principal (corpus:
`CompletedPseudoDiffOpIntegerPrincipal`) so the residue module is simple — then the signed degree
`deg(W) = length(M/(M ∩ σM)) - length(σM/(M ∩ σM))`, its independence of `M`, additivity in short
exact sequences, and from there the Harder--Narasimhan filtration whose attained exponents upgrade
the available `liminf` separation to the `limsup` bound the Sylvester contraction consumes.

### Lean progress — residue length over the completed valuation ring (2026-09-11)

`CompletedPseudoDiffOpResidueLength` supplies the counting input for the degree of an invariant
subspace.

```text
DiffOp.isSimpleModule_quotient_maximalIdeal        the residue module is simple
DiffOp.length_quotient_maximalIdeal_eq_one         hence has length one
DiffOp.uniformizerInteger                          the uniformizer inside the valuation ring
DiffOp.exists_mul_uniformizerInteger_of_mem_maximalIdeal
DiffOp.length_span_le_card_of_uniformizer_smul_eq_zero
```

The valuation ring is local and its maximal ideal is maximal as an ideal, so the residue module is a
coatom quotient, hence simple, hence of length one.  Every element of the maximal ideal is a right
multiple of the canonical uniformizer: its additive value is at least one, so dividing by the
uniformizer stays integral — the only delicate point is that `WithTop ℤ` needs the discreteness step
`0 < v ⇒ 1 ≤ v`.

The capstone is the finiteness the degree needs: **a finitely generated module killed by the
uniformizer has length at most its generator count**.  The proof is an induction over the generating
finset: splitting off one generator gives an exact sequence whose sub-object is the span of the rest
and whose quotient is cyclic, and the cyclic quotient is `O` modulo a left ideal containing the
maximal ideal — because the uniformizer already annihilates the module — so it has length at most
one.

Direct check, targeted leaf build and axiom audit pass; all 7 declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, and the leaf is wired into `HTGeometry` without an
umbrella build.

Next: iterate this over the filtration `M ⊆ M + πᵏ⁻¹N ⊆ ⋯ ⊆ N` to get finite length for the layer
between commensurable integral lattices, then define
`deg(W) = length(M/(M ∩ σM)) - length(σM/(M ∩ σM))` for `M = L ⊓ W` and prove it independent of `M`
and additive.

### Lean progress — finite length of uniformizer-torsion modules (2026-09-11)

`CompletedPseudoDiffOpTorsionLength` closes the finiteness the degree needs.

```text
DiffOp.coe_uniformizerInteger_pow            ring power = unit power
DiffOp.uniformizerConj, DiffOp.uniformizerInteger_pow_mul
    π^k a = (π^k a π^{-k}) π^k, the conjugate again integral
DiffOp.uniformizerTorsion                    the annihilator of π^k is a submodule
DiffOp.length_ne_top_of_fg_of_uniformizer_smul_eq_zero
DiffOp.length_ne_top_of_fg_of_uniformizer_pow_smul_eq_zero
```

The noncommutative obstruction is that multiplication by a uniformizer power is `O`-**semi**linear,
not `O`-linear, so neither the annihilator of `π^k` nor the image `π·A` is a submodule for free.
Both become submodules through the single identity `π^k a = (π^k a π^{-k}) π^k`, whose conjugate
stays integral because the valuation is multiplicative.  With that, the induction on `k` runs:
splitting a finitely generated `A` along the span of `π·(generators)` gives an exact sequence whose
sub-object is finitely generated and killed by `π^k` — induction hypothesis — and whose quotient is
finitely generated and killed by `π` — the residue-length bound of the previous leaf.

**The layer between two commensurable integral lattices therefore has finite length**, which is
exactly what makes the signed degree `deg(W) = length(σM/(M ∩ σM)) - length(M/(M ∩ σM))` a
well-formed integer.

Direct check, targeted leaf build and axiom audit pass; all 7 declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, and the leaf is wired into `HTGeometry` without an
umbrella build.

Next: the degree itself — independence of the chosen lattice `M`, additivity along invariant
subspaces, and then the Harder--Narasimhan filtration whose attained slopes upgrade the proved
`liminf` separation to the `limsup` bound the Sylvester contraction consumes.

### Correction — the relative tower needs a properness companion (2026-09-11)

The entry above on `exists_variationalRelativeAttractingSubspace_fixedPoint` is correct as stated but
was described as if the fixed point were automatically useful.  It is not: the ascending tower could
in principle stabilize at `⊤`, and `variationalRelativeAttractingSubspace σ b L ⊤ = ⊤` holds
vacuously.  So the tower gives a `σ`-invariant `W` with trivial relative core, but properness of `W`
is a separate obligation.

What supplies it is an elementary non-archimedean estimate, and it is worth recording because it is
also the reason no "parabolic accumulation" can occur:

> **Block estimate.**  Let `W` be `σ`-invariant.  If every vector of `W` is in the attracting core
> (uniformly, at lattice level) *and* `variationalRelativeAttractingSubspace σ b L W = ⊤`, then the
> orbit is bounded.

In an adapted lattice `L = L_W ⊕ L_U` the matrix of `σ` is block triangular `[[A,0],[B,C]]`, and the
off-diagonal block of `σⁿ` is `wₙ = Σ_j σ^{n-1-j}(B(u_j))`.  Each summand has valuation at least
`-ε(n-1) - β` — subexponential on `W` for the outer factor, subexponential on `V/W` for `u_j` — and
because the valuation is **non-archimedean the sum of the `n` summands is no worse than the largest**.
Hence `‖σⁿ‖ ≤ ‖B‖·q^{εn}` for every `ε`, so the speed is zero.

Contrapositive: in the boundary phase, the relative attracting subspace of the attracting core is
*proper*, so the tower fixed point is a proper `σ`-invariant subspace with trivial relative core —
exactly the datum the Sylvester contraction needs on the quotient side.

This estimate is the next brick.  It needs a `D`-complement of `W` (`Submodule.exists_isCompl`), the
adapted lattice, and the summation bound; the uniform lattice-level slowness it consumes is already
available from the slow sets applied to a finite generating family.

### Lean progress — lattices adapted to a splitting (2026-09-11)

`DifferentialVariationalAdaptedLattice` supplies the compatibility the block estimate consumes.

```text
adaptedTraceLattice L W U hWU = (L ⊓ W) ⊔ (L ⊓ U)
exists_split_of_uniformizer_smul_mem_adaptedTraceLattice
```

The adapted lattice is finitely generated as a sum of two finitely generated traces, and full because
each trace already spans its own subspace while the two subspaces span everything.  The splitting
theorem is the substantive part: **if a uniformizer power pushes `x` into the adapted lattice, then
`x = w + u` with `w ∈ W`, `u ∈ U`, and the same uniformizer power pushes each component into the
corresponding trace lattice.**  Without adaptation a bound on `σⁿ x` says nothing about its two
components; with it, the bound splits, which is what lets the off-diagonal sum
`wₙ = Σ_j σ^{n-1-j}(B(u_j))` be estimated term by term and then collected — the collection being free
because the terms all lie in one submodule.

Direct check, targeted leaf build and axiom audit pass; both declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, and the leaf is wired into `HTGeometry` without an
umbrella build.

Note on performance: the naive proof of fullness times out even at a million heartbeats, because
rewriting through `subspaceTraceLattice` forces the scalar-tower instance repeatedly.  Stating the
two span equalities first and chaining them with `calc` avoids the rewrite entirely and elaborates
in seconds.  The same shape should be used for the remaining bricks of this layer.

### Lean progress — eventual confinement upgrades to uniform confinement (2026-09-11)

`DifferentialVariationalUniformShift` removes the "eventually" from the rate bounds the block
estimate consumes.

```text
exists_uniform_shift_of_eventually_carrier_le
    (∀ᶠ n, σⁿ P ⊆ π^{-⌊n/c⌋} L)  ⇒  ∃ γ, ∀ n, σⁿ P ⊆ π^{-(⌊n/c⌋ + γ)} L
```

The unrolled off-diagonal term `wₙ = Σ_j σ^{n-1-j}(B(u_j))` needs the rate bound at *every* exponent
`n-1-j`, including the small ones, whereas a slow set only supplies it eventually.  The finitely many
early indices each admit some uniformizer confinement — every lattice sits inside some dilation of
every other — and the supremum of those finitely many exponents is a single additive constant that
makes the bound hold at all indices.  A constant is invisible to the rate, so nothing is lost.

Direct check, targeted leaf build and axiom audit pass; the declaration audits to exactly
`[propext, Classical.choice, Quot.sound]`, and the leaf is wired into `HTGeometry`.

With the adapted lattice and this uniformisation both in place, the remaining pieces of the block
estimate are the component recursion `w_{n+1} = σ(wₙ) + pr_W(σ(uₙ))`, `u_{n+1} = pr_U(σ(uₙ))`, its
unrolling, and the observation that the `n` summands all lie in the single submodule
`π^{-(ε(n-1)+β)} L₀`, so their sum does too.

### Lean progress — the block sum obeys the component recursion (2026-09-11)

`DifferentialVariationalBlockRecursion` ties the closed form of the previous leaf to the recursion
that actually generates it.

```text
DifferentialFieldAut.vecBuildingAction_injective     the vector action is injective
DifferentialFieldAut.vecBuildingAction_one           the identity acts trivially
DifferentialFieldAut.vecBuildingAction_succ_left     σ ∘ σⁿ = σⁿ⁺¹ on vectors
variationalBlockSum_succ                             Σ_{j<n+1} = σ(Σ_{j<n}) + aₙ
```

The two basic facts were genuinely missing.  Injectivity is not a triviality for a semilinear action:
the action is a matrix multiplication composed with a coefficient ring equivalence, and the matrix has
no `Inv` instance to invert directly — what does work is that the matrix acts through
`completedPseudoDiffOpMatrixLinearEquiv`, an equivalence, so injectivity comes for free from the
composite of two injections.  `vecBuildingAction_one` then follows from the cocycle law `(1·1)·v =
1·(1·v)` plus injectivity, rather than from unfolding the canonical matrix unit — which would force
the elaborator through the whole Ore-matrix construction.

`variationalBlockSum_succ` is the reindexing `n-1-j ↦ n-j` that pushing `σ` inside the sum performs,
with the new top summand `σ⁰(aₙ) = aₙ`.  It is the recursion half of the block estimate: the orbit's
off-diagonal component satisfies `w_{n+1} = σ(wₙ) + aₙ`, and the estimate of the previous leaf applies
to the closed form, so the two must be identified.

Direct check, targeted leaf build and axiom audit pass; all four declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, and the leaf is wired into `HTGeometry` without an umbrella
build.

### Lean progress — base independence and the orbit decomposition (2026-09-11)

`DifferentialVariationalBlockDecomposition` supplies the two structural inputs of the block estimate.

```text
variationalAttractingCore_base_independent            the growth filtration ignores the base lattice
variationalRelativeAttractingCore_base_independent    and so does the relative one
exists_variationalBlockDecomposition                  σⁿ(x) = uₙ + Σ_{j<n} σ^{n-1-j}(aⱼ)
DifferentialFieldAut.vecBuildingAction_add
DiffOp.exists_nat_mem_leftScale, DiffOp.exists_nat_finset_mem_leftScale
DiffOp.leftScale_uniformizer_le_of_carrier_le
nat_div_two_mul_add_le
```

Base independence is what lets the estimate be run in a lattice adapted to a splitting while the
hypotheses are stated for the given lattice.  It is not formal: the two lattices sit inside
uniformizer dilations of each other only up to a **constant** shift, and a constant is invisible to a
rate only if there is room for it.  Reading the hypothesis at half the rate creates exactly that
room, because `⌊n/2c⌋ + ⌊n/2c⌋ ≤ ⌊n/c⌋` by superadditivity of floor division and the constant is
eventually below `⌊n/2c⌋`.  This is the content of `nat_div_two_mul_add_le`, and the same lemma is
reused at the end of the estimate.

The decomposition needs nothing but `W ⊔ U = ⊤`: the splitting at each step is a choice, and the
closed form follows from the recursion by the reindexing already proved in
`variationalBlockRecursion`.  Invariance of `W` is *not* needed here — it enters only when the
accumulated block is shown to lie in `W`.

Direct check, targeted leaf build and axiom audit pass; the leaf is wired into `HTGeometry` without an
umbrella build.

### Lean progress — the block estimate, and the boundary datum (2026-09-11)

`DifferentialVariationalBlockEstimate` closes the properness obligation recorded in the correction
above, and does so in a stronger form than that correction anticipated.

```text
variationalRelativeAttractingCore_subset_variationalAttractingCore
    W invariant and slow  ⟹  slow modulo W  ⟹  slow
variationalAttractingCore_eq_univ_of_block
variationalRelativeAttractingSubspace_attractingSubspace
    relAttr(F) = F  for  F = variationalAttractingSubspace σ b L
exists_proper_invariant_relativeAttracting_fixed_of_translationLength_pos
DiffOp.mem_leftScale_uniformizer_iff, DiffOp.uniformizer_smul_mem_submodule
DifferentialFieldAut.vecBuildingAction_pow_mem_subspace, variationalBlockSum_mem_subspace
exists_uniform_slow_shift_of_fg
```

**The estimate.**  Let `W` be `σ`-invariant with every vector of `W` slow.  Choose a complement `U`
and work in the adapted lattice `L' = (L ⊓ W) ⊕ (L ⊓ U)`.  For `u₀ ∈ U` the orbit unrolls as
`σⁿ(u₀) = uₙ + Σ_{j<n} σ^{n-1-j}(aⱼ)` with `uₙ ∈ U` and `aⱼ ∈ W`.  Relative slowness of `u₀` bounds
`uₙ` — this is where adaptedness is indispensable, because a bound on `σⁿ(u₀)` modulo `W` says
nothing about its `U`-component unless the lattice splits, and where the direct-sum uniqueness turns
the split supplied by the lattice into *the* component.  The same splitting applied one step later
bounds `aⱼ`, using only that one step of the action moves the adapted lattice into a fixed dilation
of itself.  Uniform slowness on the finitely generated trace lattice `L ⊓ W` — the "eventually" of a
slow set upgraded to "always" on a finite generating family — bounds each transported term.  The
accumulated sum then costs **nothing**: all `n` summands lie in the *same* dilation, and a submodule
is closed under addition.

**The consequence that matters.**  The correction above expected the estimate to make some tower
fixed point proper.  In fact it does better: taking `W = F := variationalAttractingSubspace σ b L`,
which is invariant and slow *by definition*, the estimate says `relAttr(F) ≤ F`, and the reverse
inclusion is always true, so

```text
variationalRelativeAttractingSubspace σ b L F = F.
```

**The canonical attracting subspace is already a fixed point of the relative tower.**  The ascending
tower of `DifferentialVariationalRelativeGrowth` does not need to be iterated at all, and the
vacuous-stabilisation worry disappears: in the boundary phase `F ≠ ⊤` by
`variationalAttractingSubspace_ne_top_iff_translationLength_pos`, so the boundary datum is a *proper*
`σ`-invariant subspace that absorbs nothing from outside itself.

No building, no boundary at infinity, no CAT(0) structure is used anywhere; the whole argument is the
non-archimedean fact that a sum of `n` terms of a common size has that size.

All 17 declarations of the two leaves audit to exactly `[propext, Classical.choice, Quot.sound]`;
both leaves build and are wired into `HTGeometry` without an umbrella build.

**State of `(16)`.**  The attracting half of the boundary pair is now canonical, proper and
saturated, and the same applies to the repelling half by replacing `σ` with `σ⁻¹`
(`differentialVariationalEuclideanTranslationLength_inv` already gives that the two phases agree).
What `(16)` still asserts beyond this is **oppositeness**, `F ⊔ G = ⊤`.  That is exactly the slope
decomposition, and it is the one remaining input: over a complete discretely valued base a
`σ`-semilinear automorphism has a Harder–Narasimhan filtration, but transversality of the extreme
steps is the splitting of that filtration.  The degree function needed to define the slopes is the
next brick, and its finiteness is already proved
(`DiffOp.length_ne_top_of_fg_of_uniformizer_pow_smul_eq_zero`).

### Lean progress — length along a tower, and the signed lattice index (2026-09-11)

Two leaves start the slope layer that `(16)` still needs.

`ModuleLengthTower` supplies what mathlib leaves out.  Mathlib has additivity of `Module.length` in a
short exact sequence but not the filtration form

```text
Module.length_quotient_add_length_quotient   length (B/A) + length (Q/B) = length (Q/A)
Module.length_eq_of_linearEquiv
```

both over an arbitrary ring, with no finiteness hypothesis — the identity holds in `ℕ∞` with `⊤` on
both sides when the lengths are infinite.  The short exact sequence `0 → B/A → Q/A → Q/B → 0` is
built explicitly from two `liftQ`s.

`CompletedPseudoDiffOpLatticeIndex` then builds the index itself.

```text
DiffOp.uniformizerScaleSubmodule                 π^k M, as the image of a semilinear map
DiffOp.uniformizerScaleSubmodule_le / _fg / _le_of_smul_mem / _antitone
DiffOp.relLength M N = length (N / (M ⊓ N))
DiffOp.relLength_ne_top                          finiteness from a uniformizer bound
DiffOp.relLength_tower                           relLength A B + relLength B D = relLength A D
DiffOp.relIndex Q M N = length (N/Q) - length (M/Q)
DiffOp.relIndex_add / _self / _swap              the cocycle laws, free from the definition
DiffOp.relIndex_of_le                            refining the base changes nothing
DiffOp.relIndex_base_independent                 and neither does replacing it altogether
Module.length_quotient_comap_subtype             ↥(comap C.subtype B) ≃ ↥B, on relative lengths
```

Two design points are worth recording because they are what make the noncommutative case go through
unchanged.

*No intersections.*  The usual construction of a lattice index takes `M ⊓ N` as the common
sublattice, which forces a Noetherian hypothesis on the valuation ring to keep it finitely generated.
Here the common refinement of two base sublattices `Q₁, Q₂` is instead the **scaling** `π^j Q₁`: it
lies inside `Q₁` because `π^j` is integral, and inside `Q₂` by commensurability
(`DiffOp.exists_uniformizer_smul_le`).  Finite generation is then automatic, because the scaling is
the image of a semilinear map.  Nothing in the development needs `O` to be Noetherian.

*The cocycle is free, the base independence is the content.*  Measured from a fixed common
sublattice, `relIndex Q M N + relIndex Q N P = relIndex Q M P` is a triviality about subtraction.  All
the work is in `relIndex_base_independent`, and it is exactly the tower additivity applied twice, to
`Q₃ ≤ Q₁` and `Q₃ ≤ Q₂`.

Direct checks, targeted leaf builds and axiom audits pass; all 18 declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, and both leaves are wired into `HTGeometry` without an
umbrella build.

Next: `σ`-equivariance of the relative length (the action induces a semilinear bijection of the layer,
so lengths agree — this needs `Module.length` to be an invariant of *semilinear* equivalences, which
mathlib also lacks), then the degree `deg(W) = relIndex Q (L ⊓ W) (σ(L ⊓ W))` for a `σ`-stable `W`,
its independence of `L` (the cocycle plus equivariance make the two comparison terms cancel), and its
additivity along an exact sequence.  Then slopes, and the Harder--Narasimhan filtration whose
integrality supplies the **uniform** escape rate that the Sylvester contraction needs — the one thing
that separates the proved `relAttr(F) = F` from transversality `F ⊔ G = ⊤`.

### Plan — the slope splitting that closes `(16)` (2026-09-27)

Oppositeness is the only open statement.  It follows from a three-part decomposition proved by
strong induction on dimension, for any additive bijection `T` of a finite-dimensional space `E`
over the completed skew field `D` that is semilinear for a valuation-preserving automorphism fixing
`π` (this class contains the variational action, its powers, its inverse, and `π^{-c}T^d`):

`E = E_+ ⊕ E_0 ⊕ E_-`, all `T`-invariant, with a lattice `P ⊆ E_+` and `m ≥ 1` such that
`T^{-m}P ⊆ πP` (quantitative expansion), a lattice `N ⊆ E_0` with `TN = N`, and a lattice
`Q ⊆ E_-` with `T^mQ ⊆ πQ`.

Ingredients, in order:
1. forward hull `Λ_∞ = ∑_{n≥0} TⁿΛ` and its divisible part `W' = ⋂_k π^kΛ_∞`, an invariant
   subspace independent of `Λ`;
2. **divisible-part lemma**: `Λ_∞ ⊆ W' + π^{-c}Λ` — needs the Artinian structure of `E/Λ` and
   one completeness statement in `D` (a sequence with `c_{n+1} − c_n ∈ πⁿO` converges with
   `c − c_n ∈ πⁿO`), used through the coordinates of a lattice basis;
3. exhaustion: if `W' = E` then `Λ_{n+1} = TΛ_n` eventually, and a single `m` gives
   `π^{-1}Λ_{n₁} ⊆ T^mΛ_{n₁}`;
4. an extension of forward-bounded by forward-bounded is forward-bounded (ultrametric block sums);
5. bounded in both directions gives a `T`-stable lattice (the hull `∑ TⁿN`);
6. Sylvester splitting `X = −∑ T_{W'}^{-(n+1)} A Cⁿ` of `0 → W' → E → E/W' → 0`;
7. induction: `W'` has no forward-bounded part (its image in `E/A_+` would be a bounded hull
   containing a subspace), so `W' = E_+`, and the complement splits by the induction hypothesis.

Then the attracting core is `E_0 ⊕ E_-`, the repelling core is `E_0 ⊕ E_+`, and their sum is `E`.
Applying the same theorem to `π^{-c}T^d` for every rational `c/d` gives the canonical slope
decomposition `E = ⊕_s E_s` (rationality from integrality of the lattice index), hence the
weighted flags, their oppositeness, and the identification of the weights with the Cartan
translation vector `(14)`.

### Lean progress — oppositeness `F ⊔ G = ⊤` is proved (2026-09-27)

The slope splitting is now formal, for the whole class of uniformizer-semilinear automorphisms of an
arbitrary finite-dimensional vector space `E` over the completed skew field `𝔻` (automorphisms are
`E ≃ₗ[ℤ] E`, semilinear for a ring automorphism of `𝔻` preserving `𝒪` and fixing `π`).  New leaves,
in dependency order:

```text
CompletedPseudoDiffOpAdicCompleteness    valuation balls are closed nbhds; 𝔻 is adically complete
CompletedPseudoDiffOpVectorLattice       dilations ϖ^k M, absorption, coordinates, separation,
                                         completeness and uniqueness of limits for fg M ⊆ E
CompletedPseudoDiffOpVectorArtinian      𝔻/𝒪 Artinian; descending chains above a lattice stabilize
CompletedPseudoDiffOpSemilinearAut       IsUniformizerSemilinear, images T M, forwardBoundedSubspace
CompletedPseudoDiffOpForwardHull         divisible-part lemma M ⊆ W' + ϖ^{-c}Λ; exhaustion ⇒ ϖ^{-1}P ⊆ T^m P
CompletedPseudoDiffOpContractingLattice  splitting lemma (series Σ T^{-(i+1)} w_i, tails T t_n = w_n + t_{n+1});
                                         no bounded vectors ⇒ T⁻¹ contracts a lattice (strong induction)
CompletedPseudoDiffOpBoundedSplitting    boundedness mod B(T) is boundedness; quotient automorphism of
                                         E/W; second splitting lemma;
                                         forwardBoundedSubspace_sup_backwardContractingSubspace_eq_top
CompletedPseudoDiffOpThreePartDecomposition
                                         E = C(T) ⊕ (B(T) ⊓ B(T⁻¹)) ⊕ C(T⁻¹), contracting lattices
DifferentialVariationalOppositeBoundaryPair
                                         variationalAttractingSubspace_sup_variationalRepellingSubspace_eq_top
```

`variationalAttractingSubspace σ b L ⊔ variationalRepellingSubspace σ b L = ⊤` holds for every
differential field automorphism `σ`: bounded forward orbits are slow, bounded backward orbits are slow
for `σ⁻¹`, and every vector is a sum of the two.  No hypotheses; no heartbeat options in any new leaf
(a local registration of the valuation-ring action replaces them).

Still to do for the full weighted-flag statement of `(16)`: identify the canonical subspaces with
`B(T)`, `B(T⁻¹)` (so `F ⊓ G` is the neutral part with a `T`-stable lattice), the degree
`deg_T(W) = index(Λ, TΛ)` and the average-slope recursion giving the rational slope decomposition
`E = ⊕_s E_s` with opposite filtrations `B(ϖ^cT^d) ⊕ C(ϖ^cT^d) = E` at every rational slope `c/d`, and
the identification of the slopes (with multiplicity) with the Cartan translation vector `(14)`.
