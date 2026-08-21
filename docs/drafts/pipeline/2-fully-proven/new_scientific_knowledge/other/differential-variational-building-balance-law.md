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
