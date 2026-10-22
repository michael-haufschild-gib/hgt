# The constraint-linearization gerbe and curvature--holonomy conservation

- **ID:** `constraint-linearization-gerbe`
- **Stage:** 1-in-progress
- **Type:** GENERAL HT CONJECTURE / LOCAL-LINEARIZATION AND GLOBAL-HOLONOMY FIELD
- **Scientific status:** `[CONJECTURE] [EXPONENTIAL-SEQUENCE BACKBONE CLASSICAL] [GAMMA/BOTTCHER MODELS] [NOVELTY OPEN]`
- **Parents:**
  - `constraint-curvature-integration-stack.md`
  - `calibrated-clock-curvature-class.md`
  - `source-mackey-clock-interval.md`
- **Statement:** For group-valued nonlocal constraints, local nonlinear curvature and global
  monodromy are different representatives of one total source class. Finite differential clocks
  see the local Lie-algebra data but can erase the discrete period lattice that prevents the local
  linearizations from gluing.

## Raw nonlinear arity is not invariant

Let `P` be a polynomial of degree `d>=2` and let `Phi` be an external Böttcher coordinate on a
domain where

```text
Phi(P(z))=Phi(z)^d.                                      (1)
```

The right side has polynomial degree `d` in `Phi`, so its raw Taylor hierarchy has nonzero
homogeneous layers through order `d`. But on any simply connected chart where `Phi` is nonzero,
choose `u=log(Phi)`. Then

```text
u(P(z))-d u(z) in 2 pi i Z.                              (2)
```

On a connected chart the integer is locally constant and normalization can often fix it. Thus the
apparently nonlinear constraint `(1)` becomes affine-linear locally. Its degree and raw higher
variations are not presentation invariants.

On overlaps of logarithm charts,

```text
u_i-u_j=2 pi i n_ij,  n_ij in Z,                         (3)
```

and the `n_ij` form a Cech cocycle. The nonlinearity removed locally has reappeared as global
holonomy.

The same mechanism occurs for Gamma. On a chart avoiding poles and a branch cut,

```text
Gamma(z+1)=z Gamma(z)                                    (4)
```

becomes

```text
g(z+1)-g(z)-log(z) in 2 pi i Z,  g=log(Gamma).           (5)
```

Differentiation gives the single-valued meromorphic equation

```text
psi(z+1)-psi(z)=1/z,                                     (6)
```

and kills the locally constant lattice in `(5)`. This is an exact mechanism by which differential
clock observables lose global source information.

The exponential sequence

```text
0 -> 2 pi i Z -> O --exp--> O^x -> 1                    (7)
```

and its connecting class are classical. Böttcher hypertranscendence and the classification of
differentially algebraic exceptional cases are also established parent results. The new claim is
not `(2)`, `(3)`, `(5)`, or `(7)` separately.

## Conjecture I: curvature--holonomy conservation

Let a regular constrained HT source admit local calibrated charts in which its source constraint
takes values in a finite-dimensional algebraic or analytic group `G`. Let `g=Lie(G)` and let
`Lambda_G` be the local period/deck group of a source logarithm.

**[CONJECTURE — TOTAL SOURCE CLASS]** The local clock-curvature fields, their higher nonlinear
corrections, and the transition cocycles between local linearizing charts assemble into one total
hypercohomology class

```text
Theta_x in H_total(source clock cover, Lambda_G -> g -> Curv_x).  (8)
```

The displayed complex is schematic until the source site and curvature differential are defined.
A source coordinate change may transfer mass between the curvature and Cech components of
`Theta_x`, but cannot change the total class.

**[CONJECTURE — CONSERVATION LAW]** If a nonlinear chart kills all higher local curvature, the
same source information survives as nontrivial affine holonomy or a period-lattice cocycle. If the
holonomy is killed on a cover, it reappears in the descent data needed to return to the source.

**Falsifier.** A source-equivalent change of charts kills both local curvature and global cocycle
while preserving all source normalization and deformation data.

## Conjecture II: the linearization gerbe is the integration stack

Let `Lin_x(U)` be the groupoid of calibrated source charts on `U` that linearize the nonlocal
constraint to its minimal Lie-algebra-valued form. These groupoids form a stack over the source
domain.

**[CONJECTURE — LINEARIZATION/INTEGRATION EQUIVALENCE]** The stack of local linearizing charts and
their descent data is equivalent to the constraint-curvature integration stack

```text
Lin_x ~= I_x.                                             (9)
```

Under `(9)`:

1. absence of a chart on a larger domain is continuation failure;
2. inequivalent global charts are boundary conditions;
3. automorphisms and transition loops are monodromy;
4. infinitesimal failure of chart rigidity is spectral tangent homology;
5. reflected orientation of that homology is the positivity problem.

This gives a concrete source interpretation to the abstract integration fiber. It also makes the
"same object" criterion strict: two obstruction chains agree only if they preserve the same local
linearizing charts, period cocycle, and curvature under `(9)`.

**Falsifier.** Gamma or Böttcher supplies an integration primitive with no corresponding local
linearizing chart, or its chart gerbe carries strictly more source deformation data than the
integration stack.

## Conjecture III: abelianizable and genuinely higher HT phases

**[CONJECTURE — ABELIANIZABLE PHASE]** Gamma and generic nonexceptional Böttcher coordinates belong
to an abelianizable constrained-HT phase: after a source cover their minimal higher curvature is
unary, while a rank-one period lattice carries the global defect.

**[CONJECTURE — GENUINELY HIGHER PHASE]** Other constrained HT sources have a nonabelian minimal
model in which no analytic source chart kills the higher brackets. Their thin boundary is measured
by the minimal `L_infinity` ranks together with the holonomy of their integration stack.

Raw polynomial degree does not distinguish these phases. The invariant is the minimal total class
`Theta_x` after all permitted analytic source equivalences.

**Positive no-go.** If Böttcher's higher variations disappear under logarithmic linearization,
this does not kill the boundary program. It proves that Böttcher is a holonomy model rather than a
genuinely higher-curvature model. A different source is then required to test nonlinear minimality.

## Conjecture IV: differential clocks forget the discrete source lattice

The derivative annihilates locally constant transition functions. More generally, finite
differential jets naturally see the Lie algebra `g` but not necessarily the integral/deck lattice
`Lambda_G` from which `G` is recovered.

**[CONJECTURE — LATTICE BLINDNESS]** For an abelianizable corona-pure HT source, every finite
algebraic differential clock factors through the infinitesimal `g`-realization of `(8)`, while the
source constraint depends essentially on `Lambda_G`. Hypertranscendence prevents any finite
algebraic differential relation from reconstructing that lost global lattice.

This is stronger than saying that derivatives lose an additive constant. The claim is that the
minimal period/deck lattice is a source invariant and that its loss is exactly the finite-clock
nonconservativity measured by the curvature field.

**Falsifier.** A finite algebraic differential observable reconstructs the normalized Böttcher or
Gamma period cocycle functorially from a bounded jet window.

## Conjecture V: self-dual total class

Suppose source reflection acts on `G`, `g`, `Lambda_G`, and the clock cover.

**[CONJECTURE — SELF-DUAL LINEARIZATION GERBE]** Reflection carries `Theta_s` to the dual of
`Theta_(s^vee)` and equips the fixed integration stack with an orientation line. The common
degeneracy spectrum is the support where the reflected linearization gerbe fails to be a unique
transverse oriented chart.

Self-duality still permits off-fixed paired failures. Positivity of the actual source orientation,
not the existence of the gerbe, is needed for fixed-locus confinement.

## RH pressure test only

**[CONJECTURE; NOT AN RH RESULT]** The prime Euler product provides a multiplicative source chart
in its initial half-plane, and its logarithm provides an additive prime chart there. A completed
source construction would have to glue this chart to an archimedean reflected chart without using
the zeta divisor. Its total class `Theta_zeta`, if it exists, would be the pre-divisor
linearization gerbe.

The different RH chains could represent curvature, continuation obstruction, period holonomy,
boundary-chart ambiguity, or reflected tangent orientation of this one class. Critical zeros
would be fixed-locus degeneracies of the self-dual gerbe. This is a research hypothesis, not an RH
result; defining the gerbe from `log zeta`, `xi`, or their zeros would be circular.

## Parent collisions and gates

- Exponential sequences, Deligne cohomology, lifting gerbes, differential characters, and
  curvature/holonomy packages are parent theory.
- Local logarithmic linearization of multiplicative constraints is classical.
- Formal-moduli minimal models and nonabelian cohomology are parent languages.
- The candidate novelty is the source-canonical total class `(8)`, its finite-clock lattice
  blindness, and equivalence `(9)` across actual HT constraint presentations.

- [x] raw nonlinear arity killed as a coordinate invariant
- [x] Gamma and Böttcher local linearization mechanisms isolated
- [x] exact location of lost discrete lattice identified
- [ ] source site and admissible clock cover defined
- [ ] `Theta_Gamma` constructed without choosing a logarithm globally
- [ ] `Theta_Bottcher` constructed and matched to deck monodromy
- [ ] lattice blindness proved for every finite differential clock in one model
- [ ] linearization/integration equivalence `(9)` proved
- [ ] one genuinely higher nonabelian HT source identified
- [ ] reflected orientation constructed in a non-RH family
- [ ] two analytic obstruction chains proved to carry one `Theta_x`
- [ ] independent novelty and significance audit
