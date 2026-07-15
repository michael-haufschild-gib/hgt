# The integration stack of the hypertranscendental constraint-curvature field

- **ID:** `constraint-curvature-integration-stack`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL HT CONJECTURE / UNIFIED REALIZATION OBJECT
- **Scientific status:** `[CONJECTURE] [LINEAR FIBER SKELETON LEAN-FORMALIZED] [RAW LIM1 CARRIER KILLED] [NOVELTY OPEN]`
- **Parents:**
  - `source-transgression-field.md`
  - `calibrated-clock-curvature-class.md`
  - `hypertranscendental-constraint-corona-motive.md`
- **Statement:** The common object is not an ordinary derived limit of finite clocks. It is the
  source-curvature field together with the derived moduli space of its global integrations in
  each realization category. Continuation, boundary conditions, monodromy, spectral
  incompleteness, and positivity are five invariants of that one integration fiber.

## Ordinary finite-clock `lim^1` no-go

Suppose every calibrated gauge space `G_N` is finite-dimensional over a field. For fixed `N`, the
images of all later transition maps in `G_N` form a descending chain of finite-dimensional
subspaces and therefore stabilize. The tower is Mittag--Leffler, so its ordinary countable
algebraic `lim^1` vanishes.

Hence a nonzero class in

```text
lim^1_N G_N                                                   (1)
```

cannot be the general thin boundary field when the gauges are genuinely finite-clock linear data.
A nonzero `(1)` would require infinite-dimensional gauges, nonclosed topological images, partial
transition maps, or another singular completion. Merely declaring one of these does not construct
the source object.

**Positive theorem-shape.** In a Mittag--Leffler realization, every compatible affine obstruction
is effective after gauge. This defines a positive clock-effective phase rather than a failed
boundary theory.

## Source curvature

Let `A_x` be the independently given algebra of nonlocal source constraints of a point `x`. Let
`O_N(x)` be its finite observable clocks and let `T_N(a)` be the calibrated `N`-shadow of
`a in A_x`. Define

```text
kappa_N(a)=p_N T_(N+1)(a)-T_N(a) p_N.                       (2)
```

The exact formal laws are

```text
p_01 kappa_12+kappa_01 p_12=kappa_02,                       (3)
kappa(a b)=kappa(a) T(b)+T(a) kappa(b),                     (4)
kappa(T+g)=kappa(T)+kappa(g).                               (5)
```

Equations `(3)`--`(5)` are Lean-formalized. They are respectively the clock Bianchi law, the
constraint-algebra Leibniz law, and gauge additivity.

**[CONJECTURE — CANONICAL SOURCE CURVATURE]** Source symbol, affine normalization, and source
relations canonically select `(2)` up to a contractible calibrated choice. When the shadows are
forward-compatible, the intrinsic finite field is the Lean-formalized quotient transfer
`O_(N+1)/range(i_N) -> O_N`, not a split boundary vector. The resulting nonlinear higher-curvature
field `bold_kappa_x` is invariant under analytic source-presentation equivalence.

The curvature field can be nonzero and still globally integrable. Nonzero curvature and
nonintegrability are distinct.

## The integration stack

For an admissible realization category `R`, let

```text
Global_R(x)                                                 (6)
```

be the derived groupoid of source operations on the completed source object, with its domain,
topology, affine calibration, and reflection retained. Let

```text
curv_R : Global_R(x) -> Curv_R(x)                           (7)
```

send a global operation to its finite-clock curvature field.

Define the **constraint-curvature integration stack**

```text
I_x(R)=hofib_(bold_kappa_x)(curv_R).                        (8)
```

It is the moduli object of global source realizations integrating the prescribed finite-clock
field. This is the proposed precise meaning of the "same interval" seen by different obstruction
chains.

At the linear level, if `curv_R` is a linear map `P -> C`, the fiber over `kappa` is empty exactly
when `kappa` is outside its range. Once a primitive exists, the fiber is canonically an affine
torsor under `ker(curv_R)`. These two facts are Lean-formalized.

## Conjecture I: the five-face theorem

**[CONJECTURE — FIVE FACES OF ONE FIBER]** Whenever `(8)` is a perfect derived analytic stack with
reflection, the five obstruction languages are the following literal invariants:

1. **continuation failure:** `I_x(R)` is empty after extension to the requested domain;
2. **boundary-condition ambiguity:** `pi_0 I_x(R)` has more than one point;
3. **monodromy:** `pi_1 I_x(R)` or the holonomy of its integration torsor is nontrivial;
4. **spectral incompleteness:** the tangent complex of `I_x(R)` has nonzero homology;
5. **positivity failure:** the reflected Hermitian orientation on that tangent homology is not
   positive.

This is stronger than matching five scalar spectra. A valid comparison must be an equivalence of
integration fibers carrying source curvature, affine origin, algebra action, and reflection.

**Falsifier.** One claimed realization has the correct degeneracy set but no functor from `(8)`, or
two realizations carry inequivalent curvature derivations despite having the same determinant.

## Conjecture II: thin boundary, infinite capacity

Let

```text
c_x(N)=trdeg_F F(x,delta x,...,delta^N x).                 (9)
```

**[CONJECTURE — THIN INTEGRATION FIELD]** A regular source-minimal constrained HT point satisfies

```text
c_x(N)=N+1 for all N,                                     (10)
```

while the cotangent complex of `(8)` is perfect of finite source-constraint rank and bounded
amplitude. Infinite algebraic clock capacity and thin boundary are therefore independent but
simultaneous properties.

The whole analytic/formal completion cokernel may be enormous; thinness applies only to the
source-generated integration stack.

## Conjecture III: nonlinear clock-corona correspondence

The unary curvature field cannot reconstruct a nonlinear constraint. Let

```text
bold_kappa_x=kappa_x^(1)+kappa_x^(2)+kappa_x^(3)+...       (11)
```

be the complete hierarchy obtained from the Taylor layers and syzygies of the analytic source
constraint.

**[CONJECTURE — CLOCK-CORONA CORRESPONDENCE]** The formal deformation category of regular
source-minimal constrained HT germs is equivalent to the category of integrable, affine-calibrated,
maximal-capacity thin curvature fields satisfying:

1. the higher Bianchi identities;
2. the constraint-algebra Leibniz identities;
3. analytic source-growth conditions;
4. presentation descent;
5. reflection coherence when present.

Full faithfulness is nonlinear source reconstruction. Essential surjectivity is the inverse
problem: every abstract field satisfying these integrability conditions comes from a nonlocal HT
source constraint.

Formal moduli, curved `L_infinity` structures, and derived integration stacks are parent languages.
The candidate-new assertion is this source-forced correspondence and the maximal-capacity/thin-
boundary essential image.

**Falsifiers.** Two inequivalent analytic source germs yield equivalent complete fields and
integration stacks; or an integrable field satisfying all five conditions has no source
realization.

## Conjecture IV: Gamma is the positive integrable vacuum

Gamma's unit translation has nonzero rank-one finite-clock curvature, but the factorial tail sums
to the actual analytic translation operator in its source topology.

**[CONJECTURE — GAMMA INTEGRABILITY]** After affine normalization, the Gamma integration stack is
nonempty and contractible. Its rank-one curvature and infinite Taylor conormal are respectively
the field strength and boundary covector of its unique global analytic primitive.

This corrects the earlier guess that Gamma should carry a nonzero ordinary `lim^1` obstruction.
Gamma is the solvable vacuum model showing that a thin nonzero field need not obstruct global
integration.

**Falsifier.** The source topology admits two inequivalent normalized global primitives, or the
rank-one curvature fails to reconstruct analytic unit translation.

## Conjecture V: nonlinear and singular phases

Gamma cannot test higher curvature because its tangent shift constraint is linear. A raw Böttcher
power constraint has higher Taylor layers, but local logarithmic linearization transfers them to a
period-lattice cocycle. Böttcher is therefore the first curvature--holonomy transfer test, not yet
a genuinely higher minimal-curvature example.

**[CONJECTURE — PHASE STRUCTURE]** The general constrained HT theory contains at least four phases:

1. **integrable:** `(8)` is contractible after calibration;
2. **multiboundary:** `(8)` is nonempty with nontrivial `pi_0`;
3. **holonomic:** `(8)` is connected with nontrivial `pi_1`;
4. **singular:** `(8)` is empty or has nonperfect tangent because integration is nonclosable,
   noncompact, or obstructed by a quotient ideal.

These phases can share the same finite algebraic capacity. Hypertranscendence does not choose the
phase; the source constraint does.

**Positive no-go.** A route that lands in the integrable phase has discovered a global source
operation, not failed to discover an obstruction. Its positive statement should be an integration
or uniqueness theorem.

## Conjecture VI: self-dual degeneracy spectrum

For a reflected parameter family `x_s`, suppose

```text
I_(s^vee)(R) ~= dual(I_s(R))                               (12)
```

coherently, with a source-defined orientation line.

**[CONJECTURE — COMMON SELF-DUAL DEGENERACY]** The common degeneracy spectrum is the support where
the self-dual integration stack ceases to be transversely a single oriented point. Fixed
parameters are self-dual degeneracies; nonfixed degeneracies occur in reflected pairs.

Reflection alone does not exclude the paired off-fixed case. Fixed-locus confinement requires a
new positive-orientation theorem on the actual tangent complex of `(8)`.

## RH pressure test only

**[CONJECTURE; NOT AN RH RESULT]** A completed-zeta source may determine `bold_kappa_zeta` from its
prime and archimedean constraint algebra before any divisor is examined. The Sonin/Calkin,
Hedenmalm/nonclosability, continuation, positivity, boundary-extension, and Böttcher/monodromy
chains represent the same object only if they are functorial realizations of one integration stack
`I_zeta` preserving `(3)`--`(5)` and `(12)`.

The critical zeros would then be fixed-locus degeneracies of that stack. No zeta function,
completed xi function, zeros, or zero-indexed operator may be used to define the curvature field.
No such common realization has yet been constructed.

## Parent-theory and manufacture attacks

- Homotopy fibers, derived moduli, deformation complexes, boundary triples, and integration
  groupoids are established parent structures.
- Choosing `Curv_R` after seeing the desired global object makes `(8)` tautological. The finite
  curvature must be source-derived first.
- Taking the full completion defect loses HT specificity.
- Allowing arbitrary topological completions manufactures empty or nonempty fibers at will.
- Low displacement rank is classical structured-operator theory.
- A self-dual stack may have off-fixed degeneracies.
- Gamma can validate integrability and calibration, but not nonintegrability, nonlinear coherence,
  or spectral realization.

The candidate-new residue is the canonical source construction of `bold_kappa_x`, the
clock-corona correspondence, and a theorem identifying genuinely different analytic obstruction
chains as invariants of the same source integration stack.

## Gates

- [x] ordinary finite-dimensional algebraic `lim^1` carrier killed
- [x] nonzero curvature separated from nonintegrability
- [x] Bianchi, gauge-additivity, and constraint-algebra Leibniz laws Lean-formalized
- [x] linear fiber nonemptiness/range criterion Lean-formalized
- [x] nonempty linear fiber identified with the kernel torsor in Lean
- [x] canonical finite Taylor shadows and rank-one Gamma curvature constructed
- [ ] source-presentation invariance of the Gamma calibration proved
- [ ] Gamma rank-one field proved to integrate uniquely
- [x] raw Böttcher higher curvature rejected as coordinate-invariant data
- [ ] Böttcher curvature--holonomy transfer class constructed
- [ ] higher minimal curvature constructed for a genuinely non-linearizable source
- [ ] one noncontractible source integration stack constructed
- [ ] presentation invariance proved for two source descriptions
- [ ] nonlinear clock-corona full faithfulness proved in one class
- [ ] essential-image integrability criterion proved
- [ ] self-dual tangent pairing constructed in one parameterized non-RH family
- [ ] two distinct obstruction realizations proved equivalent as integration fibers
- [ ] independent novelty and significance audit
