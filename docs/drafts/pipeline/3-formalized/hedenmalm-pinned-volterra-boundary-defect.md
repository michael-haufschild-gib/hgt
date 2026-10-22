# Universal pinned-Volterra boundary defect and bounded composite-metric no-go

- **ID:** `hedenmalm-pinned-volterra-boundary-defect`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / OPERATOR CLASSIFICATION / NO-GO WITH POSITIVE SURVIVOR
- **Route:** D — prime–archimedean Hankel sign and reconstruction
- **Scientific status:** `[PROVED HERE] [LOCAL-RESEARCH] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../2-fully-proven/needs-audit/hedenmalm-quantile-volterra-universal-boundary-defect.md`
- **Statement:** On actual infinite-dimensional complex `L2(0,1)`, the pinned primitive has an
  explicit Hilbert adjoint; their sum is a self-adjoint rank-two affine boundary operator with one
  positive and one negative mode, while no injective bounded composite metric can satisfy the
  corresponding anticommutator equation.

## Goal

Replace two pieces of operator theatre with exact theorems:

1. formalizing only the resulting `2 x 2` boundary matrix does not prove the full `L2` adjoint and
   range statement;
2. saying that a local metric "should" symmetrize the quantile-normal operator does not establish
   a closed operator identity.

The module therefore constructs the full bounded operators first and derives the finite boundary
system as their exact range.  It also proves a sharp bounded-operator obstruction before any Xi
zero or target divisor is read.

## Theorem

Let

```text
H = L2((0,1), C),
(Cf)(t) = integral_0^t f(u)du - t integral_0^1 f(u)du.
```

Then `C` is bounded with norm at most `2`.  Its Hilbert adjoint is the bounded reverse primitive

```text
(Cdag f)(t) = integral_t^1 f(u)du - integral_0^1 u f(u)du.
```

The operator

```text
R = Cdag + C
```

has the exact pointwise representative

```text
(Rf)(t) = (1-t) integral_0^1 f(u)du - integral_0^1 u f(u)du.
```

Hence

```text
range R = span_C {1,t},
finrank_C(range R) = 2,
Rdag = R.
```

Writing `center(t)=t-1/2`, the explicit modes

```text
v_plus  = 1-center,
v_minus = 1+center
```

satisfy

```text
inner(R v_plus,v_plus)   =  1/6,
inner(R v_minus,v_minus) = -1/6.
```

Thus the full infinite-dimensional boundary defect has exact mixed inertia `(1,1)`.

The reverse primitive is injective.  Consequently every bounded operator `A : H -> H` satisfying

```text
Cdag A + A C = 0
```

kills the constant mode.  In particular no injective bounded `A` satisfies this equation.
If `A` is a bounded pointwise multiplication operator, its multiplier is `A(1)`; hence the same
identity forces `A=0`.  This is the exact bounded local-metric classification, not only an
injectivity obstruction.

## Proof architecture

1. Restrict Lebesgue measure to `[0,1]` and prove it is a probability measure with null
   singletons.
2. Use the probability-space `L2 -> L1` bound to construct lower and upper primitives as genuine
   `L2` vectors and bounded continuous linear maps.
3. Prove the forward/reverse inner-product identity by an integrable triangle kernel and Fubini.
   Hilbert-adjoint extensionality then gives `Cdag=C*`.
4. Convert upper prefixes to interval integrals.  If `Cdag f=0`, continuity of the indefinite
   integral upgrades almost-everywhere constancy to pointwise constancy on `[0,1]`; the interval
   Lebesgue differentiation theorem gives `f=0` almost everywhere.
5. Add the two primitive formulas.  Exact zeroth, first, and second interval moments give the
   affine range, reverse range witnesses, rank two, and the two signed quadratic values.
6. Apply `Cdag A+A C=0` to `1`.  Since `C1=0` and `Cdag` is injective, `A1=0`; injectivity of `A`
   contradicts `1 != 0`.  For a pointwise multiplier, `Af=(A1)f`, so `A1=0` forces `A=0`.

No numerical computation, finite-dimensional surrogate, Xi zero enumeration, RH hypothesis, or
unproved domain assertion enters the proof.

## Hostile audit

1. **Not RH.** Mixed inertia supplies both signs and does not force theta root modes into the null
   cone.
2. **Not the complete quantile theorem.** The probability-integral unitary from Hedenmalm's
   weighted source space, the unbounded quantile multiplier, and transformed source inverse remain
   separate formal obligations on the parent card.
3. **No unbounded-domain claim.** The anticommutator theorem concerns bounded composite `A`.  A
   singular metric whose composite with quantile speed is unbounded must still prove closedness,
   common-domain invariance, and symmetry.
4. **No local-to-global leap.** The theorem kills bounded injective composite metrics obeying the
   local anticommutator.  It does not exclude genuinely nonlocal cross-source boundary laws.
5. **No matrix theatre.** The rank-two result is derived only after the complete `L2` operators,
   adjoint, injectivity, and range equality are proved.

## Positive survivor and representation lesson

Failure of bounded local symmetrization exposes a sharper survivor than a bare no-go:

```text
source dependence may be diagonal/local,
but neutralization of the universal two-channel flux must be genuinely nonlocal.
```

For Route D, this removes local reweighting of a source-normal Volterra inverse as a producer.  Any
reopening must construct the global cross-source incidence or boundary law that selects the null
cone before Xi divisor specialization.  That surviving law is exactly where Weil positivity
remains, so the present theorem narrows the hard problem without renaming it.

## Novelty audit

Internal searches found no prior formal or paper card containing the probability-coordinate pinned
primitive, its exact adjoint range, and the composite-metric anticommutator obstruction together.
External exact searches for `C* M_a + M_a C`, Volterra multiplication symmetrizers, and weighted
Volterra metrics found adjacent literature on the classical Volterra operator, its injective
adjoint, commutants, and complex symmetry, but no matching pinned-primitive theorem.  This is
negative search evidence only; external novelty remains unverified.

Adjacent primary sources:

- H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494 (2026).
- P. Aiena, F. Burderi, and S. Triolo, *Further Properties of an Operator Commuting with an
  Injective Quasi-Nilpotent Operator*, Mediterr. J. Math. 21 (2024), 34.

## Lean formalization

```text
GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPinnedVolterraBoundaryDefect
```

Main public declarations:

```text
pinnedVolterraCLM
pinnedVolterraAdjointCLM
pinnedVolterraAdjointCLM_eq_adjoint
pinnedVolterraAdjointCLM_injective
adjoint_add_pinnedVolterraCLM_eq_pinnedBoundaryCLM
range_pinnedBoundaryCLM_eq_affineSubspace
pinnedBoundaryCLM_adjoint_eq
finrank_range_pinnedBoundaryCLM
inner_pinnedBoundaryCLM_pinnedPositiveMode
inner_pinnedBoundaryCLM_pinnedNegativeMode
pinnedBoundaryCLM_exact_rankTwo_mixed_inertia
anticommutator_eq_zero_imp_apply_pinnedOne_eq_zero
IsPinnedPointwiseMultiplier
pointwiseMultiplier_anticommutator_eq_zero_imp_eq_zero
no_injective_pinnedVolterra_anticommutator
```

## Gates

- [x] exact conjecture frozen before proof engineering
- [x] prior Route D and Hedenmalm corpus audit
- [x] dependency-closed paper proof
- [x] infinite-dimensional construction, not matrix surrogate
- [x] Fubini adjoint proof
- [x] Lebesgue-differentiation injectivity proof
- [x] exact range and rank two
- [x] explicit positive and negative modes
- [x] bounded injective composite-metric no-go
- [x] exact bounded pointwise-multiplier classification
- [x] hostile audit and positive survivor
- [x] external preliminary novelty search
- [x] unconditional Lean formalization
- [x] theorem-area umbrella import
- [x] `lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmPinnedVolterraBoundaryDefect.lean`
- [x] leaf-only `lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPinnedVolterraBoundaryDefect`
- [x] axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [ ] broad external operator-theory novelty audit
- [ ] probability-integral transform and actual theta-source specialization

No full build was run.
