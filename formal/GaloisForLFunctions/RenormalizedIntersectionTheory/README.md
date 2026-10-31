# Renormalized Intersection Theory of the Scaling Surface (RIT)

Namespace `GaloisForLFunctions.RenormalizedIntersectionTheory`; umbrella
`RenormalizedIntersectionTheory.lean`. Everything is unconditional; theorems named
`riemannHypothesis_iff_*` are equivalences, not proofs of RH.

## 1. Motivation

Weil's proof for a curve `C/𝔽_q` uses one object on `C × C`: the graph of Frobenius. Its intersection
with the diagonal counts points (Lefschetz), the Hodge index theorem on the plane it spans with the
fibres gives the sign (Castelnuovo–Severi), Riemann–Roch gives the count, and the graph is canonical,
so no twin of `ζ_C` carries it.

Over `ℤ` the corpus has every ingredient separately and no object that carries two of them:

- the scaling correspondences `Γ_u` and their intersection numbers exist: the intersection matrix of
  the `Γ_u` is the Weil correlation, an exponential sum over the zeros (AOG, HKT);
- the self-intersection of the diagonal diverges like `log N` and only exists after a counterterm
  that runs with the horizon (`log N − γ`); every fixed counterterm loses the sign (AIT, RBG, AKG);
- the local data at every place are hyperbolic planes (pole–successor states), and the archimedean
  place glues the global object by one hyperplane, not by a square (AKG);
- the sign of the complete Weil form is localized: averages over conductors are positive at
  RH-complete resolution, the ground state is the pole conductor, and the open part is the
  pole-orthogonal hyperplane (CAF, CACT, RAPT).

RIT is the geometry that puts these on one object: a **renormalized intersection pairing on the
scaling surface**, with local terms at all places coupled through the product formula, a canonical
running counterterm, and a Hodge index statement on the hyperplane orthogonal to the pole class.
Its purpose is to answer, with theorems, what this geometry can and cannot deliver, and which single
statement inside it is RH.

## 2. Objects

| Object | Meaning |
|---|---|
| Scaling surface | the test space of the explicit formula, with the Weil pairing as intersection form |
| Scaling correspondence `Γ_u` | dilation by `u ∈ ℚ_{>0}`; `Γ_u · Γ_v = K(u⁻¹v)`, `K` the Weil correlation |
| Pole class `v_1` | the boost functional `w ↦ Σ w_i u_i^{−1/2}`; on integer slopes the pole-conductor vector `n^{−1/2}` |
| Successor class | the conformal successor `−c|b|` on translations; with the pole it spans the hyperbolic plane |
| Local boost characters | `χ_v(u) = |u|_v^{1/2}` at every place `v`; local pole pair `χ_v + χ_v^{−1}` |
| Weights | sign patterns `ε ∈ {±1}^S`; weight characters `χ^ε = ∏_{p∈S} χ_p^{ε_p}` |
| Extremal weight | `ε` constant; by the product formula the archimedean boost |
| Tensor (Künneth) square | the kernel `K ⊗ K` on the product scaling surface; frequencies `ρ + ρ'` |
| Renormalized self-intersection | horizon value minus the running counterterm; finite part |
| Index `κ` | number of negative squares of a Hermitian kernel on a group |
| Collision quantum `O` | horizontal collision charge of the heat flow on a window |

## 3. Language

- **Renormalized pairing**: a pairing defined at horizon `N` minus a counterterm that runs with `N`.
- **Pole-orthogonal hyperplane**: kernel of the boost functional; on integer slopes `v_1^⊥`.
- **Renormalized Hodge index**: the pairing is definite on the pole-orthogonal hyperplane; equivalently
  the global state has exactly one negative square.
- **Separated sum / tensor product / extremal component** of local poles: the three ways local hyperbolic
  planes can be combined.
- **Archimedean-continuous weight**: a weight character that is the restriction of `u ↦ u^s`.
- **All-or-nothing index**: an index that takes only the values `0` and `∞`.

## 4. Mechanisms (target)

1. **Hyperbolic plane of the pole.** The pole and successor classes span a plane of signature `(1, 1)`;
   the archimedean glue costs exactly one square and is blind to the weight of the pole.
2. **Product-formula gluing.** Separated local poles keep one square each; their tensor product
   decomposes into weight pairs `{ε, −ε}`; the product formula identifies the archimedean pole with the
   extremal weight, the only archimedean-continuous one.
3. **Weight amplification.** Tensor powers multiply positive and negative squares; with infinitely many
   positive squares the index of a tensor power is `0` or `∞`.
4. **Running counterterm.** The divergent self-intersection is `log N` plus a finite part; the finite
   part is the archimedean constant; over `𝔽_q` the counterterm is exact.
5. **Hodge index on the hyperplane.** RH is the definiteness of the renormalized pairing on the
   pole-orthogonal hyperplane, i.e. index one for the glued global state.

## 5. Pillar theorems (target list; statuses in §12)

| Pillar | Statement |
|---|---|
| P1 Hyperbolic plane | the glued global state has index `κ_ζ + 1`; RH ⇔ index one ⇔ positivity on the pole-orthogonal hyperplane |
| P2 Product-formula gluing | separated sum of `m` local poles: index `m`; tensor product: index `2^{m−1}`; extremal component: index one, equal to the archimedean pole on `S`-units; extremal ⇔ archimedean-continuous |
| P3 Künneth square | `κ(K ⊗ K) ∈ {0, ∞}`; RH ⇔ the tensor square of the Weil correlation is positive ⇔ its index is finite |
| P4 Canonical finite part | renormalized self-intersection of the diagonal = `−γ`; exact counterterm over `𝔽_q` |
| P5 Pole class on integer slopes | the boost functional on slopes `1..N` is the pole-conductor vector, the complete-Weil ground state |
| P6 Quantum | collision mass after small heat = twice the hyperplane index plus multiplicity excess |

## 6. Tools (target)

- Weight calculus for products of local pole pairs (expansion, pairing of `ε` with `−ε`, separation by
  `∏_{p∈S} p`).
- Kronecker inertia for tensor kernels on product groups.
- Hyperplane index (boost-polar index) and its gluing formula.
- Finite-part extraction for divergent prime sums.

## 7. Questions

1. Is the global pole a product-formula coupling of local poles with one negative square?
2. Is the renormalized pairing definite on the pole-orthogonal hyperplane, and what is it equivalent to?
3. Does the Künneth square carry a finite-index stratum?
4. What is the canonical finite part of the renormalized self-intersection?
5. Is the collision quantum an intersection index?
6. Why are negative directions confined to low conductors, and with which dependence?
7. What separates `ℤ` from `𝔽_q[T]` inside this geometry?

## 8. Traps (initial)

| Trap | Fact |
|---|---|
| Summing local poles gives the global pole | separated places keep one square each |
| A fixed counterterm gives a sign | no fixed counterterm makes the prime kernel Pontryagin |
| The pole selects ζ on the hyperplane | the glued index is blind to the pole weight |

## 9. Context

Neighbours: AdelicKreinGeometry (local signatures, gluing), HeckeKreinToeplitz (index formula),
ArithmeticIntersectionTheory (circle intersection, regulator anomaly), RenormalizedBiarithmeticGeometry
(survival cones), ArithmeticOrientationGeometry (scaling correspondences), ArithmeticCastelnuovoSeveri
(scaling surface, Hodge index), CompletedArithmeticForms / CriticalArithmeticCorrelationTheory /
RenormalizedArithmeticPotentialTheory (complete Weil matrix), HTGeometry (tensor inertia), RHTower
(Mertens, heat collisions).

## 10. Success criteria (initial)

A pillar counts when it is a Lean theorem, unconditional, and either (a) answers a question of §7 with
an equivalence, a classification or a no-go, or (b) builds a tool used by another pillar.

## 11. Contribution criteria (initial)

New objects must be built from integers and adeles; every equivalence with RH must be stated as such;
every positive theorem must say which wall it does not cross.

## 12. Status

First draft. Modules and pillar statuses are added as they are proved.
