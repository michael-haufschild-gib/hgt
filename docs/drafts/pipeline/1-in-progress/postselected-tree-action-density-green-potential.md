# Postselected tree action density and dynamical Green potential

- **ID:** `postselected-tree-action-density-green-potential`
- **Stage:** 1-in-progress
- **Type:** EXACT FINITE-DEPTH THEOREM / QFT-FACING CONJECTURE
- **Scientific status:** `[FINITE TREE LAW PROVED] [GREEN-POTENTIAL IDENTIFICATION PROVED]`
  `[HT INHERITANCE OPEN] [CANDIDATE NEW PHYSICAL OBSERVABLE]`
- **Parent theorem:**
  `../2-fully-proven/needs-audit/postselected-qubit-clock-integrability-fracture.md`
- **Tail classifications:**
  `../2-fully-proven/new_scientific_knowledge/rational-coarse-graining-orbifold-tail-classification.md`
  and
  `../2-fully-proven/new_scientific_knowledge/nonautonomous-rational-first-order-tail-orbifold-law.md`
- **Statement:** Iterating the balanced postselected-qubit protocol as a complete binary tree makes
  the intensive negative log-success probability equal to a canonical escape-rate potential of the
  homogeneous rational lift.  This gives an operational tree-tensor-network action density whose
  curvature detects the Julia equilibrium geometry.  Whether this nonholomorphic physical
  observable is itself hypertranscendental is the open core.

## Exact postselected tree

Use the homogeneous lift of the balanced conditional-qubit map

```text
H(a,b)=(a^2+b^2,b^2-a^2),                                     (1)
```

and the squared amplitude norm

```text
S(a,b)=|a|^2+|b|^2.                                            (2)
```

The parallelogram identity gives

```text
S(H(a,b))=2(|a|^4+|b|^4).                                     (3)
```

The successful XOR measurement keeps the unnormalized amplitudes `(a^2,b^2)`; the subsequent
balanced unitary does not change their norm.  Therefore the exact one-node success probability is

```text
                   |a|^4+|b|^4          S(Hv)
p(v)= -------------------------------- = ---------.             (4)
                   S(v)^2                2 S(v)^2
```

This probability is projectively well defined.  For the affine real ray `(z,1)`,

```text
p(z)=(z^4+1)/(z^2+1)^2,             1/2 <= p(z) <= 1.          (5)
```

## Exact finite-depth success theorem

To produce one depth-`n` output, start with `2^n` identical input qubits and contract a complete
binary tree of the successful two-copy instrument.  Set

```text
v_0=v,                v_(k+1)=H(v_k),                S_k=S(v_k). (6)
```

At layer `k`, there are `2^(n-1-k)` independent nodes, each with success probability
`S_(k+1)/(2S_k^2)`.  Hence

```text
P_n(v)=product_(k=0)^(n-1)
         [S_(k+1)/(2S_k^2)]^(2^(n-1-k)).                       (7)
```

Every intermediate norm cancels exactly.  Since the complete binary tree has `2^n-1` internal
nodes,

```text
                              S_n
P_n(v)= -------------------------------------------------.      (8)
          2^(2^n-1) S_0^(2^n)
```

Equation `(8)` is not an asymptotic estimate.  It is the exact Born probability that every
postselection in the depth-`n` tensor network succeeds.

## Intensive action density

Define the negative log-success cost per ultraviolet input qubit by

```text
A_n([v])=-2^(-n) log P_n(v).                                   (9)
```

The projective scaling of numerator and denominator in `(8)` cancels, and

```text
A_n([v])=log S_0+(1-2^(-n))log 2-2^(-n)log S_n.               (10)
```

Because `(1)` is a nondegenerate homogeneous polynomial lift of degree two, its escape-rate limit

```text
G_H(v)=lim_(n->infinity) 2^(-n) log S(H^n(v))                 (11)
```

exists away from the zero vector and satisfies

```text
G_H(Hv)=2G_H(v),
G_H(cv)=G_H(v)+2log|c|.                                       (12)
```

Therefore the physical infinite-tree action density exists and is

```text
A([v])=log S(v)+log 2-G_H(v).                                 (13)
```

Equivalently, if

```text
g_F([v])=G_H(v)-log S(v)                                      (14)
```

is the projective dynamical Green potential in the squared-norm convention, then

```text
A=log 2-g_F.                                                   (15)
```

The same identity follows from the exact weighted cohomological equation

```text
A([v])=1/2[-log p(v)+A(F[v])].                                (16)
```

Thus the resource cost of the quantum postselection tree is not merely correlated with complex
dynamics: it is the canonical projective Green potential, up to the fixed additive normalization
in `(15)`.

## Physical geometry

In standard pluripotential normalization, the curvature of the Green potential together with the
Fubini--Study background gives the equilibrium measure of the rational map, supported on its Julia
set.  Consequently the state-dependence of the asymptotic postselection action has a canonical
geometric singularity set: the same Julia boundary that separates stable conditional-qubit
behaviors.

This suggests an operational protocol.  Prepare input rays across a two-real-dimensional patch,
measure the all-success frequency for increasing complete-tree depth, and estimate `A_n`.  The
limiting action landscape reconstructs the Green potential; its curvature reconstructs the
equilibrium geometry.  This is resource-intensive—`2^n` input copies and exponentially rare
all-success events can be required—but it is an exact Born-probability statement, not a hidden
auxiliary coordinate.

## Why the Green action cannot be a hidden finite-jet current

The balanced rational map is nonexceptional.  The autonomous rational-tail classification
therefore gives a trivial stable differential-observable tail for a differential-generic source
family.  The nonautonomous extension further says that any persistent first-order observable in a
layer-dependent degree-expanding rational tower forces the late layers into parabolic-orbifold
coverings.

These theorems rule out the easiest redressing of `(13)`: the Green action cannot secretly be an
ordinary finite differential-rational current transported through every layer.  It evades the tail
classification in two load-bearing ways:

1. it is defined by an infinite-depth norm limit, not a finite jet;
2. it depends on amplitudes and their conjugates, not on a holomorphic scalar jet alone.

Thus a proof of HT inheritance for `A` would genuinely extend the current differential-tail theory
to nonholomorphic or polarized infinite-depth observables.  Conversely, if the polarized action
turned out to be DA, that would not contradict the tail theorem unless it also became an exact
finite-order stable current.

## QFT interpretation and limit

The complete binary circuit is a postselected tree tensor network.  Its negative log contraction
weight is an action, and `(9)` is the intensive action density per boundary leg.  Equation `(16)` is
an exact discrete radial renormalization law.  This is the finite-dimensional local model for a
measurement-conditioned tensor-network path integral.

The connection is structural but not yet a continuum QFT theorem.  Tensor-network
renormalization does provide lattice and continuum constructions for Euclidean quantum fields, but
the present tree has no spacetime locality, stress tensor, reflection-positivity proof, or
controlled continuum limit.  Calling `(15)` a QFT free energy without those structures would be
theatre.

The exact continuum target is:

`[CONJECTURE]` There exists a reflection-positive postselected tensor-network regularization of a
nontrivial quantum field theory whose radial boundary-source instrument contains the balanced
projective map `F`, and whose renormalized all-success action density converges to a nonconstant
field-theoretic observable carrying the same Green-potential obstruction.

## Hypertranscendence open core

The parent theorem proves that the holomorphic exact radial **clock** of `F` is HT.  It does not
automatically prove that `A` is HT, because `A` depends on both amplitudes and their complex
conjugates and is not a holomorphic Poincare, Schroeder, Abel, or Boettcher function.

The correct mathematical object is the polarized complexification.  Replace conjugate amplitudes
by independent variables `(ã,b̃)` and polarize

```text
S((a,b),(ã,b̃))=aã+b b̃.                                      (17)
```

Iterate `H` in the first variables and the coefficient-conjugate lift in the second.  The polarized
escape potential is then a solution of a two-map functional equation.  The novelty-bearing theorem
would be one of the following:

1. the polarized action density satisfies no nonzero algebraic partial differential equation over
   the rational source field;
2. a physically fixed one-real-parameter slice of `A` is HT as an ordinary analytic function;
3. DA of the polarized action forces `F` into a Ritt-integrable class.

None is presently proved.  Parametrized difference Galois theory for Mahler and Poincare equations
is relevant, but the composition operator here is a nonexceptional rational self-map and the source
term is a polarized logarithmic Born weight.  A theorem for scalar Mahler dilation cannot simply be
quoted.

## Anti-theatre and novelty gate

The complete-tree product `(7)`, telescoping `(8)`, homogeneous escape-rate limit, and dynamical
Green potential are individually standard mechanisms.  The candidate new physical content is their
exact identification with an experimentally meaningful postselection resource density for a
coherent nonexceptional qubit rational map.

Targeted searches for postselection success probability together with rational-map Green
potentials, escape rates, Julia equilibrium measures, and hypertranscendence found the quantum
protocol and complex-dynamics literatures separately and no prior form of `(8)`--`(16)`.  This is a
provisional novelty result.  The card remains in progress because the dual gate is not yet cleared:
the Green-potential identity is significant only if it yields either an operational reconstruction
theorem beyond known Julia tomography or the HT inheritance theorem above.

## Lean boundary

The homogeneous map and its projective nondegeneracy are already formalized in
`formal/GaloisForLFunctions/HTGeometry/PostselectedQubitRationalDynamics.lean`.  The next
unconditional formal batch is:

- the squared-norm identity `(3)` over rational real amplitudes;
- the one-node success ratio `(4)` as a cross-multiplied identity;
- the finite binary-tree exponent telescope `(7)`--`(8)` in a division-free form.

No analytic escape-rate existence or HT claim will be postulated as a Lean assumption.

## Primary sources

- T. Kiss, I. Jex, G. Alber, and S. Vymetal, *Complex chaos in the conditional dynamics of
  qubits*, <https://arxiv.org/abs/quant-ph/0511208>.
- T. Kiss, I. Jex, G. Alber, and S. Vymetal, *Complex chaos in conditional qubit dynamics and
  purification protocols*, <https://arxiv.org/abs/0705.1979>.
- G. Zhu, O. Kalman, K. Wang, et al., *Experimental orthogonalization of highly overlapping
  quantum states with single photons*, <https://arxiv.org/abs/1910.10377>.
- G. Evenbly and G. Vidal, *Tensor Network Renormalization*,
  <https://arxiv.org/abs/1412.0732>.
- Q. Hu, A. Franco-Rubio, and G. Vidal, *Continuous tensor network renormalization for quantum
  fields*, <https://arxiv.org/abs/1809.05176>.
- L. Di Vizio and G. Fernandes, *A Galoisian proof of Ritt theorem on the differential
  transcendence of Poincare functions*, <https://arxiv.org/abs/2102.08268>.
- T. Dreyfus, C. Hardouin, and J. Roques, *Hypertranscendence of solutions of Mahler equations*,
  <https://arxiv.org/abs/1507.03361>.

## Gates

- [x] Exact one-node Born success probability derived.
- [x] Exact complete-tree success product derived.
- [x] Finite-depth exponent telescope proved.
- [x] Intensive action density derived.
- [x] Action density identified with projective Green potential.
- [x] Exact weighted cohomological equation derived.
- [x] Autonomous and nonautonomous finite-jet tail classifications applied as exclusion gates.
- [x] QFT analogy separated from a continuum theorem.
- [x] Polarized HT open core stated without promotion.
- [x] Targeted conjunction search provisionally found no prior theorem.
- [ ] Division-free finite-tree algebra formalized in Lean.
- [ ] Differential-algebraic classification of polarized action proved.
- [ ] Operational Green-potential reconstruction theorem proved.
- [ ] Reflection-positive local QFT/tensor-network realization constructed.
